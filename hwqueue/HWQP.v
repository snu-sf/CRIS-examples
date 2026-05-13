Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader HWQI.
Require Import CallFilter ProphecyI SchTactics.

Ltac unfoldIterEqS :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_s;
  rewrite unfold_iter;
  show_until marker.

Ltac unfoldIterEqT :=
  let marker := fresh "MARKER" in
  set_marker marker;
  hide_ihyps;
  only_itree_t;
  rewrite unfold_iter;
  show_until marker.

(* Prophecy-inserted intermediate module, HWQP *)
Module HWQP. Section HWQP.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS}.
  Context (mn : string).

  Definition new_queue : list val → itree crisE val := λ sz,
    𝒴;;; sz <- (pargs [Tint] sz)?;;
    𝒴;;; 'q : val <- ccallU MemHdr.alloc [Vint (2 + sz)];;
    𝒴;;; '(qblk, qofs) : _ <- (pargs [Tptr] [q])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs); Vint sz];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 1)%Z; Vint 0];;
    𝒴;;; ITree.iter (λ (x : nat), (* initialization *)
      𝒴;;;
        if Nat.ltb x (Z.to_nat sz) 
        then 
          '_ : val <- ccallU MemHdr.store [Vptr (qblk, qofs + 2 + x)%Z; Vint 0];; Ret (inl (S x))
        else
          Ret (inr ())) 0;;;
    𝒴;;; trigger (Call (Prophecy.new mn).1 ("hwq", q↑↑)↑);;; Ret q.

  Definition dequeue_aux (q : val) (range : nat) (i : nat) : itree crisE (() + val) :=
    𝒴;;;
      ITree.iter (λ i : nat,
        𝒴;;;
        if (decide (i = 0))
        then Ret (inr (inl ()))
        else
          let j := range - i in
          𝒴;;; '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] [q])?;;
          𝒴;;; 'x : val <- ccallU MemHdr.load [Vptr (blk, ofs + 2 + j)%Z];;
          match x with
          | Vint 0 => 𝒴;;; Ret (inl (i - 1))
          | Vptr (xblk, xofs) =>
              𝒴;;;
                'c : val <- ccallU MemHdr.cas [Vptr (blk, ofs + 2 + j)%Z; x; Vint 0];;
                trigger (Call (Prophecy.resolve mn).1
                  (("hwq", q↑↑), (j, bool_decide (c = x))↑↑)↑);;;
              𝒴;;; 'succ : val <- ccallU MemHdr.cmp [c; x];;
              𝒴;;;
                match succ with
                | Vint 0 => 𝒴;;; Ret (inl (i - 1))
                | Vint 1 => 𝒴;;; Ret (inr (inr c))
                | _ => 𝒴;;; triggerUB
                end
          | _ => triggerUB
          end) i.

  Definition dequeue : list val → itree crisE val := λ q,
    𝒴;;; '(qblk, qofs) : mblock * ptrofs <- (pargs [Tptr] q)?;;
    𝒴;;;
      ITree.iter (λ _ : unit,
        𝒴;;; 'sz : val <- ccallU MemHdr.load [Vptr (qblk, qofs)];;
        𝒴;;; 'sz : Z <- (pargs [Tint] [sz])?;;
        𝒴;;; 'back : val <- ccallU MemHdr.load [Vptr (qblk, qofs + 1)%Z];;
        𝒴;;; 'back : Z <- (pargs [Tint] [back])?;;
        𝒴;;; let range := Z.to_nat (Z.min sz back) in
        dequeue_aux (Vptr (qblk, qofs)) range range) ().

  Definition msk : emask :=
    CFilter.msk_filter_in (MemHdr.exports ∪ SchHdr.exports ∪ Prophecy.exports mn)
      (msk_real (msk_scp [] msk_true)).

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk, (None, cfunU imp_fun_t new_queue));
      fid HWQHdr.enqueue   # (msk, (None, cfunU imp_fun_t (HWQI.enqueue)));
      fid HWQHdr.dequeue   # (msk, (None, cfunU imp_fun_t dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.

  Lemma filter_helping mnh : CFilter.filter (Helping.exports mnh) t = t.
  Proof. cfilter_solver. Qed.

  Lemma real_mod : Mod.real_mod t.
  Proof. real_mod_solver. Qed.
End HWQP. End HWQP.

Module HWQIP. Section HWQIP.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS}.
  Context (mn : string).

  Local Definition IstFull := IstProd (IstSB (Mod.scopes (HWQP.t mn)) IstEq) IstEq.
  Lemma ctxr :
    ctx_refines
      (HWQI.t    ★ ProphecyI.t mn, emp)%I
      (HWQP.t mn ★ ProphecyI.t mn, emp)%I.
  Proof using.
    apply main_adequacy with (Ist:=IstFull).
    cStartModSim.
    { cStartFunSim.
      cStepsS. destruct Any.downcast as [sz|]; cStepsS; ss. cStepsT.
      rewrite /HWQP.new_queue /HWQI.new_queue.
      cStepsS. cStepsT. sYieldRR "IST".
      sYieldS. cStepsS.
      destruct sz as [|[sz| | ] [|]]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (ret st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      destruct v as [ | [blk ofs] | ]; cStepsS; ss; cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS.
      cNormS. cNormT.
      replace 0 with (Z.to_nat sz - Z.to_nat sz) by lia.
      assert (Z.to_nat sz ≤ Z.to_nat sz) as Hsz by lia.
      revert Hsz. generalize (Z.to_nat sz) at 1 5 8 as n.
      clear_st. intros n Hn. iInduction n as [|n] "IH_loop" forall (Hn st_src st_tgt).
      { replace (Z.to_nat sz - 0) with (Z.to_nat sz) by lia.
        unfoldIterEqS. unfoldIterEqT.
        rewrite Nat.ltb_irrefl.
        cStepsT. sYieldRR "IST".
        sYieldRR "IST".
        sYieldS. cStepsS. sYieldS. cStepsS. cInlineS. rewrite /ProphecyI.new. cStepsS.
        cStep. iFrame. auto.
      }
      unfoldIterEqS. unfoldIterEqT.
      destruct Nat.ltb eqn : Heqb; last (apply Nat.ltb_ge in Heqb; lia).
      cStepsS. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      replace (S (Z.to_nat sz - S n)) with (Z.to_nat sz - n) by lia.
      iApply "IH_loop"; iFrame. by iPureIntro; lia.
    }
    { cStartFunSim. cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      rewrite /HWQI.enqueue. cStepsS. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS. destruct pargs as [[[? ?] v]|]; last cStepsS; ss.
      cStepsS. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      rewrite /MemHdr.faa. cStepsS; cStepsT.
      destruct pargs; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      destruct pargs; cStepsS; ss. cStepsT.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      destruct pargs; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      case_match; last first.
      { cStepsS; cStepsT.
        sYieldRR "IST".
        sYieldS. cStepsS.
        iApply wsim_reset.
        iStopProof. revert st_src; combine_quant st_tgt; eapply wsim_coind.
        intros ??? []; iIntros "IST". destruct_quant CIH.
        unfoldIterEqS; unfoldIterEqT.
        cStepsS; cStepsT.
        sYieldRR "IST".
        sYieldS. cStepsS.
        cByCoind CIH. iFrame.
      }
      cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS; cStepsT; destruct Any.downcast as [|]; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      cStep. iFrame. done.
    }
    { cStartFunSim.
      cStepsS. destruct Any.downcast as [q|]; cStepsS; ss. cStepsT.
      rewrite /HWQI.dequeue /HWQP.dequeue.
      cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      destruct pargs as [[qblk qofs]|]; last cStepsS; ss. cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_reset. iStopProof. revert st_src. combine_quant st_tgt.
      eapply wsim_coind. iIntros (g _ CIH [st_tgt st_src]) "IST". destruct_quant CIH.
      match goal with | |- context [ITree.iter ?a ?b] => set (src := a) end.
      unfoldIterEqS.
      match goal with | |- context [ITree.iter ?a ?b] => set (tgt := a) end.
      unfoldIterEqT. rewrite {1}/src {1}/tgt.
      cStepsS. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      destruct pargs as [x0|]; last cStepsS; ss. cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      destruct pargs as [x1|]; cStepsS; ss; cStepsT.
      sYieldRR "IST".
      sYieldS. cStepsS.
      rewrite /HWQI.dequeue_aux /HWQP.dequeue_aux. cStepsT; cStepsS.
      sYieldRR "IST".
      sYieldS. cStepsS.
      assert (Z.to_nat (x0 `min` x1) <= Z.to_nat (x0 `min` x1)) as Hi by lia.
      revert Hi. generalize (Z.to_nat (x0 `min` x1)) at 1 6 9 as i.
      intros i Hi.
      iEval (match goal with | |- context [ITree.iter ?a ?b] => set (src2 := a) end).
      set (a := i) at 2.
      iEval (match goal with | |- context [ITree.iter ?a a] => set (tgt2 := a) end). subst a.
      iInduction i as [|i] "IH" forall (st_src st_tgt Hi).
      { unfoldIterEqS; unfoldIterEqT.
        rewrite {1}/src2 {1}/tgt2.
        cStepsS; cStepsT.
        sYieldRR "IST".
        sYieldS. cStepsS. cByCoind CIH. iFrame.
      }
      unfoldIterEqS. unfoldIterEqT. rewrite {2}/src2 {2}/tgt2.
      cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS.
      cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS.
      cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS.
      cStepsS; cStepsT.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      destruct (decide (v1 = Vint 0)) as [->|Hv1].
      { cStepsS; cStepsT.
        sYieldRR "IST".
        sYieldS.
        cStepsS; cStepsT.
        rewrite Nat.sub_0_r.
        iApply "IH"; iFrame. iPureIntro; lia.
      }
      destruct v1 as [v1 | [blk ofs] | ]; cycle 2.
      { cStepsS; ss. }
      { destruct v1; first clarify; cStepsS; ss. }
      cStepsS; cStepsT.
      sYieldRR "IST".
      sYieldS.
      cStepsS; cStepsT.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      cInlineS. rewrite /ProphecyI.new; cStepsS.
      sYieldRR "IST".
      sYieldS.
      cStepsS.
      iApply wsim_call; iFrame; clear_st; iIntros (? st_src st_tgt) "IST".
      cStepsS. cStepsT. destruct Any.downcast; cStepsS; ss. cStepsT.
      sYieldRR "IST".
      sYieldS.
      destruct v2 as [n2 | ptr2 | ]; [|sYieldS; cStepsS; ss|sYieldS; cStepsS; ss].
      destruct (decide (n2 = 0%Z)) as [->|?].
      { cNormS. cStepsT. sYieldRR "IST".
        sYieldS. cStepsS. rewrite Nat.sub_0_r.
        iApply "IH"; iFrame; iPureIntro; lia.
      }
      destruct (decide (n2 = 1%Z)) as [->|?].
      { cNormS. cStepsT. sYieldRR "IST".
        sYieldS. cStepsS.
        cStep. iFrame. done.
      }
      repeat case_match; clarify; sYieldS; cStepsS; ss.
    }
    iIntros "_"; iExists _, _, _, _. repeat iSplit; eauto.
  (*SLOW*)Qed.
End HWQIP. End HWQIP.
