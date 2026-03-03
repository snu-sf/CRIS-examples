Require Import CRIS.
Require Import KnotMainI KnotMainA KnotA.
Require Import APCTactics APC APCC APCHeader.

Module KnotMainIA. Section KnotMainIA.
  Import KnotA KnotMainA APCA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _KNOT: !knotGS}.

  (* 1. global environment *)
  Context (genv: GEnv.t).
  (* 2. spec tables *)
  Context (sp sp_rec sp_fun sp_pure sp_mem : specmap).
  (* 3. hypotheses for genv *)
  Context (GEnvWF : GEnv.wf genv).
  Context (GEnvIncl : incl KnotMainGEnv.t genv).
  (* 4. hypotheses for sp *)
  Context (MainInFun : (main_fun_sp genv sp_rec) ⊆ sp_fun).
  Context (KnotInSp : knot_rec_sp ⊆ sp).
  Context (APCInSp : APCA.sp ⊆ sp).
  (* 5. hypotheses for pure sp *)
  Context (RecInSpPure : sp_rec ⊆ sp_pure).
  Context (PureInGlobal : sp_pure ⊆ sp).

  Local Notation APCA := (APCA.t sp_pure sp).
  Local Notation MemA := (MemA.t sp_mem).
  Local Notation KnotA := (KnotA.t genv sp_rec sp_fun sp).
  Local Notation KnotAMod := (KnotA ★ MemA ★ APCA).
  Local Notation KnotMainA := (KnotMainA.t genv sp_rec true sp).
  Local Notation KnotMainI := (KnotMainI.t genv).
  Local Notation KnotMainAMod := (KnotMainA ★ KnotAMod).
  Local Notation KnotMainIMod := (KnotMainI ★ KnotAMod).
  Local Notation IstFull := (IstProd (IstSB KnotMainA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_fib : ISim.sim_fun open KnotMainAMod KnotMainIMod IstFull (fid KnotMainHdr.fib).
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    cStartFunSim. rewrite /KnotMainI.fibF.

    cStepsS. destruct _q as [n I]; s. iDestruct "ASM" as "[[[%fb [-> [% %Hspec]]] I] [%vo [-> %LEvo]]]".
    cStepsT. inv Hspec. rewrite FBLOCK. cStepsT.
    unfold assume. unshelve cForceT; eauto. cStepsT.
    des_ifs.
    { (* base case *)
      rewrite /APC.pure_body. cStepsS. simpl_sp. cForcesS. iSplitR; et. cStepsS.
      cInlineS. cStepsS.
      iDestruct "ASM" as "[-> <-]". cStepsS.
      unfold APC. cForceS 0. cStepsS.

      (* SRC: change to skip *)
      iApply wsim_apc_src. cStepsS. cForcesS. iSplitR; et. cStepsS.
      cForcesS. iSplitL "I"; iFrame; et.
      assert (n = 1 \/ n = 0) by nia. assert (Hn : Z.of_nat (Fib n) = 1%Z).
      { des; subst; reflexivity. }
      rewrite Hn. cStep. iSplit; et.
    }
    { (* recursive cCall *)
      cStepsT. rewrite /pure_body. cStepsS. simpl_sp. cForcesS. iSplitR; et. cStepsS.
      cInlineS. cStepsS.
      iDestruct "ASM" as "[-> <-]". cStepsS. unfold APC.
      cForceS 2. cStepsS.

      (* first cCall - rec(n - 1) *)
      dup SPEC. inv SPEC.
      apcCallWeak ""; et.
      { instantiate (1 := 1). apply OrdArith.lt_from_nat. ss. }
      { instantiate (1 := (2 * (n - 1) + 1)%ord). eapply Ord.lt_le_lt; [|et].
        rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia. 
      }
      iSplitL "IST I".
      { ss. instantiate (1:= (n - 1)). iFrame. iSplit; et.
        - iPureIntro. split.
          { repeat f_equal. lia. }
          { unfold intrange_64 in *.
            bsimpl; des; split; des_sumbool;
            repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss.
          }
        - iPureIntro. eexists; esplits; et. refl. 
      }
      clear_st. iIntros (st_src st_tgt ret) "[IST [-> I]]".
      cStepsT.

      (* second cCall - rec(n - 2) *)
      apcCallWeak ""; et.
      { instantiate (1:=0). apply OrdArith.lt_from_nat. ss. }
      { instantiate (1 := (2 * (n - 1))%ord). eapply Ord.lt_le_lt; [|et].
        rewrite -!OrdArith.mult_from_nat. eapply OrdArith.lt_from_nat. nia.
      }
      { iFrame. instantiate (1:= (n - 2)). iSplit; et.
        { iPureIntro. splits; first (repeat f_equal; nia).
          { unfold intrange_64 in *.
            bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec;
              unfold min_64, max_64, modulus_64_half in *; try nia; ss.
          }
          eexists; esplits; et. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat.
          eapply OrdArith.le_from_nat. nia.
      }
        clear_st. iIntros (st_src st_tgt ret) "[IST [-> I]]". cStepsT.

        iApply wsim_apc_src. cStepsS. cForcesS. iSplit; et. cStepsS. cForcesS. iFrame. iSplit; et.

        cStep. iSplit; et.
        iPureIntro. repeat f_equal. rewrite unfold_fib; nia.
      }
    }
    Unshelve. all: exact (0↑).
  (*SLOW*)Qed.

  Lemma simF_main : ISim.sim_fun open KnotMainAMod KnotMainIMod IstFull entry.
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    cStartFunSim. rewrite /KnotMainI.mainF /main_body.

    (* SKINCL *)
    pose proof (@CEnv.incl_incl_env KnotMainGEnv.t genv) as INCLENV.
    unfold KnotMainGEnv.t in GEnvIncl; ss.
    eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotMainHdr.fib Gfun↑) as SF.
    hexploit SF; [left; ss|intro SKINCL_F].
    des. clear SF INCLENV.

    (* SKWF *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotMainHdr.fib blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDF.

    (* SRC: precondition *)
    cStepsS. iDestruct "ASM" as "[-> [-> FG]]". cStepsS.

    (* TGT: find a block of the function "fib" using SKINCL *)
    cStepsT. rewrite FINDF. cStepsT.

    (* TGT: inlining "fib" *)
    cInlineT. cForceT Fib. cForcesT. iSplitL "FG"; et.
    { (* prove the precondition of "fib" *)
      iFrame. iSplit; et. iPureIntro. eexists. esplits; et. econs; esplits; et.
      econs.
      { simpl_sp; ss. }
      iIntros (P Q) "[% [-> ->]]"; iExists _, _; iSplit.
      { iPureIntro; exists (x, knot_frag (Some Fib)); split; ss. }
      iIntros (? ?) "[[% $] %] !>"; iSplit; eauto; iPureIntro; des; subst; esplits; eauto.
      ltac2:(renames H into RGx, SPfb, LEvo).
      inv SPfb. econs; eauto.
      inv SPEC. econs; eauto.
      iIntros (? ?) "[%m [-> ->]]". iPoseProof (WEAK with "[]") as "[% [% [%Hfsp I]]]".
      { iPureIntro. exists (Fib, m); split; ss. }
      iExists _, _; iSplit; first eauto.
      unfoldPrePost. iIntros (? ?) "[[% F] [% %]]"; iPoseProof ("I" with "[F]") as "?".
      { iFrame. iSplit; eauto. }
      eauto.
    }

    (* TGT: take a postcondition of "fib" *)
    cStepsT. iDestruct "GRT" as "[-> [[% [-> %]] FG]]". cStepsT. inv H.

    (* TGT: find a block of the function "rec" using the postcondition of "fib" *)
    rewrite FBLOCK. cStepsT.
    
    (* SRC: handle pure (APC) *)
    unfold pure. cStepsS.
    cForceS 30%ord. cStepsS. simpl_sp. cForceS.
    cForcesS. iSplitR; et. cStepsS.

    (* SRC: inlining APC *)
    cInlineS. cStepsS. iDestruct "ASM" as "%"; des; subst. cStepsS.
    unfold APC. cForceS 1. cStepsS. 
    inv SPEC.
    (* SRC, TGT: cCall "fib" using APC tactic *)
    apcCallWeak "FG"; et.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat; et. }
    { instantiate (1:=29). cSimpl. eapply OrdArith.lt_from_nat; nia. }
    iSplitL "FG IST".
    { ss. instantiate (1:=(Fib, 10)). iFrame. iSplit; et.
      iPureIntro. eexists; esplits; ss.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.le_from_nat; nia.
    }
    clear_st. iIntros (st_src st_tgt ret) "[IST [-> FG]]". cStepsT.

    (* SRC: jump APC *)
    iApply wsim_apc_src. cStepsS. cForcesS. iSplit; et. cStepsS. cForceS. cStepsS.
    cForceS. iSplit; eauto. 
    cStep. iSplitR; et.
    Unshelve. all: try exact (tt↑).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open KnotMainAMod KnotMainIMod emp%I IstFull.
  Proof.
    cStartModSim.
    (* - exfalso. revert H. unfold_mod; ss. *)
    { eapply simF_fib; et. }
    { eapply simF_main; et. }
    { iIntros "_"; repeat iExists _; iSplit; eauto. }
  Qed.

  Lemma ctxr :
    ctx_refines
      (KnotMainA.t genv sp_rec true sp
        ★ KnotA.t genv sp_rec sp_fun sp
        ★ MemA.t sp_mem
        ★ APCA.t sp_pure sp,
      emp%I)
      (KnotMainI.t genv
        ★ KnotA.t genv sp_rec sp_fun sp
        ★ MemA.t sp_mem
        ★ APCA.t sp_pure sp,
      emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.

  Lemma ctxr_close :
    ctx_refines
      (KnotMainA.t genv sp_rec false sp ★ APCC.t sp, emp%I)
      (KnotMainA.t genv sp_rec true  sp ★ APCC.t sp, emp%I).
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    eapply main_adequacy.
    cStartModSim.
    { cStartFunSim. rewrite /pure_body.
      cStepsS. case_match. iDestruct "ASM" as "[[% PRE] %]"; des; cSimpl.
      rewrite /pure_body. cStepsS. simpl_sp. cForcesS.
      iSplitR; eauto. cStepsS. cForceT (n, u).
      cForcesT. iSplitL "PRE".
      { iFrame; iPureIntro; esplits; eauto. }
      cSimpl. cStepsT. simpl_sp. cStepsT. iDestruct "GRT" as "%"; des; cSimpl.
      cCall "IST"; eauto.
      iIntros (???) "IST".
      cStepsS. cStepsT. cForcesT. iSplitL "ASM"; eauto.
      cStepsT. iDestruct "GRT" as "[% POST]". cForcesS.
      iSplitL "POST"; iFrame; eauto.
      cStep. iFrame; eauto.
    }
    { cStartFunSim. rewrite /main_body.
      cStepsS. cSimpl. iDestruct "ASM" as "[% [% ?]]"; des; cSimpl.
      cStepsS. cForcesT. iFrame. iSplit; eauto. cStepsT.
      rewrite /pure. cStepsT. simpl_sp. cStepsT. cInlineT. cForcesT. iSplit; eauto. cStepsT.
      iDestruct "GRT" as "(% & %)". cSimpl. cForcesT. iSplitR; et.
      cStepsT. cForcesS. iSplit; eauto. cStep.
      iSplit; eauto.
    }
    { instantiate (1:=const (const emp%I)). iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Unshelve. all: et. exact tt.
  (*SLOW*)Qed.
End KnotMainIA. End KnotMainIA.
