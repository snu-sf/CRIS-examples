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

  Lemma simF_fib : ISim.sim_fun open KnotMainAMod KnotMainIMod IstFull (Some KnotMainHdr.fib).
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    iStartSim.

    steps_l. destruct _q as [n I]; s. iDestruct "ASM" as "[[[%fb [-> [% %Hspec]]] I] [%vo [-> %]]]".
    steps_r. inv Hspec. rewrite FBLOCK. steps_r.
    unfold assume. unshelve force_r; eauto. steps_r.
    des_ifs.
    { (* base case *)
      rewrite /APC.pure_body. steps_l. simpl_sp. forces_l. iSplitR; et. steps_l.
      inline_l. steps_l.
      iDestruct "ASM" as "[-> <-]". steps_l.
      unfold APC. force_l 0. steps_l.

      (* SRC: change to skip *)
      iApply wsim_apc_src. steps_l. forces_l. iSplitR; et. steps_l.
      forces_l. iSplitL "I"; iFrame; et.
      assert (n = 1 \/ n = 0) by nia. assert (Hn : Z.of_nat (Fib n) = 1%Z).
      { des; subst; reflexivity. }
      rewrite Hn. step. iSplit; et.
    }
    { (* recursive call *)
      steps_r. rewrite /pure_body. steps_l. simpl_sp. forces_l. iSplitR; et. steps_l.
      inline_l. steps_l.
      iDestruct "ASM" as "[-> <-]". steps_l. unfold APC.
      force_l 2. steps_l.

      (* first call - rec(n - 1) *)
      dup SPEC. inv SPEC.
      apc_call_weaker ""; et.
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
      steps_r.

      (* second call - rec(n - 2) *)
      apc_call_weaker ""; et.
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
        clear_st. iIntros (st_src st_tgt ret) "[IST [-> I]]". steps_r.

        iApply wsim_apc_src. steps_l. forces_l. iSplit; et. steps_l. forces_l. iFrame. iSplit; et.

        step. iSplit; et.
        iPureIntro. repeat f_equal. rewrite unfold_fib; nia.
      }
    }
    Unshelve. all: exact (0↑).
  (*SLOW*)Qed.

  Lemma simF_main : ISim.sim_fun open KnotMainAMod KnotMainIMod IstFull None.
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    iStartSim.

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
    steps_l. iDestruct "ASM" as "[-> [-> FG]]". steps_l.

    (* TGT: find a block of the function "fib" using SKINCL *)
    steps_r. rewrite FINDF. steps_r.

    (* TGT: inlining "fib" *)
    inline_r. force_r Fib. forces_r. iSplitL "FG"; et.
    { (* prove the precondition of "fib" *)
      iFrame. iSplit; et. iPureIntro. eexists. esplits; et. econs; esplits; et.
      econs.
      { simpl_sp; ss. }
      iIntros (P Q) "[% [-> ->]]"; iExists _, _; iSplit.
      { iPureIntro; exists (x, knot_frag (Some Fib)); split; ss. }
      iIntros (? ?) "[[% $] %] !>"; iSplit; eauto; iPureIntro; des; esplits; eauto.
      inv H3. econs; eauto.
      inv SPEC. econs; eauto.
      iIntros (? ?) "[%n [-> ->]]". iPoseProof (WEAK with "[]") as "[% [% [% I]]]".
      { iPureIntro. exists (Fib, n); split; ss. }
      iExists _, _; iSplit; first eauto.
      unfold_pre_post. iIntros (? ?) "[[% F] [% %]]"; iPoseProof ("I" with "[F]") as "?".
      { iFrame. iSplit; eauto. }
      eauto.
    }

    (* TGT: take a postcondition of "fib" *)
    steps_r. iDestruct "GRT" as "[-> [[% [-> %]] FG]]". steps_r. inv H.

    (* TGT: find a block of the function "rec" using the postcondition of "fib" *)
    rewrite FBLOCK. steps_r.
    
    (* SRC: handle pure (APC) *)
    unfold pure. steps_l.
    force_l 30%ord. steps_l. simpl_sp. force_l.
    forces_l. iSplitR; et. steps_l.

    (* SRC: inlining APC *)
    inline_l. steps_l. iDestruct "ASM" as "%"; des; subst. steps_l.
    unfold APC. force_l 1. steps_l. 
    inv SPEC.
    (* SRC, TGT: call "fib" using APC tactic *)
    apc_call_weaker "FG"; et.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat; et. }
    { instantiate (1:=29). hss. eapply OrdArith.lt_from_nat; nia. }
    iSplitL "FG IST".
    { ss. instantiate (1:=(Fib, 10)). iFrame. iSplit; et.
      iPureIntro. eexists; esplits; ss.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.le_from_nat; nia.
    }
    clear_st. iIntros (st_src st_tgt ret) "[IST [-> FG]]". steps_r.

    (* SRC: jump APC *)
    iApply wsim_apc_src. steps_l. forces_l. iSplit; et. steps_l. force_l. steps_l.
    force_l. iSplit; eauto. 
    step. iSplitR; et.
    Unshelve. all: try exact (tt↑).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open KnotMainAMod KnotMainIMod emp%I IstFull.
  Proof.
    init_sim.
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
    init_sim.
    (* { exfalso. revert H. hrepeat do 1 unfold_mod. i; inv H. } *)
    { iStartSim.
      steps_l. case_match. iDestruct "ASM" as "[[% PRE] %]"; des; hss.
      rewrite /pure_body. steps_l. simpl_sp. forces_l.
      iSplitR; eauto. steps_l. force_r (n, u).
      forces_r. iSplitL "PRE".
      { iFrame; iPureIntro; esplits; eauto. }
      hss. steps_r. simpl_sp. steps_r. iDestruct "GRT" as "%"; des; hss.
      call "IST"; eauto.
      iIntros (???) "IST".
      steps_l. steps_r. forces_r. iSplitL "ASM"; eauto.
      steps_r. iDestruct "GRT" as "[% POST]". forces_l.
      iSplitL "POST"; iFrame; eauto.
      step. iFrame; eauto.
    }
    { iStartSim.
      steps_l. hss. iDestruct "ASM" as "[% [% ?]]"; des; hss.
      steps_l. forces_r. iFrame. iSplit; eauto. steps_r.
      rewrite /pure. steps_r. simpl_sp. steps_r. inline_r. forces_r. iSplit; eauto. steps_r.
      iDestruct "GRT" as "(% & %)". hss. forces_r. iSplitR; et.
      steps_r. forces_l. iSplit; eauto. step.
      iSplit; eauto.
    }
    { instantiate (1:=const (const emp%I)). iIntros "_"; repeat iExists _; repeat iSplit; eauto. }
  Unshelve. all: et. exact tt.
  (*SLOW*)Qed.
End KnotMainIA. End KnotMainIA.
