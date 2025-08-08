
Require Import CRIS.
Require Import KnotHeader KnotI KnotA MemHeader APCHeader APC APCA APCTactics Tactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module KnotIA. Section KnotIA.
  Import KnotA APC APCA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  Context `{_knotG: !knotG}.
                 
  (* 1. global environment *)
  Context (genv: GEnv.t).
  (* 3. spec tables *)
  Context (Sp : sp_type).
  Context (SpRec SpFun SpMem SpPure: spl_type).
  (* 4. hypotheses for genv *)
  Context (GEnvWF: GEnv.wf genv).
  Context (GEnvIncl: incl KnotGEnv.t genv).
  (* 5. hypotheses for sp *)
  Context (RecInSp: spl_sub KnotRecSp SpRec).
  Context (APCInSp: sp_incl APCA.Sp Sp).
  (* 6. hypotheses for pure sp *)
  Context (FunInPure: spl_sub SpFun SpPure).
  Context (PureInSp : sp_incl SpPure Sp).

  Definition inv : iProp Σ :=
    (∃ (f': optionO (natO -d> natO)) (fb': val),
        (⌜∀ f (EQ: f' ≡ (Some f: optionO (natO -d> natO))),
            ∃ fb,
              (<<BLK: fb' = Vptr (fb, 0%Z)>>) /\
              (<<FN: fb_has_spec_in genv SpFun fb (fun_gen genv SpRec f)>>)⌝)
          ∗ (knot_full f')
          ∗ (var_points_to genv KnotHdr._f fb'))%I.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, inv.

  Local Definition APCA := (APCA.t SpPure Sp).
  Local Definition MemP := MemP.t.
  Local Definition KnotA := (KnotA.t genv SpRec SpFun Sp).
  Local Definition KnotAMod := (KnotA ★ MemP ★ APCA).
  Local Definition KnotIMod := ((KnotI.t genv) ★ MemP ★ APCA).
  Local Definition IstFull := (IstProd (IstSB KnotA.(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_rec:
    ISim.sim_fun open KnotAMod KnotIMod (KnotA.init_cond genv) IstFull (Some KnotHdr.rec).
  Proof using GEnvWF GEnvIncl RecInSp APCInSp FunInPure PureInSp.
    init_simF.

    (* SKINCL - SkEnv id2blk *)
    pose proof (@CEnv.incl_incl_env KnotGEnv.t genv) as INCLENV.
    (* unfold KnotIMod in GEnvIncl; ss. apply (incl_app_inv KnotGEnv _) in GEnvIncl. des. *)
    unfold KnotGEnv.t in GEnvIncl.
    eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotHdr._f (Gvar 0%Z)↑) as SF.
    specialize (@GEnvIncl KnotHdr.rec Gfun↑) as SR.
    hexploit SF; [right; right; left; ss|intro SKINCL_F].
    hexploit SR; [right; left; ss|intro SKINCL_REC]. des. clear SF SR INCLENV.

    (* SKWF - SkEnv blk2id *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotHdr.rec blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDR.

    (* Simulation Start *)
    (* SRC: precondition *)
    steps_l. iDestruct "ASM" as "((%Y & FG) & %Q)"; des; subst; hss. steps_r.
    iDestruct "IST" as (? ? ? ?) "(%ST & [% IST] & %E)"; des; subst.
    iDestruct "IST" as (? ?) "(% & FL & VF)".

    (* RA: Set _f as a funciton pointer whose spec is "_f_spec" *)
    iPoseProof (knot_ra_merge with "FL FG") as "%".
    symmetry in H2. specialize (H1 _q1 H2). des; subst.
    rename _q1 into _f_spec.
    
    (* TGT: get a block of _f *)
    rewrite FIND0. hss. steps_r.

    (* TGT: load the function at the block of _f by inlining "load" *)
    inline_r. rewrite /MemSpec.load.
    steps_r.
    rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.
    iApply wsim_update_proph_tgt; iExists (blk0, 0%Z, 1%Qp, (Vptr (fb, 0%Z))).
    iSplitL "VF".
    { iSplit; eauto. unfold var_points_to. rewrite FIND0. iFrame. }
    iIntros (?) "[Q %]".
    (* steps_r. iMod ("Q" with "GRT") as "[VF %]". des; subst; hss. *)
    des; subst; hss. steps_r. hss_r. inv H2. steps_l. steps_r.

    (* TGT: get blocks of the function pointer and "rec" *)
    dup FN. inv FN. des. rewrite FBLOCK. hss. forces_l. iSplitR; et.
    steps_r. rewrite FINDR; hss. steps_r.

    (* SRC: unfold APC *)
    steps_l. inline_l. steps_l. iDestruct "ASM" as "%"; subst; hss.
    steps_l. unfold apc_body, APC.
    force_l 1. steps_l. 

    (* call apc with fn *)
    dup SPEC. inv SPEC.
    apc_call_weaker "FL FG Q"; eauto.
    { instantiate (1 := 0). apply OrdArith.lt_from_nat. nia. }
    { instantiate (1:= (2 * _q2)). eapply Ord.lt_le_lt; et. rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia. }
    { iSplitR "FL Q".
      - unfold precond. ss. iFrame. iSplit.
        + iPureIntro. eexists; esplits; et. econs; et.
          econs; [|replace rec_spec with (fspec_flat (Some rec_spec)) by ss; refl].
          apply RecInSp. unfold KnotRecSp. unseal CRIS. ss.
        + iPureIntro. eexists; esplits; et. rewrite -OrdArith.mult_from_nat. apply OrdArith.le_from_nat. nia. 
      - iExists _, _, _, _. repeat (iSplit; et). iExists (Some _f_spec), _. iSplit.
        + iPureIntro. i. esplits; et. instantiate (1:=fb). econs; et. inv EQ; et.
        + unfold var_points_to. rewrite FIND0. iFrame.
    }
    iDestruct "ISTPOST" as "[IST [% FG]]". hss.

    (* TGT: steps tgt *)
    steps_r. hss. steps_r.

    (* SRC: change to skip *)
    apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplitL "FG"; iFrame; et.

    step. by iFrame.
    Unshelve. all: ss.
  (*SLOW*)Admitted.

  Lemma simF_knot:
    ISim.sim_fun open KnotAMod KnotIMod (KnotA.init_cond genv) IstFull (Some KnotHdr.knot).
  Proof using GEnvWF GEnvIncl RecInSp APCInSp FunInPure PureInSp.
    init_simF.

    (* SKINCL *)
    pose proof (@CEnv.incl_incl_env KnotGEnv.t genv) as INCLENV.
    unfold KnotGEnv.t in GEnvIncl. eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotHdr._f (Gvar 0%Z)↑) as SF.
    specialize (@GEnvIncl KnotHdr.rec Gfun↑) as SR.
    hexploit SF; [right; right; left; ss|intro SKINCL_F].
    hexploit SR; [right; left; ss|intro SKINCL_REC]. des. clear SF SR INCLENV.

    (* SKWF *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotHdr.rec blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDR.

    (* SRC: precondition *)
    steps_l.
    rename _q into new_spec.
    iDestruct "ASM" as "((%FB & [%old OLD]) & %Q)". des; subst. hss. steps_r.
    iDestruct "IST" as (? ? ? ?) "(%ST & [% IST] & %E)"; des; subst.
    iDestruct "IST" as (? ?) "(% & FL & VF)".

    (* RA: unify the infomation of f_spec *)
    iPoseProof (knot_ra_merge with "FL OLD") as "%". symmetry in H2.
    assert (REFL: knot_full f' ⊢ knot_full old). { iIntros "F". rewrite /knot_full H2. ss. }
    iPoseProof (REFL with "FL") as "FL".
    rewrite FIND0; hss. steps_r.
    
    (* TGT: save a function by calling "store" *)
    steps_r. inline_r.
    rewrite /MemSpec.store. steps_r.
    rewrite /fspec_proph_update; unfold_iter_r; steps_r; hss_r; steps_r.

    iApply wsim_update_proph_tgt; iExists (blk0, 0%Z, _, Vptr (fb, 0%Z)). iSplitL "VF".
    { iSplit; et. unfold var_points_to. rewrite FIND0; eauto. }
    iIntros (?) "[VF %]". steps_r. hss_r;  steps_r.

    (* RA: update spec *)
    hss. steps_r. rewrite FINDR; hss. steps_r.
    iCombine "FL OLD" as "SPEC".
    iPoseProof (auth_excl_both_update with "SPEC") as ">[FL FG]".

    (* finish reasoning *)
    steps_l. force_l. steps_l. force_l. force_l.
    iSplitL "FG"; iFrame; et.
    { iSplit; et. iPureIntro. eexists. esplit; et. econs; et.
      econs; [|replace rec_spec with (fspec_flat (Some rec_spec)) by ss; refl].
      apply RecInSp. unfold KnotRecSp. unseal CRIS. ss. }
    steps_l.
    hss. steps_r. step. iSplit; et.

    (* check IST *)
    inv FB0. des.
    iExists _, _, _, _. iSplit; et. iSplit; et. iSplit; et. unfold Ist, inv.
    iExists (Some new_spec), _. iSplit; iFrame; et.
    { iPureIntro. ii. eexists. esplits; et. econs; et. inv EQ. et. }
    { unfold var_points_to. des_ifs. }
  Qed.

  Theorem sim : ISim.t open KnotAMod KnotIMod (KnotA.init_cond genv) IstFull.
  Proof.
    init_sim.
    - split; eauto. iIntros "[VF FL]". iSplit; et.
      { iPureIntro. split; ss. }
      { unfold Ist, inv. iExists None, _. iSplit; iFrame; et. iPureIntro. ii. inv EQ. }
    - apply simF_rec; et.
    - apply simF_knot; et.
  Qed.

  Theorem ctxr
    :
    ctx_refines
      (KnotA.t genv SpRec SpFun Sp ★ MemP ★ APCA.t SpPure Sp,
        KnotA.init_cond genv)
      (KnotI.t genv ★ MemP ★ APCA.t SpPure Sp,
        emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.

End KnotIA. End KnotIA.
