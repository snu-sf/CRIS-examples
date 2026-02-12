(* Require Import CRIS.

Require Import Imp.
Require Import AddHeader AddI AddA.
Require Import RepeatHeader RepeatA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module AddIA. Section AddIA.
  Import AddAS APC APCA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Context (genv : GEnv.t).
  Context (sp : sp_type).
  Context (sp_pure sp_pure_fun : spl_type).

  (* GEnv Hypothesis *)
  Context (GEnvWF : GEnv.wf genv).
  Context (GEnvIncl : incl AddGEnv.t genv).

  (* SPC Hypothesis *)
  Context (APCInSpPure : spl_sub APCA.Sp sp_pure).
  Context (SpPureInSp : sp_incl sp_pure sp).
  Context (repeatInSpPure : alist_find (Some RepeatHdr.repeat) sp_pure = Some (fsp_some (RepeatAS.repeat_spec sp_pure_fun genv))).
  Context (succInSpPureFun : alist_find (Some AddHdr.succ) sp_pure_fun = Some (fsp_some AddAS.succ_spec)).

  (* Modules *)
  Local Definition APCA := (APCA.t sp_pure sp).
  Local Definition RepeatA := (RepeatA.t genv sp sp_pure_fun).
  Local Definition RepeatAMod := (RepeatA ★ APCA).
  Local Definition AddI := (AddI.t genv).
  Local Definition AddA := (AddA.t sp).
  Local Definition AddIMod := (AddI ★ RepeatAMod).
  Local Definition AddAMod := (AddA ★ RepeatAMod).

  (* IST *)
  Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    (λ st_src st_tgt, emp%I).
  Local Definition IstFull := (IstProd (IstSB AddA.(Mod.scopes) Ist) IstEq).

  (* helper lemma for simF_add proof *)
  Lemma _add_succ_repeat_fun:
    ∀ n m, add_fun (Z.of_nat n) m = RepeatAS.repeat_fun succ_fun n m.
  Proof.
    rewrite /add_fun /succ_fun.
    induction n; ii; ss.
    assert ((S n + m)%Z = (n + (m + 1)))%Z as -> by lia. ss.
  Qed.

  Lemma add_succ_repeat_fun:
    ∀ n m, (0 ≤ n)%Z → add_fun n m = RepeatAS.repeat_fun succ_fun (Z.to_nat n) m.
  Proof.
    ii. rewrite -{1}(Z2Nat.id n); et.
    apply (_add_succ_repeat_fun (Z.to_nat n) m).
  Qed.

  Lemma simF_succ : ISim.sim_fun open AddAMod AddIMod AddA.init_cond IstFull (Some AddHdr.succ).
  Proof using _crisG GEnvWF GEnvIncl APCInSpPure SpPureInSp repeatInSpPure succInSpPureFun.
    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of succ *)
    steps_l. rename _q into n.
    iDestruct "ASM" as "%". hss. steps_l.

    (* SRC: find apc in sp *)
    assert (SPAPC: sp APCHdr.apc = fsp_some apc_spec).
    { apply SpPureInSp, APCInSpPure. rewrite /Sp. unseal CRIS; ss. }
    rewrite SPAPC.

    (* TGT: steps tgt *)
    steps_r.

    (* SRC: unfold APC *)
    forces_l. iSplit; eauto.
    inline_l. steps_l. iDestruct "ASM" as "%". hss.
    steps_l. unfold APC. force_l. steps_l.

    (* SRC: change to skip *)
    apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

    (* prove the IST *)
    step. by iSplit.
    Unshelve. et. exact (0↑).
  (*SLOW*)Qed.

  Lemma simF_add : ISim.sim_fun open AddAMod AddIMod AddA.init_cond IstFull (Some AddHdr.add).
  Proof using _crisG GEnvWF GEnvIncl APCInSpPure SpPureInSp repeatInSpPure succInSpPureFun.
    (* succ is in somewhere at CEnv *)
    pose proof (@CEnv.incl_incl_env AddGEnv.t genv) as INCLENV.
    eapply INCLENV in GEnvIncl; et.
    pose proof (@GEnvIncl AddHdr.succ Gfun↑) as SS.
    hexploit SS; [left; ss|intros]. des. clear SS INCLENV.
    apply CEnv.load_genv_wf in GEnvWF.
    pose proof (GEnvWF AddHdr.succ blk) as GEnvWF. apply GEnvWF in FIND as FIND'.

    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of add *)
    steps_l. rename _q1 into n, _q2 into m.
    iDestruct "ASM" as "%". hss. steps_l.

    (* SRC: find apc in sp *)
    assert (SPAPC: sp APCHdr.apc = fsp_some apc_spec).
    { apply SpPureInSp, APCInSpPure. rewrite /Sp. unseal CRIS; ss. }
    rewrite SPAPC.

    (* TGT: handle input *)
    steps_r. rewrite FIND. hss. steps_r.

    (* SRC: unfold APC *)
    forces_l. iSplit; eauto.
    inline_l. steps_l. iDestruct "ASM" as "%". hss.
    steps_l. unfold APC. force_l 1. steps_l.

    (* call apc with repeat *)
    apc_call "IST"; et.
    { instantiate (1 := 0). apply OrdArith.lt_from_nat; lia. }
    { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:= (Z.to_nat n)). apply OrdArith.lt_from_nat. lia. }
    { unfold precond. ss. iFrame. instantiate (1 := (Z.to_nat n, m, succ_fun)). iPureIntro. split.
      - exists AddHdr.succ, blk. rewrite Z2Nat.id; et. hrepeat split; et. unfold_intrange_64; des_ifs_safe; hrepeat destruct Z_le_gt_dec; ss; try lia.
        (* succ has sufficient spec *)
        econs; et. unfold succ_spec, fspec_imply.
        ii. rr in ValidSP; des; subst. eexists _,_. split; [rr; et|].
        instantiate (1:=x). split; r; ii; iIntros; iModIntro; hss.
        iPureIntro. split; ss. exists vo. split; et. eapply Ord.le_trans; et. apply Ord.lt_le. apply Ord.omega_upperbound.
      - exists (Ord.omega + (Z.to_nat n))%ord. split; et. apply Ord.le_refl. }
    unfold postcond. ss.
    iDestruct "ISTPOST" as "[IST %]". subst.

    (* TGT: steps tgt *)
    steps_r. hss. steps_r.

    (* SRC: change to skip *)
    apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

    (* prove the IST *)
    step. iSplit; et. 
    iPureIntro. do 2 f_equal.
    apply add_succ_repeat_fun; et.
    Unshelve. et.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open AddAMod AddIMod AddA.init_cond IstFull.
  Proof.
    init_sim.
    - split; eauto. iIntros "_". iModIntro.
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    - apply simF_succ; et.
    - apply simF_add; et.
  Qed.
End AddIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition ctxr (ge : GEnv.t) (sp : sp_type) (sp_pure sp_pure_fun : spl_type)
        (GEnvWF : GEnv.wf ge)
        (GEnvIncl : incl AddGEnv.t ge)
        (APCInSpPure : spl_sub APCA.Sp sp_pure)
        (SpPureInSp : sp_incl sp_pure sp)
        (repeatInSpPure: alist_find (Some RepeatHdr.repeat) sp_pure = Some (fsp_some (RepeatAS.repeat_spec sp_pure_fun ge)))
        (succInSpPureFun : alist_find (Some AddHdr.succ) sp_pure_fun = Some (fsp_some AddAS.succ_spec)) :
    ctx_refines
      ((AddA.t sp) ★ (RepeatA.t ge sp sp_pure_fun) ★ (APCA.t sp_pure sp), emp%I)
      ((AddI.t ge)    ★ (RepeatA.t ge sp sp_pure_fun) ★ (APCA.t sp_pure sp), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End AddIA. *)
