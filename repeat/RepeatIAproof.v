Require Import CRIS.

Require Import RepeatHeader RepeatI RepeatA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module RepeatIA. Section RepeatIA.
  Import RepeatAS APC APCA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Context (genv : GEnv.t).
  Context (sp : sp_type).
  Context (sp_pure sp_pure_fun : spl_type). (* sp_pure_fun stores fspecs which repeat use *)

  (* SPC Hypothesis *)
  Context (APCInSpPure : spl_sub APCA.Sp sp_pure).
  Context (SpPureInSp : sp_incl sp_pure sp).
  Context (SpPureFunInSpPure : spl_sub sp_pure_fun sp_pure).
  Context (repeatInSpPure : alist_find (Some RepeatHdr.repeat) sp_pure 
            = Some (fsp_some (RepeatAS.repeat_spec sp_pure_fun genv))). (* to avoid recursive definition of SpPure *)

  (* Modules *)
  Local Definition APCA := (APCA.t sp_pure sp).
  Local Definition RepeatI := (RepeatI.t genv).
  Local Definition RepeatA := (RepeatA.t genv sp sp_pure_fun).
  Local Definition RepeatIMod := (RepeatI ★ APCA).
  Local Definition RepeatAMod := (RepeatA ★ APCA).

  (* IST *)
  Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    (λ st_src st_tgt, emp%I).
  Local Definition IstFull := (IstProd (IstSB RepeatA.(Mod.scopes) Ist) IstEq).

  Lemma simF_repeat : ISim.sim_fun open RepeatAMod RepeatIMod RepeatA.init_cond IstFull (Some RepeatHdr.repeat).
  Proof using _crisG APCInSpPure SpPureInSp SpPureFunInSpPure repeatInSpPure.
    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of repeat *)
    steps_l. rename _q2 into f_sem, _q3 into n, _q4 into x.
    iDestruct "ASM" as "%". hss. dup H3. inv H3. steps_l.

    (* SRC: find apc in sp *)
    assert (SPAPC: sp APCHdr.apc = fsp_some apc_spec).
    { apply SpPureInSp. apply APCInSpPure. rewrite /Sp. unseal CRIS. ss. }
    rewrite SPAPC.

    (* TGT: handle input *)
    steps_r. unfold assume. force_r. steps_r.

    (* case analysis: n *)
    destruct n as [|n'].

    (* CASE: n is 0 *)
    {
      (* TGT: steps tgt *)
      hss. steps_r.

      (* SRC: unfold APC *)
      forces_l. iSplit; eauto.
      steps_l. inline_l. steps_l. iDestruct "ASM" as "%". hss.
      steps_l. unfold APC. force_l. steps_l.

      (* SRC: change to skip *)
      apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

      (* prove the IST *)
      step. by iSplit.
    }

    (* CASE: n is S n' *)
    {
      (* TGT: load fn from function pointer *)
      destruct (Z_lt_le_dec (S n') 1) eqn:E; try lia.
      rewrite H2. hss. steps_r.

      (* SRC: unfold APC *)
      forces_l. iSplit; eauto. steps_l. 
      inline_l. steps_l. iDestruct "ASM" as "%". hss.
      steps_l. unfold APC. force_l 2. steps_l.

      (* call apc with fn *)
      apc_call_weaker "IST"; et.
      { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
      { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:=n'). apply OrdArith.lt_from_nat. lia. }
      { unfold precond. ss. do 2 (iSplit; et). iExists (Ord.omega + n')%ord. iSplit; et. iPureIntro. apply OrdArith.add_base_l. }
      iDestruct "ISTPOST" as "[IST %]". unfold postcond. subst.

      (* TGT: steps tgt *)
      steps_r. hss. steps_r. assert (S n' - 1 = n')%Z as -> by lia.

      (* call apc with repeat *)
      apc_call "IST"; et.
      { instantiate (1 := 0%ord). apply OrdArith.lt_from_nat; lia. }
      { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:= n'). apply OrdArith.lt_from_nat; lia. }
      { unfold precond. ss. iFrame. instantiate (1:= (n', (f_sem x), f_sem)). iPureIntro. split.
        - exists fn, fptr. hrepeat split; et. unfold_intrange_64; des_ifs_safe; hrepeat destruct Z_le_gt_dec; ss; try lia.
        - exists (Ord.omega + n')%ord. split; et. apply Ord.le_refl. }
      unfold postcond. ss.
      iDestruct "ISTPOST" as "[IST %]". subst.

      (* TGT: steps tgt *)
      steps_r. hss. steps_r.

      (* SRC: change to skip *)
      apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iSplit; et.

      (* prove the IST *)
      step. by iSplit.
    }
    Unshelve. all: et. exact (0↑).
  (*SLOW*)Qed.

  Theorem sim : ISim.t open RepeatAMod RepeatIMod RepeatA.init_cond IstFull.
  Proof.
    init_sim.
    - split; eauto. iIntros "_". iModIntro. repeat (iSplit; eauto); iPureIntro; ss.
    - apply simF_repeat; eauto.
  Qed.
End RepeatIA. 

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition ctxr (ge : GEnv.t) (sp : sp_type) (sp_pure sp_pure_fun : spl_type)
        (APCInSpPure : spl_sub APCA.Sp sp_pure)
        (SpPureInSp : sp_incl sp_pure sp)
        (SpPureFunInSpPure : spl_sub sp_pure_fun sp_pure)
        (repeatInSpPure: alist_find (Some RepeatHdr.repeat) sp_pure = Some (fsp_some (RepeatAS.repeat_spec sp_pure_fun ge))) :
    ctx_refines
      ((RepeatA.t ge sp sp_pure_fun) ★ (APCA.t sp_pure sp), emp%I)
      ((RepeatI.t ge)                    ★ (APCA.t sp_pure sp), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End RepeatIA.
