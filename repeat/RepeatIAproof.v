Require Import CRIS.

Require Import RepeatHeader RepeatI RepeatA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module RepeatIA. Section RepeatIA.
  Import RepeatAS APC APCA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Context (genv : GEnv.t).
  Context (sp sp_pure sp_pure_fun : string → option fspec). (* sp_pure_fun stores fspecs which repeat use *)

  (* SPC Hypothesis *)
  Context (APCInSpPure : sp_incl APCA.Sp sp_pure).
  Context (SpPureInSp : sp_sub sp_pure sp).
  Context (SpPureFunInSpPure : sp_sub sp_pure_fun sp_pure).
  Context (repeatInSpPure : sp_pure RepeatHdr.repeat = Some (RepeatAS.repeat_spec sp_pure_fun genv)). (* to avoid recursive definition of SpPure *)

  (* Modules *)
  Local Definition APCA := (APCA.t sp_pure sp).
  Local Definition RepeatI := (RepeatI.t genv).
  Local Definition RepeatA := (RepeatA.t genv sp sp_pure_fun).
  Local Definition RepeatIMod := (RepeatI ★ APCA).
  Local Definition RepeatAMod := (RepeatA ★ APCA).

  (* IST *)
  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_src st_tgt, emp%I).
  Local Definition IstFull := (IstProd (IstSB RepeatA.(HMod.scopes) Ist) IstEq).

  Lemma simF_repeat : HSim.sim_fun open RepeatAMod RepeatIMod IstFull RepeatHdr.repeat.
  Proof using _sinvG APCInSpPure SpPureInSp SpPureFunInSpPure repeatInSpPure.
    (* Simulation Start *)
    init_simF.

    (* SRC: handle the precond of repeat *)
    steps_l. rename q2 into f_sem, q3 into n, q4 into x.
    iDestruct "ASM" as "%". hss. dup H3. inv H3. steps_l.

    (* TGT: handle input *)
    steps_r. unfold assume. force_r. steps_r.

    (* case analysis: n *)
    destruct n as [|n'].

    (* CASE: n is 0 *)
    {
      (* TGT: steps tgt *)
      hss. steps_r.

      (* SRC: unfold APC *)
      forces_l. iSplit. { iPureIntro. apply SpPureInSp. apply APCInSpPure. unfold APCA.Sp. unseal CRIS. et. }
      steps_l. forces_l. iSplit; et. inline_l. steps_l. iDestruct "ASM" as "%". hss.
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
      force_l. iSplit. { iPureIntro. apply SpPureInSp. apply APCInSpPure. unfold APCA.Sp. unseal CRIS. et. }
      steps_l. forces_l. iSplit; et. steps_l.
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
  (*FAST*)Qed.

  Theorem sim : HSim.t open RepeatAMod RepeatIMod RepeatA.init_cond IstFull.
  Proof.
    init_sim.
    - iIntros "_". repeat iExists [].
      repeat (iSplit; eauto); iPureIntro; ss.
    - apply simF_repeat; eauto.
  Qed.
End RepeatIA. 

Section ctxr.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Definition ctxr (ge : GEnv.t) (sp sp_pure sp_pure_fun : string → option fspec)
        (APCInSpPure : sp_incl APCA.Sp sp_pure)
        (SpPureInSp : sp_sub sp_pure sp)
        (SpPureFunInSpPure : sp_sub sp_pure_fun sp_pure)
        (repeatInSpPure: sp_pure RepeatHdr.repeat = Some (RepeatAS.repeat_spec sp_pure_fun ge)) :
    ctx_refines
      ((RepeatA.t ge sp sp_pure_fun) ★ (APCA.t sp_pure sp), emp%I)
      ((RepeatI.t ge)                    ★ (APCA.t sp_pure sp), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End RepeatIA.
