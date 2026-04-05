Require Import CRIS.

Require Import RepeatHeader RepeatI RepeatA.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module RepeatIA. Section RepeatIA.
  Import RepeatAS APC APCA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Context (genv : GEnv.t).
  Context (sp sp_pure sp_pure_fun : specmap).

  (* SPC Hypothesis *)
  Context (APCInSp : APCA.sp ⊆ sp).
  Context (SpPureInSp : sp_pure ⊆ sp).
  Context (SpPureFunInSpPure : sp_pure_fun ⊆ sp_pure).
  Context (repeatInSpPure : sp_pure.1 !! (fid RepeatHdr.repeat)
            = fsp_some (RepeatAS.repeat_spec sp_pure_fun genv)).

  (* Modules *)
  Local Definition APCA := (APCA.t sp_pure sp).
  Local Definition RepeatI := (RepeatI.t genv).
  Local Definition RepeatA := (RepeatA.t genv sp sp_pure_fun).
  Local Definition RepeatIMod := (RepeatI ★ APCA).
  Local Definition RepeatAMod := (RepeatA ★ APCA).

  (* IST *)
  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    (λ _ _, True)%I.
  Local Definition IstFull := (IstProd (IstSB RepeatA.(Mod.scopes) Ist) IstEq).

  Lemma simF_repeat : ISim.sim_fun open RepeatAMod RepeatIMod IstFull (fid RepeatHdr.repeat).
  Proof using APCInSp SpPureInSp SpPureFunInSpPure repeatInSpPure.
    (* Simulation Start *)
    cStartFunSim. rewrite /RepeatI.repeat.

    (* SRC: handle the precond of repeat *)
    cStepsS. destruct _q as [[n x] f_sem].
    iDestruct "ASM" as "%". cSimpl. dup H3. inv H4. rewrite /pure_body /cfunN.
    cStepsS.

    (* SRC: find apc in sp *)
    simpl_sp.

    (* TGT: handle input *)
    cStepsT. unfold assume. cForceT. cStepsT.

    (* case analysis: n *)
    destruct n as [|n'].

    (* CASE: n is 0 *)
    {
      (* TGT: cSteps tgt *)
      cSimpl. cStepsT.

      (* SRC: unfold APC *)
      cForcesS. iSplit; eauto.
      cStepsS. cInlineS. cStepsS. iDestruct "ASM" as "%". cSimpl.
      cStepsS. unfold APC. cForceS. cStepsS.

      (* SRC: change to skip *)
      apcS. cStepsS. cForcesS. iSplit; et. cStepsS. cForcesS. iSplit; et.

      (* prove the IST *)
      cStep. by iSplit.
    }

    (* CASE: n is S n' *)
    {
      (* TGT: load fn from function pointer *)
      destruct (Z_lt_le_dec (S n') 1) eqn:E; try lia.
      rewrite H2. cSimpl. cStepsT.

      (* SRC: unfold APC *)
      cForcesS. iSplit; eauto. cStepsS. 
      cInlineS. cStepsS. iDestruct "ASM" as "%". cSimpl.
      cStepsS. unfold APC. cForceS 2. cStepsS.

      (* cCall apc with fn *)
      apcCallWeak "IST"; et.
      { instantiate (1:= 1%ord). apply OrdArith.lt_from_nat. lia. }
      { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:=n'). apply OrdArith.lt_from_nat. lia. }
      iSplitL "IST".
      { unfold precond. ss. do 2 (iSplit; et). iExists (Ord.omega + n')%ord. iSplit; et. iPureIntro. apply OrdArith.add_base_l. }
      iIntros (???) "ISTPOST".
      iDestruct "ISTPOST" as "[IST %]". unfold postcond. subst.

      (* TGT: cSteps tgt *)
      cStepsT. cSimpl. cStepsT. assert (S n' - 1 = n')%Z as -> by lia.

      (* cCall apc with repeat *)
      apcCall "IST"; et.
      { instantiate (1 := 0%ord). apply OrdArith.lt_from_nat; lia. }
      { eapply Ord.lt_le_lt; et. apply OrdArith.lt_add_r. instantiate (1:= n'). apply OrdArith.lt_from_nat; lia. }
      { unfold precond. ss. iFrame. instantiate (1:= (n', (f_sem x), f_sem)). iPureIntro. split.
        - exists fn, fptr. hrepeat split; et. unfold_intrange_64; des_ifs_safe; hrepeat destruct Z_le_gt_dec; ss; try lia.
        - exists (Ord.omega + n')%ord. split; et. apply Ord.le_refl. }
      iIntros (???) "ISTPOST".
      unfold postcond. ss.
      iDestruct "ISTPOST" as "[IST %]". subst.

      (* TGT: cSteps tgt *)
      cStepsT. cSimpl. cStepsT.

      (* SRC: change to skip *)
      apcS. cStepsS. cForcesS. iSplit; et. cStepsS. cForcesS. iSplit; et.

      (* prove the IST *)
      cStep. by iSplit.
    }
    Unshelve. all: et. all: exact (0↑). 
  (*SLOW*)Qed.

  Lemma sim : ISim.t open RepeatAMod RepeatIMod RepeatA.init_cond IstFull.
  Proof.
    cStartModSim.
    - apply simF_repeat; eauto.
    - iIntros "_". rewrite /IstProd. eauto.
  Qed.
End RepeatIA. 

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.

  Definition ctxr (ge : GEnv.t) (sp sp_pure sp_pure_fun : specmap)
        (APCInSp : APCA.sp ⊆ sp)
        (SpPureInSp : sp_pure ⊆ sp)
        (SpPureFunInSpPure : sp_pure_fun ⊆ sp_pure)
        (repeatInSpPure: sp_pure.1 !! (fid RepeatHdr.repeat) = Some (fspec_to_rel (RepeatAS.repeat_spec sp_pure_fun ge))) :
    ctx_refines
      ((RepeatI.t ge)                ★ (APCA.t sp_pure sp), emp%I)
      ((RepeatA.t ge sp sp_pure_fun) ★ (APCA.t sp_pure sp), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End RepeatIA.
