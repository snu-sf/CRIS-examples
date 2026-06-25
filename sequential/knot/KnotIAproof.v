Require Import CRIS.
Require Import MemTactics.
Require Import APCHeader APC APCA APCTactics Tactics.
Require Import KnotI KnotA.

Module KnotIA. Section KnotIA.
  Import KnotA APC APCA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _KNOT: !knotGS}.

  (* 1. global environment *)
  Context (genv: GEnv.t).

  (* 2. spec maps *)
  Context (sp sp_rec sp_fun sp_pure : specmap).

  (* 3. hypotheses for genv *)
  Context (GEnvWF : GEnv.wf genv).
  Context (GEnvIncl : incl KnotGEnv.t genv).

  (* 4. hypotheses for sp *)
  Context (RecInSp: knot_rec_sp ⊆ sp_rec).
  Context (APCInSp: APCA.sp ⊆ sp).

  (* 5. hypotheses for pure sp *)
  Context (FunInPure: sp_fun ⊆ sp_pure).
  Context (PureInSp : sp_pure ⊆ sp).

  Definition Ist : ist_type Σ := λ _ _,
    (∃ (f' : optionO (natO -d> natO)) (fb' : val),
        (⌜∀ f (EQ: f' ≡ (Some f: optionO (natO -d> natO))),
            ∃ fb,
              (<<BLK: fb' = Vptr (fb, 0%Z)>>) /\
              (<<FN: fb_has_spec_in genv sp_fun fb (fun_gen genv sp_rec f)>>)⌝)
          ∗ (knot_full f')
          ∗ (var_points_to genv KnotHdr._f.1 fb'))%I.

  Local Notation APCA := (APCA.t sp_pure sp).
  Local Notation MemA := (MemA.t ∅).
  Local Notation KnotA := (KnotA.t genv sp_rec sp_fun sp).
  Local Notation KnotAMod := (KnotA ★ MemA ★ APCA).
  Local Notation KnotIMod := ((KnotI.t genv) ★ MemA ★ APCA).
  Local Notation IstFull := (IstProd (IstSB KnotA.(Mod.scopes) Ist) IstEq).

  Lemma simF_rec : ISim.sim_fun open KnotAMod KnotIMod IstFull (fid KnotHdr.rec).
  Proof using GEnvWF GEnvIncl RecInSp APCInSp FunInPure PureInSp.
    cStartFunSim. rewrite /KnotI.recF.

    (* SKINCL - SkEnv id2blk *)
    pose proof (@CEnv.incl_incl_env KnotGEnv.t genv) as INCLENV.
    (* unfold KnotIMod in GEnvIncl; ss. apply (incl_app_inv KnotGEnv _) in GEnvIncl. des. *)
    unfold KnotGEnv.t in GEnvIncl.
    eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotHdr._f.1 (Gvar 0%Z)↑) as SF.
    specialize (@GEnvIncl KnotHdr.rec.1 Gfun↑) as SR.
    hexploit SF; [right; right; left; ss|intros [blk_sf SKINCL_F]].
    hexploit SR; [right; left; ss|intros [blk_sr SKINCL_REC]]. clear SF SR INCLENV.

    (* SKWF - SkEnv blk2id *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    (* specialize (GEnvWF KnotHdr.rec blk_sr). *)
    apply GEnvWF in SKINCL_REC; et. apply GEnvWF in SKINCL_F as FINDR.

    (* Simulation Start *)
    (* SRC: precondition *)
    cStepsS. destruct _q as [f o]. iDestruct "ASM" as "(((-> & %) & FG) & %Q)". cStepsT.
    iDestruct "IST" as (? ? ? ?) "(%ST & [% IST] & %E)"; des; subst.
    iDestruct "IST" as (? ?) "(%HIN & FL & VF)".

    (* RA: Set _f as a funciton pointer whose spec is "_f_spec" *)
    iPoseProof (knot_ra_merge with "FL FG") as "<-".
    
    (* TGT: get a block of _f *)
    rewrite SKINCL_F. cStepsT.

    (* TGT: load the function at the block of _f by inlining "load" *)
    iEval (rewrite /var_points_to SKINCL_F) in "VF". mLoadT "VF".
    hexploit (HIN f); eauto; intros [fb [EQ [? FBLOCK]]]; rewrite EQ /=.

    (* TGT: get blocks of the function pointer and "rec" *)
    cStepsT. rewrite FBLOCK. cStepsT.
    eapply GEnvWF in SKINCL_REC; rewrite SKINCL_REC. cStepsT.

    (* SRC: unfold APC *)
    rewrite /pure_body.
    cStepsS. cSimpl. cForceS. cForcesS. iSplit; eauto. cStepsS.
    cInlineS. cStepsS. iDestruct "ASM" as "[-> <-]".
    cStepsS. unfold apc_body, APC. cForceS 1. cStepsS. 

    (* cCall apc with fn *)
    pose proof SPEC as SPEC1. inv SPEC1.
    iApply wsim_apc_src_call_tgt_weaker; [ | | |cSimpl| | |iSplitL "FL FG VF"]; eauto.
    { instantiate (1 := 0). apply OrdArith.lt_from_nat. nia. }
    { instantiate (1:= (2 * o)). eapply Ord.lt_le_lt; et.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia.
    }
    { iSplitR "FL VF".
      - ss. iFrame. iSplit.
        + iPureIntro. eexists; esplits; et. econs; et.
          { eapply GEnvWF; eauto. }
          econs; [cSimpl; eauto|].
          iIntros (??) "% %% F !>"; iExists _, _; iSplit; [done|iSplitL "F"; [done|iIntros "%% $//"]].
        + iPureIntro. eexists; esplits; et. rewrite -OrdArith.mult_from_nat. apply OrdArith.le_from_nat. nia. 
      - iExists _, _, _, _. repeat (iSplit; et). iExists (Some f), _. iSplit.
        + iPureIntro. intros ? temp; inv temp; esplits; et. econs; eauto.
        + unfold var_points_to. rewrite SKINCL_F. iFrame.
    }
    clear_st. iIntros (st_src st_tgt ret) "IST".
    iDestruct "IST" as "[IST [-> FG]]". cStepsT.

    (* SRC: change to skip *)
    iApply wsim_apc_src. cStepsS. cForcesS. iSplit; et. cStepsS. cForcesS. iSplitL "FG"; iFrame; et.

    cStep. by iFrame.
    Unshelve. all: try exact (tt↑).
  (*SLOW*)Qed.

  Lemma simF_knot : ISim.sim_fun open KnotAMod KnotIMod IstFull (fid KnotHdr.knot).
  Proof using GEnvWF GEnvIncl RecInSp APCInSp FunInPure PureInSp.
    cStartFunSim. rewrite /KnotI.knotF.

    (* SKINCL *)
    pose proof (@CEnv.incl_incl_env KnotGEnv.t genv) as INCLENV.
    unfold KnotGEnv.t in GEnvIncl. eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotHdr._f.1 (Gvar 0%Z)↑) as SF.
    specialize (@GEnvIncl KnotHdr.rec.1 Gfun↑) as SR.
    hexploit SF; [right; right; left; ss|intro SKINCL_F].
    hexploit SR; [right; left; ss|intro SKINCL_REC]. des. clear SF SR INCLENV.

    (* SKWF *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotHdr.rec.1 blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDR.

    (* SRC: precondition *)
    cStepsS. rename _q into new_spec.
    iDestruct "ASM" as "(%Q & (%FB & [%old OLD]))". des; subst. cStepsT.
    iDestruct "IST" as (? ? ? ?) "(%ST & [% IST] & %E)"; des; subst.
    iDestruct "IST" as (? ?) "(%HIN & FL & VF)".

    (* RA: unify the infomation of f_spec *)
    iPoseProof (knot_ra_merge with "FL OLD") as "->".
    (* iPoseProof (REFL with "FL") as "FL". *)
    rewrite FIND0. cStepsT.
    
    (* TGT: save a function by calling "store" *)
    rewrite /var_points_to FIND0. mStoreT "VF".

    (* RA: update spec *)
    rewrite FINDR. cStepsT.
    iMod (knot_update _ (Some new_spec) with "[FL OLD]") as "[FL FG]"; first iFrame.
    (* iCombine "FL OLD" as "SPEC". *)
    (* iPoseProof (auth_excl_both_update with "SPEC") as ">[FL FG]". *)

    (* finish reasoning *)
    cForceS. cStepsS. cForceS. cForceS.
    iSplitL "FG".
    { iSplitR; et. iSplitR; eauto. iPureIntro. eexists. esplit; et. econs; et.
      econs; [cSimpl; ss|].
      iIntros (??) "% %% F !>"; iExists _, _; iSplit; [done|iSplitL "F"; [done|iIntros "%% $//"]].
    }
    cStep. iSplit; et.

    (* check IST *)
    inv FB0. des.
    iExists _, _, _, _. iSplit; et. iSplit; et. iSplit; et. unfold Ist, inv.
    iExists (Some new_spec), _. iSplit; iFrame; et.
    { iPureIntro. ii. eexists. esplits; et. econs; et. inv EQ. et. }
    { unfold var_points_to. des_ifs. }
  Qed.

  Lemma sim : ISim.t open KnotAMod KnotIMod (KnotA.init_cond genv) IstFull.
  Proof.
    cStartModSim.
    { apply simF_rec. }
    { apply simF_knot. }
    { iIntros "[VF FL]". iExists _, _, _, _. iSplit; et. iSplit; eauto.
      iSplit; iFrame; et. iPureIntro. ii. inv EQ.
    }
  Qed.

  Lemma ctxr :
    ctx_refines
      (KnotI.t genv ★ MemA ★ APCA.t sp_pure sp,                  emp%I)
      (KnotA.t genv sp_rec sp_fun sp ★ MemA ★ APCA.t sp_pure sp, KnotA.init_cond genv).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End KnotIA. End KnotIA.
