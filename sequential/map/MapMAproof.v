From CRIS.common Require Import CRIS.
From CRIS.map Require Export MapHeader MapM MapA.

Module MapMA. Section MapMA.
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MAP: !mapGS}.
  Import MapA.

  Context (sp_s sp_t : specmap).
  Context (MapInSpS : MapA.sp ⊆ sp_s).
  Context (MapInSpT : MapM.sp ⊆ sp_t).

  Section SIM_FUNS.
    Context `{STATE : !stateGS Σ}.

    Definition Ist : iProp Σ :=
      (∃ f sz,
          MapA.v_map ↦src f↑ ∗ MapM.v_size ↦tgt sz↑ ∗
          MapM.v_map ↦tgt f↑ ∗
          (⌜f = (λ _ : Z, 0%Z) ∧ sz = 0%Z⌝ ∗ MapM.pending ∗ initial_map ∨
            pending ∗ auth_allocated f ∗ auth_unallocated sz))%I.

    Local Definition MapA := (MapA.t sp_s).
    Local Definition MapM := (MapM.t sp_t).

    Lemma simF_init :
      ⊢ ISim.sim_fun open MapA MapM Ist (fid MapHdr.init).
    Proof using MapInSpS MapInSpT.
      cStartFunSim. rewrite /MapM.init.

      cStepsS. rename _q into sz. iDestruct "ASM" as "[-> [[-> %range] P]]".

      (* SRC: handle the IST of Map and the precond of init *)
      iDestruct "IST" as (f ?) "(MAPS & SIZE & MAPT & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
      { iExFalso. iApply (pending_unique with "P P'"). }
      des; subst.

      (* TGT: prove the precond of init *)
      cForceT sz. cForceT ([Vint sz] ↑). cForceT.
      iSplitL "P0"; [iFrame; eauto|].

      (* TGT: handle the postcond of init *)
      cStepsT. iDestruct "GRT" as "(% & %)". subst.

      (* SRC: prove the postcond of init *)
      iMod (initialize with "INIT") as "(ALLOC & UNALLOC & INIT)".
      cForceS. cStepsS. cForceS. cForceS.
      iSplitL "INIT"; [iFrame; eauto|].

      (* prove the IST of Map *)
      cStep. iSplit; eauto.
      iExists _, _. iFrame. iRight. iFrame.
    (*SLOW*)Qed.

    Lemma simF_get :
      ⊢ ISim.sim_fun open MapA MapM Ist (fid MapHdr.get).
    Proof using MapInSpS MapInSpT.
      cStartFunSim. rewrite /MapM.get /get.

      cStepsS. destruct _q as [idx v]. iDestruct "ASM" as "(-> & (-> & MAP))".

      (* SRC: handle the IST of Map and the precond of get *)
      iDestruct "IST" as (f sz) "(MAPS & SIZE & MAPT & [(% & P0 & INIT)|(P' & B & U)])".
      { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
      des; subst. cStepsS.

      (* TGT: prove the precond of get *)
      cForceT idx. cForceT. cForceT.
      iSplit; first eauto.

      (* TGT : handle the body of get *)
      iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
      cStepsT.
      rewrite /assume; unshelve cForceT; eauto.

      (* TGT: handle the postcond of get *)
      iSplit; first eauto.
      cStepsT. iDestruct "GRT" as "(<- & _)".

      (* SRC: prove the postcond of get *)
      cForceS. cForceS.
      iPoseProof (auth_allocated_get with "B MAP") as "->".
      iSplitL "MAP". { iFrame. eauto. }

      (* prove the IST of Map *)
      cStep. iSplit; eauto.
      iExists _, _. iFrame. iRight. iFrame.
    (*SLOW*)Qed.

    Lemma simF_set :
      ⊢ ISim.sim_fun open MapA MapM Ist (fid MapHdr.set).
    Proof using MapInSpS MapInSpT.
      cStartFunSim. rewrite /MapM.set /set.

      (* SRC: handle the IST of Map and the precond of set *)
      do 2 cStepS.
      destruct _q as [[k w] v]. cStepsS.
      iDestruct "ASM" as "(-> & (-> & MAP))".
      iDestruct "IST" as (f sz) "(MAPS & SIZE & MAPT & [(% & P0 & INIT)|(P' & B & U)])".
      { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
      des; subst. cStepsS.

      (* TGT: prove the precond of set *)
      cForceT (k, v). cForceT. cForceT. iSplitR; first eauto.

      (* TGT : handle the body of set *)
      cStepsT. rewrite /assume.
      iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
      unshelve cForceT; eauto. iSplit; first eauto. cStepsT.

      (* TGT: handle the postcond of set *)
      iDestruct "GRT" as "(<- & _)".

      (* SRC : prove the postcond of set *)
      iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
      cForceS. cForceS. iSplitL "MAP". { iFrame. eauto. }

      (* prove the IST of Map *)
      cStep. iSplit; eauto.
      iExists _, _. iFrame. iRight. iFrame.
    (*SLOW*)Qed.

    Lemma simF_set_by_user :
      ⊢ ISim.sim_fun open MapA MapM Ist (fid MapHdr.set_by_user).
    Proof using MapInSpS MapInSpT.
      cStartFunSim. rewrite /MapM.set_by_user /set_by_user. cHideS. cHideT.

      (* SRC: handle the IST of Map and the precond of set_by_user *)
      do 2 cStepS. destruct _q as [k w]. cStepsS.
      iDestruct "ASM" as "(-> & (-> & MAP))". cStepsS.

      (* TGT: prove the precond of set_by_user *)
      cForceT. cForceT. cForceT. iSplitR. { eauto. }

      (* process an input *)
      cStepsT. cStep.

      (* TGT: handle the precond of set *)
      cStepsT. cSimpl. cStepsT. destruct _q as [? ?]; iDestruct "GRT" as "%". des; cSimpl.

      (* SRC: prove the precond of set *)
      cStepsS. cSimpl. cForceS (_,_,_). cForceS. cForceS.
      iSplitL "MAP". { iFrame. eauto. }

      (* make a cCall to set *)
      cCall "IST" as (ret) "IST".

      (* SRC: handle the postcond of set *)
      cStepsS. iDestruct "ASM" as "(-> & (-> & MAP))". cStepsS; cStepsT.

      (* TGT: prove the postcond of set *)
      cForceT. cForceT. iSplitR. { iFrame. eauto. }

      (* TGT: handle the postcond of set_by_user *)
      cStepsT. iDestruct "GRT" as "(<- & _)".

      (* SRC: prove the postcond of set_by_user *)
      cForceS. cForceS. iSplitL "MAP". { iFrame. eauto. }

      (* prove the IST of Map *)
      cStep. iFrame. eauto.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim : MapA.init_cond ⊢ ISim.t open MapA MapM.
  Proof using MapInSpS MapInSpT.
    cStartModSim (fun STATE : stateGS Σ => Ist (STATE := STATE)).
    { iDestruct "INIT" as "[INIT P]".
      rewrite /state_init_src /state_init_tgt.
      iDestruct "SRC" as "[SRC _]". iDestruct "TGT" as "[TGT _]".
      assert (SRCEQ :
        state_slice (list_to_set (Mod.scopes MapA))
          (Mod.initial_st MapA) =
          {[MapA.v_map := (λ _ : Z, 0%Z)↑]}).
      { rewrite /MapA /MapA.t /SMod.to_mod /MapA.smod
          /state_slice /live_state /=. vm_compute. reflexivity. }
      assert (TGTEQ :
        state_slice (list_to_set (Mod.scopes MapM))
          (Mod.initial_st MapM) =
          {[MapM.v_size := 0%Z↑; MapM.v_map := (λ _ : Z, 0%Z)↑]}).
      { rewrite /MapM /MapM.t /SMod.to_mod /MapM.smod
          /state_slice /live_state /=. vm_compute. reflexivity. }
      iEval (rewrite SRCEQ big_sepM_singleton) in "SRC".
      iEval (rewrite TGTEQ big_sepM_insert) in "TGT".
      iDestruct "TGT" as "[SIZE MAPT]".
      iEval (rewrite big_sepM_singleton) in "MAPT".
      iExists (λ _ : Z, 0%Z), 0%Z. iFrame. iLeft. iFrame.
      iPureIntro; split; reflexivity. }
    { iApply simF_init. }
    { iApply simF_get. }
    { iApply simF_set. }
    { iApply simF_set_by_user. }
  Qed.

  Lemma ctxr :
    MapA.init_cond ⊢ ctx_refines (MapM.t sp_t) (MapA.t sp_s).
  Proof.
    etrans; first (eapply MapMA.sim; eauto).
    eapply main_adequacy.
  Qed.
End MapMA. End MapMA.
