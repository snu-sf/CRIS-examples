Require Import CRIS.
Require Export MapHeader MapM MapA.

Module MapMA. Section MapMA.
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MAP: !mapGS}.
  Import MapA.

  Context (sp_s sp_t : specmap).
  Context (MapInSpS : MapA.sp ⊆ sp_s).
  Context (MapInSpT : MapM.sp ⊆ sp_t).

  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
      ∃ f sz,
        ⌜st_src = {[MapA.v_map # f↑]} ∧
        st_tgt = {[MapM.v_size # sz↑; MapM.v_map # f↑]}⌝ ∗
        (⌜f = (λ _ : Z, 0%Z) ∧ sz = 0%Z⌝ ∗ MapM.pending ∗ initial_map ∨
          pending ∗ auth_allocated f ∗ auth_unallocated sz))%I.

  Local Definition MapA := (MapA.t sp_s).
  Local Definition MapM := (MapM.t sp_t).

  Lemma simF_init : ISim.sim_fun open MapA MapM Ist (fid MapHdr.init).
  Proof using MapInSpS MapInSpT.
    cStartFunSim. rewrite /MapM.init.

    cStepsS. rename _q into sz. iDestruct "ASM" as "[-> [[-> %range] P]]".

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (f ?) "(% & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
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
    iExists _, _. iSplitR; eauto. iRight. iFrame.
  (*SLOW*)Qed.

  Lemma simF_get : ISim.sim_fun open MapA MapM Ist (fid MapHdr.get).
  Proof using MapInSpS MapInSpT.
    cStartFunSim. rewrite /MapM.get /get.

    cStepsS. destruct _q as [idx v]. iDestruct "ASM" as "(-> & (-> & MAP))".

    (* SRC: handle the IST of Map and the precond of get *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des; subst. cStepsS.

    (* TGT: prove the precond of get *)
    cForceT idx. cForceT. cForceT.
    iSplit; first eauto.

    (* TGT : handle the body of get *)
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    cStepsT. rewrite /assume; unshelve cForceT; eauto.

    (* TGT: handle the postcond of get *)
    cStepsT. iDestruct "GRT" as "(<- & _)".

    (* SRC: prove the postcond of get *)
    cForceS. cForceS.
    iPoseProof (auth_allocated_get with "B MAP") as "->".
    iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    cStep. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*SLOW*)Qed.

  Lemma simF_set : ISim.sim_fun open MapA MapM Ist (fid MapHdr.set).
  Proof using MapInSpS MapInSpT.
    cStartFunSim. rewrite /MapM.set /set.

    (* SRC: handle the IST of Map and the precond of set *)
    do 2 cStepS.
    destruct _q as [[k w] v]. cStepsS.
    iDestruct "ASM" as "(-> & (-> & MAP))".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des; subst. cStepsS.

    (* TGT: prove the precond of set *)
    cForceT (k, v). cForceT. cForceT. iSplitR; first eauto.

    (* TGT : handle the body of set *)
    cStepsT. rewrite /assume.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    unshelve cForceT; eauto. cStepsT.

    (* TGT: handle the postcond of set *)
    iDestruct "GRT" as "(<- & _)".
    
    (* SRC : prove the postcond of set *)
    iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
    cForceS. cForceS. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    cStep. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*SLOW*)Qed.

  Lemma simF_set_by_user : ISim.sim_fun open MapA MapM Ist (fid MapHdr.set_by_user).
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
    cStepsT. simpl_sp. cStepsT. destruct _q as [? ?]; iDestruct "GRT" as "%". des; cSimpl.
    
    (* SRC: prove the precond of set *)
    cStepsS. simpl_sp. cForceS (_,_,_). cForceS. cForceS.
    iSplitL "MAP". { iFrame. eauto. }

    (* make a cCall to set *)
    cCall "IST" as (ret st_src st_tgt) "IST".

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

  Lemma sim : ISim.t open MapA MapM MapA.init_cond Ist.
  Proof using MapInSpS MapInSpT.
    cStartModSim.
    { iIntros "(IST & P)"; s. iExists _, _. iSplit; eauto. iLeft. iFrame. eauto. }
    { apply simF_init; eauto. }
    { apply simF_get; eauto. }
    { apply simF_set; eauto. }
    { apply simF_set_by_user; eauto. }
  Qed.

  Lemma ctxr :
    ctx_refines
      (MapM.t sp_t, emp%I)
      (MapA.t sp_s, MapA.init_cond).
  Proof. eapply main_adequacy, MapMA.sim; eauto. Qed.
End MapMA. End MapMA.
