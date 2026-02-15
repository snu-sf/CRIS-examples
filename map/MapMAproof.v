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
    iStartSim.

    steps_l. rename _q into sz. iDestruct "ASM" as "[-> [[-> %range] P]]".

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (f ?) "(% & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    des; subst.
    
    (* TGT: prove the precond of init *)
    force_r sz. force_r ([Vint sz] ↑). force_r.
    iSplitL "P0"; [iFrame; eauto|].

    (* TGT: handle the postcond of init *)
    steps_r. iDestruct "GRT" as "(% & %)". subst.
    
    (* SRC: prove the postcond of init *)
    iMod (initialize with "INIT") as "(ALLOC & UNALLOC & INIT)".
    force_l. steps_l. force_l. force_l.
    iSplitL "INIT"; [iFrame; eauto|].
    
    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplitR; eauto. iRight. iFrame.
  (*SLOW*)Qed.

  Lemma simF_get : ISim.sim_fun open MapA MapM Ist (fid MapHdr.get).
  Proof using MapInSpS MapInSpT.
    iStartSim.

    steps_l. destruct _q as [idx v]. iDestruct "ASM" as "(-> & (-> & MAP))".

    (* SRC: handle the IST of Map and the precond of get *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des; subst. steps_l.

    (* TGT: prove the precond of get *)
    force_r idx. force_r. force_r.
    iSplit; first eauto.

    (* TGT : handle the body of get *)
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    steps_r. rewrite /assume; unshelve force_r; eauto.

    (* TGT: handle the postcond of get *)
    steps_r. iDestruct "GRT" as "(<- & _)".

    (* SRC: prove the postcond of get *)
    force_l. force_l.
    iPoseProof (auth_allocated_get with "B MAP") as "->".
    iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*SLOW*)Qed.

  Lemma simF_set : ISim.sim_fun open MapA MapM Ist (fid MapHdr.set).
  Proof using MapInSpS MapInSpT.
    iStartSim.

    (* SRC: handle the IST of Map and the precond of set *)
    do 2 step_l.
    destruct _q as [[k w] v]. steps_l.
    iDestruct "ASM" as "(-> & (-> & MAP))".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des; subst. steps_l.

    (* TGT: prove the precond of set *)
    force_r (k, v). force_r. force_r. iSplitR; first eauto.

    (* TGT : handle the body of set *)
    steps_r. rewrite /assume.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    unshelve force_r; eauto. steps_r.

    (* TGT: handle the postcond of set *)
    iDestruct "GRT" as "(<- & _)".
    
    (* SRC : prove the postcond of set *)
    iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
    force_l. force_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*SLOW*)Qed.

  Lemma simF_set_by_user : ISim.sim_fun open MapA MapM Ist (fid MapHdr.set_by_user).
  Proof using MapInSpS MapInSpT.
    iStartSim.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    do 2 step_l. destruct _q as [k w]. steps_l.
    iDestruct "ASM" as "(-> & (-> & MAP))". steps_l.

    (* TGT: prove the precond of set_by_user *)
    force_r. force_r. force_r. iSplitR. { eauto. }

    (* process an input *)
    steps_r. step.

    (* TGT: handle the precond of set *)
    steps_r. simpl_sp. steps_r. destruct _q as [? ?]; iDestruct "GRT" as "%". des; hss.
    
    (* SRC: prove the precond of set *)
    steps_l. simpl_sp. force_l (_,_,_). force_l. force_l.
    iSplitL "MAP". { iFrame. eauto. }

    (* make a call to set *)
    call "IST".

    (* SRC: handle the postcond of set *)
    clear_st; iIntros (ret st_src st_tgt) "IST".
    steps_l. iDestruct "ASM" as "(-> & (-> & MAP))". steps_l; steps_r.

    (* TGT: prove the postcond of set *)
    force_r. force_r. iSplitR. { iFrame. eauto. }

    (* TGT: handle the postcond of set_by_user *)
    steps_r. iDestruct "GRT" as "(<- & _)".
    
    (* SRC: prove the postcond of set_by_user *)
    force_l. force_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MapA MapM MapA.init_cond Ist.
  Proof using MapInSpS MapInSpT.
    init_sim.
    { iIntros "(IST & P)"; s. iExists _, _. iSplit; eauto. iLeft. iFrame. eauto. }
    { apply simF_init; eauto. }
    { apply simF_get; eauto. }
    { apply simF_set; eauto. }
    { apply simF_set_by_user; eauto. }
  Qed.

  Lemma ctxr :
    ctx_refines
      (MapA.t sp_s, MapA.init_cond)
      (MapM.t sp_t, emp%I).
  Proof. eapply main_adequacy, MapMA.sim; eauto. Qed.
End MapMA. End MapMA.
