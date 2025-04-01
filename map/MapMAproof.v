Require Import CRIS.

Require Import MapHeader MapM MapA.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MapMA. Section MapMA.
  Import MapAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ}.
  Context (u_a u_m : univ_id).
  Context `(u_a > u_m).

  Context (sp_s sp_t : string → option fspec).
  Context (MapInSpS : sp_incl (MapAS.sp u_a) sp_s).
  Context (MapInSpT : sp_incl (MapMS.sp u_m) sp_t).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_src st_tgt,
      ∃ f sz,
        ⌜st_src = [(MapA.v_map, f↑)] ∧ st_tgt = [(MapM.v_size, sz↑); (MapM.v_map, f↑)]⌝
        ∗ (⌜f = (λ _ : Z, 0%Z) ∧ sz = 0%Z⌝
            ∗ MapMS.pending
            ∗ initial_map
          ∨ pending
            ∗ auth_allocated f
            ∗ auth_unallocated sz))%I.

  Local Definition MapA := (MapA.t u_a sp_s).
  Local Definition MapM := (MapM.t u_m sp_t).

  Lemma simF_init : HSim.sim_fun open MapA MapM Ist MapHdr.init.
  Proof.
    init_simF u_a u_m.

    steps_l.
    iDestruct "ASM" as "[[[-> %range] P] ->]".

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT) | (P' & B & U)])"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    des. hss. rename q into sz.
    
    (* TGT: prove the precond of init *)
    step_r. force_r sz. force_r ([Vint sz] ↑). force_r.
    iSplitL "P0". { iFrame. eauto. }

    (* TGT: handle the postcond of init *)
    hss. steps_r. iDestruct "GRT" as "(_ & %)". hss.
    
    (* SRC: prove the postcond of init *)
    iMod (initialize with "INIT") as "(ALLOC & UNALLOC & INIT)".
    force_l. steps_l. force_l. force_l.
    iSplitL "INIT". { iFrame. eauto. }
    
    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplitR; eauto. iRight. iFrame.
  (*FAST*)Qed.

  Lemma simF_get : HSim.sim_fun open MapA MapM Ist MapHdr.get.
  Proof.
    init_simF u_a u_m.

    steps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    rename q1 into k.

    (* SRC: handle the IST of Map and the precond of get *)
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    hss. steps_l. hss. steps_l.

    (* TGT: prove the precond of get *)
    step_r. force_r k. force_r. force_r.
    iSplit; first eauto.

    (* TGT : handle the body of get *)
    hss. steps_r. hss. steps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    force_r; first eauto.

    (* TGT: handle the postcond of get *)
    steps_r. hss. steps_r. iDestruct "GRT" as "(_ & <-)".

    (* SRC: prove the postcond of get *)
    force_l. force_l.
    iPoseProof (auth_allocated_get with "B MAP") as "->".
    iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*FAST*)Qed.

  Lemma simF_set : HSim.sim_fun open MapA MapM Ist MapHdr.set.
  Proof.
    init_simF u_a u_m.

    (* SRC: handle the IST of Map and the precond of set *)
    do 2 step_l.
    destruct q as [[k w] v]. steps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    iDestruct "IST" as (f sz) "(% & [(% & P0 & INIT)|(P' & B & U)])".
    { iExFalso. iApply (initial_map_points_to with "INIT MAP"). }
    des. hss. steps_l. hss. steps_l. hss.

    (* TGT: prove the precond of set *)
    step_r. force_r (k, v). force_r. force_r. iSplitR; first eauto.

    (* TGT : handle the body of set *)
    hss. steps_r. hss. steps_r.
    iPoseProof (auth_unallocated_points_to with "U MAP") as "%".
    force_r; first done. steps_r. hss. steps_r.

    (* TGT: handle the postcond of set *)
    iDestruct "GRT" as "(_ & <-)".
    
    (* SRC : prove the postcond of set *)
    iPoseProof (auth_allocated_set with "B MAP") as ">(B & MAP)".
    force_l. force_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. iSplit; eauto.
    iExists _, _. iSplit; eauto. iRight. iFrame.
  (*FAST*)Qed.

  Lemma simF_set_by_user : HSim.sim_fun open MapA MapM Ist MapHdr.set_by_user.
  Proof.
    init_simF u_a u_m.

    (* SRC: handle the IST of Map and the precond of set_by_user *)
    do 2 step_l. destruct q as [k w]. steps_l.
    iDestruct "ASM" as "((-> & MAP) & ->)".
    hss. steps_l.

    (* TGT: prove the precond of set_by_user *)
    step_r. force_r. force_r. force_r. hss. iSplitR. { eauto. }

    (* process an input *)
    steps_r. step.

    (* TGT: handle the precond of set *)
    steps_r. iDestruct "GRT" as "%". des. hss.
    
    (* SRC: prove the precond of set *)
    steps_l. force_l (_,_,_). force_l. force_l.
    iSplitL "MAP". { iFrame. eauto. }

    (* make a call to set *)
    call "IST".

    (* SRC: handle the postcond of set *)
    steps_l. iDestruct "ASM" as "((-> & MAP) & ->)". hss.

    (* TGT: prove the postcond of set *)
    steps_l. force_r. force_r. iSplitR. { iFrame. eauto. }

    (* TGT: handle the postcond of set_by_user *)
    steps_r. hss. steps_r. iDestruct "GRT" as "(_ & <-)".
    
    (* SRC: prove the postcond of set_by_user *)
    force_l. force_l. iSplitL "MAP". { iFrame. eauto. }

    (* prove the IST of Map *)
    step. eauto.
  (*FAST*)Qed.

  Lemma sim : HSim.t open MapA MapM MapA.init_cond Ist.
  Proof.
    init_sim.
    - iIntros "(IST & P)"; s.
      iExists _, _. iSplit; eauto. iLeft. iFrame. eauto.
    - apply simF_init; eauto.
    - apply simF_get; eauto.
    - apply simF_set; eauto.
    - apply simF_set_by_user; eauto.
  Qed.
End MapMA.
Section MapMA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !MapAGΓ Γ, !MapMGΓ Γ, !memGΓ Γ}.
  Lemma ctxr u_s u_t sp_s sp_t
      (LE : u_s > u_t)
      (MapInSpS : sp_incl (MapAS.sp u_s) sp_s)
      (MapInSpT : sp_incl (MapMS.sp u_t) sp_t) :
    ctx_refines
      (MapA.t u_s sp_s, MapA.init_cond)
      (MapM.t u_t sp_t, emp%I).
  Proof. eapply main_adequacy, MapMA.sim; eauto. Qed.
End MapMA. End MapMA.