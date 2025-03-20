Require Import CRIS.
Require Import IncrMainI IncrMainA SchA MemA SchTactics.
From iris Require Import frac_auth numbers.

Module IncrIA. Section IncrIA.
  Import IncrMainAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Context (u_s : univ_id).
  Context (spc_s spc_user_s spc_mem : string → option fspec).
  Context (SchInSpc : spc_incl (SchAS.spc u_s spc_user_s) spc_s).
  Context (MemInSpc : spc_incl MemA.spc spc_s).
  Context (MainInSpc : spc_incl (IncrMainAS.spc u_s) spc_user_s).

  Local Definition MemA := (MemA.t u_s spc_mem).
  Local Definition IncrMainA := (IncrMainA.t u_s spc_s).
  Local Definition IncrMainI := (IncrMainI.t).
  Local Definition IstFull := (IstProd (IstSB IncrMainA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (IncrMainA ★ MemA).
  Local Definition MI := (IncrMainI ★ MemA).

  Lemma f_spawnable γ v blk ofs:
    SchAS.fspec_spawnable u_s (IncrMainAS.f_spec u_s)
      (λ varg arg, ⌜varg = arg ∧ varg = ([Vptr blk ofs]↑↑)⌝ ∗ counter γ (1/2) v ∗ f_inv u_s 0 γ blk ofs)%I
      (λ vret ret, existT 0 ((⌜vret = ret ∧ vret = tt↑↑⌝ ∗ counter_syn γ (1/2) (v + 1))%SRF)).
  Proof.
    rewrite /SchAS.fspec_spawnable /w_fspec /fspec_virtual /precond /postcond /f_spec /=.
    ii; ss. eexists (x_src, (blk, ofs, v, γ)); split; red; ii.
    - rewrite /precond /w_fspec_sch /fspec_simple /w_fspec /precond /=.
      iIntros "[W [% [-> [TID [% [-> [[-> ->] [C #INV]]]]]]]]". iFrame. eauto.
    - rewrite /postcond /w_fspec_sch /fspec_simple /w_fspec /postcond /=.
      iIntros "[W [TID [[-> C] ->]]]". iFrame. iExists _; iSplitR; eauto.
      iExists _; iSplitR; eauto. SL_red. iSplitR; eauto.
  Qed.

  Lemma f_simF : HSim.sim_fun open MA MI IstFull MainHdr.f.
  Proof.
    init_simF u_s 0.

    steps_l. iDestruct "ASM" as "[TID [[-> [C #INV]] ->]]". hss.

    steps_l. hss. steps_l.
    steps_r. hss. steps_r.
    rewrite /IncrMainI.f /IncrMainA.f /=. steps_r.

    sch_yield_r.
    iSplitL "IST"; iFrame.
    clear nths NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".
    steps_r.
    sch_yield_r.
    iSplitL "IST"; iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    rewrite /IncrMainAS.f_inv.
    iInv "INV" as "I" "IA". SL_red.
    iDestruct "I" as (x) "PT". SL_red. iDestruct "PT" as "[PT CA]".

    rewrite /MemHdr.faa.
    inline_r. steps_r.
    force_r (q7, q8, Vint x, 1%Qp).
    steps_r. force_r ([Vptr q7 q8]↑).
    steps_r. force_r.
    iSplitL "PT".
    { iFrame; ss. }
    steps_r.
    iDestruct "GRT" as "[[PT ->] ->]". hss.
    steps_r.

    inline_r. steps_r.
    force_r (q7, q8, Vint (x + 1)). steps_r.
    force_r ([Vptr q7 q8; Vint (x + 1)]↑). steps_r.
    force_r. iSplitL "PT"; iFrame; ss. steps_r.
    iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.

    iMod (counter_incr 1 with "[C CA]") as "[C CA]"; first iFrame.
    iMod ("IA" with "[PT CA]") as "_".
    { iExists (x + 1)%Z; SL_red; ss; iFrame. }
    
    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_l.
    steps_l. force_l. steps_l. force_l. iSplitL "TID C"; iFrame; eauto. steps_l.
    step; eauto.
  (*FAST*)Qed.

  Lemma main_simF : HSim.sim_fun open MA MI IstFull MainHdr.main.
  Proof.
    init_simF u_s 0.

    steps_l. iDestruct "ASM" as "[TID [-> ->]]". hss.
    steps_l.

    (* src/tgt yield *)
    steps_r.
    sch_yield_r. iFrame.
    clear nths NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_l.

    (* src/tgt alloc *)
    steps_l. force_l 1. steps_l. force_l. steps_l.
    force_l. iSplit; eauto. steps_l.
    steps_r. call "IST".
    steps_l. iDestruct "ASM" as "[[%b [-> [PT _]]] ->]". hss.
    steps_r. hss. steps_r.

    (* tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".
    steps_r.
    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    (* tgt store *)
    inline_r. steps_r. force_r (b, 0%Z, Vint 0%Z). steps_r.
    force_r. steps_r. force_r. iSplitL "PT".
    { iFrame. eauto. }
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.

    (* src/tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".
    sch_yield_l.

    iApply (wsim_own_alloc (●F 0%Z ⋅ ◯F{1} 0%Z)).
    { apply frac_auth_valid; ss. }

    iIntros "[%γc [A F]]".
    iMod (inv_alloc (ccounter_syn 0 γc b 0%Z) _ _ _ N_main with "[PT A]") as "#I"; eauto.
    { rewrite /ccounter_syn; SL_red; iExists 0; SL_red; iFrame. }
    iPoseProof (counter_op with "[F]") as "[F1 F2]".
    { rewrite -Qp.half_half -{2}(Z.add_0_r 0%Z). iApply "F". }

    iCombine "F1 I" as "F1". iCombine "F2 I" as "F2".
    steps_l. steps_r.

    (* src/tgt spawns *)
    sch_spawn; eauto using f_spawnable.
    { eapply MainInSpc. ss. }
    iFrame. iSplitL "" ; eauto.
    clear nths st_s st_t NODS NODD. iIntros (tid nths st_s st_t NODS NODD) "IST TID TKN".

    (* src/tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_l.

    sch_spawn; eauto using f_spawnable.
    { eapply MainInSpc. ss. }
    iFrame. iSplitL "" ; eauto.
    clear nths st_s st_t NODS NODD. iIntros (tid2 nths st_s st_t NODS NODD) "IST TID TKN2".

    (* src/tgt yield *)
    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_l.

    sch_join. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t ? ? NODS NODD) "IST TID Q /=". SL_red.
    iDestruct "Q" as "[[-> ->] Q]".

    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_l.

    sch_join. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t ? ? NODS NODD) "IST TID Q2 /="; SL_red.
    iDestruct "Q2" as "[[-> ->] Q2]".

    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    iInv "I" as "INV" "INVA"; iEval (SL_red) in "INV"; iDestruct "INV" as "[%x INV]".
    iEval (SL_red) in "INV". iDestruct "INV" as "[PT C]".
    iCombine "C Q Q2" as "C" gives %[_ WF%frac_auth_agree]. inv WF; ss.
    iDestruct "C" as "[CA CF]".

    inline_r. steps_r. force_r (b, 0%Z, (Vint 2), 1%Qp). steps_r. forces_r.
    iSplitL "PT"; eauto.
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.

    iMod ("INVA" with "[CA PT]") as "_".
    { SL_red. iExists 2; SL_red; iFrame. }

    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".

    sch_yield_l. step.
    steps_l. steps_r.

    sch_yield_r. iFrame.
    clear nths st_s st_t NODS NODD. iIntros (nths st_s st_t NODS NODD) "IST TID".
    
    sch_yield_l.
    steps_l. force_l. steps_l. force_l. iSplitL "TID"; eauto.
    steps_l. steps_r.
    step. eauto.
  (*FAST*)Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; eauto. }
    { eapply main_simF. }
    { eapply f_simF. }
  Qed.
End IncrIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition ctxr (u : univ_id) (spc_s spc_user_s spc_mem : string → option fspec)
      (SchInSpc : spc_incl (SchAS.spc u spc_user_s) spc_s)
      (MainInSpc : spc_incl (IncrMainAS.spc u) spc_user_s)
      (MemInSpc : spc_incl MemA.spc spc_s) :
    ctx_refines
      ((IncrMainA.t u spc_s) ★ (MemA.t u spc_mem), emp%I)
      ((IncrMainI.t)         ★ (MemA.t u spc_mem), emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End IncrIA.
