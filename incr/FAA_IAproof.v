Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader MemA SchA SchTactics SchHeader.
Require Import FAA_I FAA_A.

Module FaaIA. Section FaaIA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
                
  Context (u_s : univ_id).
  Context (sp_s sp_mem sp_user_s : string → option fspec).
  Context (SchInSp : sp_incl (SchAS.sp u_s sp_user_s) sp_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t sp_mem).
  Local Definition FaaA := (FaaA.t u_s sp_s).
  Local Definition FaaI := (FaaI.t).
  Local Definition IstFull := (IstProd (IstSB FaaA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (FaaA ★ MemA).
  Local Definition MI := (FaaI ★ MemA).

  Lemma faa2_simF : HSim.sim_fun open MA MI IstFull FaaHdr.faa2.
  Proof using SchInSp.
    init_simF u_s 0.
    steps_l. iDestruct "ASM" as "[TID [-> ->]]". hss. rename q3 into b, q4 into ofs, q1 into tid.
    steps_l. steps_r.

    (* tgt yield *)
    sch_yield_r.
    iFrame. clear nths st_src st_tgt NODD NODS. iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* src yield *)
    sch_yield_l.
    (* src take pointsto *)
    steps_l. rename q into v.
    (* tgt inline - load *)
    rewrite /MemHdr.faa. inline_r.
    (* tgt prove preconditions for load *)
    force_r (b, ofs, Vint v, 1%Qp). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from load *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* tgt inline - store *)
    inline_r. force_r (b, ofs, Vint (v + 1)). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from store *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* src give pointsto *)
    force_l. iFrame. steps_l.
    (* tgt yield *)
    sch_yield_r.
    iFrame. clear nths st_s st_t NODD NODS. iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* src yield *)
    sch_yield_l.
    (* src take pointsto *)
    steps_l. clear v; rename q into v.
    (* tgt inline - load *)
    rewrite /MemHdr.faa. inline_r.
    (* tgt prove preconditions for load *)
    force_r (b, ofs, Vint v, 1%Qp). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from load *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* tgt inline - store *)
    inline_r. force_r (b, ofs, Vint (v + 1)). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from store *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* src give pointsto *)
    force_l. iFrame. steps_l.
    (* tgt yield *)
    sch_yield_r.
    iFrame. clear nths st_s st_t NODD NODS. iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* tgt terminate *)
    steps_r.
    (* src yield & terminate *)
    sch_yield_l. steps_l. forces_l. iFrame. iSplit; eauto. steps_l. step. iFrame. done.
  (*SLOW*)Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; eauto. }
    { eapply faa2_simF. }
  Qed.
End FaaIA. End FaaIA.
