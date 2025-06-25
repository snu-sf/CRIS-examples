Require Import CRIS.
From CRIS.incr Require Import Header.
Require Import ImpPrelude MemHeader MemA SchA SchTactics SchHeader.
Require Import FaaI FaaA.

Module FaaIA. Section FaaIA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.

  Context (sp_mem : string → option fspec).
  Local Lemma sp_incl_sch : sp_incl (SchAS.sp ∅ sp_empty) (to_sp (SchAS.sp ∅ sp_empty)).
  Proof.
    split; ss.
    rewrite /SchAS.sp; unseal CRIS; ss.
    prove_nodup.
  Qed.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t sp_mem).
  Local Definition FaaA := (FaaA.t).
  Local Definition FaaI := (FaaI.t).
  Local Definition IstFull := (IstProd (IstSB FaaA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (FaaA ★ MemA).
  Local Definition MI := (FaaI ★ MemA).

  Lemma faa2_simF : HSim.sim_fun open MA MI IstFull FaaHdr.faa2.
  Proof using.
    init_simF.
    steps_l. iDestruct "ASM" as "[TID [-> ->]]". hss.
    destruct q2 as [b ofs]. rename q1 into tid.
    steps_l. steps_r.

    (* tgt yield *)
    sch_yield_r; eauto.
    { apply sp_incl_sch. }
    iFrame. clear nths st_src st_tgt NODD NODS. iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* src yield *)
    sch_yield_l.
    (* src take pointsto *)
    steps_l. rename q into v.
    (* tgt inline - load *)
    rewrite /MemHdr.faa. inline_r.
    (* tgt prove preconditions for load *)
    force_r (b, ofs, 1%Qp, Vint v). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from load *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* tgt inline - store *)
    inline_r. force_r (b, ofs, _, Vint (v + 1)). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from store *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* src give pointsto *)
    force_l. iFrame. steps_l.
    (* tgt yield *)
    sch_yield_r; eauto using sp_incl_sch.
    iFrame. clear nths st_s st_t NODD NODS. iIntros (nths st_s st_t NODS NODD) "IST TID".
    (* src yield *)
    sch_yield_l.
    (* src take pointsto *)
    steps_l. clear v; rename q into v.
    (* tgt inline - load *)
    rewrite /MemHdr.faa. inline_r.
    (* tgt prove preconditions for load *)
    force_r (b, ofs, 1%Qp, Vint v). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from load *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* tgt inline - store *)
    inline_r. force_r (b, ofs, _, Vint (v + 1)). forces_r. iFrame. iSplit; first eauto.
    (* tgt get postconditions from store *)
    steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss. steps_r.
    (* src give pointsto *)
    force_l. iFrame. steps_l.
    (* tgt yield *)
    sch_yield_r; first eauto using sp_incl_sch.
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
