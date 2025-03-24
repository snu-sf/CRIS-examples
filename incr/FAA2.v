Require Import CRIS.
Require Import ImpPrelude IncrHeader MemHeader MemA SchA SchTactics SchHeader.

Module FaaI. Section FaaI.
  Context {Σ : GRA}.

  Definition scopes : list string := [].

  Definition faa : list val → itree pmodE unit :=
    λ arg,
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; '_ : val <- MemHdr.faa arg;;
      𝒴;;; Ret tt.

  Definition fnsems := [(FaaHdr.faa, (scopes, cfunU faa))].

  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End FaaI. End FaaI.

Module FaaA. Section FaaA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ}.

  Definition faa_spec u : fspec :=
    w_fspec_sch u (fspec_simple (λ '(b, ofs), (λ arg, ⌜arg = [Vptr b ofs]↑⌝, λ ret, ⌜ret = tt↑⌝)))%I.

  Definition spc u : alist string fspec :=
    [(FaaHdr.faa, faa_spec u)].

  Definition scopes : list string := [].

  Definition faa : list val → itree hmodE unit :=
    λ arg,
      '(b, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)?;;
      𝒴;;;
        'v : Z <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;;
        'v : Z <- trigger (Take Z);;
        trigger (Assume ((b, ofs) ↦ Vint v));;;
        trigger (Guarantee ((b, ofs) ↦ Vint (v + 1)));;;
      𝒴;;; Ret tt.

  Definition fnsems u := [(FaaHdr.faa, (scopes, mk_specbody (faa_spec u) (cfunN faa)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems u;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u spc : HMod.t := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) spc (Mod u)).
End FaaA. End FaaA.

Module FaaIA. Section FaaIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ}.
  Context (u_s u_mem : univ_id).
  Context (spc_s spc_mem spc_user_s : string → option fspec).
  Context (SchInSpc : spc_incl (SchAS.spc u_s spc_user_s) spc_s).

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Local Definition MemA := (MemA.t u_mem spc_mem).
  Local Definition FaaA := (FaaA.t u_s spc_s).
  Local Definition FaaI := (FaaI.t).
  Local Definition IstFull := (IstProd (IstSB FaaA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (FaaA ★ MemA).
  Local Definition MI := (FaaI ★ MemA).

  Lemma faa_simF : HSim.sim_fun open MA MI IstFull FaaHdr.faa.
  Proof.
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
  (*FAST*)Qed.

  Lemma sim : HSim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { iIntros "_"; iExists [], [], [], []; eauto. }
    { eapply faa_simF. }
  Qed.
End FaaIA. End FaaIA.