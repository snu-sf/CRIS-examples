Require Import CRIS.
Require Import CellioHeader LibHeader.

Set Implicit Arguments.

Local Definition RA : ucmra :=
  authUR (optionUR (exclR ZO)).
Class CellioAGΓ (Γ : HRA) := {
  #[local] RA_inG :: inG RA Γ;
}.
Definition CellioAΓ : HRA := #[RA].
Global Instance subG_GΓ {Γ : HRA} : subG CellioAΓ Γ → CellioAGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_GΓ RA_inG : GRA_index.

Module CellioA. Section CellioA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellioAGΓ Γ}.

  Definition auth (v : Z) : iProp Σ :=
    own base_γ (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own base_γ (◯E v).

  Definition ir : DRA_mk RA := ●E 0%Z ⋅ ◯E 0%Z.
  Lemma ir_valid : ✓ ir. Proof. rewrite /ir. eapply excl_auth_valid. Qed.
  Definition irΓ : CellioAΓ := *[Some ir].

  Lemma cell_auth_get v v':
    cell v -∗ auth v' -∗ ⌜v = v'⌝.
  Proof.
    rewrite /cell /auth.
    iIntros "P P'"; iCombine "P P'" as "P" gives %wf.
    by apply excl_auth_agree in wf.
  Qed.

  Lemma cell_auth_set v v':
    cell v -∗ auth v ==∗ cell v' ∗ auth v'.
  Proof.
    rewrite /cell /auth.
    iIntros "C AU". iCombine "C AU" as "H".
    iMod (own_update with "H") as "[C AU]"; last by (iModIntro; iSplitL "AU"). 
    rewrite comm; apply excl_auth_update.
  Qed.

  Definition set: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      (* i <- trigger (@IO _ Z "Input" tt);; *)
      'i: Z <- ccallU LibHdr.input tt;;
      trigger (Guarantee (CellioA.cell i));;;
      Ret tt↑.
  
  Definition get: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      trigger (Guarantee (CellioA.cell x));;;
      Ret x↑.

  Definition scopes := [CellioHdr.mn].
  
  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellioHdr.set, (scopes, mk_specbody fspec_trivial set));
     (CellioHdr.get, (scopes, mk_specbody fspec_trivial get))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ :=
    CellioA.auth 0.

  Definition InitRes : Σ := own.iRes_singleton base_γ (●E 0%Z).

  Definition t spc := Seal.sealing CRIS (SMod.to_hmod emp spc Mod).
End CellioA. End CellioA.
