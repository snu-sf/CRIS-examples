Require Import CRIS.
Require Import CellioHeader CtxHeader.

Set Implicit Arguments.

Section CellioRA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Local Definition RA : ucmra :=
    authUR (optionUR (exclR ZO)).

  Class cellioG `{!crisG Γ Σ α β τ _S _I} := {
    cellio_inG :: inG RA Γ;
  }.
  Definition cellioΓ : HRA := #[RA].
  Global Instance subG_cellioG : subG cellioΓ Γ → cellioG.
  Proof. solve_inG. Defined.
End CellioRA.  
Hint Unfold subG_cellioG cellio_inG : GRA_index.

Module CellioA. Section CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_CELLIO: !cellioG}.

  Definition auth (v : Z) : iProp Σ :=
    own base_γ (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own base_γ (◯E v).

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

  Definition set: Any.t -> itree crisE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      (* i <- trigger (@IO _ Z "Input" tt);; *)
      'i: Z <- ccallU CtxHdr.input tt;;
      trigger (Guarantee (CellioA.cell i));;;
      Ret tt↑.
  
  Definition get: Any.t -> itree crisE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      trigger (Guarantee (CellioA.cell x));;;
      Ret x↑.

  Definition scopes := [CellioHdr.mn].

  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.set # (msk_scp scopes msk_true, (fsp_some fspec_trivial, set));
      fid CellioHdr.get # (msk_scp scopes msk_true, (fsp_some fspec_trivial, get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ :=
    CellioA.auth 0.

  (* We can use ∅ because Cellio will be removed before cancellation *)
  Definition t := SMod.to_mod ∅ smod.
End CellioA. End CellioA.
