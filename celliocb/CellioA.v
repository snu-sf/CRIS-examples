Require Import CRIS.
From CRIS.celliocb Require Import CellioHeader CtxHeader.

Local Definition RA := authUR (optionUR (exclR ZO)).

Class cellioGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cellio_inG :: inG RA Γ;
}.

Class cellioGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cellioGS_cellioGpreS :: cellioGpreS;
  cellio_name : gname;
}.

Definition cellioΓ : HRA := #[RA].
Global Instance subG_cellioGpreS `{!crisG Γ Σ α β τ _S _I} : subG cellioΓ Γ → cellioGpreS.
Proof. solve_inG. Defined.
(* Hint Unfold subG_cellioG cellio_inG : GRA_index. *)

Module CellioA. Section CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_CELLIOCB: !cellioGS}.

  Definition auth (v : Z) : iProp Σ :=
    own cellio_name (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own cellio_name (◯E v).

  Definition ir : DRA_mk RA := ●E 0%Z ⋅ ◯E 0%Z.
  Lemma ir_valid : ✓ ir. Proof. rewrite /ir. eapply excl_auth_valid. Qed.
  (* Definition irΓ : cellioΓ := *[Some ir]. *)

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

  Definition set: string -> itree crisE () :=
    λ cb,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      i <- ccallU CtxHdr.cb_t cb tt;;
      trigger (Guarantee (CellioA.cell i));;;
      Ret tt.
  
  Definition get: () -> itree crisE Z :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CellioA.cell x));;;
      trigger (Guarantee (CellioA.cell x));;;
      Ret x.

  Definition scopes := [CellioHdr.mn].
  
  Definition fnsems : fnsemmap :=
    {[fid CellioHdr.set # (msk_scp scopes msk_true, (None, cfunU CellioHdr.set_t set));
      fid CellioHdr.get # (msk_scp scopes msk_true, (None, cfunU CellioHdr.get_t get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := auth 0.

  (* We can use sp_none because Cellio will be removed before cancellation *)
  Definition t := SMod.to_mod ∅ smod.
End CellioA. End CellioA.

Lemma cellio_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !cellioGpreS} :
  ⊢ o=> ∃ (_ : cellioGS), CellioA.init_cond ∗ CellioA.cell 0.
Proof.
  iMod (own_alloc (●E 0%Z ⋅ ◯E 0%Z)) as "[%γt T]".
  { apply auth_both_valid_discrete; esplits; ss. }
  pose (Build_cellioGS _ _ _ _ _ _ _ _ _ γt) as Hcell.
  rewrite own_op; iExists Hcell. iDestruct "T" as "[T0 T1]"; iFrame.
  done.
Qed.
