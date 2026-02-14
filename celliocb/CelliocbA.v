Require Import CRIS.
Require Import CelliocbHeader.

Local Definition RA := authUR (optionUR (exclR ZO)).

Class celliocbGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] celliocb_inG :: inG RA Γ;
}.

Class celliocbGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] celliocbGS_celliocbGpreS :: celliocbGpreS;
  celliocb_name : gname;
}.

Definition celliocbΓ : HRA := #[RA].
Global Instance subG_celliocbGpreS `{!crisG Γ Σ α β τ _S _I} : subG celliocbΓ Γ → celliocbGpreS.
Proof. solve_inG. Defined.
(* Hint Unfold subG_celliocbG celliocb_inG : GRA_index. *)

Module CelliocbA. Section CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS}.
  Context `{_CELLIOCB: !celliocbGS}.

  Definition auth (v : Z) : iProp Σ :=
    own celliocb_name (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own celliocb_name (◯E v).

  Definition ir : DRA_mk RA := ●E 0%Z ⋅ ◯E 0%Z.
  Lemma ir_valid : ✓ ir. Proof. rewrite /ir. eapply excl_auth_valid. Qed.
  (* Definition irΓ : celliocbΓ := *[Some ir]. *)

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

  Definition set: string -> itree crisE unit :=
    λ cb,
      x <- trigger (Take Z);;
      trigger (Assume (CelliocbA.cell x));;;
      'i: Z <- ccallU cb tt;;
      trigger (Guarantee (CelliocbA.cell i));;;
      Ret tt.
  
  Definition get: Any.t -> itree crisE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CelliocbA.cell x));;;
      trigger (Guarantee (CelliocbA.cell x));;;
      Ret x↑.

  Definition scopes := [CelliocbHdr.mn].
  
  Definition fnsems : fnsemmap :=
    {[Some CelliocbHdr.set := Some (msk_scp scopes msk_true, (None, cfunU set));
      Some CelliocbHdr.get := Some (msk_scp scopes msk_true, (None, get))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := auth 0.

  (* We can use sp_none because Cellio will be removed before cancellation *)
  Definition t := SMod.to_mod ∅ smod.
End CelliocbA. End CelliocbA.
