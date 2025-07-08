Require Import CRIS.
Require Import CelliocbHeader.

Set Implicit Arguments.

Section CelliocbRA.
  Context `{!crisG Γ Σ α β τ _I _S}.

  Local Definition RA : ucmra :=
    authUR (optionUR (exclR ZO)).

  Class celliocbG `{!crisG Γ Σ α β τ _I _S} := {
    celliocb_inG :: inG RA Γ;
  }.
  Definition celliocbΓ : HRA := #[RA].
  Global Instance subG_celliocbG : subG celliocbΓ Γ → celliocbG.
  Proof. solve_inG. Defined.
End CelliocbRA.  
Hint Unfold subG_celliocbG celliocb_inG : GRA_index.

Module CelliocbA. Section CelliocbA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_celliocbG: !celliocbG}.

  Definition auth (v : Z) : iProp Σ :=
    own base_γ (●E v).

  Definition cell (v : Z) : iProp Σ :=
    own base_γ (◯E v).

  Definition ir : DRA_mk RA := ●E 0%Z ⋅ ◯E 0%Z.
  Lemma ir_valid : ✓ ir. Proof. rewrite /ir. eapply excl_auth_valid. Qed.
  Definition irΓ : celliocbΓ := *[Some ir].

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

  Definition set: string -> itree hmodE unit :=
    λ cb,
      x <- trigger (Take Z);;
      trigger (Assume (CelliocbA.cell x));;;
      'i: Z <- ccallU cb tt;;
      trigger (Guarantee (CelliocbA.cell i));;;
      Ret tt.
  
  Definition get: Any.t -> itree hmodE Any.t :=
    λ _,
      x <- trigger (Take Z);;
      trigger (Assume (CelliocbA.cell x));;;
      trigger (Guarantee (CelliocbA.cell x));;;
      Ret x↑.

  Definition scopes := [CelliocbHdr.mn].
  
  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(Some CelliocbHdr.set, (true, wmask_all, scopes, (None, cfunU set)));
     (Some CelliocbHdr.get, (true, wmask_all, scopes, (None, get)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ := auth 0.
  (* handle sp_none Since we left call as call *)
  Definition t := Seal.sealing CRIS (SMod.to_hmod sp_none Mod).
End CelliocbA. End CelliocbA.
