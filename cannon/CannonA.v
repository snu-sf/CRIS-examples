Require Import CRIS.
Require Import ImpPrelude.
Require Import CannonHeader.

Set Implicit Arguments.

Set Implicit Arguments.

Local Definition RA : ucmra := excl_authR unitO.
Class CannonAGΓ (Γ : HRA) := {
  #[local] cannon_inG :: inG (excl_authR unitO) Γ;
}.
Definition CannonAΓ : HRA := #[excl_authR unitO].
Global Instance subG_GΓ {Γ : HRA} : subG CannonAΓ Γ → CannonAGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_GΓ cannon_inG : GRA_index.

Module CannonAS. Section CannonAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.
  
  Definition Ready : iProp Σ := own base_γ (●E tt).
  Definition Ball : iProp Σ := own base_γ (◯E tt).
  Definition Fired : iProp Σ := own base_γ ((●E tt) ⋅ (◯E tt)).

  Definition ir : DRA_mk RA := ●E tt ⋅ ◯E tt.
  Lemma ir_valid : ✓ ir. Proof. rewrite /ir. eapply excl_auth_valid. Qed.
  Definition irΓ : CannonAΓ := *[Some ir].

  Lemma ReadyBall : Ready ∗ Ball ⊣⊢ Fired.
  Proof.
    rewrite /Ready /Ball /Fired. iSplit.
    { iIntros "[B W]". iSplitL "B"; iFrame. }
    { iIntros "[$ $]". }
  Qed.

  Lemma FiredReady : Ready ∗ Fired ⊢ False.
  Proof.
    rewrite /Ready /Fired. iIntros "[B0 [B1 W]]". iCombine "B0 B1" as "X" gives %FALSE.
    rewrite excl_auth_auth_op_valid // in FALSE.
  Qed.

  Lemma FiredBall : Ball ∗ Fired ⊢ False.
  Proof.
    rewrite /Ball /Fired. iIntros "[W0 [B W1]]". iCombine "W0 W1" as "X" gives %FALSE.
    rewrite excl_auth_frag_op_valid // in FALSE.
  Qed.

  Definition fire_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ arg, (⌜arg = ([]: list val)↑⌝ ∗ Ball)),
      (λ ret, (⌜ret = (1: Z)%Z↑⌝)))
    )%I.

  Definition Spc : alist string fspec :=
    Seal.sealing CRIS [(CannonHdr.fire, fire_spec)].

  Lemma Spc_nodup : List.NoDup (List.map fst Spc).
  Proof. unfold Spc. unseal CRIS. prove_nodup. Qed.
End CannonAS. End CannonAS.

Module CannonA. Section CannonA.
  Import CannonAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CannonAGΓ Γ}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv".

  Definition fire : list val → itree hmodE Z :=
    λ _,
      let r := 1%Z in
      _ <- trigger (@IO _ unit "print" [r]↑);;
      Ret r.

  Definition fnsems :=
    [(CannonHdr.fire, (scopes, mk_specbody CannonAS.fire_spec (cfunU fire)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_lv, 1%Z↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := Ready.

  Definition t spc := Seal.sealing CRIS (SMod.to_hmod emp spc Mod).
End CannonA. End CannonA.
