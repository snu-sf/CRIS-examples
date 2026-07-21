From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.cannon Require Import CannonHeader.

Local Definition RA := excl_authR unitO.

Class cannonGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cannon_inG :: inG (excl_authR unitO) Γ;
}.
Class cannonGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cannonGS_cannonGpreS :: cannonGpreS;
  cannon_name : gname;
}.
Definition cannonΓ : HRA := #[excl_authR unitO].
Global Instance subG_cannonGpreS `{!crisG Γ Σ α β τ _S _I} : subG cannonΓ Γ → cannonGpreS.
Proof. solve_inG. Defined.

Module CannonA. Section CannonA.
  Context `{!crisG Γ Σ α β τ _S _I, _CANNON: !cannonGS}.

  Definition Ready : iProp Σ := own cannon_name (●E tt).
  Definition Ball : iProp Σ := own cannon_name (◯E tt).
  Definition Fired : iProp Σ := own cannon_name ((●E tt) ⋅ (◯E tt)).

  Lemma ReadyBall : Ready ∗ Ball ⊣⊢ Fired.
  Proof. rewrite /Ready /Ball /Fired own_op //. Qed.

  Lemma FiredReady : Ready ∗ Fired ⊢ False.
  Proof.
    rewrite /Ready /Fired; iIntros "[B0 [B1 W]]". iCombine "B0 B1" as "X" gives %FALSE.
    rewrite excl_auth_auth_op_valid // in FALSE.
  Qed.

  Lemma FiredBall : Ball ∗ Fired ⊢ False.
  Proof.
    rewrite /Ball /Fired. iIntros "[W0 [B W1]]". iCombine "W0 W1" as "X" gives %FALSE.
    rewrite excl_auth_frag_op_valid // in FALSE.
  Qed.

  Definition fire_spec : fspec :=
    fspec_simple_typ CannonHdr.fire (λ _ : unit,
      ((λ arg, ⌜arg = []⌝ ∗ Ball),
       (λ ret, ⌜ret = 1%Z⌝))
    )%I.

  Definition sp : specmap := {[fid CannonHdr.fire @ fire_spec]}.

  Definition scopes := ["Cannon"].
  Definition v_lv := "Cannon" ↯ "lv".

  Definition fire : list val → itree crisE Z :=
    λ _,
      let r := 1%Z in
      _ <- trigger (@IO _ unit "print" [r]↑);;
      Ret r.

  Definition fnsems : fnsemmap :=
    {[fid CannonHdr.fire # (msk_scp scopes msk_true, (fsp_some fire_spec, cfunU CannonHdr.fire fire))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End CannonA. End CannonA.

Lemma cannon_alloc `{!crisG Γ Σ α β τ _S _I, !cannonGpreS} :
  ⊢ o=> ∃ (_ : cannonGS), CannonA.Ready ∗ CannonA.Ball.
Proof.
  iMod (own_alloc (●E tt ⋅ ◯E tt)) as "[%c [? ?]]".
  { apply : excl_auth_valid. }
  by iExists (Build_cannonGS _ _ _ _ _ _ _ _ _ c); iFrame.
Qed.
