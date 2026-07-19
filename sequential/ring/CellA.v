From CRIS.common Require Import CRIS.
Require Import ImpPrelude.
Require Import RingHeader CellHeader.

Local Definition pendingUR := (nat -d> optionUR (exclR unitO)).
Local Definition cellUR := (nat -d> optionUR (exclR ZO)).
Local Definition RA := prodUR pendingUR (authUR cellUR).

Class cellGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cell_inG :: inG RA Γ;
}.
Class cellGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] cellGS_cellGpreS :: cellGpreS;
  cell_name : gname;
}.
Definition cellΓ : HRA := #[RA].
Global Instance subG_cellGpreS `{!crisG Γ Σ α β τ _S _I} : subG cellΓ Γ → cellGpreS.
Proof. solve_inG. Qed.

Module CellA. Section CellA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.

  (* Index of this Cell *)
  Variable idx : nat.

  (* Resources *)
  (* Holds an exclusive token ensuring uniqueness of the pending state *)
  Definition pending : iProp Σ :=
    own cell_name (((λ n, if Nat.eq_dec n idx then Some (Excl ()) else ε) : pendingUR, ε)).

  (* Raw representation of the cell's value as an exclusive resource at [idx] *)
  Definition cellraw_r (v : Z) : cellUR :=
    (λ n, if Nat.eq_dec n idx then Excl' v else ε).

  (* A fragmental view on the value [v] that the cell at [idx] currently holds *)
  Definition cell (v : Z) : iProp Σ :=
    own cell_name ((ε, ◯ (cellraw_r v)) : RA).

  (* Authoritative ownership asserting that the cell at [idx] definitively stores [v]. *)
  Definition auth (v : Z) : iProp Σ :=
    own cell_name ((ε, ● (cellraw_r v)) : RA).

  (* Lemmas *)
  (* Two simultaneous pending assertions for the same cell are contradictory. *)
  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    rewrite /pending.
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE; rewrite -pair_op pair_valid in FALSE; des; ss.
    rr in FALSE; specialize (FALSE idx); des_ifs.
  Qed.

  (* A cell at [idx] cannot simultaneously hold two different fragmental values. *)
  Lemma cell_unique v v':
    cell v -∗ cell v' -∗ False.
  Proof.
    rewrite /cell /auth /cellraw_r.
    iIntros "P P'"; iCombine "P P'" as "P" gives %FALSE; rewrite -pair_op pair_valid in FALSE; des; ss.
    rewrite -auth_frag_op in FALSE0; apply auth_frag_valid_1 in FALSE0.
    rr in FALSE0; specialize (FALSE0 idx); des_ifs.
  Qed.

  (* Fragmental assertion [cell v'] combined with authoritative assertion [auth v] 
     implies equality [v = v']. *)
  Lemma cell_auth_get v v':
    cell v' -∗ auth v -∗ ⌜v = v'⌝.
  Proof.
    rewrite /cell /auth /cellraw_r.
    iIntros "P P'"; iCombine "P P'" as "P" gives %wf.
    rewrite -pair_op pair_valid auth_both_valid_discrete /= in wf; des.
    apply (discrete_fun_included_spec_1 _ _ idx) in wf0; ss;
    des_ifs.
    by rewrite Excl_included in wf0.
  Qed.

  (* Given fragmental [cell v] and authoritative [auth v] ownership of the same cell,
     one can atomically update both to reflect a new value [v']. *)
  Lemma cell_auth_set v v':
    cell v -∗ auth v -∗ |==> cell v' ∗ auth v'.
  Proof.
    rewrite /cell /auth /cellraw_r.
    iIntros "C AU". iCombine "C AU" as "H".
    iMod (own_update with "H") as "[C AU]"; last by (iModIntro; iSplitL "AU").
    rewrite comm; apply prod_update, auth_update, discrete_fun_local_update; intros x; ss.
    destruct (decide (idx = x)); subst; des_ifs.
    apply option_local_update, exclusive_local_update; ss.
  Qed.

  (* Specifications of get and set *)
  Definition get_spec : fspec :=
    fspec_simple (λ v : Z,
     ((λ arg, ⌜arg = tt↑⌝ ∗ cell v),
      (λ ret, ⌜ret = v↑⌝ ∗ cell v)))%I.

  Definition set_spec : fspec :=
    fspec_simple (λ '(v0, v),
     ((λ arg, ⌜arg = v↑⌝ ∗ (pending ∨ cell v0)),
      (λ ret, ⌜ret = tt↑⌝ ∗ cell v)))%I.

  Definition sp : specmap :=
    {[fid (CellHdr.get idx) @ get_spec;
      fid (CellHdr.set idx) @ set_spec]}.

  Definition scopes : list string := [CellHdr.mn idx].

  Definition fnsems : fnsemmap :=
    {[fid (CellHdr.get idx) # (msk_scp scopes msk_true, (fsp_some get_spec, fbody_trivial));
      fid (CellHdr.set idx) # (msk_scp scopes msk_true, (fsp_some set_spec, fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.

  Definition init_cond : iProp Σ := (∃ v, cell v ∗ auth v)%I.
End CellA. End CellA.

(* Lemma cell_alloc `{!crisG Γ Σ α β τ _S _I, _CELLPRE: !cellGpreS} idx v :
  ⊢ o=> ∃ (_ : cellGS), CellA.pending idx ∗ CellA.auth idx v.
Proof.
  iMod (own_alloc ((λ n, if Nat.eq_dec n idx then Some (Excl ()) else ε) : pendingUR, ε) ⋅
    ). *)
