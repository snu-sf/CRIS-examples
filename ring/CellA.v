Require Import CRIS.

Require Import ImpPrelude.
Require Import RingHeader CellHeader.

Set Implicit Arguments.

Local Definition pendingUR := (nat -d> optionUR (exclR unitO)).
Local Definition cellUR := (nat -d> optionUR (exclR ZO)).
Local Definition RA : ucmra := prodUR pendingUR (authUR cellUR).
Class CellAGΓ (Γ : HRA) := {
  #[local] RA_inG :: inG RA Γ;
}.
Definition CellAΓ : HRA := #[RA].

Module CellAS. Section CellAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellAGΓ Γ}.

  (* Index of this Cell *)
  Variable idx : nat.

  (* Resources *)

  (* Holds an exclusive token ensuring uniqueness of the pending state *)
  Definition pending : iProp Σ :=
    own base_γ (((fun n => if Nat.eq_dec n idx then Some (Excl ()) else ε) : pendingUR, ε): RA).

  (* Raw representation of the cell's value as an exclusive resource at [idx] *)
  Definition cellraw_r (v : Z) : cellUR :=
    (fun n => if Nat.eq_dec n idx then Excl' v else ε).

  (* A fragmental view on the value [v] that the cell at [idx] currently holds *)
  Definition cell (v : Z) : iProp Σ :=
    own base_γ ((ε, ◯ (cellraw_r v)): RA).

  (* Authoritative ownership asserting that the cell at [idx] definitively stores [v]. *)
  Definition auth (v : Z) : iProp Σ :=
    own base_γ ((ε, ● (cellraw_r v)): RA).

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


  (* Fragmental assertion [cell v'] combined with authoritative assertion [auth v] implies equality [v = v']. *)
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
    fspec_simple (fun v: Z =>
     ((fun arg => ⌜arg = tt↑⌝ ∗ cell v),
      (fun ret => ⌜ret = v↑⌝ ∗ cell v)))%I.

  Definition set_spec : fspec :=
    fspec_simple (fun '(v0,v) =>
     ((fun arg => ⌜arg = v↑⌝ ∗ (pending ∨ cell v0)),
      (fun ret => ⌜ret = tt↑⌝ ∗ cell v)))%I.

  Definition Sp : alist string fspec :=
    Seal.sealing CRIS [(CellHdr.get idx, get_spec);
                       (CellHdr.set idx, set_spec)].

  Lemma Sp_nodup : List.NoDup (List.map fst Sp).
  Proof.
    unfold Sp. unseal CRIS. prove_nodup.
  Qed.

End CellAS. End CellAS.

Global Hint Unfold CellAS.Sp : sp.

(* Define CellA Module *)
Module CellA. Section CellA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellAGΓ Γ}.

  (* Index of this Cell *)
  Variable idx : nat.

  (* Scopes *)
  Definition scopes := [CellHdr.mn idx].

  Definition fnsems : alist string (list string * fspecbody) :=
    [(CellHdr.get idx, ([], mk_specbody (CellAS.get_spec idx) fbody_trivial));
     (CellHdr.set idx, ([], mk_specbody (CellAS.set_spec idx) fbody_trivial))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}
  .
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition InitCond : iProp Σ :=
    (∃ v, CellAS.cell idx v ∗ CellAS.auth idx v)%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod Sp Mod).

End CellA. End CellA.
