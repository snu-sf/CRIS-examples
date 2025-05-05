Require Import CRIS.

Require Import KnotHeader.
Require Import APCHeader APC.

Set Implicit Arguments.

Section RA.
  Context `{!sinvG Γ Σ α β τ _I _S}.

  Local Definition RA : ucmra :=
    authUR (optionUR (exclR (optionO (natO -d> natO)))).

  Class knotG `{!sinvG Γ Σ α β τ _I _S} := {
    knot_inG :: inG RA Γ;
  }.
  Definition knotΓ : HRA := #[RA].
  Global Instance subG_knotG : subG knotΓ Γ → knotG.
  Proof. solve_inG. Defined.
End RA.  
Hint Unfold subG_knotG knot_inG : GRA_index.

(* Initial Resource *)
Definition knot_init_res : RA := (● (Excl' None) ⋅ ◯ (Excl' None)).

Lemma knot_init_valid : ✓ knot_init_res.
Proof. rewrite /knot_init_res auth_both_valid //. Qed.
Definition ir_knotRA : DRA_mk RA := knot_init_res.
Lemma ir_knotRA_valid : ✓ ir_knotRA.
Proof. eapply knot_init_valid. Qed.

Definition ir_knotAΓ : knotΓ := *[Some (ir_knotRA)].

Module KnotA. Section KnotA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_knotG: !knotG}.

  (* Resources *)

  Global Instance leibniz_equiv_discrete_funO_natO_natO: LeibnizEquiv (natO -d> natO).
  Proof.
    ii. assert ((x: nat → nat) = (y: nat → nat)).
    { apply func_ext. intro z. specialize (H z). ss. } ss.
  Qed.

  Definition knot_full (f: option (nat → nat)) : iProp Σ :=
    own base_γ (● (Some (Excl (f: optionO (natO -d> natO))))).
  Definition knot_frag (f: option (nat → nat)) : iProp Σ := 
    own base_γ (◯ (Some (Excl (f: optionO (natO -d> natO))))).

  Definition knot_init: iProp Σ := knot_frag None.

  Lemma knot_ra_merge
      (f0 f1: optionO (natO -d> natO))
    :
    (knot_full f0) -∗ (knot_frag f1) -∗ (⌜f1 ≡ f0⌝).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H" gives %WF.
    iPureIntro. rewrite auth_both_valid_discrete in WF. des.
    apply Excl_included in WF. et.
  Qed.

  Lemma knot_frag_unique
      (f0 f1: optionO (natO -d> natO))
    :
      (knot_frag f0) -∗ (knot_frag f1) -∗ (⌜False⌝).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H" gives %WF. exfalso.
    rewrite -auth_frag_op auth_frag_valid in WF. inv WF.
  Qed.

  Lemma knot_full_unique
      (f0 f1: optionO (natO -d> natO))
    :
      (knot_full f0) -∗ (knot_full f1) -∗ (⌜False⌝).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H" gives %WF. exfalso.
    inv WF; ss.
  Qed.

  Lemma auth_excl_both_update N
      (old new: optionO (natO -d> natO))
    :
      own N (● Excl' old ⋅ ◯ Excl' old) ⊢ |==> own N (● Excl' new ⋅ ◯ Excl' new).
  Proof.
    apply own_update. apply auth_update. rewrite local_update_discrete. i.
    split; ss. destruct mz; ss. destruct c; ss. inv H0.
  Qed.

  (* Specifications *)

Section KnotAS.

  Variable genv: GEnv.t.
  Variable SpRec: string → option fspec.
  Variable SpFun: string → option fspec.
  Variable SpPure: string → option fspec.

  Definition var_points_to (var: string) (v: val): iProp Σ :=
    match ((CEnv.load_genv genv).(CEnv.id2blk) var) with
    | Some blk => mem_points_to_singleton (blk, 0%Z) 1%Qp v
    | None => True
    end.

  Definition mrec_spec (f: nat -> nat) (INV: iProp Σ): fspec :=
    fspec_apc (λ n: nat, 2 * n + 1)%ord
      (fun (n: nat) =>
          ((fun arg => (⌜arg = [Vint (Z.of_nat n)]↑ /\ (intrange_64 n)⌝ ∗ INV)%I),
            (fun ret => (⌜ret = (Vint (Z.of_nat (f n)))↑⌝ ∗ INV)%I))).
  
  Definition rec_spec: fspec :=
    fspec_apc (λ '(f, n), (2 * (n: nat) + 1)%ord)
      (fun '(f, n) => 
        ((fun varg => (⌜varg = [Vint (Z.of_nat n)]↑ /\ (intrange_64 n)⌝ ∗ knot_frag (Some f))%I),
          (fun vret => (⌜vret = (Vint (Z.of_nat (f n)))↑⌝ ∗ knot_frag (Some f))%I))).
  
  Definition fun_gen (f: nat -> nat): fspec :=
    fspec_apc (λ n: nat, (2 * n)%ord)
      (fun n => 
        ((fun varg => (⌜∃ fb, varg = [Vptr (fb, 0%Z); Vint (Z.of_nat n)]↑ ∧ (intrange_64 n) ∧
                        fb_has_spec genv SpRec fb rec_spec⌝
                        ∗ knot_frag (Some f))%I),
          (fun vret => (⌜vret = (Vint (Z.of_nat (f n)))↑⌝ ∗ knot_frag (Some f))%I))).

  Definition KnotRecSp: alist string fspec :=
    Seal.sealing CRIS [(KnotHdr.rec, rec_spec)].

  Definition knot_spec : fspec :=
    fspec_simple (X:=(nat -> nat))
      (fun f => 
        ((fun varg => (⌜∃ fb, varg = [Vptr (fb, 0%Z)]↑ ∧ 
                        fb_has_spec genv SpFun fb (fun_gen f)⌝
                        ∗ (∃ old, knot_frag old))%I,
          (fun vret => (⌜∃ fb, vret = (Vptr (fb, 0%Z))↑ ∧
                        fb_has_spec genv SpRec fb rec_spec⌝
                        ∗ knot_frag (Some f))%I)))).

  Definition KnotSp : alist string fspec :=
    Seal.sealing CRIS 
      [(KnotHdr.rec, rec_spec); 
      (KnotHdr.knot, knot_spec)].

End KnotAS.

Section KnotA.
  (* Define Module *)

  Definition scopes := ["Knot"].

  Definition fnsems genv SpRec SpFun :=
    [(KnotHdr.rec, (wmask_all, scopes, mk_specbody rec_spec pure_body));
     (KnotHdr.knot, (wmask_all, scopes, mk_specbody (knot_spec genv SpRec SpFun) fbody_trivial))].

  Program Definition Mod genv SpRec SpFun : SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv SpRec SpFun;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond genv : iProp Σ :=
    ((var_points_to genv KnotHdr._f (Vint 0)) ∗ knot_full None)%I.

  Definition t genv SpRec SpFun Sp :=
    Seal.sealing CRIS (SMod.to_hmod Sp (Mod genv SpRec SpFun)).
End KnotA.
End KnotA. End KnotA.
