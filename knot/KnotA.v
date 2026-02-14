Require Import CRIS.
Require Import KnotHeader.
Require Import APCHeader APC.

Local Definition RA := authUR (optionUR (exclR (optionO (natO -d> natO)))).

Class knotGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] knot_inG :: inG RA Γ;
}.
Class knotGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] knotG_knotGpreS :: knotGpreS;
  knot_name : gname;
}.
Definition knotΓ : HRA := #[RA].
Global Instance subG_knotG `{!crisG Γ Σ α β τ _S _I} : subG knotΓ Γ → knotGpreS.
Proof. solve_inG. Qed.

Module KnotA. Section KnotA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _KNOT: !knotGS}.

  Global Instance leibniz_equiv_discrete_funO_natO_natO: LeibnizEquiv (natO -d> natO).
  Proof.
    intros ?? EQ. assert ((x: nat → nat) = (y: nat → nat)).
    { apply func_ext. intro z. specialize (EQ z). ss. } ss.
  Qed.

  Definition knot_full (f : option (nat → nat)) : iProp Σ :=
    own knot_name (● (Some (Excl (f : optionO (natO -d> natO))))).
  Definition knot_frag (f: option (nat → nat)) : iProp Σ := 
    own knot_name (◯ (Some (Excl (f : optionO (natO -d> natO))))).

  Lemma knot_ra_merge (f0 f1 : optionO (natO -d> natO)) :
    knot_full f0 -∗ knot_frag f1 -∗ ⌜f1 = f0⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H" gives %WF.
    iPureIntro. rewrite auth_both_valid_discrete in WF. des.
    apply Excl_included in WF. inv WF; eauto.
  Qed.

  Lemma knot_frag_unique (f0 f1 : optionO (natO -d> natO)) :
    knot_frag f0 -∗ knot_frag f1 -∗ ⌜False⌝.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H" gives %WF. exfalso.
    rewrite -auth_frag_op auth_frag_valid // in WF.
  Qed.

  Lemma knot_full_unique (f0 f1 : optionO (natO -d> natO)) :
    knot_full f0 -∗ knot_full f1 -∗ ⌜False⌝.
  Proof. iIntros "H0 H1". iCombine "H0 H1" as "H" gives %[]; ss. Qed.

  Lemma knot_update (f1 f2 : option (nat → nat)) :
    knot_full f1 ∗ knot_frag f1 ==∗ knot_full f2 ∗ knot_frag f2.
  Proof.
    rewrite /knot_full /knot_frag -?own_op own_update; [iIntros "$"|].
    by apply auth_update, option_local_update, exclusive_local_update.
  Qed.

  Variable (genv : GEnv.t) (sp_rec sp_fun : specmap).

  Definition var_points_to (var : string) (v : val): iProp Σ :=
    match ((CEnv.load_genv genv).(CEnv.id2blk) var) with
    | Some blk => (blk, 0%Z) ↦ v
    | None => True
    end.

  Definition mrec_spec (f: nat → nat) (INV: iProp Σ): fspec :=
    fspec_apc (λ n: nat, 2 * n + 1)%ord
      (λ (n: nat),
          ((λ arg, (⌜arg = [Vint (Z.of_nat n)]↑ /\ (intrange_64 n)⌝ ∗ INV)%I),
            (λ ret, (⌜ret = (Vint (Z.of_nat (f n)))↑⌝ ∗ INV)%I))).
  
  Definition rec_spec: fspec :=
    fspec_apc (λ '(f, n), (2 * (n: nat) + 1)%ord)
      (λ '(f, n), 
        ((λ varg, (⌜varg = [Vint (Z.of_nat n)]↑ /\ (intrange_64 n)⌝ ∗ knot_frag (Some f))%I),
          (λ vret, (⌜vret = (Vint (Z.of_nat (f n)))↑⌝ ∗ knot_frag (Some f))%I))).
  
  Definition fun_gen (f : nat → nat) : fspec :=
    fspec_apc (λ n : nat, (2 * n)%ord)
      (λ n, 
        ((λ varg, (⌜∃ fb, varg = [Vptr (fb, 0%Z); Vint (Z.of_nat n)]↑ ∧ (intrange_64 n) ∧
                        fb_has_spec_in genv sp_rec fb rec_spec⌝
                        ∗ knot_frag (Some f))%I),
          (λ vret, (⌜vret = (Vint (Z.of_nat (f n)))↑⌝ ∗ knot_frag (Some f))%I))).

  Definition knot_rec_sp : specmap := {[speckey_fn KnotHdr.rec := fspec_to_rel rec_spec]}.

  Definition knot_spec : fspec :=
    fspec_simple (X:=nat → nat)
      (λ f, 
        ((λ varg, (⌜∃ fb, varg = [Vptr (fb, 0%Z)]↑ ∧ fb_has_spec_in genv sp_fun fb (fun_gen f)⌝ ∗
          (∃ old, knot_frag old))%I,
        (λ vret, (⌜∃ fb, vret = (Vptr (fb, 0%Z))↑ ∧ fb_has_spec_in genv sp_rec fb rec_spec⌝ ∗
          knot_frag (Some f))%I)))).

  Definition knot_sp : specmap :=
    {[speckey_fn KnotHdr.rec := fspec_to_rel rec_spec;
      speckey_fn KnotHdr.knot := fspec_to_rel knot_spec]}.

  Definition scopes := ["Knot"].

  Definition fnsems : fnsemmap :=
    {[Some KnotHdr.rec := Some (msk_scp scopes msk_true, (fsp_some rec_spec, pure_body));
      Some KnotHdr.knot := Some (msk_scp scopes msk_true, (fsp_some (knot_spec), fbody_trivial))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := (var_points_to KnotHdr._f (Vint 0) ∗ knot_full None)%I.

  Definition t sp := SMod.to_mod sp smod.
End KnotA. End KnotA.

Lemma knot_alloc `{!crisG Γ Σ α β τ _S _I, _KNOTPRE: !knotGpreS} :
  ⊢ o=> ∃ (_ : knotGS), KnotA.knot_full None ∗ KnotA.knot_frag None.
Proof.
  iMod (own_alloc (● (Excl' None) ⋅ ◯ (Excl' None))) as "[%γ [? ?]]".
  { apply auth_both_valid_discrete; split; done. }
  by iExists (Build_knotGS _ _ _ _ _ _ _ _ _ γ); iFrame.
Qed.