Require Import CRIS.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.
From iris.bi.lib Require Import fractional.
From CRIS Require Export MemHeader ProphecyHeader HelpingHeader.

(* Memory resource algebra *)
Canonical Structure valO := leibnizO val.
Local Definition frac_valO := dfrac_agreeR valO.
Local Definition _memRA := (mblock -d> Z -d> optionUR frac_valO).
Local Definition memRA := authUR _memRA.
Class memGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mem_inG :: inG memRA Γ;
}.
Class memGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] memGS_memGSpreS :: memGpreS;
  mem_name : gname;
}.
Definition memΓ : HRA := #[memRA].
Global Instance subG_memGS `{!crisG Γ Σ α β τ _S _I} : subG memΓ Γ → memGpreS.
Proof. solve_inG. Defined.

Local Existing Instances memGS_memGSpreS mem_inG.

Section MEM.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  (* Initial resources for memory *)
  Definition mem_init_val (csl : string → bool) (genv : GEnv.t) (blk : mblock) ofs : option Z :=
    match genv !! blk with
    | Some (g, gd) =>
      match gd↓ with
      | Some (Gvar gv) => if negb (csl g) && (bool_decide (ofs = 0%Z)) then Some gv else None
      | _ => None
      end
    | None => None
    end.

  Definition mem_init_auth_r (csl : string → bool) (genv : GEnv.t) : memRA :=
    ● ((λ blk ofs,
        match mem_init_val csl genv blk ofs with
        | Some gv => Some (to_dfrac_agree (DfracOwn 1) (Vint gv))
        | _ => ε
        end) : _memRA).

  Definition mem_init_frag_r (csl : string → bool) (genv : GEnv.t) : memRA :=
    ◯ ((λ blk ofs,
        match mem_init_val csl genv blk ofs with
        | Some gv => Some (to_dfrac_agree (DfracOwn 1) (Vint gv))
        | _ => ε
        end) : _memRA).

  Definition mem_init_auth csl genv : iProp Σ :=
    own mem_name (mem_init_auth_r csl genv).

  Definition mem_init_frag csl genv : iProp Σ :=
    own mem_name (mem_init_frag_r csl genv).

  Definition mem_init csl genv : iProp Σ :=
    own mem_name (mem_init_auth_r csl genv ⋅ mem_init_frag_r csl genv).
End MEM.

Lemma mem_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !memGpreS} csl genv :
  ⊢ o=> ∃ (_ : memGS), mem_init csl genv.
Proof.
  iMod (own_alloc (mem_init_auth_r csl genv ⋅ mem_init_frag_r csl genv)) as "[%γm M]".
  { apply auth_both_valid_discrete; split; ss; ii; des_ifs. }
  pose (Build_memGS _ _ _ _ _ _ _ _ _ γm) as Hmem.
  by iExists Hmem; iFrame.
Qed.

Local Arguments Z.of_nat : simpl nomatch.

Section MemRA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition mem_val : Type := Qp * val.

  Definition _points_to_r (loc : mblock * Z) (q : dfrac) (mvs : list val) : _memRA :=
    let (b, ofs) := loc in
    λ _b _ofs,
      if bool_decide (_b = b ∧ (ofs <= _ofs < (ofs + Z.of_nat (List.length mvs))))%Z
      then match (mvs !! (Z.to_nat (_ofs - ofs))) with
        | Some v => Some (to_dfrac_agree q v)
        | None => ε
        end
      else ε.

  Definition mem_points_to_singleton_r (loc : mblock * Z) (q : dfrac) (v : val) : memRA :=
    ◯ (discrete_fun_singleton loc.1 (discrete_fun_singleton loc.2 (Some (to_dfrac_agree q v)))).
  Definition mem_points_to_singleton (loc : mblock * Z) (q : dfrac) (v : val) : iProp Σ :=
    own mem_name (mem_points_to_singleton_r loc q v).

  Definition mem_points_to : (mblock * Z) → dfrac → list val → iProp Σ :=
    λ '(blk, ofs) q vs, ([∗ list] i ↦ v ∈ vs, mem_points_to_singleton (blk, ofs + i)%Z q v)%I.

  Global Instance mem_points_to_singleton_fractional l v :
    Fractional (λ q, mem_points_to_singleton l (DfracOwn q) v)%I.
  Proof.
    destruct l. rewrite /mem_points_to_singleton /mem_points_to_singleton_r /=.
    intros p q; rewrite -own_op -auth_frag_op discrete_fun_singleton_op.
    rewrite auth_frag_proper; first refl.
    rewrite discrete_fun_singleton_proper; first refl.
    rewrite discrete_fun_singleton_op -Some_op. do 2 f_equiv.
    rewrite -dfrac_agree_op -dfrac_op_own //.
  Qed.
  Global Instance mem_points_to_singleton_as_fractional l v q :
    AsFractional
      (mem_points_to_singleton l (DfracOwn q) v)
      (λ q, mem_points_to_singleton l (DfracOwn q) v)%I q.
  Proof. econs; ss. apply _. Qed.
  Global Instance mem_points_to_persistent loc v :
    Persistent (mem_points_to_singleton loc DfracDiscarded v).
  Proof. apply _. Qed.

  Lemma mem_points_to_singleton_agree (loc : mblock * Z) (q1 q2 : dfrac) (v1 v2 : val) :
    mem_points_to_singleton loc q1 v1 -∗
    mem_points_to_singleton loc q2 v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    destruct loc.
    rewrite /mem_points_to_singleton /mem_points_to_singleton_r /=; iIntros "H1 H2".
    iPoseProof (own_valid_2 with "H1 H2") as "%WF".
    apply auth_frag_op_valid_1 in WF.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF.
    rewrite discrete_fun_singleton_op discrete_fun_singleton_valid in WF.
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in WF; des; clarify.
  Qed.

  Lemma mem_points_to_singleton_valid (loc : mblock * ptrofs) (q1 q2 : Qp) (v1 v2 : val) :
    mem_points_to_singleton loc (DfracOwn q1) v1 -∗
    mem_points_to_singleton loc (DfracOwn q2) v2 -∗
    ⌜q1 + q2 ≤ 1⌝%Qp.
  Proof.
    rewrite /mem_points_to_singleton; iIntros "a b"; iCombine "a b" gives %wf.
    rewrite /mem_points_to_singleton_r -auth_frag_op discrete_fun_singleton_op in wf.
    rewrite auth_frag_valid in wf; specialize (wf loc.1).
    rewrite discrete_fun_lookup_singleton discrete_fun_singleton_op in wf.
    specialize (wf loc.2); rewrite discrete_fun_lookup_singleton in wf.
    rewrite -Some_op Some_valid dfrac_agree_op_valid_L in wf.
    rewrite dfrac_op_own dfrac_valid in wf; by des.
  Qed.

  Lemma mem_init_auth_r_valid (csl : string → bool) (genv : GEnv.t) blk ofs v :
    mem_init_val csl genv blk ofs = Some v →
    mem_points_to_singleton_r (blk, ofs) (DfracOwn 1) (Vint v) ≼ mem_init_frag_r csl genv.
  Proof.
    intros H'. rewrite /mem_init_auth_r /mem_points_to_singleton_r /mem_init_val; ss.
    rewrite /mem_init_frag_r. apply auth_frag_mono.
    match goal with
    | |- _ ≼ ?f' => remember f' as f
    end.
    exists ((λ blk' ofs', if (decide (blk = blk' ∧ ofs = ofs')) then ε else (f blk' ofs'))).
    intros b o; clarify; rewrite ?discrete_fun_lookup_op; des_ifs; des; clarify.
    { rewrite right_id !discrete_fun_lookup_singleton //. }
    { apply not_and_or in n; des; bsimpl; des; ss; subst; ss.
      { rewrite !discrete_fun_lookup_singleton_ne; et. }
      { destruct (dec b blk); subst; ss.
        { rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; et. }
        { rewrite !discrete_fun_lookup_singleton_ne; et. }
      }
    }
    { apply not_and_or in n; des; bsimpl; des; ss; subst; ss.
      { rewrite !discrete_fun_lookup_singleton_ne; et. }
      { destruct (dec b blk); subst; ss.
        { rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne; et. }
        { rewrite !discrete_fun_lookup_singleton_ne; et. }
      }
    }
  Qed.
End MemRA.

Section syn_mem.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition syn_mem_points_to_singleton {n} loc q v : GTerm.t n :=
    sown mem_name ((mem_points_to_singleton_r loc q v): memRA).

  Definition syn_mem_points_to {n} : (mblock * Z) → dfrac → list val → GTerm.t n :=
    λ '(blk, ofs) q vs, ([∗ list] i ↦ v ∈ vs, syn_mem_points_to_singleton (blk, ofs + i)%Z q v)%SAT.
End syn_mem.

Reserved Notation "l '↦{' q '}' v"
  (at level 20, q at level 1, format "l  ↦{ q }  v").
Reserved Notation "l ↦ v"
  (at level 20, format "l  ↦  v").
Reserved Notation "l '|->{' q '}' vs"
  (at level 20, q at level 1, format "l  |->{ q }  vs").
Reserved Notation "l |-> vs"
  (at level 20, format "l  |->  vs").

Notation "loc ↦{ q } v" := (mem_points_to_singleton loc (DfracOwn q) v)%I : bi_scope.
Notation "loc ↦ v" := (mem_points_to_singleton loc (DfracOwn 1) v)%I : bi_scope.
Notation "loc |->{ q } vs" := (mem_points_to loc (DfracOwn q) vs)%I : bi_scope.
Notation "loc |-> vs" := (mem_points_to loc (DfracOwn 1) vs)%I : bi_scope.

Notation "loc ↦{ q } v" := (syn_mem_points_to_singleton loc (DfracOwn q) v)%SAT : SAT_scope.
Notation "loc ↦ v" := (syn_mem_points_to_singleton loc (DfracOwn 1) v)%SAT : SAT_scope.
Notation "loc |->{ q } vs" := (syn_mem_points_to loc (DfracOwn q) vs)%SAT : SAT_scope.
Notation "loc |-> vs" := (syn_mem_points_to loc (DfracOwn 1) vs)%SAT : SAT_scope.

Section reduction.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Global Instance mem_points_to_singleton_red n loc q v :
    SLRed n (loc ↦{q} v) (loc ↦{q} v).
  Proof. solve_sl_red. Qed.

  Global Instance mem_points_to_red n loc q vs :
    SLRed n (loc |->{q} vs) (loc |->{q} vs).
  Proof. destruct loc as [blk ofs]. solve_sl_red. Qed.
End reduction.

Global Opaque mem_points_to_singleton_r.
Arguments mem_points_to_singleton_r : simpl never.

(* Memory specification *)
Module MemA. Section MemA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition alloc : fspec :=
    fspec_simple (λ sz,
      (λ arg, ⌜arg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝,
      λ ret, ∃ b, ⌜ret = (Vptr (b, 0%Z))↑⌝ ∗ (b, 0%Z) |-> replicate sz Vundef))%I.

  Definition free : fspec :=
    fspec_simple (λ '(b, ofs, v),
      (λ arg, ⌜arg = [Vptr (b, ofs)]↑⌝ ∗ (b, ofs) ↦ v,
      λ ret, ⌜ret = (Vint 0)↑⌝))%I.

  Definition load : fspec :=
    fspec_simple (λ '(b, ofs, q, v),
      (λ arg, ⌜arg = [Vptr (b, ofs)]↑⌝ ∗ (b, ofs) ↦{q} v,
      λ ret, (b, ofs) ↦{q} v ∗ ⌜ret = v↑⌝))%I.

  Definition store : fspec :=
    fspec_simple (λ '(b, ofs, v_old, v_new),
       (λ arg, ⌜arg = [Vptr (b, ofs) ; v_new]↑⌝ ∗ (b, ofs) ↦ v_old,
        λ ret, (b, ofs) ↦ v_new ∗ ⌜ret = (Vint 0)↑⌝))%I.

  Definition val_r (arg : val) q v : iProp Σ :=
    match arg with
    | Vptr (b, ofs) => (b, ofs) ↦{q} v
    | _ => True%I
    end.

  Definition compare_val (v0 v1: val) : val :=
    match v0, v1 with
    | Vint i0, Vint i1 => Vint (if bool_decide (i0 = i1) then 1 else 0)
    | Vint 0, Vptr _ => Vint 0
    | Vptr _, Vint 0 => Vint 0
    | Vptr (b0,ofs0), Vptr (b1,ofs1) =>
       if bool_decide (b0 = b1 ∧ ofs0 = ofs1) then Vint 1 else Vint 0
    | _, _ => Vundef
    end.

  Definition cmp :=
    fspec_simple (λ '(v1, v2, succ, E),
      (λ arg,
        ⌜arg = [v1; v2]↑ ∧ compare_val v1 v2 = Vint succ⌝ ∗ E ∗
        (E ==∗ ∃ q0 q1 v1' v2', val_r v1 q0 v1' ∗ val_r v2 q1 v2' ∗
          (val_r v1 q0 v1' ∗ val_r v2 q1 v2' ==∗ E)),
       λ ret, ⌜ret = (Vint succ)↑⌝ ∗ E))%I.

  Definition cas : fspec :=
    fspec_simple (λ '(b, ofs, v_cur, v_old, v_new, succ, E),
      (λ arg, ⌜arg = [Vptr (b, ofs); v_old; v_new]↑ ∧ compare_val v_cur v_old = Vint succ⌝ ∗
        (b, ofs) ↦ v_cur ∗ E ∗
        (E ==∗ ∃ q0 q1 v0 v1, val_r v_cur q0 v0 ∗ val_r v_old q1 v1 ∗
          (val_r v_cur q0 v0 ∗ val_r v_old q1 v1 ==∗ E)),
       λ ret, ⌜ret = v_cur↑⌝ ∗
        (b, ofs) ↦ (if bool_decide (succ = 1) then v_new else v_cur) ∗ E))%I.

  Definition scopes : list string := ["Mem"].

  Definition mask : emask := msk_scp scopes (CFilter.msk_filter_in ∅ msk_true).

  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc # (mask, (fsp_some alloc, fbody_trivial));
      fid MemHdr.free  # (mask, (fsp_some free, fbody_trivial));
      fid MemHdr.load  # (mask, (fsp_some load, fbody_trivial));
      fid MemHdr.store # (mask, (fsp_some store, fbody_trivial));
      fid MemHdr.cmp   # (mask, (fsp_some cmp, fbody_trivial));
      fid MemHdr.cas   # (mask, (fsp_some cas, fbody_trivial))]}.

  (* Module definition *)
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond csl genv : iProp Σ := mem_init_auth csl genv.

  Definition t sp : Mod.t := SMod.to_mod sp smod.

  Lemma filter_prophecy mn sp:
    CFilter.filter (Prophecy.exports mn) (t sp) = t sp.
  Proof. cfilter_solver. Qed.

  Lemma filter_helping mn sp:
    CFilter.filter (Helping.exports mn) (t sp) = t sp.
  Proof. cfilter_solver. Qed.

End MemA. End MemA.
