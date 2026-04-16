Require Import CRIS.
Require Export ImpPrelude SchA SchTactics MemA.
Require Import IncrHeader.
From iris Require Import frac_auth numbers.

Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Class incrG := { incr_inG :: inG (frac_authR ZR) Γ; }.
  Definition incrΓ : HRA := #[frac_authR ZR].
  Global Instance subG_incrG : subG incrΓ Γ → incrG.
  Proof. solve_inG. Defined.
End RA.

Module ClientA. Section ClientA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !incrG}.

  Definition counter γ q (v : Z) : iProp Σ := own γ (◯F{q} v).
  Definition counter_syn {n} γ q (v : Z) : GTerm.t n := sown γ (◯F{q} v).
  Definition counter_auth γ (v : Z) : iProp Σ := own γ (●F v).

  Definition syn_ccounter {n} γ bofs : GTerm.t n :=
    (∃ v : τ{Z, n},
      bofs ↦ Vint v ∗
      sown γ (frac_auth_auth v))%SAT.
  Definition ccounter γ bofs : iProp Σ :=
    (∃ v : Z,
      bofs ↦ Vint v ∗
      own γ (frac_auth_auth v))%I.
  Global Instance slred_ccounter n γ bofs : SLRed n (syn_ccounter γ bofs) (ccounter γ bofs).
  Proof. solve_sl_red. Qed.

  Definition incr_inv n N γ bofs : iProp Σ := inv n (N .@ "client") (syn_ccounter γ bofs).

  (* rules *)
  Lemma counter_op γ v1 q1 v2 q2 :
    counter γ q1 v1 ∗ counter γ q2 v2 ⊣⊢ counter γ (q1 + q2) (v1 ⋅ v2).
  Proof. rewrite /counter -own_op -frac_auth_frag_op //. Qed.

  Lemma counter_incr v' γ v1 q1 v2 :
    counter γ q1 v1 ∗ counter_auth γ v2 ==∗ counter γ q1 (v1 + v') ∗ counter_auth γ (v2 + v').
  Proof.
    rewrite /counter /counter_auth -own_op. iIntros "C".
    iMod (own_update with "C") as "[C CA]".
    { rewrite comm. eapply frac_auth_update, (Z_local_update _ _ (v2 + v') (v1 + v')); lia. }
    iFrame; done.
  Qed.

  Definition incr_spec N : fspec :=
    fspec_sch (↑N)
      (fspec_mk
        (λ '(bofs, v, γ) varg arg,
          ⌜varg = ([Vptr bofs]↑↑)↑ ∧ arg = varg⌝ ∗ counter γ (1/2) v ∗ incr_inv 0 N γ bofs)
        (λ '(bofs, v, γ) vret ret, ⌜vret = (tt↑↑)↑ ∧ ret = vret⌝ ∗ counter γ (1/2) (v + 2)))%I.

  Definition sp N : specmap :=
    {[fid ClientHdr.thread @ incr_spec (N)]}.

  (* Module definition *)
  Definition scopes : list string := [].

  Definition incr : list val → itree crisE unit :=
    λ _, 𝒴;;; Ret tt.

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; 'ptr_raw : val <- trigger (Choose val);;
      𝒴;;; tid1 <- Sch.spawn (ClientHdr.thread.1, [ptr_raw]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (ClientHdr.thread.1, [ptr_raw]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; trigger (IO (I:=val) "OUT" 4%Z);;;
      𝒴;;; Ret (tt↑).

  Definition fnsems (N : namespace) : fnsemmap :=
    {[fid ClientHdr.thread # (msk_scp scopes msk_true, (fsp_some (incr_spec N), cfunN (fntyp _ _) (sfunN ClientHdr.thread incr)));
      entry # (msk_scp scopes msk_true, (fsp_some (fspec_sch (↑N) fspec_trivial), main))]}.

  Program Definition smod N : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems N;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t N sp : Mod.t := SMod.to_mod sp (smod N).
End ClientA. End ClientA.
