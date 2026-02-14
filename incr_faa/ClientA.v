Require Import CRIS.
Require Export ImpPrelude SchA SchTactics MemA.
Require Import FaaHeader.
From iris Require Import frac_auth numbers.

Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Class incrG := { incr_inG :: inG (frac_authR ZR) Γ; }.
  Definition incrΓ : HRA := #[frac_authR ZR].
  Global Instance subG_incrG : subG incrΓ Γ → incrG.
  Proof. solve_inG. Defined.
End RA.

Module ClientA. Section ClientA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, _INCR: !incrG}.

  Definition N_main N : namespace := (N .@ IncrHdr.main).

  Definition counter γ q (v : Z) : iProp Σ := own γ (◯F{q} v).
  Definition counter_syn {n} γ q (v : Z) : GTerm.t n := sown γ (◯F{q} v).
  Definition counter_auth γ (v : Z) : iProp Σ := own γ (●F v).

  Definition ccounter_syn n γ bofs : GTerm.t n :=
    (∃ v : τ{Z, n},
      bofs ↦ Vint v ∗
      sown γ (frac_auth_auth v))%SAT.

  Definition incr_inv n N γ bofs : iProp Σ := inv n (N_main N) (ccounter_syn n γ bofs).

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

  (* Definition init_cond E : iProp Σ := winv (E, E) ∗ Tid 0 0. *)

  Definition sp N : specmap :=
    {[speckey_fn IncrHdr.incr := fspec_to_rel (incr_spec N)]}.

  (* Module definition *)
  Definition scopes : list string := [].

  Definition incr : list val → itree crisE unit :=
    λ _, 𝒴;;; Ret tt.

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; 'ptr_raw : val <- trigger (Choose val);;
      𝒴;;; tid1 <- Sch.spawn (IncrHdr.incr, [ptr_raw]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (IncrHdr.incr, [ptr_raw]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; trigger (IO (O:=unit) "OUT" 4%Z);;;
      𝒴;;; Ret (tt↑).

  Definition fnsems (N : namespace) : fnsemmap :=
    {[Some IncrHdr.incr := Some (msk_scp scopes msk_true, (fsp_some (incr_spec N), cfunN (sfunN incr)));
      None := Some (msk_scp scopes msk_true, (fsp_some (fspec_sch (↑N) fspec_trivial), main))]}.

  Program Definition smod N : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems N;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t N sp : Mod.t := SMod.to_mod sp (smod N).
End ClientA. End ClientA.
