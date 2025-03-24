Require Import CRIS.
Require Export ImpPrelude IncrHeader SchHeader SchA SchTactics MemHeader MemA.
From iris Require Import frac_auth numbers.

Class IncrAGΓ (Γ : HRA) := {
  #[local] RA_inG :: inG (frac_authR ZR) Γ;
}.
Definition IncrAΓ : HRA := #[frac_authR ZR].
Global Instance subG_GΓ {Γ : HRA} : subG IncrAΓ Γ → IncrAGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_GΓ IncrAΓ : GRA_index.

Module IncrAS. Section IncrAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !IncrAGΓ Γ}.

  Definition N_main : namespace := (nroot .@ IncrHdr.main).

  Definition counter γ q (v : Z) : iProp Σ := own γ (◯F{q} v).
  Definition counter_syn {n} γ q (v : Z) : GTerm.t n := <own> γ (◯F{q} v).
  Definition counter_auth γ (v : Z) : iProp Σ := own γ (●F v).

  Definition ccounter_syn n γ blk ofs : GTerm.t n :=
    (∃ v : τ{Z, n},
      <own> base_γ (mem_points_to_singleton_r (blk, ofs) 1%Qp (Vint v))
      ∗ <own> γ (frac_auth_auth v))%SAT.

  Definition incr_inv u n γ blk ofs : iProp Σ :=
    inv u n N_main (ccounter_syn n γ blk ofs).

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

  Definition incr_spec u : fspec :=
    w_fspec_sch u
      (fspec_simple (λ '(blk, ofs, v, γ),
        (λ varg, ⌜varg = ([Vptr blk ofs]↑↑)↑⌝ ∗ counter γ (1/2) v ∗ incr_inv u 0 γ blk ofs,
        λ vret, ⌜vret = (tt↑↑)↑⌝ ∗ counter γ (1/2) (v + 2))
      ))%I.

  Definition main_spec u : fspec :=
    w_fspec_sch u (fspec_simple (λ _ : unit, (λ arg, ⌜arg = tt↑⌝, λ ret, ⌜ret = tt↑⌝)))%I.

  Definition spc u : alist string fspec :=
    [(IncrHdr.incr, incr_spec u);
     (IncrHdr.main, main_spec u)].
End IncrAS. End IncrAS.

Module IncrA. Section IncrA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !IncrAGΓ Γ}.

  Definition scopes : list string := [].

  Definition incr : list val → itree hmodE unit :=
    λ _, 𝒴;;; Ret tt.

  Definition main : unit → itree hmodE unit :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemHdr.alloc [Vint 1%Z];;
      𝒴;;; tid1 <- Sch.spawn (IncrHdr.incr, [ptr_raw]↑↑);;
      𝒴;;; tid2 <- Sch.spawn (IncrHdr.incr, [ptr_raw]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; trigger (IO (O:=unit) "OUT" 4%Z);;;
      𝒴;;; Ret tt.

  Definition fnsems u :=
    [(IncrHdr.incr, (scopes, mk_specbody (IncrAS.incr_spec u) (cfunN (sfunN incr))));
     (IncrHdr.main, (scopes, mk_specbody (IncrAS.main_spec u) (cfunN main)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems u;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u spc : HMod.t :=
    Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) spc (Mod u)).
End IncrA. End IncrA.