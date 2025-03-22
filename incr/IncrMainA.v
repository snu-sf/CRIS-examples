Require Import CRIS.
Require Export ImpPrelude IncrMainHeader SchHeader SchA SchTactics MemHeader MemA.
From iris Require Import frac_auth numbers.

Class IncrMainAGΓ (Γ : HRA) := {
  #[local] RA_inG :: inG (frac_authR ZR) Γ;
}.
Definition IncrMainAΓ : HRA := #[frac_authR ZR].
Global Instance subG_GΓ {Γ : HRA} : subG IncrMainAΓ Γ → IncrMainAGΓ Γ.
Proof. solve_inG. Defined.
Hint Unfold subG_GΓ IncrMainAΓ : GRA_index.

Module IncrMainAS. Section IncrMainAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition main_spec u : fspec :=
    w_fspec_sch u (fspec_simple (λ _ : unit, (λ arg, ⌜arg = tt↑⌝, λ ret, ⌜ret = tt↑⌝)))%I.

  Definition N_main : namespace := (nroot .@ MainHdr.main).

  Definition counter γ q (v : Z) : iProp Σ := own γ (◯F{q} v).
  Definition counter_syn {n} γ q (v : Z) : GTerm.t n := <own> γ (◯F{q} v).
  Definition counter_auth γ (v : Z) : iProp Σ := own γ (●F v).

  Definition ccounter_syn n γ blk ofs : GTerm.t n :=
    (∃ v : τ{Z, n},
      <own> base_γ (mem_points_to_singleton_r (blk, ofs) 1%Qp (Vint v))
      ∗ <own> γ (frac_auth_auth v))%SAT.

  Definition f_inv u n γ blk ofs : iProp Σ :=
    inv u n N_main (ccounter_syn n γ blk ofs).

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

  Definition f_spec u : fspec :=
    w_fspec_sch u
      (fspec_simple (λ '(blk, ofs, v, γ),
        (λ varg, ⌜varg = ([Vptr blk ofs]↑↑)↑⌝ ∗ counter γ (1/2) v ∗ f_inv u 0 γ blk ofs,
        λ vret, ⌜vret = (tt↑↑)↑⌝ ∗ counter γ (1/2) (v + 1))
      ))%I.

  Definition spc u : alist string fspec :=
    [(MainHdr.main, main_spec u);
     (MainHdr.f,    f_spec u)].
End IncrMainAS. End IncrMainAS.

Module IncrMainA. Section IncrMainA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !IncrMainAGΓ Γ}.

  Definition scopes : list string := [].

  Definition main : unit → itree hmodE unit :=
    λ _,
      𝒴;;; 'ptr_raw : val <- ccallU MemHdr.alloc [Vint 1%Z];;
      𝒴;;; tid1 <- Sch.spawn ("f", [ptr_raw]↑↑);;
      𝒴;;; tid2 <- Sch.spawn ("f", [ptr_raw]↑↑);;
      𝒴;;; Sch.join tid1;;;
      𝒴;;; Sch.join tid2;;;
      𝒴;;; trigger (IO (O:=unit) "OUT" 2%Z);;;
      𝒴;;; Ret tt.

  Definition f : list val → itree hmodE unit :=
    λ _, 𝒴;;; Ret tt.

  Definition fnsems u :=
    [(MainHdr.main, (scopes, mk_specbody (IncrMainAS.main_spec u) (cfunN main)));
     (MainHdr.f,    (scopes, mk_specbody (IncrMainAS.f_spec u) (cfunN (sfunN f))))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems u;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u spc : HMod.t :=
    Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) spc (Mod u)).
End IncrMainA. End IncrMainA.
