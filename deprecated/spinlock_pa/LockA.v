(* Require Import CRIS.
From CRIS.spinlock_pa Require Import Header.
Require Import ImpPrelude MemHeader MemA.
Require Import SchHeader SchA.
From iris Require Import excl.

(** Specification Module of the spinlock library *)

(* Resource algebra *)
(* Structure of the resource algebra definition is similar to that of iris,
  but few differences exist. *)
(* HRAs are structs similar to GRAs, but for RAs that sProps can own. *)
Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Class spinlockG `{!crisG Γ Σ α β τ _S _I} := {
    spinlock_inG :: inG (exclR unitO) Γ;
  }.
  Definition spinlockΓ : HRA := #[exclR unitO].
  (* Be sure to annotate Γ as HRA, or tc search may not work properly. *)
  Global Instance subG_spinlockG : subG spinlockΓ Γ → spinlockG.
  Proof. solve_inG. Defined.
  (* Be sure to add these two instances to hint database so that we can resolve inG instances
    in the cancellation phase. *)
End RA.
Hint Unfold subG_spinlockG spinlock_inG : GRA_index.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module LockAS. Section LockAS.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG, !spinlockG}.

  (* Initial resource *)
  Definition ir : spinlockΓ := *[None].

  Definition N_SpinLockA := nroot .@ "spin_lock".

  Definition token n γ : GTerm.t n := sown γ (Excl ()).

  Definition lock_inv {n} bofs (P : GTerm.t n) γ : GTerm.t n :=
    bofs ↦ (Vint 1)
    ∨ bofs ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} γ v P : iProp Σ :=
    ∃ bofs, ⌜v = Vptr bofs⌝ ∗ inv n N_SpinLockA (lock_inv bofs P γ).

  (* Function specs *)

  Definition newlock_spec E : fspec :=
      (fspec_winv E (* namespace for invariant access *)
         (fspec_simple (X:= {n : level & GTerm.t n})
           (λ '(existT n P),
            ((λ arg, ⌜∃ v: list val, arg = v↑⌝ ∗ ⟦P⟧),
             (λ ret, ∃ v γ, ⌜ret = v↑⌝ ∗ is_lock γ v P))%I))).

  Definition acquire_spec E : fspec :=
      (fspec_winv E
         (fspec_simple (X:= (_ * _ * {n & GTerm.t n}))
            (λ '(γ, v, (existT n P)),
             ((λ arg, ⌜arg = [v]↑⌝ ∗ is_lock γ v P),
              (λ ret, ⌜ret = Vundef↑⌝ ∗ ⟦token n γ⟧ ∗ ⟦P⟧))%I))).

  Definition release_spec E : fspec :=
      (fspec_winv E
         (fspec_simple (X:= (_ * _ * {n & GTerm.t n}))
            (λ '(γ, v, (existT n P)),
              ((λ arg, ⌜arg = [v]↑⌝ ∗
                       is_lock γ v P ∗
                       ⟦token n γ⟧ ∗
                       ⟦P⟧),
               (λ ret, ⌜ret = Vundef↑⌝))%I))).

End LockAS. End LockAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockA. Section SpinLockA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG, !spinlockG}.
  Context `{E: coPset}.
  
  Definition scopes : list string := [].

  Definition newlock E : Any.t → itree crisE Any.t :=
    λ arg,
      ret <- lat_real false (LockAS.newlock_spec E) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.

  Definition acquire E : Any.t → itree crisE Any.t :=
    λ arg,
      ret <- lat_real true (LockAS.acquire_spec E) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.

  Definition release E : Any.t → itree crisE Any.t :=
    λ arg,
      ret <- lat_real false (LockAS.release_spec E) 𝒴 fbody_trivial arg;; 𝒴;;; Ret ret.

  Definition fnsems E : fnsems_type :=
    [(Some SpinLockHdr.newlock, (false, wmask_all, scopes, (None, newlock E)));
     (Some SpinLockHdr.acquire, (false, wmask_all, scopes, (None, acquire E)));
     (Some SpinLockHdr.release, (false, wmask_all, scopes, (None, release E)))].

  Program Definition smod E: SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems E;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t E : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none (smod E)).
End SpinLockA. End SpinLockA. *)
