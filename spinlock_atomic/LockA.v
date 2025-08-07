Require Import CRIS.
From CRIS.spinlock Require Import Header.
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

  Definition token n γ : GTerm.t n := <own> γ (Excl ()).

  Definition lock_inv {n} bofs (P : GTerm.t n) γ : GTerm.t n :=
    bofs ↦ (Vint 1)
    ∨ bofs ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} γ val P : iProp Σ :=
    ∃ bofs, ⌜val = Vptr bofs⌝ ∗ inv n N_SpinLockA (lock_inv bofs P γ).

  (* Function specs *)
  Definition newlock_spec : fspecS :=
    from_fspec
      (fspec_winv (↑N_SpinLockA) (* namespace for invariant access *)
        (fspec_simple (X := {n & GTerm.t n})
          (λ '(existT n P),
            ((λ _, ⟦P⟧),
             (λ ret, ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock γ val P)))))%I.

  Definition acquire_spec : fspecS :=
    from_fspec
      (fspec_winv (↑N_SpinLockA)
        (fspec_simple
          (λ '(γ, val, P),
            ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock γ val (projT2 P)),
             (λ ret, ⌜ret = Vundef↑⌝ ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧)))))%I.

  Definition release_spec : fspecS :=
    from_fspec
      (fspec_winv (↑N_SpinLockA)
        (fspec_simple
          (λ '(γ, val, P),
            ((λ arg, ⌜arg = [val]↑⌝ ∗
              is_lock γ val (projT2 P) ∗
              ⟦token (projT1 P) γ⟧ ∗
              ⟦projT2 P⟧),
            (λ ret, ⌜ret = Vundef↑⌝)))))%I.
End LockAS. End LockAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockA. Section SpinLockA.
  Context `{!crisG Γ Σ α β τ _S _I, !memG, !schG, !spinlockG}.

  Definition scopes : list string := [].

  Definition newlock : Any.t → itree crisE Any.t :=
    fspec_proph_update (list val) val LockAS.newlock_spec (λ _, 𝒴;;; Ret (tt↑)).

  Definition acquire : Any.t → itree crisE Any.t :=
    λ arg,
      ret <- fspec_proph_update_option (list val) val LockAS.acquire_spec (λ _, 𝒴;;; Ret tt↑) arg;;
      𝒴;;; Ret ret.

  Definition release : Any.t → itree crisE Any.t :=
    λ arg,
      ret <- fspec_proph_update (list val) val LockAS.release_spec (λ _, 𝒴;;; Ret tt↑) arg;;
      𝒴;;; Ret ret.

  Definition fnsems : fnsems_type :=
    [(Some SpinLockHdr.newlock, (false, wmask_all, scopes, (None, newlock)));
     (Some SpinLockHdr.acquire, (false, wmask_all, scopes, (None, acquire)));
     (Some SpinLockHdr.release, (false, wmask_all, scopes, (None, release)))].

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End SpinLockA. End SpinLockA.
