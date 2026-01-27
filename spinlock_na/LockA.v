Require Import CRIS.
From CRIS.spinlock_na Require Import Header.
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
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.

  (* Initial resource *)
  Definition ir : spinlockΓ := *[None].

  Definition N_SpinLockA := nroot .@ "spin_lock".

  Definition token n γ : GTerm.t n := sown γ (Excl ()).

  Definition lock_inv {n} bofs (P : GTerm.t n) γ : GTerm.t n :=
    bofs ↦ (Vint 1)
    ∨ bofs ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} γ val P : iProp Σ :=
    ∃ bofs, ⌜val = Vptr bofs⌝ ∗ inv n N_SpinLockA (lock_inv bofs P γ).

  (* Function specs *)
  Definition newlock_spec E q : fspec :=
    fspec_winv E (fspec_sch q
      (fspec_simple (X := {n & GTerm.t n})
        (λ '(existT n P),
          ((λ _, ⟦P⟧),
          (λ ret, ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock γ val P))
      ))%I).

  Definition acquire_spec E q : fspec :=
    fspec_winv E (fspec_sch q
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock γ val (projT2 P)),
          (λ ret, ⌜ret = Vundef↑⌝ ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧))
      )))%I.

  Definition release_spec E q : fspec :=
    fspec_winv E (fspec_sch q
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝
            ∗ is_lock γ val (projT2 P)
            ∗ ⟦token (projT1 P) γ⟧
            ∗ ⟦projT2 P⟧),
          (λ ret, ⌜ret = Vundef↑⌝))
      )))%I.

  Definition sp E q : spl_type :=
    [(Some SpinLockHdr.newlock, fsp_some (newlock_spec E q));
     (Some SpinLockHdr.acquire, fsp_some (acquire_spec E q));
     (Some SpinLockHdr.release, fsp_some (release_spec E q))].
End LockAS. End LockAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockA. Section SpinLockA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition acquire : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.
  Definition release : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.

  Definition fnsems E q : fnsems_type :=
    [(Some SpinLockHdr.newlock, (true, wmask_all, scopes, (fsp_some (LockAS.newlock_spec E q), cfunU newlock)));
     (Some SpinLockHdr.acquire, (true, wmask_all, scopes, (fsp_some (LockAS.acquire_spec E q), cfunU acquire)));
     (Some SpinLockHdr.release, (true, wmask_all, scopes, (fsp_some (LockAS.release_spec E q), cfunU release)))].

  Program Definition smod E q : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems E q;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t E q sp : Mod.t := Seal.sealing CRIS (SMod.to_mod sp (smod E q)).
End SpinLockA. End SpinLockA.
