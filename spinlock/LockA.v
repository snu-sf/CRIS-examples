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
  Context `{!sinvG Γ Σ α β τ _I _S}.
  
  Class spinlockG `{!sinvG Γ Σ α β τ _I _S} := {
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
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.
  
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
  Definition newlock_spec E : fspec :=
    fspec_sch E
      (fspec_simple (X := {n & GTerm.t n})
        (λ '(existT n P),
          ((λ _, ⟦P⟧),
          (λ ret, ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock γ val P))
      ))%I.

  Definition acquire_spec E : fspec :=
    fspec_sch E
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock γ val (projT2 P)),
          (λ ret, ⌜ret = Vundef↑⌝ ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧))
      ))%I.

  Definition release_spec E : fspec :=
    fspec_sch E
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝
            ∗ is_lock γ val (projT2 P)
            ∗ ⟦token (projT1 P) γ⟧
            ∗ ⟦projT2 P⟧),
          (λ ret, ⌜ret = Vundef↑⌝))
      ))%I.

  Definition sp E : alist string fspec :=
    [(SpinLockHdr.newlock, newlock_spec E);
     (SpinLockHdr.acquire, acquire_spec E);
     (SpinLockHdr.release, release_spec E)].
End LockAS. End LockAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockA. Section SpinLockA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree hmodE val := λ _, 𝒴;;; trigger (Choose val).
  Definition acquire : list val → itree hmodE val :=
    λ _,
      (iterC (λ _,
        𝒴;;; 'x : bool <- trigger (Choose bool);;
        Ret (if x then inr tt else inl tt)) tt
      );;;
      Ret Vundef.
  Definition release : list val → itree hmodE val := λ _, 𝒴;;; Ret Vundef.

  Definition fnsems u :=
    [(SpinLockHdr.newlock, (wmask_all, scopes, mk_specbody (LockAS.newlock_spec u) (cfunU newlock)));
     (SpinLockHdr.acquire, (wmask_all, scopes, mk_specbody (LockAS.acquire_spec u) (cfunU acquire)));
     (SpinLockHdr.release, (wmask_all, scopes, mk_specbody (LockAS.release_spec u) (cfunU release)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems u;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t u sp : HMod.t := Seal.sealing CRIS SMod.to_hmod sp (Mod u).
End SpinLockA. End SpinLockA.
