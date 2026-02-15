Require Import CRIS.
Require Import LockHeader.
Require Import ImpPrelude MemHeader MemA.
Require Import SchHeader SchA.
From iris Require Import excl.

(** Specification Module of the spinlock library *)

(* Resource algebra *)
(* Structure of the resource algebra definition is similar to that of iris,
  but few differences exist. *)
Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  
  Class spinlockG `{!crisG Γ Σ α β τ _S _I} := {
    spinlock_inG :: inG (exclR unitO) Γ;
  }.
  Definition spinlockΓ : HRA := #[exclR unitO].
  Global Instance subG_spinlockG : subG spinlockΓ Γ → spinlockG.
  Proof. solve_inG. Defined.
End RA.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module LockA. Section LockA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS, _SPINLOCK: !spinlockG}.

  Definition N_SpinLockA := nroot .@ "spin_lock".

  Definition token n γ : GTerm.t n := sown γ (Excl ()).

  Definition lock_inv {n} bofs (P : GTerm.t n) γ : GTerm.t n :=
    bofs ↦ (Vint 1)
    ∨ bofs ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} γ val P : iProp Σ :=
    ∃ bofs, ⌜val = Vptr bofs⌝ ∗ inv n N_SpinLockA (lock_inv bofs P γ).

  (* Function specs *)
  Definition newlock_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (X := {n & GTerm.t n})
        (λ '(existT n P),
          ((λ _, ⟦P⟧),
          (λ ret, ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock γ val P))
      ))%I).

  Definition acquire_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ is_lock γ val (projT2 P)),
          (λ ret, ⌜ret = Vundef↑⌝ ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧))
      )))%I.

  Definition release_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (X := gname * val * {n & GTerm.t n})
        (λ '(γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝
            ∗ is_lock γ val (projT2 P)
            ∗ ⟦token (projT1 P) γ⟧
            ∗ ⟦projT2 P⟧),
          (λ ret, ⌜ret = Vundef↑⌝))
      )))%I.

  Definition sp E : specmap :=
    {[fid SpinLockHdr.newlock @ (newlock_spec E);
      fid SpinLockHdr.acquire @ (acquire_spec E);
      fid SpinLockHdr.release @ (release_spec E)]}.

  (* Module definition *)
  (* Define three components for a module:
    1) scope
    2) code (via itree)
    3) initial state (via Any.t)
  *)
  Definition scopes : list string := [].

  Definition newlock : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).
  Definition acquire : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.
  Definition release : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.

  Definition fnsems (E : coPset) : fnsemmap :=
    {[fid SpinLockHdr.newlock # (msk_scp scopes msk_true, (fsp_some (newlock_spec E), cfunU newlock));
      fid SpinLockHdr.acquire # (msk_scp scopes msk_true, (fsp_some (acquire_spec E), cfunU acquire));
      fid SpinLockHdr.release # (msk_scp scopes msk_true, (fsp_some (release_spec E), cfunU release))]}.

  Program Definition smod E : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems E;
    SMod.initial_st := ∅
  |}.
  Solve All Obligations with mod_tac.

  Definition t E sp : Mod.t := SMod.to_mod sp (smod E).
End LockA. End LockA.
