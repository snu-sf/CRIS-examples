(* Require Import CRIS.
Require Import SpinLockI.
Require Import SchHeader SchA.
Require Import PFMemHeader PFMemUser.
Require Import HistoryRA AtomicRA OneShotRA.

(** Specification Module of the spinlock library *)

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module SpinLockA. Section SpinLockA.
  Context `{!crisG Γ Σ α β τ _S _I, !histGS, !atomicG, !schG, !one_shotG}.

  Definition N_SpinLock := nroot .@ "spin_lock".

  Definition lock_inv {n} loc (P : GTerm.t n) γ : GTerm.t n :=
    loc ↦ Val.one
    ∨ loc ↦ Val.zero ∗ P ∗ <own> γ Pending.

  Definition is_lock {n} u γ val P : iProp Σ :=
    ∃ bofs, ⌜val = Vptr bofs⌝ ∗ inv u n N_SpinLockA (lock_inv bofs P γ).

  (* Function specs *)
  Definition newlock_spec u : fspec :=
    wsim_fspec u
      (fspec_simple (X := nat * {n & GTerm.t n})
        (λ '(tid, (existT n P)),
          ((λ _, SchAS.tid_user tid ∗ ⟦P⟧),
          (λ ret, SchAS.tid_user tid ∗ ∃ val γ, ⌜ret = val↑⌝ ∗ is_lock u γ val P))
      ))%I.

  Definition acquire_spec u : fspec :=
    wsim_fspec u
      (fspec_simple (X := nat * gname * val * {n & GTerm.t n})
        (λ '(tid, γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝ ∗ SchAS.tid_user tid ∗ is_lock u γ val (projT2 P)),
          (λ ret, ⌜ret = Vundef↑⌝ ∗ SchAS.tid_user tid ∗ ⟦token (projT1 P) γ⟧ ∗ ⟦projT2 P⟧))
      ))%I.

  Definition release_spec u : fspec :=
    wsim_fspec u
      (fspec_simple (X := nat * gname * val * {n & GTerm.t n})
        (λ '(tid, γ, val, P),
          ((λ arg, ⌜arg = [val]↑⌝
            ∗ SchAS.tid_user tid
            ∗ is_lock u γ val (projT2 P)
            ∗ ⟦token (projT1 P) γ⟧
            ∗ ⟦projT2 P⟧),
          (λ ret, ⌜ret = Vundef↑⌝
            ∗ SchAS.tid_user tid))
      ))%I.

  Definition sp u : alist string fspec :=
    [(SpinLockHdr.newlock, newlock_spec u);
     (SpinLockHdr.acquire, acquire_spec u);
     (SpinLockHdr.release, release_spec u)].
End SpinLockAS. End SpinLockAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockA. Section SpinLockA.
  Context `{_sinvGpreS: !crisG Γ Σ α β τ _S _I}.
  Context `{_memGS: !memGS}.
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
    [(SpinLockHdr.newlock, (wmask_all, scopes, mk_specbody (SpinLockAS.newlock_spec u) (cfunU newlock)));
     (SpinLockHdr.acquire, (wmask_all, scopes, mk_specbody (SpinLockAS.acquire_spec u) (cfunU acquire)));
     (SpinLockHdr.release, (wmask_all, scopes, mk_specbody (SpinLockAS.release_spec u) (cfunU release)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems u;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t u sp : HMod.t := Seal.sealing CRIS SMod.to_hmod sp (Mod u).
End SpinLockA. End SpinLockA. *)
