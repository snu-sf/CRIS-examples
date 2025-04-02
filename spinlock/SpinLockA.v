Require Import CRIS.
Require Import ImpPrelude MemHeader MemA SpinLockHeader.
Require Import SchHeader SchA.
From iris Require Import excl.

(** Specification Module of the spinlock library *)

(* Resource algebra *)
(* Structure of the resource algebra definition is similar to that of iris,
  but few differences exist. *)
(* HRAs are structs similar to GRAs, but for RAs that sProps can own. *)
Class SpinLockAGΓ (Γ : HRA) := {
  #[local] spinlock_inG :: inG (exclR unitO) Γ;
}.
Definition SpinLockΓ : HRA := #[exclR unitO].
(* Be sure to annotate Γ as HRA, or tc search may not work properly. *)
Global Instance subG_GΓ {Γ : HRA} : subG SpinLockΓ Γ → SpinLockAGΓ Γ.
Proof. solve_inG. Defined.
(* Be sure to add these two instances to hint database so that we can resolve inG instances
  in the cancellation phase. *)
Hint Unfold subG_GΓ spinlock_inG : GRA_index.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module SpinLockAS. Section SpinLockAS.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ, !SpinLockAGΓ Γ}.

  (* Initial resource *)
  Definition ir : SpinLockΓ := *[None].

  Definition N_SpinLockA := nroot .@ "spin_lock".

  Definition token n γ : GTerm.t n := <own> γ (Excl ()).

  Definition lock_inv {n} blk ofs (P : GTerm.t n) γ : GTerm.t n :=
    (blk, ofs) ↦ (Vint 1)
    ∨ (blk, ofs) ↦ (Vint 0) ∗ P ∗ token n γ.

  Definition is_lock {n} u γ val P : iProp Σ :=
    ∃ blk ofs, ⌜val = Vptr blk ofs⌝ ∗ inv u n N_SpinLockA (lock_inv blk ofs P γ).

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
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !memGΓ Γ, !SpinLockAGΓ Γ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ}.

  Definition scopes : list string := [].

  Definition newlock : list val → itree hmodE val := λ _, 𝒴;;; trigger (Choose val).
  Definition acquire : list val → itree hmodE val :=
    λ _,
      (ITree.iter (λ _,
        𝒴;;; 'x : bool <- trigger (Choose bool);;
        Ret (if x then inr tt else inl tt)) tt
      );;;
      Ret Vundef.
  Definition release : list val → itree hmodE val := λ _, 𝒴;;; Ret Vundef.

  Definition fnsems u :=
    [(SpinLockHdr.newlock, (scopes, mk_specbody (SpinLockAS.newlock_spec u) (cfunU newlock)));
     (SpinLockHdr.acquire, (scopes, mk_specbody (SpinLockAS.acquire_spec u) (cfunU acquire)));
     (SpinLockHdr.release, (scopes, mk_specbody (SpinLockAS.release_spec u) (cfunU release)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems u;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t u sp : HMod.t := Seal.sealing CRIS SMod.to_hmod sp (Mod u).
End SpinLockA. End SpinLockA.
