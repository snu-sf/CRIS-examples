Require Import CRIS.
From CRIS.spinlock Require Import Header LockA.
Require Import ImpPrelude SchHeader SchA MemHeader MemA.
From iris Require Import frac_auth numbers.

(** Specification Module of SpinLockMainI *)

(* Resource algebra - same as Counter.v example from iris *)
Section RA.
  Context `{!sinvG Γ Σ α β τ _I _S}.

  Class spinlockmainG `{!sinvG Γ Σ α β τ _I _S} := {
    spinlockmain_inG :: inG (frac_authR ZR) Γ;
  }.
  Definition spinlockmainΓ : HRA := #[frac_authR ZR].
  Global Instance subG_spinlockmainG : subG spinlockmainΓ Γ → spinlockmainG.
  Proof. solve_inG. Defined.
End RA.
Hint Unfold subG_spinlockmainG spinlockmain_inG : GRA_index.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module MainAS. Section MainAS.
  Import LockAS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.
  Context `{_spinlockmainG: !spinlockmainG}.

  (* initial resource *)
  Definition ir : spinlockmainΓ := *[None].

  Definition main_spec E : fspec :=
    fspec_sch E
      (fspec_simple (λ _ : unit,
        (λ arg, ⌜arg = tt↑⌝,
        λ ret, ⌜ret = tt↑⌝)))%I.

  Definition lock_P loc γ : GTerm.t 0 :=
    ∃ v : τ{Z}%SAT, loc ↦ (Vint v) ∗ <own> γ (●F v).

  Definition incr_spec E : fspec :=
    fspec_sch E
      (fspec_simple (λ '(bofs_l, bofs_v, γ_v),
        ((λ arg,
          ⌜arg = ([Vptr bofs_l; Vptr bofs_v]↑↑)↑⌝ ∗
          (∃ γ_l, is_lock γ_l (Vptr bofs_l) (lock_P bofs_v γ_v) ∗
          own γ_v (◯F{1/2} 0%Z))),
        (λ ret,
          ⌜ret = ((Vundef)↑↑)↑⌝
          ∗ own γ_v (◯F{1/2} 1%Z)))
      ))%I.

  (* pre/postconditions for threads to be spawned *)
  Definition incr_pre bofs_l bofs_v γ_v : SAny.t → SAny.t → iProp Σ :=
    λ varg arg,
      (⌜varg = arg⌝
      ∗ (⌜varg = [Vptr bofs_l; Vptr bofs_v]↑↑⌝
      ∗ ∃ γ_l, is_lock γ_l (Vptr bofs_l) (lock_P bofs_v γ_v)
          ∗ own γ_v (◯F{1/2} 0%Z)))%I.

  Definition incr_post γ_v : SAny.t → SAny.t → SynDepO :=
    (λ _ _, existT 0 (<own> γ_v (◯F{1/2} 1%Z)))%SAT.

  Lemma incr_spawnable E bofs_l bofs_v γ_v :
    SchAS.fspec_spawnable E (incr_spec E)
      (incr_pre bofs_l bofs_v γ_v) (incr_post γ_v).
  Proof.
    intros x_s; ss.
    exists (x_s, (bofs_l, bofs_v, γ_v)); split.
    { intros varg arg. unfold_pre_post.
      iIntros "[W [%va [-> [TID [%sarg [-> [-> [-> P]]]]]]]]".
      iFrame. iModIntro. iSplit; eauto.
    }
    { iIntros (vret ret); rewrite /postcond /incr_spec /=.
      iIntros "[$ [$ [[-> F] ->]]]".
      iFrame. iModIntro; iExists _; iSplit; eauto. iExists _. iSplit; eauto. SL_red; done.
    }
  Qed.

  Definition sp E : alist string fspec :=
    [(SpinLockMainHdr.main, main_spec E);
     (SpinLockMainHdr.incr, incr_spec E)].
End MainAS. End MainAS.

(* Module definition *)
(* Define three components for a module:
  1) scope
  2) code (via itree)
  3) initial state (via Any.t)
*)
Module SpinLockMainA. Section SpinLockMainA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.
  Context `{_spinlockG: !spinlockG}.
  Context `{_spinlockmainG: !spinlockmainG}.
                        
  Definition scopes : list string := [].

  Definition main : unit → itree hmodE unit :=
    λ _,
      𝒴;;; '(l, v) : val * val <- trigger (Choose (val * val));;
      𝒴;;; 't1 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; 't2 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; '_ : SAny.t <- Sch.join t1;;
      𝒴;;; '_ : SAny.t <- Sch.join t2;;
      (iterC
        (λ _, 𝒴;;; 'x : bool <- trigger (Choose bool);; Ret (if x then inr tt else inl tt)) tt);;;
      𝒴;;; '_ : unit <- trigger (IO "printf" 2%Z);;
      𝒴;;; Ret tt.

  Definition incr : list val → itree hmodE val :=
    λ _,
      (iterC (λ _,
        𝒴;;; 'x : bool <- trigger (Choose bool);;
        Ret (if x then inr tt else inl tt)
      ) tt);;;
      Ret Vundef.

  Definition fnsems u :=
    [(SpinLockMainHdr.main, (wmask_all, scopes, mk_specbody (MainAS.main_spec u) (cfunN main)));
     (SpinLockMainHdr.incr, (wmask_all, scopes, mk_specbody (MainAS.incr_spec u) (cfunN (sfunN incr))))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems u;
    SMod.initial_st := []
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Defined.

  Definition t u sp : HMod.t := Seal.sealing CRIS SMod.to_hmod sp (Mod u).
End SpinLockMainA. End SpinLockMainA.
