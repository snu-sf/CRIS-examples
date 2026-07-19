Require Import CRIS.common.CRIS.
Require Import LockHeader LockA.
Require Import ImpPrelude.
From CRIS.scheduler Require Import SchHeader SchA.
Require Import MemHeader MemA.
From iris Require Import frac_auth numbers.

(** Specification Module of SpinLockMainI *)

(* Resource algebra - same as Counter.v example from iris *)
Section RA.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Class spinlockmainG `{!crisG Γ Σ α β τ _S _I} := {
    spinlockmain_inG :: inG (frac_authR ZR) Γ;
  }.
  Definition spinlockmainΓ : HRA := #[frac_authR ZR].
  Global Instance subG_spinlockmainG : subG spinlockmainΓ Γ → spinlockmainG.
  Proof. solve_inG. Defined.
End RA.

(* Spec definition *)
(* Define 1) initial resource 2) function specs 3) sp here. *)
Module MainA. Section MainA.
  Import LockA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !schGS, !spinlockG, !spinlockmainG}.

  Definition lock_P loc γ : GTerm.t 0 :=
    ∃ v : τ{Z}%SAT, loc ↦ (Vint v) ∗ sown γ (●F v).

  Definition incr_spec E : fspec :=
    (fspec_sch E
      (fspec_simple (λ '(bofs_l, bofs_v, γ_v),
        ((λ arg,
          ⌜arg = ([Vptr bofs_l; Vptr bofs_v]↑↑)↑⌝ ∗
          (∃ γ_l, is_lock γ_l (Vptr bofs_l) (lock_P bofs_v γ_v) ∗
          own γ_v (◯F{1/2} 0%Z))),
        (λ ret,
          ⌜ret = ((Vundef)↑↑)↑⌝
          ∗ own γ_v (◯F{1/2} 1%Z)))
      )))%I.

  (* pre/postconditions for threads to be spawned *)
  Definition incr_pre bofs_l bofs_v γ_v : SAny.t → SAny.t → iProp Σ :=
    λ varg arg,
      (⌜varg = arg⌝
      ∗ (⌜varg = [Vptr bofs_l; Vptr bofs_v]↑↑⌝
      ∗ ∃ γ_l, is_lock γ_l (Vptr bofs_l) (lock_P bofs_v γ_v)
          ∗ own γ_v (◯F{1/2} 0%Z)))%I.

  Definition incr_post γ_v : SAny.t → SAny.t → leibnizO {n & GTerm.t n} :=
    (λ _ _, existT 0 (sown γ_v (◯F{1/2} 1%Z)))%SAT.

  Lemma incr_spawnable E bofs_l bofs_v γ_v :
    ⊢ SchA.fspec_spawnable (incr_spec E) (incr_pre bofs_l bofs_v γ_v) (incr_post γ_v).
  Proof.
    iApply SchA.fspec_sch_spawnable; first done.
    iIntros "%P1 %Q1 [% [-> ->]] %varg %arg [%va [%sarg [[-> ->] [-> [-> ?]]]]] !>"; des; clarify.
    iExists _, _; iSplit; first (iPureIntro).
    { exists (bofs_l, bofs_v, γ_v); split; ss. }
    iSplitL; first iFrame; eauto.
    iIntros "%% [-> [-> ?]] !>"; iExists _, _; iSplit; eauto.
    solve_base_sl_red; iSplit; done.
  Qed.

  Definition main_spec (N : namespace) : fspec := fspec_sch (↑N) fspec_trivial.

  Definition sp E : specmap := {[fid SpinLockMainHdr.incr @ (incr_spec E)]}.

  (* Module definition *)
  (* Define three components for a module:
    1) scope
    2) code (via itree)
    3) initial state (via Any.t)
  *)
  Definition scopes : list string := [].

  Definition main : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;; '(l, v) : val * val <- trigger (Choose (val * val));;
      𝒴;;; 't1 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; 't2 : nat <- Sch.spawn ("incr", [l; v]↑↑);;
      𝒴;;; '_ : SAny.t <- Sch.join t1;;
      𝒴;;; '_ : SAny.t <- Sch.join t2;;
      𝒴;;; '_ : unit <- trigger (IO "printf" 2%Z);;
      𝒴;;; Ret tt↑.

  Definition incr : list val → itree crisE val :=
    λ _, 𝒴;;; Ret Vundef.

  Definition fnsems (N : namespace) : fnsemmap :=
    {[entry # (msk_scp scopes msk_true, (fsp_some (main_spec N), main));
      fid SpinLockMainHdr.incr # (msk_scp scopes msk_true, (fsp_some (incr_spec (↑N)), cfunN (fntyp _ _) (sfunN SpinLockMainHdr.incr incr)))]}.

  Program Definition smod N : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems N;
    SMod.initial_st := ∅
  |}.
  Solve All Obligations with mod_tac.

  Definition t N sp : Mod.t := SMod.to_mod sp (smod N).
End MainA. End MainA.
