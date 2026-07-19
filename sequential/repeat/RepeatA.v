From CRIS.common Require Import CRIS.
From CRIS.imp_system.imp Require Import Imp.
From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.repeat Require Import RepeatHeader.
From CRIS.apc Require Import APCHeader APC.

Set Implicit Arguments.

(* Define Specification *)
Module RepeatAS. Section RepeatAS.
  Context `{!crisG Σ Γ α β τ Hinv Hsub}.

  Context (genv : GEnv.t).
  Context (sp_pure : specmap).

  (* mathematical repeat *)
  Fixpoint repeat_fun A (f: A → A) (n: nat) (a: A): A :=
    match n with
    | 0 => a
    | S n' => repeat_fun f n' (f a)
    end.

  Definition repeat_spec (genv: GEnv.t) : fspec :=
    fspec_apc (λ '(n, x, f_sem), OrdArith.add Ord.omega (n:nat)%ord)
      (λ '(n, x, f_sem),
        ((λ arg, ⌜∃ (fn:string) (fptr:mblock), arg = [Vptr (fptr, 0%Z); Vint (Z.of_nat n); Vint x]↑
                        ∧ (intrange_64 (Z.of_nat n))
                        ∧ CEnv.blk2id (CEnv.load_genv genv) fptr = Some fn
                        ∧ fn_has_spec_in sp_pure fn
                            (fspec_apc
                              (λ _, Ord.omega)
                              (λ x, 
                                ((λ varg, ⌜varg = [Vint x]↑⌝%I),
                                (λ vret, ⌜vret = (Vint (f_sem x))↑⌝%I))
                              )
                            )
                      ⌝%I),
          (λ ret, ⌜ret = (Vint (repeat_fun f_sem n x))↑⌝%I))).

  Definition Sp: specmap :=
    {[fid RepeatHdr.repeat @ repeat_spec genv]}.

End RepeatAS. End RepeatAS.

(* Define Module *)
Module RepeatA. Section RepeatA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Definition scopes := [RepeatHdr.mn].

  Definition fnsems (genv : GEnv.t) (sp_pure: specmap) : fnsemmap :=
    {[fid RepeatHdr.repeat # (msk_scp scopes msk_true, (fsp_some (RepeatAS.repeat_spec sp_pure genv), pure_body))]}.

  Program Definition smod genv sp_pure : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv sp_pure;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := emp%I.

  Definition t genv sp sp_pure := SMod.to_mod sp (smod genv sp_pure).
End RepeatA. End RepeatA.
