Require Import CRIS.
Require Import Imp.
Require Import ImpPrelude.
Require Import RepeatHeader.
Require Import APCHeader APC.

Set Implicit Arguments.

(* Define Specification *)
Module RepeatAS. Section RepeatAS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Context (genv : GEnv.t).
  Context (sp_pure : string → option fspec).

  (* mathematical repeat *)
  Fixpoint repeat_fun A (f: A → A) (n: nat) (a: A): A :=
    match n with
    | 0 => a
    | S n' => repeat_fun f n' (f a)
    end.

  Definition repeat_spec (genv: GEnv.t) : fspec :=
    fspec_apc (λ '(n, x, f_sem), OrdArith.add Ord.omega (n:nat)%ord)
      (λ '(n, x, f_sem),
        ((λ arg, ⌜∃ (fn:string) (fptr:mblock), arg = [Vptr fptr 0; Vint (Z.of_nat n); Vint x]↑
                        ∧ (intrange_64 (Z.of_nat n))
                        ∧ CEnv.blk2id (CEnv.load_genv genv) fptr = Some fn
                        ∧ fn_has_spec sp_pure fn
                            (fspec_apc
                              (λ _, Ord.omega)
                              (λ x, 
                                ((λ varg, ⌜varg = [Vint x]↑⌝%I),
                                (λ vret, ⌜vret = (Vint (f_sem x))↑⌝%I))
                              )
                            )
                      ⌝%I),
          (λ ret, ⌜ret = (Vint (repeat_fun f_sem n x))↑⌝%I))).

  Definition Sp: alist string fspec :=
    Seal.sealing CRIS [(RepeatHdr.repeat, repeat_spec genv)].

End RepeatAS. End RepeatAS.

(* Define Module *)
Module RepeatA. Section RepeatA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.

  Definition scopes := [RepeatHdr.mn].

  Definition fnsems genv sp_pure :=
    [(RepeatHdr.repeat, (scopes, mk_specbody (RepeatAS.repeat_spec sp_pure genv) pure_body))].

  Program Definition Mod genv sp_pure : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv sp_pure;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t genv sp sp_pure := Seal.sealing CRIS (SMod.to_hmod sp (Mod genv sp_pure)).
End RepeatA. End RepeatA.
