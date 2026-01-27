Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module KnotMainA. Section KnotMainA.
  Import KnotA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  Context `{_knotG: !knotG}.

  (* Specifications *)

  Fixpoint Fib (n: nat): nat :=
    match n with
    | 0 => 1
    | S n' =>
      let r := Fib n' in
      match n' with
      | 0 => 1
      | S n'' => r + Fib n''
      end
    end.

  Lemma unfold_fib n
    (COND: n > 1)
    :
    Fib n = Fib (n - 1) + Fib (n - 2).
  Proof.
    destruct n; try nia. destruct n; try nia.
    unfold Fib at 1. des_ifs.
  Qed.

  (***************)
Section KnotMainAS.

  Variable genv: GEnv.t.
  Variable SpRec: spl_type.
  Variable SpPure: spl_type.
  Variable Sp: spl_type.

  Definition fib_spec : fspec :=
    fspec_apc (λ '(n, INV), (2 * (n: nat))%ord)
      (fun '(n, INV) => 
        ((fun varg => (⌜∃ fb, varg = [Vptr (fb, 0%Z); Vint (Z.of_nat n)]↑ ∧ (intrange_64 n) ∧
                          fb_has_spec_in genv SpRec fb (mrec_spec Fib INV)⌝ ∗ INV)%I),
         (fun vret => (⌜vret = (Vint (Z.of_nat (Fib n)))↑⌝ ∗ INV)%I))).

  Definition MainFunSp : spl_type := 
    Seal.sealing CRIS
      [(Some KnotMainHdr.fib, fsp_some fib_spec)].

  Definition MainSp : spl_type :=
    Seal.sealing CRIS
      [(Some "fib", fsp_some fib_spec); (None, fsp_none)].
End KnotMainAS.

Section KnotMainA.
  Definition scopes := ["KnotMain"].

  Variable with_pure: bool.  
  
  Definition main_body: () → itree crisE val :=
    λ _, (if with_pure then pure else Ret ()↑);;; Ret (Vint (Z.of_nat (Fib 10))).

  Definition fnsems genv SpRec : fnsems_type :=
    [(Some KnotMainHdr.fib, (true, wmask_all, scopes, (fsp_some (fib_spec genv SpRec), pure_body)));
     (None, (true, wmask_all, scopes, (fsp_none, cfunU main_body)))].

  Program Definition smod genv SpRec : SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv SpRec;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := knot_init%I.

  Definition t genv SpRec Sp := Seal.sealing CRIS (SMod.to_mod Sp (smod genv SpRec)).
End KnotMainA.
End KnotMainA. End KnotMainA.
