Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module KnotMainA. Section KnotMainA.
  Import KnotA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
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
  Variable SpRec: string -> option fspec.
  Variable SpPure: string -> option fspec.
  Variable Sp: string -> option fspec.

  Definition fib_spec : fspec :=
    fspec_apc (λ '(n, INV), (2 * (n: nat))%ord)
      (fun '(n, INV) => 
        ((fun varg => (⌜∃ fb, varg = [Vptr (fb, 0%Z); Vint (Z.of_nat n)]↑ ∧ (intrange_64 n) ∧
                          fb_has_spec genv SpRec fb (mrec_spec Fib INV)⌝ ∗ INV)%I),
         (fun vret => (⌜vret = (Vint (Z.of_nat (Fib n)))↑⌝ ∗ INV)%I))).

  Definition MainFunSp : alist string fspec := 
    Seal.sealing CRIS
      [(KnotMainHdr.fib, fib_spec)].

  Definition main_body: Any.t → itree hmodE Any.t :=
    λ _, pure;;; trigger (Choose _).

  Definition main_spec: fspec :=
    fspec_simple
      (fun '() =>
        ((fun varg => (⌜varg = tt↑⌝ ∗ knot_init)%I),
         (fun vret => (⌜vret = (Vint (Z.of_nat (Fib 10)))↑⌝)%I))).

  Definition MainSp : alist string fspec :=
    Seal.sealing CRIS
      [("fib", fib_spec); ("main", main_spec)].
End KnotMainAS.

Section KnotMainA.
  Definition scopes := ["KnotMain"].

  Definition fnsems genv SpRec :=
    [(KnotMainHdr.fib, (wmask_all, scopes, mk_specbody (fib_spec genv SpRec) pure_body));
     (KnotMainHdr.main, (wmask_all, scopes, mk_specbody main_spec main_body))].

  Program Definition Mod genv SpRec : SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv SpRec;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t genv SpRec Sp := Seal.sealing CRIS (SMod.to_hmod Sp (Mod genv SpRec)).
End KnotMainA.
End KnotMainA. End KnotMainA.
