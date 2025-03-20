Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotA.
Require Import APCHeader APC APCA.

Set Implicit Arguments.

Module KnotMainA. Section KnotMainA.
  Import KnotA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !KnotAGΓ Γ, !memGΓ Γ}.
  Notation iProp := (iProp Σ).
  Local Existing Instance RA_inG.

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
  Variable SpcRec: string -> option fspec.
  Variable SpcPure: string -> option fspec.
  Variable Spc: string -> option fspec.

  Definition fib_spec : fspec :=
    fspec_apc (λ '(n, INV), (2 * (n: nat))%ord)
      (fun '(n, INV) => 
        ((fun varg => (⌜∃ fb, varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ ∧ (intrange_64 n) ∧
                          fb_has_spec genv SpcRec fb (mrec_spec Fib INV)⌝ ∗ INV)%I),
         (fun vret => (⌜vret = (Vint (Z.of_nat (Fib n)))↑⌝ ∗ INV)%I))).

  Definition MainFunSpc : alist string fspec := 
    Seal.sealing CRIS
      [(KnotMainHdr.fib, fib_spec)].

  Definition main_body: Any.t → itree hmodE Any.t :=
    λ _, pure;;; trigger (Choose _).

  Definition main_spec: fspec :=
    fspec_simple
      (fun '() =>
        ((fun varg => (⌜varg = tt↑⌝ ∗ knot_init)%I),
         (fun vret => (⌜vret = (Vint (Z.of_nat (Fib 10)))↑⌝)%I))).

  Definition MainSpc : alist string fspec :=
    Seal.sealing CRIS
      [("fib", fib_spec); ("main", main_spec)].
End KnotMainAS.

Section KnotMainA.
  Definition scopes := ["KnotMain"].

  Definition fnsems genv SpcRec :=
    [(KnotMainHdr.fib, (scopes, mk_specbody (fib_spec genv SpcRec) pure_body));
     (KnotMainHdr.main, (scopes, mk_specbody main_spec main_body))].

  Program Definition Mod genv SpcRec : SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems genv SpcRec;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp := emp%I.

  Definition t genv u SpcRec Spc := Seal.sealing CRIS (SMod.to_hmod (wsim_ginv u ⊤) Spc (Mod genv SpcRec)).
End KnotMainA.
End KnotMainA. End KnotMainA.
