Require Import CRIS.
Require Import APCHeader APC APCA.
Require Export KnotHeader KnotMainHeader KnotA.

Module KnotMainA. Section KnotMainA.
  Import KnotA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _MEM: !memGS, _KNOT: !knotGS}.

  (* Specifications *)
  Fixpoint Fib (n : nat) : nat :=
    match n with
    | 0 => 1
    | S n' =>
      let r := Fib n' in
      match n' with
      | 0 => 1
      | S n'' => r + Fib n''
      end
    end.

  Lemma unfold_fib n (COND: n > 1) : Fib n = Fib (n - 1) + Fib (n - 2).
  Proof.
    destruct n; try nia. destruct n; try nia.
    unfold Fib at 1. des_ifs.
  Qed.

  Context (genv : GEnv.t) (sp_rec : specmap).

  Definition fib_spec : fspec :=
    fspec_apc (λ '(n, _), (2 * (n : nat))%ord)
      (λ '(n, INV),
        ((λ varg, (⌜∃ fb, varg = [Vptr (fb, 0%Z); Vint (Z.of_nat n)]↑ ∧ (intrange_64 n) ∧
                          fb_has_spec_in genv sp_rec fb (mrec_spec Fib INV)⌝ ∗ INV)%I),
         (λ vret, (⌜vret = (Vint (Z.of_nat (Fib n)))↑⌝ ∗ INV)%I))).

  Definition main_spec : fspec :=
    fspec_simple (λ _ : unit,
      ((λ varg, ⌜varg = tt↑⌝ ∗ knot_frag None),
       (λ vret, emp)))%I.

  Definition main_fun_sp : specmap :=  {[speckey_fn KnotMainHdr.fib := fspec_to_rel fib_spec]}.
  Definition main_sp : specmap := {[speckey_fn "fib" := fspec_to_rel fib_spec]}.

  Definition scopes := ["KnotMain"].

  Context (with_pure : bool).

  Definition main_body: () → itree crisE val :=
    λ _, (if with_pure then pure else Ret ()↑);;; Ret (Vint (Z.of_nat (Fib 10))).

  Definition fnsems : fnsemmap :=
    {[Some KnotMainHdr.fib := Some (msk_scp scopes msk_true, (fsp_some fib_spec, pure_body));
      None := Some (msk_scp scopes msk_true, (fsp_some main_spec, cfunU main_body))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := knot_frag None.

  Definition t sp := SMod.to_mod sp (smod).
End KnotMainA. End KnotMainA.
