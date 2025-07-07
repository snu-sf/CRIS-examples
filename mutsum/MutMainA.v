Require Import CRIS.
Require Import MutHeader APCHeader APC.

Set Implicit Arguments.

Module MutMainA. Section MutMainA.
  Context `{!crisG Γ Σ α β τ _I _S}.

  Variable with_pure: bool.
  
  Definition scopes := ["MutMain"].

  Definition main_body : Any.t → itree hmodE Any.t :=
    λ _, (if with_pure then pure else Ret ()↑);;; Ret (Vint 55)↑.

  Definition Sp: spl_type :=
    Seal.sealing CRIS [(None, None)].

  Definition fnsems : alist (option string) (fnsem_type (option fspec * fbody)) :=
    [(None, (true, wmask_all, scopes, (None, main_body)))].

  Program Definition Mod: SMod.t :=
  {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := Seal.sealing CRIS (SMod.to_hmod Sp Mod).
End MutMainA. End MutMainA.
