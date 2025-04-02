Require Import CRIS.
Require Import ImpPrelude.
Require Import SchHeader SchA SchTactics.
Require Import MemHeader MemA.
Require Import IncrementHeader.

Module IncrementA. Section IncrementA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!SchAGΣ Σ, !SchAGΓ Γ, !memGΓ Γ}.

  Definition increment_spec u : fspec :=
    sch_fspec u
      (fspec_simple (λ '(blk, ofs),
        ((λ varg, ⌜varg = [Vptr blk ofs]↑⌝),
        (λ vret, True))
      ))%I.

  Definition sp u : alist string fspec :=
    [(IncrementHdr.increment, increment_spec u)].

  Definition scopes : list string := [].

  (* Definition increment1 : list val → itree hmodE val :=
    λ arg,
      '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)!;;
      𝒴;;;
        ITree.iter (λ _ : unit,
          𝒴;;;
          v <- trigger (Take Z);;
          trigger (Assume ((blk, ofs) ↦ Vint v));;;
          trigger (Guarantee ((blk, ofs) ↦ Vint v));;;
          𝒴;;;
          v2 <- trigger (Take Z);;
          trigger (Assume ((blk, ofs) ↦ Vint v2));;;
          if (decide (v = v2))
          then trigger (Guarantee ((blk, ofs) ↦ Vint (1 + v2)));;; 𝒴;;; Ret (inr (Vint v2))
          else trigger (Guarantee ((blk, ofs) ↦ Vint v2));;; 𝒴;;; Ret (inl tt)
        ) (). *)

  Definition increment2 : list val → itree hmodE val :=
    λ arg,
      '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] arg)!;;
      𝒴;;;
        ITree.iter (λ _ : unit,
          𝒴;;;
          v <- trigger (Take Z);;
          trigger (Assume ((blk, ofs) ↦ Vint v));;;
          'b : bool <- trigger (Choose bool);;
          if b
          then trigger (Guarantee ((blk, ofs) ↦ Vint (v + 1)));;; 𝒴;;; Ret (inr (Vint v))
          else trigger (Guarantee ((blk, ofs) ↦ Vint v));;; 𝒴;;; Ret (inl tt)
        ) ().

  Definition increment : list val → itree hmodE val :=
    λ arg, increment2 arg.
      (* 'b : bool <- trigger (Take bool);; *)
      (* if b then (increment1 arg) else (increment2 arg). *)

  Definition fnsems u :=
    [(IncrementHdr.increment, (scopes, mk_specbody (increment_spec u) (cfunN increment)))].

  Program Definition Mod u : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems u;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t u sp : HMod.t := Seal.sealing CRIS (SMod.to_hmod sp (Mod u)).
End IncrementA. End IncrementA.