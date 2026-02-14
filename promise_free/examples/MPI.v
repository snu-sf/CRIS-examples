Require Import CRIS.
Require Import PFMemHeader PFMemUser SchHeader HistoryRA.
Require Import SystemHeader.

Notation flag := 0 (only parsing).
Notation data := 1 (only parsing).

Module MPHdr.
  Definition mp2 : string := "mp2".
End MPHdr.

(* Message passing - implementation *)
Module MPI. Section MPI.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Definition scopes : list string := [].

  Definition mp : Any.t → itree crisE Any.t :=
    λ _,
      (* alloc *)
      𝒴;;; m <- ccallU SystemHdr.alloc 2;;
      𝒴;;; loc <- parse_loc m;;
      (* store *)
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> flag, Val.Vnum 0, Ordering.na);;
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> data, Val.Vnum 0, Ordering.na);;
      (* spawn *)
      𝒴;;; '_ : () <- ccallU SystemHdr.spawn (MPHdr.mp2, m↑↑);;
      (* loop *)
      iterC (λ _,
        𝒴;;; r <- ccallU SystemHdr.read (loc >> flag, Ordering.acqrel);;
        𝒴;;; n <- parse_num r;;
        𝒴;;;
          if (decide (n = 0))
          then Ret (inl tt)
          else 
            𝒴;;; r <- ccallU SystemHdr.read (loc >> data, Ordering.acqrel);;
            𝒴;;; n <- parse_num r;;
            Ret (inr (Val.Vnum n)↑)
      ) ().

  Definition mp2 : Val.t → itree crisE Val.t :=
    λ m,
      𝒴;;; loc <- parse_loc m;;
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> data, Val.Vnum 42, Ordering.relaxed);;
      𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> flag, Val.Vnum 1, Ordering.acqrel);;
      𝒴;;; Ret Val.zero.

  Definition fnsems : fnsemmap :=
    {[Some MPHdr.mp2 := Some (msk_real (msk_scp scopes msk_true), (None, cfunU (sfunU mp2)));
      None := Some (msk_real (msk_scp scopes msk_true), (None, mp))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End MPI. End MPI.