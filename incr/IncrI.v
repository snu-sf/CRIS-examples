Require Import CRIS.
Require Import IncrHeader MemHeader SchHeader ProphecyHeader.

Module IncrI. Section IncrI.

  Context `{Σ : GRA}.

  Definition scopes : list string := ["Incr"].
  Definition v_cnt := "Incr" ↯ "cnt".
  Definition id_incr (n : nat) : Prophecy.ID := ("Incr", n↑↑).

  Definition incr : list val → itree crisE val :=
    λ arg,
      'c : nat <- cgetU v_cnt;;
      cput v_cnt (1 + c);;;
      ccallU (Y:=unit) ProphecyName.new (id_incr c);;;
      𝒴;;;
        ITree.iter (λ t,
          𝒴;;;
            v_raw <- ccallU MemHdr.load arg;;
            v <- (pargs [Tint] v_raw)?;;
          𝒴;;;
            s_raw <- ccallU MemHdr.cas (arg ++ [Vint v; Vint (v + 1)]);;
            s <- (pargs [Tint] s_raw)?;;
            ccallU (Y:=unit) ProphecyName.resolve (id_incr c, s↑↑);;;
          𝒴;;;
            if (decide (s = v)) then Ret (inr tt) else Ret (inl tt)
        ) ();;;
        ccallU (Y:=unit) ProphecyName.close (id_incr c);;;
      𝒴;;; Ret Vundef.

  Definition fnsems : fnsems_type :=
    [(Some IncrHdr.incr, (false, wmask_all, scopes, (None, cfunU incr)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_cnt, 0↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).

End IncrI. End IncrI.
