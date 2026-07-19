Require Import CRIS.common.CRIS ImpPrelude.
Require Import MemHeader CRIS.scheduler.SchHeader PQueueHeader IOHeader.

Module IOI. Section IOI.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Definition init : list val → itree crisE val := λ arg,
    𝒴;;; qptr <- ccallU PQueueHdr.new arg;;
    𝒴;;; Sch.spawn (fn_name IOHdr.proxy, [qptr]↑↑);;;
    Ret qptr.

  Definition request : list val → itree crisE val := λ arg,
    𝒴;;; '(qptr, (cptr, (num, prt))) : _ <- (pargs [Tptr; Tptr; Tint; Tint] arg)?;;
    𝒴;;; 'ptr : val <- ccallU MemHdr.alloc [Vint 3];;
    𝒴;;; '(hblk, hofs) : _ * _ <- (pargs [Tptr] [ptr])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (hblk, hofs); Vint 0];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (hblk, hofs + 1)%Z; Vptr cptr];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (hblk, hofs + 2)%Z; Vint num];;
    𝒴;;; '_ : val <- ccallU PQueueHdr.add [Vptr qptr; Vint prt; Vptr (hblk, hofs)];;
    𝒴;;;
      ITree.iter (λ _ : (),
        𝒴;;; 'ret : val <- ccallU MemHdr.load [Vptr (hblk, hofs)];;
        𝒴;;; 'cmp : val <- ccallU MemHdr.cmp [ret; Vint 1];;
        𝒴;;; 'cmp : Z <- (pargs [Tint] [cmp])?;;
        𝒴;;;
          if decide (cmp = 0%Z)
          then Ret (inl tt)
          else Ret (inr Vundef)
      ) tt.

  Definition fnsems : fnsemmap :=
    {[ fid IOHdr.init    # (msk_real (msk_scp [] msk_true), (None, cfunU imp_fun_t init));
       fid IOHdr.request # (msk_real (msk_scp [] msk_true), (None, cfunU imp_fun_t request)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.initial_st := ∅;
    SMod.fnsems := fnsems;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IOI. End IOI.

Module ProxyI. Section ProxyI.
  Context `{!crisG Γ Σ α β τ Hinv Hsub}.

  Definition proxy : list val → itree crisE val := λ arg,
    𝒴;;; 'qptr : _ <- (pargs [Tptr] arg)?;;
    𝒴;;; ITree.iter (λ _ : (),
      𝒴;;; v <- ccallU PQueueHdr.remove_min [Vptr qptr];;
      𝒴;;;
        match v with
        | Vptr (blk, ofs) =>
          𝒴;;; cptr <- ccallU MemHdr.load [Vptr (blk, ofs + 1)%Z];;
          𝒴;;; '(cblk, cofs) : mblock * ptrofs <- (pargs [Tptr] [cptr])?;;
          𝒴;;; n <- ccallU MemHdr.load [Vptr (blk, ofs + 2)%Z];;
          𝒴;;; 'n : Z <- (pargs [Tint] [n])?;;
          𝒴;;;
            ITree.iter (λ i : nat,
              𝒴;;;
                if decide (i = Z.to_nat n)
                then Ret (inr tt)
                else
                  𝒴;;; v <- ccallU MemHdr.load [Vptr (cblk, cofs + i)%Z];;
                  𝒴;;; trigger (IO (I:=val) "network.send" (i, v));;;
                  𝒴;;; Ret (inl (S i))
            ) 0;;;
          𝒴;;; ccallU MemHdr.store [Vptr (blk, ofs); Vint 1];;;
          Ret (inl tt)
        | _ => Ret (inl tt)
        end
    ) tt.

  Definition fnsems : fnsemmap :=
    {[ fid IOHdr.proxy # (msk_real (msk_scp [] msk_true), (None, cfunU (fntyp _ _) (sfunU imp_fun_t proxy))) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.initial_st := ∅;
    SMod.fnsems := fnsems;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End ProxyI. End ProxyI.
