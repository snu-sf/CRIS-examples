Require Import CRIS.common.CRIS.
Require Import CRIS.scheduler.SchHeader.
From CRIS.imp_system Require Import mem.MemHeader.
From CRIS.elimination_stack Require Import StackHeader.
From CRIS.priority_queue Require Import PQueueHeader.

Module PQueueI. Section PQueueI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition new : list val → itree crisE val := λ args,
    𝒴;;; n <- (pargs [Tint] args)?;;
    𝒴;;; queue <- ccallU MemHdr.alloc [Vint (n + 1)%Z];;
    𝒴;;; '(b, ofs) : _ <- (pargs [Tptr] [queue])?;;
    𝒴;;; ccallU MemHdr.store [Vptr (b, ofs); Vint n];;;
    let n := Z.to_nat n in
    ITree.iter (λ '(n, ofs),
      match n with
      | 0 => 𝒴;;; Ret (inr ())
      | S n' =>
          𝒴;;; bin <- ccallU StackHdr.new_stack (@nil val);;
          𝒴;;; ccallU MemHdr.store [Vptr (b, ofs); bin];;;
          𝒴;;; Ret (inl (n', (ofs + 1)%Z))
      end
    ) (n, ofs + 1)%Z;;;
    𝒴;;; Ret queue.

  Definition add : list val → itree crisE val := λ args,
    𝒴;;; '(queueb, queueofs, (p, v)) : _ <- (pargs [Tptr; Tint; Tuntyped] args)?;;
    𝒴;;; bin <- ccallU MemHdr.load [Vptr (queueb, queueofs + p + 1)%Z];;
    𝒴;;; ccallU StackHdr.push [bin; v];;;
    𝒴;;; Ret Vundef.

  Definition remove_min : list val → itree crisE val := λ args,
    𝒴;;; q <- (pargs [Tuntyped] args)?;;
    𝒴;;; n <- ccallU MemHdr.load [q];;
    𝒴;;; '(b, ofs, n) : mblock * ptrofs * Z <- (pargs [Tptr; Tint] [q; n])?;;
    let n := Z.to_nat n in 
    ITree.iter (λ '(n, ofs),
      match n with
      | 0 => 𝒴;;; Ret (inr Vundef)
      | S n' =>
          𝒴;;; s <- ccallU MemHdr.load [Vptr (b, ofs)];;
          𝒴;;; v <- ccallU StackHdr.pop [s];;
          match v with
          | Vundef => 𝒴;;; Ret (inl (n', ofs + 1)%Z)
          | _ => 𝒴;;; Ret (inr v)
          end
      end
    ) (n, ofs + 1)%Z.

  Definition fnsems : fnsemmap :=
    {[fid PQueueHdr.new        # (msk_real (msk_scp scopes msk_true), (None, cfunU imp_fun_t new));
      fid PQueueHdr.add        # (msk_real (msk_scp scopes msk_true), (None, cfunU imp_fun_t add));
      fid PQueueHdr.remove_min # (msk_real (msk_scp scopes msk_true), (None, cfunU imp_fun_t remove_min))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End PQueueI. End PQueueI.
