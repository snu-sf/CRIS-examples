Require Import CRIS.
Require Import SchHeader.
Require Import MemHeader.
Require Import StackHeader.
Require Import PQueueHeader.

Module PQueueI. Section PQueueI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition new : list val → itree crisE val := λ args,
    𝒴;;; 'n : Z <- (pargs [Tint] args)?;;
    𝒴;;; 'queue : val <- ccallU MemHdr.alloc [Vint (n + 1)%Z];;
    𝒴;;; '(b, ofs) : _ <- (pargs [Tptr] [queue])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (b, ofs); Vint n];;
    let n := Z.to_nat n in
    ITree.iter (λ '(n, ofs),
      match n with
      | 0 => 𝒴;;; Ret (inr ())
      | S n' =>
          𝒴;;; 'bin : val <- ccallU StackHdr.new_stack (@nil val);;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (b, ofs); bin];;
          𝒴;;; Ret (inl (n', (ofs + 1)%Z))
      end
    ) (n, ofs + 1)%Z;;;
    𝒴;;; Ret queue.

  Definition add : list val → itree crisE val := λ args,
    𝒴;;; '(queueb, queueofs, (p, v)) : _ <- (pargs [Tptr; Tint; Tuntyped] args)?;;
    𝒴;;; 'bin : val <- ccallU MemHdr.load [Vptr (queueb, queueofs + p + 1)%Z];;
    𝒴;;; '_ : val <- ccallU StackHdr.push [bin; v];;
    𝒴;;; Ret Vundef.

  Definition remove_min : list val → itree crisE val := λ args,
    𝒴;;; 'q : val <- (pargs [Tuntyped] args)?;;
    𝒴;;; 'n : val <- ccallU MemHdr.load [q];;
    𝒴;;; '(b, ofs, n) : mblock * ptrofs * Z <- (pargs [Tptr; Tint] [q; n])?;;
    let n := Z.to_nat n in 
    ITree.iter (λ '(n, ofs),
      match n with
      | 0 => 𝒴;;; Ret (inr Vundef)
      | S n' =>
          𝒴;;; 's : val <- ccallU MemHdr.load [Vptr (b, ofs)];;
          𝒴;;; 'v : val <- ccallU StackHdr.pop [s];;
          match v with
          | Vundef => 𝒴;;; Ret (inl (n', ofs + 1)%Z)
          | _ => 𝒴;;; Ret (inr v)
          end
      end
    ) (n, ofs + 1)%Z.

  Definition fnsems : fnsemmap :=
    {[Some PQueueHdr.new :=        Some (msk_real (msk_scp scopes msk_true), (None, cfunU new));
      Some PQueueHdr.add        := Some (msk_real (msk_scp scopes msk_true), (None, cfunU add));
      Some PQueueHdr.remove_min := Some (msk_real (msk_scp scopes msk_true), (None, cfunU remove_min))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End PQueueI. End PQueueI.