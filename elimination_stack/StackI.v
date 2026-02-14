Require Import CRIS.
Require Import MemHeader SchHeader HelpingHeader.
Require Export StackHeader.

Module StackI. Section StackI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition new_stack : list val → itree crisE val := λ _,
    𝒴;;; 'stack : val <- ccallU MemHdr.alloc [Vint 2];;
    𝒴;;; '(b, ofs) : _ <- (pargs [Tptr] [stack])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (b, 0%Z); Vint 0];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (b, 1%Z); Vint 0];;
    𝒴;;; Ret stack.

  Definition _push : list val → itree crisE (() + val) := λ args,
    𝒴;;; '((stackb, stackofs), v) : (mblock * ptrofs) * val <- (pargs [Tptr; Tuntyped] args)?;;
    𝒴;;; 'head_old : val <- ccallU MemHdr.load [Vptr (stackb, stackofs)];;
    𝒴;;; 'head_new : val <- ccallU MemHdr.alloc [Vint 2];;
    𝒴;;; '(head_newb, head_newofs) : mblock * ptrofs <- (pargs [Tptr] [head_new])?;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (head_newb, head_newofs); v];;
    𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (head_newb, head_newofs + 1)%Z; head_old];;
    𝒴;;; 'ret : val <-
      ccallU MemHdr.cas [Vptr (stackb, stackofs); head_old; Vptr (head_newb, head_newofs)];;
    𝒴;;; 'cmp : val <- ccallU MemHdr.cmp [ret; head_old];;
    𝒴;;;
      match cmp with
      | Vint 0 =>
          𝒴;;; 'offer : val <- ccallU MemHdr.alloc [Vint 2];;
          𝒴;;; '(offerb, offerofs) : mblock * ptrofs <- (pargs [Tptr] [offer])?;;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (offerb, offerofs); v];;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (offerb, offerofs + 1)%Z; Vint 0];;
          𝒴;;; '_ : val <-
            ccallU MemHdr.store [Vptr (stackb, stackofs + 1)%Z; Vptr (offerb, offerofs)];;
          𝒴;;; '_ : val <- ccallU MemHdr.store [Vptr (stackb, stackofs + 1)%Z; Vint 0];;
          𝒴;;; 'ret : val <- ccallU MemHdr.cas [Vptr (offerb, offerofs + 1)%Z; Vint 0; Vint 2];;
          𝒴;;; 'cmpret : val <- ccallU MemHdr.cmp [Vint 0; ret];;
          match cmpret with
          | Vint 0%Z => Ret (inr Vundef)
          | Vint 1%Z => Ret (inl ())
          | _ => triggerUB
          end
      | Vint 1 => Ret (inr Vundef)
      | _ => triggerUB
      end.

  Definition _pop : list val → itree crisE (() + val) := λ args,
    𝒴;;; '(stackb, stackofs) : (mblock * ptrofs) <- (pargs [Tptr] args)?;;
    𝒴;;; 'head_old : val <- ccallU MemHdr.load [Vptr (stackb, stackofs)];;
    𝒴;;;
      match head_old with
      | Vint 0%Z => Ret (inr Vundef)
      | Vptr (head_oldb, head_oldofs) =>
          𝒴;;; 'head_old_data : val <- ccallU MemHdr.load [Vptr (head_oldb, head_oldofs + 1)%Z];;
          𝒴;;; 'ret : val <-
            ccallU MemHdr.cas [Vptr (stackb, stackofs); head_old; head_old_data];;
          𝒴;;; 'cmp : val <- ccallU MemHdr.cmp [ret; head_old];;
          match cmp with
          | Vint 0 => (* Failed to pop *)
              (* See if there is an offer *)
              𝒴;;; 'offer : val <- ccallU MemHdr.load [Vptr (stackb, stackofs + 1)%Z];;
              match offer with
              | Vint 0 => Ret (inl ()) (* No offer, try again *)
              | Vptr (offerb, offerofs) =>
                  𝒴;;; 'ret : val <-
                    ccallU MemHdr.cas [Vptr (offerb, offerofs + 1)%Z; Vint 0; Vint 1];;
                  𝒴;;; 'cmp : val <- ccallU MemHdr.cmp [ret; Vint 0];;
                  𝒴;;;
                    match cmp with
                    | Vint 0 => Ret (inl ()) (* Failed to pop, try again *)
                    | Vint 1 =>
                        (* Success pop *)
                        𝒴;;; 'ret : val <- ccallU MemHdr.load [Vptr (offerb, offerofs)];;
                        𝒴;;; Ret (inr ret)
                    | _ => triggerUB
                    end
              | _ => triggerUB
              end
          | Vint 1 => (* Success pop *)
              𝒴;;; 'ret : val <- ccallU MemHdr.load [Vptr (head_oldb, head_oldofs)];;
              𝒴;;; Ret (inr ret)
          | _ => triggerUB
          end
      | _ => triggerUB
      end.

  Definition push : list val → itree crisE val := λ args, ITree.iter (λ _, (_push args)) ().
  Definition pop : list val → itree crisE val := λ args, ITree.iter (λ _, (_pop args)) ().

  Definition fnsems : fnsemmap :=
    {[Some StackHdr.new_stack := Some (msk_real (msk_scp scopes msk_true), (None, cfunU new_stack));
      Some StackHdr.push      := Some (msk_real (msk_scp scopes msk_true), (None, cfunU push));
      Some StackHdr.pop       := Some (msk_real (msk_scp scopes msk_true), (None, cfunU pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End StackI. End StackI.