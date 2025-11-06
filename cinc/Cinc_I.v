Require Import CRIS.
Require Import MemHeader SchHeader.
Require Import Cinc_H.

Set Implicit Arguments.

Module Cinc_I. Section Cinc_I.
  Context `{Σ: GRA}.

  Definition scopes := [Cinc_H.scope].

  Definition alloc_pair tag n : itree crisE (nat*Z) :=
    'dp: val <- ccallU MemHdr.alloc [Vint 2];; dp <- (unptr dp)?;;
    𝒴;;; '_: val <- ccallU MemHdr.store [Vptr dp; tag];;
    𝒴;;; p <- (vadd (Vptr dp) (Vint 8))?;; '_: val <- ccallU MemHdr.store [p; Vint n];;
    Ret dp.

  Definition read_pair (dp: nat*Z) : itree crisE (val * Z) :=
    'tag: val <- ccallU MemHdr.load [Vptr dp];;
    𝒴;;; p <- (vadd (Vptr dp) (Vint 8))?;; '_n: val <- ccallU MemHdr.load [p];;
    n <- (unint _n)?;;
    Ret (tag, n).

  Definition free_pair (dp: nat*Z) : itree crisE val :=
    ccallU MemHdr.free [Vptr dp].

  Definition new: list val → itree crisE val :=
    λ _,
    𝒴;;; 'cp: val <- ccallU MemHdr.alloc [Vint 1];;
    𝒴;;;  dp <- alloc_pair (Vint 0) 0;;
    𝒴;;; '_ : val <- ccallU MemHdr.store [cp; Vptr dp];;
    𝒴;;; Ret cp.

  Definition complete (cp dp fp: nat * Z) (n: Z) : itree crisE val :=
    'f: val <- ccallU MemHdr.load [Vptr fp];;
    let n' := (match f with Vint k => (k+n)%Z | _ => n end) in
    𝒴;;; dp' <- alloc_pair (Vint 0) n';;
    𝒴;;; 'res: val <- ccallU MemHdr.cas [Vptr cp; Vptr dp; Vptr dp'];;
    𝒴;;; if val_dec res (Vptr dp) then Ret (Vint 0) (* free_pair dp *) else free_pair dp'.

  Definition prepare cp : itree crisE _ :=
    'dp: val <- ccallU MemHdr.load [Vptr cp];; dp <- (unptr dp)?;;
    𝒴;;; '(tag, n): _ <- read_pair dp;;
    match tag with
    | Vptr fp => 𝒴;;; complete cp dp fp n;;; Ret None
    | _ => Ret (Some (dp, n))
    end.

  Definition get (varg: list val) : itree crisE val :=
    '(cp, fp):_ <- (pargs [Tptr; Tptr] varg)?;;
    𝒴;;; ITree.iter (λ _,
      res <- prepare cp;;
      match res with
      | None => 𝒴;;; Ret (inl ())
      | Some (_, n) => 𝒴;;; Ret (inr (Vint n))
      end
    ) ().
        
  Definition inc (varg: list val) : itree crisE val :=
    '(cp, fp):_ <- (pargs [Tptr; Tptr] varg)?;;
    𝒴;;; ITree.iter (λ _,
      res <- prepare cp;;
      match res with
      | None => 𝒴;;; Ret (inl ())
      | Some (dp, n) =>
        𝒴;;; dp' <- alloc_pair (Vptr fp) n;;
        𝒴;;; 'res: val <- ccallU MemHdr.cas [Vptr cp; Vptr dp; Vptr dp'];;
        if val_dec res (Vptr dp)
        then (* 𝒴;;; free_pair dp;;; *)
             𝒴;;; complete cp dp' fp n;;; 𝒴;;; Ret (inr Vundef)
        else 𝒴;;; free_pair dp';;; 𝒴;;; Ret (inl ())          
      end
    ) ().
  
  Definition fnsems : fnsems_type :=
    [(Some Cinc_H.new, (false, wmask_all, scopes, (None, cfunU new)));
     (Some Cinc_H.get, (false, wmask_all, scopes, (None, cfunU get)));
     (Some Cinc_H.inc, (false, wmask_all, scopes, (None, cfunU inc)))].
  
  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t := Seal.sealing CRIS (SMod.to_mod sp_none Mod).

End Cinc_I. End Cinc_I.
