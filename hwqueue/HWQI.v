Require Export CRIS ImpPrelude ProphecyHeader HWQHeader SchHeader MemHeader.
(** * Implementation of the queue operations ********************************)

Module HWQI. Section HWQI.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS}.

  Definition new_queue : list val → itree crisE val := λ sz,
    𝒴;;; sz <- (pargs [Tint] sz)?;;
    𝒴;;; 'q : val <- ccallU (cftyp _ _) MemHdr.alloc [Vint (2 + sz)];;
    𝒴;;; '(qblk, qofs) : _ <- (pargs [Tptr] [q])?;;
    𝒴;;; '_ : val <- ccallU (cftyp _ _) MemHdr.store [Vptr (qblk, qofs); Vint sz];; (* size of the queue *)
    𝒴;;; '_ : val <- ccallU (cftyp _ _) MemHdr.store [Vptr (qblk, qofs + 1)%Z; Vint 0];; (* first free cell *)
    𝒴;;; ITree.iter (λ (x : nat), (* initialization *)
      𝒴;;;
        if Nat.ltb x (Z.to_nat sz) 
        then 
          '_ : val <- ccallU (cftyp _ _) MemHdr.store [Vptr (qblk, qofs + 2 + x)%Z; Vint 0];; Ret (inl (S x))
        else
          Ret (inr ())
    ) 0;;;
    𝒴;;; Ret q.

  (** enqueue(q : queue, x : item){
      let i : int := FAA(q.back, 1) in
      if(i < q.size){
        q.items[i] := x
      } else {
        while true;
      }
    } *)
  Definition enqueue : list val → itree crisE val := λ q,
    𝒴;;; '(qblk, qofs, v) : mblock * ptrofs * _ <- (pargs [Tptr; Tuntyped] q)?;;
    𝒴;;; 'sz : val <- ccallU (cftyp _ _) MemHdr.load [Vptr (qblk, qofs)];;
    𝒴;;; 'sz : Z <- (pargs [Tint] [sz])?;;
    𝒴;;; 'back : val <- MemHdr.faa [Vptr (qblk, qofs + 1)%Z];;
    𝒴;;; 'back : Z <- (pargs [Tint] [back])?;;
    𝒴;;;
      if (Z.ltb back sz)
      then
        𝒴;;; '_ : val <- ccallU (cftyp _ _) MemHdr.store [Vptr (qblk, qofs + 2 + back)%Z; v];;
        𝒴;;; Ret Vundef
      else
        𝒴;;; ITree.iter (λ _, 𝒴;;; Ret (inl ())) ().

  (** dequeue(q : queue){
        let range = min(!q.back, q.size) in
        let rec dequeue_aux(i) =
          if i = 0 {
            dequeue(q)
          } else {
            let j = range - i in
            let x = ! q.ar[j] in
            if x == null {
              dequeue_aux(i-1)
            } else {
              if resolve (CAS q.ar[j] x null) q.p (j, x) {
                v
              } else {
                dequeue_aux(i-1)
              }
            }
          }
        in
        dequeue_aux(range)
      } *)
  Definition dequeue_aux (q : val) (range : nat) (i : nat) : itree crisE (() + val) :=
    𝒴;;;
      ITree.iter (λ i : nat,
        𝒴;;;
        if (decide (i = 0))
        then Ret (inr (inl ()))
        else
          let j := range - i in
          𝒴;;; '(blk, ofs) : mblock * ptrofs <- (pargs [Tptr] [q])?;;
          𝒴;;; 'x : val <- ccallU (cftyp _ _) MemHdr.load [Vptr (blk, ofs + 2 + j)%Z];;
          match x with
          | Vint 0 => 𝒴;;; Ret (inl (i - 1))
          | Vptr (xblk, xofs) =>
              𝒴;;; 'c : val <- ccallU (cftyp _ _) MemHdr.cas [Vptr (blk, ofs + 2 + j)%Z; x; Vint 0];;
              𝒴;;; 'succ : val <- ccallU (cftyp _ _) MemHdr.cmp [c; x];;
              𝒴;;;
                match succ with
                | Vint 0 => 𝒴;;; Ret (inl (i - 1))
                | Vint 1 => 𝒴;;; Ret (inr (inr c))
                | _ => 𝒴;;; triggerUB
                end
          | _ => 𝒴;;; triggerUB
          end
      ) i.
  Definition dequeue : list val → itree crisE val := λ q,
    𝒴;;; '(qblk, qofs) : mblock * ptrofs <- (pargs [Tptr] q)?;;
    𝒴;;;
      ITree.iter (λ _ : unit,
        𝒴;;; 'sz : val <- ccallU (cftyp _ _) MemHdr.load [Vptr (qblk, qofs)];;
        𝒴;;; 'sz : Z <- (pargs [Tint] [sz])?;;
        𝒴;;; 'back : val <- ccallU (cftyp _ _) MemHdr.load [Vptr (qblk, qofs + 1)%Z];;
        𝒴;;; 'back : Z <- (pargs [Tint] [back])?;;
        𝒴;;; let range := Z.to_nat (Z.min sz back) in
        dequeue_aux (Vptr (qblk, qofs)) range range) ().

  Definition msk : emask :=
    CFilter.msk_filter_in (MemHdr.exports ∪ SchHdr.exports) (msk_real (msk_scp [] msk_true)).

  Definition fnsems : fnsemmap :=
    {[fid HWQHdr.new_queue # (msk, (None, cfunU (cftyp _ _) new_queue));
      fid HWQHdr.enqueue   # (msk, (None, cfunU (cftyp _ _) enqueue));
      fid HWQHdr.dequeue   # (msk, (None, cfunU (cftyp _ _) dequeue))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := [];
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.

  Lemma filter_prophecy mn : CFilter.filter (Prophecy.exports mn) t = t.
  Proof. cfilter_solver. Qed.
End HWQI. End HWQI.
