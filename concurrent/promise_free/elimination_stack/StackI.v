Require Import CRIS.common.CRIS.
Require Import CRIS.scheduler.SchHeader.
From CRIS.promise_free.algebra Require Import HistoryRA.
From CRIS.promise_free.pfmem Require Import PFMemHeader.
From CRIS.promise_free.system Require Import SystemHeader.
From CRIS.promise_free.elimination_stack Require Export StackHeader.

Module StackI. Section StackI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := [].

  Definition new_stack : () → itree crisE Val.t := λ _,
    stack <- ccallU SystemHdr.alloc 3;;
    𝒴;;; loc <- parse_loc stack;;
    (* The third cell is a stable atomic guard.  Shared pointer histories use
       the guard pointer as their empty value, so every compared pointer has
       a permanently allocated atomic target. *)
    𝒴;;; '_ : Val.t <- ccallU SystemHdr.write (loc >> 2, Val.zero, Ordering.na);;
    𝒴;;; '_ : Val.t <- ccallU SystemHdr.write
      (loc >> 0, Val.Vptr (loc >> 2), Ordering.na);;
    𝒴;;; '_ : Val.t <- ccallU SystemHdr.write
      (loc >> 1, Val.Vptr (loc >> 2), Ordering.na);;
    𝒴;;; Ret stack.

  Definition push_once (stack value : Val.t) : itree crisE (() + Val.t) :=
    Sch.yield;;; stack_loc <- parse_loc stack;;
    Sch.yield;;; head_old <- ccallU SystemHdr.read (stack_loc >> 0, Ordering.acqrel);;
    head_old_loc <- parse_loc head_old;;
    let head_old := Val.Vptr head_old_loc in

    (* Cell 0 is a stable guard; cells 1 and 2 hold next and value. *)
    Sch.yield;;; node <- ccallU SystemHdr.alloc 3;;
    Sch.yield;;; node_loc <- parse_loc node;;
    Sch.yield;;; '_ : Val.t <- ccallU SystemHdr.write (node_loc >> 0, Val.zero, Ordering.na);;
    Sch.yield;;; '_ : Val.t <- ccallU SystemHdr.write (node_loc >> 1, head_old, Ordering.na);;
    Sch.yield;;; '_ : Val.t <- ccallU SystemHdr.write
      (node_loc >> 2, StackHdr.encode value, Ordering.na);;
    Sch.yield;;; won <- ccallU SystemHdr.cas
      (stack_loc >> 0, head_old, node, Ordering.relaxed, Ordering.acqrel);;
    Sch.yield;;; won <- parse_num won;;
    if decide (won = 1) then Ret (inr Val.zero) else
    if decide (won = 0) then
      (* The fast path lost. Publish an elimination offer that a pop may take. *)
      Sch.yield;;; offer <- ccallU SystemHdr.alloc 3;;
      Sch.yield;;; offer_loc <- parse_loc offer;;
      Sch.yield;;; '_ : Val.t <- ccallU SystemHdr.write (offer_loc >> 0, Val.zero, Ordering.na);;
      Sch.yield;;; '_ : Val.t <- ccallU SystemHdr.write (offer_loc >> 1, Val.zero, Ordering.na);;
      Sch.yield;;; '_ : Val.t <- ccallU SystemHdr.write
        (offer_loc >> 2, StackHdr.encode value, Ordering.na);;
      (* Only the winner may expose this offer in the shared slot. *)
      Sch.yield;;; published <- ccallU SystemHdr.cas
        (stack_loc >> 1, Val.Vptr (stack_loc >> 2), offer,
          Ordering.relaxed, Ordering.acqrel);;
      Sch.yield;;; published <- parse_num published;;
      if decide (published = 1) then
        (* Remove exactly our offer; a pop claims it through its state cell. *)
        Sch.yield;;; cleared <- ccallU SystemHdr.cas
          (stack_loc >> 1, offer, Val.Vptr (stack_loc >> 2),
            Ordering.relaxed, Ordering.acqrel);;
        Sch.yield;;; cleared <- parse_num cleared;;
        (* A failed clear means that a pop claimed the slot.  In either case,
           the state CAS decides whether this push was taken or must retry. *)
        '_ : () <- (
          if decide (cleared = 1) then Ret () else
          if decide (cleared = 0) then Ret () else triggerUB);;
        (* 0 -> 1 means that a pop took the offer; 0 -> 2 withdraws it. *)
        Sch.yield;;; withdrew <- ccallU SystemHdr.cas
          (offer_loc >> 1, Val.zero, Val.Vnum 2,
            Ordering.acqrel, Ordering.acqrel);;
        Sch.yield;;; withdrew <- parse_num withdrew;;
        if decide (withdrew = 1) then Ret (inl ()) else
        if decide (withdrew = 0) then Ret (inr Val.zero) else triggerUB
      else if decide (published = 0) then Ret (inl ()) else triggerUB
    else triggerUB.

  Definition push_loop (stack value : Val.t) : itree crisE Val.t :=
    ITree.iter (λ _, push_once stack value) ().

  Lemma push_loop_unfold stack value :
    push_loop stack value =
      lr <- push_once stack value;;
      match lr with
      | inl next => tau;; push_loop stack value
      | inr ret => Ret ret
      end.
  Proof.
    unfold push_loop at 1. rewrite unfold_iter.
    f_equal. apply functional_extensionality. intros [[ ]|ret]; reflexivity.
  Qed.

  Global Opaque push_loop.

  Definition push : Val.t * Val.t → itree crisE Val.t := λ '(stack, value),
    𝒴;;; push_loop stack value.

  Definition pop_once (stack : Val.t) : itree crisE (() + Val.t) :=
    Sch.yield;;; stack_loc <- parse_loc stack;;
    Sch.yield;;; head_old <- ccallU SystemHdr.read (stack_loc >> 0, Ordering.acqrel);;
    match head_old with
    | Val.Vptr node_loc =>
        if decide (node_loc = (stack_loc >> 2)) then
          (* An acquire load may see an old sentinel message.  Validate that
             it is still current before reporting an empty stack. *)
          Sch.yield;;; empty <- ccallU SystemHdr.cas
            (stack_loc >> 0, head_old, head_old,
              Ordering.relaxed, Ordering.acqrel);;
          Sch.yield;;; empty <- parse_num empty;;
          if decide (empty = 1) then Ret (inr Val.Vundef) else
          if decide (empty = 0) then Ret (inl ()) else triggerUB
        else
        Sch.yield;;; next <- ccallU SystemHdr.read (node_loc >> 1, Ordering.relaxed);;
        Sch.yield;;; won <- ccallU SystemHdr.cas
          (stack_loc >> 0, head_old, next, Ordering.relaxed, Ordering.acqrel);;
        Sch.yield;;; won <- parse_num won;;
        if decide (won = 1) then
          Sch.yield;;; value <- ccallU SystemHdr.read (node_loc >> 2, Ordering.na);;
          Sch.yield;;; Ret (inr (StackHdr.decode value))
        else if decide (won = 0) then
          (* A failed pop may complete a pending push through its offer. *)
          Sch.yield;;; offer <- ccallU SystemHdr.read (stack_loc >> 1, Ordering.acqrel);;
          match offer with
          | Val.Vptr offer_loc =>
              if decide (offer_loc = (stack_loc >> 2)) then Ret (inl ()) else
              (* Claim the current slot before dereferencing the offer.  A
                 stale slot read can only fail this validation CAS. *)
              Sch.yield;;; claimed <- ccallU SystemHdr.cas
                (stack_loc >> 1, offer, Val.Vptr (stack_loc >> 2),
                  Ordering.acqrel, Ordering.acqrel);;
              Sch.yield;;; claimed <- parse_num claimed;;
              if decide (claimed = 1) then
                Sch.yield;;; took <- ccallU SystemHdr.cas
                  (offer_loc >> 1, Val.zero, Val.one,
                    Ordering.acqrel, Ordering.acqrel);;
                Sch.yield;;; took <- parse_num took;;
                if decide (took = 1) then
                  Sch.yield;;; value <- ccallU SystemHdr.read
                    (offer_loc >> 2, Ordering.na);;
                  Sch.yield;;; Ret (inr (StackHdr.decode value))
                else if decide (took = 0) then Ret (inl ()) else triggerUB
              else if decide (claimed = 0) then Ret (inl ()) else triggerUB
          | _ => triggerUB
          end
        else triggerUB
    | _ => triggerUB
    end.

  Definition pop : Val.t → itree crisE Val.t := λ stack,
    ITree.iter (λ _, pop_once stack) ().

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack #
        (msk_real (msk_scp scopes msk_true),
          (None, cfunU StackHdr.new_stack new_stack));
      fid StackHdr.push #
        (msk_real (msk_scp scopes msk_true),
          (None, cfunU StackHdr.push push));
      fid StackHdr.pop #
        (msk_real (msk_scp scopes msk_true),
          (None, cfunU StackHdr.pop pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End StackI. End StackI.
