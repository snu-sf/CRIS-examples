Require Import CRIS.
Require Import SystemHeader PFMemHeader.

Definition tidmap : Type := gmap Ident.t nat.

Module SystemI. Section SystemI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["System"].
  Definition v_tid := "System" ↯ "tid".
  Definition v_tids := "System" ↯ "tids".

  Definition _spawn : Ident.t * string * SAny.t → itree crisE unit :=
    λ '(my_tid, fn, arg),
      trigger (Call fn arg↑);;;
      System.terminate.

  Definition spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'my_tid : Ident.t <- cgetU v_tid;;
      'tids : tidmap <- cgetU v_tids;;
      'new_mtid : Ident.t <- ccallU PFMemHdr.spawn my_tid;;
      new_stid <- trigger (Spawn SystemHdr._spawn (new_mtid, fn, arg)↑);;
      let newtids : tidmap := <[new_mtid := new_stid]> tids in
      cput v_tids newtids.

  Definition yield : unit → itree crisE unit :=
    λ _,
      'tids : tidmap <- cgetU v_tids;;
      '(exist _ (mtid, stid) _) : _ <- trigger (Choose {p : Ident.t * nat | tids !! p.1 = Some p.2});;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition get_tid : () → itree crisE Ident.t :=
    λ _, cgetU v_tid.

  Definition alloc : nat → itree crisE Val.t :=
    λ sz,
      'tid : Ident.t <- get_tid ();;
      ccallU PFMemHdr.alloc (tid, Z.of_nat sz).

  Definition write : Loc.t * Val.t * Ordering.t → itree crisE Val.t :=
    λ '(loc, val, ord),
      'tid : Ident.t <- get_tid ();;
      ccallU PFMemHdr.write (tid, loc, val, ord).

  Definition read : Loc.t * Ordering.t → itree crisE Val.t :=
    λ '(loc, ord),
      'tid : Ident.t <- get_tid ();;
      ccallU PFMemHdr.read (tid, loc, ord).

  Definition fnsems : fnsemmap :=
    {[Some SystemHdr._spawn := Some (msk_real (msk_scp scopes msk_true), (None, cfunU _spawn));
      Some SystemHdr.spawn := Some (msk_real (msk_scp scopes msk_true), (None, cfunU spawn));
      Some SystemHdr.get_tid := Some (msk_real (msk_scp scopes msk_true), (None, cfunU get_tid));
      Some SystemHdr.yield := Some (msk_real (msk_scp scopes msk_true), (None, cfunU yield));
      Some SystemHdr.alloc := Some (msk_real (msk_scp scopes msk_true), (None, cfunU alloc));
      Some SystemHdr.write := Some (msk_real (msk_scp scopes msk_true), (None, cfunU write));
      Some SystemHdr.read := Some (msk_real (msk_scp scopes msk_true), (None, cfunU read))]}.

  Program Definition Mod: SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st :=
      {[v_tid := Some 1%positive↑; v_tids := Some ({[1%positive := 0]} : tidmap)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ Mod.
End SystemI. End SystemI.
