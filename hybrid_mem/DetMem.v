From CRIS Require Import CRIS.
Require Import MemHdr MemLib.

(* Deterministic Memory model, Bottom-level memory model of this example. *)

Module DetMem. Section DetMem.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["MemH"].
  Definition v_mem := "MemH" ↯ "mem".

  Definition alloc : list val → itree crisE val :=
    fun arg =>
      'sz : Z <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      if (bool_decide (0 <= (8 * sz) < modulus_64))%Z
      then (
            let mem0 : Mem.t := mem in
            let (loc, mem1) := Mem.alloc mem0 sz in
            trigger (SPut v_mem mem1↑);;;
            Ret (Vint loc))
      else triggerUB
. 

  Definition free : list val → itree crisE val :=
    λ arg,
      loc <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem loc)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  . 

  Definition load: list val -> itree crisE val :=
    fun arg =>      
      'loc : Z <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem loc)?;;
      Ret v
  .

  Definition store : list val → itree crisE val :=
    fun arg =>
      '(loc, v) : _ <- (pargs [Tint; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem loc v)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  .

  Definition cmp : list val → itree crisE val :=
    fun arg =>
      '(v0, v1): _ <- (pargs [Tuntyped; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      'b: bool <- (Mem.vcmp mem v0 v1)?;;
      Ret (Vint (if b then 1 else 0))
  .

  Definition cas: list val -> itree crisE val :=
    fun arg =>
      ' (loc, (v_old, v_new)): _ <- (pargs [Tint; Tuntyped; Tuntyped] arg)?;;
      'v_cur: val <- ccallU MemHdr.load [Vint loc];;
      'succ: val <- ccallU MemHdr.cmp [v_cur; v_old];;
      (if (bool_decide (succ = (Vint 1)))
       then ccallU MemHdr.store [Vint loc; v_new]
       else Ret Vundef);;;
      Ret v_cur
  .
  
  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc # (msk_real (msk_scp scopes msk_true), (None, cfunU alloc));
      fid MemHdr.free  # (msk_real (msk_scp scopes msk_true), (None, cfunU free));
      fid MemHdr.load  # (msk_real (msk_scp scopes msk_true), (None, cfunU load));
      fid MemHdr.store # (msk_real (msk_scp scopes msk_true), (None, cfunU store));
      fid MemHdr.cmp   # (msk_real (msk_scp scopes msk_true), (None, cfunU cmp));
      fid MemHdr.cas   # (msk_real (msk_scp scopes msk_true), (None, cfunU cas))]}.

  Program Definition smod : SMod.t :=
    {|
      SMod.scopes := scopes;
      SMod.fnsems := fnsems ;
      SMod.initial_st := {[v_mem # (Mem.empty)↑]};
    |}
  .
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End DetMem. End DetMem.
