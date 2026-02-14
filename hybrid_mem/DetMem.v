From CRIS Require Import CRIS.
Require Import MemHdr MemLib.

(* Deterministic Memory model, Bottom-level memory model of this example. *)

Module DetMem. Section DetMem.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS}.

  Definition scopes : list string := ["MemH"].
  Definition v_mem := "MemH" ↯ "mem".

  Definition alloc : list val → itree crisE val :=
    fun arg =>
      'sz : Z <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
      then (
            let mem0 : Mem.t := mem in
            let (blk, mem1) := Mem.alloc mem0 sz in
            trigger (SPut v_mem mem1↑);;;
            Ret (Vptr (blk, 0%Z)))
      else triggerUB
. 

  Definition free : list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem bofs)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0)
  . 

  Definition load: list val -> itree crisE val :=
    fun arg =>      
      bofs <- (pargs [Tptr] arg)?;;        
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem bofs)?;;
      Ret v
  .

  Definition store : list val → itree crisE val :=
    fun arg =>
      '(bofs, v): _ <- (pargs [Tptr; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem bofs v)?;;
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
      ' (bofs, (v_old, v_new)): _ <- (pargs [Tptr; Tuntyped; Tuntyped] arg)?;;
      'v_cur: val <- ccallU MemHdr.load [Vptr bofs];;
      'succ: val <- ccallU MemHdr.cmp [v_cur; v_old];;
      (if (dec succ (Vint 1))
       then ccallU MemHdr.store [Vptr bofs; v_new]
       else Ret Vundef);;;
      Ret v_cur
  .
  
  Definition fnsems : fnsemmap :=
    {[Some MemHdr.alloc := Some (msk_real (msk_scp scopes msk_true), (None, cfunU alloc));
      Some MemHdr.free  := Some (msk_real (msk_scp scopes msk_true), (None, cfunU free));
      Some MemHdr.load  := Some (msk_real (msk_scp scopes msk_true), (None, cfunU load));
      Some MemHdr.store := Some (msk_real (msk_scp scopes msk_true), (None, cfunU store));
      Some MemHdr.cmp   := Some (msk_real (msk_scp scopes msk_true), (None, cfunU cmp));
      Some MemHdr.cas   := Some (msk_real (msk_scp scopes msk_true), (None, cfunU cas))]}.

  Program Definition smod : SMod.t :=
    {|
      SMod.scopes := scopes;
      SMod.fnsems := fnsems ;
      SMod.initial_st := {[v_mem := Some (Mem.empty)↑]};
    |}
  .
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ smod.
End DetMem. End DetMem.
