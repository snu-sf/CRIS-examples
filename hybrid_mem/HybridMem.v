From CRIS Require Import CRIS.
Require Import MemHdr MemLib DetMem.

Module HybMem. Section HybMem.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.
  Import DetMem.

  Definition v_mem := "MemH" ↯ "mem".

  Definition val_r (arg : val) q v : iProp Σ :=
    match arg with
    | Vptr (b, ofs) => (b, ofs) ⤇{q} v
    | _ => True%I
    end.

  Definition compare_val (v0 v1: val) : val :=
    match v0, v1 with
    | Vint i0, Vint i1 => Vint (if dec i0 i1 then 1 else 0)
    | Vint 0, Vptr _ => Vint 0
    | Vptr _, Vint 0 => Vint 0
    | Vptr (b0,ofs0), Vptr (b1,ofs1) =>
       if dec b0 b1 && dec ofs0 ofs1 then Vint 1 else Vint 0
    | _, _ => Vundef
    end.


  Definition alloc : list val → itree crisE val :=
    λ arg,
      'sz : Z <- (pargs [Tint] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b
      then 
        trigger (Assume (⌜0 <= sz /\ 8 * sz < modulus_64⌝)%Z%I);;;
        blk <- trigger (Choose nat);;
        trigger (Guarantee ((blk, 0%Z) |=> List.repeat Vundef (Z.to_nat sz)));;;
        Ret (Vptr (blk, 0%Z))
      else 
          if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
          then
              mem <- trigger (SGet v_mem);; mem <- mem↓?;;
              delta <- trigger (Choose nat);;
              let mem0 := Mem.mem_pad mem delta in
              let (blk, mem1) := Mem.alloc mem0 sz in
              trigger (SPut v_mem mem1↑);;;
              Ret (Vptr (blk, 0%Z))
          else triggerUB
    .

  Definition free : list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b 
      then 
        trigger (Assume (∃v, bofs ⤇ v));;; Ret (Vint 0)
      else 
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        mem1 <- (Mem.free mem bofs)?;;
        trigger (SPut v_mem mem1↑);;;
        Ret (Vint 0)
    . 

  Definition load: list val -> itree crisE val :=
    fun arg =>      
      bofs <- (pargs [Tptr] arg)?;;    
      'b : bool <- trigger (Take bool);;
      if b
      then
        '(v, q) : _ <- trigger (Take _);;
        trigger (Assume (bofs ⤇{q} v));;;
        trigger (Guarantee (bofs ⤇{q} v));;;
        Ret v
      else
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        v <- (Mem.load mem bofs)?;;
        Ret v
      .

  Definition store : list val → itree crisE val :=
    fun arg =>
      '(bofs, v): _ <- (pargs [Tptr; Tuntyped] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b
      then 
        trigger (Assume (∃v_old, bofs ⤇ v_old));;;
        trigger (Guarantee (bofs ⤇ v));;;
        Ret (Vint 0)
      else 
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        mem1 <- (Mem.store mem bofs v)?;;
        trigger (SPut v_mem mem1↑);;;
        Ret (Vint 0)
  .

  Definition cmp : list val → itree crisE val :=
    fun arg =>
      '(arg0, arg1): _ <- (pargs [Tuntyped; Tuntyped] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b
      then
        '((v0, q0), (v1, q1)): _ <- trigger (Take _);;
        trigger (Assume (⌜∃ succ, compare_val arg0 arg1 = Vint succ⌝ ∗ val_r arg0 q0 v0 ∗ val_r arg1 q1 v1));;;
        trigger (Guarantee (val_r arg0 q0 v0 ∗ val_r arg1 q1 v1));;;
        Ret (compare_val arg0 arg1)
      else
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        succ <- (Mem.vcmp mem arg0 arg1)?;;
        Ret (Vint (if succ then 1 else 0))
  .

  Definition cas : list val → itree crisE val :=
    fun arg =>
      '(bofs, (v_old, v_new)): _ <- (pargs [Tptr; Tuntyped; Tuntyped] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b 
      then
        '(v_cur, succ, (v0, q0), (v1, q1)) : _ <- trigger (Take _);;
        trigger (Assume (⌜compare_val v_cur v_old = Vint succ⌝ ∗ bofs ⤇ v_cur ∗ val_r v_cur q0 v0 ∗ val_r v_old q1 v1));;;
        trigger (Guarantee (bofs ⤇ (if dec succ 1 then v_new else v_cur) ∗ val_r v_cur q0 v0 ∗ val_r v_old q1 v1));;;
        Ret v_cur
      else
        'v_cur: val <- ccallU MemHdr.load [Vptr bofs];;
        'succ: val <- ccallU MemHdr.cmp [v_cur; v_old];;
        (if (dec succ (Vint 1))
        then ccallU MemHdr.store [Vptr bofs; v_new]
        else Ret Vundef);;;
        Ret v_cur
  .

  Definition fnsems : fnsemmap :=
    {[Some MemHdr.alloc := Some (msk_scp scopes msk_true, (None, cfunU alloc));
      Some MemHdr.free  := Some (msk_scp scopes msk_true, (None, cfunU free));
      Some MemHdr.load  := Some (msk_scp scopes msk_true, (None, cfunU load));
      Some MemHdr.store := Some (msk_scp scopes msk_true, (None, cfunU store));
      Some MemHdr.cmp   := Some (msk_scp scopes msk_true, (None, cfunU cmp));
      Some MemHdr.cas   := Some (msk_scp scopes msk_true, (None, cfunU cas))]}.

  (* Module definition *)
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem := Some (Mem.empty)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := mem_init_auth.

  Definition t := SMod.to_mod ∅ smod.
End HybMem. End HybMem.
