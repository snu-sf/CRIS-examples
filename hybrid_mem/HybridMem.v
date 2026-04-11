From CRIS Require Import CRIS.
Require Import MemHdr MemLib DetMem.

Module HybMem. Section HybMem.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.
  Import DetMem.

  Definition v_mem := "MemH" ↯ "mem".

  Definition val_r (arg : val) q v : iProp Σ :=
    match arg with
    | Vint loc => if bool_decide (0 < loc)%Z then loc ⤇{q} v else True%I
    | _ => True%I
    end.

  Definition compare_val (v0 v1: val) : val :=
    match v0, v1 with
    | Vint i0, Vint i1 =>
      if bool_decide (0 < i0)%Z
      then
        if bool_decide (0 < i1)%Z
        then Vint (if bool_decide (i0 = i1) then 1 else 0)
        else if bool_decide (i1 = 0)%Z then Vint 0 else Vundef
      else
        if bool_decide (0 < i1)%Z
        then if bool_decide (i0 = 0)%Z then Vint 0 else Vundef
        else Vint (if bool_decide (i0 = i1) then 1 else 0)
    | _, _ => Vundef
    end.


  Definition alloc : list val → itree crisE val :=
    λ arg,
      'sz : Z <- (pargs [Tint] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b
      then 
        trigger (Assume (⌜0 <= sz /\ 8 * sz < modulus_64⌝)%Z%I);;;
        loc <- trigger (Choose Z);;
        trigger (Guarantee (⌜(0 < loc)%Z⌝ ∗ loc |=> List.repeat Vundef (Z.to_nat sz)));;;
        Ret (Vint loc)
      else 
          if (bool_decide (0 <= (8 * sz) < modulus_64))%Z
          then
              mem <- trigger (SGet v_mem);; mem <- mem↓?;;
              delta <- trigger (Choose nat);;
              let mem0 := Mem.mem_pad mem delta in
              let (loc, mem1) := Mem.alloc mem0 sz in
              trigger (SPut v_mem mem1↑);;;
              Ret (Vint loc)
          else triggerUB
    .

  Definition free : list val → itree crisE val :=
    λ arg,
      loc <- (pargs [Tint] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b 
      then 
        trigger (Assume (∃v, loc ⤇ v));;; Ret (Vint 0)
      else 
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        mem1 <- (Mem.free mem loc)?;;
        trigger (SPut v_mem mem1↑);;;
        Ret (Vint 0)
    . 

  Definition load: list val -> itree crisE val :=
    fun arg =>      
      loc <- (pargs [Tint] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b
      then
        '(v, q) : _ <- trigger (Take _);;
        trigger (Assume (loc ⤇{q} v));;;
        trigger (Guarantee (loc ⤇{q} v));;;
        Ret v
      else
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        v <- (Mem.load mem loc)?;;
        Ret v
      .

  Definition store : list val → itree crisE val :=
    fun arg =>
      '(loc, v): _ <- (pargs [Tint; Tuntyped] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b
      then 
        trigger (Assume (∃v_old, loc ⤇ v_old));;;
        trigger (Guarantee (loc ⤇ v));;;
        Ret (Vint 0)
      else 
        mem <- trigger (SGet v_mem);; mem <- mem↓?;;
        mem1 <- (Mem.store mem loc v)?;;
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
      '(loc, (v_old, v_new)): _ <- (pargs [Tint; Tuntyped; Tuntyped] arg)?;;
      'b : bool <- trigger (Take bool);;
      if b 
      then
        '(v_cur, succ, (v0, q0), (v1, q1)) : _ <- trigger (Take _);;
        trigger (Assume (⌜compare_val v_cur v_old = Vint succ⌝ ∗ loc ⤇ v_cur ∗ val_r v_cur q0 v0 ∗ val_r v_old q1 v1));;;
        trigger (Guarantee (loc ⤇ (if bool_decide (succ = 1) then v_new else v_cur) ∗ val_r v_cur q0 v0 ∗ val_r v_old q1 v1));;;
        Ret v_cur
      else
        'v_cur: val <- ccallU imp_fun_t MemHdr.load [Vint loc];;
        'succ: val <- ccallU imp_fun_t MemHdr.cmp [v_cur; v_old];;
        (if (bool_decide (succ = (Vint 1)))
        then ccallU imp_fun_t MemHdr.store [Vint loc; v_new]
        else Ret Vundef);;;
        Ret v_cur
  .

  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc # (msk_scp scopes msk_true, (None, cfunU imp_fun_t alloc));
      fid MemHdr.free  # (msk_scp scopes msk_true, (None, cfunU imp_fun_t free));
      fid MemHdr.load  # (msk_scp scopes msk_true, (None, cfunU imp_fun_t load));
      fid MemHdr.store # (msk_scp scopes msk_true, (None, cfunU imp_fun_t store));
      fid MemHdr.cmp   # (msk_scp scopes msk_true, (None, cfunU imp_fun_t cmp));
      fid MemHdr.cas   # (msk_scp scopes msk_true, (None, cfunU imp_fun_t cas))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem # (Mem.empty)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition init_cond : iProp Σ := mem_init_auth.

  Definition t := SMod.to_mod ∅ smod.
End HybMem. End HybMem.
