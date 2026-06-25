From CRIS Require Import CRIS MemHeader HelpingHeader ProphecyHeader.

Module Mem.
  Record t : Type := mk {
    cnts : mblock → Z → option val;
    nb : mblock;
  }.

  Definition wf (m0 : t) : Prop := ∀ blk ofs (LT : (blk < m0.(nb))%nat), m0.(cnts) blk ofs = None.

  Definition alloc (m : Mem.t) (sz : Z) : mblock * Mem.t :=
    (nb m,
     Mem.mk
      (update (cnts m)
        (nb m) (λ ofs, if bool_decide (0 <= ofs < sz)%Z then Some Vundef else None))
      (S m.(nb))).

  Opaque Z.ltb Z.leb Z.mul Z.eq_dec Nat.eq_dec.

  Definition empty : t := mk (λ _ _, None) 0.

  Definition free (m0 : Mem.t) := fun '(b,ofs) =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (update m0.(cnts) b (update (m0.(cnts) b) ofs None)) m0.(nb))
    | _ => None
    end.

  Definition load (m0 : Mem.t) := fun '(b,ofs) =>
    m0.(cnts) b ofs.

  Definition store (m0 : Mem.t) := fun '(b,ofs) v =>
    match m0.(cnts) b ofs with
    | Some _ => Some (Mem.mk (fun _b _ofs => if (dec b _b) && (dec ofs _ofs)
                                             then Some v
                                             else m0.(cnts) _b _ofs) m0.(nb))
    | _ => None
    end.

  Definition valid_ptr (m0 : Mem.t) := fun '(b,ofs) =>
    if m0.(cnts) b ofs then true else false.

  Definition load_mem (genv : GEnv.t) : Mem.t :=
    Mem.mk
      (λ blk ofs,
         p ← (genv !! blk); let '(g, gd) := p in
         match gd↓ with
         | Some Gfun =>
           None
         | Some (Gvar gv) =>
           if (bool_decide (ofs = 0%Z)) then Some (Vint gv) else None
         | _ => None
         end)
      (List.length genv).

  Definition mem_pad (m : Mem.t) (delta : nat) : Mem.t :=
    Mem.mk m.(Mem.cnts) (m.(Mem.nb) + delta).

  Definition vcmp (m0 : Mem.t) (x y : val) : option bool :=
    match x, y with
    | Vint x, Vint y => Some (bool_decide (x = y))
    | Vptr (x, xofs), Vptr (y, yofs) =>
      if bool_decide (Mem.valid_ptr m0 (x, xofs) ∧ Mem.valid_ptr m0 (y, yofs))
      then Some (bool_decide (x = y ∧ xofs = yofs))
      else None
    | Vptr (x, xofs), Vint y =>
      if bool_decide (Mem.valid_ptr m0 (x, xofs) ∧ y = 0)
      then Some false
      else None
    | Vint x, Vptr (y, yofs) =>
      if bool_decide (Mem.valid_ptr m0 (y, yofs) ∧ x = 0)
      then Some false
      else None
    | _, _ => None
    end.
End Mem.

Module MemI. Section MemI.
  Context `{!crisG Γ Σ α β τ _S _I}.

  Definition scopes : list string := ["Mem"].
  Definition v_mem : key := "Mem" ↯ "mem".

  Definition alloc : list val → itree crisE val :=
    λ arg,
      'sz : Z <- (pargs [Tint] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      if (bool_decide (0 <= (8 * sz) < modulus_64))%Z
      then
        delta <- trigger (Choose _);;
        let mem0 : Mem.t := Mem.mem_pad mem delta in
        let (blk, mem1) := Mem.alloc mem0 sz in
        trigger (SPut v_mem mem1↑);;;
        Ret (Vptr (blk, 0%Z))
      else triggerUB.

  Definition free : list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.free mem bofs)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0).

  Definition load: list val → itree crisE val :=
    λ arg,
      bofs <- (pargs [Tptr] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      v <- (Mem.load mem bofs)?;;
      Ret v.

  Definition store : list val → itree crisE val :=
    λ arg,
      '(bofs, v): _ <- (pargs [Tptr; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      mem1 <- (Mem.store mem bofs v)?;;
      trigger (SPut v_mem mem1↑);;;
      Ret (Vint 0).

  Definition cmp : list val → itree crisE val :=
    λ arg,
      '(v0, v1): _ <- (pargs [Tuntyped; Tuntyped] arg)?;;
      mem <- trigger (SGet v_mem);; mem <- mem↓?;;
      'b: bool <- (Mem.vcmp mem v0 v1)?;;
      Ret (Vint (if b then 1 else 0)).

  Definition cas: list val → itree crisE val :=
    λ arg,
      '(bofs, (v_old, v_new)) : _ <- (pargs [Tptr; Tuntyped; Tuntyped] arg)?;;
      'v_cur : val <- ccallU MemHdr.load [Vptr bofs];;
      'succ : val <- ccallU MemHdr.cmp [v_cur; v_old];;
      (if (bool_decide (succ = (Vint 1)))
       then ccallU MemHdr.store [Vptr bofs; v_new]
       else Ret Vundef);;;
      Ret v_cur.

  Definition mask : emask :=
    msk_real (msk_scp scopes (CFilter.msk_filter_in MemHdr.exports msk_true)).

  Definition fnsems : fnsemmap :=
    {[fid MemHdr.alloc # (mask, (None, (cfunU imp_fun_t alloc)));
      fid MemHdr.free  # (mask, (None, (cfunU imp_fun_t free)));
      fid MemHdr.load  # (mask, (None, (cfunU imp_fun_t load)));
      fid MemHdr.store # (mask, (None, (cfunU imp_fun_t store)));
      fid MemHdr.cmp   # (mask, (None, (cfunU imp_fun_t cmp)));
      fid MemHdr.cas   # (mask, (None, (cfunU imp_fun_t cas)))]}.

  Program Definition smod genv : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_mem # (Mem.load_mem genv)↑]};
  |}.
  Solve Obligations with mod_tac.

  Definition t genv : Mod.t := SMod.to_mod ∅ (smod genv).

  Lemma filter_prophecy mn genv:
    CFilter.filter (Prophecy.exports mn) (t genv) = t genv.
  Proof. cfilter_solver. Qed.

  Lemma filter_helping mn genv:
    CFilter.filter (Helping.exports mn) (t genv) = t genv.
  Proof. cfilter_solver. Qed.

  Lemma real genv: Mod.real_mod (t genv).
  Proof. real_mod_solver. Qed.
  
End MemI. End MemI.
