Require Import CRIS.common.CRIS ImpPrelude.
Require Import MemHeader CRIS.scheduler.SchHeader PQueueHeader IOHeader.
From CRIS.scheduler Require Import Atomic SchA SchTactics.
Require Import PQueueA StackA MemA.
Require Import MemTactics.
Require Import CRIS.helping.HelpingTactics.
Require Import CRIS.scheduler.SchI.

Section preds.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.

  Definition data_inv (b cb : mblock) (cofs : ptrofs) (num reqid : nat) : iProp Σ :=
    ((b, 0%Z) ↦ Vint 0 ∨ (b, 0%Z) ↦ Vint 1 ∗ HelpDone reqid (Vundef↑↑)) ∗
    (b, 1%Z) ↦ Vptr (cb, cofs) ∗ (b, 2%Z) ↦ Vint num.
  Definition syn_data_inv {n} (b cb : mblock) (cofs : ptrofs) (num reqid : nat) : GTerm.t n :=
    (((b, 0%Z) ↦ Vint 0 ∨ (b, 0%Z) ↦ Vint 1 ∗ syn_HelpDone _ reqid (Vundef↑↑)) ∗
    (b, 1%Z) ↦ Vptr (cb, cofs) ∗ (b, 2%Z) ↦ Vint num)%SAT.
  Global Instance data_inv_red n b cb cofs num reqid :
    SLRed n (syn_data_inv b cb cofs num reqid) (data_inv b cb cofs num reqid).
  Proof. solve_sl_red. Qed.

  Definition proxy_inv (n : nat) (N : namespace) (γq : gname) (sz : nat) : iProp Σ := 
    ∃ (bins : list (list val)), ⌜base.length bins = sz⌝ ∗ queue_contents γq bins ∗
      [∗ list] l ∈ bins, [∗ list] v ∈ l,
        ∃ reqid cb cofs num, HelpPend reqid (Some N) (cb, cofs, 0, num, None : option val)↑↑ ∗
        ∃ b γh, ⌜v = Vptr (b, 0%Z)⌝ ∗
          hinv (N.@"proxy".@"data") γh (syn_data_inv b cb cofs num reqid : GTerm.t n).
  Definition syn_proxy_inv {n} (N : namespace) (γq : gname) (sz : nat) : GTerm.t n := 
    (∃ (bins : τ{list (list val)}), ⌜base.length bins = sz⌝ ∗ syn_queue_contents γq bins ∗
      [∗ list] l ∈ bins, [∗ list] v ∈ l,
        ∃ (reqid : τ{nat}) (cb : τ{mblock})
          (cofs : τ{ptrofs}) (num : τ{nat}),
            syn_HelpPend _ reqid (Some N) ((cb, cofs, 0, num, None) : mblock * ptrofs * nat * nat * option val)↑↑ ∗
        ∃ (b : τ{mblock}) (γh : τ{gname}), ⌜v = Vptr (b, 0%Z)⌝ ∗
          syn_hinv (N.@"proxy".@"data") γh (syn_data_inv b cb cofs num reqid))%SAT.
  Global Instance proxy_inv_red n N γq sz :
    SLRed n (syn_proxy_inv N γq sz) (proxy_inv n N γq sz).
  Proof. solve_sl_red. Qed.

  Definition is_proxy (N : namespace) (q : val) (sz : nat) : iProp Σ :=
    ∃ (qb : mblock) (qofs : ptrofs), ⌜q = Vptr (qb, qofs)⌝ ∗
      ∃ (γq : gname), is_queue (N.@"queue") 0 γq sz q ∗
        inv 0 (N.@"proxy") (syn_proxy_inv N γq sz).

  Definition proxy_spec : fspec :=
    fspec_sch ⊤
      (fspec_mk
        (λ (_ : ()) varg arg, ∃ q, ⌜arg = varg ∧ varg = ([q]↑↑)↑⌝ ∗ ∃ N sz, is_proxy N q sz)%I
        (λ _ _ _, False%I)).

  Definition jobCode : SAny.t → itree crisE (SAny.t + SAny.t) := λ arg,
    '((blk, ofs), i, n, vo) : mblock * ptrofs * nat * nat * option val <- (arg↓↓)?;;
    match vo with
    | Some v =>
        trigger (IO (I:=val) "network.send" (i, v));;;
        Ret (inl ((blk, ofs)%Z, S i, n, None : option val)↑↑)
    | None =>
      if (decide (i = n)) then Ret (inr Vundef↑↑)
      else
        v <- trigger (Take val);;
        trigger (Assume ((blk, ofs + i)%Z ↦ v));;;
        trigger (Guarantee ((blk, ofs + i)%Z ↦ v));;;
        Ret (inl ((blk, ofs)%Z, i, n, Some v)↑↑)
    end.
End preds.

Module IOA. Section IOA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.

  Definition init (arg : Any.t) :=
    {{{ ∀∀ (sz : nat), ⌜arg = [Vint sz]↑ ∧ 8 * (sz + 1) < modulus_64⌝%Z }}}
      𝒴@{Some N};;; q <- trigger (Choose val);;
      𝒮@{fn_name IOHdr.proxy, [q]↑↑, proxy_spec};;;
      Ret (q↑, q)
    {{{ ∀∀ (q : val), is_proxy N q sz }}} @ N.

  Definition request (arg : Any.t) :=
    {{{ ∀∀ '((q, bofs, num, prt) : _ * _ * nat * nat),
        ⌜arg = [q; Vptr bofs; Vint num; Vint prt]↑⌝ ∗ ∃ sz, is_proxy N q sz ∗ ⌜prt < sz⌝ }}}
      yield_namespace_iter (Some N) (λ i : nat,
        if decide (i = num) then Ret (inr tt)
        else
          v <- trigger (Take val);;
          trigger (Assume ((bofs.1, bofs.2 + i)%Z ↦ v));;;
          trigger (Guarantee ((bofs.1, bofs.2 + i)%Z ↦ v));;;
          𝒴@{Some N};;;
          trigger (IO (I:=val) "network.send" (i, v));;;
          Ret (inl (S i))
      ) 0;;;
      Ret (Vundef↑, tt)
    {{{ ∀∀ (_ : ()), emp }}} @ N.

  Definition fnsems : fnsemmap :=
    {[ fid IOHdr.init    # (msk_scp [] msk_true, (None, init));
       fid IOHdr.request # (msk_scp [] msk_true, (None, request)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.initial_st := ∅;
    SMod.fnsems := fnsems;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IOA. End IOA.

Module IOM. Section IOM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.
  Context (mn : string).

  Definition request (arg : Any.t) :=
    {{{ ∀∀ '((q, bofs, num, prt) : _ * _ * nat * nat), 
        ⌜arg = [q; Vptr bofs; Vint num; Vint prt]↑⌝ ∗ ∃ sz, is_proxy N q sz ∗ ⌜prt < sz⌝ }}}
      trigger (Call (Helping.run mn) (Some N, ((bofs.1, bofs.2), 0, num, None : option val)↑↑)↑);;;
      Ret (Vundef↑, tt)
    {{{ ∀∀ (_ : ()), emp }}} @ N.

  Definition fnsems : fnsemmap :=
    {[ fid IOHdr.init    # (msk_scp [] msk_true, (None, IOA.init));
       fid IOHdr.request # (msk_scp [] msk_true, (None, request)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.initial_st := ∅;
    SMod.fnsems := fnsems;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End IOM. End IOM.

Module ProxyA. Section ProxyA.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.

  Definition proxy : list val → itree crisE val := λ _,
    𝒴;;; trigger (Choose val).

  Definition fnsems : fnsemmap :=
    {[ fid IOHdr.proxy # (msk_scp [] msk_true, (fsp_some proxy_spec, cfunN (fntyp _ _) (sfunN imp_fun_t proxy))) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.initial_st := ∅;
    SMod.fnsems := fnsems;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp : Mod.t := SMod.to_mod sp smod.
End ProxyA. End ProxyA.

Module ProxyM. Section ProxyM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !schGS, !memGS, !queueG, !stackGS}.
  Context (mn : string).

  Definition proxy (arg : Any.t) :=
    {{{ ∀∀ (q : val), ⌜arg = ([q]↑↑)↑⌝ ∗ ∃ sz, is_proxy N q sz }}}
      yield_namespace_iter (Some N) (λ _ : (),
        trigger (Call (Helping.help mn) (Some N)↑);;;
        Ret (inl tt : () + ())
      ) tt;;;
      v <- trigger (Choose val);;
      Ret (v↑, tt)
    {{{ ∀∀ (_ : ()), False }}} @ N.

  Definition fnsems : fnsemmap :=
    {[ fid IOHdr.proxy # (msk_scp [] msk_true, (None, proxy)) ]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := [];
    SMod.initial_st := ∅;
    SMod.fnsems := fnsems;
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End ProxyM. End ProxyM.
