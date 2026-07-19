Require Import CRIS.common.CRIS.

From CRIS.promise_free.lib Require Import
  Basic Loc Val DataStructure DenseOrder Event.

From CRIS.promise_free.model Require Import Time View Cell.

Set Implicit Arguments.


Module Block.
  Variant state_t :=
    | prealloced
    | global (size: Z)
    | heap (size: Z)
    | freed
  .

  Definition state_t_le st1 st2 :=
    match st1, st2 with
    | global sz1, global sz2 => sz1 = sz2
    | global _, _
    | _, global _ => False
    | prealloced, _
    | _, freed => True
    | heap sz1, heap sz2 => sz1 = sz2
    | _, _ => False
    end.

  Global Program Instance state_t_le_PreOrder: PreOrder state_t_le.
  Next Obligation. ii. unfold state_t_le. des_ifs. Qed.
  Next Obligation. ii. unfold state_t_le in *. des_ifs. Qed.

  Structure t :=
    mk {
        state: state_t;
        contents: Z -> Cell.t;
      }.

  Definition bot: t := mk prealloced (fun _ => Cell.bot).

  Definition init_static (size: Z): t := mk (global size) (fun _ => Cell.init 0%Z).

  Definition init_dynamic: t := mk prealloced (fun _ => Cell.init Val.Vundef).

  Definition alloc (size: Z) (blk: t): t := mk (heap size) (contents blk).

  Definition free (blk: t): t := mk freed (contents blk).

  Definition prealloc (blk: t): t := mk prealloced (contents blk).

  Definition valid (ofs: Z) (blk: t): bool :=
    match state blk with
    | global size
    | heap size => andb (0 <=? ofs)%Z (ofs <=? size)%Z
    | _ => false
    end.

Definition accessible (ofs: Z) (blk: t): bool :=
    match state blk with
    | global size
    | heap size => andb (0 <=? ofs)%Z (ofs <? size)%Z
    | _ => false
    end.

  Definition is_freeable (blk: t): bool :=
    match state blk with
    | heap _ => true
    | _ => false
    end.

  Definition is_prealloced (blk: t): bool :=
    match state blk with
    | prealloced => true
    | _ => false
    end.

  Definition is_global (blk: t): bool :=
    match state blk with
    | global _ => true
    | _ => false
    end.

  Definition is_freed (blk: t): bool :=
    match state blk with
    | freed => true
    | _ => false
    end.

  Definition get (ofs:Z) (ts:Time.t) (blk:t): option (Time.t * Message.t) :=
    Cell.get ts (contents blk ofs).

  Definition get_size (blk:t): option Z :=
    match state blk with
    | global size
    | heap size => Some size
    | _ => None
    end.

  Lemma ext
        lhs rhs
        (STATE: state lhs = state rhs)
        (EXT: forall ofs ts, get ofs ts lhs = get ofs ts rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs. ss. subst. f_equal.
    extensionality ofs. apply Cell.ext. eauto.
  Qed.

  Lemma ext_contents lhs rhs
        (GET: forall ofs to, get ofs to lhs = get ofs to rhs):
    contents lhs = contents rhs.
  Proof.
    extensionality ofs. apply Cell.ext. eauto.
  Qed.

  Lemma prealloced_is_not_accessible (ofs: Z) (blk: t) 
        (PREALLOC: is_prealloced blk)
        (ACCESSIBLE: accessible ofs blk) : False.
  Proof.
    destruct blk, state0; unfold is_prealloced, accessible in *; ss.
  Qed.

  Lemma prealloced_is_not_global (blk: t) 
        (PREALLOC: is_prealloced blk)
        (GLOBAL: is_global blk) : False.
  Proof.
    destruct blk, state0; unfold is_prealloced, is_global in *; ss.
  Qed.

  Lemma prealloced_is_not_freeable (blk: t) 
        (PREALLOC: is_prealloced blk)
        (FREEABLE: is_freeable blk) : False.
  Proof.
    destruct blk, state0; unfold is_prealloced, is_freeable in *; ss.
  Qed.

  Lemma prealloced_is_not_freed (blk: t) 
        (PREALLOC: is_prealloced blk)
        (FREED: is_freed blk) : False.
  Proof.
    destruct blk, state0; unfold is_prealloced, is_freed in *; ss.
  Qed.

  Variant add (blk1:t) (ofs:Z) (from to:Time.t) (msg:Message.t) (blk2:t): Prop :=
    | add_intro
        r
        (ADD: Cell.add (contents blk1 ofs) from to msg r)
        (BLK2: blk2 = mk (state blk1)
                         (fun ofs' => if Z.eq_dec ofs' ofs
                                      then r
                                      else contents blk1 ofs'))
  .

  Variant remove (blk1:t) (ofs:Z) (from to:Time.t) (msg:Message.t) (blk2:t): Prop :=
    | remove_intro
        r
        (REMOVE: Cell.remove (contents blk1 ofs) from to msg r)
        (BLK2: blk2 = mk (state blk1)
                         (fun ofs' => if Z.eq_dec ofs' ofs
                                      then r
                                      else contents blk1 ofs'))
  .

  Definition ofs_ts_eq_dec := pair_eq_dec Z.eq_dec Time.eq_dec.

  Lemma add_o
        blk2 blk1 ofs from to msg
        o t
        (ADD: add blk1 ofs from to msg blk2):
    get o t blk2 =
      if ofs_ts_eq_dec (o, t) (ofs, to)
      then Some (from, msg)
      else get o t blk1.
  Proof.
    inv ADD. unfold get in *. ss.
    condtac; ss; subst.
    - erewrite Cell.add_o; eauto.
      condtac; ss; subst.
      + condtac; ss. des; ss.
      + condtac; ss. des; ss.
    - condtac; ss. des; ss.
  Qed.

  Lemma remove_o
    blk1 blk2 ofs from to msg
    o t
    (REMOVE: remove blk1 ofs from to msg blk2):
    get o t blk2 =
      if ofs_ts_eq_dec (o, t) (ofs, to)
      then None
      else get o t blk1.
  Proof.
    inv REMOVE. unfold get in *. ss.
    condtac; ss; subst.
    - erewrite Cell.remove_o; eauto.
      condtac; ss; subst.
      + condtac; ss. des; ss.
      + condtac; ss. des; ss.
    - condtac; ss. des; ss.
  Qed.

  Definition cap (b b_cap: t):=
    <<STATE: state_t_le (state b) (state b_cap)>> /\
    <<CONTENTS: forall ofs, Cell.cap (contents b ofs) (contents b_cap ofs)>>.
  
  Lemma cap_exists b:
    exists b_cap, cap b b_cap /\ state b = state b_cap.
  Proof.
    unfold cap. destruct b as [st blk]. ss. 
    cut (exists blk_cap, forall ofs,
            (fun ofs cell => Cell.cap (blk ofs) cell) ofs (blk_cap ofs)).
    { i. des. exists (mk st blk_cap). splits; ss. refl. }
    eapply dependent_functional_choice. i. apply Cell.cap_exists.
  Qed.

  Lemma future_cap_exists b st_future
    (STATE: state_t_le (state b) st_future):
    exists b_cap, cap b b_cap /\ state b_cap = st_future.
  Proof.
    unfold cap. destruct b as [st blk]. ss.
    cut (exists blk_cap, forall ofs,
            (fun ofs cell => Cell.cap (blk ofs) cell) ofs (blk_cap ofs)).
    { i. des. exists (mk st_future blk_cap). splits; ss. }
    eapply dependent_functional_choice. i. apply Cell.cap_exists.
  Qed.

End Block.
#[export] Hint Unfold Block.get: core.
#[export] Hint Resolve Block.state_t_le_PreOrder: core.

Module Memory.
  Structure t :=
    mk {
        blocks (tid: option Tid.t) (bid: Bid.t): Block.t;
        next_bid (tid: Tid.t): Bid.t
      }.

  Definition valid (loc:Loc.t) (mem:t): bool :=
    Block.valid (Loc.ofs loc) (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Definition accessible (loc:Loc.t) (mem:t): bool :=
    Block.accessible (Loc.ofs loc) (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Definition is_prealloced (loc:Loc.t) (mem:t): bool :=
    Block.is_prealloced (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Definition is_freeable (loc:Loc.t) (mem:t): bool :=
    Block.is_freeable (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Definition is_freed (loc:Loc.t) (mem:t): bool :=
    Block.is_freed (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Definition get_state (loc: Loc.t) (mem: t): Block.state_t :=
    Block.state (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Definition get (loc:Loc.t) (ts:Time.t) (mem:t): option (Time.t * Message.t) :=
    Block.get (Loc.ofs loc) ts (blocks mem (Loc.tid loc) (Loc.bid loc)).

  (* ADDITIONAL *)
  Definition get_cell (loc : Loc.t) (mem : t) : Cell.t :=
    Block.contents (blocks mem (Loc.tid loc) (Loc.bid loc)) (Loc.ofs loc).

  Definition read (loc:Loc.t) (ts:Time.t) (mem:t): option (Time.t * Message.t) :=
    if accessible loc mem
    then get loc ts mem
    else None.

  Definition get_size (loc:Loc.t) (mem:t): option Z :=
    Block.get_size (blocks mem (Loc.tid loc) (Loc.bid loc)).

  Lemma accessible_get_size loc mem
        (ACCESSIBLE: accessible loc mem):
    exists size, get_size loc mem = Some size /\ (0 <= Loc.ofs loc < size)%Z.
  Proof.
    unfold accessible, Block.accessible, get_size, Block.get_size in *.
    des_ifs; esplits; eauto; inv H; inv ACCESSIBLE; nia.
  Qed.

  Lemma prealloced_is_not_accessible loc mem
        (PREALLOC: is_prealloced loc mem)
        (ACCESSIBLE: accessible loc mem) : False.
  Proof.
    unfold is_prealloced, accessible, Block.is_prealloced, Block.accessible in *.
    destruct (Block.state (blocks mem (Loc.tid loc) (Loc.bid loc))); ss.
  Qed.

  Lemma prealloced_is_not_freeable loc mem
        (PREALLOC: is_prealloced loc mem)
        (FREEABLE: is_freeable loc mem) : False.
  Proof.
    unfold is_prealloced, is_freeable, Block.is_prealloced, Block.is_freeable in *.
    destruct (Block.state (blocks mem (Loc.tid loc) (Loc.bid loc))); ss.
  Qed.

  Lemma prealloced_is_not_freed loc mem
        (PREALLOC: is_prealloced loc mem)
        (FREED: is_freed loc mem) : False.
  Proof.
    unfold is_prealloced, is_freed, Block.is_prealloced, Block.is_freed in *.
    destruct (Block.state (blocks mem (Loc.tid loc) (Loc.bid loc))); ss.
  Qed.

  Lemma ext
        lhs rhs
        (STATES: forall loc, get_state loc lhs = get_state loc rhs)
        (EXT: forall loc ts, get loc ts lhs = get loc ts rhs)
        (NEXT: next_bid lhs = next_bid rhs):
    lhs = rhs.
  Proof.
    destruct lhs, rhs. ss. subst. f_equal.
    extensionality tid.
    extensionality bid.
    eapply Block.ext; i.
    - specialize (STATES (Loc.mk tid bid 0)). ss.
    - specialize (EXT (Loc.mk tid bid ofs)).
      unfold get in *. ss.
  Qed.

  Lemma ext_contents
        lhs rhs
        (EXT: forall loc ts, get loc ts lhs = get loc ts rhs):
    forall tid bid, Block.contents (blocks lhs tid bid) = Block.contents (blocks rhs tid bid).
  Proof.
    i. eapply Block.ext_contents; i.
    specialize (EXT (Loc.mk tid bid ofs)). unfold get in *. ss.
  Qed.
    
  Lemma get_ts
        loc to mem from msg
        (GET: get loc to mem = Some (from, msg)):
    Time.lt from to.
  Proof.
    unfold get in *.
    destruct loc; unfold Block.get in GET; des_ifs; eapply Cell.get_ts; eauto.
  Qed.

  Lemma get_ts_bot
        loc to mem from msg
        (GET: get loc to mem = Some (from, msg)):
    to <> Time.bot.
  Proof.
    exploit get_ts; eauto. ii. timetac.
  Qed.

  Lemma get_disjoint
        l f1 f2 t1 t2 msg1 msg2 m
        (GET1: get l t1 m = Some (f1, msg1))
        (GET2: get l t2 m = Some (f2, msg2)):
    (t1 = t2 /\ f1 = f2 /\ msg1 = msg2) \/
    Interval.disjoint (f1, t1) (f2, t2).
  Proof.
    destruct m. destruct l; ss; unfold Block.get in *; des_ifs; eapply Cell.get_disjoint; eauto.
  Qed.

  Lemma lt_get
        loc mem
        to1 from1 msg1
        to2 from2 msg2
        (LT: Time.lt to1 to2)
        (GET1: get loc to1 mem = Some (from1, msg1))
        (GET2: get loc to2 mem = Some (from2, msg2)):
    Time.le to1 from2.
  Proof.
    exploit get_ts; try exact GET1. i. des; timetac.
    destruct (TimeFacts.le_lt_dec to1 from2); ss.
    exploit get_disjoint; [exact GET1|exact GET2|]. i. des; timetac.
    exfalso. apply (x1 to1); econs; ss; try refl.
    econs. ss.
  Qed.

  Lemma lt_from_get
        loc mem
        to1 from1 msg1
        to2 from2 msg2
        (LT: Time.lt from1 to2)
        (GET1: get loc to1 mem = Some (from1, msg1))
        (GET2: get loc to2 mem = Some (from2, msg2)):
    from1 = from2 /\ to1 = to2 /\ msg1 = msg2 \/
    Time.le to1 from2.
  Proof.
    exploit get_ts; try exact GET1. i.
    exploit get_ts; try exact GET2. i.
    destruct (TimeFacts.le_lt_dec to1 from2); auto.
    exploit get_disjoint; [exact GET1|exact GET2|]. i. des; auto.
    exfalso.
    destruct (TimeFacts.le_lt_dec to1 to2).
    - apply (x2 to1); econs; ss. refl.
    - apply (x2 to2); econs; ss; timetac. refl.
  Qed.

  Definition le (lhs rhs:t): Prop :=
    forall loc to from msg
      (LHS: get loc to lhs = Some (from, msg)),
      get loc to rhs = Some (from, msg).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. auto. Qed.
  Next Obligation. ii. eapply H0; eauto. Qed.
  
  Variant disjoint (lhs rhs:t): Prop :=
  | disjoint_intro
      (DISJOINT: forall loc to1 to2 from1 from2 msg1 msg2
                   (GET1: get loc to1 lhs = Some (from1, msg1))
                   (GET2: get loc to2 rhs = Some (from2, msg2)),
          Interval.disjoint (from1, to1) (from2, to2) /\
          (to1, to2) <> (Time.init, Time.init))
  .
  #[global] Hint Constructors disjoint: core.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    i. inv H. econs. i. exploit DISJOINT; eauto. i. des. splits.
    - symmetry. auto.
    - ii. inv H.
  Qed.

  Lemma disjoint_get
        lhs rhs
        loc froml fromr to msgl msgr
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc to lhs = Some (froml, msgl))
        (RMSG: get loc to rhs = Some (fromr, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. intros x. des.
    destruct (Time.eq_dec to (Time.init)).
    - subst. ss.
    - eapply x.
      + apply Interval.mem_ub.
        eapply get_ts; eauto.
      + apply Interval.mem_ub.
        eapply get_ts; eauto.
  Qed.

  Lemma disjoint_get_general
        lhs rhs
        loc ts0 ts1 ts2 ts3 msgl msgr
        (TS12: Time.lt ts1 ts2)
        (TS23: Time.le ts2 ts3)
        (DISJOINT: disjoint lhs rhs)
        (LMSG: get loc ts2 lhs = Some (ts0, msgl))
        (RMSG: get loc ts3 rhs = Some (ts1, msgr)):
    False.
  Proof.
    inv DISJOINT. exploit DISJOINT0; eauto. intros x. des.
    destruct (Time.le_lt_dec ts2 ts0).
    - exploit get_ts; try exact LMSG. i. timetac.
    - eapply x.
      + eapply Interval.mem_ub. auto.
      + econs; auto.
  Qed.

  Definition reserve_only (rsv: t): Prop :=
    forall loc from to msg
      (GET: get loc to rsv = Some (from, msg)),
      msg = Message.reserve.

  Definition bot: t := mk (fun _ _ => Block.bot) (fun _ => 0).

  Lemma bot_get loc ts: get loc ts bot = None.
  Proof.
    unfold get. destruct loc; ss. apply Cell.bot_get.
  Qed.

  Lemma bot_le mem: le bot mem.
  Proof.
    ii. rewrite bot_get in LHS. congruence.
  Qed.

  Lemma bot_disjoint mem: disjoint bot mem.
  Proof.
    econs. i. rewrite bot_get in GET1. inv GET1.
  Qed.

  Lemma bot_reserve_only: reserve_only bot.
  Proof.
    ii. rewrite bot_get in GET. ss.
  Qed.

  Definition init (size: list Z): t :=
    mk (fun tid bid =>
          if tid
          then Block.init_dynamic
          else Block.init_static (List.nth bid size 0%Z))
       (fun _ => 0).

  Lemma init_get
        size loc from to msg
        (GET: get loc to (Memory.init size) = Some (from, msg)):
    to = Time.init /\ from = Time.bot /\ (msg = Message.elt 0%Z \/ msg = Message.elt Val.Vundef).
  Proof.
    unfold get, init, Block.get, Block.init_dynamic, Block.init_static, Cell.get, Cell.init in GET.
    ss. des_ifs; apply DOMap.singleton_find_inv in GET; des; inv GET0; auto.
  Qed.

  Lemma le_reserve_only
        rsv1 rsv2
        (LE: le rsv1 rsv2)
        (ONLY: reserve_only rsv2):
    reserve_only rsv1.
  Proof.
    ii. eapply ONLY. eauto.
  Qed.

  Variant message_to: forall (msg:Message.t) (loc:Loc.t) (to:Time.t), Prop :=
    | message_to_message
        val released na loc to
        (TS: Time.le ((View.rlx released) loc) to):
      message_to (Message.message val released na) loc to
    | message_to_reserve
      loc to:
      message_to Message.reserve loc to
  .
  #[global] Hint Constructors message_to: core.

  Variant closed_view (view:View.t) (mem:t): Prop :=
  | closed_view_intro
      (RLX: forall loc,
          (View.rlx view) loc = Time.bot \/
            exists from val released na,
              get loc ((View.rlx view) loc) mem = Some (from, Message.message val released na))
      (ACCESSIBLE: forall loc, accessible loc mem ->
                          (View.alloc_view view) (Loc.get_tbid loc) ->
                          Time.le Time.init ((View.rlx view) loc))
      (ALLOC_VIEW: forall loc, (View.alloc_view view) (Loc.get_tbid loc) -> ~ is_prealloced loc mem)
      (UNALLOCED: forall loc, is_prealloced loc mem -> (View.rlx view) loc = Time.bot).
  #[global] Hint Constructors closed_view: core.

  Variant closed_message: forall (msg:Message.t) (mem:t), Prop :=
    | closed_message_message
        val released na mem
        (CLOSED: closed_view released mem):
      closed_message (Message.message val released na) mem
    | closed_message_reserve
        mem:
      closed_message Message.reserve mem
  .
  #[global] Hint Constructors closed_message: core.

  Definition inhabited (mem:t): Prop :=
    forall loc, let val := (match Loc.tid loc with
                       | Some _ => Val.Vundef
                       | None => Val.Vnum 0%Z
                       end) in
           get loc Time.init mem = Some (Time.bot, Message.elt val).
  #[global] Hint Unfold inhabited: core.

  Variant closed (mem:t): Prop :=
  | closed_intro
      (CLOSED: forall loc from to msg
                 (MSG: get loc to mem = Some (from, msg)),
          <<MSG_TS: message_to msg loc to>> /\
          <<MSG_CLOSED: closed_message msg mem>>)
      (INHABITED: inhabited mem).
  #[global] Hint Constructors closed: core.

  Lemma closed_view_bot
        mem:
    closed_view View.bot mem.
  Proof. econs; eauto; ss. Qed.

  Lemma closed_view_init size:
    closed_view (View.init size) (init size).
  Proof.
    econs; i.
    - unfold View.init. destruct loc. destruct tid; s; eauto.
      destruct (List.nth_error size bid) eqn:GET; eauto. condtac; eauto. right.
      unfold get, Block.get. ss.
      rewrite Cell.init_get. condtac; ss. esplits; ss.
    - destruct loc. destruct tid; s.
      { unfold accessible in H. ss. }
      unfold accessible, Block.accessible in *. ss. unfold AllocView.init in *. ss.
      destruct (bid <? length size) eqn:BID; ss. eapply Bid.ltb_lt in BID.
      destruct (List.nth_error size bid) eqn:GET.
      + condtac; try refl.
        eapply List.nth_error_nth in GET. rewrite GET in H. congruence.
        Unshelve. exact 0.
      + eapply List.nth_error_Some in BID. congruence.
    - destruct loc. destruct tid; ss.
    - destruct loc. destruct tid; ss.
  Qed.

  (* Lemma le_closed_view *)
  (*       view mem1 mem2 *)
  (*       (LE: le mem1 mem2) *)
  (*       (CLOSED: closed_view view mem1): *)
  (*   closed_view view mem2. *)
  (* Proof. *)
  (*   inv CLOSED. econs; i. *)
  (*   - specialize (RLX loc). des; eauto. *)
  (*     right. esplits; eauto. *)
  (*   - specialize (ALLOC_VIEW loc). ii. eapply ALLOC_VIEW; eauto. *)
  (*     unfold is_prealloced. *)
  (* Qed. *)

  (* Lemma le_closed_message *)
  (*       msg mem1 mem2 *)
  (*       (LE: le mem1 mem2) *)
  (*       (CLOSED: closed_message msg mem1): *)
  (*   closed_message msg mem2. *)
  (* Proof. *)
  (*   inv CLOSED; econs. *)
  (*   eapply le_closed_view; eauto. *)
  (* Qed. *)

  Lemma init_closed size: closed (init size).
  Proof.
    econs; i; ss.
    - revert MSG.
      unfold get, init, Block.get. ss.
      destruct loc. destruct tid; ss.
      + rewrite Cell.init_get. condtac; ss. i. inv MSG.
        splits; econs; try apply Time.bot_spec. eapply closed_view_bot.
      + rewrite Cell.init_get. condtac; ss. i. inv MSG.
        splits; econs; try apply Time.bot_spec. eapply closed_view_bot.
    - ii. unfold get, init, Block.get. ss.
      destruct loc. destruct tid; ss.
  Qed.

  Variant well_alloced (mem:t): Prop :=
  | well_alloced_intro
      (PREALLOC: forall tid bid (BID: next_bid mem tid <= bid),
                 Block.is_prealloced (blocks mem (Some tid) bid))
      (ALLOC: forall tid bid (BID: bid < next_bid mem tid),
                ~ Block.is_prealloced (blocks mem (Some tid) bid))
      (SIZE: forall loc size, Some size = get_size loc mem -> (0 <= size)%Z)
      (GLOBAL: forall bid, exists size, Block.state (blocks mem None bid) = Block.global size).
  #[global] Hint Constructors closed: core.

  Lemma init_well_alloced size
    (SIZE: List.Forall (fun sz => 0 <= sz)%Z size):
    well_alloced (init size).
  Proof.
    econs; i; ss; try nia.
    unfold get_size, Block.get_size, init in H. ss. des_ifs. ss. clarify.
    destruct (le_lt_dec (length size) (Loc.bid loc)).
    - exploit List.nth_overflow; eauto. i. rewrite x0. ss.
    - eapply List.Forall_nth; eauto.
    - esplits; eauto.
      Unshelve. exact 0.
  Qed.

  Lemma well_alloced_trans
        mem1 mem2
        (GET_STATE : forall loc, get_state loc mem2 = get_state loc mem1)
        (NEXT_BID : next_bid mem2 = next_bid mem1)
        (WELL_ALLOC: well_alloced mem1):
    well_alloced mem2.
  Proof.
    econs.
    - rewrite NEXT_BID; unfold Block.is_prealloced, get_state in *; i;
      specialize (GET_STATE (Loc.mk (Some tid) bid 0)); ss; rewrite GET_STATE;
      eapply WELL_ALLOC; eauto.
    - rewrite NEXT_BID; unfold Block.is_prealloced, get_state in *; i;
      specialize (GET_STATE (Loc.mk (Some tid) bid 0)); ss; rewrite GET_STATE;
      eapply WELL_ALLOC; eauto.
    - i. eapply WELL_ALLOC. unfold get_size, Block.get_size, get_state in *.
      rewrite <- GET_STATE. eauto.
    - i. unfold get_state in *. specialize (GET_STATE (Loc.mk None bid 0)); ss.
      rewrite GET_STATE. eapply WELL_ALLOC.
  Qed.
    
  Variant add (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
    | add_intro
        blk2
        (ADD: Block.add (blocks mem1 (Loc.tid loc) (Loc.bid loc)) (Loc.ofs loc) from to msg blk2)
        (MEM2: mem2 = mk (fun t b =>
                            if Loc.id_eq_dec (t, b) (Loc.get_tbid loc)
                            then blk2
                            else blocks mem1 t b)
                         (next_bid mem1))
  .
  #[global] Hint Constructors add: core.

  Variant remove (mem1:t) (loc:Loc.t) (from to:Time.t) (msg:Message.t) (mem2:t): Prop :=
    | remove_intro
        blk2
        (REMOVE: Block.remove (blocks mem1 (Loc.tid loc) (Loc.bid loc)) (Loc.ofs loc) from to msg blk2)
        (MEM2: mem2 = mk (fun t b =>
                            if Loc.id_eq_dec (t, b) (Loc.get_tbid loc)
                            then blk2
                            else blocks mem1 t b)
                         (next_bid mem1))
  .
  #[global] Hint Constructors add: core.

  Variant alloc (mem1:t) (tid: Tid.t) (size:Z) (mem2:t): forall (loc:Loc.t), Prop :=
    | alloc_heap_intro
        bid
        (BID: bid = (next_bid mem1) tid)
        (SIZE: (0 <= size)%Z)
        (MEM2: mem2 = mk (fun t b =>
                            if Loc.id_eq_dec (t, b) (Some tid, bid)
                            then Block.alloc size (blocks mem1 (Some tid) bid)
                            else blocks mem1 t b)
                         (fun t =>
                            if Tid.eq_dec t tid
                            then S (next_bid mem1 tid)
                            else next_bid mem1 t)):
      alloc mem1 tid size mem2 (Loc.mk (Some tid) bid 0%Z)
  .
  #[global] Hint Constructors alloc: core.

  Variant free (mem1:t) (loc:Loc.t) (mem2:t): Prop :=
    | free_intro
        tid bid
        (LOC: loc = Loc.mk (Some tid) bid 0)
        (FREEABLE: is_freeable loc mem1)
        (MEM2: mem2 = mk (fun t b =>
                            if Loc.id_eq_dec (t, b) (Some tid, bid)
                            then Block.free (blocks mem1 (Some tid) bid)
                            else blocks mem1 t b)
                         (next_bid mem1))
  .
  #[global] Hint Constructors free: core.

  Variant reserve (rsv1 mem1: t) (loc: Loc.t) (from to: Time.t) (rsv2 mem2: t): Prop :=
    | reserve_intro
        (RSV: add rsv1 loc from to Message.reserve rsv2)
        (MEM: add mem1 loc from to Message.reserve mem2)
  .
  #[global] Hint Constructors reserve: core.

  Variant cancel (rsv1 mem1: t) (loc: Loc.t) (from to: Time.t) (rsv2 mem2: t): Prop :=
    | cancel_intro
        (RSV: remove rsv1 loc from to Message.reserve rsv2)
        (MEM: remove mem1 loc from to Message.reserve mem2)
  .
  #[global] Hint Constructors cancel: core.

  Variant messages_le (lhs rhs: t): Prop :=
  | messages_le_intro
      (GET: forall loc to from val released na
              (LHS: get loc to lhs = Some (from, Message.message val released na)),
          get loc to rhs = Some (from, Message.message val released na))
      (STATES: forall loc, Block.state_t_le (get_state loc lhs) (get_state loc rhs))
      (BID: forall tid, next_bid lhs tid <= next_bid rhs tid)
  .
  #[global] Hint Constructors messages_le: core.

  Global Program Instance messages_le_PreOrder: PreOrder messages_le.
  Next Obligation. ii. econs; eauto; try refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; i; etrans; eauto. Qed.

  Variant future (mem1 mem2:t): Prop :=
  | future_intro
    (MESSAGE_LE: messages_le mem1 mem2)
    (CLOSED: closed mem2)
    (WELL_ALLOCED: well_alloced mem2)
  .
  #[global] Hint Constructors future: core.

  (* Lemmas on add *)

  Lemma add_ts
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2):
    Time.lt from to.
  Proof.
    inv ADD. inv ADD0. inv ADD. ss.
  Qed.

  Lemma add_get_cell loc' mem1 loc from to msg mem2
      (ADD: add mem1 loc from to msg mem2) :
    ∃ C',
      (get_cell loc' mem2 = if (Loc.eq_dec loc loc') then C' else get_cell loc' mem1) ∧ 
      Cell.add (get_cell loc mem1) from to msg C'.
  Proof.
    inv ADD. inv ADD0. rewrite /get_cell /=. exists r.
    split; ss.
    destruct loc', loc; des_ifs; ss; des; clarify. des_ifs; ss. des_ifs; ss.
  Qed.

  Lemma add_o
        mem2 mem1 loc from to msg
        l t
        (ADD: add mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then Some (from, msg)
    else get l t mem1.
  Proof.
    unfold get. inv ADD. destruct l, loc. ss.
    condtac; ss.
    - des. subst.
      erewrite Block.add_o; eauto. condtac; ss.
      + des. subst. condtac; ss. des; ss.
      + condtac; ss. des; subst; ss. congruence.
    - condtac; ss. des; subst; congruence.
  Qed.

  Lemma add_get0
        mem1 loc from1 to1 msg1 mem2
        (ADD: add mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = None>> /\
    <<GET: get loc to1 mem2 = Some (from1, msg1)>>.
  Proof.
    unfold get, Block.get.
    inv ADD. inv ADD0. ss.
    repeat (condtac; ss; try by (des; congruence)).
    exploit Cell.add_get0; eauto.
  Qed.

  Lemma add_get1
        m1 loc from to msg m2
        l f t m
        (ADD: add m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    get l t m2 = Some (f, m).
  Proof.
    erewrite add_o; eauto. condtac; ss.
    des. subst. exploit add_get0; eauto. i. des. congruence.
  Qed.

  Lemma add_get_diff
        mem1 loc from to msg mem2
        loc'
        (ADD: add mem1 loc from to msg mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite add_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma add_inj
        mem loc from to msg mem1 mem2
        (ADD1: add mem loc from to msg mem1)
        (ADD2: add mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply ext; i.
    - unfold get_state.
      inv ADD1. inv ADD. inv ADD2. inv ADD. ss.
      repeat (condtac; ss); des; subst; ss.
    - erewrite add_o; eauto.
      erewrite (@add_o mem2); eauto.
    - inv ADD1. inv ADD2. ss.
  Qed.

  Lemma add_inhabited
        mem1 mem2 loc from to msg
        (ADD: add mem1 loc from to msg mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite add_o; eauto. condtac; eauto. ss.
    des. subst. specialize (INHABITED loc). des. exfalso.
    inv ADD. inv ADD0. inv ADD. eapply DISJOINT.
    - unfold get, Block.get, Cell.get in INHABITED. eapply INHABITED.
    - eapply Interval.mem_ub; ss.
    - eapply Interval.mem_ub; ss. eapply Time.init_spec.
  Qed.

  Lemma add_le
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2):
    le mem1 mem2.
  Proof.
    ii. eapply add_get1; eauto.
  Qed.
  
  Lemma add_reserve_only
        mem1 loc from to mem2
        (ADD: add mem1 loc from to Message.reserve mem2)
        (ONLY1: reserve_only mem1):
    reserve_only mem2.
  Proof.
    ii. revert GET.
    erewrite add_o; eauto. condtac; ss; eauto.
    i. des. inv GET. ss.
  Qed.

  Lemma add_preserve
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2):
    <<GET_STATE: forall l, get_state l mem2 = get_state l mem1>> /\
    <<NEXTBID: next_bid mem2 = next_bid mem1>>.
  Proof.
    inv ADD. inv ADD0. split; ss. ii. unfold get_state. ss.
    repeat (condtac; ss; try by (des; congruence)).
  Qed.

  Lemma add_accessible
        mem1 mem2 loc from to msg
        l
        (ADD: add mem1 loc from to msg mem2):
    accessible l mem2 = accessible l mem1.
  Proof.
    inv ADD. unfold accessible in *. inv ADD0. destruct loc. ss. condtac; ss. des. subst.
    unfold Block.accessible in *. inv ADD. ss.
  Qed.

  Lemma add_get_size
        mem1 mem2 loc from to msg
        l
        (ADD: add mem1 loc from to msg mem2):
    get_size l mem2 = get_size l mem1.
  Proof.
    inv ADD. unfold get_size in *. inv ADD0. destruct loc. ss. condtac; ss. des. subst.
    unfold Block.get_size in *. inv ADD. ss.
  Qed.

  (* lemmas on remove *)

  Lemma remove_o
        mem2 mem1 loc from to msg
        l t
        (REMOVE: remove mem1 loc from to msg mem2):
    get l t mem2 =
    if loc_ts_eq_dec (l, t) (loc, to)
    then None
    else get l t mem1.
  Proof.
    unfold get. inv REMOVE. destruct l, loc. ss.
    condtac; ss.
    - des. subst.
      erewrite Block.remove_o; eauto. condtac; ss.
      + des. subst. condtac; ss. des; ss.
      + condtac; ss. des; subst; ss. congruence.
    - condtac; ss. des; subst; congruence.
  Qed.

  Lemma remove_get0
        mem1 loc from1 to1 msg1 mem2
        (REMOVE: remove mem1 loc from1 to1 msg1 mem2):
    <<GET: get loc to1 mem1 = Some (from1, msg1)>> /\
    <<GET: get loc to1 mem2 = None>>.
  Proof.
    unfold get, Block.get.
    inv REMOVE. inv REMOVE0. ss.
    repeat (condtac; ss; try by (des; congruence)).
    exploit Cell.remove_get0; eauto.
  Qed.

  Lemma remove_get1
        m1 loc from to msg m2
        l f t m
        (REMOVE: remove m1 loc from to msg m2)
        (GET1: get l t m1 = Some (f, m)):
    l = loc /\ f = from /\ t = to /\ m = msg \/
    get l t m2 = Some (f, m).
  Proof.
    erewrite remove_o; eauto. condtac; ss; eauto.
    des. subst. exploit remove_get0; eauto. i. des.
    rewrite GET in GET1. inv GET1. eauto.
  Qed.

  Lemma remove_get_diff
        mem1 loc from to msg mem2
        loc'
        (REMOVE: remove mem1 loc from to msg mem2)
        (LOC: loc' <> loc):
    forall to', get loc' to' mem2 = get loc' to' mem1.
  Proof.
    i. erewrite remove_o; eauto. condtac; ss. des. ss.
  Qed.

  Lemma remove_ts
        mem1 mem2 loc from to msg
        (REMOVE: remove mem1 loc from to msg mem2):
    Time.lt from to.
  Proof.
    exploit remove_get0; eauto. i. des.
    exploit get_ts; eauto.
  Qed.

  Lemma remove_inj
        mem loc from to msg mem1 mem2
        (REMOVE1: remove mem loc from to msg mem1)
        (REMOVE2: remove mem loc from to msg mem2):
    mem1 = mem2.
  Proof.
    apply ext; i.
    - unfold get_state.
      inv REMOVE1. inv REMOVE. inv REMOVE2. inv REMOVE. ss.
      repeat (condtac; ss); des; subst; ss.
    - erewrite remove_o; eauto.
      erewrite (@remove_o mem2); eauto.
    - inv REMOVE1. inv REMOVE2. ss.
  Qed.

  Lemma remove_inhabited
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite remove_o; eauto. condtac; eauto. ss.
    des. subst. exploit remove_get0; eauto. i. des.
    specialize (INHABITED loc). des.
    rewrite INHABITED in GET. ss.
  Qed.

  Lemma remove_le
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2):
    le mem2 mem1.
  Proof.
    ii. revert LHS.
    erewrite remove_o; eauto. condtac; ss.
  Qed.

  Lemma remove_reserve_only
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (ONLY1: reserve_only mem1):
    reserve_only mem2.
  Proof.
    ii. revert GET.
    erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.

  Lemma remove_preserve
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2):
    <<GET_STATE: forall l, get_state l mem2 = get_state l mem1>> /\
    <<NEXTBID: next_bid mem2 = next_bid mem1>>.
  Proof.
    inv REMOVE. inv REMOVE0. split; ss. ii. unfold get_state. ss.
    repeat (condtac; ss; try by (des; congruence)).
  Qed.

  Lemma alloc_o
        m1 tid size loc m2
        l t
        (ALLOC: alloc m1 tid size m2 loc):
    get l t m2 = get l t m1.
  Proof.
    unfold get. destruct l. inv ALLOC. ss.
    condtac; ss. des. subst. unfold Block.alloc. ss.
  Qed.

  (* ADDITIONAL *)
  Lemma alloc_get_cell 
        m1 tid size loc m2
        (ALLOC : alloc m1 tid size m2 loc) :
    ∀ l, get_cell l m2 = get_cell l m1.
  Proof. intros l; apply Cell.ext; intros ts. hexploit alloc_o; eauto. Qed.

  Lemma alloc_is_freeable
        m1 tid size loc m2
        (WF : well_alloced m1)
        (ALLOC : alloc m1 tid size m2 loc) :
    ∀ (l : Loc.t),
      Loc.get_tbid l = Loc.get_tbid loc ∧ ¬ is_freeable l m1 ∧ is_freeable l m2
      ∨ Loc.get_tbid l ≠ Loc.get_tbid loc ∧ is_freeable l m1 = is_freeable l m2.
  Proof.
    intros l; destruct (decide (Loc.get_tbid l = Loc.get_tbid loc)); [left | right]; split; ss.
    { inv ALLOC; destruct l; ss; clarify. split.
      { inv WF; hexploit (PREALLOC tid (next_bid m1 tid)); ss.
        rewrite /is_freeable /Block.is_freeable /Block.is_prealloced.
        des_ifs; ss; rewrite Heq in Heq0; clarify.
      }
      rewrite /is_freeable; ss; des_ifs; ss; des; clarify.
    }
    inv ALLOC. rewrite /is_freeable; ss; des_ifs; ss; des.
    destruct l; ss; clarify.
  Qed.

  Lemma alloc_get_state mem1 tid sz mem2 loc
      (WF : Memory.well_alloced mem1)
      (WRITE : Memory.alloc mem1 tid sz mem2 loc) :
    ∀ loc',
      Loc.get_tbid loc = Loc.get_tbid loc'
        ∧ Memory.get_state loc' mem1 = Block.prealloced
        ∧ Memory.get_state loc' mem2 = Block.heap sz
      ∨ Loc.get_tbid loc ≠ Loc.get_tbid loc'
        ∧ Memory.get_state loc' mem1 = Memory.get_state loc' mem2.
  Proof.
    intros loc'; destruct (decide (Loc.get_tbid loc = Loc.get_tbid loc')); [left | right]; split; ss.
    { inv WRITE; rewrite /Memory.get_state /=; des_ifs; destruct loc'; ss; des; clarify; split; ss.
      inv WF; hexploit (PREALLOC tid (Memory.next_bid mem1 tid)); eauto.
      rewrite /Block.is_prealloced; des_ifs.
    }
    inv WRITE; rewrite /Memory.get_state /=; des_ifs.
    destruct loc'; ss; des; clarify.
  Qed.

  Lemma alloc_get_size mem1 tid sz mem2 loc
      (WF : Memory.well_alloced mem1)
      (ALLOC : Memory.alloc mem1 tid sz mem2 loc) :
    ∀ loc',
      Loc.get_tbid loc = Loc.get_tbid loc'
        ∧ Memory.get_size loc' mem1 = None
        ∧ Memory.get_size loc' mem2 = Some sz
      ∨ Loc.get_tbid loc ≠ Loc.get_tbid loc'
        ∧ Memory.get_size loc' mem1 = Memory.get_size loc' mem2.
  Proof.
    intros loc'; destruct (decide (Loc.get_tbid loc = Loc.get_tbid loc')); [left | right]; split; ss.
    { inv ALLOC; rewrite /Memory.get_size /=; des_ifs; destruct loc'; ss; des; clarify; split; ss.
      inv WF; hexploit (PREALLOC tid (Memory.next_bid mem1 tid)); eauto.
      rewrite /Block.is_prealloced /Block.get_size; des_ifs.
    }
    inv ALLOC; rewrite /Memory.get_size /=; des_ifs.
    destruct loc'; ss; des; clarify.
  Qed.
  
  Lemma alloc_inhabited
        mem1 tid size loc mem2
        (ALLOC: alloc mem1 tid size mem2 loc)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite alloc_o; eauto.
  Qed.

  Lemma alloc_le
    mem1 tid size loc mem2
    (ALLOC: alloc mem1 tid size mem2 loc):
    le mem1 mem2.
  Proof.
    ii. erewrite alloc_o; eauto.
  Qed.

  Lemma alloc_accessible
        mem1 tid size loc mem2 l
        (ALLOC: alloc mem1 tid size mem2 loc)
        (ACCESSIBLE: accessible l mem1)
        (WELL_ALLOCED: well_alloced mem1):
    accessible l mem2.
  Proof.
    inv ALLOC. unfold accessible, Block.accessible in *. ss. condtac; ss. des.
    inv WELL_ALLOCED. exploit (PREALLOC tid); try refl. i.
    rewrite a in ACCESSIBLE. rewrite a0 in ACCESSIBLE.
    unfold Block.is_prealloced in x0. des_ifs.
  Qed.

  Lemma alloc_accessible1
        mem1 tid size loc mem2 loc'
        (ALLOC: alloc mem1 tid size mem2 loc)
        (LOC: Loc.get_tbid loc' = Loc.get_tbid loc /\ (0 <= Loc.ofs loc' < size)%Z):
    accessible loc' mem2.
  Proof.
    unfold Loc.get_tbid in *. destruct loc, loc'. ss. des. inv LOC.
    inv ALLOC. unfold accessible, Block.accessible in *. ss. condtac; des; ss; try congruence.
    eapply andb_true_intro. split; nia.
  Qed.

  Lemma alloc_accessible2
        mem1 tid size loc mem2 loc'
        (ALLOC: alloc mem1 tid size mem2 loc)
        (ACCESSIBLE: accessible loc' mem2):
    (<<LOC: Loc.get_tbid loc' = Loc.get_tbid loc /\ (0 <= Loc.ofs loc' < size)%Z>>) \/
    (<<ACCESSIBLE: accessible loc' mem1>>) /\ (<<LOC: Loc.get_tbid loc' <> Loc.get_tbid loc>>).
  Proof.
    unfold Loc.get_tbid. destruct loc, loc'. ss. inv ALLOC. revert ACCESSIBLE.
    unfold accessible, Block.accessible. ss. condtac; eauto.
    - left. des. ss. subst. split; eauto. eapply andb_prop in ACCESSIBLE. des. nia.
    - right. ss. split; eauto. ii. inv H. des; congruence.
  Qed.

  (* ADDITIONAL *)
  Lemma alloc_accessible3
        mem1 tid size loc mem2 loc'
        (ALLOC: alloc mem1 tid size mem2 loc)
        (ACCESSIBLE: accessible loc' mem2)
        (WELL_ALLOCED: well_alloced mem1) :
    (<<LOC: Loc.get_tbid loc' = Loc.get_tbid loc /\ (0 <= Loc.ofs loc' < size)%Z /\ is_prealloced loc' mem1>>) \/
    (<<ACCESSIBLE: accessible loc' mem1>>) /\ (<<LOC: Loc.get_tbid loc' <> Loc.get_tbid loc>>).
  Proof.
    unfold Loc.get_tbid. destruct loc, loc'. ss. inv ALLOC. revert ACCESSIBLE.
    unfold accessible, Block.accessible. ss. condtac; eauto.
    - left. des. ss. subst. split; eauto. eapply andb_prop in ACCESSIBLE. des. split; first nia.
      inv WELL_ALLOCED. hexploit (PREALLOC tid (next_bid mem1 tid)); ss.
    - right. ss. split; eauto. ii. inv H. des; congruence.
  Qed.

  Lemma free_o
        m1 loc m2
        l t
        (FREE: free m1 loc m2):
    get l t m2 = get l t m1.
  Proof.
    unfold get. destruct l. inv FREE. ss.
    condtac; ss. des. subst. unfold Block.free. ss.
  Qed.

  Lemma free_inhabited
        mem1 loc mem2
        (FREE: free mem1 loc mem2)
        (INHABITED: inhabited mem1):
    <<INHABITED: inhabited mem2>>.
  Proof.
    ii. erewrite free_o; eauto.
  Qed.

  Lemma free_le
    mem1 loc mem2
    (FREE: free mem1 loc mem2):
    le mem1 mem2.
  Proof.
    ii. erewrite free_o; eauto.
  Qed.

  Lemma free_is_freeable
        m1 loc m2
        (WF : well_alloced m1)
        (FREE : free m1 loc m2) :
    ∀ (l : Loc.t),
      Loc.get_tbid l = Loc.get_tbid loc ∧ is_freeable l m1 ∧ ¬ is_freeable l m2
      ∨ Loc.get_tbid l ≠ Loc.get_tbid loc ∧ is_freeable l m1 = is_freeable l m2.
  Proof.
    intros l; destruct (decide (Loc.get_tbid l = Loc.get_tbid loc)); [left | right]; split; ss.
    { inv FREE; destruct l; ss; clarify. split.
      { inv WF; hexploit (PREALLOC tid (next_bid m1 tid)); ss. }
      rewrite /is_freeable; ss; des_ifs; ss; des; clarify.
    }
    inv FREE. rewrite /is_freeable; ss; des_ifs; ss; des.
    destruct l; ss; clarify.
  Qed.


  (* lemmas on future *)

  Lemma future_get1
        loc from to val released na mem1 mem2
        (FUTURE: future mem1 mem2)
        (GET: get loc to mem1 = Some (from, Message.message val released na)):
    <<GET: get loc to mem2 = Some (from, Message.message val released na)>>.
  Proof.
    eapply FUTURE; eauto.
  Qed.

  Lemma future_trans
        mem1 mem2 mem3
        (FUTURE1: future mem1 mem2)
        (FUTURE2: future mem2 mem3):
    future mem1 mem3.
  Proof.
    econs; try eapply FUTURE2.
    eapply Memory.messages_le_PreOrder; [eapply FUTURE1|eapply FUTURE2].
  Qed.

  (* Lemmas on closedness *)

  Lemma join_closed_view
        lhs rhs mem
        (LHS: closed_view lhs mem)
        (RHS: closed_view rhs mem):
    closed_view (View.join lhs rhs) mem.
  Proof.
    inv LHS. inv RHS. unfold View.join, TimeMap.join, AllocView.join. econs; i; ss.
    - specialize (RLX loc). specialize (RLX0 loc).
      destruct (Time.join_cases (View.rlx lhs loc) (View.rlx rhs loc)) as [X|X];
        rewrite X; eauto.
    - destruct (View.alloc_view lhs (Loc.get_tbid loc)) eqn: LHS;
        destruct (View.alloc_view rhs (Loc.get_tbid loc)) eqn: RHS; ss.
      + exploit ACCESSIBLE; eauto. i. etrans; eauto. eapply Time.join_l.
      + exploit ACCESSIBLE; eauto. i. etrans; eauto. eapply Time.join_l.
      + exploit ACCESSIBLE0; eauto. i. etrans; eauto. eapply Time.join_r.
    - specialize (ALLOC_VIEW loc). specialize (ALLOC_VIEW0 loc).
      eapply Bool.orb_prop in H. des; eauto.
    - rewrite UNALLOCED; eauto. rewrite UNALLOCED0; eauto.
  Qed.

  Lemma add_closed_view
        view
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; i.
    - erewrite add_o; eauto. condtac; ss.
      des. subst. specialize (RLX loc). des; eauto.
      exploit add_get0; eauto. i. des. congruence.
    - eapply ACCESSIBLE; eauto. exploit add_preserve; eauto. i. des.
      unfold get_state, accessible, Block.accessible in *. rewrite <- GET_STATE. eauto.
    - exploit add_preserve; eauto. i. des.
      unfold get_state, is_prealloced, Block.is_prealloced in *. rewrite GET_STATE. eauto.
    - exploit add_preserve; eauto. i. des.
      unfold get_state, is_prealloced, Block.is_prealloced in *.
      eapply UNALLOCED; eauto. rewrite <- GET_STATE. eauto.
  Qed.

  Lemma add_closed_message
        msg'
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply add_closed_view; eauto.
  Qed.

  Lemma add_closed
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED: closed mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    closed mem2.
  Proof.
    exploit add_preserve; eauto. i. des.
    inv CLOSED. econs. inv ADD.
    i. revert MSG. erewrite add_o; eauto. condtac; ss.
    - des. subst. i. inv MSG. splits; auto.
    - guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
      eapply add_closed_message; eauto.
    - inv ADD. eapply add_inhabited; eauto.
  Qed.

  Lemma add_well_alloced
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (WELL_ALLOCED: well_alloced mem1):
    well_alloced mem2.
  Proof.
    exploit add_preserve; eauto. i. des. unfold get_state in GET_STATE.
    inv WELL_ALLOCED. econs; i; ss.
    - specialize (GET_STATE (Loc.mk (Some tid) bid 0%Z)). ss.
      unfold Block.is_prealloced in *. rewrite GET_STATE.
      eapply PREALLOC. rewrite <- NEXTBID. eauto.
    - specialize (GET_STATE (Loc.mk (Some tid) bid 0%Z)). ss.
      unfold Block.is_prealloced in *. rewrite GET_STATE.
      eapply ALLOC. rewrite <- NEXTBID. eauto.
    - eapply SIZE. unfold get_size, Block.get_size in *. rewrite <- GET_STATE. eauto.
    - i. specialize (GET_STATE (Loc.mk None bid 0%Z)). ss. rewrite GET_STATE. eauto.
  Qed.

  Lemma remove_closed_view
        view
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; i.
    - specialize (RLX loc0). des; eauto. right.
      erewrite remove_o; eauto. condtac; eauto.
      des. ss. subst. exfalso.
      exploit remove_get0; eauto. i. des. congruence.
    - eapply ACCESSIBLE; eauto. exploit remove_preserve; eauto. i. des.
      unfold get_state, accessible, Block.accessible in *. rewrite <- GET_STATE. eauto.
    - exploit remove_preserve; eauto. i. des.
      unfold get_state, is_prealloced, Block.is_prealloced in *. rewrite GET_STATE. eauto.
    - exploit remove_preserve; eauto. i. des.
      unfold get_state, is_prealloced, Block.is_prealloced in *.
      eapply UNALLOCED; eauto. rewrite <- GET_STATE. eauto.
Qed.

  Lemma remove_closed_message
        msg'
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed_message msg' mem1):
    closed_message msg' mem2.
  Proof.
    destruct msg'; ss. inv CLOSED. econs.
    eapply remove_closed_view; eauto.
  Qed.

  Lemma remove_closed
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    exploit remove_preserve; eauto. i. des.
    inv CLOSED. econs.
    - i. revert MSG. erewrite remove_o; eauto. condtac; ss.
      guardH o. i. exploit CLOSED0; eauto. i. des. splits; auto.
      eapply remove_closed_message; eauto.
    - eapply remove_inhabited; eauto.
  Qed.

  Lemma remove_well_alloced
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2)
        (WELL_ALLOCED: well_alloced mem1):
    well_alloced mem2.
  Proof.
    exploit remove_preserve; eauto. i. des.
    inv WELL_ALLOCED. econs.
    - i. unfold Block.is_prealloced, get_state in *.
      specialize (GET_STATE (Loc.mk (Some tid) bid 0)). ss. rewrite GET_STATE.
      eapply PREALLOC. rewrite <- NEXTBID. eauto.
    - i. unfold Block.is_prealloced, get_state in *.
      specialize (GET_STATE (Loc.mk (Some tid) bid 0)). ss. rewrite GET_STATE.
      eapply ALLOC. rewrite <- NEXTBID. eauto.
    - i. eapply SIZE. unfold get_state, get_size, Block.get_size in *. rewrite <- GET_STATE. eauto.
    - i. unfold get_state in GET_STATE.
      specialize (GET_STATE (Loc.mk None bid 0%Z)). ss. rewrite GET_STATE. eauto.
Qed.

  Lemma alloc_closed_view
        view mem1 tid size loc mem2
        (ALLOC: alloc mem1 tid size mem2 loc)
        (CLOSED: closed_view view mem1)
        (WF: Memory.well_alloced mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; i.
    - specialize (RLX loc0). des; eauto. right.
      erewrite alloc_o; eauto.
    - revert H. unfold accessible, Block.accessible in *. inv ALLOC. ss. condtac; eauto; ss.
      exfalso. eapply ALLOC_VIEW; eauto. inv WF. unfold is_prealloced.
      des. rewrite a. rewrite a0. eapply PREALLOC. eauto.
    - unfold get_state, is_prealloced, Block.is_prealloced in *.
      inv ALLOC. ss. condtac; ss. eauto.
    - unfold get_state, is_prealloced, Block.is_prealloced in *.
      inv ALLOC. ss. revert H. condtac; ss. eauto.
  Qed.

  (* ADDITIONAL *)
  Lemma alloc_closed_view_bot
        view mem1 tid size loc mem2
        (ALLOC: alloc mem1 tid size mem2 loc)
        (CLOSED: closed_view view mem1)
        (WF: Memory.well_alloced mem1):
      ∀ ofs, (View.rlx view) (Loc.mk (Loc.tid loc) (Loc.bid loc) ofs) = Time.bot.
  Proof.
    inv CLOSED; inv ALLOC; s.
    intros ofs; remember (Loc.mk _ _ ofs) as loc; rewrite (UNALLOCED loc); ss.
    inv WF; apply PREALLOC; eauto.
  Qed.

  Lemma alloc_closed_message
        msg mem1 tid size loc mem2
        (ALLOC: alloc mem1 tid size mem2 loc)
        (CLOSED: closed_message msg mem1)
        (WF: Memory.well_alloced mem1):
    closed_message msg mem2.
  Proof.
    destruct msg; ss. inv CLOSED. econs.
    eapply alloc_closed_view; eauto.
  Qed.

  Lemma alloc_closed
        mem1 tid size loc mem2
        (ALLOC: alloc mem1 tid size mem2 loc)
        (CLOSED: closed mem1)
        (WF: Memory.well_alloced mem1):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite alloc_o; eauto.
      i. exploit CLOSED0; eauto. i. des. splits; auto.
      eapply alloc_closed_message; eauto.
    - eapply alloc_inhabited; eauto.
  Qed.

  Lemma alloc_well_alloced
        mem1 tid size loc mem2
        (ALLOC: alloc mem1 tid size mem2 loc)
        (WELL_ALLOCED: well_alloced mem1):
    well_alloced mem2.
  Proof.
    inv WELL_ALLOCED. econs.
    - i. inv ALLOC. ss. condtac.
      + ss. des. exfalso. inversion a. subst. rewrite Tid.eq_dec_eq in BID. nia.
      + eapply PREALLOC. ss. des.
        * rewrite Tid.eq_dec_neq in BID; eauto.  congruence.
        * destruct (Tid.eq_dec tid0 tid); subst; try nia.
    - i. inv ALLOC. ss. condtac; ss.
      eapply ALLOC0. ss. des.
      + rewrite Tid.eq_dec_neq in BID; eauto. congruence.
      + destruct (Tid.eq_dec tid0 tid); subst; try nia.
    - i. inv ALLOC. unfold get_size, Block.get_size in *. ss. revert H. condtac; try eauto.
      unfold Block.alloc. ss. i. clarify.
    - i. inv ALLOC. ss. condtac; ss. des. congruence.
Qed.

  Lemma free_closed_view
        view mem1 loc mem2
        (FREE: free mem1 loc mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; i.
    - specialize (RLX loc0). des; eauto. right.
      erewrite free_o; eauto.
    - revert H. unfold accessible, Block.accessible in *. inv FREE. ss. condtac; eauto; ss.
    - unfold get_state, is_prealloced, Block.is_prealloced in *.
      inv FREE. ss. condtac; ss. eauto.
    - unfold get_state, is_prealloced, Block.is_prealloced in *.
      inv FREE. ss. revert H. condtac; ss. eauto.
Qed.

  Lemma free_closed_message
        msg mem1 loc mem2
        (FREE: free mem1 loc mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    destruct msg; ss. inv CLOSED. econs.
    eapply free_closed_view; eauto.
  Qed.

  Lemma free_closed
        mem1 loc mem2
        (FREE: free mem1 loc mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    inv CLOSED. econs.
    - i. revert MSG. erewrite free_o; eauto.
      i. exploit CLOSED0; eauto. i. des. splits; auto.
      eapply free_closed_message; eauto.
    - eapply free_inhabited; eauto.
  Qed.

  Lemma free_well_alloced
        mem1 loc mem2
        (FREE: free mem1 loc mem2)
        (WELL_ALLOCED: well_alloced mem1):
    well_alloced mem2.
  Proof.
    inv WELL_ALLOCED. econs.
    - i. inv FREE. ss. condtac; ss.
      + des. rewrite <- a in FREEABLE. rewrite <- a0 in FREEABLE.
        exfalso. exploit PREALLOC; eauto. i.
        unfold is_freeable, Block.is_freeable, Block.is_prealloced in *. ss. des_ifs.
      + eapply PREALLOC. ss.
    - i. inv FREE. ss. condtac; ss.
      eapply ALLOC. ss.
    - i. inv FREE. unfold get_size, Block.get_size in *. ss. revert H. condtac; try eauto.
      unfold Block.free. ss.
    - i. inv FREE. ss. condtac; ss. des. congruence.
  Qed.

  Lemma future_closed_view
        view mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; i.
    - specialize (RLX loc). des; eauto. right.
      esplits. eapply FUTURE; eauto.
    - eapply ACCESSIBLE; eauto.
      inv FUTURE. inv MESSAGE_LE. specialize (STATES loc).
      unfold accessible, Block.accessible, get_state in *. r in STATES. des_ifs; ss.
      exfalso. eapply ALLOC_VIEW; eauto.
      unfold is_prealloced, Block.is_prealloced. rewrite Heq. ss.
    - inv FUTURE. inv MESSAGE_LE. unfold get_state, is_prealloced, Block.is_prealloced in *.
      specialize (ALLOC_VIEW loc). specialize (STATES loc).
      destruct (Block.state (blocks mem1 (Loc.tid loc) (Loc.bid loc)));
        destruct (Block.state (blocks mem2 (Loc.tid loc) (Loc.bid loc))); ss. eauto.
    - inv FUTURE. inv MESSAGE_LE. unfold get_state, is_prealloced, Block.is_prealloced in *.
      specialize (STATES loc). des_ifs. eapply UNALLOCED.
      destruct (Block.state (blocks mem1 (Loc.tid loc) (Loc.bid loc))); ss.
  Qed.
  
  Lemma future_closed_message
        msg mem1 mem2
        (FUTURE: future mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; eauto using future_closed_view.
  Qed.

  Lemma future_closed
        mem1 mem2
        (FUTURE: future mem1 mem2):
    closed mem2.
  Proof.
    eapply FUTURE.
  Qed.

  Lemma singleton_closed_view
        loc from to val released na mem
        (GET: get loc to mem = Some (from, Message.message val released na))
        (ALLOCED: ~ is_prealloced loc mem):
    closed_view (View.singleton loc to) mem.
  Proof.
    unfold View.singleton, TimeMap.singleton, LocFun.add, LocFun.find.
    econs; i; ss.
    destruct (Loc.eq_dec loc0 loc); ss.
    - subst. right. eauto.
    - left. eauto.
    - condtac; ss. subst. congruence.
  Qed.

  Lemma alloc_view_singleton_closed_view tid loc size mem1 mem2
        (INHABITED: inhabited mem1)
        (ALLOC: alloc mem1 tid size mem2 loc):
    closed_view (View.alloc_view_singleton loc size) mem2.
  Proof.
    econs; i; ss.
    - exploit alloc_inhabited; eauto. i. des. destruct loc, loc0.
      unfold TimeMap.singleton. ss.
      condtac; eauto. right. eauto.
    - unfold AllocView.singleton in H0. des_ifs.
      unfold TimeMap.singletons. destruct loc, loc0. ss. subst.
      inv ALLOC. unfold accessible, Block.accessible in H. ss. condtac; try refl.
      revert H. condtac; des; ss. i.
      rewrite Nat.eqb_refl in COND. rewrite Tid.eqb_refl in COND. rewrite H in COND. ss.
    - unfold AllocView.singleton in H. des_ifs.
      inv ALLOC. ss. unfold is_prealloced, Block.is_prealloced. ss. condtac; ss. des; congruence.
    - unfold TimeMap.singletons. inv ALLOC. unfold is_prealloced, Block.is_prealloced in H. ss.
      des_ifs. ss. exfalso. eapply andb_prop in Heq. desH Heq. eapply andb_prop in Heq1. des.
      + eapply Tid.eqb_eq in Heq. subst. eauto.
      + eapply Nat.eqb_eq in Heq1. subst. eauto.
  Qed.

  (* Lemma init_closed_view mem size *)
  (*       (INHABITED: inhabited mem): *)
  (*   closed_view (View.init size) mem. *)
  (* Proof. *)
  (*   econs; i; ss. specialize (INHABITED loc). des. *)
  (*   unfold View.init, TimeMap.init, AllocView.init. ss. *)
  (*   destruct loc as [[tid|] bid ofs]; eauto. *)
  (*   right. eauto. *)
  (* Qed. *)

  (* finite *)

  Definition finite (mem:t): Prop :=
    exists dom,
    forall loc from to msg (GET: get loc to mem = Some (from, msg)),
      List.In (loc, to) dom.

  Lemma bot_finite: finite bot.
  Proof.
    exists []. ii. rewrite bot_get in GET. congruence.
  Qed.

  Lemma add_finite
        mem1 loc from to msg mem2
        (WRITE: add mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists ((loc, to) :: dom). i. inv WRITE.
    revert GET. erewrite add_o; eauto. condtac; ss; eauto.
    i. des. inv GET. auto.
  Qed.

  Lemma remove_finite
        mem1 loc from to msg mem2
        (REMOVE: remove mem1 loc from to msg mem2)
        (FINITE: finite mem1):
    finite mem2.
  Proof.
    unfold finite in *. des. exists dom. i.
    revert GET. erewrite remove_o; eauto. condtac; ss; eauto.
  Qed.

  (* messages_le *)
  Lemma add_messages_le
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2):
    messages_le mem1 mem2.
  Proof.
    econs; i.
    - eapply add_get1; eauto.
    - inv ADD. unfold get_state. ss. condtac; ss; eauto; try refl.
      des. rewrite a. rewrite a0. inv ADD0. ss. refl.
    - inv ADD. ss.
  Qed.

  Lemma remove_messages_le
        mem1 loc from to mem2
        (REMOVE: remove mem1 loc from to Message.reserve mem2):
    messages_le mem1 mem2.
  Proof.
    econs; i.
    - erewrite remove_o; eauto.
      condtac; ss. des. subst.
      exploit remove_get0; eauto. i. des. congruence.
    - inv REMOVE. unfold get_state. ss. condtac; ss; eauto; try refl.
      des. rewrite a. rewrite a0. inv REMOVE0. ss. refl.
    - inv REMOVE. ss.
  Qed.

  Lemma reserve_messages_le
        rsv1 mem1 loc from to rsv2 mem2
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2):
    messages_le mem1 mem2.
  Proof.
    inv RESERVE. eauto using add_messages_le.
  Qed.

  Lemma cancel_messages_le
        rsv1 mem1 loc from to rsv2 mem2
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2):
    messages_le mem1 mem2.
  Proof.
    inv CANCEL. eauto using remove_messages_le.
  Qed.

  Lemma alloc_messages_le
        mem1 tid size loc mem2
        (CLOSED: closed mem1)
        (WELL_ALLOCED: well_alloced mem1)
        (ALLOC: alloc mem1 tid size mem2 loc):
    messages_le mem1 mem2.
  Proof.
    econs; i.
    - erewrite alloc_o; eauto.
    - inv ALLOC. unfold get_state. ss. condtac; ss; try refl.
      des. rewrite a. rewrite a0. inv WELL_ALLOCED.
      exploit PREALLOC. eauto. unfold Block.is_prealloced. des_ifs. rewrite Heq. ss.
    - inv ALLOC. ss. condtac; ss. subst. nia.
      Unshelve. exact tid.
  Qed.

  Lemma free_messages_le
    mem1 loc mem2
    (FREE: free mem1 loc mem2):
    messages_le mem1 mem2.
  Proof.
    econs; i.
    - erewrite free_o; eauto.
    - inv FREE. unfold get_state. ss. condtac; ss; try refl.
      des. rewrite a. rewrite a0. unfold is_freeable, Block.is_freeable in FREEABLE. ss. des_ifs.
    - inv FREE. ss.
  Qed.

  Lemma messages_le_closed_view
        view mem1 mem2
        (LE: messages_le mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    inv CLOSED. econs; i; ss.
    - specialize (RLX loc). des; eauto. right. inv LE.
      exploit GET; eauto.
    - inv LE. unfold get_state, is_prealloced, Block.is_prealloced in *.
      specialize (ALLOC_VIEW loc). specialize (STATES loc). r in STATES.
      des_ifs; try by (exfalso; eapply ALLOC_VIEW; ss).
      + eapply ACCESSIBLE; eauto.
        unfold accessible, Block.accessible in *. rewrite Heq. rewrite Heq0 in H. ss.
      + eapply ACCESSIBLE; eauto.
        unfold accessible, Block.accessible in *. rewrite Heq. rewrite Heq0 in H. ss.
      + exfalso. unfold accessible, Block.accessible in H. rewrite Heq0 in H. ss.
      + exfalso. unfold accessible, Block.accessible in H. rewrite Heq0 in H. ss.
    - inv LE. unfold get_state, is_prealloced, Block.is_prealloced in *.
      specialize (ALLOC_VIEW loc). specialize (STATES loc).
      destruct (Block.state (blocks mem1 (Loc.tid loc) (Loc.bid loc)));
        destruct (Block.state (blocks mem2 (Loc.tid loc) (Loc.bid loc))); ss. eauto.
    - inv LE. unfold get_state, is_prealloced, Block.is_prealloced in *.
      specialize (STATES loc). des_ifs. eapply UNALLOCED.
      destruct (Block.state (blocks mem1 (Loc.tid loc) (Loc.bid loc))); ss.
  Qed.

  Lemma messages_le_closed_message
        msg mem1 mem2
        (LE: messages_le mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; econs. eapply messages_le_closed_view; eauto.
  Qed.

  Lemma future_messages_le
        mem1 mem2
        (FUTURE: future mem1 mem2):
    messages_le mem1 mem2.
  Proof.
    eapply FUTURE.
  Qed.

  (* future *)

  Lemma add_future
        rsv
        mem1 loc from to msg mem2
        (ADD: add mem1 loc from to msg mem2)
        (CLOSED1: closed mem1)
        (WELL_ALLOCED: well_alloced mem1)
        (LE: le rsv mem1)
        (MSG_CLOSED: closed_message msg mem2)
        (MSG_TS: message_to msg loc to):
    <<LE2: le rsv mem2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    splits; eauto.
    - etrans; eauto. eapply add_le; eauto.
    - econs.
      + eapply add_messages_le; eauto.
      + eapply add_closed; eauto.
      + eapply add_well_alloced; eauto.
  Qed.

  Lemma reserve_future
        rsv1 mem1 loc from to rsv2 mem2
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2)
        (CLOSED1: closed mem1)
        (WELL_ALLOCED: well_alloced mem1)
        (LE: le rsv1 mem1)
        (FINITE: finite rsv1)
        (ONLY: reserve_only rsv1):
    <<LE2: le rsv2 mem2>> /\
    <<FINITE2: finite rsv2>> /\
    <<ONLY2: reserve_only rsv2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv RESERVE. splits; eauto.
    - ii. erewrite add_o; eauto.
      revert LHS. erewrite add_o; try exact RSV.
      condtac; ss; eauto.
    - eapply add_finite; eauto.
    - eapply add_reserve_only; eauto.
    - econs.
      + eapply add_messages_le; eauto.
      + eapply add_closed; eauto.
      + eapply add_well_alloced; eauto.
  Qed.

  Lemma cancel_future
        rsv1 mem1 loc from to rsv2 mem2
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2)
        (CLOSED1: closed mem1)
        (WELL_ALLOCED: well_alloced mem1)
        (LE: le rsv1 mem1)
        (FINITE: finite rsv1)
        (ONLY: reserve_only rsv1):
    <<LE2: le rsv2 mem2>> /\
    <<FINITE2: finite rsv2>> /\
    <<ONLY2: reserve_only rsv2>> /\
    <<FUTURE: future mem1 mem2>>.
  Proof.
    inv CANCEL. splits; eauto.
    - ii. erewrite remove_o; eauto.
      revert LHS. erewrite remove_o; try exact RSV.
      condtac; ss; eauto.
    - eapply remove_finite; eauto.
    - eapply remove_reserve_only; eauto.
    - econs.
      + eapply remove_messages_le; eauto.
      + eapply remove_closed; eauto.
      + eapply remove_well_alloced; eauto.
  Qed.

  Lemma add_disjoint
        mem1 loc from to msg mem2 ctx
        (ADD: add mem1 loc from to msg mem2)
        (LE_CTX: le ctx mem1):
    <<LE_CTX2: le ctx mem2>>.
  Proof.
    r. etrans; eauto. eapply add_le. eauto.
  Qed.

  Lemma reserve_disjoint
        rsv1 mem1 loc from to rsv2 mem2 ctx
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2)
        (DISJOINT: disjoint rsv1 ctx)
        (LE_CTX: le ctx mem1):
    <<DISJOINT2: disjoint rsv2 ctx>> /\
    <<LE_CTX2: le ctx mem2>>.
  Proof.
    inv RESERVE. splits.
    - inv DISJOINT. econs. i.
      revert GET1. erewrite add_o; eauto.
      condtac; ss; eauto. i. des. inv GET1. exploit add_get0; eauto. i. des. splits.
      + inv MEM. inv ADD. inv ADD0. eapply DISJOINT.
        apply LE_CTX in GET2. unfold get, Block.get, Cell.get in GET2. eauto.
      + ii. inv H. exploit add_get0; eauto. i. des. eapply LE_CTX in GET2. congruence.
    - etrans; eauto. eapply add_le. eauto.
  Qed.

  Lemma cancel_disjoint
        rsv1 mem1 loc from to rsv2 mem2 ctx
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2)
        (DISJOINT: disjoint rsv1 ctx)
        (LE_CTX: le ctx mem1):
    <<DISJOINT2: disjoint rsv2 ctx>> /\
    <<LE_CTX2: le ctx mem2>>.
  Proof.
    inv CANCEL. splits.
    - inv DISJOINT. econs. i.
      revert GET1. erewrite remove_o; eauto.
      condtac; ss; eauto.
    - ii. erewrite remove_o; eauto.
      condtac; ss; eauto. des. subst.
      exploit LE_CTX; eauto. i.
      exploit remove_get0; try exact RSV. i. des.
      exploit disjoint_get; try exact DISJOINT; eauto. ss.
  Qed.


  (* Lemmas on max_timemap *)

  Definition max_ts (loc:Loc.t) (mem:t): Time.t :=
    Cell.max_ts (Block.contents (blocks mem (Loc.tid loc) (Loc.bid loc)) (Loc.ofs loc)).

  Lemma max_ts_spec
        loc ts from msg mem
        (GET: get loc ts mem = Some (from, msg)):
    <<GET: exists from msg, get loc (max_ts loc mem) mem = Some (from, msg)>> /\
    <<MAX: Time.le ts (max_ts loc mem)>>.
  Proof. eapply Cell.max_ts_spec; eauto. Qed.

  Lemma max_ts_spec2
        tm mem loc
        (CLOSED: closed_view tm mem):
    Time.le (View.rlx tm loc) (max_ts loc mem).
  Proof.
    inv CLOSED. specialize (RLX loc). des.
    - rewrite RLX. eapply Time.bot_spec.
    - eapply max_ts_spec. eauto.
  Qed.

  Definition max_view (mem:t): View.t :=
    View.mk (fun loc => max_ts loc mem) (AllocView.bot).

  (* Lemma max_view_spec *)
  (*       tm mem *)
  (*       (VIEW: closed_view tm mem): *)
  (*   View.le tm (max_view mem). *)
  (* Proof. *)
  (*   econs. *)
  (*   - ii. specialize (VIEW loc). des. *)
  (*     + rewrite VIEW. apply Time.bot_spec. *)
  (*     + eapply max_ts_spec; eauto. *)
  (*   - eapply Alloc *)
  (* Qed. *)

  Lemma le_max_ts
        mem1 mem2 loc
        (LE: le mem1 mem2)
        (INHABITED: inhabited mem1):
    Time.le (max_ts loc mem1) (max_ts loc mem2).
  Proof.
    specialize (INHABITED loc). des.
    exploit max_ts_spec; try apply INHABITED. i. des.
    exploit LE; eauto. i.
    exploit max_ts_spec; try exact x0. i. des.
    apply MAX0.
  Qed.

  (* Lemmas on existence of memory op *)
  Lemma add_exists
        mem1 loc from to msg
        (DISJOINT: forall to2 from2 msg2
                     (GET2: get loc to2 mem1 = Some (from2, msg2)),
            Interval.disjoint (from, to) (from2, to2))
        (TO1: Time.lt from to):
    exists mem2, add mem1 loc from to msg mem2.
  Proof.
    exploit Cell.add_exists; eauto. i. des. destruct loc.
    eexists. econs; eauto. econs; eauto.
  Qed.

  Lemma add_exists_max_ts
        mem1 loc to msg
        (TS: Time.lt (max_ts loc mem1) to):
    exists mem2,
      add mem1 loc (max_ts loc mem1) to msg mem2.
  Proof.
    eapply add_exists; eauto.
    i. exploit max_ts_spec; eauto. i. des.
    ii. inv LHS. inv RHS. ss.
    destruct Time.lt_strorder as [IRREF TRANS].
    assert (H1: Time.le x (max_ts loc mem1)).
    { etrans; [apply TO0 | apply MAX]. }
    eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_max
        mem1 loc to msg
        (TO: Time.lt (max_ts loc mem1) to):
    exists from,
      (<<FROM: Time.lt (max_ts loc mem1) from>>) /\
      exists mem2,
        (<<ADD: add mem1 loc from to msg mem2>>).
  Proof.
    exploit Time.middle_spec; try exact TO. i. des.
    eexists. splits; try exact x0.
    eapply add_exists; eauto.
    ii. inv LHS. inv RHS. ss.
    exploit max_ts_spec; try exact GET2. i. des.
    assert (H1: Time.le x (max_ts loc mem1)).
    { etrans; [apply TO1 | apply MAX]. }
     eapply Time.lt_strorder. eapply TimeFacts.le_lt_lt; eauto.
  Qed.

  Lemma add_exists_le
        mem1' mem1 loc from to msg mem2
        (LE: le mem1' mem1)
        (ADD: add mem1 loc from to msg mem2):
    exists mem2', add mem1' loc from to msg mem2'.
  Proof.
    inv ADD; inv ADD0.
    - exploit Cell.add_exists_le; eauto.
      { ii. specialize (LE loc to0 from0 msg0).
        exploit LE.
        { unfold get, Block.get. erewrite LHS. ss. }
        i. unfold get, Block.get in x0. des_ifs.
      }
      i. des.
      eexists. econs; eauto. econs; eauto.
  Qed.

  Lemma remove_exists
        mem1 loc from to msg
        (GET: get loc to mem1 = Some (from, msg)):
    exists mem2, remove mem1 loc from to msg mem2.
  Proof.
    unfold get, Block.get in GET. des_ifs.
    exploit Cell.remove_exists; eauto. i. des.
    eexists. econs; eauto. econs; eauto.
  Qed.

  Lemma remove_exists_le
        mem1 mem1' loc from to msg mem2
        (LE: le mem1 mem1')
        (REMOVE: remove mem1 loc from to msg mem2):
    exists mem2', remove mem1' loc from to msg mem2'.
  Proof.
    exploit remove_get0; eauto. i. des.
    exploit LE; eauto. i.
    eapply remove_exists. ss.
  Qed.

  Lemma alloc_exists
    mem1 tid size loc bid
    (LOC: loc = Loc.mk (Some tid) bid 0)
    (BID: bid = Memory.next_bid mem1 tid)
    (SIZE: (0 <= size)%Z):
    exists mem2, Memory.alloc mem1 tid size mem2 loc.
  Proof.
    eexists. subst. econs; ss.
  Qed.

  Lemma free_exists
    mem1 loc tid bid
    (LOC: loc = Loc.mk (Some tid) bid 0)
    (FREEABLE: is_freeable loc mem1):
    exists mem2, Memory.free mem1 loc mem2.
  Proof.
    eexists. subst. econs; ss.
  Qed.

  (* maximal & minimal messages satisfying a property *)

  Lemma max_exists P loc mem:
    (<<NONE: forall from to msg
                    (GET: get loc to mem = Some (from, msg)),
        ~ P to>>) \/
    exists from_max to_max msg_max,
      (<<GET: get loc to_max mem = Some (from_max, msg_max)>>) /\
      (<<SAT: P to_max>>) /\
      (<<MAX: forall from to msg
                     (GET: get loc to mem = Some (from, msg))
                     (SAT: P to),
          Time.le to to_max>>).
  Proof.
    hexploit (Cell.max_exists P). i. des; eauto.
    right. esplits; eauto.
  Qed.

  Lemma min_exists P loc mem:
    (<<NONE: forall from to msg
                    (GET: get loc to mem = Some (from, msg)),
        ~ P to>>) \/
    exists from_min to_min msg_min,
      (<<GET: get loc to_min mem = Some (from_min, msg_min)>>) /\
      (<<SAT: P to_min>>) /\
      (<<MIN: forall from to msg
                     (GET: get loc to mem = Some (from, msg))
                     (SAT: P to),
          Time.le to_min to>>).
  Proof.
    hexploit (Cell.min_exists P). i. des; eauto.
    right. esplits; eauto.
  Qed.

  (* next & previous message *)

  Definition empty (mem: t) (loc: Loc.t) (ts1 ts2: Time.t): Prop :=
    forall ts (TS1: Time.lt ts1 ts) (TS2: Time.lt ts ts2),
      get loc ts mem = None.

  Lemma next_exists
        ts mem loc f t m
        (GET: get loc t mem = Some (f, m))
        (TS: Time.lt ts (max_ts loc mem)):
    exists from to msg,
      get loc to mem = Some (from, msg) /\
      Time.lt ts to /\
      empty mem loc ts to.
  Proof.
    exploit Cell.next_exists; eauto.
  Qed.

  Lemma prev_exists
        ts mem loc f t m
        (GET: get loc t mem = Some (f, m))
        (TS: Time.lt t ts):
    exists from to msg,
      get loc to mem = Some (from, msg) /\
      Time.lt to ts /\
      empty mem loc to ts.
  Proof.
    exploit Cell.prev_exists; eauto.
  Qed.

  (* adjacent *)

  Variant adjacent (loc: Loc.t) (from1 to1 from2 to2: Time.t) (mem: t): Prop :=
  | adjacent_intro
      m1 m2
      (GET1: get loc to1 mem = Some (from1, m1))
      (GET2: get loc to2 mem = Some (from2, m2))
      (TS: Time.lt to1 to2)
      (EMPTY: forall ts (TS1: Time.lt to1 ts) (TS2: Time.le ts from2),
          get loc ts mem = None)
  .

  Lemma adjacent_ts
        loc from1 to1 from2 to2 mem
        (ADJ: adjacent loc from1 to1 from2 to2 mem):
    Time.le to1 from2.
  Proof.
    destruct (Time.le_lt_dec to1 from2); auto.
    exfalso. inv ADJ.
    exploit get_ts; try exact GET1.
    exploit get_ts; try exact GET2.
    exploit get_disjoint; [exact GET1|exact GET2|..]. i. des.
    { subst. timetac. }
    apply (x0 to1); econs; ss.
    - refl.
    - econs. auto.
  Qed.

  Lemma adjacent_inj
        loc to mem
        from1 from2 from3 to3 from4 to4
        (ADJ1: adjacent loc from1 to from3 to3 mem)
        (ADJ2: adjacent loc from2 to from4 to4 mem):
    from1 = from2 /\ from3 = from4 /\ to3 = to4.
  Proof.
    inv ADJ1. inv ADJ2.
    inv GET1.
    destruct (Time.le_lt_dec to3 to4); cycle 1.
    { exfalso.
      destruct (Time.le_lt_dec to4 from3).
      - exploit EMPTY; try exact l0; eauto. i. congruence.
      - exploit get_ts; try exact GET2.
        exploit get_ts; try exact GET3.
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x0 to4); econs; ss.
        + econs. ss.
        + refl. }
    inv l.
    { exfalso.
      destruct (Time.le_lt_dec to3 from4).
      - exploit EMPTY0; try exact l; eauto. i. congruence.
      - exploit get_ts; try exact GET2.
        exploit get_ts; try exact GET3.
        exploit get_disjoint; [exact GET2|exact GET3|..]. i. des.
        { subst. timetac. }
        apply (x0 to3); econs; ss.
        + refl.
        + econs. ss. }
    inv H. inv GET2.
    splits; auto.
  Qed.

  Lemma adjacent_exists
        loc from1 to1 msg mem
        (GET: get loc to1 mem = Some (from1, msg))
        (TO: Time.lt to1 (max_ts loc mem)):
    exists from2 to2,
      adjacent loc from1 to1 from2 to2 mem.
  Proof.
    exploit next_exists; eauto. i. des.
    esplits. econs; try exact x0; eauto. i.
    eapply x2; eauto.
    exploit get_ts; try exact x0.
    - eapply TimeFacts.le_lt_lt; eauto.
  Qed.


  (* cap *)

  Variant cap (mem1 mem2: t): Prop :=
  | cap_intro
      (SOUND: le mem1 mem2)
      (MIDDLE: forall loc from1 to1 from2 to2
                 (ADJ: adjacent loc from1 to1 from2 to2 mem1)
                 (TO: Time.lt to1 from2),
          get loc from2 mem2 = Some (to1, Message.reserve))
      (BACK: forall loc from msg
               (GET: get loc (max_ts loc mem1) mem1 = Some (from, msg)),
          get loc (Time.incr (max_ts loc mem1)) mem2 =
          Some (max_ts loc mem1, Message.reserve))
      (COMPLETE: forall loc from to msg
                   (GET1: get loc to mem1 = None)
                   (GET2: get loc to mem2 = Some (from, msg)),
          (exists f m, get loc from mem1 = Some (f, m)))
      (GET_STATE: forall loc, Block.state_t_le (get_state loc mem1) (get_state loc mem2))
      (NEXTBID: forall tid, next_bid mem1 tid <= next_bid mem2 tid)
  .
  #[global] Hint Constructors cap: core.

  Lemma cap_inv
        mem1 mem2
        loc from to msg
        (CAP: cap mem1 mem2)
        (GET: get loc to mem2 = Some (from, msg)):
    get loc to mem1 = Some (from, msg) \/
    (get loc to mem1 = None /\
     exists from1 to2,
        adjacent loc from1 from to to2 mem1 /\
        Time.lt from to /\
        msg = Message.reserve) \/
    (get loc to mem1 = None /\
     from = max_ts loc mem1 /\
     to = Time.incr from /\
     msg = Message.reserve /\
     exists f m,
       get loc from mem1 = Some (f, m)).
  Proof.
    inv CAP. move GET at bottom.
    destruct (get loc to mem1) as [[]|] eqn:GET1.
    { exploit SOUND; eauto. intros x.
      rewrite GET in x. inv x. auto. }
    right. exploit COMPLETE; eauto. intros x. des.
    exploit max_ts_spec; eauto. intros x0. des. inv MAX.
    - left.
      exploit adjacent_exists; try eapply H; eauto. intros x1. des.
      assert (LT: Time.lt from from2).
      { clear MIDDLE BACK COMPLETE GET0 H.
        inv x1. inv x.
        exploit get_ts; try exact GET2.
        destruct (Time.le_lt_dec from2 from); auto.
        inv l.
        - exfalso.
          exploit get_ts; try exact H0.
          exploit get_disjoint; [exact H0|exact GET2|..]. i. des.
          { subst. timetac. }
          apply (x0 from); econs; ss.
          + refl.
          + econs. auto.
        - exfalso. inv H.
          exploit SOUND; try exact GET2. intros x.
          exploit get_ts; try exact GET.
          exploit get_disjoint; [exact GET|exact x|..]. i. des.
          { subst. rewrite GET1 in GET2. inv GET2. }
          destruct (Time.le_lt_dec to to2).
          + apply (x1 to); econs; ss. refl.
          + apply (x1 to2); econs; ss.
            * econs. auto.
            * refl.
      }
      exploit MIDDLE; try eapply x1; eauto. intros x0.
      destruct (Time.eq_dec to from2).
      + subst. rewrite GET in x0. inv x0. esplits; eauto.
      + exfalso. inv x1.
        exploit get_ts; try exact GET.
        exploit get_ts; try exact x0.
        exploit get_disjoint; [exact GET|exact x0|..]. i. des; try congruence.
        destruct (Time.le_lt_dec to from2).
        * apply (x2 to); econs; ss. refl.
        * apply (x2 from2); econs; ss.
          { econs. auto. }
          { refl. }
    - right. inv H. do 2 (split; auto).
      inv x.
      specialize (BACK loc).
      exploit get_ts; try exact GET.
      exploit BACK; eauto. i.
      exploit get_disjoint; [exact GET|exact x0|..]. i. des.
      { subst. esplits; eauto. }
      exfalso.
      destruct (Time.le_lt_dec to (Time.incr (max_ts loc mem1))).
      + apply (x2 to); econs; ss. refl.
      + apply (x2 (Time.incr (max_ts loc mem1))); econs; s;
          eauto using Time.incr_spec; try refl.
        econs. ss.
  Qed.

  Lemma cap_messages_le
        mem1 mem2
        (CAP: cap mem1 mem2):
    messages_le mem1 mem2.
  Proof.
    inv CAP. econs; i; eauto.
  Qed.

  Lemma cap_closed_view
        mem1 mem2 view
        (CAP: cap mem1 mem2)
        (CLOSED: closed_view view mem1):
    closed_view view mem2.
  Proof.
    eapply messages_le_closed_view; eauto. eapply cap_messages_le; eauto.
  Qed.

  Lemma cap_closed_message
        mem1 mem2 msg
        (CAP: cap mem1 mem2)
        (CLOSED: closed_message msg mem1):
    closed_message msg mem2.
  Proof.
    inv CLOSED; eauto using cap_closed_view.
  Qed.

  Lemma cap_closed
        mem1 mem2
        (CAP: cap mem1 mem2)
        (CLOSED: closed mem1):
    closed mem2.
  Proof.
    inv CLOSED. inv CAP. econs; eauto; ii.
    exploit cap_inv; eauto. i. des; subst; try by splits; ss.
    exploit CLOSED0; eauto. i. des.
    splits; eauto using cap_closed_message.
  Qed.

  Lemma cap_le
        mem1 mem2
        (CAP: cap mem1 mem2):
    le mem1 mem2.
  Proof.
    inv CAP. ii. eauto.
  Qed.

  Lemma cap_max_ts
        mem1 mem2
        (INHABITED: inhabited mem1)
        (CAP: cap mem1 mem2):
    forall loc, max_ts loc mem2 = Time.incr (max_ts loc mem1).
  Proof.
    i. dup CAP. inv CAP0. specialize (INHABITED loc). des.
    exploit (max_ts_spec loc); try apply INHABITED. i. des.
    exploit BACK; eauto. i.
    exploit max_ts_spec; try exact x0. i. des.
    apply TimeFacts.antisym; ss.
    destruct (Time.le_lt_dec (max_ts loc mem2) (Time.incr (max_ts loc mem1))); ss.
    specialize (Time.incr_spec (max_ts loc mem1)). i.
    exploit cap_inv; try exact GET0; eauto. i. des.
    - exploit max_ts_spec; try exact x1. i. des.
      exploit TimeFacts.lt_le_lt; try exact l; try exact MAX1. i.
      timetac.
    - inv x2. exploit get_ts; try exact GET2. i.
      exploit max_ts_spec; try exact GET2. i. des.
      exploit TimeFacts.lt_le_lt; try exact x2; try exact MAX1. i.
      assert (H1: Time.lt (Time.incr (max_ts loc mem1)) (max_ts loc mem1)).
      { etrans. exact l. exact x4. }
      timetac.
    - subst. rewrite x3 in l. timetac.
  Qed.

  Lemma cap_exists mem:
    exists mem_cap, <<CAP: cap mem mem_cap>> /\
               <<GET_STATE: forall loc, get_state loc mem_cap = get_state loc mem>> /\
               <<NEXT_BID: next_bid mem_cap = next_bid mem>>.
  Proof.
    destruct mem as [blocks next_bid].

    cut (exists blocks_cap, forall tid bid,
            (fun tid bid blk =>
               Block.cap (blocks tid bid) blk /\ Block.state (blocks tid bid) = Block.state blk)
            tid bid (blocks_cap tid bid)).
    { i. des. exists (mk blocks_cap next_bid).
      splits; ii; ss.
      econs; ii; ss.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1.
        eapply MIDDLE; eauto. move ADJ at bottom. inv ADJ.
        unfold get, Block.get in *. ss.
        econs; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        unfold get_state; ss. rewrite STATE. refl.
      - unfold get_state. ss. destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. eauto.
    }

    cut (exists blocks_cap_cur, forall tbid,
            (fun tbid blk =>
               Block.cap (blocks (fst tbid) (snd tbid)) blk /\
               Block.state (blocks (fst tbid) (snd tbid)) = Block.state blk)
            tbid (blocks_cap_cur tbid)).
    { i. des. exists (fun tid bid => blocks_cap_cur (tid, bid)). i. eapply (H (tid, bid)). }
    eapply dependent_functional_choice. intros tbid. eapply Block.cap_exists.
  Qed.

  Definition cap_of_aux (mem: t):
    { mem_cap: t | (fun mem mem_cap => cap mem mem_cap /\
                                     (forall loc, get_state loc mem_cap = get_state loc mem) /\
                                     (next_bid mem_cap = next_bid mem))
                     mem mem_cap }.
  Proof.
    apply IndefiniteDescription.constructive_indefinite_description.
    apply cap_exists.
  Qed.

  Definition cap_of (mem: t): t :=
    match cap_of_aux mem with
    | exist _ mem_cap _ => mem_cap
    end.

  Lemma cap_of_cap (mem: t):
    <<CAP: cap mem (cap_of mem)>> /\
    <<GET_STATE: forall loc, get_state loc (cap_of mem) = get_state loc mem>> /\
    <<NEXT_BID: next_bid (cap_of mem) = next_bid mem>>.
  Proof.
    unfold cap_of.
    destruct (cap_of_aux mem). des. ss.
  Qed.

  Lemma cap_of_well_alloced mem
    (WELL_ALLOCED: well_alloced mem):
    well_alloced (cap_of mem).
  Proof.
    unfold cap_of.
    destruct (cap_of_aux mem). destruct a as [CAP [GET_STATE NEXTBID]].
    inv WELL_ALLOCED. econs.
    - i. unfold Block.is_prealloced, get_state in *.
      specialize (GET_STATE (Loc.mk (Some tid) bid 0)). ss. rewrite GET_STATE.
      eapply PREALLOC. rewrite <- NEXTBID. eauto.
    - i. unfold Block.is_prealloced, get_state in *.
      specialize (GET_STATE (Loc.mk (Some tid) bid 0)). ss. rewrite GET_STATE.
      eapply ALLOC. rewrite <- NEXTBID. eauto.
    - i. eapply SIZE. unfold get_size, Block.get_size, get_state in *. rewrite <- GET_STATE. eauto.
    - i. unfold get_state in *.
      specialize (GET_STATE (Loc.mk None bid 0)). ss. rewrite GET_STATE. eauto.
  Qed.

  Lemma cap_of_future mem
    (CLOSED: closed mem)
    (WELL_ALLOCED: well_alloced mem):
    future mem (cap_of mem).
  Proof.
    econs.
    - eapply cap_messages_le; eapply cap_of_cap.
    - eapply cap_closed; eauto. eapply cap_of_cap.
    - eapply cap_of_well_alloced; eauto.
  Qed.

  Lemma future_cap_exists
        mem mem_future
        (FUTURE: messages_le mem mem_future):
    exists mem_cap, <<CAP: cap mem mem_cap>> /\
               <<GET_STATE: forall loc, get_state loc mem_cap = get_state loc mem_future>> /\
               <<NEXT_BID: next_bid mem_cap = next_bid mem_future>>.
  Proof.
    destruct mem as [blocks next_bid]. destruct mem_future as [blocks_future next_bid_future].

    cut (exists blocks_cap, forall tid bid,
            (fun tid bid blk =>
               Block.cap (blocks tid bid) blk /\
               Block.state blk = Block.state (blocks_future tid bid))
            tid bid (blocks_cap tid bid)).
    { i. des. exists (mk blocks_cap next_bid_future).
      splits; ii; ss.
      econs; ii; ss.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1.
        eapply MIDDLE; eauto. move ADJ at bottom. inv ADJ.
        unfold get, Block.get in *. ss.
        econs; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        specialize (H1 (Loc.ofs loc)); inv H1; eauto.
      - destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. inv CAP. clear H0.
        unfold get_state; ss. rewrite STATE. eapply FUTURE.
      - eapply FUTURE.
      - unfold get_state. ss. destruct (H (Loc.tid loc) (Loc.bid loc)) as [CAP STATE]. eauto.
    }

    cut (exists blocks_cap_cur, forall tbid,
            (fun tbid blk =>
               Block.cap (blocks (fst tbid) (snd tbid)) blk /\
               Block.state blk = Block.state (blocks_future (fst tbid) (snd tbid)))
            tbid (blocks_cap_cur tbid)).
    { i. des. exists (fun tid bid => blocks_cap_cur (tid, bid)). i. eapply (H (tid, bid)). }
    eapply dependent_functional_choice. intros tbid. eapply Block.future_cap_exists.
    inv FUTURE. specialize (STATES (Loc.mk (fst tbid) (snd tbid) 0%Z)). ss.
  Qed.

  Variant state_future (mem mem': Memory.t): Prop :=
  | state_future_intro
      (GET: forall loc to, get loc to mem = get loc to mem')
      (STATE: forall loc, Block.state_t_le (get_state loc mem) (get_state loc mem'))
      (BID: forall tid, next_bid mem tid <= next_bid mem' tid)
  .
  
  Global Program Instance state_future_PreOrder: PreOrder state_future.
  Next Obligation.
  Proof.
    ii. econs; eauto. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. inv H. inv H0. econs; i; etrans; eauto.
  Qed.

  Lemma cap_state_future
        mem mem_cap
        (CAP: cap mem mem_cap):
    state_future (cap_of mem) mem_cap.
  Proof.
    hexploit (cap_of_cap mem). i. des.
    econs; i.
    - destruct (get loc to mem_cap) as [[from1 msg1]|] eqn:GET1.
      + inv CAP0. exploit cap_inv; try exact GET1; eauto. i. des.
        * exploit SOUND; eauto.
        * subst. exploit MIDDLE; eauto.
        * subst. exploit BACK; eauto.
      + destruct (get loc to (cap_of mem)) as [[from2 msg2]|] eqn:GET2; ss.
        inv CAP. exploit cap_inv; try exact GET2; eauto. i. des.
        * exploit SOUND; eauto. i. congruence.
        * subst. exploit MIDDLE; eauto. i. congruence.
        * subst. exploit BACK; eauto. i. congruence.
    - rewrite GET_STATE. eapply CAP.
    - rewrite NEXT_BID. eapply CAP.
  Qed.

  Lemma add_state_future
        mem1 loc from to msg mem2 mem1'
        (ADD: add mem1 loc from to msg mem2)
        (ST_FUTURE: state_future mem1 mem1'):
    exists mem2', <<ADD: add mem1' loc from to msg mem2'>> /\
             <<ST_FUTURE: state_future mem2 mem2'>>.
  Proof.
    inv ST_FUTURE.
    inv ADD. inv ADD0. erewrite ext_contents in ADD; eauto.
    esplits.
    - econs; ss. econs; ss. eapply ADD.
    - erewrite ext_contents; eauto.
      econs; i; ss.
      + unfold get, Block.get. ss. condtac; ss.
        erewrite ext_contents; eauto.
      + unfold get_state in *. ss. condtac; ss.
  Qed.

  Lemma reserve_state_future
        rsv1 mem1 loc from to rsv2 mem2 mem1'
        (RESERVE: reserve rsv1 mem1 loc from to rsv2 mem2)
        (ST_FUTURE: state_future mem1 mem1'):
    exists mem2', <<RESERVE: reserve rsv1 mem1' loc from to rsv2 mem2'>> /\
             <<ST_FUTURE: state_future mem2 mem2'>>.
  Proof.
    inv RESERVE. exploit add_state_future; eauto. i. des.
    esplits; eauto.
  Qed.

  Lemma cancel_state_future
        rsv1 mem1 loc from to rsv2 mem2 mem1'
        (CANCEL: cancel rsv1 mem1 loc from to rsv2 mem2)
        (ST_FUTURE: state_future mem1 mem1'):
    exists mem2', <<CANCEL: cancel rsv1 mem1' loc from to rsv2 mem2'>> /\
             <<ST_FUTURE: state_future mem2 mem2'>>.
  Proof.
    inv CANCEL. inv ST_FUTURE.
    inv MEM. inv REMOVE. erewrite ext_contents in REMOVE0; eauto.
    esplits.
    - econs; eauto. econs; ss. econs; eauto.
    - erewrite ext_contents; eauto.
      econs; i; ss.
      + unfold get, Block.get. ss. condtac; ss.
        erewrite ext_contents; eauto.
      + unfold get_state in *. ss. condtac; ss.
  Qed.

  Definition na_added_latest (loc: Loc.t) (mem1: t) (mem2: t): Prop :=
    exists from2 ts2 val2 released2,
      (<<GET: get loc ts2 mem2 = Some (from2, Message.message val2 released2 true)>>) /\
        (<<LATEST: forall from1 ts1 val1 released1 na1
                          (GET0: get loc ts1 mem1 = Some (from1, Message.message val1 released1 na1)),
            Time.lt ts1 ts2>>).

  Lemma na_added_latest_le loc mem0 mem1 mem2 mem3
        (LE0: messages_le mem0 mem1)
        (ADDED: na_added_latest loc mem1 mem2)
        (LE1: messages_le mem2 mem3)
    :
    na_added_latest loc mem0 mem3.
  Proof.
    unfold na_added_latest in *. des. esplits.
    { eapply LE1. eauto. }
    i. eapply LE0 in GET0. hexploit LATEST; eauto.
  Qed.

  Variant freed_latest (loc: Loc.t) (mem1: t) (mem2: t): Prop :=
  | freed_latest_intro
      (NFREED: ~ is_freed loc mem1)
      (FREED: is_freed loc mem2).

  Lemma free_inaccessible loc mem1 mem2
    (FREE: free mem1 loc mem2):
    ~ accessible loc mem2.
  Proof.
    inv FREE. unfold accessible, Block.accessible. ss. unfold Block.free.
    condtac; ss. des; congruence.
  Qed.

  Lemma free_accessible loc mem1 mem2 loc'
        (FREE: free mem1 loc mem2)
        (ACCESSIBLE: accessible loc' mem2):
    accessible loc' mem1.
  Proof.
    inv FREE. unfold accessible, Block.accessible in *. ss. revert ACCESSIBLE. condtac; ss.
  Qed.

  Lemma free_accessible1 loc mem1 mem2 loc'
        (FREE: free mem1 loc mem2)
        (ACCESSIBLE: accessible loc' mem1):
    (<<LOC: Loc.get_tbid loc' = Loc.get_tbid loc>>) \/
    (<<ACCESSIBLE: accessible loc' mem2>>).
  Proof.
    destruct loc, loc'. unfold Loc.get_tbid, accessible, Block.accessible in *. ss.
    inv FREE. ss.
    destruct (Loc.id_eq_dec (tid0, bid0) (Some tid1, bid1)); eauto. des. ss. subst. eauto.
  Qed.

  Lemma get_max_ts mem loc ts
    (TS: Time.lt (max_ts loc mem) ts):
    get loc ts mem = None.
  Proof.
    destruct (get loc ts) eqn:GET; eauto. exfalso. destruct p.
    exploit max_ts_spec; eauto. i. des. eapply TimeFacts.le_not_lt; eauto.
  Qed.

  Lemma cap_accessible loc mem:
    accessible loc mem <-> accessible loc (cap_of mem).
  Proof.
    exploit cap_of_cap. i. des. specialize (GET_STATE loc).
    unfold accessible, Block.accessible, get_state in *. ss.
    rewrite GET_STATE. eauto.
    Unshelve. exact mem.
  Qed.

  Lemma add_lt_init
    mem1 loc from to msg mem2
    (ADD: add mem1 loc from to msg mem2)
    (INHABITED: inhabited mem1):
    Time.le Time.init from.
  Proof.
    destruct (Time.le_lt_dec Time.init from); eauto.
    dup ADD. inv ADD0. inv ADD1. inv ADD0. exfalso.
    destruct (Time.le_lt_dec to Time.init).
    - eapply DISJOINT; try eapply INHABITED.
      + eapply Interval.mem_ub; eauto.
      + econs; eauto. ss. ett; eauto. eapply Time.bot_spec.
    - eapply DISJOINT; try eapply INHABITED.
      + econs; try eapply l. ss. econs. eauto.
      + eapply Interval.mem_ub. eapply Time.incr_spec.
  Qed.

  (* ADDITIONAL *)
  Definition cut (Vcut : View.t) (m : Memory.t) : Memory.t :=
    Memory.mk
      (λ tid bid, let blk := Memory.blocks m tid bid in
        Block.mk
          (Block.state blk)
          (λ ofs, let loc := Loc.mk tid bid ofs in
            Cell.cut (Memory.get_cell loc m) (View.rlx Vcut loc)))
      (Memory.next_bid m).

  Lemma cut_get_cell m V loc :
    Memory.get_cell loc (cut V m) = Cell.cut (Memory.get_cell loc m) (View.rlx V loc).
  Proof.
    apply Cell.ext; rewrite /Memory.get_cell /= /Cell.cut; destruct m; ss; rewrite /DOMap.cut /Cell.get /=.
    rewrite /Memory.get_cell /=; intros ts; destruct loc; ss.
  Qed.

  Lemma cut_accessible m V loc :
    Memory.accessible loc (Memory.cut V m) = Memory.accessible loc m.
  Proof.
    destruct loc as [tid bid ofs]. rewrite /Memory.accessible /Block.accessible /= //.
  Qed.

  Lemma get_memory_cell loc ts mem :
    Cell.get ts (Memory.get_cell loc mem) = Memory.get loc ts mem.
  Proof. ss. Qed.

  Lemma cut_add_cell 
        from1 to1 msg1 mem1 from2 to2 msg2 cell2 mem2 loc V t
        (LT: Time.lt from1 to1)
        (TLT: Time.lt to1 to2)
        (SINGLETON: t = to1)
        (RLX: Time.le (View.rlx V loc) t)
        (CUT: Cell.get t (Cell.singleton msg1 LT) = Cell.get t (Cell.cut (Memory.get_cell loc mem1) (View.rlx V loc)))
        (ADD: Cell.add (Cell.singleton msg1 LT) from2 to2 msg2 cell2)
        (MEM: Memory.add mem1 loc from2 to2 msg2 mem2) :
    Cell.get to2 cell2 = Cell.get to2 (Cell.cut (Memory.get_cell loc mem2) (View.rlx V loc)).
  Proof.
    hexploit Cell.add_o; eauto.
    intros. rewrite Cell.singleton_get in CUT; des_ifs. 
    rewrite Cell.cut_spec in CUT; des_ifs.
    hexploit add_o; eauto.
    instantiate (1:=to2). instantiate (1:=loc).
    intros; des_ifs.
    2: { inv o. }
    assert (LECUT: Time.le (View.rlx V loc) to2).
    { etrans; eauto. timetac. }
    rewrite Cell.cut_spec; des_ifs; try timetac.
    rewrite get_memory_cell; rewrite H. rewrite H0. ss.
  Qed.

  Lemma cut_init : Memory.cut (View.init []) (Memory.init []) = (Memory.init []).
  Proof.
    apply Memory.ext; ss.
    intros loc ts; rewrite /cut /get /= /Block.get /= Cell.cut_spec; des_ifs; ss; try timetac.
  Qed.

  Lemma cut_init' : Memory.cut (View.init' []) (Memory.init []) = (Memory.init []).
  Proof.
    apply Memory.ext; ss.
    rewrite /View.init' /cut /get /= /Block.get /=. intros loc ts.
    rewrite Cell.cut_spec /TimeMap.init'; des_ifs; ss; try timetac.
    { rewrite Cell.init_get; des_ifs; timetac. }
    { rewrite Cell.init_get; des_ifs; timetac. } 
    { rewrite Cell.init_get; des_ifs; timetac. }
  Qed.
End Memory.
#[export] Hint Resolve Memory.le_PreOrder: core.
#[export] Hint Resolve Memory.messages_le_PreOrder: core.
#[export] Hint Resolve Memory.state_future_PreOrder: core.
