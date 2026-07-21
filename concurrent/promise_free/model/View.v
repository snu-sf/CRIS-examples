Require Import CRIS.common.CRIS.

From Stdlib Require Import Lists.ListDec Decidable.

From CRIS.promise_free.lib Require Import Basic DataStructure DenseOrder Loc.

From CRIS.promise_free.model Require Import Time.

Set Implicit Arguments.


Lemma time_decidable: decidable_eq Time.t.
Proof.
  ii. destruct (Time.eq_dec x y); [left|right]; eauto.
Qed.

Definition loc_ts_eq_dec := pair_eq_dec Loc.eq_dec Time.eq_dec.

Lemma loc_time_decidable: decidable_eq (Loc.t * Time.t).
Proof.
  ii. destruct x, y.
  destruct (loc_ts_eq_dec (t, t0) (t1, t2)); ss.
  - left. des. subst. ss.
  - right. ii. inv H. des; ss.
Qed.


Module TimeMap <: JoinableType.
  Definition t := Loc.t -> Time.t.

  Definition eq := @eq t.
  
  Definition le (lhs rhs:t): Prop :=
    forall loc, Time.le (lhs loc) (rhs loc).

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. refl. Qed.
  Next Obligation. ii. etrans; eauto. Qed.
  #[global] Hint Resolve le_PreOrder_obligation_2: core.

  Definition bot: t := fun _ => Time.bot.

  Lemma bot_spec (tm:t): le bot tm.
  Proof. ii. apply Time.bot_spec. Qed.

  Definition init size: t :=
    fun loc => match loc with
            | Loc.mk None bid ofs =>
                match List.nth_error size bid with
                | Some sz => if andb (Z.leb 0 ofs) (Z.ltb ofs sz) then Time.init else Time.bot
                | _ => Time.bot
                end
            | Loc.mk (Some _) _ _ => Time.bot
            end.

  Definition init' : t :=
    fun loc => Time.init.

  Definition get (loc:Loc.t) (c:t) := c loc.

  Definition add (l:Loc.t) (ts:Time.t) (tm:t): t :=
    fun l' =>
      if Loc.eq_dec l' l
      then ts
      else get l' tm.

  Definition add_spec l' l ts tm:
    get l' (add l ts tm) =
    if Loc.eq_dec l' l
    then ts
    else get l' tm.
  Proof. auto. Qed.

  Lemma add_spec_eq l ts tm:
    get l (add l ts tm) = ts.
  Proof.
    rewrite add_spec.
    destruct (Loc.eq_dec l l); auto.
    congruence.
  Qed.

  Lemma add_spec_neq l' l ts tm (NEQ: l' <> l):
    get l' (add l ts tm) = get l' tm.
  Proof.
    rewrite add_spec.
    destruct (Loc.eq_dec l' l); auto.
    congruence.
  Qed.

  Definition join (lhs rhs:t): t :=
    fun loc => Time.join (lhs loc) (rhs loc).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. apply LocFun.ext. i. apply Time.join_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply LocFun.ext. i. apply Time.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof. ii. apply Time.join_l. Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. ii. apply Time.join_r. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof. unfold join. ii. apply Time.join_spec; auto. Qed.

  Definition singleton loc ts :=
    LocFun.add loc ts (LocFun.init Time.bot).

  Definition singletons (loc:Loc.t) (size:Z) (ts:Time.t): t :=
    match loc with
    | Loc.mk tid bid ofs => fun loc0 => match loc0 with
                                      | Loc.mk tid0 bid0 ofs0 =>
                                          if andb
                                               (option_rel_bool Tid.eqb tid tid0)
                                               (andb
                                                  (Bid.eqb bid bid0)
                                                  (andb (ofs <=? ofs0)%Z (ofs0 <? ofs + size)%Z))
                                          then ts
                                          else bot loc0
                                      end
    end.

  Lemma singleton_spec loc ts c
        (LOC: Time.le ts (c loc)):
    le (singleton loc ts) c.
  Proof.
    ii. unfold singleton, LocFun.add, LocFun.find.
    condtac; subst; ss. apply Time.bot_spec.
  Qed.

  (* ADDITIONAL *)
  Lemma singletons_spec loc' loc sz ts :
    (singletons loc sz ts) loc' =
    if (decide
      (Loc.get_tbid loc = Loc.get_tbid loc'
      ∧ (Loc.ofs loc <= Loc.ofs loc')
      ∧ (Loc.ofs loc' < Loc.ofs loc + sz)))%Z
    then ts
    else Time.bot.
  Proof.
    rewrite /singletons; des_ifs.
    { simpl_bool; des; exfalso; apply n; ss; split; try lia.
      destruct tid; destruct tid0; ss.
      { apply Pos.eqb_eq in Heq; subst. apply Nat.eqb_eq in Heq0; subst; ss. }
      apply Nat.eqb_eq in Heq0; subst; ss.
    }
    rewrite /Loc.get_tbid in a; ss; des; clarify.
    simpl_bool; des.
    { destruct tid0; ss; apply Pos.eqb_neq in Heq; ss. }
    { apply Nat.eqb_neq in Heq; ss. }
    { lia. }
    { lia. }
  Qed.

  Lemma singleton_inv loc ts c
        (LE: le (singleton loc ts) c):
    Time.le ts (c loc).
  Proof.
    generalize (LE loc). unfold singleton, LocFun.add, LocFun.find.
    condtac; [| congruence]. auto.
  Qed.

  Lemma le_join_l l r
        (LE: le r l):
    join l r = l.
  Proof.
    apply LocFun.ext. i.
    unfold join, Time.join, LocFun.find. condtac; auto.
    apply TimeFacts.antisym; auto.
  Qed.

  Lemma le_join_r l r
        (LE: le l r):
    join l r = r.
  Proof.
    apply LocFun.ext. i.
    unfold join, Time.join, LocFun.find. condtac; auto.
    exfalso. eapply Time.lt_strorder. eapply TimeFacts.lt_le_lt; eauto.
  Qed.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    extensionality loc. apply TimeFacts.antisym; auto.
  Qed.

  Definition bot_unless (cond:bool) (c:t): t :=
    if cond then c else bot.

  Lemma join_bot_l rhs:
    join bot rhs = rhs.
  Proof.
    apply antisym.
    - apply join_spec.
      + apply bot_spec.
      + refl.
    - apply join_r.
  Qed.

  Lemma join_bot_r lhs:
    join lhs bot = lhs.
  Proof.
    rewrite join_comm.
    apply join_bot_l.
  Qed.

  Lemma join_le
        v1 v2 w1 w2
        (LE1: le v1 w1)
        (LE2: le v2 w2):
    le (join v1 v2) (join w1 w2).
  Proof. eauto using join_spec, join_l, join_r. Qed.

End TimeMap.

Module AllocView <: JoinableType.
  Definition t := TBid.t -> bool.

  Definition eq := @eq t.

  Definition le (lhs rhs:t): Prop :=
    forall tbid, lhs tbid -> rhs tbid.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. eauto. Qed.
  Next Obligation. ii. eauto. Qed.
  #[global] Hint Resolve le_PreOrder_obligation_2: core.

  Lemma ext (l r: t)
        (EQ: forall tbid, l tbid = r tbid)
    : l = r.
  Proof. extensionality tbid. apply EQ. Qed.

  Definition bot: t := fun _ => false.

  Lemma bot_spec (tm:t): le bot tm.
  Proof. ii. ss. Qed.

  Definition init (size: list Z): t :=
    fun tbid => match fst tbid with
             | None => if Nat.ltb (snd tbid) (List.length size) then true else false
             | Some _ => false
             end.

  Definition join (lhs rhs:t): t :=
    fun tbid => orb (lhs tbid) (rhs tbid).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. apply ext. i. apply Bool.orb_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply ext. i. unfold join. rewrite Bool.orb_assoc. eauto.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof. ii. unfold join. destruct (lhs tbid); ss. Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. ii. unfold join. destruct (rhs tbid); ss. eauto. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    unfold join. ii. specialize (LHS tbid). specialize (RHS tbid).
    destruct (lhs tbid); destruct (rhs tbid); destruct (o tbid); eauto.
  Qed.

  Definition singleton tbid :=
    fun tbid' => if TBid.eq_dec tbid' tbid then true else false.

  Lemma singleton_spec tbid (c: t)
        (LOC: c tbid):
    le (singleton tbid) c.
  Proof.
    unfold le, singleton. intro tbid0. condtac; subst; ss.
  Qed.

  Lemma singleton_inv tbid c
        (LE: le (singleton tbid) c):
    c tbid.
  Proof.
    generalize (LE tbid). unfold singleton.
    condtac; [| congruence]. i. auto.
  Qed.

  Lemma le_join_l l r
        (LE: le r l):
    join l r = l.
  Proof.
    apply ext. i. specialize (LE tbid).
    unfold join. destruct (l tbid); destruct (r tbid); ss; eauto. exploit LE; eauto.
  Qed.

  Lemma le_join_r l r
        (LE: le l r):
    join l r = r.
  Proof.
    apply ext. i. specialize (LE tbid).
    unfold join. destruct (l tbid); destruct (r tbid); ss; eauto. exploit LE; eauto.
  Qed.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    extensionality tbid. specialize (LR tbid). specialize (RL tbid).
    destruct (l tbid); destruct (r tbid); ss; eauto. exploit LR; ss.
  Qed.

  Lemma join_bot_l rhs:
    join bot rhs = rhs.
  Proof.
    apply antisym.
    - apply join_spec.
      + apply bot_spec.
      + refl.
    - apply join_r.
  Qed.

  Lemma join_bot_r lhs:
    join lhs bot = lhs.
  Proof.
    rewrite join_comm.
    apply join_bot_l.
  Qed.

  Lemma join_le
        v1 v2 w1 w2
        (LE1: le v1 w1)
        (LE2: le v2 w2):
    le (join v1 v2) (join w1 w2).
  Proof. eauto using join_spec, join_l, join_r. Qed.

End AllocView.
  
Module View <: JoinableType.
  Structure t_ := mk {
    rlx: TimeMap.t;
    alloc_view: AllocView.t;
  }.

  Definition t := t_.

  Definition eq := @eq t.

  (* Variant wf (view:t): Prop := *)
  (* | wf_intro *)
  (*     (PREALLOCED: forall loc, ~ alloc_view view (Loc.get_tbid loc) -> *)
  (*                         (rlx view) loc = Time.bot) *)
  (*     (ALLOCED: forall loc, alloc_view view (Loc.get_tbid loc) -> *)
  (*                      Time.le (Time.init) ((rlx view) loc)) *)
  (* . *)
  (* #[global] Hint Constructors wf: core. *)

  Variant le_ (lhs rhs:t): Prop :=
  | le_intro
      (RLX: TimeMap.le (rlx lhs) (rlx rhs))
      (ALLOC_VIEW: AllocView.le (alloc_view lhs) (alloc_view rhs))
  .
  Definition le := le_.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; refl.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
  Qed.
  #[global] Hint Resolve le_PreOrder_obligation_2: core.

  Lemma ext l r
        (RLX: (rlx l) = (rlx r))
        (ALLOC_VIEW: (alloc_view l) = (alloc_view r))
    : l = r.
  Proof.
    destruct l, r. f_equal; auto.
  Qed.

  Definition bot: t := mk TimeMap.bot AllocView.bot.

  Lemma bot_spec (c:t): le bot c.
  Proof. econs; try apply TimeMap.bot_spec; ss. Qed.

  (* Lemma bot_wf: wf bot. *)
  (* Proof. econs; i; ss. Qed. *)

  Definition init size: t := mk (TimeMap.init size) (AllocView.init size).
  Definition init' size: t := mk (TimeMap.init') (AllocView.init size).

  (* Lemma init_wf size: wf (init size). *)
  (* Proof. *)
  (*   econs; i; destruct loc as [[tid|] bid ofs]; ss. *)
  (*   - unfold Loc.get_tbid, AllocView.init in *. ss. refl. *)
  (* Qed. *)

  Definition join (lhs rhs:t): t :=
    mk (TimeMap.join (rlx lhs) (rlx rhs))
       (AllocView.join (alloc_view lhs) (alloc_view rhs)).

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. apply ext. apply TimeMap.join_comm. apply AllocView.join_comm. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof.
    apply ext. apply TimeMap.join_assoc. apply AllocView.join_assoc.
  Qed.

  Lemma join_l lhs rhs: le lhs (join lhs rhs).
  Proof. econs. apply TimeMap.join_l. apply AllocView.join_l. Qed.

  Lemma join_r lhs rhs: le rhs (join lhs rhs).
  Proof. econs. apply TimeMap.join_r. apply AllocView.join_r. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof.
    inv LHS. inv RHS.
    econs. apply TimeMap.join_spec; eauto. apply AllocView.join_spec; eauto.
  Qed.

  (* Lemma join_wf *)
  (*       lhs rhs *)
  (*       (LHS: wf lhs) *)
  (*       (RHS: wf rhs): *)
  (*   wf (join lhs rhs). *)
  (* Proof. *)
  (*   inv LHS. inv RHS. *)
  (*   econs; ii; ss. *)
  (*   - specialize (PREALLOCED loc). specialize (PREALLOCED0 loc). *)
  (*     unfold AllocView.join in H. unfold TimeMap.join. *)
  (*     destruct (alloc_view lhs (Loc.get_tbid loc)); *)
  (*       destruct (alloc_view rhs (Loc.get_tbid loc)); ss. *)
  (*     rewrite PREALLOCED; ss. rewrite PREALLOCED0; ss. *)
  (*   - specialize (ALLOCED loc). specialize (ALLOCED0 loc). *)
  (*     unfold AllocView.join in H. unfold TimeMap.join. *)
  (*     destruct (alloc_view lhs (Loc.get_tbid loc)); *)
  (*       destruct (alloc_view rhs (Loc.get_tbid loc)); ss. *)
  (*     + etrans; eauto. eapply Time.join_l. *)
  (*     + etrans; eauto. eapply Time.join_l. *)
  (*     + etrans; eauto. eapply Time.join_r. *)
  (* Qed. *)

  Definition singleton loc ts :=
    mk (TimeMap.singleton loc ts) AllocView.bot.

  Definition alloc_view_singleton (loc:Loc.t) (size:Z): t :=
    mk (TimeMap.singletons loc size Time.init) (AllocView.singleton (Loc.get_tbid loc)).

  (* Definition singleton_wf loc ts *)
  (*   (TS: Time.le Time.init ts): *)
  (*   wf (singleton loc ts). *)
  (* Proof. *)
  (*   econs; i; ss. *)
  (*   - unfold AllocView.singleton in H. unfold TimeMap.singleton. *)
  (*     unfold LocFun.add. condtac; ss. subst. des_ifs. *)
  (*   - unfold AllocView.singleton in H. unfold TimeMap.singleton. *)
  (*     unfold LocFun.add. condtac; ss. subst. des_ifs. *)
  (*   - *)

  Lemma singleton_spec loc ts c
        (LOC: Time.le ts (c.(rlx) loc)):
    le (singleton loc ts) c.
  Proof.
    ii. unfold singleton, LocFun.add, LocFun.find. econs; ss.
    eapply TimeMap.singleton_spec. eauto.
  Qed.

  (* Lemma singleton_inv loc ts c *)
  (*       (LE: le (singleton loc ts) c): *)
  (*   Time.le ts (c loc). *)
  (* Proof. *)
  (*   generalize (LE loc). unfold singleton, LocFun.add, LocFun.find. *)
  (*   condtac; [| congruence]. auto. *)
  (* Qed. *)

  Lemma le_join_l l r
        (LE: le r l):
    join l r = l.
  Proof.
    inv LE. apply ext. apply TimeMap.le_join_l; auto. apply AllocView.le_join_l; auto.
  Qed.

  Lemma le_join_r l r
        (LE: le l r):
    join l r = r.
  Proof.
    inv LE. apply ext. apply TimeMap.le_join_r; auto. apply AllocView.le_join_r; auto.
  Qed.

  Lemma antisym l r
        (LR: le l r)
        (RL: le r l):
    l = r.
  Proof.
    destruct l, r. inv LR. inv RL. ss.
    f_equal. apply TimeMap.antisym; auto. apply AllocView.antisym; auto.
  Qed.

  Lemma join_bot_l rhs:
    join bot rhs = rhs.
  Proof.
    apply antisym.
    - apply join_spec.
      + apply bot_spec.
      + refl.
    - apply join_r.
  Qed.

  Lemma join_bot_r lhs:
    join lhs bot = lhs.
  Proof.
    rewrite join_comm.
    apply join_bot_l.
  Qed.

  Lemma join_le
        v1 v2 w1 w2
        (LE1: le v1 w1)
        (LE2: le v2 w2):
    le (join v1 v2) (join w1 w2).
  Proof. eauto using join_spec, join_l, join_r. Qed.

End View.

