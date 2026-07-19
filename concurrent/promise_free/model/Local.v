Require Import CRIS.common.CRIS.

From CRIS.promise_free.lib Require Import
  Basic Loc DataStructure DenseOrder Event.

From CRIS.promise_free.model Require Import
  Time View BoolMap Promises Cell Memory TView Global.
From CRIS.promise_free.lib Require Import Val Ordering.

Set Implicit Arguments.


Module ThreadEvent.
  Variant t :=
  | promise (loc: Loc.t)
  | reserve (loc: Loc.t) (from to: Time.t)
  | cancel (loc: Loc.t) (from to: Time.t)
  | free_promise (tbid: TBid.t)
  | silent
  | read (loc: Loc.t) (ts: Time.t) (val: Val.t) (released: View.t) (ord: Ordering.t)
  | write (loc: Loc.t) (from to: Time.t) (val: Val.t) (released: View.t) (ord: Ordering.t)
  | faa (loc: Loc.t) (tsr tsw: Time.t) (valr addendum: Val.t)
           (releasedr releasedw: View.t) (ordr ordw: Ordering.t)
  | cas (loc: Loc.t) (tsr tsw: Time.t) (valr valc valw: Val.t) (valret: option bool)
        (releasedr releasedw: View.t) (ordr ordw: Ordering.t)
  | fence (ordr ordw: Ordering.t)
  | syscall (e: Event.t)
  | failure
  | alloc (loc: Loc.t) (size: Z)
  | free (loc: Loc.t) (size: Z)
  | ptr_eq (loc1 loc2: Loc.t) (valret: bool)
  | racy_read (loc: Loc.t) (to: option Time.t) (val: Val.t) (ord: Ordering.t) (racy_prm: bool)
  | racy_write (loc: Loc.t) (to: option Time.t) (val: Val.t) (ord: Ordering.t) (racy_prm: bool)
  | racy_faa (loc: Loc.t) (to: option Time.t) (valr addendum: Val.t) (ordr ordw: Ordering.t) (racy_prm: bool)
  | racy_cas (loc: Loc.t) (to: option Time.t) (valr valc valw: Val.t) (valret: option bool) (ordr ordw: Ordering.t) (racy_prm: bool)
  | racy_free (loc: Loc.t) (size: Z) (racy_prm: bool)
  | inaccessible_read (loc: Loc.t) (val: Val.t) (ord: Ordering.t) (racy_prm: bool)
  | inaccessible_write (loc: Loc.t) (val: Val.t) (ord: Ordering.t) (racy_prm: bool)
  | inaccessible_faa (loc: Loc.t) (valr addendum: Val.t) (ordr ordw: Ordering.t) (racy_prm: bool)
  | inaccessible_cas (loc: Loc.t) (valr valc valw: Val.t) (valret: option bool) (ordr ordw: Ordering.t) (racy_prm: bool)
  | inaccessible_cmp_cas (loc: Loc.t) (to: Time.t) (valr valc valw: Val.t) (valret: option bool)
                         (released: View.t) (ordr ordw: Ordering.t) (racy_prm: bool)
  | inaccessible_free (loc: Loc.t) (size: Z) (racy_prm: bool)
  | inaccessible_ptr_eq (loc1 loc2: Loc.t) (valret: option bool) (racy_prm: bool)
  .
  #[global] Hint Constructors t: core.

  Definition get_event (e: t): option Event.t :=
    match e with
    | syscall e => Some e
    | _ => None
    end.

  Definition get_program_event (e: t): ProgramEvent.t :=
    match e with
    | read loc _ val _ ord
    | racy_read loc _ val ord _
    | inaccessible_read loc val ord _ => ProgramEvent.read loc val ord
    | write loc _ _ val _ ord
    | racy_write loc _ val ord _
    | inaccessible_write loc val ord _ => ProgramEvent.write loc val ord
    | faa loc _ _ valr addendum _ _ ordr ordw
    | racy_faa loc _ valr addendum ordr ordw _
    | inaccessible_faa loc valr addendum ordr ordw _ => ProgramEvent.faa loc valr addendum ordr ordw
    | cas loc _ _  valr valc valw valret _ _ ordr ordw
    | racy_cas loc _ valr valc valw valret ordr ordw _
    | inaccessible_cas loc valr valc valw valret ordr ordw _
    | inaccessible_cmp_cas loc _ valr valc valw valret _ ordr ordw _ =>
      ProgramEvent.cas loc valr valc valw valret ordr ordw
    | fence ordr ordw => ProgramEvent.fence ordr ordw
    | syscall ev => ProgramEvent.syscall ev
    | failure => ProgramEvent.failure
    | alloc loc size => ProgramEvent.alloc loc size
    | free loc _
    | racy_free loc _ _
    | inaccessible_free loc _ _ => ProgramEvent.free loc
    | ptr_eq loc1 loc2 valret => ProgramEvent.ptr_eq loc1 loc2 (Some valret)
    | inaccessible_ptr_eq loc1 loc2 valret _ => ProgramEvent.ptr_eq loc1 loc2 valret
    | promise _
    | reserve _ _ _
    | cancel _ _ _
    | free_promise _
    | silent => ProgramEvent.silent
    end.

  Definition get_machine_event (e: t): MachineEvent.t :=
    match e with
    | syscall e => MachineEvent.syscall e
    | failure
    | racy_write _ _ _ _ _
    | racy_faa _ _ _ _ _ _ _
    | racy_cas _ _ _ _ _ _ _ _ _
    | racy_free _ _ _
    | inaccessible_read _ _ _ _
    | inaccessible_write _ _ _ _
    | inaccessible_faa _ _ _ _ _ _
    | inaccessible_cas _ _ _ _ _ _ _ _
    | inaccessible_cmp_cas _ _ _ _ _ _ _ _ _ _
    | inaccessible_free _ _ _ => MachineEvent.failure
    | _ => MachineEvent.silent
    end.

  Definition get_machine_event_pf (e: t): MachineEvent.t :=
    match e with
    | syscall e => MachineEvent.syscall e
    | failure
    | racy_read _ _ _ _ _
    | racy_write _ _ _ _ _
    | racy_faa _ _ _ _ _ _ _
    | racy_cas _ _ _ _ _ _ _ _ _
    | racy_free _ _ _
    | inaccessible_read _ _ _ _
    | inaccessible_write _ _ _ _
    | inaccessible_faa _ _ _ _ _ _
    | inaccessible_cas _ _ _ _ _ _ _ _
    | inaccessible_cmp_cas _ _ _ _ _ _ _ _ _ _
    | inaccessible_free _ _ _
    | inaccessible_ptr_eq _ _ _ _ => MachineEvent.failure
    | _ => MachineEvent.silent
    end.

  Definition is_reading (e:t): option (Loc.t * Time.t * Val.t * View.t * Ordering.t) :=
    match e with
    | read loc ts val released ord => Some (loc, ts, val, released, ord)
    | faa loc tsr _ valr _ releasedr _ ordr _ => Some (loc, tsr, valr, releasedr, ordr)
    | cas loc tsr _ valr _ _ _ releasedr _ ordr _ => Some (loc, tsr, valr, releasedr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Time.t * Time.t * Val.t * View.t * Ordering.t) :=
    match e with
    | write loc from to val released ord => Some (loc, from, to, val, released, ord)
    | faa loc tsr tsw valr addendum _ releasedw _ ordw => Some (loc, tsr, tsw, Val.add valr addendum, releasedw, ordw)
    | cas loc tsr tsw _ _ valw valret _ releasedw _ ordw =>
        match valret with
        | Some true => Some (loc, tsr, tsw, valw, releasedw, ordw)
        | _ => None
        end
    | _ => None
    end.

  Definition is_free (e:t): option (Loc.t * Z) :=
    match e with
    | free loc size => Some (loc, size)
    | _ => None
    end.

  Definition is_accessing_loc (l: Loc.t) (e: t): Prop :=
    match e with
    | read loc _ _ _ _
    | write loc _ _ _ _ _
    | faa loc _ _ _ _ _ _ _ _
    | racy_read loc _ _ _ _
    | racy_write loc _ _ _ _
    | racy_faa loc _ _ _ _ _ _
    | racy_cas loc _ _ _ _ _ _ _ _
    | inaccessible_read loc _ _ _
    | inaccessible_write loc _ _ _
    | inaccessible_faa loc _ _ _ _ _
    | inaccessible_cas loc _ _ _ _ _ _ _ => loc = l
    | alloc loc size
    | free loc size
    | racy_free loc size _
    | inaccessible_free loc size _ => Loc.get_tbid loc = Loc.get_tbid l /\
                                           (0 <= Loc.ofs l < size)%Z
    | cas loc _ _ valr valc _ _ _ _ _ _
    | inaccessible_cmp_cas loc _ valr valc _ _ _ _ _ _ => loc = l \/ valr = Val.Vptr l \/ valc = Val.Vptr l
    | ptr_eq loc1 loc2 _
    | inaccessible_ptr_eq loc1 loc2 _ _ => loc1 = l \/ loc2 = l
    | _ => False
    end.

  Definition is_accessing_block (tbid: TBid.t) (e: t): Prop :=
    match e with
    | read loc _ _ _ _
    | write loc _ _ _ _ _
    | faa loc _ _ _ _ _ _ _ _
    | alloc loc _
    | racy_read loc _ _ _ _
    | racy_write loc _ _ _ _
    | racy_faa loc _ _ _ _ _ _
    | racy_cas loc _ _ _ _ _ _ _ _
    | inaccessible_read loc _ _ _
    | inaccessible_write loc _ _ _
    | inaccessible_faa loc _ _ _ _ _
    | free loc _
    | racy_free loc _ _
    | inaccessible_free loc _ _ 
    | inaccessible_cas loc _ _ _ _ _ _ _ => Loc.get_tbid loc = tbid
    | cas loc _ _ valr valc _ _ _ _ _ _
    | inaccessible_cmp_cas loc _ valr valc _ _ _ _ _ _ =>
        Loc.get_tbid loc = tbid \/
        (exists l, valr = Val.Vptr l /\ Loc.get_tbid l = tbid) \/
        (exists l, valc = Val.Vptr l /\ Loc.get_tbid l = tbid)
    | ptr_eq loc1 loc2 _
    | inaccessible_ptr_eq loc1 loc2 _ _ => Loc.get_tbid loc1 = tbid \/ Loc.get_tbid loc2 = tbid
    | _ => False
    end.

  Definition is_failure (e: t): Prop :=
    match e with
    | failure
    | racy_read _ _ _ _ _
    | racy_write _ _ _ _ _
    | racy_faa _ _ _ _ _ _ _
    | racy_cas _ _ _ _ _ _ _ _ _
    | racy_free _ _ _
    | inaccessible_read _ _ _ _
    | inaccessible_write _ _ _ _
    | inaccessible_faa _ _ _ _ _ _
    | inaccessible_cas _ _ _ _ _ _ _ _
    | inaccessible_cmp_cas _ _ _ _ _ _ _ _ _ _
    | inaccessible_free _ _ _
    | inaccessible_ptr_eq _ _ _ _ => True
    | _ => False
    end.

  Definition is_failure_promise (e: t): Prop :=
    match e with
    | racy_read _ _ _ _ true
    | racy_write _ _ _ _ true
    | racy_faa _ _ _ _ _ _ true
    | racy_cas _ _ _ _ _ _ _ _ true
    | racy_free _ _ true
    | inaccessible_read _ _ _ true
    | inaccessible_write _ _ _ true
    | inaccessible_faa _ _ _ _ _ true
    | inaccessible_cas _ _ _ _ _ _ _ true
    | inaccessible_cmp_cas _ _ _ _ _ _ _ _ _ true
    | inaccessible_free _ _ true
    | inaccessible_ptr_eq _ _ _ true => True
    | _ => False
    end.

  Definition is_racy_message_promise (e: t): Prop :=
    match e with
    | racy_read _ _ _ _ true
    | racy_write _ _ _ _ true
    | racy_faa _ _ _ _ _ _ true
    | racy_cas _ _ _ _ _ _ _ _ true
    | racy_free _ _ true => True
    | _ => False
    end.

  Definition is_racy_free_promise (e: t): Prop :=
    match e with
    | inaccessible_read _ _ _ true
    | inaccessible_write _ _ _ true
    | inaccessible_faa _ _ _ _ _ true
    | inaccessible_cas _ _ _ _ _ _ _ true
    | inaccessible_cmp_cas _ _ _ _ _ _ _ _ _ true
    | inaccessible_free _ _ true
    | inaccessible_ptr_eq _ _ _ true => True
    | _ => False
    end.

  Lemma is_racy_promise_nor
        e
        (RACE: is_failure_promise e):
    is_racy_message_promise e \/ is_racy_free_promise e.
  Proof.
    destruct e; ss; eauto; destruct to; eauto.
  Qed.

  Definition is_sc (e: t): Prop :=
    match e with
    | fence _ ordw => Ordering.le Ordering.seqcst ordw
    | syscall _ => True
    | _ => False
    end.

  Definition is_pf (e: t): Prop :=
    match e with
    | promise _
    | reserve _ _ _
    | free_promise _ => False
    | _ => True
    end.

  Definition is_internal (e: t): Prop :=
    match e with
    | promise _
    | reserve _ _ _
    | cancel _ _ _
    | free_promise _ => True
    | _ => False
    end.

  Definition is_program (e: t): Prop :=
    match e with
    | promise _
    | reserve _ _ _
    | cancel _ _ _
    | free_promise _  => False
    | _ => True
    end.

  Definition is_silent (e: t): Prop :=
    get_machine_event e = MachineEvent.silent.

  (* Lemma eq_program_event_eq_loc *)
  (*       e1 e2 loc *)
  (*       (EVENT: get_program_event e1 = get_program_event e2): *)
  (*   is_accessing_loc loc e1 <-> is_accessing_loc loc e2. *)
  (* Proof. *)
  (*   unfold is_accessing_loc. *)
  (*   destruct e1; destruct e2; ss; inv EVENT; ss. *)
  (* Qed. *)
End ThreadEvent.


Module Local.
  Structure t := mk {
    tview: TView.t;
    promises: Promises.t;
    reserves: Memory.t;
    free_promises: FreePromises.t;
    tid: Tid.t;
  }.

  Definition init (tid : Tid.t) size :=
    mk (TView.init size) Promises.bot Memory.bot FreePromises.bot tid.

  Variant is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: promises lc = Promises.bot)
      (PROMISESFREE: free_promises lc = FreePromises.bot)
  .
  #[global] Hint Constructors is_terminal: core.

  Variant wf (lc: t) (gl: Global.t): Prop :=
  | wf_intro
      (TVIEW_WF: TView.wf (tview lc))
      (TVIEW_CLOSED: TView.closed (tview lc) (Global.memory gl))
      (PROMISES: Promises.le (promises lc) (Global.promises gl))
      (PROMISES_FINITE: Promises.finite (promises lc))
      (FREE_PROMISES: FreePromises.le (free_promises lc) (Global.free_promises gl))
      (FREE_PROMISES_FINITE: FreePromises.finite (free_promises lc))
      (RESERVES: Memory.le (reserves lc) (Global.memory gl))
      (RESERVES_ONLY: Memory.reserve_only (reserves lc))
      (RESERVES_FINITE: Memory.finite (reserves lc))
  .
  #[global] Hint Constructors wf: core.

  Lemma init_wf (tid : Tid.t) (size : list Z): wf (init tid size) (Global.init size).
  Proof.
    econs; ss.
    - apply TView.init_wf.
    - apply TView.init_closed.
    - apply Promises.bot_finite.
    - apply FreePromises.bot_finite.
    - apply Memory.bot_le.
    - apply Memory.bot_reserve_only.
    - apply Memory.bot_finite.
  Qed.

  Lemma cap_wf
        lc gl gl_cap
        (WF: wf lc gl)
        (CAP: Global.cap gl gl_cap):
    wf lc gl_cap.
  Proof.
    inv WF. inv CAP. econs; ss.
    - eapply TView.cap_closed; eauto.
    - rewrite PRM. eauto.
    - rewrite FPRM. eauto.
    - etrans; eauto. apply Memory.cap_le. eauto.
  Qed.

  Lemma cap_of_wf
        lc gl
        (WF: wf lc gl):
    wf lc (Global.cap_of gl).
  Proof.
    eapply cap_wf; eauto. eapply Global.cap_of_cap.
  Qed.

  (* Additional *)
  Definition promise_free (lc : t) : Prop :=
    promises lc = Promises.bot ∧ reserves lc = Memory.bot ∧ free_promises lc = FreePromises.bot.
  
  Lemma init_promise_free tid sz : promise_free (init tid sz). by ss. Qed.

  Variant disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (PROMISES_DISJOINT: Promises.disjoint (promises lc1) (promises lc2))
      (FREE_PROMISES_DISJOINT: FreePromises.disjoint (free_promises lc1) (free_promises lc2))
      (RESERVES_DISJOINT: Memory.disjoint (reserves lc1) (reserves lc2))
      (NEQ: tid lc1 <> tid lc2)
  .
  #[global] Hint Constructors disjoint: core.

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs; try by (symmetry; apply H).
  Qed.

  Variant promise_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (lc2: t) (gl2: Global.t): Prop :=
  | promise_step_intro
      prm2 gprm2
      (PROMISE: Promises.promise (promises lc1) (Global.promises gl1) loc prm2 gprm2)
      (LC2: lc2 = mk (tview lc1) prm2 (reserves lc1) (free_promises lc1) (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) gprm2 (Global.free_promises gl1) (Global.memory gl1))
  .
  #[global] Hint Constructors promise_step: core.

  Variant reserve_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (from to: Time.t) (lc2: t) (gl2: Global.t): Prop :=
  | reserve_step_intro
      rsv2 mem2
      (RESERVE: Memory.reserve (reserves lc1) (Global.memory gl1) loc from to rsv2 mem2)
      (LC2: lc2 = mk (tview lc1) (promises lc1) rsv2 (free_promises lc1) (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) (Global.promises gl1) (Global.free_promises gl1) mem2)
  .
  #[global] Hint Constructors reserve_step: core.

  Variant cancel_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (from to: Time.t) (lc2: t) (gl2: Global.t): Prop :=
  | cancel_step_intro
      rsv2 mem2
      (CANCEL: Memory.cancel (reserves lc1) (Global.memory gl1) loc from to rsv2 mem2)
      (LC2: lc2 = mk (tview lc1) (promises lc1) rsv2 (free_promises lc1) (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) (Global.promises gl1) (Global.free_promises gl1) mem2)
  .
  #[global] Hint Constructors cancel_step: core.

  Variant free_promise_step (lc1: t) (gl1: Global.t) (tbid: TBid.t) (lc2: t) (gl2: Global.t): Prop :=
  | free_promise_step_intro
      prm2 gprm2
      (PROMISE: FreePromises.promise (free_promises lc1) (Global.free_promises gl1)
                                     tbid prm2 gprm2)
      (NFREED: ~ Block.is_freed (Memory.blocks (Global.memory gl1) (fst tbid) (snd tbid)))
      (LC2: lc2 = mk (tview lc1) (promises lc1) (reserves lc1) prm2 (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) (Global.promises gl1) gprm2 (Global.memory gl1))
  .
  #[global] Hint Constructors free_promise_step: core.

  Variant read_step
          (lc1: t) (gl1: Global.t)
          (loc: Loc.t) (to: Time.t) (val: Val.t) (released: View.t) (ord: Ordering.t)
          (lc2: t): Prop :=
  | read_step_intro
      from val' na
      tview2
      (ACCESSIBLE: Memory.accessible loc (Global.memory gl1))
      (GET: Memory.get loc to (Global.memory gl1) = Some (from, Message.message val' released na))
      (VAL: Val.le val val')
      (READABLE: TView.readable (TView.cur (tview lc1)) loc to ord)
      (TVIEW: TView.read_tview (tview lc1) loc to released ord = tview2)
      (LC2: lc2 = mk tview2 (promises lc1) (reserves lc1) (free_promises lc1) (tid lc1)):
      read_step lc1 gl1 loc to val released ord lc2
  .
  #[global] Hint Constructors read_step: core.

  Variant write_step
          (lc1: t) (gl1: Global.t)
          (loc: Loc.t) (from to: Time.t)
          (val: Val.t) (releasedm released: View.t) (ord: Ordering.t)
          (lc2: t) (gl2: Global.t): Prop :=
  | write_step_intro
      prm2 gprm2 mem2
      (ACCESSIBLE: Memory.accessible loc (Global.memory gl1))
      (RELEASED: released = TView.write_released (tview lc1) loc to releasedm ord)
      (WRITABLE: TView.writable (TView.cur (tview lc1)) loc to ord)
      (FULFILL: Promises.fulfill (promises lc1) (Global.promises gl1) loc ord prm2 gprm2)
      (WRITE: Memory.add (Global.memory gl1) loc from to
                         (Message.message val released (Ordering.le ord Ordering.na)) mem2)
      (LC2: lc2 = mk (TView.write_tview (tview lc1) loc to ord) prm2 (reserves lc1) (free_promises lc1) (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) gprm2 (Global.free_promises gl1) mem2):
      write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2
  .
  #[global] Hint Constructors write_step: core.

  Variant fence_step (lc1: t) (gl1: Global.t) (ordr ordw: Ordering.t) (lc2: t) (gl2: Global.t): Prop :=
  | fence_step_intro
      tview2
      (READ: TView.read_fence_tview (tview lc1) ordr = tview2)
      (LC2: lc2 = mk (TView.write_fence_tview tview2 (Global.sc gl1) ordw)
                     (promises lc1) (reserves lc1) (free_promises lc1) (tid lc1))
      (GL2: gl2 = Global.mk (TView.write_fence_sc tview2 (Global.sc gl1) ordw)
                            (Global.promises gl1) (Global.free_promises gl1) (Global.memory gl1))
      (PROMISES: Ordering.le Ordering.seqcst ordw -> promises lc1 = Promises.bot)
      (FREEPROMISES: Ordering.le Ordering.seqcst ordw -> free_promises lc1 = FreePromises.bot):
      fence_step lc1 gl1 ordr ordw lc2 gl2
  .
  #[global] Hint Constructors fence_step: core.

  Variant failure_step (lc1:t): Prop :=
  | failure_step_intro
  .
  #[global] Hint Constructors failure_step: core.

  Variant alloc_step
          (lc1: t) (gl1: Global.t)
          (loc: Loc.t) (size:Z)
          (lc2: t) (gl2: Global.t): Prop :=
  | alloc_step_intro
      mem2 tview2
      (ALLOC: Memory.alloc (Global.memory gl1) (tid lc1) size mem2 loc)
      (TVIEW: TView.alloc_tview (tview lc1) loc size = tview2)
      (LC2: lc2 = mk tview2 (promises lc1) (reserves lc1) (free_promises lc1) (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) (Global.promises gl1) (Global.free_promises gl1) mem2):
      alloc_step lc1 gl1 loc size lc2 gl2
  .
  #[global] Hint Constructors alloc_step: core.

  Fixpoint locs loc size: list Loc.t :=
    match size with
    | O => []
    | S size' => loc :: locs (Loc.mk (Loc.tid loc) (Loc.bid loc) ((Loc.ofs loc) + 1)) size'
    end.
  
  Lemma locs_in_inv
    loc1 loc2 size
    (IN: List.In loc1 (locs loc2 size)):
    Loc.tid loc1 = Loc.tid loc2 /\ Loc.bid loc1 = Loc.bid loc2 /\
    (Loc.ofs loc2 <= Loc.ofs loc1 < Loc.ofs loc2 + (Z.of_nat size))%Z.
  Proof.
    generalize dependent loc2. revert loc1.
    induction size; i; ss. des.
    - subst. esplits; eauto; nia.
    - exploit IHsize; eauto. i. ss. des. esplits; eauto; nia.
  Qed.

  Lemma locs_in
        loc1 loc2 size
        (TIDE: Loc.tid loc1 = Loc.tid loc2)
        (BID: Loc.bid loc1 = Loc.bid loc2)
        (OFS: (Loc.ofs loc2 <= Loc.ofs loc1 < Loc.ofs loc2 + (Z.of_nat size))%Z):
    List.In loc1 (locs loc2 size).
  Proof.
    generalize dependent loc2. revert loc1.
    induction size; i; ss; try nia. des.
    eapply Zle_lt_or_eq in OFS. des.
    - right. eapply IHsize; eauto. ss. nia.
    - left. destruct loc1, loc2. ss. subst. eauto.
  Qed.

  Lemma locs_nodup
        loc size:
    List.NoDup (locs loc size).
  Proof.
    revert loc. induction size; i; ss; try by econs.
    econs; eauto. ii. exploit locs_in_inv; eauto. i. ss. des. nia.
  Qed.

  Variant free_step
          (lc1: t) (gl1: Global.t)
          (loc: Loc.t) (size: Z)
          (lc2: t) (gl2: Global.t): Prop :=
  | free_step_intro
      mem2 prm2 gprm2 fprm2 gfprm2
      (FREE: Memory.free (Global.memory gl1) loc mem2)
      (SIZE: Some size = Memory.get_size loc (Global.memory gl1))
      (FULFILLS: Promises.fulfills (promises lc1) (Global.promises gl1) (locs loc (Z.to_nat size))
                                  Ordering.na prm2 gprm2)
      (FULFILL: FreePromises.sfulfill (free_promises lc1) (Global.free_promises gl1)
                                          (Loc.get_tbid loc) fprm2 gfprm2)
      (LC2: lc2 = mk (tview lc1) prm2 (reserves lc1) fprm2 (tid lc1))
      (GL2: gl2 = Global.mk (Global.sc gl1) gprm2 gfprm2 mem2)
  .
  #[global] Hint Constructors free_step: core.

  Variant ptr_eq_step
          (lc1: Local.t) (gl1: Global.t)
          (loc1 loc2: Loc.t) (valret: bool): Prop :=
  | ptr_eq_step_same_block
      (BlOCK: TBid.eq_dec (Loc.get_tbid loc1) (Loc.get_tbid loc2))
      (EQ: valret = Z.eqb (Loc.ofs loc1) (Loc.ofs loc2)):
      ptr_eq_step lc1 gl1 loc1 loc2 valret
  | ptr_eq_step_diff_block
      (BlOCK: ~ TBid.eq_dec (Loc.get_tbid loc1) (Loc.get_tbid loc2))
      (EQ: valret = false):
      ptr_eq_step lc1 gl1 loc1 loc2 valret
  .
  #[global] Hint Constructors ptr_eq_step: core.

  Variant is_racy (lc1: t) (gl1: Global.t) (loc: Loc.t): forall (to: option Time.t) (ord: Ordering.t) (racy_prm: bool), Prop :=
  | is_racy_promise
      ord
      (GET: (Global.promises gl1) loc = true)
      (GETP: (promises lc1) loc = false):
    is_racy lc1 gl1 loc None ord true
  | is_racy_message
      to from val released na ord
      (GET: Memory.get loc to (Global.memory gl1) = Some (from, Message.message val released na))
      (RACE: TView.racy_view (TView.cur (tview lc1)) loc to)
      (MSG: Ordering.le Ordering.relaxed ord -> na = true):
    is_racy lc1 gl1 loc (Some to) ord false
  .
  #[global] Hint Constructors is_racy: core.

  Variant racy_read_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (to: option Time.t)
    (val:Val.t) (ord:Ordering.t) (racy_prm: bool): Prop :=
  | racy_read_step_race
      (RACE: is_racy lc1 gl1 loc to ord racy_prm).
  #[global] Hint Constructors racy_read_step: core.

  Variant racy_write_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (to: option Time.t)
    (ord: Ordering.t) (racy_prm: bool): Prop :=
  | racy_write_step_race
      (RACE: is_racy lc1 gl1 loc to ord racy_prm).
  #[global] Hint Constructors racy_write_step: core.

  Variant racy_faa_step (lc1: t) (gl1: Global.t) (loc: Loc.t):
    forall (to: option Time.t) (ordr ordw: Ordering.t) (racy_prm: bool), Prop :=
  | racy_faa_step_ordr
      ordr ordw
      (ORDR: Ordering.le ordr Ordering.na):
    racy_faa_step lc1 gl1 loc None ordr ordw false
  | racy_faa_step_ordw
      ordr ordw
      (ORDW: Ordering.le ordw Ordering.na):
    racy_faa_step lc1 gl1 loc None ordr ordw false
  | racy_faa_step_race
      to ordr ordw racy_prm
      (RACE: is_racy lc1 gl1 loc to ordr racy_prm):
    racy_faa_step lc1 gl1 loc to ordr ordw racy_prm
  .
  #[global] Hint Constructors racy_faa_step: core.

  Variant racy_cas_step (lc1: t) (gl1: Global.t) (loc: Loc.t):
    forall (to: option Time.t) (ordr ordw: Ordering.t) (racy_prm: bool), Prop :=
  | racy_cas_step_ordr
      ordr ordw
      (ORDR: Ordering.le ordr Ordering.na):
    racy_cas_step lc1 gl1 loc None ordr ordw false
  | racy_cas_step_ordw
      ordr ordw
      (ORDW: Ordering.le ordw Ordering.na):
    racy_cas_step lc1 gl1 loc None ordr ordw false
  | racy_cas_step_race
      to ordr ordw racy_prm
      (RACE: is_racy lc1 gl1 loc to ordr racy_prm):
    racy_cas_step lc1 gl1 loc to ordr ordw racy_prm
  .
  #[global] Hint Constructors racy_cas_step: core.

  Variant racy_free_step (lc1: t) (gl1: Global.t) (loc: Loc.t) (size: Z) (racy_prm: bool): Prop :=
  | racy_free_race
      to
      (STATE: Memory.is_freeable loc (Global.memory gl1))
      (SIZE: Some size = Memory.get_size loc (Global.memory gl1))
      (OFS: Loc.ofs loc = 0%Z)
      (RACE: exists ofs, (0 <= ofs < size)% Z /\
                    is_racy lc1 gl1 (Loc.mk (Loc.tid loc) (Loc.bid loc) ofs) to Ordering.na racy_prm).
  #[global] Hint Constructors racy_free_step: core.
  
  Variant is_inaccessible (lc: t) (gl: Global.t) (loc: Loc.t): forall (racy_prm: bool), Prop :=
  | is_inaccessible_promise
      (FREEPROMISE: FreePromises.minus (Global.free_promises gl) (free_promises lc) (Loc.get_tbid loc)):
    is_inaccessible lc gl loc true
  | is_inaccessible_state
      (INACCESSIBLE: ~ Memory.accessible loc (Global.memory gl)):
    is_inaccessible lc gl loc false
  | is_inaccessible_alloc_view
      (ALLOC_VIEW: ~ (View.alloc_view (TView.cur (tview lc))) (Loc.get_tbid loc)):
    is_inaccessible lc gl loc false
  .

  (* Pointer comparison in CAS may not sync with allocation *)
  Variant is_inaccessible_weak (lc: t) (gl: Global.t) (loc: Loc.t): forall (racy_prm: bool), Prop :=
  | is_inaccessible_weak_promise
      (FREEPROMISE: FreePromises.minus (Global.free_promises gl) (free_promises lc) (Loc.get_tbid loc)):
    is_inaccessible_weak lc gl loc true
  | is_inaccessible_weak_state
      (INACCESSIBLE: ~ Memory.accessible loc (Global.memory gl)):
    is_inaccessible_weak lc gl loc false.

  Variant inaccessible_free_step (lc1: t) (gl1: Global.t) (loc: Loc.t): forall (size: Z) (racy_prm: bool), Prop :=
  | inaccessible_free_step_inaccessible
      size racy_prm
      (STATE: Memory.is_freeable loc (Global.memory gl1))
      (SIZE: Some size = Memory.get_size loc (Global.memory gl1))
      (OFS: Loc.ofs loc = 0%Z)
      (RACE: (exists ofs, (0 <= ofs < size)%Z /\
                     is_inaccessible lc1 gl1 (Loc.mk (Loc.tid loc) (Loc.bid loc) ofs) racy_prm) \/
             (FreePromises.minus (Global.free_promises gl1) (free_promises lc1) (Loc.get_tbid loc) /\ racy_prm = true)):
    inaccessible_free_step lc1 gl1 loc size racy_prm
  | inaccessible_free_step_wrong
      (WRONG_FREE: (Loc.ofs loc <> 0)%Z \/
                   ~ (Memory.is_freeable loc (Global.memory gl1)) \/
                   ~ (View.alloc_view (TView.cur (tview lc1))) (Loc.get_tbid loc)):
    inaccessible_free_step lc1 gl1 loc 0 false
  .
  #[global] Hint Constructors inaccessible_free_step: core.

  Variant inaccessible_ptr_eq_step
          (lc1: Local.t) (gl1: Global.t) (loc1 loc2: Loc.t) (racy_prm: bool): Prop :=
  | racy_ptr_eq_step_race1
      (BLOCK: ~ TBid.eq_dec (Loc.get_tbid loc1) (Loc.get_tbid loc2))
      (RACE: is_inaccessible lc1 gl1 loc1 racy_prm)
  | racy_ptr_eq_step_race2
      (BLOCK: ~ TBid.eq_dec (Loc.get_tbid loc1) (Loc.get_tbid loc2))
      (RACE: is_inaccessible lc1 gl1 loc2 racy_prm).
  #[global] Hint Constructors inaccessible_ptr_eq_step: core.

  Variant inaccessible_weak_ptr_eq_step
          (lc1: Local.t) (gl1: Global.t) (loc1 loc2: Loc.t) (racy_prm: bool): Prop :=
  | weak_racy_ptr_eq_step_race1
      (BLOCK: ~ TBid.eq_dec (Loc.get_tbid loc1) (Loc.get_tbid loc2))
      (RACE: is_inaccessible_weak lc1 gl1 loc1 racy_prm)
  | weak_racy_ptr_eq_step_race2
      (BLOCK: ~ TBid.eq_dec (Loc.get_tbid loc1) (Loc.get_tbid loc2))
      (RACE: is_inaccessible_weak lc1 gl1 loc2 racy_prm).

  Variant val_eq_mem (lc: t) (gl: Global.t): forall (v1 v2: Val.t) (valret: option bool) (racy_prm: bool), Prop :=
  | num_eq
      n1 n2:
    val_eq_mem lc gl (Val.Vnum n1) (Val.Vnum n2) (Some (Z.eqb n1 n2)) false
  | ptr_eq
      loc1 loc2 valret
      (CMP: ptr_eq_step lc gl loc1 loc2 valret):
    val_eq_mem lc gl (Val.Vptr loc1) (Val.Vptr loc2) (Some valret) false
  | racy_ptr_eq
      loc1 loc2 racy_prm
      (CMP: inaccessible_ptr_eq_step lc gl loc1 loc2 racy_prm):
    val_eq_mem lc gl (Val.Vptr loc1) (Val.Vptr loc2) None racy_prm
  | other_eq
      v1 v2
      (VAL: match v1, v2 with
            | Val.Vnum _, Val.Vnum _
            | Val.Vptr _, Val.Vptr _ => False
            | _, _ => True
            end):
    val_eq_mem lc gl v1 v2 None false.

  Variant weak_val_eq_mem (lc: t) (gl: Global.t): forall (v1 v2: Val.t) (valret: option bool) (racy_prm: bool), Prop :=
  | weak_num_eq
      n1 n2:
    weak_val_eq_mem lc gl (Val.Vnum n1) (Val.Vnum n2) (Some (Z.eqb n1 n2)) false
  | weak_ptr_eq
      loc1 loc2 valret
      (CMP: ptr_eq_step lc gl loc1 loc2 valret):
    weak_val_eq_mem lc gl (Val.Vptr loc1) (Val.Vptr loc2) (Some valret) false
  | weak_racy_ptr_eq
      loc1 loc2 racy_prm
      (CMP: inaccessible_weak_ptr_eq_step lc gl loc1 loc2 racy_prm):
    weak_val_eq_mem lc gl (Val.Vptr loc1) (Val.Vptr loc2) None racy_prm
  | weak_other_eq
      v1 v2
      (VAL: match v1, v2 with
            | Val.Vnum _, Val.Vnum _
            | Val.Vptr _, Val.Vptr _ => False
            | _, _ => True
            end):
    weak_val_eq_mem lc gl v1 v2 None false.

  Variant inaccessible_cmp_cas_step
          (lc1: t) (gl1: Global.t) (loc: Loc.t) (valr valc: Val.t) (released: View.t)
          (ord: Ordering.t) (racy_prm: bool) (to: Time.t) (lc2: t): Prop :=
  | inaccessible_cmp_cas_intro
      (LOCAL: read_step lc1 gl1 loc to valr released ord lc2)
      (COMPARE: weak_val_eq_mem lc2 gl1 valr valc None racy_prm)
  .

  Variant internal_step:
    forall (e: ThreadEvent.t) (lc1: t) (gl1: Global.t) (lc2: t) (gl2: Global.t), Prop :=
  | internal_step_promise
      lc1 gl1
      loc lc2 gl2
      (LOCAL: promise_step lc1 gl1 loc lc2 gl2):
    internal_step (ThreadEvent.promise loc) lc1 gl1 lc2 gl2
  | internal_step_reserve
      lc1 gl1
      loc from to lc2 gl2
      (LOCAL: reserve_step lc1 gl1 loc from to lc2 gl2):
    internal_step (ThreadEvent.reserve loc from to) lc1 gl1 lc2 gl2
  | internal_step_cancel
      lc1 gl1
      loc from to lc2 gl2
      (LOCAL: cancel_step lc1 gl1 loc from to lc2 gl2):
    internal_step (ThreadEvent.cancel loc from to) lc1 gl1 lc2 gl2
  | internal_step_free_promise
      lc1 gl1
      tbid lc2 gl2
      (LOCAL: free_promise_step lc1 gl1 tbid lc2 gl2):
    internal_step (ThreadEvent.free_promise tbid) lc1 gl1 lc2 gl2
  .
  #[global] Hint Constructors internal_step: core.

  Variant program_step:
    forall (e: ThreadEvent.t) (lc1: t) (gl1: Global.t) (lc2: t) (gl2: Global.t), Prop :=
  | program_step_silent
      lc1 gl1:
    program_step ThreadEvent.silent lc1 gl1 lc1 gl1
  | program_step_read
      lc1 gl1
      loc to val released ord lc2
      (LOCAL: read_step lc1 gl1 loc to val released ord lc2):
    program_step (ThreadEvent.read loc to val released ord) lc1 gl1 lc2 gl1
  | program_step_write
      lc1 gl1
      loc from to val released ord lc2 gl2
      (LOCAL: write_step lc1 gl1 loc from to val View.bot released ord lc2 gl2):
    program_step (ThreadEvent.write loc from to val released ord) lc1 gl1 lc2 gl2
  | program_step_faa
      lc1 gl1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw addendum lc3 gl3
      (LOCAL1: read_step lc1 gl1 loc tsr valr releasedr ordr lc2)
      (LOCAL2: write_step lc2 gl1 loc tsr tsw (Val.add valr addendum) releasedr releasedw ordw lc3 gl3):
    program_step (ThreadEvent.faa loc tsr tsw valr addendum releasedr releasedw ordr ordw)
      lc1 gl1 lc3 gl3
  | program_step_cas_success
      lc1 gl1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw lc3 gl3
      valc
      (LOCAL1: read_step lc1 gl1 loc tsr valr releasedr ordr lc2)
      (COMPARE: weak_val_eq_mem lc2 gl1 valr valc (Some true) false)
      (LOCAL2: write_step lc2 gl1 loc tsr tsw valw releasedr releasedw ordw lc3 gl3):
    program_step (ThreadEvent.cas loc tsr tsw valr valc valw (Some true) releasedr releasedw ordr ordw)
      lc1 gl1 lc3 gl3
  | program_step_cas_fail
      lc1 gl1
      loc ordr ordw
      tsr valr releasedr releasedw lc2
      tsw valw
      valc
      (LOCAL1: read_step lc1 gl1 loc tsr valr releasedr ordr lc2)
      (COMPARE: weak_val_eq_mem lc2 gl1 valr valc (Some false) false):
    program_step (ThreadEvent.cas loc tsr tsw valr valc valw (Some false) releasedr releasedw ordr ordw)
      lc1 gl1 lc2 gl1
  | program_step_fence
      lc1 gl1
      ordr ordw lc2 gl2
      (LOCAL: fence_step lc1 gl1 ordr ordw lc2 gl2):
    program_step (ThreadEvent.fence ordr ordw) lc1 gl1 lc2 gl2
  | program_step_syscall
      lc1 gl1
      e lc2 gl2
      (LOCAL: fence_step lc1 gl1 Ordering.seqcst Ordering.seqcst lc2 gl2):
    program_step (ThreadEvent.syscall e) lc1 gl1 lc2 gl2
  | program_step_failure
      lc1 gl1
      (LOCAL: failure_step lc1):
    program_step ThreadEvent.failure lc1 gl1 lc1 gl1
  | program_step_alloc
      lc1 gl1
      size loc
      lc2 gl2
      (LOCAL: alloc_step lc1 gl1 loc size lc2 gl2):
    program_step (ThreadEvent.alloc loc size) lc1 gl1 lc2 gl2
  | program_step_free
      lc1 gl1
      loc size
      lc2 gl2
      (LOCAL: free_step lc1 gl1 loc size lc2 gl2):
    program_step (ThreadEvent.free loc size) lc1 gl1 lc2 gl2
  | program_step_ptr_eq
      lc1 gl1
      loc1 loc2 valret
      (LOCAL: ptr_eq_step lc1 gl1 loc1 loc2 valret):
    program_step (ThreadEvent.ptr_eq loc1 loc2 valret) lc1 gl1 lc1 gl1
  | program_step_racy_read
      lc1 gl1
      loc to val ord racy_prm
      (LOCAL: racy_read_step lc1 gl1 loc to val ord racy_prm):
    program_step (ThreadEvent.racy_read loc to val ord racy_prm) lc1 gl1 lc1 gl1
  | program_step_racy_write
      lc1 gl1
      loc to val ord racy_prm
      (LOCAL: racy_write_step lc1 gl1 loc to ord racy_prm):
    program_step (ThreadEvent.racy_write loc to val ord racy_prm) lc1 gl1 lc1 gl1
  | program_step_racy_faa
      lc1 gl1
      loc to valr valw ordr ordw racy_prm
      (LOCAL: racy_faa_step lc1 gl1 loc to ordr ordw racy_prm):
    program_step (ThreadEvent.racy_faa loc to valr valw ordr ordw racy_prm) lc1 gl1 lc1 gl1
  | program_step_racy_cas
      lc1 gl1
      loc to valr valw valc valret ordr ordw racy_prm
      (LOCAL: racy_cas_step lc1 gl1 loc to ordr ordw racy_prm):
    program_step (ThreadEvent.racy_cas loc to valr valc valw valret ordr ordw racy_prm)
      lc1 gl1 lc1 gl1
  | program_step_racy_free
      lc1 gl1 loc size racy_prm
      (LOCAL: racy_free_step lc1 gl1 loc size racy_prm):
    program_step (ThreadEvent.racy_free loc size racy_prm) lc1 gl1 lc1 gl1
  | program_step_inaccessible_read
      lc1 gl1
      loc val ord racy_prm
      (RACE: is_inaccessible lc1 gl1 loc racy_prm):
    program_step (ThreadEvent.inaccessible_read loc val ord racy_prm) lc1 gl1 lc1 gl1
  | program_step_inaccessible_write
      lc1 gl1
      loc val ord racy_prm
      (RACE: is_inaccessible lc1 gl1 loc racy_prm):
    program_step (ThreadEvent.inaccessible_write loc val ord racy_prm) lc1 gl1 lc1 gl1
  | program_step_inaccessible_faa
      lc1 gl1
      loc valr valw ordr ordw racy_prm
      (RACE: is_inaccessible lc1 gl1 loc racy_prm):
    program_step (ThreadEvent.inaccessible_faa loc valr valw ordr ordw racy_prm) lc1 gl1 lc1 gl1
  | program_step_inaccessible_cas
      lc1 gl1
      loc valr valw valc valret ordr ordw racy_prm
      (RACE: is_inaccessible lc1 gl1 loc racy_prm):
    program_step (ThreadEvent.inaccessible_cas loc valr valc valw valret ordr ordw racy_prm) lc1 gl1 lc1 gl1
  | program_step_inaccessible_cmp_cas
      lc1 gl1 lc2
      loc to valr valw valc valret released ordr ordw racy_prm
      (LOCAL: inaccessible_cmp_cas_step lc1 gl1 loc valr valc released ordr racy_prm to lc2):
    program_step (ThreadEvent.inaccessible_cmp_cas loc to valr valc valw valret released ordr ordw racy_prm) lc1 gl1 lc2 gl1
  | program_step_inaccessible_free
      lc1 gl1
      loc size racy_prm
      (LOCAL: inaccessible_free_step lc1 gl1 loc size racy_prm):
    program_step (ThreadEvent.inaccessible_free loc size racy_prm) lc1 gl1 lc1 gl1
  | program_step_inaccessible_ptr_eq
      lc1 gl1
      loc1 loc2 valret racy_prm
      (LOCAL: inaccessible_ptr_eq_step lc1 gl1 loc1 loc2 racy_prm):
    program_step (ThreadEvent.inaccessible_ptr_eq loc1 loc2 valret racy_prm) lc1 gl1 lc1 gl1
  .
  #[global] Hint Constructors program_step: core.

  (* step_preserve *)
  Lemma internal_step_preserve
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    <<NEQ: Local.tid lc2 = Local.tid lc1>> /\
    <<NEXTBID: forall tid, Memory.next_bid (Global.memory gl2) tid =
                      Memory.next_bid (Global.memory gl1) tid>>.
  Proof.
    inv STEP; inv LOCAL; ss.
    - inv RESERVE. inv MEM. ss.
    - inv CANCEL. inv MEM. ss.
  Qed.
  
  Lemma internal_step_preserve2
        e lc1 gl1 lc2 gl2 loc
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    Memory.get_state loc gl2.(Global.memory) = Memory.get_state loc gl1.(Global.memory).
  Proof.
    inv STEP; inv LOCAL; ss.
    - inv RESERVE. eapply Memory.add_preserve; eauto.
    - inv CANCEL. eapply Memory.remove_preserve; eauto.
  Qed.

  Lemma program_step_preserve
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2):
    <<NEQ: Local.tid lc2 = Local.tid lc1>> /\
    <<NEXTBID: forall tid, Local.tid lc1 <> tid ->
                      Memory.next_bid (Global.memory gl2) tid =
                      Memory.next_bid (Global.memory gl1) tid>>.
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL. inv WRITE. ss.
    - inv LOCAL1. inv LOCAL2. inv WRITE. ss.
    - inv LOCAL1. inv LOCAL2. inv WRITE. ss.
    - inv LOCAL1. ss.
    - inv LOCAL. inv ALLOC. ss. esplits; ss. i. condtac; congruence.
    - inv LOCAL. inv FREE. ss.
    - inv LOCAL; ss. inv LOCAL0; ss.
  Qed.

  (* step_future *)

  Lemma promise_step_future
        lc1 gl1 loc lc2 gl2
        (STEP: promise_step lc1 gl1 loc lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Promises.promise_le; eauto. i.
    hexploit Promises.promise_finite; eauto. i.
    splits; ss; try refl.
    econs; try refl. econs; ss. eapply Memory.messages_le_PreOrder.
  Qed.

  Lemma free_promise_step_future
        lc1 gl1 loc lc2 gl2
        (STEP: free_promise_step lc1 gl1 loc lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit FreePromises.promise_le; eauto. i.
    hexploit FreePromises.promise_finite; eauto. i.
    splits; ss; try refl.
    econs; try refl. econs; ss. eapply Memory.messages_le_PreOrder.
  Qed.

  Lemma reserve_step_future
        lc1 gl1 loc from to lc2 gl2
        (STEP: reserve_step lc1 gl1 loc from to lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Memory.reserve_future; eauto. i. des.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { inv RESERVE. exploit Memory.add_preserve; eauto. i. des. specialize (GET_STATE loc0).
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite <- GET_STATE. eauto.
    }
    splits; try refl.
    - econs; ss; eauto.
      + eapply TView.future_closed; eauto.
    - econs; ss.
      + eapply Memory.future_closed_view; eauto.
      + eapply FUTURE.
      + eapply Memory.add_well_alloced; eauto. inv RESERVE. eauto.
    - econs; eauto. refl.
  Qed.

  Lemma cancel_step_future
        lc1 gl1 loc from to lc2 gl2
        (STEP: cancel_step lc1 gl1 loc from to lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Memory.cancel_future; eauto. i. des.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { inv CANCEL. exploit Memory.remove_preserve; eauto. i. des. specialize (GET_STATE loc0).
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite <- GET_STATE. eauto.
    }
    splits; try refl.
    - econs; ss; eauto.
      + eauto using TView.future_closed.
    - econs; ss.
      + eauto using Memory.future_closed_view.
      + eapply FUTURE.
      + eapply Memory.remove_well_alloced; eauto. inv CANCEL. eauto.
    - econs; eauto. refl.
  Qed.

  Lemma read_step_future
        lc1 gl1 loc ts val released ord lc2
        (STEP: read_step lc1 gl1 loc ts val released ord lc2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl1>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<REL_CLOSED: Memory.closed_view released (Global.memory gl1)>> /\
    <<REL_TS: Time.le ((View.rlx released) loc) ts>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    dup MEM_CLOSED. inv MEM_CLOSED0. exploit CLOSED; eauto. i. des.
    inv MSG_CLOSED. inv MSG_TS.
    exploit TViewFacts.read_future; try exact GET; eauto.
    { unfold Memory.accessible, Block.accessible, Memory.is_prealloced, Block.is_prealloced in *.
      des_ifs.
    }
    i. des. splits; auto.
    - econs; ss; eauto.
    - apply TViewFacts.read_tview_incr.
  Qed.

  Lemma write_step_future
        lc1 gl1 loc from to val releasedm released ord lc2 gl2
        (STEP: write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2)
        (REL_CLOSED: Memory.closed_view releasedm (Global.memory gl1))
        (REL_TS: Time.le ((View.rlx releasedm) loc) to)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>> /\
    <<REL_TS: Time.le ((View.rlx released) loc) to>> /\
    <<REL_CLOSED: Memory.closed_view released (Global.memory gl2)>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    hexploit Promises.fulfill_le; try exact FULFILL; eauto. i.
    hexploit Promises.fulfill_finite; try exact FULFILL; eauto. i.
    exploit TViewFacts.write_future; try eapply WRITE; eauto.
    { unfold Memory.accessible, Block.accessible, Memory.is_prealloced, Block.is_prealloced in *.
      des_ifs.
    }
    s. i. des.
    exploit Memory.add_future; try apply WRITE; eauto.
    { econs. eapply TViewFacts.write_released_ts; eauto. }
    i. des.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { exploit Memory.add_preserve; eauto. i. des. specialize (GET_STATE loc0).
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite <- GET_STATE. eauto.
    }
    exploit Memory.add_get0; try apply WRITE; eauto. i. des.
    splits; eauto.
    - econs; ss.
      + eapply Memory.future_closed_view; eauto.
      + eapply FUTURE.
      + eapply Memory.add_well_alloced; eauto.
    - apply TViewFacts.write_tview_incr. auto.
    - econs; eauto. refl.
    - eapply TViewFacts.write_released_ts; eauto.
  Qed.

  Lemma faa_step_future
        lc1 gl1 loc ts val1 released1 ordr lc2
        to val2 released2 ordw lc3 gl3
        (READ: read_step lc1 gl1 loc ts val1 released1 ordr lc2)
        (WRITE: write_step lc2 gl1 loc ts to val2 released1 released2 ordw lc3 gl3)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc3 gl3>> /\
    <<GL_WF2: Global.wf gl3>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl3>> /\
    <<REL_TS: Time.le ((View.rlx released2) loc) to>> /\
    <<REL_CLOSED: Memory.closed_view released2 (Global.memory gl3)>>.
  Proof.
    exploit read_step_future; eauto. i. des.
    exploit write_step_future; eauto.
    { etrans; eauto. econs.
      inv WRITE. eapply Memory.add_ts; eauto.
    }
    i. des.
    esplits; eauto.
  Qed.

  Lemma fence_step_future
        lc1 gl1 ordr ordw lc2 gl2
        (STEP: fence_step lc1 gl1 ordr ordw lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    exploit TViewFacts.read_fence_future; eauto. i. des.
    exploit TViewFacts.write_fence_future; eauto. i. des.
    assert (LE: TView.le (tview lc1)
                  (TView.write_fence_tview (TView.read_fence_tview (tview lc1) ordr) (Global.sc gl1) ordw)).
    { etrans. eapply TViewFacts.read_fence_tview_incr; eauto.
      eapply TViewFacts.write_fence_tview_incr; eauto. }
    splits; eauto.
    econs; try refl.
    apply TViewFacts.write_fence_sc_incr.
    econs; ss. eapply Memory.messages_le_PreOrder.
  Qed.

  Lemma alloc_step_future
        lc1 gl1 loc size lc2 gl2
        (STEP: alloc_step lc1 gl1 loc size lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { i. inv ALLOC. unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *. ss.
      revert H. condtac; ss.
    }
    splits; eauto.
    - exploit TViewFacts.alloc_tview_future; eauto. i. des. econs; eauto; ss.
      etrans; try eapply RESERVES. eapply Memory.alloc_le; eauto.
    - econs; ss; eauto.
      + eapply Memory.alloc_closed_view; eauto.
      + eapply Memory.alloc_closed; eauto.
      + eapply Memory.alloc_well_alloced; eauto.
    - unfold TView.alloc_tview. econs; ss; try refl; apply View.join_l.
    - econs; eauto; try refl. econs.
      + eapply Memory.alloc_messages_le; eauto.
      + eapply Memory.alloc_closed; eauto.
      + eapply Memory.alloc_well_alloced; eauto.
  Qed.

  Lemma free_step_future
        lc1 gl1 loc size lc2 gl2
        (STEP: free_step lc1 gl1 loc size lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv LC_WF1. inv GL_WF1. inv STEP. ss.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { i. inv FREE. unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *. ss.
      revert H. condtac; ss.
    }
    splits; eauto.
    - econs; ss.
      + eapply TView.le_closed; eauto. eapply Memory.free_messages_le; eauto.
      + eapply Promises.fulfills_le; eauto.
      + eapply Promises.fulfills_finite; eauto.
      + eapply FreePromises.sfulfill_le; eauto.
      + eapply FreePromises.sfulfill_finite; eauto.
      + etrans; eauto. eapply Memory.free_le; eauto.
    - econs; ss; eauto.
      + eapply Memory.free_closed_view; eauto.
      + eapply Memory.free_closed; eauto.
      + eapply Memory.free_well_alloced; eauto.
    - refl.
    - econs; eauto; try refl. econs.
      + eapply Memory.free_messages_le; eauto.
      + eapply Memory.free_closed; eauto.
      + eapply Memory.free_well_alloced; eauto.
  Qed.

  Lemma internal_step_future
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv STEP.
    - eapply promise_step_future; eauto.
    - eapply reserve_step_future; eauto.
    - eapply cancel_step_future; eauto.
    - eapply free_promise_step_future; eauto.
  Qed.

  Lemma program_step_future
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.future gl1 gl2>>.
  Proof.
    inv STEP; try by (splits; eauto; try refl; eapply Global.future_refl; eauto).
    - exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl. eapply Global.future_refl; eauto.
    - exploit write_step_future; eauto;
        try apply Time.bot_spec; try apply Memory.closed_view_bot. i. des.
      esplits; eauto; try refl.
    - exploit read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs.
      { etrans; eauto. inv LOCAL2.
        econs. eauto using Memory.add_ts.
      }
      i. des.
      esplits; eauto; etrans; eauto.
    - exploit read_step_future; eauto. i. des.
      exploit write_step_future; eauto; try by econs.
      { etrans; eauto. inv LOCAL2.
        econs. eauto using Memory.add_ts.
      }
      i. des.
      esplits; eauto; etrans; eauto.
    - exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl. eapply Global.future_refl; eauto.
    - exploit fence_step_future; eauto.
    - exploit fence_step_future; eauto.
    - exploit alloc_step_future; eauto.
    - exploit free_step_future; eauto.
    - inv LOCAL. exploit read_step_future; eauto. i. des.
      esplits; eauto; try refl. eapply Global.future_refl; eauto.
  Qed.

  (* step_strong_future *)

  Lemma promise_step_strong_future
        lc1 gl1 loc lc2 gl2
        (STEP: promise_step lc1 gl1 loc lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit promise_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. left. inv STEP. ss. inv PROMISE. inv GADD.
      change (Promises.AFun.add loc true (Global.promises gl1) loc0) with
        (LocFun.find loc0 (LocFun.add loc true (Global.promises gl1))).
      rewrite LocFun.add_spec. des_ifs. rewrite Bool.implb_same. auto.
    }
    { econs. i. left. inv STEP. ss. rewrite Bool.implb_same. auto. }
  Qed.

  Lemma reserve_step_strong_future
        lc1 gl1 loc from to lc2 gl2
        (STEP: reserve_step lc1 gl1 loc from to lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit reserve_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
  Qed.

  Lemma cancel_step_strong_future
        lc1 gl1 loc from to lc2 gl2
        (STEP: cancel_step lc1 gl1 loc from to lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit cancel_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
  Qed.

  Lemma free_promise_step_strong_future
        lc1 gl1 tbid lc2 gl2
        (STEP: free_promise_step lc1 gl1 tbid lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit free_promise_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
    { econs. i. left. inv STEP. ss. inv PROMISE. inv GADD.
      change (FreePromises.AFun.add tbid true (Global.free_promises gl1) (Loc.get_tbid loc)) with
        (FreePromises.AFun.find (Loc.get_tbid loc) (FreePromises.AFun.add tbid true (Global.free_promises gl1))).
      rewrite FreePromises.AFun.add_spec. des_ifs. rewrite Bool.implb_same. auto.
    }
  Qed.

  Lemma write_step_strong_future
        lc1 gl1 loc from to val releasedm released ord lc2 gl2
        (STEP: write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2)
        (REL_CLOSED: Memory.closed_view releasedm (Global.memory gl1))
        (REL_TS: Time.le (View.rlx releasedm loc) to)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>> /\
    <<REL_TS: Time.le ((View.rlx released) loc) to>> /\
    <<REL_CLOSED: Memory.closed_view released (Global.memory gl2)>>
    \/
    exists ts racy_prm, <<NA: Ordering.le ord Ordering.na>> /\ <<RACE: is_racy lc1 gl1 loc ts ord racy_prm>>
  .
  Proof.
    destruct (classic (exists ts racy_prm, Ordering.le ord Ordering.na /\ is_racy lc1 gl1 loc ts ord racy_prm)) as [RACE|SAFE]; auto.
    left. hexploit write_step_future; eauto. i. des.
    esplits; eauto. econs; eauto.
    { econs. i. inv STEP. ss. inv FULFILL; ss.
      { left. rewrite Bool.implb_same. auto. }
      inv GREMOVE.
      change (Promises.AFun.add loc false (Global.promises gl1) loc0) with
        (LocFun.find loc0 (LocFun.add loc false (Global.promises gl1))).
      rewrite LocFun.add_spec. condtac.
      { subst. right. left. repeat red. esplits.
        { inv ORD. rewrite H0 in WRITE. rewrite H0. eapply Memory.add_get0; eauto. }
        i. destruct (Time.le_lt_dec to ts1); auto. exfalso.
        eapply SAFE. esplits.
        { destruct ord; ss. }
        econs 2.
        { eauto. }
        { unfold TView.racy_view.
          eapply TimeFacts.lt_le_lt; eauto.
          inv WRITABLE. eauto.
        }
        { destruct ord; ss. }
      }
      { rewrite Bool.implb_same. auto. }
    }
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
  Qed.

  Lemma fence_step_strong_future
        lc1 gl1 ordr ordw lc2 gl2
        (STEP: fence_step lc1 gl1 ordr ordw lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit fence_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
  Qed.

  Lemma alloc_step_strong_future
        lc1 gl1 loc size lc2 gl2
        (STEP: alloc_step lc1 gl1 loc size lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit alloc_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
    { econs. i. left. inv STEP. rewrite Bool.implb_same. auto. }
  Qed.

  Lemma free_step_strong_future
        lc1 gl1 loc size lc2 gl2
        (STEP: free_step lc1 gl1 loc size lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    hexploit free_step_future; eauto. i. des. esplits; eauto. econs; eauto.
    { econs. i. inv STEP. ss. inv FREE. ss.
      unfold Memory.is_freeable, Block.is_freeable, Memory.is_freed, Block.is_freed in *. ss.
      destruct (classic (Loc.get_tbid loc0 = (Some tid0, bid))).
      - right. right. econs.
        + unfold Memory.is_freed, Block.is_freed, Loc.get_tbid in *. clarify. rewrite H1. ss.
          clear - FREEABLE. des_ifs.
        + unfold Memory.is_freed, Block.is_freed, Loc.get_tbid in *. clarify. rewrite H1. ss.
          condtac; ss. des; congruence.
      - left. exploit (@Promises.fulfills_inv_not_in _ _ _ _ _ _ loc0); eauto.
        { ii. eapply locs_in_inv in H0. ss. des; ss. unfold Loc.get_tbid in H. congruence. }
        i. desH x0. rewrite x1. rewrite Bool.implb_same. eauto.
    }
    { econs. i. inv STEP. ss. inv FREE. ss.
      unfold Memory.is_freeable, Block.is_freeable, Memory.is_freed, Block.is_freed in *. ss.
      destruct (classic (Loc.get_tbid loc0 = (Some tid0, bid))).
      - right. econs.
        + unfold Memory.is_freed, Block.is_freed, Loc.get_tbid in *. clarify. rewrite H1. ss.
          clear - FREEABLE. des_ifs.
        + unfold Memory.is_freed, Block.is_freed, Loc.get_tbid in *. clarify. rewrite H1. ss.
          condtac; ss. des; congruence.
      - left. inv FULFILL; ss.
        + rewrite Bool.implb_same. eauto.
        + inv GREMOVE. unfold Loc.get_tbid in *. ss.
          change (FreePromises.AFun.add (Some tid0, bid) false (Global.free_promises gl1) (Loc.tid loc0, Loc.bid loc0)) with
            (FreePromises.AFun.find (Loc.tid loc0, Loc.bid loc0) (FreePromises.AFun.add (Some tid0, bid) false (Global.free_promises gl1))).
          rewrite FreePromises.AFun.add_spec. condtac; ss. rewrite Bool.implb_same. eauto.
    }
  Qed.

  Lemma internal_step_strong_future
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>>.
  Proof.
    inv STEP.
    - eapply promise_step_strong_future; eauto.
    - eapply reserve_step_strong_future; eauto.
    - eapply cancel_step_strong_future; eauto.
    - eapply free_promise_step_strong_future; eauto.
  Qed.

  Lemma program_step_strong_future
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2)
        (LC_WF1: wf lc1 gl1)
        (GL_WF1: Global.wf gl1):
    <<LC_WF2: wf lc2 gl2>> /\
    <<GL_WF2: Global.wf gl2>> /\
    <<TVIEW_FUTURE: TView.le (tview lc1) (tview lc2)>> /\
    <<GL_FUTURE: Global.strong_future gl1 gl2>> \/
    exists e_race,
      <<STEP: program_step e_race lc1 gl1 lc1 gl1>> /\
      <<EVENT: ThreadEvent.get_program_event e_race = ThreadEvent.get_program_event e>> /\
      <<RACE: ThreadEvent.get_machine_event e_race = MachineEvent.failure>>
  .
  Proof.
    inv STEP; try by (left; splits; eauto; try refl; try eapply Global.strong_future_refl).
    - left. exploit read_step_future; eauto. i. des. esplits; eauto.
      eapply Global.strong_future_refl; eauto.
    - exploit write_step_strong_future; eauto;
        try apply Time.bot_spec; try apply Memory.closed_view_bot. i. des.
      { left. esplits; eauto; try refl. }
      { right. esplits.
        { eapply program_step_racy_write. econs; eauto. }
        { ss. }
        { ss. }
      }
    - exploit read_step_future; eauto. i. des.
      exploit write_step_strong_future; eauto; try by econs.
      { etrans; eauto. inv LOCAL2.
        econs. eauto using Memory.add_ts.
      }
      i. des.
      { left. esplits; eauto. etrans; eauto. }
      { right. esplits.
        { eapply program_step_racy_faa; eauto. }
        { ss. }
        { ss. }
      }
    - exploit read_step_future; eauto. i. des.
      exploit write_step_strong_future; eauto; try by econs.
      { etrans; eauto. inv LOCAL2.
        econs. eauto using Memory.add_ts.
      }
      i. des.
      { left. esplits; eauto. etrans; eauto. }
      { right. esplits.
        { eapply program_step_racy_cas; eauto. }
        { ss. }
        { ss. }
      }
    - left. exploit read_step_future; eauto. i. des. esplits; eauto.
      eapply Global.strong_future_refl; eauto.
    - left. exploit fence_step_strong_future; eauto.
    - left. exploit fence_step_strong_future; eauto.
    - left. exploit alloc_step_strong_future; eauto.
    - left. exploit free_step_strong_future; eauto.
    - left. inv LOCAL. exploit read_step_future; eauto. i. des. esplits; eauto.
      eapply Global.strong_future_refl; eauto.
  Qed.
  
  (* step_disjoint *)

  Lemma promise_step_disjoint
        lc1 gl1 loc lc2 gl2 lc
        (STEP: promise_step lc1 gl1 loc lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    exploit Promises.promise_disjoint; eauto. i. desH x0.
    esplits; eauto.
  Qed.

  Lemma reserve_step_disjoint
        lc1 gl1 loc from to lc2 gl2 lc
        (STEP: reserve_step lc1 gl1 loc from to lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    hexploit Memory.reserve_messages_le; eauto. i.
    exploit Memory.reserve_disjoint; eauto. i. desH x0.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { inv RESERVE. exploit Memory.add_preserve; eauto. i. des. specialize (GET_STATE loc0).
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite <- GET_STATE. eauto.
    }
    esplits; eauto. econs; ss; eauto. eapply TView.le_closed; eauto.
  Qed.

  Lemma cancel_step_disjoint
        lc1 gl1 loc from to lc2 gl2 lc
        (STEP: cancel_step lc1 gl1 loc from to lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    hexploit Memory.cancel_messages_le; eauto. i.
    exploit Memory.cancel_disjoint; eauto. i. des.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { inv CANCEL. exploit Memory.remove_preserve; eauto. i. des. specialize (GET_STATE loc0).
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite <- GET_STATE. eauto.
    }
    esplits; eauto. econs; ss; eauto. eapply TView.le_closed; eauto.
  Qed.

  Lemma free_promise_step_disjoint
        lc1 gl1 loc lc2 gl2 lc
        (STEP: free_promise_step lc1 gl1 loc lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    exploit FreePromises.promise_disjoint; eauto. i. desH x0.
    esplits; eauto.
  Qed.

  Lemma read_step_disjoint
        lc1 gl1 loc ts val released ord lc2 lc
        (STEP: read_step lc1 gl1 loc ts val released ord lc2)
        (DISJOINT1: disjoint lc1 lc):
    disjoint lc2 lc.
  Proof.
    inv DISJOINT1. inv STEP. ss.
  Qed.

  Lemma write_step_disjoint
        lc1 gl1 loc from to val releasedm released ord lc2 gl2 lc
        (STEP: write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    hexploit Memory.add_messages_le; eauto. i.
    exploit Promises.fulfill_disjoint; try exact FULFILL; eauto. i. des.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { exploit Memory.add_preserve; eauto. i. des. specialize (GET_STATE loc0).
      unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *.
      rewrite <- GET_STATE. eauto.
    }
    esplits; eauto. econs; ss; eauto.
    - eapply TView.le_closed; eauto.
    - etrans; eauto. eapply Memory.add_le; eauto.
  Qed.

  Lemma fence_step_disjoint
        lc1 gl1 ordr ordw lc2 gl2 lc
        (STEP: fence_step lc1 gl1 ordr ordw lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP. splits; ss.
  Qed.

  Lemma alloc_step_disjoint
        lc1 gl1 loc size lc2 gl2 lc
        (STEP: alloc_step lc1 gl1 loc size lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1)
        (GL_WF: Global.wf gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP. splits; ss.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { i. inv ALLOC. unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *. ss.
      revert H. condtac; ss.
    }
    econs; ss; eauto.
    - inv TVIEW_CLOSED. econs; i; eapply Memory.alloc_closed_view; eauto; try eapply GL_WF.
    - etrans; eauto. eapply Memory.alloc_le; eauto.
  Qed.

  Lemma free_step_disjoint
        lc1 gl1 loc size lc2 gl2 lc
        (STEP: free_step lc1 gl1 loc size lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv DISJOINT1. inv LC_WF. inv STEP.
    hexploit Memory.free_messages_le; eauto. i.
    exploit Promises.fulfills_disjoint; try exact FULFILL; eauto. i. des.
    exploit FreePromises.sfulfill_disjoint; try exact FULFILL_FREE; eauto. i. des.
    assert (forall loc, Memory.is_prealloced loc mem2 -> Memory.is_prealloced loc (Global.memory gl1)).
    { i. inv FREE. unfold Memory.is_prealloced, Block.is_prealloced, Memory.get_state in *. ss.
      revert H0. condtac; ss.
    }
    esplits; eauto. econs; ss; eauto.
    - eapply TView.le_closed; eauto.
    - etrans; eauto. eapply Memory.free_le; eauto.
  Qed.

  Lemma read_step_promises
        lc1 gl1 loc to val released ord lc2
        (READ: read_step lc1 gl1 loc to val released ord lc2):
    (promises lc1) = (promises lc2).
  Proof.
    inv READ. auto.
  Qed.

  Lemma internal_step_disjoint
        e lc1 gl1 lc2 gl2 lc
        (STEP: internal_step e lc1 gl1 lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv STEP.
    - eapply promise_step_disjoint; eauto.
    - eapply reserve_step_disjoint; eauto.
    - eapply cancel_step_disjoint; eauto.
    - eapply free_promise_step_disjoint; eauto.
  Qed.

  Lemma program_step_disjoint
        e lc1 gl1 lc2 gl2 lc
        (STEP: program_step e lc1 gl1 lc2 gl2)
        (DISJOINT1: disjoint lc1 lc)
        (LC_WF: wf lc gl1)
        (GL_WF: Global.wf gl1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<LC_WF: wf lc gl2>>.
  Proof.
    inv STEP; try by (splits; eauto).
    - exploit read_step_disjoint; eauto.
    - exploit write_step_disjoint; eauto.
    - exploit read_step_disjoint; eauto. i.
      exploit write_step_disjoint; eauto.
    - exploit read_step_disjoint; eauto. i.
      exploit write_step_disjoint; eauto.
    - exploit read_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit fence_step_disjoint; eauto.
    - exploit alloc_step_disjoint; eauto.
    - exploit free_step_disjoint; eauto.
    - inv LOCAL; try by (splits; eauto).
      exploit read_step_disjoint; eauto.
  Qed.

  Lemma program_step_promises
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2):
    Promises.le (promises lc2) (promises lc1) /\
    Promises.le (Global.promises gl2) (Global.promises gl1).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL. eapply Promises.fulfill_le2; eauto.
    - inv LOCAL1. inv LOCAL2. eapply Promises.fulfill_le2; eauto.
    - inv LOCAL1. inv LOCAL2. ss. eapply Promises.fulfill_le2; eauto.
    - inv LOCAL1. ss.
    - inv LOCAL. eapply Promises.fulfills_le2; eauto.
    - inv LOCAL; ss. inv LOCAL0; ss.
  Qed.

  Lemma program_step_free_promises
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2):
    FreePromises.le (free_promises lc2) (free_promises lc1) /\
    FreePromises.le (Global.free_promises gl2) (Global.free_promises gl1).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL1; inv LOCAL2; ss.
    - inv LOCAL1. inv LOCAL2. ss.
    - inv LOCAL1. ss.
    - inv LOCAL. eapply FreePromises.sfulfill_le2; eauto.
    - inv LOCAL; ss. inv LOCAL0; ss.
  Qed.

  Lemma internal_step_promises_minus
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    Promises.minus (Global.promises gl1) (promises lc1) =
    Promises.minus (Global.promises gl2) (promises lc2).
  Proof.
    inv STEP; inv LOCAL; ss.
    eapply Promises.promise_minus; eauto.
  Qed.

  Lemma program_step_promises_minus
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2):
    Promises.minus (Global.promises gl1) (promises lc1) =
    Promises.minus (Global.promises gl2) (promises lc2).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL. ss.
      eapply Promises.fulfill_minus; eauto.
    - inv LOCAL1. inv LOCAL2. ss.
      eapply Promises.fulfill_minus; eauto.
    - inv LOCAL1. inv LOCAL2. ss.
      eapply Promises.fulfill_minus; eauto.
    - inv LOCAL1. ss.
    - inv LOCAL. eapply Promises.fulfills_minus; eauto.
    - inv LOCAL; ss. inv LOCAL0; ss.
  Qed.

  Lemma internal_step_free_promises_minus
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    FreePromises.minus (Global.free_promises gl1) (free_promises lc1) =
    FreePromises.minus (Global.free_promises gl2) (free_promises lc2).
  Proof.
    inv STEP; inv LOCAL; ss.
    eapply FreePromises.promise_minus; eauto.
  Qed.

  Lemma program_step_free_promises_minus
        e lc1 gl1 lc2 gl2
        (STEP: program_step e lc1 gl1 lc2 gl2):
    FreePromises.minus (Global.free_promises gl1) (free_promises lc1) =
    FreePromises.minus (Global.free_promises gl2) (free_promises lc2).
  Proof.
    inv STEP; ss; try by (inv LOCAL; ss).
    - inv LOCAL1. inv LOCAL2. ss.
    - inv LOCAL1. inv LOCAL2. ss.
    - inv LOCAL1. ss.
    - inv LOCAL. eapply FreePromises.sfulfill_minus; eauto.
    - inv LOCAL; ss. inv LOCAL0; ss.
  Qed.

  Lemma write_max_exists
        lc1 gl1
        loc val releasedm ord
        (LC_WF: Local.wf lc1 gl1)
        (ALLOCED: View.alloc_view (TView.cur (tview lc1)) (Loc.get_tbid loc))
        (ACCESSIBLE: Memory.accessible loc (Global.memory gl1)):
    exists from to released lc2 gl2,
      (<<WRITE: write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2>>) /\
      (<<FROM: Time.lt (Memory.max_ts loc (Global.memory gl1)) from>>).
  Proof.
    exploit Memory.add_exists_max; try eapply Time.incr_spec.
    i. des. esplits; try exact FROM.
    econs; try exact ADD; eauto. econs; eauto.
    eapply TimeFacts.le_lt_lt; [|apply Time.incr_spec].
    inv LC_WF. inv TVIEW_CLOSED. inv CUR. specialize (RLX loc). des.
    { rewrite RLX. apply Time.bot_spec. }
    eapply Memory.max_ts_spec. eauto.
  Qed.

  Lemma fence_step_non_sc
        lc1 gl1 or ow lc2 gl2
        (STEP: fence_step lc1 gl1 or ow lc2 gl2)
        (SC: Ordering.le ow Ordering.acqrel):
    gl2 = gl1.
  Proof.
    destruct gl1. inv STEP. ss. f_equal.
    apply TViewFacts.write_fence_sc_acqrel. ss.
  Qed.

  Lemma internal_step_messages_le_inv
        e lc1 gl1 lc2 gl2
        (STEP: internal_step e lc1 gl1 lc2 gl2):
    <<MESSAGES_LE: Memory.messages_le (Global.memory gl2) (Global.memory gl1)>>.
  Proof.
    inv STEP; inv LOCAL; ss; try refl.
    - eapply Memory.messages_le_PreOrder.
    - inv RESERVE. exploit Memory.add_preserve; eauto. i. des. econs; i.
      + revert LHS. erewrite Memory.add_o; eauto. condtac; ss.
      + rewrite GET_STATE. refl.
      + rewrite NEXTBID. refl.
    - inv CANCEL. exploit Memory.remove_preserve; eauto. i. des. econs; i.
      + revert LHS. erewrite Memory.remove_o; eauto. condtac; ss.
      + rewrite GET_STATE. refl.
      + rewrite NEXTBID. refl.
    - eapply Memory.messages_le_PreOrder.
  Qed.
End Local.

