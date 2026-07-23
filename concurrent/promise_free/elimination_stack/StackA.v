Require Import CRIS.common.CRIS.
Require Import CRIS.scheduler.SchHeader.
Require Export CRIS.scheduler.Atomic.
From CRIS.promise_free.lib Require Import Val.
From CRIS.promise_free.model Require Import Cell Time View.
From CRIS.promise_free.gpfsl Require Import LatticeRA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.system Require Import SystemA.
From CRIS.promise_free.elimination_stack Require Export StackHeader.
From CRIS.helping Require Import HelpingHeader HelpingTactics.
From CRIS.iris_system.lib Require Import ghost_map.

From iris.algebra Require Import auth excl gmap_view.

Canonical Structure stackValO := leibnizO Val.t.

Global Instance Loc_countable : Countable Loc.t.
Proof.
  refine (inj_countable'
    (λ l, (Loc.tid l, Loc.bid l, Loc.ofs l))
    (λ '(tid, bid, ofs), Loc.mk tid bid ofs) _).
  by intros [].
Defined.

(** Authoritative abstract LIFO contents.  The persistent invariant in
    [stack_handle] associates this ghost name with the concrete descriptor. *)
Definition stackR : ucmra := authR (optionUR (exclR (listO stackValO))).

Class stackG `{!crisG Γ Σ α β τ _S _I} := StackG {
  #[local] stack_inG :: inG stackR Γ;
  #[local] stack_token_inG :: inG (exclR unitO) Γ;
  #[local] stack_node_map_inG ::
    inG (gmap_viewR Loc.t (agreeR (leibnizO Loc.t))) Γ;
}.

Definition stackΓ : HRA :=
  #[stackR; exclR unitO; gmap_viewR Loc.t (agreeR (leibnizO Loc.t))].

Global Instance subG_stackG `{!crisG Γ Σ α β τ _S _I} :
  subG stackΓ Γ → stackG.
Proof. solve_inG. Defined.

Section stack_resources.
  Context `{!crisG Γ Σ α β τ _S _I, !histGS, !atomicG, !stackG, !helpingGS}.

  Local Existing Instances histGS_histGpreS histGS_view histGS_hist histGS_free.
  Local Existing Instances Loc_eq_dec Loc_countable stack_node_map_inG.
  Local Instance stack_node_mapGΓ : ghost_mapG Γ Loc.t Loc.t.
  Proof. constructor. exact stack_node_map_inG. Defined.
  Local Instance stack_node_mapGS : ghost_mapG Σ Loc.t Loc.t.
  Proof. constructor. apply _. Defined.

  Definition stackN := nroot .@ "promise-free-elimination-stack".
  Definition stackInvN := stackN .@ "stack".
  Definition offerN := stackN .@ "offer".
  Record node_desc := NodeDesc {
    node_next : Loc.t;
    node_value : Val.t;
    node_pub_view : View.t;
  }.

  Definition stack_content (γs : gname) (vs : list stackValO) : iProp Σ :=
    own γs (◯ Excl' vs).

  Definition syn_stack_content {n} (γs : gname) (vs : list stackValO) : GTerm.t n :=
    sown γs (◯ Excl' vs).

  Global Instance stack_content_red n γs vs :
    SLRed n (syn_stack_content γs vs) (stack_content γs vs).
  Proof. solve_sl_red. Qed.

  Local Instance own_loc_na_red n loc q value V :
    SLRed n (syn_own_loc_na n loc q value V) (@{V} own_loc_na loc q value).
  Proof. apply syn_own_loc_na_red. Qed.

  Lemma view_at_view_mon_pred (P : View.t → iProp Σ) `{!MonPred P}
      V1 V2 (LE : V1 ⊑ V2) :
    P V1 ⊢ P V2.
  Proof. rewrite LE. done. Qed.

  Fixpoint node_chain (sentinel : Loc.t) (nodes : gmap Loc.t node_desc)
      (vs : list Val.t) (rep : Val.t) : Prop :=
    match vs with
    | [] => rep = Val.Vptr sentinel
    | value :: vs' =>
        ∃ node d, rep = Val.Vptr node ∧ node ≠ sentinel ∧
          nodes !! node = Some d ∧ d.(node_value) = value ∧
          node_chain sentinel nodes vs' (Val.Vptr d.(node_next))
    end.

  Definition node_links (sentinel : Loc.t)
      (targets : list (Loc.t * View.t))
      (nodes : gmap Loc.t node_desc) : Prop :=
    ∀ node d, nodes !! node = Some d →
      node ≠ sentinel ∧
      (d.(node_next) = sentinel ∨
        ∃ dnext Vguard,
          nodes !! d.(node_next) = Some dnext ∧
          (d.(node_next), Vguard) ∈ targets ∧
          dnext.(node_pub_view) ⊑ d.(node_pub_view) ∧
          Vguard ⊑ d.(node_pub_view)).

  Definition current_message (ζ : Cell.t) (value : Val.t) (V : View.t) : Prop :=
    ∃ f b,
      Cell.get (Cell.max_ts ζ) ζ = Some (f, Message.message value V b).

  Definition pointer_history (sentinel : Loc.t)
      (targets : list (Loc.t * View.t)) (ζ : Cell.t) : Prop :=
    ∀ t f value V b,
      Cell.get t ζ = Some (f, Message.message value V b) →
      ∃ loc Vguard, value = Val.Vptr loc ∧
        (loc, Vguard) ∈ targets ∧ (loc = sentinel ∨ Vguard ⊑ V).

  Definition head_history (sentinel : Loc.t)
      (nodes : gmap Loc.t node_desc) (ζ : Cell.t) : Prop :=
    ∀ t f value V b,
      Cell.get t ζ = Some (f, Message.message value V b) →
      value = Val.Vptr sentinel ∨
      ∃ node d, value = Val.Vptr node ∧ nodes !! node = Some d ∧
        d.(node_pub_view) ⊑ V.

  (** CAS is the only writer after initialization.  Consequently every
      non-maximal message has a direct RMW successor.  This rules out a CAS
      insertion below the current maximum: its write interval would overlap
      the already present successor interval. *)
  Definition cas_history (ζ : Cell.t) : Prop :=
    ∀ t f value V b,
      Cell.get t ζ = Some (f, Message.message value V b) →
      t = Cell.max_ts ζ ∨
        ∃ t' value' V' b',
          Cell.get t' ζ = Some (t, Message.message value' V' b').

  Lemma cas_history_add_from_max ζ from to value V b ζ' f old Vold bold
      (HIST : cas_history ζ)
      (GET : Cell.get from ζ = Some (f, Message.message old Vold bold))
      (ADD : Cell.add ζ from to (Message.message value V b) ζ') :
    from = Cell.max_ts ζ.
  Proof.
    destruct (HIST _ _ _ _ _ GET) as [MAX|NEXT]; first done.
    destruct NEXT as (next & value' & V' & b' & NEXT).
    inv ADD. hexploit DISJOINT; first eapply NEXT. intros DISJ.
    exfalso.
    eapply (DISJ (Time.meet to next)).
    - econs; simpl.
      + destruct (Time.meet_cases to next) as [MEET|MEET];
          rewrite MEET; eauto using Cell.get_ts.
      + apply Time.meet_l.
    - econs; simpl.
      + destruct (Time.meet_cases to next) as [MEET|MEET];
          rewrite MEET; eauto using Cell.get_ts.
      + apply Time.meet_r.
  Qed.

  Lemma cas_history_add ζ from to value V b ζ' f old Vold bold
      (HIST : cas_history ζ)
      (GET : Cell.get from ζ = Some (f, Message.message old Vold bold))
      (ADD : Cell.add ζ from to (Message.message value V b) ζ') :
    cas_history ζ'.
  Proof.
    assert (from = Cell.max_ts ζ) as MAX.
    { eapply cas_history_add_from_max; eauto. }
    assert (Cell.max_ts ζ' = to) as MAX'.
    { subst from. eapply Cell.add_max_ts; eauto. }
    intros t f' value' V' b' GET'.
    erewrite Cell.add_o in GET'; eauto.
    destruct (Time.eq_dec t to) as [EQ|NE].
    { subst t. left. symmetry. done. }
    destruct (HIST _ _ _ _ _ GET') as [CUR|NEXT].
    - right. exists to, value, V, b.
      rewrite <- MAX in CUR. subst t.
      destruct (Cell.add_get0 ADD) as [_ GETNEW]. exact GETNEW.
    - right. destruct NEXT as (next & value'' & V'' & b'' & NEXT).
      exists next, value'', V'', b''.
      eapply Cell.add_get1; eauto.
  Qed.

  Definition numeric_history (ζ : Cell.t) : Prop :=
    ∀ t f value V b,
      Cell.get t ζ = Some (f, Message.message value V b) →
      ∃ z, value = Val.Vnum z.

  (** An offer state changes at most once, from zero to either claimed or
      withdrawn. Thus every nonzero message agrees with the current state. *)
  Definition offer_state_history (ζ : Cell.t) (state : Val.t) : Prop :=
    ∀ t f value V b,
      Cell.get t ζ = Some (f, Message.message value V b) →
      value = Val.zero ∨ value = state.

  Lemma current_message_add ζ from to value V b ζ' old Vold
      (CUR : current_message ζ old Vold)
      (MAX : from = Cell.max_ts ζ)
      (ADD : Cell.add ζ from to (Message.message value V b) ζ') :
    current_message ζ' value V.
  Proof.
    destruct CUR as (f0 & b0 & GET0). subst from.
    assert (Cell.max_ts ζ' = to) as MAX'.
    { eapply Cell.add_max_ts; eauto. }
    exists (Cell.max_ts ζ), b. rewrite MAX'.
    by destruct (Cell.add_get0 ADD).
  Qed.

  Lemma pointer_history_add sentinel targets ζ from to loc V b ζ'
      (HIST : pointer_history sentinel targets ζ)
      (NEW : ∃ Vguard, (loc, Vguard) ∈ targets ∧
        (loc = sentinel ∨ Vguard ⊑ V))
      (ADD : Cell.add ζ from to (Message.message (Val.Vptr loc) V b) ζ') :
    pointer_history sentinel targets ζ'.
  Proof.
    intros t f value Vmsg bmsg GET.
    erewrite Cell.add_o in GET; eauto. des_ifs.
    - destruct NEW as (Vguard & IN & SAFE).
      exists loc, Vguard. repeat split; eauto.
    - eapply HIST; eauto.
  Qed.

  Lemma head_history_add sentinel nodes ζ from to loc V b ζ'
      (HIST : head_history sentinel nodes ζ)
      (NEW : loc = sentinel ∨
        ∃ d, nodes !! loc = Some d ∧ d.(node_pub_view) ⊑ V)
      (ADD : Cell.add ζ from to (Message.message (Val.Vptr loc) V b) ζ') :
    head_history sentinel nodes ζ'.
  Proof.
    intros t f value Vmsg bmsg GET.
    erewrite Cell.add_o in GET; eauto. des_ifs.
    - destruct NEW as [->|(d & LOOK & LE)].
      { left; done. }
      right. eexists loc, d. split; first done. split; done.
    - eapply HIST; eauto.
  Qed.

  Lemma numeric_history_add ζ from to z V b ζ'
      (HIST : numeric_history ζ)
      (ADD : Cell.add ζ from to (Message.message (Val.Vnum z) V b) ζ') :
    numeric_history ζ'.
  Proof.
    intros t f value Vmsg bmsg GET.
    erewrite Cell.add_o in GET; eauto. des_ifs.
    - eauto.
    - eapply HIST; eauto.
  Qed.

  Lemma offer_state_history_add_from_zero ζ from to state V b ζ'
      (HIST : offer_state_history ζ Val.zero)
      (ADD : Cell.add ζ from to (Message.message state V b) ζ') :
    offer_state_history ζ' state.
  Proof.
    intros t f value Vmsg bmsg GET.
    erewrite Cell.add_o in GET; eauto. des_ifs.
    - right. done.
    - destruct (HIST _ _ _ _ _ GET) as [ZERO|ZERO]; left; done.
  Qed.

  Lemma current_message_mutual_le_agree ζ1 ζ2 value V f b value' V' :
    current_message ζ1 value V →
    Cell.le ζ1 ζ2 → Cell.le ζ2 ζ1 →
    Cell.get (Cell.max_ts ζ2) ζ2 =
      Some (f, Message.message value' V' b) →
    value = value'.
  Proof.
    intros (f0 & b0 & CUR) LE12 LE21 GET.
    pose proof (LE12 _ _ _ CUR) as CUR2.
    pose proof (LE21 _ _ _ GET) as GET1.
    destruct (Cell.max_ts_spec (Cell.max_ts ζ1) ζ2 CUR2) as [_ MAX12].
    destruct (Cell.max_ts_spec (Cell.max_ts ζ2) ζ1 GET1) as [_ MAX21].
    assert (Cell.max_ts ζ1 = Cell.max_ts ζ2) as EQ.
    { apply TimeFacts.antisym; done. }
    rewrite EQ in CUR2.
    rewrite CUR2 in GET. inversion GET. done.
  Qed.

  Local Instance sync_local_red n loc ζ V :
    SLRed n (syn_SyncLocal n loc ζ V) (SyncLocal loc ζ V).
  Proof. apply syn_SyncLocal_red. Qed.

  Local Instance atomic_pts_to_red n loc γ ζ mode V :
    SLRed n (@{V} syn_AtomicPtsTo n loc γ ζ mode)
      (@{V} AtomicPtsTo loc γ ζ mode).
  Proof. apply syn_AtomicPtsTo_red. Qed.

  Definition syn_atomic_swriter n (loc : Loc.t) γ ζ (V : View.t) : GTerm.t n :=
    ((syn_SyncLocal n loc ζ V ∗ syn_at_reader n γ ζ ∗ ⌜good_absHist ζ⌝ ∗
      (∃ Va : τ{View.t}, ⌜Va ⊑ V⌝ ∗ syn_at_last_na n γ Va)) ∗
      syn_at_writer n γ ζ ∗ syn_at_exclusive_write n γ (Cell.max_ts ζ) 1)%SAT.

  Global Instance atomic_swriter_red n loc γ ζ V :
    SLRed n (syn_atomic_swriter n loc γ ζ V) (view_at (AtomicSWriter loc γ ζ) V).
  Proof.
    rewrite AtomicSWriter_eq /AtomicSWriter_def AtomicSync_eq /AtomicSync_def.
    rewrite /view_at. solve_sl_red.
  Qed.

  Definition syn_atomic_seen n (loc : Loc.t) γ ζ (V : View.t) : GTerm.t n :=
    (syn_SeenLocal n loc ζ V ∗ syn_at_reader n γ ζ ∗ ⌜good_absHist ζ⌝ ∗
      (∃ Va : τ{View.t}, ⌜Va ⊑ V⌝ ∗ syn_at_last_na n γ Va))%SAT.

  Global Instance atomic_seen_red n loc γ ζ V :
    SLRed n (syn_atomic_seen n loc γ ζ V) (view_at (AtomicSeen loc γ ζ) V).
  Proof.
    rewrite AtomicSeen_eq /AtomicSeen_def /view_at. solve_sl_red.
  Qed.

  Lemma atomic_pts_to_swriter_to_cas loc γ ζ V :
    @{V} loc sw↦{γ} ζ -∗ @{V} loc sw⊒{γ} ζ -∗ @{V} loc cas↦{γ} ζ.
  Proof.
    rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
    iDestruct 1 as (tx) "PT". iIntros "SW". iExists tx.
    rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def
      AtomicSWriter_eq /AtomicSWriter_def.
    iDestruct "SW" as "[_ [W _]]".
    iDestruct "PT" as (C Va ->) "[SL [H [AA _]]]".
    iExists ζ, Va. iSplit; first done. iFrame.
  Qed.

  Lemma atomic_pts_to_seen_current loc γ tx ζ ζseen mode Vseen Vfull
      (LEVIEW : Vseen ⊑ Vfull) :
    @{Vfull} AtomicPtsToX loc γ tx ζ mode -∗
    @{Vseen} AtomicSeen loc γ ζseen -∗
      @{Vfull} AtomicPtsToX loc γ tx ζ mode ∗
      @{Vfull} AtomicSeen loc γ ζ.
  Proof.
    iIntros "PT #SEEN".
    iDestruct (AtomicSeen_non_empty' with "SEEN") as
      (t f msg) "%GET".
    iPoseProof (view_at_view_mon_pred
      (view_at (AtomicSeen loc γ ζseen)) Vseen Vfull LEVIEW
      with "SEEN") as "#SEENfull".
    iEval (rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def) in "PT".
    iDestruct "PT" as (C Va ->) "[SYNC [HIST [AUTH MODE]]]".
    iEval (rewrite /view_at AtomicSeen_eq /AtomicSeen_def) in "SEENfull".
    iDestruct "SEENfull" as "[_ [READER [%GOOD LASTNA]]]".
    iPoseProof (at_auth_reader_latest with "AUTH READER") as "%LEHIST".
    iPoseProof (at_auth_fork_at_reader with "AUTH") as "#READERfull".
    iPoseProof (SyncLocal_SeenLocal with "SYNC") as "#LOCALfull".
    iSplitL "SYNC HIST AUTH MODE".
    { rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def.
      iExists ζ, Va. iSplit; first done. iFrame. }
    rewrite /view_at AtomicSeen_eq /AtomicSeen_def.
    iFrame "LOCALfull READERfull LASTNA".
    iPureIntro. intros BOT.
    pose proof (LEHIST _ _ _ GET) as GETfull.
    rewrite BOT Cell.bot_get in GETfull. done.
  Qed.


  Lemma hist_full_exclusive loc C1 C2 :
    hist loc 1 C1 -∗ hist loc 1 C2 -∗ False.
  Proof.
    rewrite hist_eq /hist_def.
    iIntros "H1 H2". iCombine "H1 H2" gives %VALID.
    move : VALID.
    rewrite auth_frag_op_valid discrete_fun_singleton_op
      discrete_fun_singleton_valid -Some_op.
    intros VALID.
    change (✓ ((DfracOwn 1, to_agree C1) ⋅
      (DfracOwn 1, to_agree C2))) in VALID.
    move : VALID. rewrite -pair_op pair_valid dfrac_op_own dfrac_valid_own.
    naive_solver.
  Qed.

  Definition syn_immutable_field n (loc : Loc.t) (value : Val.t)
      (Vpub : View.t) : GTerm.t n :=
    (∃ (f t : τ{Time.t}) (LT : τ{Time.lt f t}) (Vmsg Vfield : τ{View.t})
       (b : τ{bool}) (γ : τ{gname}),
      ⌜Vfield ⊑ Vpub ∧ Vmsg ⊑ Vfield⌝ ∗
      @{Vfield} loc sw↦{γ}
        (Cell.singleton (Message.message value Vmsg b) LT) ∗
      syn_atomic_swriter n loc γ
        (Cell.singleton (Message.message value Vmsg b) LT) Vfield)%SAT.

  Definition immutable_field (loc : Loc.t) (value : Val.t)
      (Vpub : View.t) : iProp Σ :=
    ∃ (f t : Time.t) (LT : Time.lt f t) (Vmsg Vfield : View.t) b γ,
      ⌜Vfield ⊑ Vpub ∧ Vmsg ⊑ Vfield⌝ ∗
      @{Vfield} loc sw↦{γ}
        (Cell.singleton (Message.message value Vmsg b) LT) ∗
      @{Vfield} loc sw⊒{γ}
        (Cell.singleton (Message.message value Vmsg b) LT).

  Global Instance immutable_field_red n loc value Vpub :
    SLRed n (syn_immutable_field n loc value Vpub)
      (immutable_field loc value Vpub).
  Proof. solve_sl_red. Qed.

  Definition syn_node_record n (node : Loc.t) (d : node_desc) : GTerm.t n :=
    syn_immutable_field n (node >> 1) (Val.Vptr d.(node_next)) d.(node_pub_view).

  Definition node_record (node : Loc.t) (d : node_desc) : iProp Σ :=
    immutable_field (node >> 1) (Val.Vptr d.(node_next)) d.(node_pub_view).

  Global Instance node_record_red n node d :
    SLRed n (syn_node_record n node d) (node_record node d).
  Proof. solve_sl_red. Qed.

  Definition node_next_map (nodes : gmap Loc.t node_desc) : gmap Loc.t Loc.t :=
    node_next <$> nodes.

  Definition syn_node_registry (n : nat) (target_map : gname)
      (nodes : gmap Loc.t node_desc) : GTerm.t n :=
    (syn_ghost_map_auth (K:=Loc.t) (V:=Loc.t) (Γ:=Γ) (τ:=τ)
        target_map 1 (node_next_map nodes) ∗
      [∗ map] node ↦ d ∈ nodes,
        syn_ghost_map_elem (K:=Loc.t) (V:=Loc.t) (Γ:=Γ) (τ:=τ)
          target_map node DfracDiscarded d.(node_next) ∗
        syn_node_record n node d)%SAT.

  Definition node_registry (target_map : gname)
      (nodes : gmap Loc.t node_desc) : iProp Σ :=
    (ghost_map_auth target_map 1 (node_next_map nodes) ∗
      [∗ map] node ↦ d ∈ nodes,
        node ↪[target_map]□ d.(node_next) ∗ node_record node d)%I.

  Global Instance node_registry_red n target_map nodes :
    SLRed n (syn_node_registry n target_map nodes)
      (node_registry target_map nodes).
  Proof. solve_sl_red. Qed.

  Lemma node_next_token_agree target_map node next1 next2 :
    node ↪[target_map]□ next1 -∗ node ↪[target_map]□ next2 -∗
      ⌜next1 = next2⌝.
  Proof. iIntros "H1 H2". iApply (ghost_map_elem_agree with "H1 H2"). Qed.

  Lemma node_registry_alloc :
    ⊢ o=> ∃ target_map, node_registry target_map (∅ : gmap Loc.t node_desc).
  Proof.
    iMod (ghost_map_alloc_empty (K:=Loc.t) (V:=Loc.t))
      as (target_map) "AUTH".
    iModIntro. iExists target_map. rewrite /node_registry /node_next_map
      fmap_empty big_sepM_empty. iFrame.
  Qed.

  Definition syn_live_value n (node : Loc.t) (d : node_desc) : GTerm.t n :=
    (∃ Vfield : τ{View.t}, ⌜Vfield ⊑ d.(node_pub_view)⌝ ∗
      @{Vfield} (node >> 2) ↦ StackHdr.encode d.(node_value))%SAT.

  Definition live_value (node : Loc.t) (d : node_desc) : iProp Σ :=
    (∃ Vfield, ⌜Vfield ⊑ d.(node_pub_view)⌝ ∗
      @{Vfield} (node >> 2) ↦ StackHdr.encode d.(node_value))%I.

  Global Instance live_value_red n node d :
    SLRed n (syn_live_value n node d) (live_value node d).
  Proof. solve_sl_red. Qed.

  (** Only values of currently reachable nodes remain linearly owned.  A
      retired node stays in [node_registry] only through its atomic next
      field, which is precisely the field a stale head read may dereference. *)
  Fixpoint syn_live_chain n (sentinel : Loc.t)
      (nodes : gmap Loc.t node_desc) (vs : list Val.t)
      (rep : Val.t) : GTerm.t n :=
    match vs with
    | [] => ⌜rep = Val.Vptr sentinel⌝
    | value :: vs' =>
        (∃ (node : τ{Loc.t}) (d : τ{node_desc}),
          ⌜rep = Val.Vptr node ∧ node ≠ sentinel ∧
            nodes !! node = Some d ∧ d.(node_value) = value⌝ ∗
          syn_live_value n node d ∗
          syn_live_chain n sentinel nodes vs' (Val.Vptr d.(node_next)))%SAT
    end.

  Fixpoint live_chain (sentinel : Loc.t) (nodes : gmap Loc.t node_desc)
      (vs : list Val.t) (rep : Val.t) : iProp Σ :=
    match vs with
    | [] => ⌜rep = Val.Vptr sentinel⌝
    | value :: vs' =>
        (∃ node d,
          ⌜rep = Val.Vptr node ∧ node ≠ sentinel ∧
            nodes !! node = Some d ∧ d.(node_value) = value⌝ ∗
          live_value node d ∗
          live_chain sentinel nodes vs' (Val.Vptr d.(node_next)))%I
    end.

  Global Instance live_chain_red n sentinel nodes vs rep :
    SLRed n (syn_live_chain n sentinel nodes vs rep)
      (live_chain sentinel nodes vs rep).
  Proof. revert n rep; induction vs; intros; solve_sl_red. Qed.

  Lemma live_value_take node d Vcur
      (ACQUIRED : d.(node_pub_view) ⊑ Vcur) :
    live_value node d -∗
      @{Vcur} (node >> 2) ↦ StackHdr.encode d.(node_value).
  Proof.
    iDestruct 1 as (Vfield) "[%LE PT]".
    iApply (view_at_view_mon_pred
      (view_at (own_loc_na (node >> 2) 1 (StackHdr.encode d.(node_value))))
      Vfield Vcur with "PT").
    etrans; eauto.
  Qed.

  Lemma live_chain_node_chain sentinel nodes vs rep :
    live_chain sentinel nodes vs rep -∗
      live_chain sentinel nodes vs rep ∗
      ⌜node_chain sentinel nodes vs rep⌝.
  Proof.
    revert rep; induction vs as [|value vs IH]; intros rep; simpl.
    { iIntros "%EQ". iSplit; iPureIntro; done. }
    iDestruct 1 as (node d) "[%REL [VALUE TAIL]]".
    iDestruct (IH with "TAIL") as "[TAIL %CHAIN]".
    iSplitL "VALUE TAIL".
    { iExists node, d. iFrame. done. }
    iPureIntro. destruct REL as (REP & NONSENTINEL & LOOK & VALUE).
    eexists node, d. repeat split; eauto.
  Qed.

  Lemma node_lookup_agree (nodes : gmap Loc.t node_desc) (node : Loc.t)
      (d1 d2 : node_desc)
      (LOOK1 : nodes !! node = Some d1)
      (LOOK2 : nodes !! node = Some d2) :
    d1 = d2.
  Proof. congruence. Qed.

  Lemma node_registry_lookup target_map nodes node d
      (LOOK : nodes !! node = Some d) :
    node_registry target_map nodes -∗
      node ↪[target_map]□ d.(node_next) ∗ node_record node d.
  Proof.
    iIntros "[_ REG]". iApply (big_sepM_lookup with "REG"); done.
  Qed.

  Lemma node_registry_lookup_acc target_map nodes node d
      (LOOK : nodes !! node = Some d) :
    node_registry target_map nodes -∗
      node_record node d ∗ node ↪[target_map]□ d.(node_next) ∗
      (node_record node d -∗ node_registry target_map nodes).
  Proof.
    iIntros "[AUTH REG]".
    iDestruct (big_sepM_lookup_acc with "REG") as "[[#NEXT REC] CLOSE]";
      first done.
    iFrame "REC NEXT". iIntros "REC". iFrame "AUTH".
    iApply "CLOSE". iFrame "NEXT REC".
  Qed.

  Lemma node_registry_insert target_map nodes node d
      (FRESH : nodes !! node = None) :
    node_record node d -∗ node_registry target_map nodes ==∗
      node_registry target_map (<[node := d]> nodes).
  Proof.
    iIntros "REC [AUTH REG]".
    iMod (ghost_map_insert_persist node d.(node_next) with "AUTH")
      as "[AUTH #NEXT]".
    { rewrite /node_next_map lookup_fmap FRESH. done. }
    iModIntro. rewrite /node_registry /node_next_map fmap_insert
      big_sepM_insert //.
    iFrame "AUTH REG REC NEXT".
  Qed.

  Lemma node_record_conflict node d value V :
    node_record node d -∗ @{V} (node >> 1) ↦ value -∗ False.
  Proof.
    rewrite /node_record /immutable_field.
    iDestruct 1 as (f t LT Vmsg Vfield b γ) "[_ [PT _]]".
    rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
    iDestruct "PT" as (tx) "PT".
    rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def.
    iDestruct "PT" as (C Va ->) "[_ [HIST _]]".
    rewrite /view_at own_loc_na_eq /own_loc_na_def.
    iDestruct 1 as (f' t' LT' Vmsg' b') "[[_ HIST'] _]".
    iApply (hist_full_exclusive with "HIST HIST'").
  Qed.

  Lemma node_registry_fresh target_map nodes node value V :
    @{V} (node >> 1) ↦ value -∗ node_registry target_map nodes -∗
      ⌜nodes !! node = None⌝ ∗
      @{V} (node >> 1) ↦ value ∗ node_registry target_map nodes.
  Proof.
    iIntros "NEW REG".
    destruct (nodes !! node) as [d|] eqn:LOOK; last by iFrame.
    iDestruct (node_registry_lookup _ _ _ _ LOOK with "REG")
      as "[_ REC]".
    iExFalso. iApply (node_record_conflict with "REC NEW").
  Qed.

  Lemma head_history_lookup sentinel nodes ζ t f node V b
      (NONSENTINEL : node ≠ sentinel)
      (GET : Cell.get t ζ =
        Some (f, Message.message (Val.Vptr node) V b))
      (HIST : head_history sentinel nodes ζ) :
    ∃ d, nodes !! node = Some d ∧ d.(node_pub_view) ⊑ V.
  Proof.
    destruct (HIST _ _ _ _ _ GET) as [EQ|(node' & d & EQ & LOOK & LE)].
    { inversion EQ. contradiction. }
    inversion EQ; subst. eauto.
  Qed.

  Lemma node_chain_cons_lookup sentinel nodes value vs rep :
    node_chain sentinel nodes (value :: vs) rep →
    ∃ node d, rep = Val.Vptr node ∧ node ≠ sentinel ∧
      nodes !! node = Some d ∧ d.(node_value) = value ∧
      node_chain sentinel nodes vs (Val.Vptr d.(node_next)).
  Proof. done. Qed.

  (** The field's global [AtomicPtsTo] resource stays at [Vfield], while the
      persistent seen handle can be lifted to an acquiring reader's [Vcur]. *)
  Lemma immutable_field_access loc value Vpub Vcur
      (ACQUIRED : Vpub ⊑ Vcur) :
    immutable_field loc value Vpub -∗
      ∃ γ ζ Vfield,
        @{Vfield} loc sw↦{γ} ζ ∗
        @{Vcur} loc sn⊒{γ} ζ ∗
        (@{Vfield} loc sw↦{γ} ζ -∗ immutable_field loc value Vpub).
  Proof.
    iDestruct 1 as (f t LT Vmsg Vfield b γ) "[%LE [PT SW]]".
    destruct LE as [LEfield LEmsg].
    assert (Vfield ⊑ Vcur) as LEcur by (etrans; eauto).
    iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SEEN".
    iPoseProof (view_at_view_mon_pred
      (view_at (AtomicSeen loc γ
        (Cell.singleton (Message.message value Vmsg b) LT)))
      _ _ LEcur with "SEEN") as "#SEENcur".
    iExists γ, (Cell.singleton (Message.message value Vmsg b) LT), Vfield.
    iFrame "PT SEENcur".
    iIntros "PT".
    iExists f, t, LT, Vmsg, Vfield, b, γ. iFrame.
    iPureIntro. split; done.
  Qed.

  Lemma node_registry_access target_map nodes node d Vcur
      (LOOK : nodes !! node = Some d)
      (ACQUIRED : d.(node_pub_view) ⊑ Vcur) :
    node_registry target_map nodes -∗
      ∃ γ ζ Vfield,
        @{Vfield} (node >> 1) sw↦{γ} ζ ∗
        @{Vcur} (node >> 1) sn⊒{γ} ζ ∗
        (@{Vfield} (node >> 1) sw↦{γ} ζ -∗
          node_registry target_map nodes).
  Proof.
    iDestruct 1 as "REG".
    iDestruct (node_registry_lookup_acc _ _ _ _ LOOK with "REG")
      as "[REC [_ CLOSE]]".
    iDestruct (immutable_field_access _ _ _ _ ACQUIRED with "REC")
      as (γ ζ Vfield) "[PT [SEEN REBUILD]]".
    iExists γ, ζ, Vfield. iFrame "PT SEEN".
    iIntros "PT". iApply "CLOSE". iApply "REBUILD". done.
  Qed.

  Lemma base_loc_not_sentinel stack_loc node
      (STACK_BASE : Loc.ofs stack_loc = 0%Z)
      (NODE_BASE : Loc.ofs node = 0%Z) :
    node ≠ stack_loc >> 2.
  Proof.
    intros ->. destruct stack_loc as [tid bid ofs].
    rewrite /shift /= in NODE_BASE. simpl in STACK_BASE. lia.
  Qed.

  Lemma node_chain_sentinel_empty sentinel nodes vs
      (CHAIN : node_chain sentinel nodes vs (Val.Vptr sentinel)) :
    vs = [].
  Proof.
    destruct vs as [|value vs]; first done.
    simpl in CHAIN. destruct CHAIN as
      (node & d & EQ & NONSENTINEL & LOOK & VALUE & TAIL).
    inversion EQ; subst. contradiction.
  Qed.

  Lemma live_chain_sentinel_empty sentinel nodes vs :
    live_chain sentinel nodes vs (Val.Vptr sentinel) -∗
      live_chain sentinel nodes vs (Val.Vptr sentinel) ∗ ⌜vs = []⌝.
  Proof.
    iIntros "CHAIN".
    iDestruct (live_chain_node_chain with "CHAIN") as "[CHAIN %PURE]".
    iFrame. iPureIntro. eapply node_chain_sentinel_empty; eauto.
  Qed.

  Lemma live_chain_insert_mono sentinel nodes vs rep node d
      (FRESH : nodes !! node = None) :
    live_chain sentinel nodes vs rep -∗
      live_chain sentinel (<[node := d]> nodes) vs rep.
  Proof.
    revert rep; induction vs as [|value vs IH]; intros rep; simpl.
    { iIntros "$". }
    iDestruct 1 as (node0 d0) "[%REL [VALUE TAIL]]".
    destruct REL as (REP & NONSENTINEL & LOOK & VALUEEQ).
    assert (node0 ≠ node) as NE.
    { intros ->. rewrite FRESH in LOOK. congruence. }
    iExists node0, d0. iFrame "VALUE".
    iSplit.
    { iPureIntro. repeat split; eauto. by rewrite lookup_insert_ne. }
    iApply IH. done.
  Qed.

  Lemma head_history_insert sentinel nodes ζ node d
      (FRESH : nodes !! node = None)
      (HIST : head_history sentinel nodes ζ) :
    head_history sentinel (<[node := d]> nodes) ζ.
  Proof.
    intros t f value V b GET.
    destruct (HIST _ _ _ _ _ GET) as [SENTINEL|(node0 & d0 & EQ & LOOK & LE)].
    { left; done. }
    right. exists node0, d0. split; first done. split; last done.
    assert (node0 ≠ node) as NE.
    { intros ->. rewrite FRESH in LOOK. congruence. }
    by rewrite lookup_insert_ne.
  Qed.

  Lemma pointer_history_cons sentinel target targets ζ
      (HIST : pointer_history sentinel targets ζ) :
    pointer_history sentinel (target :: targets) ζ.
  Proof.
    intros t f value V b GET.
    destruct (HIST _ _ _ _ _ GET) as (loc & Vguard & EQ & IN & SAFE).
    exists loc, Vguard. split; first done. split; first (right; done). done.
  Qed.

  Lemma node_links_target_cons sentinel target targets nodes
      (LINKS : node_links sentinel targets nodes) :
    node_links sentinel (target :: targets) nodes.
  Proof.
    intros node d LOOK.
    destruct (LINKS _ _ LOOK) as [NONSENTINEL [SENTINEL|NEXT]].
    { split; first done. left; done. }
    split; first done. right.
    destruct NEXT as (dnext & Vnext & NEXT & IN & LEPUB & LEGUARD).
    exists dnext, Vnext. split; first done.
    split; first (right; done). split; done.
  Qed.

  Lemma node_links_insert sentinel targets nodes node d Vguard
      (FRESH : nodes !! node = None)
      (NONSENTINEL : node ≠ sentinel)
      (NEWLINK : d.(node_next) = sentinel ∨
        ∃ dnext Vnext,
          nodes !! d.(node_next) = Some dnext ∧
          (d.(node_next), Vnext) ∈ targets ∧
          dnext.(node_pub_view) ⊑ d.(node_pub_view) ∧
          Vnext ⊑ d.(node_pub_view))
      (LINKS : node_links sentinel targets nodes) :
    node_links sentinel ((node, Vguard) :: targets) (<[node := d]> nodes).
  Proof.
    intros node0 d0 LOOK.
    destruct (decide (node0 = node)) as [->|NE].
    - rewrite lookup_insert in LOOK. inversion LOOK; subst d0.
      split; first done. destruct NEWLINK as [->|NEWLINK]; first by left.
      right. destruct NEWLINK as (dnext & Vnext & NEXT & IN & LEPUB & LEGUARD).
      exists dnext, Vnext. split.
      + assert (node_next d ≠ node) as NEXTNE.
        { intros EQ. rewrite EQ FRESH in NEXT. congruence. }
        by rewrite lookup_insert_ne.
      + split; first (right; done). split; done.
    - rewrite lookup_insert_ne in LOOK; last done.
      destruct (LINKS _ _ LOOK) as [OLDNON [->|OLDLINK]].
      { split; first done. left; done. }
      split; first done. right.
      destruct OLDLINK as (dnext & Vnext & NEXT & IN & LEPUB & LEGUARD).
      exists dnext, Vnext. split.
      + assert (node_next d0 ≠ node) as NEXTNE.
        { intros EQ. rewrite EQ FRESH in NEXT. congruence. }
        by rewrite lookup_insert_ne.
      + split; first (right; done). split; done.
  Qed.

  (** Every pointer stored in a shared CAS history names one of these stable
      atomic guards.  Guard cells are never reused or freed. *)
  Definition syn_target_record n (target : Loc.t * View.t) : GTerm.t n :=
    (∃ (f t : τ{Time.t}) (LT : τ{Time.lt f t}) (Vmsg : τ{View.t})
       (b : τ{bool}) (γ : τ{gname}),
      @{target.2} target.1 sw↦{γ}
        (Cell.singleton (Message.message Val.zero Vmsg b) LT) ∗
      syn_atomic_swriter n target.1 γ
        (Cell.singleton (Message.message Val.zero Vmsg b) LT) target.2)%SAT.

  Definition target_record (target : Loc.t * View.t) : iProp Σ :=
    ∃ (f t : Time.t) (LT : Time.lt f t) (Vmsg : View.t) b γ,
      @{target.2} target.1 sw↦{γ}
        (Cell.singleton (Message.message Val.zero Vmsg b) LT) ∗
      @{target.2} AtomicSWriter target.1 γ
        (Cell.singleton (Message.message Val.zero Vmsg b) LT).

  Global Instance target_record_red n target :
    SLRed n (syn_target_record n target) (target_record target).
  Proof. solve_sl_red. Qed.

  Fixpoint syn_target_pool n (targets : list (Loc.t * View.t)) : GTerm.t n :=
    match targets with
    | [] => (emp)%SAT
    | target :: targets' =>
        (syn_target_record n target ∗ syn_target_pool n targets')%SAT
    end.

  Fixpoint target_pool (targets : list (Loc.t * View.t)) : iProp Σ :=
    match targets with
    | [] => emp%I
    | target :: targets' => target_record target ∗ target_pool targets'
    end.

  Global Instance target_pool_red n targets :
    SLRed n (syn_target_pool n targets) (target_pool targets).
  Proof. revert n; induction targets; intros; solve_sl_red. Qed.

  Lemma target_pool_lookup targets target :
    target ∈ targets → target_pool targets -∗ target_record target.
  Proof.
    revert target; induction targets as [|target' targets IH]; intros target IN.
    { inversion IN. }
    apply elem_of_cons in IN as [EQ|IN].
    { destruct EQ. simpl; iIntros "[REC _]". iExact "REC". }
    simpl; iIntros "[_ POOL]". iApply (IH _ IN with "POOL").
  Qed.

  Lemma target_record_seen target :
    target_record target -∗ ∃ ζ γ, @{target.2} target.1 sn⊒{γ} ζ.
  Proof.
    iDestruct 1 as (f t LT Vmsg b γ) "[_ SW]".
    iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SN".
    eauto.
  Qed.

  Lemma target_record_take target Vcur (LE : target.2 ⊑ Vcur) :
    target_record target -∗
      ∃ qr Cr Vr γ Cr',
        @{Vr} target.1 p↦{qr} Cr ∗ @{Vcur} target.1 sn⊒{γ} Cr'.
  Proof.
    destruct target as [loc V]. simpl in LE |-*.
    iDestruct 1 as (f t LT Vmsg b γ) "[PT SW]".
    iPoseProof (AtomicSWriter_AtomicSeen with "SW") as "#SN".
    iPoseProof (view_at_view_mon_pred
      (view_at (AtomicSeen loc γ
        (Cell.singleton (Message.message Val.zero Vmsg b) LT))) _ _ LE
      with "SN") as "#SNcur".
    rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
    iDestruct "PT" as (tx) "PT".
    rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def.
    iDestruct "PT" as (C Va ->) "[SYNC [HIST _]]".
    iDestruct "SYNC" as "[SEEN _]".
    rewrite /SeenLocal. iDestruct "SEEN" as %SEEN.
    iExists 1%Qp,
      (Cell.singleton (Message.message Val.zero Vmsg b) LT), V, γ,
      (Cell.singleton (Message.message Val.zero Vmsg b) LT).
    iSplitL "HIST"; last done.
    rewrite /view_at /own_loc_prim.
    iSplit; last done. iPureIntro. split; first apply SEEN.
    eexists t, (f, Message.message Val.zero Vmsg b). split.
    { rewrite Cell.singleton_get. des_ifs. }
    apply SEEN. rewrite Cell.singleton_get. des_ifs; eauto.
  Qed.

  Lemma target_record_prim target :
    target_record target -∗
      ∃ q C V, @{V} target.1 p↦{q} C.
  Proof.
    iIntros "REC".
    iDestruct (target_record_take target target.2 with "REC") as
      (q C V γ C') "[PR _]"; first done.
    iExists q, C, V. done.
  Qed.

  (** [Vstate] and [Vvalue] are the views at which the offer's immutable
      initial state observation and payload were created.  They remain fixed
      across state transitions; publication records that both are below the
      slot message view. *)
  Definition syn_offer_inv n (γo : gname) (offer_loc : Loc.t) (reqid : nat)
      (value : Val.t) (γs : gname) (Vstate Vvalue : View.t) : GTerm.t n :=
    (∃ (state : τ{Val.t}) (ζ ζseen : τ{Cell.t})
       (Vb Vmsg : τ{View.t}) (γ : τ{gname}),
      @{Vb} (offer_loc >> 1) cas↦{γ} ζ ∗
      syn_atomic_seen n (offer_loc >> 1) γ ζseen Vstate ∗
      ⌜Cell.le ζseen ζ ∧ current_message ζ state Vmsg ∧
        numeric_history ζ ∧ cas_history ζ ∧
        offer_state_history ζ state⌝ ∗
      match state with
      | Val.Vnum z =>
          if decide (z = 0%Z) then
            (@{Vvalue} (offer_loc >> 2) ↦ StackHdr.encode value ∗
              syn_HelpPend n reqid (Some stackN) (value, γs)↑↑)%SAT
          else if decide (z = 1%Z) then syn_HelpDone n reqid Val.zero↑↑
          else if decide (z = 2%Z) then sown γo (Excl ())
          else ⌜False⌝
      | _ => ⌜False⌝
      end)%SAT.

  Definition offer_inv (γo : gname) (offer_loc : Loc.t) (reqid : nat)
      (value : Val.t) (γs : gname) (Vstate Vvalue : View.t) : iProp Σ :=
    ∃ (state : Val.t) (ζ ζseen : Cell.t) (Vb Vmsg : View.t) γ,
      @{Vb} (offer_loc >> 1) cas↦{γ} ζ ∗
      @{Vstate} AtomicSeen (offer_loc >> 1) γ ζseen ∗
      ⌜Cell.le ζseen ζ ∧ current_message ζ state Vmsg ∧
        numeric_history ζ ∧ cas_history ζ ∧
        offer_state_history ζ state⌝ ∗
      match state with
      | Val.Vnum z =>
          if decide (z = 0%Z) then
            (@{Vvalue} (offer_loc >> 2) ↦ StackHdr.encode value ∗
              HelpPend reqid (Some stackN) (value, γs)↑↑)%I
          else if decide (z = 1%Z) then HelpDone reqid Val.zero↑↑
          else if decide (z = 2%Z) then own γo (Excl ())
          else ⌜False⌝
      | _ => ⌜False⌝
      end.

  Global Instance offer_inv_red n γo offer_loc reqid value γs Vstate Vvalue :
    SLRed n (syn_offer_inv n γo offer_loc reqid value γs Vstate Vvalue)
      (offer_inv γo offer_loc reqid value γs Vstate Vvalue).
  Proof. solve_sl_red; repeat case_decide; ss. Qed.

  Definition syn_is_offer n (sentinel : Loc.t) (γs : gname)
      (offer : Val.t) (Vpub : View.t) : GTerm.t n :=
    match offer with
    | Val.Vptr offer_loc =>
        if decide (offer_loc = sentinel) then (⌜True⌝)%SAT
        else
          (∃ (Vstate Vvalue : τ{View.t})
             (γinv γo : τ{gname}) (value : τ{Val.t}) (reqid : τ{nat}),
            ⌜Vstate ⊑ Vpub ∧ Vvalue ⊑ Vpub⌝ ∗
            syn_hinv offerN γinv
              (syn_offer_inv n γo offer_loc reqid value γs
                Vstate Vvalue))%SAT
    | _ => (⌜False⌝)%SAT
    end.

  Definition is_offer n (sentinel : Loc.t) (γs : gname)
      (offer : Val.t) (Vpub : View.t) : iProp Σ :=
    match offer with
    | Val.Vptr offer_loc =>
        if decide (offer_loc = sentinel) then True%I
        else (∃ Vstate Vvalue γinv γo value reqid,
          ⌜Vstate ⊑ Vpub ∧ Vvalue ⊑ Vpub⌝ ∗
          hinv offerN γinv
            (syn_offer_inv n γo offer_loc reqid value γs
              Vstate Vvalue))%I
    | _ => False%I
    end.

  Global Instance is_offer_persistent n sentinel γs offer Vpub :
    Persistent (is_offer n sentinel γs offer Vpub).
  Proof. destruct offer; rewrite /is_offer; repeat case_decide; apply _. Qed.

  Global Instance is_offer_red n sentinel γs offer Vpub :
    SLRed n (syn_is_offer n sentinel γs offer Vpub)
      (is_offer n sentinel γs offer Vpub).
  Proof. destruct offer; solve_sl_red; repeat case_decide; ss. Qed.

  Definition stack_inv'_def n (γs : gname) (stack_loc : Loc.t)
      (γh γo γnm : gname) : GTerm.t n :=
    (∃ (vs : τ{list Val.t}) (head offer : τ{Val.t})
       (ζh ζo : τ{Cell.t}) (Vbh Vbo Vh Vo : τ{View.t})
       (targets : τ{list (Loc.t * View.t)})
       (nodes : τ{gmap Loc.t node_desc}),
      sown γs (● Excl' vs) ∗
      @{Vbh} stack_loc cas↦{γh} ζh ∗
      ⌜current_message ζh head Vh ∧ cas_history ζh ∧
        pointer_history (stack_loc >> 2) targets ζh ∧
        head_history (stack_loc >> 2) nodes ζh ∧
        node_links (stack_loc >> 2) targets nodes ∧
        (∃ Vsent, (stack_loc >> 2, Vsent) ∈ targets)⌝ ∗
      syn_live_chain n (stack_loc >> 2) nodes vs head ∗
      @{Vbo} (stack_loc >> 1) cas↦{γo} ζo ∗
      ⌜current_message ζo offer Vo ∧ cas_history ζo ∧
        pointer_history (stack_loc >> 2) targets ζo⌝ ∗
      syn_is_offer n (stack_loc >> 2) γs offer Vo ∗
      syn_target_pool n targets ∗
      syn_node_registry n γnm nodes)%SAT.

  Definition stack_inv'_aux : seal (@stack_inv'_def). Proof. by eexists. Qed.
  Definition stack_inv' := unseal (@stack_inv'_aux).
  Definition stack_inv'_eq : @stack_inv' = _ := seal_eq _.

  Definition stack_inv (n : nat) γs stack_loc γinv γh γo γnm : iProp Σ :=
    hinv stackInvN γinv (stack_inv' n γs stack_loc γh γo γnm).

  Definition stack_handle (γs : gname) (stack : Val.t) (V : View.t) : iProp Σ :=
    ∃ stack_loc γinv γh γo ζh ζo γguard ζguard γnm,
      ⌜stack = Val.Vptr stack_loc ∧ Loc.ofs stack_loc = 0%Z⌝ ∗
      stack_inv 0 γs stack_loc γinv γh γo γnm ∗
      @{V} stack_loc sn⊒{γh} ζh ∗ @{V} (stack_loc >> 1) sn⊒{γo} ζo ∗
      @{V} (stack_loc >> 2) sn⊒{γguard} ζguard.

  Global Instance stack_handle_persistent γs stack V :
    Persistent (stack_handle γs stack V).
  Proof.
    rewrite /stack_handle.
    do 9 (apply bi.exist_persistent; intro).
    repeat (apply bi.sep_persistent; first apply _).
    apply AtomicSeen_persistent.
  Qed.

  Lemma stack_content_exclusive γs vs1 vs2 :
    stack_content γs vs1 -∗ stack_content γs vs2 -∗ False.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hvalid.
    by apply auth_frag_op_valid_1 in Hvalid as [].
  Qed.

  Lemma stack_content_auth_agree γs vs1 vs2 :
    own γs (● Excl' vs1) -∗ stack_content γs vs2 -∗ ⌜vs1 = vs2⌝.
  Proof.
    iIntros "HA HF". iCombine "HA HF" gives %Hvalid.
    apply auth_both_valid_discrete in Hvalid as [Hincluded _].
    by apply Excl_included, leibniz_equiv in Hincluded.
  Qed.

  Lemma stack_content_auth_update γs vs vs' :
    own γs (● Excl' vs) -∗ stack_content γs vs ==∗
      own γs (● Excl' vs') ∗ stack_content γs vs'.
  Proof.
    iIntros "HA HF". iMod (own_update_2 with "HA HF") as "[$ $]"; last done.
    eapply auth_update, option_local_update,
      (exclusive_local_update _ (Excl vs')).
    done.
  Qed.

End stack_resources.

(** A stack operation always opens [stackN].  The generic [atomic_fun]
    quantifies over a caller-chosen private namespace, which is too weak for
    the promise-free implementation: its System specifications and concrete
    invariant both use [stackN].  This fixed variant makes that mask part of
    the operation rather than an unconstrained input. *)
Definition stack_atomic_fun `{!crisG Γ Σ α β τ _S _I} {X X2 : Type}
    (P : X → iProp Σ)
    (body : X → itree crisE (Any.t * X2))
    (Q : X → X2 → Any.t → iProp Σ) : itree crisE Any.t :=
  x <- trigger (Take X);;
  trigger (Assume (winv (↑stackN, ↑stackN) ∗ P x));;;
  '(ret, x2) : _ <- body x;;
  trigger (Guarantee (winv (↑stackN, ↑stackN) ∗ Q x x2 ret));;;
  Ret ret.

(** Intermediate module used by the elimination proof.  A push installs a
    helping request whose job is exactly the abstract LIFO update.  A pop may
    run that job when it wins the offer-state CAS. *)
Module StackM. Section StackM.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS, !histGS, !atomicG, !sysGS,
    !stackG, !helpingGS}.
  Context (mn : string).

  Definition scopes : list string := [].

  Definition new_stack_spec : fspec :=
    fspec_winv (↑stackN)
      (fspec_simple (λ '((tid, stid, V) : Ident.t * nat * TView.t),
        ((λ arg, ⌜arg = tt↑⌝ ∗ tview_sys tid stid V),
         (λ ret, ∃ stack γs V',
            ⌜ret = stack↑⌝ ∗ stack_handle γs stack (TView.cur V') ∗
            stack_content γs [] ∗ tview_sys tid stid V'))))%I.

  Definition push_spec : fspec :=
    fspec_winv (↑stackN)
      (fspec_mk
        (λ '((value, γs, tid, stid, V) :
            Val.t * gname * Ident.t * nat * TView.t) varg arg,
          (∃ stack,
            ⌜varg = (stack, value, γs)↑ ∧ arg = (stack, value)↑⌝ ∗
            stack_handle γs stack (TView.cur V) ∗
            tview_sys tid stid V)%I)
        (λ '((_, _, tid, stid, _) :
            Val.t * gname * Ident.t * nat * TView.t) vret ret,
          (⌜vret = ret⌝ ∗
            ∃ V', ⌜vret = Val.zero↑⌝ ∗ tview_sys tid stid V')%I)).

  Definition jobCode : SAny.t → itree crisE (SAny.t + SAny.t) := λ arg,
    '(value, γs) : Val.t * gname <- arg↓↓?;;
    vs <- trigger (Take (list Val.t));;
    trigger (Assume (stack_content γs vs));;;
    trigger (Guarantee (stack_content γs (value :: vs)));;;
    Ret (inr Val.zero↑↑).

  Definition new_stack : fbody := λ arg,
    '_ : () <- arg↓?;;
    𝒴;;;
    𝒴@{Some stackN};;;
    stack <- trigger (Choose Val.t);;
    Ret stack↑.

  Definition push : fbody := λ arg,
    '(stack, value, γs) : Val.t * Val.t * gname <- arg↓?;;
    𝒴;;;
    trigger (Call (Helping.run mn) (Some stackN, (value, γs)↑↑)↑);;;
    𝒴@{Some stackN};;; Ret Val.zero↑.

  Definition pop : fbody := λ arg,
    stack_atomic_fun
      (λ '((γs, tid, stid, V) : gname * Ident.t * nat * TView.t),
        (∃ stack, ⌜arg = stack↑⌝ ∗
          stack_handle γs stack (TView.cur V) ∗ tview_sys tid stid V)%I)
      (λ '((γs, _, _, _) : gname * Ident.t * nat * TView.t),
        𝒴@{Some stackN};;;
        'help : bool <- trigger (Choose bool);;
        (if help
         then trigger (Call (Helping.help mn) (Some stackN)↑);;; Ret ()
         else Ret ());;;
        <<{ ∀∀ vs, stack_content γs vs,
            match vs with
            | [] => stack_content γs []
            | _ :: vs' => stack_content γs vs'
            end }>> @ stackN)
      (λ '((_, tid, stid, _) : gname * Ident.t * nat * TView.t) vs ret,
        (∃ V',
          ⌜ret = match vs with
                 | [] => Val.Vundef
                 | value :: _ => value
                 end↑⌝ ∗
          tview_sys tid stid V')%I).

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack #
        (msk_scp scopes msk_true, (fsp_some new_stack_spec, new_stack));
      fid StackHdr.push      #
        (msk_scp scopes msk_true, (fsp_some push_spec, push));
      fid StackHdr.pop       # (msk_scp scopes msk_true, (None, pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp : Mod.t := SMod.to_mod sp Mod.
End StackM. End StackM.

Module StackA. Section StackA.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS, !histGS, !atomicG, !sysGS,
    !stackG, !helpingGS}.

  Definition scopes : list string := [].

  (** [new_stack] creates the persistent handle and transfers the unique
      fragment describing an empty abstract stack to the caller. *)
  Definition new_stack : fbody := λ arg,
    stack_atomic_fun
      (λ '((tid, stid, V) : Ident.t * nat * TView.t),
        (⌜arg = tt↑⌝ ∗ tview_sys tid stid V)%I)
      (λ _ : Ident.t * nat * TView.t,
        𝒴;;;
        𝒴@{Some stackN};;; trigger (Choose (Any.t * ())))
      (λ '((tid, stid, _) : Ident.t * nat * TView.t) _ ret,
        (∃ stack γs V',
          ⌜ret = stack↑⌝ ∗ stack_handle γs stack (TView.cur V') ∗
          stack_content γs [] ∗ tview_sys tid stid V')%I).

  (** Both operations expose one logically atomic transition on the same
      authoritative list.  This is the linearizability boundary that the
      Treiber CAS and the elimination hand-off must each refine. *)
  Definition push : fbody := λ arg,
    stack_atomic_fun
      (λ '((value, γs, tid, stid, V) :
          Val.t * gname * Ident.t * nat * TView.t),
        (∃ stack, ⌜arg = (stack, value)↑⌝ ∗
          stack_handle γs stack (TView.cur V) ∗ tview_sys tid stid V)%I)
      (λ '((value, γs, _, _, _) :
          Val.t * gname * Ident.t * nat * TView.t),
        𝒴;;;
        <<{ ∀∀ vs, stack_content γs vs,
            stack_content γs (value :: vs) }>> @ stackN)
      (λ '((_, _, tid, stid, _) :
          Val.t * gname * Ident.t * nat * TView.t) _ ret,
        (∃ V', ⌜ret = Val.zero↑⌝ ∗ tview_sys tid stid V')%I).

  Definition pop : fbody := λ arg,
    stack_atomic_fun
      (λ '((γs, tid, stid, V) : gname * Ident.t * nat * TView.t),
        (∃ stack, ⌜arg = stack↑⌝ ∗
          stack_handle γs stack (TView.cur V) ∗ tview_sys tid stid V)%I)
      (λ '((γs, _, _, _) : gname * Ident.t * nat * TView.t),
        <<{ ∀∀ vs, stack_content γs vs,
            match vs with
            | [] => stack_content γs []
            | _ :: vs' => stack_content γs vs'
            end }>> @ stackN)
      (λ '((_, tid, stid, _) : gname * Ident.t * nat * TView.t) vs ret,
        (∃ V',
          ⌜ret = match vs with
                 | [] => Val.Vundef
                 | value :: _ => value
                 end↑⌝ ∗
          tview_sys tid stid V')%I).

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack # (msk_scp scopes msk_true, (None, new_stack));
      fid StackHdr.push      # (msk_scp scopes msk_true, (None, push));
      fid StackHdr.pop       # (msk_scp scopes msk_true, (None, pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp : Mod.t := SMod.to_mod sp Mod.
End StackA. End StackA.
