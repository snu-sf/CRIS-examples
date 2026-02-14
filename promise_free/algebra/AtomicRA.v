Require Import CRIS.
Require Export Basic Val Cell Loc Time View TView Memory Local Global Configuration.
Require Import LatticeRA ToAgree HistoryRA.

From iris.algebra Require Import frac_auth.
From iris Require Import fractional.

Variant AtomicMode := SingleWriter | CASOnly | ConcurrentWriter.
#[global] Instance AtomicMode_dec : EqDecision AtomicMode.
Proof. solve_decision. Qed.

(* Master-snapshot-style CMRA for histories *)
Definition histBaseUR : ucmra := gmapUR Time.t (agreeR (leibnizO (Time.t * Message.t))).
Definition histMSR    :  cmra := authUR $ histBaseUR.
(* RA for the exclusive write time *)
Definition exWriteR : cmra := frac_authR $ (agreeR positiveO).
(* RA for the last non-atomic write *)
Definition naWriteR : cmra := optionR $ agreeR $ leibnizO View.t.
(* the real one *)
Definition atomicR  : cmra := prodR histMSR (prodR exWriteR naWriteR).

Class atomicG `{!crisG Γ Σ α β τ _S _I} := { #[local] atomic_inG :: inG atomicR Γ; }.
Definition atomicΓ : HRA := #[atomicR].
Global Instance subG_atomicG `{!crisG Γ Σ α β τ _S _I} : subG atomicΓ Γ → atomicG.
Proof. solve_inG. Defined.

Definition toHistBaseUR : Cell.t → histBaseUR := λ c, (to_agreeM (Cell.to_gmap c)).

Lemma toHistBase_included ζ1 ζ2 : Cell.le ζ1 ζ2 ↔ toHistBaseUR ζ1 ≼ toHistBaseUR ζ2.
Proof.
  symmetry. rewrite /toHistBaseUR to_agreeM_included.
  rewrite map_subseteq_spec /Cell.le.
  split; ii.
  { revert LHS; rewrite ?Cell.to_gmap_spec; eauto. }
  { revert H0; rewrite -?Cell.to_gmap_spec; destruct x; eauto. }
Qed.

Implicit Types
  (l : Loc.t) (t : Time.t) (V : View.t) (C ζ : Cell.t) (M : Memory.t) (q : Qp)
  (tid : Ident.t) (𝓥 : TView.t).

Section ghost_defs.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.
  (* TODO : last non-atomic view might be useless to carry around in this model *)
  Definition at_last_na γ (Va : View.t) : iProp Σ :=
    own γ ((ε, (ε, Some $ to_agree Va)) : atomicR).

  Definition at_exclusive_write γ (tx: Time.t) q : iProp Σ :=
    own γ ((ε, (◯F{q} (to_agree tx), ε)) : atomicR).
  Definition at_auth_exclusive_write γ (tx : Time.t) : iProp Σ :=
    own γ ((ε, (●F (to_agree tx), ε)) : atomicR).

  Definition at_writer_base γ ζ q : iProp Σ :=
    own γ ((●{#q} toHistBaseUR ζ ⋅ ◯ toHistBaseUR ζ, (ε,ε)) : atomicR).
  Definition at_writer γ ζ      : iProp Σ := at_writer_base γ ζ (3/4).
  Definition at_auth_writer γ ζ : iProp Σ := at_writer_base γ ζ (1/4).

  Definition at_reader γ ζ      : iProp Σ := own γ ((◯ toHistBaseUR ζ, (ε,ε)) : atomicR).

  Definition at_auth γ ζ (tx : Time.t) (Va : View.t) : iProp Σ :=
    at_auth_writer γ ζ ∗ at_auth_exclusive_write γ tx ∗ at_last_na γ Va.
End ghost_defs.
(* TODO : add properties, and move to a separate file *)

Section ghost_defs.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.
    
  (* at_exclusive_write *)
  #[global] Instance at_exclusive_write_fractional γ t :
    Fractional (at_exclusive_write γ t)%I.
  Proof.
    intros ??. rewrite /at_exclusive_write -own_op -?pair_op.
    repeat f_equiv; ss.
    rewrite -frac_auth_frag_op agree_idemp //.
  Qed.
  #[global] Instance at_exclusive_write_asfractional γ t q :
    AsFractional (at_exclusive_write γ t q) (λ q, at_exclusive_write γ t q)%I q.
  Proof. by apply : Build_AsFractional. Qed.

  Lemma at_exclusive_write_agree γ (t1 t2: Time.t) q1 q2 : 
    at_exclusive_write γ t1 q1 -∗ at_exclusive_write γ t2 q2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ t1 = t2⌝.
  Proof.
    iIntros "H1 H2"; iCombine "H1" "H2" gives %WF.
    rewrite -?pair_op in WF; destruct WF as [_ [WF _]]; ss.
    rewrite -frac_auth_frag_op in WF.
    apply frac_auth_frag_valid in WF as [? ?%to_agree_op_valid_L]; iPureIntro; ss.
  Qed.

  Lemma at_auth_exclusive_write_agree γ (t1 t2: Time.t) q :
    at_auth_exclusive_write γ t1 -∗ at_exclusive_write γ t2 q -∗
    ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2"; iCombine "H1" "H2" gives %WF.
    rewrite -?pair_op in WF; destruct WF as [_ [WF%frac_auth_included_total%to_agree_included _]]; ss.
  Qed.

  Lemma at_full_auth_exclusive_write_agree γ (t1 t2: Time.t) ζ1 V q :
    at_auth γ ζ1 t1 V -∗ at_exclusive_write γ t2 q -∗ ⌜t1 = t2 ⌝.
  Proof. iIntros "(_ & SA & _)". by iApply at_auth_exclusive_write_agree. Qed.

  Lemma at_exclusive_write_exclusive γ t1 t2 :
    at_exclusive_write γ t1 1 -∗ at_exclusive_write γ t2 1 -∗ False.
  Proof.
    iIntros "E1 E2". by iDestruct (at_exclusive_write_agree with "E1 E2") as %[].
  Qed.

  Lemma at_exclusive_write_join γ t1 t2 q1 q2 :
    at_exclusive_write γ t1 q1 -∗ at_exclusive_write γ t2 q2 -∗
    at_exclusive_write γ t1 (q1 + q2).
  Proof.
    iIntros "S1 S2". iDestruct (at_exclusive_write_agree with "S1 S2") as %[? <-].
    iCombine "S1" "S2" as "S". iFrame.
  Qed.

  Lemma at_exclusive_write_update γ t t':
    at_auth_exclusive_write γ t -∗ at_exclusive_write γ t 1%Qp
    ==∗ at_auth_exclusive_write γ t' ∗ at_exclusive_write γ t' 1%Qp.
  Proof.
    apply bi.entails_wand, bi.wand_intro_r.
    rewrite /at_auth_exclusive_write /at_exclusive_write -?own_op -?pair_op.
    apply own_update. apply prod_update; [done|]. apply prod_update; [|done].
    by apply frac_auth_update_1.
  Qed.

  Lemma at_auth_exclusive_write_update γ t ζ Va t':
    at_auth γ ζ t Va -∗ at_exclusive_write γ t 1%Qp
    ==∗ at_auth γ ζ t' Va ∗ at_exclusive_write γ t' 1%Qp.
  Proof. iIntros "($ & SA & $)". by iApply at_exclusive_write_update. Qed.

  Instance at_writer_base_fractional γ ζ : Fractional (at_writer_base γ ζ)%I.
  Proof.
    intros ??. rewrite -own_op -?pair_op /at_writer_base.
    f_equiv; ss. f_equiv; ss.
    rewrite -cmra_assoc (cmra_assoc (◯ _)) (cmra_comm (◯ _)) -cmra_assoc
              (cmra_assoc (●{_} _) (●{_} _)) -auth_auth_dfrac_op -auth_frag_op
              dfrac_op_own.
    f_equiv. rewrite /toHistBaseUR agreeM_idemp //.
  Qed.

  Lemma at_writer_base_valid γ ζ1 ζ2 q1 q2 :
    at_writer_base γ ζ1 q1 -∗ at_writer_base γ ζ2 q2 -∗
    ⌜(q1 + q2 ≤ 1)%Qp ∧ ζ1 = ζ2⌝.
  Proof.
    iIntros "H1 H2"; iCombine "H1" "H2" gives %WF; iPureIntro; move : WF.
    rewrite -pair_op.
    rewrite -cmra_assoc (cmra_assoc (◯ _)) (cmra_comm (◯ _)) -cmra_assoc
            (cmra_assoc (●{_} _) (●{_} _)).
    intros WF; destruct WF as [?%cmra_valid_op_l%auth_auth_dfrac_op_valid _]; des; ss.
    rewrite dfrac_op_own dfrac_valid_own in H; split; eauto.
    apply to_agreeM_agree in H0.
    apply Cell.ext; intros ts; rewrite ?Cell.to_gmap_spec; rewrite H0; ss.
  Qed.

  Lemma at_writer_exclusive γ ζ1 ζ2 : at_writer γ ζ1 -∗ at_writer γ ζ2 -∗ False.
  Proof. iIntros "W1 W2". by iDestruct (at_writer_base_valid with "W1 W2") as %[]. Qed.

  Lemma at_auth_writer_exact γ ζ ζ' :
    at_auth_writer γ ζ -∗ at_writer γ ζ' -∗ ⌜ζ = ζ'⌝.
  Proof. iIntros "W1 W2". by iDestruct (at_writer_base_valid with "W1 W2") as %[]. Qed.

  Lemma at_auth_at_writer_exact γ ζ ζ' tx Va:
    at_auth γ ζ tx Va -∗ at_writer γ ζ' -∗ ⌜ζ = ζ'⌝.
  Proof. iIntros "(AW & EX & NA)". by iApply at_auth_writer_exact. Qed.

  Lemma at_writer_base_update γ ζ ζ' (Sub: Cell.le ζ ζ') :
    at_writer_base γ ζ 1 ==∗ at_writer_base γ ζ' 1.
  Proof.
    apply bi.entails_wand, own_update, prod_update; simpl; [|done].
    apply auth_update; rewrite /toHistBaseUR; apply to_agreeM_local_update.
    rewrite map_subseteq_spec; intros ts [??]; rewrite -?Cell.to_gmap_spec.
    eapply (Sub ts); eauto.
  Qed.

  Lemma at_writer_update γ ζ ζ' (Sub: Cell.le ζ ζ'):
    at_auth_writer γ ζ -∗ at_writer γ ζ ==∗ at_auth_writer γ ζ' ∗ at_writer γ ζ'.
  Proof.
    apply bi.entails_wand, bi.wand_intro_r.
    rewrite /at_auth_writer /at_writer.
    rewrite -!fractional Qp.quarter_three_quarter.
    by apply bi.wand_entails, at_writer_base_update.
  Qed.

  Lemma at_writer_update' γ ζ0 ζ ζ' (Sub : Cell.le ζ ζ'):
    at_auth_writer γ ζ0 -∗ at_writer γ ζ ==∗ at_auth_writer γ ζ' ∗ at_writer γ ζ'.
  Proof.
    iIntros "oA W". iDestruct (at_auth_writer_exact with "oA W") as %->.
    by iApply (at_writer_update with "oA W").
  Qed.

  (* writers and readers *)
  Lemma at_writer_base_latest γ q ζ1 ζ2 :
    at_writer_base γ ζ2 q -∗ at_reader γ ζ1 -∗ ⌜Cell.le ζ1 ζ2⌝.
  Proof.
    rewrite /at_writer_base /at_reader.
    iIntros "H1 H2"; iCombine "H1" "H2" gives %WF; iPureIntro; revert WF.
    rewrite -pair_op -(cmra_assoc (●{_} toHistBaseUR ζ2)) -auth_frag_op.
    rewrite pair_valid; intros [WF _].
    apply auth_both_dfrac_valid_discrete in WF; des.
    apply toHistBase_included.
    etrans; last done; eauto using cmra_included_r.
  Qed.

  Lemma at_writer_reader_latest γ ζ1 ζ2 :
    at_writer γ ζ2 -∗ at_reader γ ζ1 -∗ ⌜Cell.le ζ1 ζ2⌝.
  Proof. iIntros "H1 H2"; iApply (at_writer_base_latest with "H1"); done. Qed.

  Lemma at_auth_writer_reader_latest γ ζ1 ζ2 :
    at_auth_writer γ ζ2 -∗ at_reader γ ζ1 -∗ ⌜Cell.le ζ1 ζ2⌝.
  Proof. iIntros "H1 H2"; iApply (at_writer_base_latest with "H1"); done. Qed.

  Lemma at_auth_reader_latest γ ζ1 tx Va ζ2 :
    at_auth γ ζ2 tx Va -∗ at_reader γ ζ1 -∗ ⌜Cell.le ζ1 ζ2⌝.
  Proof. iIntros "[H1 H3] H2"; iApply (at_writer_base_latest with "H1"); done. Qed.

  Lemma at_reader_extract γ ζ1 ζ2 (Sub: Cell.le ζ2 ζ1) :
    at_reader γ ζ1 -∗ at_reader γ ζ2.
  Proof.
    apply bi.entails_wand, own_mono, prod_included. split; [|done].
    by apply auth_frag_mono, toHistBase_included.
  Qed.

  Lemma at_writer_base_fork_at_reader γ q ζ :
    at_writer_base γ ζ q ⊢ at_reader γ ζ.
  Proof. by iIntros "[_ $]". Qed.

  Lemma at_writer_fork_at_reader γ ζ : at_writer γ ζ ⊢ at_reader γ ζ.
  Proof. by apply at_writer_base_fork_at_reader. Qed.

  Lemma at_auth_writer_fork_at_reader γ ζ :
    at_auth_writer γ ζ ⊢ at_reader γ ζ.
  Proof. by apply at_writer_base_fork_at_reader. Qed.

  Lemma at_auth_fork_at_reader γ ζ tx Va :
    at_auth γ ζ tx Va -∗ at_reader γ ζ.
  Proof. iIntros "(?&_)". by iApply at_auth_writer_fork_at_reader. Qed.

  Lemma at_last_na_agree γ (V1 V2 : View.t) :
    at_last_na γ V1 -∗ at_last_na γ V2 -∗ ⌜V1 = V2⌝.
  Proof.
    iIntros "H1 H2"; iCombine "H1" "H2" gives %WF; revert WF.
    rewrite -?pair_op ?pair_valid; intros [_ [_ WF]].
    move : WF => /to_agree_op_inv_L //.
  Qed.

  Lemma at_last_na_dup γ V :
    at_last_na γ V ∗ at_last_na γ V ⊣⊢ at_last_na γ V.
  Proof. by rewrite -bi.persistent_sep_dup. Qed.

  Lemma at_auth_at_last_na_agree γ ζ tx Va Va' :
    at_auth γ ζ tx Va -∗ at_last_na γ Va' -∗ ⌜Va = Va'⌝.
  Proof. iIntros "(_&_&NA)". by iApply at_last_na_agree. Qed.

  Lemma at_auth_fork_at_last_na γ ζ tx Va :
    at_auth γ ζ tx Va -∗ at_last_na γ Va.
  Proof. by iIntros "(_&_&$)". Qed.

  Lemma at_full_auth_join γ ζ t V :
    at_auth γ ζ t V ∗ at_writer γ ζ ∗
    at_exclusive_write γ t 1%Qp ∗ at_last_na γ V
    ⊣⊢ at_writer_base γ ζ 1 ∗
      (at_auth_exclusive_write γ t ∗ at_exclusive_write γ t 1) ∗ at_last_na γ V.
  Proof.
    rewrite /at_auth bi.sep_assoc (bi.sep_comm _ (at_writer _ _)).
    rewrite (bi.sep_assoc (at_writer _ _) (at_auth_writer _ _)) -fractional.
    rewrite bi.sep_assoc -(bi.sep_comm _ (at_auth_exclusive_write _ _)).
    rewrite bi.sep_assoc -(bi.sep_assoc _ (at_auth_exclusive_write _ _)).
    rewrite Qp.three_quarter_quarter.
    rewrite 2!(bi.sep_comm _ (at_last_na _ _)) 3!bi.sep_assoc.
    rewrite at_last_na_dup.
    rewrite (bi.sep_comm (at_last_na _ _)) -!bi.sep_assoc.
    by rewrite (bi.sep_comm (at_last_na _ _)) -!bi.sep_assoc.
  Qed.

  Lemma at_full_auth_alloc ζ t V Ew E :
    ⊢ =|0, Ew|={E}=> ∃ γ,
      at_auth γ ζ t V ∗ at_writer γ ζ ∗ at_exclusive_write γ t 1%Qp ∗ at_last_na γ V.
  Proof.
    setoid_rewrite at_full_auth_join.
    do 3 setoid_rewrite <- own_op.
    iStartProof; iMod (own_alloc); last by iFrame.
    rewrite -?pair_op /=; split; ss.
    { rewrite ?right_id auth_both_valid_discrete; split; [done | apply to_agreeM_valid]. }
    { split; ss.
      rewrite left_id right_id auth_both_dfrac_valid_discrete; split; ss.
    }
  Qed.
End ghost_defs.

Section atomic_preds.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Definition SeenLocal loc ζ V : iProp Σ :=
    ⌜ View.alloc_view V (Loc.get_tbid loc) (* is not in iRC11 *)
      ∧ ∀ t, is_Some (Cell.get t ζ) → seen_local loc t V ⌝%I.
  Definition SyncLocal loc ζ V : iProp Σ :=
    SeenLocal loc ζ V ∗
    ∀ t f v b V', ⌜Cell.get t ζ = Some (f, Message.message v V' b) → seen_view loc t V' V⌝.

  (* TODO : may not need V at all *)
  Definition AtomicPtsToX_def l γ t ζ (mode : AtomicMode) V : iProp Σ :=
    ∃ C (Va : View.t),
      (* TODO : set relation between physical/logical states of the memory *)
      (* ⌜good_hist C ∧ ζ = toAbsHist C Va ∧ is_Some (ζ !! tx) ∧ no_dealloc C⌝ ∗ *)
      ⌜ C = ζ ⌝ ∗
      (* local assertions *)
      (* DELETED :(SyncLocal l ζ ∗ AtRLocal l rsa ∗ AtWLocal l ws ∗ NaLocal l rsn Va) ∗ *)
      SyncLocal l ζ V ∗
      (* own the history of l *)
      hist l 1 C ∗
      (* DELETED : and related race detector states *)
      (* ⎡ atread l 1 rsa ∗ atwrite l 1 ws ∗ naread l 1 rsn ⎤ ∗ *)
      (* authoritative ghost state of this construction *)
      at_auth γ ζ t Va ∗
      (* controller for location mode *)
      match mode with
      | SingleWriter => True
      | CASOnly => at_writer γ ζ
      | ConcurrentWriter => at_writer γ ζ ∗ at_exclusive_write γ t 1
      end.
  Definition AtomicPtsToX_aux : seal (@AtomicPtsToX_def). Proof. by eexists. Qed.
  Definition AtomicPtsToX := unseal (@AtomicPtsToX_aux).
  Definition AtomicPtsToX_eq : @AtomicPtsToX = _ := seal_eq _.

  Definition AtomicPtsTo_def l γ ζ (mode : AtomicMode) V : iProp Σ :=
    ∃ (tx : Time.t), AtomicPtsToX l γ tx ζ mode V.
  Definition AtomicPtsTo_aux : seal (@AtomicPtsTo_def). Proof. by eexists. Qed.
  Definition AtomicPtsTo := unseal (@AtomicPtsTo_aux).
  Definition AtomicPtsTo_eq : @AtomicPtsTo = _ := seal_eq _.

  (* Both [AtomicSeen] and [AtomicSync] have observed the last non-atomic event,
    as required by [NaLocal]. *)
  (* [AtomicSeen] says that one has observed the writes in ζ, but not necessarily
    synchronized with them. *)
  Definition good_absHist ζ : Prop :=
    ζ ≠ Cell.bot.

  Definition AtomicSeen_def l γ ζ V : iProp Σ :=
    SeenLocal l ζ V (* seen the writes, but not sync *)
    ∗ at_reader γ ζ
    ∗ ⌜good_absHist ζ⌝
    ∗ ∃ Va, ⌜Va ⊑ V⌝ ∗ at_last_na γ Va.
  Definition AtomicSeen_aux : seal (@AtomicSeen_def). Proof. by eexists. Qed.
  Definition AtomicSeen := unseal (@AtomicSeen_aux).
  Definition AtomicSeen_eq : @AtomicSeen = _ := seal_eq _.

  (* [AtomicSync] additionally says that it is synced. *)
  Program Definition AtomicSync_def l γ ζ V : iProp Σ :=
    SyncLocal l ζ V (* seen the writes, and sync *)
    ∗ at_reader γ ζ
    ∗ ⌜good_absHist ζ⌝
    ∗ ∃ Va, ⌜Va ⊑ V⌝ ∗ at_last_na γ Va.
  Definition AtomicSync_aux : seal (@AtomicSync_def). Proof. by eexists. Qed.
  Definition AtomicSync := unseal (@AtomicSync_aux).
  Definition AtomicSync_eq : @AtomicSync = _ := seal_eq _.

  (* A unique writer is synced, and hold the max exclusive writer *)
  Definition AtomicSWriter_def l γ ζ V : iProp Σ :=
    AtomicSync l γ ζ V
    ∗ at_writer γ ζ
    ∗ at_exclusive_write γ (Cell.max_ts ζ) 1%Qp.
  Definition AtomicSWriter_aux : seal (@AtomicSWriter_def). Proof. by eexists. Qed.
  Definition AtomicSWriter := unseal (@AtomicSWriter_aux).
  Definition AtomicSWriter_eq : @AtomicSWriter = _ := seal_eq _.

  (* A CASer holds a share of the shared writer *)
  Definition AtomicCASerX_def l γ tx ζ q V : iProp Σ :=
    AtomicSeen l γ ζ V
    ∗ at_exclusive_write γ tx q
    ∗ ⌜is_Some (Cell.get tx ζ)⌝.
  Definition AtomicCASerX_aux : seal (@AtomicCASerX_def). Proof. by eexists. Qed.
  Definition AtomicCASerX := unseal (@AtomicCASerX_aux).
  Definition AtomicCASerX_eq : @AtomicCASerX = _ := seal_eq _.

  Definition AtomicCASer_def l γ ζ q V : iProp Σ :=
    ∃ tx, AtomicCASerX l γ tx ζ q V.
  Definition AtomicCASer_aux : seal (@AtomicCASer_def). Proof. by eexists. Qed.
  Definition AtomicCASer := unseal (@AtomicCASer_aux).
  Definition AtomicCASer_eq : @AtomicCASer = _ := seal_eq _.
End atomic_preds.

Global Instance: Params (@AtomicPtsToX) 5 := {}.
Global Instance: Params (@AtomicPtsTo) 5 := {}.
Global Instance: Params (@AtomicSeen) 4 := {}.
Global Instance: Params (@AtomicSync) 4 := {}.
Global Instance: Params (@AtomicSWriter) 4 := {}.
Global Instance: Params (@AtomicCASerX) 4 := {}.
Global Instance: Params (@AtomicCASerX) 4 := {}.

Section syn_atomic_preds.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Definition syn_SeenLocal n loc ζ V : GTerm.t n :=
    ⌜ View.alloc_view V (Loc.get_tbid loc) (* is not in iRC11 *)
    ∧ ∀ t, is_Some (Cell.get t ζ) → seen_local loc t V ⌝%SAT.
  Instance syn_SeenLocal_red n loc ζ V :
    SLRed n (syn_SeenLocal n loc ζ V) (SeenLocal loc ζ V).
  Proof. solve_base_sl_red. Qed.

  Definition syn_SyncLocal n loc ζ V : GTerm.t n :=
    syn_SeenLocal n loc ζ V ∗
    ⌜∀ t f v b V', Cell.get t ζ = Some (f, Message.message v V' b) → seen_view loc t V' V⌝%SAT.
  Lemma syn_SyncLocal_red n loc ζ V :
    SLRed n (syn_SyncLocal n loc ζ V) (SyncLocal loc ζ V).
  Proof. solve_base_sl_red. iSplit; iIntros "%"; iPureIntro; ss. Qed.

  (* TODO : last non-atomic view might be useless to carry around in this model *)
  Definition syn_at_last_na n γ (Va : View.t) : GTerm.t n :=
    sown γ ((ε, (ε, Some $ to_agree Va)) : atomicR).

  Definition syn_at_exclusive_write n γ (tx: Time.t) q : GTerm.t n :=
    sown γ ((ε, (◯F{q} (to_agree tx), ε)) : atomicR).
  Definition syn_at_auth_exclusive_write n γ (tx : Time.t) : GTerm.t n :=
    sown γ ((ε, (●F (to_agree tx), ε)) : atomicR).

  Definition syn_at_writer_base n γ ζ q : GTerm.t n :=
    sown γ ((●{#q} toHistBaseUR ζ ⋅ ◯ toHistBaseUR ζ, (ε,ε)) : atomicR).
  Definition syn_at_writer n γ ζ      : GTerm.t n := syn_at_writer_base n γ ζ (3/4).
  Definition syn_at_auth_writer n γ ζ : GTerm.t n := syn_at_writer_base n γ ζ (1/4).

  Definition syn_at_reader n γ ζ      : GTerm.t n := sown γ ((◯ toHistBaseUR ζ, (ε,ε)) : atomicR).

  Definition syn_at_auth n γ ζ (tx : Time.t) (Va : View.t) : GTerm.t n :=
    syn_at_auth_writer n γ ζ ∗ syn_at_auth_exclusive_write n γ tx ∗ syn_at_last_na n γ Va.

  Definition syn_AtomicPtsToX_def n l γ t ζ (mode : AtomicMode) V : GTerm.t n :=
    (∃ (C : τ{Cell.t}) (Va : τ{View.t}),
      ⌜ C = ζ ⌝ ∗
      syn_SyncLocal n l ζ V ∗
      syn_hist n l 1 C ∗
      syn_at_auth n γ ζ t Va ∗
      match mode with
      | SingleWriter => emp
      | CASOnly => syn_at_writer n γ ζ
      | ConcurrentWriter => syn_at_writer n γ ζ ∗ syn_at_exclusive_write n γ t 1
      end)%SAT.
  Definition syn_AtomicPtsToX_aux : seal (@syn_AtomicPtsToX_def). Proof. by eexists. Qed.
  Definition syn_AtomicPtsToX := unseal (@syn_AtomicPtsToX_aux).
  Definition syn_AtomicPtsToX_eq : @syn_AtomicPtsToX = _ := seal_eq _.

  Lemma syn_AtomicPtsToX_red n l γ t ζ mode V :
    SLRed n (syn_AtomicPtsToX n l γ t ζ mode V) (AtomicPtsToX l γ t ζ mode V).
  Proof.
    rewrite syn_AtomicPtsToX_eq AtomicPtsToX_eq /AtomicPtsToX_def; solve_sl_red.
    { rewrite /SyncLocal; iSplit; iIntros "[$ %]"; iPureIntro; ss. }
    rewrite hist_eq; refl.
  Qed.

  Definition syn_AtomicPtsTo_def n l γ ζ (mode : AtomicMode) V : GTerm.t n :=
    (∃ (tx : τ{Time.t}), syn_AtomicPtsToX n l γ tx ζ mode V)%SAT.
  Definition syn_AtomicPtsTo_aux : seal (@syn_AtomicPtsTo_def). Proof. by eexists. Qed.
  Definition syn_AtomicPtsTo := unseal (@syn_AtomicPtsTo_aux).
  Definition syn_AtomicPtsTo_eq : @syn_AtomicPtsTo = _ := seal_eq _.

  Lemma syn_AtomicPtsTo_red n l γ ζ mode V :
    ⟦@{V} syn_AtomicPtsTo n l γ ζ mode⟧ ⊣⊢ @{V} AtomicPtsTo l γ ζ mode.
  Proof.
    rewrite syn_AtomicPtsTo_eq /syn_AtomicPtsTo_def AtomicPtsTo_eq /AtomicPtsTo_def; solve_base_sl_red.
    by iSplit; iIntros "[%x I]"; iExists x; rewrite syn_AtomicPtsToX_red; done.
  Qed.
End syn_atomic_preds.

Notation "l 'casX↦{' γ , tx '}' ζ" := (AtomicPtsToX l γ tx ζ CASOnly)
  (at level 20, format "l  casX↦{ γ , tx }  ζ")  : bi_scope.
Notation "l 'swX↦{' γ , tx '}' ζ" := (AtomicPtsToX l γ tx ζ SingleWriter)
  (at level 20, format "l  swX↦{ γ , tx }  ζ")  : bi_scope.
Notation "l 'atX↦{' γ , tx '}' ζ" := (AtomicPtsToX l γ tx ζ ConcurrentWriter)
  (at level 20, format "l  atX↦{ γ , tx }  ζ")  : bi_scope.

Notation "l 'cas↦{' γ '}' ζ" := (AtomicPtsTo l γ ζ CASOnly)
  (at level 20, format "l  cas↦{ γ }  ζ")  : bi_scope.
Notation "l 'sw↦{' γ '}' ζ" := (AtomicPtsTo l γ ζ SingleWriter)
  (at level 20, format "l  sw↦{ γ }  ζ")  : bi_scope.
Notation "l 'at↦{' γ '}' ζ" := (AtomicPtsTo l γ ζ ConcurrentWriter)
  (at level 20, format "l  at↦{ γ }  ζ")  : bi_scope.

(* SAT notations *)
Notation "l 'cas↦{' γ '}' ζ" := (syn_AtomicPtsTo _ l γ ζ CASOnly)
  (at level 20, format "l  cas↦{ γ }  ζ") : SAT_scope.
Notation "l 'sw↦{' γ '}' ζ" := (syn_AtomicPtsTo _ l γ ζ SingleWriter)
  (at level 20, format "l  sw↦{ γ }  ζ") : SAT_scope.
Notation "l 'at↦{' γ '}' ζ" := (syn_AtomicPtsTo _ l γ ζ ConcurrentWriter)
  (at level 20, format "l  at↦{ γ }  ζ") : SAT_scope.

Notation "l 'sn⊒{' γ '}' ζ" := (AtomicSeen l γ ζ)
  (at level 20, format "l  sn⊒{ γ }  ζ")  : bi_scope.
Notation "l 'sy⊒{' γ '}' ζ" := (AtomicSync l γ ζ)
  (at level 20, format "l  sy⊒{ γ }  ζ")  : bi_scope.
Notation "l 'sw⊒{' γ '}' ζ" := (AtomicSWriter l γ ζ)
  (at level 20, format "l  sw⊒{ γ }  ζ")  : bi_scope.
Notation "l 'cas⊒{' γ ',' q '}' ζ" := (AtomicCASer l γ ζ q)
  (at level 20, format "l  cas⊒{ γ , q }  ζ")  : bi_scope.
Notation "l 'casX⊒{' γ ',' t ',' q '}' ζ" := (AtomicCASerX l γ t ζ q)
  (at level 20, format "l  casX⊒{ γ , t , q }  ζ")  : bi_scope.

Section atomic_preds.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.
  (* Instances *)
  #[global] Instance SeenLocal_mon_pred l ζ : MonPred (SeenLocal l ζ).
  Proof.
    econs; intros ?? [Hle Ha]; iIntros "[% %Hle']"; iPureIntro; split; first by apply Ha.
    rewrite /seen_local; ii; etrans; last apply Hle; eapply Hle'; done.
  Qed.
  #[global] Instance SyncLocal_mon_pred l ζ : MonPred (SyncLocal l ζ).
  Proof.
    econs; intros ?? [Hle Ha]; iIntros "[[% %Hle'] %Hsv]"; iPureIntro; split.
    { split; first by apply Ha.
      rewrite /seen_local; ii; etrans; last apply Hle; eapply Hle'; done.
    }
    { i; hexploit Hsv; eauto; rewrite /seen_view /seen_local; i; des; split; etrans; eauto.
      { eapply Hle. }
      { econs; eauto. }
    }
  Qed.

  #[global] Instance AtomicSeen_persistent l γ ζ V : Persistent (@{V} AtomicSeen l γ ζ).
  Proof. rewrite AtomicSeen_eq. by apply _. Qed.
  #[global] Instance AtomicSeen_mon_pred l γ ζ : MonPred (AtomicSeen l γ ζ).
  Proof.
    econs; intros ?? Hle; rewrite AtomicSeen_eq /AtomicSeen_def.
    iIntros "[H [$ [$ [% [% $]]]]]"; rewrite Hle; iFrame "H".
    by iPureIntro; etrans.
  Qed.

  #[global] Instance AtomicSync_persistent l γ ζ V : Persistent (@{V} AtomicSync l γ ζ).
  Proof. rewrite AtomicSync_eq. by apply _. Qed.
  #[global] Instance AtomicSync_mon_pred l γ ζ : MonPred (AtomicSync l γ ζ).
  Proof.
    econs; intros ?? Hle; rewrite AtomicSync_eq /AtomicSync_def.
    iIntros "[H [$ [$ [% [% $]]]]]"; rewrite Hle; iFrame "H".
    by iPureIntro; etrans.
  Qed.

  #[global] Instance AtomicSWriter_mon_pred l γ ζ : MonPred (AtomicSWriter l γ ζ).
  Proof.
    econs; intros ?? Hle; rewrite AtomicSWriter_eq /AtomicSWriter_def Hle. iIntros "[$ [$ $]]".
  Qed.

  #[global] Instance AtomicCASerX_fractional l γ t ζ V :
    Fractional (λ q, @{V} AtomicCASerX l γ t ζ q)%I.
  Proof.
    rewrite /Fractional =>p q. rewrite AtomicCASerX_eq /AtomicCASerX_def /view_at.
    setoid_rewrite fractional. iSplit.
    - iIntros "[#$ ([Hp Hq] & #Le)]". iSplitL "Hp"; by iFrame "#∗".
    - iIntros "[[$ [Hp ?]] [_ [Hq ?]]]". by iFrame.
  Qed.
  #[global] Instance AtomicCASerX_asfractional l γ t ζ q V :
    AsFractional (@{V} l casX⊒{γ,t,q} ζ)%I (λ q, @{V} l casX⊒{γ,t,q} ζ)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma AtomicCASerX_agree_time l γ t1 t2 ζ1 ζ2 q1 q2 V1 V2 :
    @{V1} l casX⊒{γ,t1,q1} ζ1 -∗ @{V2} l casX⊒{γ,t2,q2} ζ2 -∗ ⌜ t1 = t2 ⌝.
  Proof.
    rewrite AtomicCASerX_eq. iIntros "(_ & H1 & _) (_ & H2 & _)".
    by iDestruct (at_exclusive_write_agree with "H1 H2") as %[_ <-].
  Qed.

  Lemma SeenLocal_SyncLocal_singleton loc to from val V_msg na V LT :
    let ζ := @Cell.singleton from to (Message.message val V_msg na) LT in
    ⌜ V_msg ⊑ V ⌝ ⊢ SeenLocal loc ζ V -∗ SyncLocal loc ζ V.
  Proof.
    iIntros (ζ) "%SV [%SA %SL]". rewrite /SeenLocal /SyncLocal. iSplit; iPureIntro; ss.
    intros ts; rewrite Cell.singleton_get; des_ifs; ss; intros ???? INV; inv INV.
    rewrite /seen_view; split; ss.
    eapply SL; rewrite Cell.singleton_get; des_ifs.
  Qed.

  Lemma SyncLocal_SeenLocal l ζ V : @{V} SyncLocal l ζ ⊢ @{V} SeenLocal l ζ.
  Proof. iIntros "[$ _]". Qed.

  (* AtomicSeen *)
  Lemma AtomicSeen_non_empty V l γ ζ : @{V} l sn⊒{γ} ζ ⊢ ⌜ ζ ≠ Cell.bot ⌝.
    Proof. rewrite AtomicSeen_eq. iIntros "(_ & _ & E)". iDestruct "E" as "[? _]"; done. Qed.

  Lemma AtomicPtsToX_AtomicSeen_latest l γ t ζ ζ' m V V' :
    @{V} AtomicPtsToX l γ t ζ m ⊢ @{V'} l sn⊒{γ} ζ' -∗ ⌜Cell.le ζ' ζ⌝.
  Proof.
    rewrite AtomicPtsToX_eq AtomicSeen_eq /AtomicPtsToX_def /AtomicSeen_def /view_at.
    iDestruct 1 as (??) "(_ & _ & _ & SA & _)". iIntros "(_ & R & _)".
    by iDestruct (at_auth_reader_latest with "[$SA] [$R]") as %?.
  Qed.

    Lemma AtomicSeen_alloc_view loc γ ζ V :
    @{V} loc sn⊒{γ} ζ ⊢ ⌜(View.alloc_view V) (Loc.get_tbid loc)⌝.
  Proof.
    rewrite /view_at AtomicSeen_eq /AtomicSeen_def; iIntros "[%SN _]"; iPureIntro; des; done.
  Qed.

  Lemma AtomicSeen_non_empty' loc γ ζ V :
    @{V} loc sn⊒{γ} ζ ⊢ ∃ to from msg, ⌜Cell.get to ζ = Some (from, msg)⌝.
  Proof.
    iIntros "S"; iPoseProof (AtomicSeen_non_empty with "S") as "%NE".
    destruct (classic (∃ ts' f' m', Cell.get ts' ζ = Some (f', m'))) as [HEX|FAL]; cycle 1.
    { exfalso; apply NE, Cell.ext; i; rewrite Cell.bot_get.
      destruct (Cell.get ts ζ) eqn : GET'; ss. destruct p; exfalso; apply FAL; esplits; eauto.  
    }
    des; eauto.
  Qed.

  Lemma AtomicSeen_max_ts loc γ ζ V :
    @{V} loc sn⊒{γ} ζ ⊢ ⌜Time.le (Cell.max_ts ζ) ((View.rlx V) loc)⌝.
  Proof.
    iIntros "S"; iPoseProof (AtomicSeen_non_empty' with "S") as "%NE".
    rewrite /view_at AtomicSeen_eq /AtomicSeen_def; iDestruct "S" as "[[_ %SN] _]"; iPureIntro; des.
    hexploit Cell.max_ts_spec; eauto; i; des; eapply SN; ss.
  Qed.

  (* AtomicSync *)
  Lemma AtomicSync_AtomicSeen l γ ζ V : @{V} l sy⊒{γ} ζ ⊢ @{V} l sn⊒{γ} ζ.
  Proof.
    rewrite AtomicSync_eq AtomicSeen_eq /AtomicSync_def /AtomicSeen_def /view_at.
    by iIntros "[[$ ?] [$ $]]".
  Qed.

  (* AtomicSWriter *)
  Lemma AtomicSWriter_AtomicSync l γ ζ V : @{V} l sw⊒{γ} ζ ⊢ @{V} l sy⊒{γ} ζ.
  Proof. rewrite AtomicSWriter_eq. iDestruct 1 as "($ & ?)". Qed.

  Lemma AtomicSWriter_AtomicSeen l γ ζ V : @{V} l sw⊒{γ} ζ ⊢ @{V} l sn⊒{γ} ζ.
  Proof. rewrite -AtomicSync_AtomicSeen. by apply AtomicSWriter_AtomicSync. Qed.

  Lemma AtomicPtsToX_at_writer_agree l γ t1 ζ1 ζ2 mode V1 :
    @{V1}(AtomicPtsToX l γ t1 ζ1 mode) -∗ at_writer γ ζ2 -∗ ⌜ζ1 = ζ2⌝.
  Proof.
    rewrite AtomicPtsToX_eq. iDestruct 1 as (??) "(_&_&_&SA&_)". iIntros "W".
    by iDestruct (at_auth_at_writer_exact with "[$SA] [$W]") as %?.
  Qed.

  Lemma AtomicPtsToX_SWriter_agree l γ t1 ζ1 ζ2 mode V1 V2 :
    @{V1}(AtomicPtsToX l γ t1 ζ1 mode) ⊢ @{V2} l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
  Proof.
    rewrite AtomicSWriter_eq. iIntros "P [_ [W1 _]]".
    iApply (AtomicPtsToX_at_writer_agree with "P [$]").
  Qed.

  Lemma AtomicPtsTo_SWriter_agree l γ ζ1 ζ2 mode V1 V2 :
    @{V1}(AtomicPtsTo l γ ζ1 mode) ⊢ @{V2} l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
  Proof.
    rewrite AtomicPtsTo_eq. apply bi.exist_elim => ?.
    by apply AtomicPtsToX_SWriter_agree.
  Qed.

  Lemma AtomicPtsToX_from_na l v Vinit Ew E :
    let Vcur := TView.cur Vinit in
    @{Vcur} l ↦ v =|0, Ew|={E}=∗
    ∃ γ t f LT V na, let ζ := @Cell.singleton f t (Message.message v V na) LT in
      ⌜V ⊑ Vcur⌝ ∗ @{Vcur} l sw⊒{γ} ζ ∗ @{Vcur} l swX↦{γ,t} ζ.
  Proof.
    iIntros (Vcur); rewrite /view_at own_loc_na_eq /own_loc_na_def.
    rewrite AtomicPtsToX_eq /AtomicPtsToX_def.
    iDestruct 1 as (f t ? Vmsg na) "[[%Hal l↦] %Hseen]".
    iMod (at_full_auth_alloc _ t) as "[%γ [AA [AW [AEW #ALN]]]]".
    iPoseProof (at_auth_fork_at_reader with "AA") as "#AR".
    set (ζ := Cell.singleton (Message.message v Vmsg na) LT).
    iModIntro. iExists γ, t, f, LT, Vmsg, na; iSplit; first done.
    iAssert (SyncLocal l ζ Vcur) as "#SL".
    { iApply SeenLocal_SyncLocal_singleton; first done.
      iPureIntro; destruct Hal as [Hav Hs]; split; first done.
      intros ?; rewrite Cell.singleton_get; des_ifs; intros INV; inv INV.
      destruct Hs as [? [? [Hget ?]]]; rewrite Cell.singleton_get in Hget; des_ifs; ss.
    }
    iSplitL "AW AEW".
    { rewrite AtomicSWriter_eq /AtomicSWriter_def /= Cell.max_ts_singleton. iFrame "AW AEW".
      rewrite AtomicSync_eq /AtomicSync_def /=; iFrame "SL AR ALN".
      iDestruct "SL" as "[? ?]".
      iSplit; last ss.
      iPureIntro; intros EQ; hexploit (Cell.bot_get t); rewrite -EQ Cell.singleton_get; des_ifs.
    }
    iFrame "AA SL"; iExists _; iSplit; done.
  Qed.

  Lemma AtomicPtsTo_from_na l v Vinit Ew E :
    let Vcur := TView.cur Vinit in
    @{Vcur} l ↦ v =|0, Ew|={E}=∗
    ∃ γ t f LT V na, let ζ := @Cell.singleton f t (Message.message v V na) LT in
      ⌜V ⊑ Vcur⌝ ∗ @{Vcur} l sw⊒{γ} ζ ∗ @{Vcur} l sw↦{γ} ζ.
  Proof.
    iIntros (?) "PT"; iMod (AtomicPtsToX_from_na with "PT") as "(%&%&%&%&%&%&[$ [$ ↦]])".
    iModIntro; rewrite /view_at AtomicPtsTo_eq; iExists t; done.
  Qed.
End atomic_preds.
