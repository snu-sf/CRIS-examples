Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts ProphecyStream.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI SchTactics.
From Stdlib Require Import IndefiniteDescription Sorted. (* require for prophecy *)
From iris.algebra Require Import numbers excl auth list gset gmap agree csum.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.
From stdpp Require Import streams list.

(** * Definition of the cameras we need for queues **************************)

Canonical Structure valO : ofe := leibnizO val.

Definition prod4R A B C D E :=
  prodR (prodR (prodR (prodR A B) C) D) E.

Definition oneshotUR := optionUR $ csumR (exclR unitR) (agreeR unitR).
Definition shot     : oneshotUR := Some $ Cinr $ to_agree ().
Definition not_shot : oneshotUR := Some $ Cinl $ Excl ().

Definition per_slot :=
  prod4R
    (* Unique token for the index. *)
    (optionUR $ exclR unitR)
    (* The location stored at our index, which always remains the same. *)
    (optionUR $ agreeR valO)
    (* Possible unique name for the index, only if being helped. *)
    (optionUR $ exclR natO)
    (* One shot witnessing the transition from pending to helped. *)
    oneshotUR
    (* One shot witnessing the physical writing of the value in the slot. *)
    oneshotUR.

(** * Definition of the cameras we need for queues **************************)

Definition eltsUR := authR $ optionUR $ exclR $ listO valO.
Definition contUR := csumR (exclR unitR) (agreeR (prodO natO natO)).
Definition slotUR := authR $ gmapUR nat per_slot.
Definition backUR := authR max_natUR.

Class hwqGpreS `{!crisG Γ Σ α β τ Hsub Hinv} :=
  HwqGpreS {
    hwq_arG   :: inG eltsUR Γ; (** Logical contents of the queue. *)
    hwq_contG :: inG contUR Γ; (** One-shot for contradiction states. *)
    hwq_slotG :: inG slotUR Γ; (** State data for used array slots. *)
    hwq_back  :: inG backUR Γ; (** Used to show that back only increases. *)
    hwq_help  :: helpingGpreS; (** Added : helping resource *)
  }.
Local Existing Instance helpingG.
Definition hwqΓ : HRA := ##[#[eltsUR; contUR; slotUR; backUR]; helpingΓ].
Global Instance subG_hwqG `{!crisG Γ Σ α β τ Hsub Hinv} : subG hwqΓ Γ → hwqGpreS.
Proof. solve_inG. Qed.

Class hwqGS `{!crisG Γ Σ α β τ Hsub Hinv} :=
  HwqGS {
    hwqG :: hwqGpreS;
    helpGS :: helpingGS;
  }.

(** * The specifiaction... **************************************************)

Section herlihy_wing_queue.

Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS, !hwqGS, !prophGS}.
(* Context (N : namespace). *)
Notation iProp := (iProp Σ).
Implicit Types γe γc γs : gname.
Implicit Types sz : nat.
(* Implicit Types ℓ_ar ℓ_back : loc.
Implicit Types p : proph_id. *)
Implicit Types v : val.
Implicit Types pvs : list nat.

(** Operations for the CMRA representing the logical contents of the queue. *)

Lemma new_elts l : ⊢ o=> ∃ γe, own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iMod (own_alloc (● Excl' l ⋅ ◯ Excl' l)) as (γe) "[H● H◯]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γe. iFrame.
Qed.

Lemma sync_elts γe (l1 l2 : list valO) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) -∗ ⌜l1 = l2⌝.
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H".
  iDestruct (own_valid with "H") as "H".
  by iDestruct "H" as %[?%Excl_included%leibniz_equiv _]%auth_both_valid_discrete.
Qed.

Lemma update_elts γe (l1 l2 l : list valO) :
  own γe (● Excl' l1) -∗ own γe (◯ Excl' l2) o==∗
    own γe (● Excl' l) ∗ own γe (◯ Excl' l).
Proof.
  iIntros "H● H◯". iCombine "H●" "H◯" as "H". rewrite -own_op.
  iMod (own_update with "H") as "$"; auto.
  by apply auth_update, option_local_update, exclusive_local_update.
Qed.

(* Fragmental part, made available during atomic updates. *)
Definition hwq_cont γe (elts : list valO) : iProp :=
  own γe (◯ Excl' elts).

Lemma hwq_cont_exclusive γe elts1 elts2 :
  hwq_cont γe elts1 -∗ hwq_cont γe elts2 -∗ False.
Proof.
  iIntros "H1 H2".
  by iCombine "H1 H2" gives %?%auth_frag_op_valid_1.
Qed.

(** Operations for the CMRA used to show that back only increases. *)

Definition back_value γb n := own γb (● MaxNat n).
Definition syn_back_value {n} γb i : GTerm.t n := sown γb (● MaxNat i).

Definition back_lower_bound γb n := own γb (◯ MaxNat n).
Definition syn_back_lower_bound {n} γb i : GTerm.t n := sown γb (◯ MaxNat i).

Lemma new_back : ⊢ o=> ∃ γb, back_value γb 0.
Proof.
  iMod (own_alloc (● MaxNat 0)) as (γb) "H●".
  - by rewrite auth_auth_valid.
  - by iExists γb.
Qed.

Lemma back_incr γb n :
  back_value γb n o==∗ back_value γb (S n).
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat (S n))). simpl. lia.
Qed.

Lemma back_snapshot γb n :
  back_value γb n o==∗ back_value γb n ∗ back_lower_bound γb n.
Proof.
  iIntros "H●". rewrite -own_op. iMod (own_update with "H●") as "$"; auto.
  by apply auth_update_alloc, max_nat_local_update.
Qed.

Lemma back_le γb n1 n2 :
  back_value γb n1 -∗ back_lower_bound γb n2 -∗ ⌜n2 ≤ n1⌝.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. iPureIntro.
  apply auth_both_valid_discrete in Hvalid as [Ha%max_nat_included _]. done.
Qed.

(* Stores a lower bound on the [i2] part of any contradiction that
   has arised or may arise in the future. *)
Definition i2_lower_bound γi n := back_value γi n.
Definition syn_i2_lower_bound {n} γi i := @syn_back_value n γi i.

(* Witness that the [i2] part of any (future or not) contradicton is
   greater than [n]. *)
Definition no_contra_wit γi n := back_lower_bound γi n.

Lemma i2_lower_bound_update γi n m :
  n ≤ m →
  i2_lower_bound γi n ==∗ i2_lower_bound γi m.
Proof.
  iIntros (?) "H●". iMod (own_update with "H●") as "[$ _]"; last done.
  apply auth_update_alloc, (max_nat_local_update _ _ (MaxNat m)). simpl. lia.
Qed.

Lemma i2_lower_bound_snapshot γi n :
  i2_lower_bound γi n ==∗ i2_lower_bound γi n ∗ no_contra_wit γi n.
Proof.
  iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
  by apply auth_update_alloc, max_nat_local_update.
Qed.

(** Operations for the one-shot CMRA used for contradiction states. *)

(** Element for "no contradiction yet". *)
Definition no_contra γc :=
  own γc (Cinl (Excl ())).
Definition syn_no_contra {n} γc : GTerm.t n :=
  sown γc (Cinl (Excl ())).

(** Element witnessing a contradiction [(i1, i2)]. *)
Definition contra γc (i1 i2 : nat) :=
  own γc (Cinr (to_agree (i1, i2))).
Definition syn_contra {n} γc (i1 i2 : nat) : GTerm.t n :=
  sown γc (Cinr (to_agree (i1, i2))).

Lemma new_no_contra : ⊢ o=> ∃ γc, no_contra γc.
Proof. by apply own_alloc. Qed.

Lemma to_contra i1 i2 γc : no_contra γc ==∗ contra γc i1 i2.
Proof. apply bi.entails_wand, own_update. by apply cmra_update_exclusive. Qed.

Lemma contra_not_no_contra i1 i2 γc :
  no_contra γc -∗ contra γc i1 i2 -∗ False.
Proof. iIntros "HnoC HC". iCombine "HnoC HC" gives %[]. Qed.

Lemma contra_agree i1 i2 i1' i2' γc :
  contra γc i1 i2 -∗ contra γc i1' i2' -∗ ⌜i1' = i1 ∧ i2' = i2⌝.
Proof.
  iIntros "HC HC'". iCombine "HC HC'" gives %Hwf.
  iPureIntro. apply to_agree_op_inv_L in Hwf. by inversion Hwf.
Qed.

Global Instance contra_persistent γc i1 i2 : Persistent (contra γc i1 i2).
Proof. apply own_core_persistent. by rewrite /CoreId. Qed.

(** Operations for the state data. *)

Inductive state :=
  (** Help was requested (element not committed). *)
  | Pend : nat → state
  (** Help has been provided (element committed). *)
  | Help : nat → state
  (** The enqueue operation known it has been committed. *)
  | Done :       state.

Local Instance state_inhabited : Inhabited state.
Proof. constructor. refine Done. Qed.

(** Data associated to each slot. The four components are:
     - the location that is being written in the slot,
     - a possible name for a stored proposition containing the postcondition
       of the atomic update of the enqueue happening for the slot (used only
       in case of helping),
     - state of the slot,
     - [true] if a value was physically written in the slot. *)
Definition slot_data : Type := val * state * bool.

Implicit Types slots : gmap nat slot_data.

Definition update_slot i f slots :=
  match slots !! i with
  | Some d => <[i := f d]> (delete i slots)
  | None   => slots
  end.

Definition val_of (data : slot_data) : val :=
  match data with (l, _, _) => l end.

Definition state_of (data : slot_data) : state :=
  match data with (_, s, _) => s end.

Definition name_of (data : slot_data) : option nat :=
  match state_of data with Pend γ => Some γ | Help γ => Some γ | _ => None end.

Definition was_written (data : slot_data) : bool :=
  match data with (_, _, b) => b end.

Definition was_committed (data : slot_data) : bool :=
  match state_of data with Pend _ => false | _ => true end.

Definition set_written (data : slot_data) : slot_data :=
  match data with (l, s, _) => (l, s, true) end.

Definition set_written_and_done (data : slot_data) : slot_data :=
  match data with (l, _, _) => (l, Done, true) end.

Definition to_helped (γ : nat) (data : slot_data) : slot_data :=
  match data with (l, _, w) => (l, Help γ, w) end.

Definition to_done (data : slot_data) : slot_data :=
  match data with (l, _, w) => (l, Done, w) end.

Definition physical_value (data : slot_data) : val :=
  match data with (l, _, w) => if w then l else Vint 0 end.

Lemma val_of_set_written d : val_of (set_written d) = val_of d.
Proof. by destruct d as [[l s] w]. Qed.

Lemma was_written_set_written d : was_written (set_written d) = true.
Proof. by destruct d as [[l s] w]. Qed.

Lemma state_of_set_written d : state_of (set_written d) = state_of d.
Proof. by destruct d as [[l s] w]. Qed.

Definition of_slot_data (data : slot_data) : per_slot :=
  match data with
  | (l, s, w) =>
    let name := match s with Pend γ => Excl' γ | Help γ => Excl' γ | Done => None end in
    let comm := if was_committed data then shot else not_shot in
    let wr := if w then shot else not_shot in
    (Excl' (), Some (to_agree l), name, comm, wr)
  end.

Lemma of_slot_data_valid d : ✓ of_slot_data d.
Proof. by destruct d as [[l []] []]. Qed.

(* The (unique) token for slot [i]. *)
Definition slot_token γs i :=
  own γs (◯ {[i := (Excl' (), None, None, None, None)]} : slotUR).
Definition syn_slot_token {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (Excl' (), None, None, None, None)]} : slotUR).

(* A witness that the location enqueued in slot [i] is [l]. *)
Definition slot_val_wit γs i l :=
  own γs (◯ {[i := (None, Some (to_agree l), None, None, None)]} : slotUR).
Definition syn_slot_val_wit {n} γs i l : GTerm.t n :=
  sown γs (◯ {[i := (None, Some (to_agree l), None, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been committed. *)
Definition slot_committed_wit γs i :=
  own γs (◯ {[i := (None, None, None, shot, None)]} : slotUR).
Definition syn_slot_committed_wit {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, shot, None)]} : slotUR).

Definition slot_name_tok γs i γ :=
  own γs (◯ {[i := (None, None, Excl' γ, None, None)]} : slotUR).
Definition syn_slot_name_tok {n} γs i γ : GTerm.t n :=
  sown γs (◯ {[i := (None, None, Excl' γ, None, None)]} : slotUR).

(* A witness that the element inserted at slot [i] has been written. *)
Definition slot_written_wit γs i :=
  own γs (◯ {[i := (None, None, None, None, shot)]} : slotUR).
Definition syn_slot_written_wit {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, None, shot)]} : slotUR).

(* A token proving that the enqueue in slot [i] has not been commited. *)
Definition slot_pending_tok γs i :=
  own γs (◯ {[i := (None, None, None, not_shot, None)]} : slotUR).
Definition syn_slot_pending_tok {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, not_shot, None)]} : slotUR).

(* A token proving that no value has been written in slot [i]. *)
Definition slot_writing_tok γs i :=
  own γs (◯ {[i := (None, None, None, None, not_shot)]} : slotUR).
Definition syn_slot_writing_tok {n} γs i : GTerm.t n :=
  sown γs (◯ {[i := (None, None, None, None, not_shot)]} : slotUR).

(* Initial slot data, with not allocated slots. *)
Lemma new_slots : ⊢ o=> ∃ γs, own γs (● ∅).
Proof.
  iMod (own_alloc (● ∅ ⋅ ◯ ∅)) as (γs) "[H● _]".
  - by apply auth_both_valid_discrete.
  - iModIntro. iExists γs. iFrame.
Qed.

(* Allocate a new slot with data [d] at the fresh index [i]. *)
Lemma alloc_slot γs slots (i : nat) (d : slot_data) :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) o==∗
    own γs (● (of_slot_data <$> (<[i := d]> slots)) : slotUR) ∗
    own γs (◯ {[i := of_slot_data d]} : slotUR).
Proof.
  iIntros (Hi) "H". rewrite -own_op fmap_insert.
  iMod (own_update with "H") as "$"; auto. apply auth_update_alloc.
  apply alloc_singleton_local_update.
  - by rewrite lookup_fmap Hi.
  - apply of_slot_data_valid.
Qed.

Lemma alloc_done_slot γs slots i l :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) o==∗
    own γs (● (of_slot_data <$> (<[i := (l, Done, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i l ∗
    slot_committed_wit γs i ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma alloc_pend_slot γs slots i l γ :
  slots !! i = None →
  own γs (● (of_slot_data <$> slots) : slotUR) o==∗
    own γs (● (of_slot_data <$> (<[i := (l, Pend γ, false)]> slots)) : slotUR) ∗
    slot_token γs i ∗
    slot_val_wit γs i l ∗
    slot_pending_tok γs i ∗
    slot_name_tok γs i γ ∗
    slot_writing_tok γs i.
Proof.
  iIntros (Hi) "H". iMod (alloc_slot _ _ _ _ Hi with "H") as "[$ Hi]".
  repeat rewrite -own_op. repeat rewrite -auth_frag_op.
  repeat rewrite -insert_op. repeat rewrite left_id.
  by rewrite insert_empty.
Qed.

Lemma use_val_wit γs slots i l :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i l -∗
  ⌜val_of <$> slots !! i = Some l⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Hwf.
  iPureIntro. apply auth_both_valid_discrete in Hwf as [Hwf%singleton_included_l _].
  destruct Hwf as [ps (Ha & H2%option_included)]. rewrite lookup_fmap in Ha.
  destruct (slots !! i) as [d|]; last by inversion Ha. simpl in Ha.
  inversion_clear Ha.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into Ha end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct Ha as [[[[_ Ha] _] _] _]; simpl in Ha. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ H2] _] _] _]; simpl in H2.
    assert (Some (to_agree l) ≡ Some (to_agree dl)) as Hwf by by transitivity b2.
    apply Some_equiv_inj, to_agree_inj in Hwf. rewrite /equiv in Hwf. inv Hwf. done.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    assert (Some (to_agree l) ≼ Some (to_agree dl)) as Hb by set_solver.
    apply option_included in Hb.
    destruct Hb as [Hb|[a [b (H11 & H12 & H13)]]]; first done.
    simplify_eq. destruct H13 as [Hb|Hb].
    + by apply to_agree_inj in Hb.
    + by apply to_agree_included in Hb.
Qed.

Lemma use_name_tok γs slots i γ :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ -∗
  ⌜name_of <$> slots !! i = Some (Some γ)⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Ha.
  iPureIntro. apply auth_both_valid_discrete in Ha as [Ha%singleton_included_l _].
  destruct Ha as [ps (Hb & H2%option_included)]. rewrite lookup_fmap in Hb.
  destruct (slots !! i) as [d|]; last by inversion Hb. simpl in Hb.
  inversion_clear Hb.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with H: of_slot_data d ≡ ps |- _ => rename H into Hb end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct Hb as [[[[_ _] Hb] _] _]; simpl in Hb. simpl. f_equal.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] H2] _] _]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≡ Excl' γ') as Ha by by transitivity b3.
      inversion Ha as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ Excl' γ') as Ha by by transitivity b3.
      inversion Ha as [x y HH|]. by inversion HH.
    + assert (Excl' γ ≡ None) as Ha by by transitivity b3.
      inversion Ha.
  - apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [H2 _]; simpl in H2.
    apply prod_included in H2 as [_ H2]; simpl in H2.
    destruct ds as [γ'|γ'|]; rewrite /name_of /=; try f_equal.
    + assert (Excl' γ ≼ Excl' γ') as Ha by set_solver.
      by apply Excl_included in Ha.
    + assert (Excl' γ ≼ Excl' γ') as Ha by set_solver.
      by apply Excl_included in Ha.
    + assert (Excl' γ ≼ None) as Ha by set_solver.
      exfalso. apply option_included in Ha as [Ha|Ha]; first done.
      destruct Ha as [a [b (H11 & H12 & H13)]]. by simplify_eq.
Qed.

Lemma shot_not_equiv_not_shot : shot ≢ not_shot.
Proof.
  intros Ha. rewrite /shot /not_shot in Ha.
  inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_equiv_not_shot' e : shot ≢ not_shot ⋅ e.
Proof.
  intros Ha. rewrite /shot /not_shot in Ha.
  destruct e as [e|]; first destruct e.
  - rewrite -Some_op -Cinl_op in Ha.
    inversion Ha as [x y Habsurd|]; inversion Habsurd.
  - rewrite -Some_op in Ha. compute in Ha.
    inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
  - inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
  - inversion Ha as [x y HAbsurd|]. inversion HAbsurd.
Qed.

Lemma shot_not_included_not_shot : ¬ shot ≼ not_shot.
Proof.
  intros Ha. rewrite /shot /not_shot in Ha.
  apply option_included in Ha. destruct Ha as [Ha|Ha]; first done.
  destruct Ha as [a [b (Ha & H2 & [H3|H3])]].
  - simplify_eq. by inversion H3.
  - simplify_eq. apply csum_included in H3.
    destruct H3 as [H3|H3]; first done. destruct H3 as [H3|H3].
    + destruct H3 as [a [b (Ha & H2 & H3)]]. by inversion Ha.
    + destruct H3 as [a [b (Ha & H2 & H3)]]. by inversion H1.
Qed.

Lemma use_committed_wit γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_committed_wit γs i -∗
  ⌜was_committed <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Hwf.
  iPureIntro. apply auth_both_valid_discrete in Hwf as [Hwf%singleton_included_l _].
  destruct Hwf as [ps (Ha & H2%option_included)]. rewrite lookup_fmap in Ha.
  destruct (slots !! i) as [d|]; last by inversion Ha. simpl in Ha.
  inversion_clear Ha.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with Hwf: of_slot_data d ≡ ps |- _ => rename Hwf into Ha end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5].
  destruct d as [[dl ds] dw].
  destruct Ha as [[[[_ _] _] Ha]]; simpl in Ha. f_equal.
  destruct (was_committed (dl, ds, dw)); first done. exfalso.
  destruct H23 as [H3|H3].
  - destruct H3 as [[[[_ _] _] H3] _]; simpl in H3.
    apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H3 as [H3 _]; simpl in H3.
    apply prod_included in H3 as [_ H3]; simpl in H3.
    apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_written_wit γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_written_wit γs i -∗
  ⌜was_written <$> slots !! i = Some true⌝.
Proof.
  iIntros "H● Hwit". iCombine "H● Hwit" gives %Hwf.
  iPureIntro. apply auth_both_valid_discrete in Hwf as [Hwf%singleton_included_l _].
  destruct Hwf as [ps (Ha & H2%option_included)]. rewrite lookup_fmap in Ha.
  destruct (slots !! i) as [d|]; last by inversion Ha. simpl in Ha.
  inversion_clear Ha.
  (* Ltac is a steaming pile of ***, so we cannot use [rename select] here.
     It infers the type of the [≡] too early and then fails to match the term. *)
  match goal with Hwf: of_slot_data d ≡ ps |- _ => rename Hwf into Ha end.
  destruct H2 as [H2|[a [b (H21 & H22 & H23)]]]; first done. simplify_eq.
  simpl. destruct b as [[[[b1 b2] b3] b4] b5]. destruct d as [[dl ds] dw].
  destruct Ha as [[[[_ _] _] _] Ha]; simpl in Ha. f_equal.
  destruct dw; first done. exfalso.
  destruct H23 as [H2|H2].
  - destruct H2 as [[[[_ _] _] _] H2]; simpl in H2.
    exfalso. apply shot_not_equiv_not_shot. set_solver.
  - apply prod_included in H2 as [_ H2]; simpl in H2.
    exfalso. apply shot_not_included_not_shot. set_solver.
Qed.

Lemma use_writing_tok γs i slots :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i set_written slots) : slotUR) ∗
    slot_written_wit γs i.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H". rewrite -own_op.
  iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [Ha H2].
  apply singleton_included_l in Ha as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|] eqn:Hi; last by inversion H1_1.
  apply Some_equiv_inj in H1_1.
  assert (w = false) as ->.
  { destruct w; [ exfalso | done ].
    apply Some_included in H1_2 as [H1_2|H1_2].
    - assert ((None, None, None, None, not_shot)
            ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by apply shot_not_equiv_not_shot.
    - destruct H1_2 as [f H1_2].
      assert ((None, None, None, None, not_shot) ⋅ f
            ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
      destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
      by eapply shot_not_equiv_not_shot'. }
  rewrite /update_slot Hi insert_delete_insert fmap_insert.
  apply auth_update. eapply (singleton_local_update _ i).
  { by rewrite lookup_fmap Hi. }
  rewrite /set_written. apply prod_local_update; first done. simpl.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma writing_tok_not_written γs slots i :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_writing_tok γs i -∗
    ⌜was_written <$> slots !! i = Some false⌝.
Proof.
  iIntros "Hs● Htok". iCombine "Hs● Htok" as "H".
  iDestruct (own_valid with "H") as %Hvalid%auth_both_valid_discrete.
  iPureIntro. destruct Hvalid as [Ha H2].
  apply singleton_included_l in Ha as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|]; last by inversion H1_1.
  apply Some_equiv_inj in H1_1. simpl. f_equal. destruct w; last done.
  exfalso. apply Some_included in H1_2 as [H1_2|H1_2].
  - assert ((None, None, None, None, not_shot)
          ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by apply shot_not_equiv_not_shot.
  - destruct H1_2 as [f H1_2].
    assert ((None, None, None, None, not_shot) ⋅ f
          ≡ of_slot_data (l, s, true)) as Hequiv by by transitivity e.
    destruct Hequiv as [[[[_ _] _] _] Hequiv]; simpl in Hequiv.
    by eapply shot_not_equiv_not_shot'.
Qed.

Lemma None_op {A : cmra} : (None : optionUR A) ⋅ None = None.
Proof. done. Qed.

Lemma use_pending_tok γs i γ slots :
  state_of <$> slots !! i = Some (Pend γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_pending_tok γs i ==∗
    own γs (● (of_slot_data <$> update_slot i (to_helped γ) slots) : slotUR) ∗
    slot_committed_wit γs i.
Proof.
  iIntros (Hlookup) "Hs● Htok". iCombine "Hs● Htok" as "H".
  rewrite -own_op. iDestruct (own_valid with "H") as %Hvalid.
  iApply (own_update with "H").
  apply auth_both_valid_discrete in Hvalid as [Ha H2].
  apply singleton_included_l in Ha as [e (H1_1 & H1_2)].
  rewrite lookup_fmap in H1_1.
  destruct (slots !! i) as [[[l s] w]|] eqn:Hi; last by inversion H1_1.
  simpl in Hlookup. inversion Hlookup; subst s.
  rewrite /update_slot Hi insert_delete_insert fmap_insert.
  apply auth_update. repeat rewrite pair_op.
  eapply (singleton_local_update _ i). { by rewrite lookup_fmap Hi. }
  rewrite /to_helped. repeat rewrite None_op.
  repeat apply prod_local_update; try done.
  by apply option_local_update, exclusive_local_update.
Qed.

Lemma slot_token_exclusive γs i :
  slot_token γs i -∗ slot_token γs i -∗ False.
Proof.
  iIntros "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Ha. iPureIntro.
  move:Ha =>/auth_frag_valid Ha. apply singleton_valid in Ha.
  by repeat apply pair_valid in Ha as [Ha _]; simpl in Ha.
Qed.

Lemma helped_to_done_aux γs i γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR) ∗
    own γs (◯ {[i := (None, None, None, None, None)]} : slotUR).
Proof.
  iIntros (Ha) "H1 H2". iCombine "H1 H2" as "H".
  iDestruct (own_valid with "H") as %Hvalid. rewrite -own_op.
  iApply (own_update with "H"). apply auth_update. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:Hd; last by inversion Ha.
  rewrite insert_delete_insert fmap_insert. eapply singleton_local_update.
  { by rewrite lookup_fmap Hd /=. }
  destruct d as [[dl ds] dw]. inversion Ha; subst ds; simpl.
  repeat apply prod_local_update; try done. simpl.
  apply delete_option_local_update. apply _.
Qed.

Lemma helped_to_done γs i γ slots :
  state_of <$> slots !! i = Some (Help γ) →
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_name_tok γs i γ ==∗
    own γs (● (of_slot_data <$> update_slot i to_done slots) : slotUR).
Proof.
  iIntros (?) "H1 H2". by iMod (helped_to_done_aux with "H1 H2") as "[H _]".
Qed.

Lemma val_wit_from_auth γs i l slots :
  val_of <$> slots !! i = Some l →
  own γs (● (of_slot_data <$> slots) : slotUR) ==∗
    own γs (● (of_slot_data <$> slots) : slotUR) ∗
    slot_val_wit γs i l.
Proof.
  iIntros (Ha) "H". rewrite -own_op. iApply (own_update with "H").
  apply auth_update_dfrac_alloc; first apply _.
  assert (∃ d, slots !! i = Some d) as [d Hlookup].
  { destruct (slots !! i) as [d|]; inversion Ha. by exists d. }
  apply singleton_included_l. rewrite lookup_fmap. rewrite Hlookup /=.
  exists (of_slot_data d). split; first done.
  apply Some_included. right. destruct d as [[dl ds] dw]. simpl.
  repeat (apply prod_included; split; simpl);
    try by (apply option_included; left).
  apply option_included; right. exists (to_agree l), (to_agree dl).
  repeat (split; first done). left.
  rewrite Hlookup /= in Ha. by inversion Ha.
Qed.

(** * Prophecy abstractions *************************************************)
Definition hwq_prophecy : Prophecy.t := stream_prophecy (nat * bool).

Fixpoint proph_data fuel sz (deq : gset nat) (str : stream (nat * bool)) : list nat :=
  match fuel with
  | O => []
  | S fuel =>
    match shead str with
    | (i, true) =>
      if (decide (i ∉ deq ∧ 0 ≤ i < sz))
      then i :: proph_data fuel sz ({[i]} ∪ deq) (stail str)
      else proph_data fuel sz deq (stail str)
    | (i, false) =>
      proph_data fuel sz deq (stail str)
    end
  end.

Definition enough_fuel sz (deq : gset nat) (str : stream (nat * bool)) fuel : Prop :=
  ∀ (x i : nat),
    0 ≤ i < sz →
    i ∉ deq →
    str !.! x = (i, true) →
    i ∈ proph_data fuel sz deq str.

Definition init (str : stream (nat * bool)) (i : nat) :
  { x : option nat |
    match x with
    | Some x => str !.! x = (i, true) ∧ ∀ (x' : nat), str !.! x' = (i, true) → x ≤ x'
    | None => ∀ x, str !.! x ≠ (i, true)
    end
  }.
Proof.
  apply constructive_indefinite_description.
  set (P := λ (n : nat), str !.! n = (i, true)).
  pose proof (dec_inh_nat_subset_has_unique_least_element P) as HP.
  destruct (classic (∃ x, P x)) as [[x Hx]|Hex].
  { hexploit HP; [intros ?; eapply classic|eauto|].
    intros [y [[Hy Hu] ?]]; exists (Some y); split; eauto.
  }
  exists None; intros ??; eauto.
Qed.

Lemma enough_fuel_exists sz deq str : ∃ fuel, enough_fuel sz deq str fuel.
Proof.
  set (fl := S (max_list (omap id ((λ x, proj1_sig (init str x)) <$> (seq 0 sz))))).
  exists fl; intros x i Hisz Hideq Hstrxi.
  destruct (init str i) as [[x2|] Hx2] eqn : Hinit; last by (exfalso; apply (Hx2 x)).
  destruct Hx2 as [Hx2 Hx2max].
  assert (x2 < fl) as Hx2fl.
  { subst fl. apply PeanoNat.le_lt_n_Sm.
    apply max_list_elem_of_le, elem_of_list_omap.
    exists (Some x2); split; last ss.
    rewrite elem_of_list_fmap; exists i; split.
    { rewrite Hinit //=. }
    apply elem_of_seq; lia.
  }
  clear dependent x. clearbody fl. clear Hinit.
  generalize dependent x2; generalize dependent deq. revert str.
  induction fl as [|fl]; intros str deq Hideq x Hxlookup Hxmin Hxfl; first lia; s.
  revert Hxlookup; destruct x as [|x]; s; destruct (shead str) as [i1 [|]]; i; clarify.
  { rewrite decide_True // elem_of_cons; left; ss. }
  { destruct (decide (i = i1)) as [->|Hii1].
    { rewrite decide_True // elem_of_cons; by left. }
    case_decide.
    { rewrite elem_of_cons; right.
      eapply (IHfl (stail str) ({[i1]} ∪ deq)); eauto; first set_solver; try lia.
      intros x2 Hx2; specialize (Hxmin (S x2) Hx2); lia.
    }
    eapply (IHfl (stail str) (deq)); eauto; try lia.
    intros x2 Hx2; specialize (Hxmin (S x2) Hx2); lia.
  }
  eapply (IHfl (stail str) (deq)); eauto; try lia.
  intros x2 Hx2; specialize (Hxmin (S x2) Hx2); lia.
Qed.


Lemma proph_data_deq fuel str sz deq :
  ∀ i, i ∈ deq → i ∉ proph_data fuel sz deq str.
Proof.
  revert deq str.
  induction fuel as [|n IHn]; intros deq str i Hideq; first set_solver.
  simpl; destruct (shead str) as [e [|]]; try by (apply IHn; set_solver).
  case_decide; try by (apply IHn; set_solver).
  rewrite not_elem_of_cons; split; first by (intros ->; set_solver).
  apply IHn; set_solver.
Qed.

Lemma proph_data_sz fuel str sz deq : ∀ i, i ∈ proph_data fuel sz deq str → i < sz.
Proof.
  revert deq str; induction fuel as [|n IHn]; intros deq str i Hi; first by set_solver.
  simpl in Hi; destruct (shead str) as [i1 [|]]; eauto.
  case_decide as Hi1; eauto.
  rewrite elem_of_cons in Hi; destruct Hi as [->|Hi]; first lia; eauto.
Qed.

Lemma proph_data_NoDup fuel sz deq str :
  NoDup (proph_data fuel sz deq str ++ elements deq).
Proof.
  apply NoDup_app; split.
  { revert deq str; induction fuel as [|n IHn]; intros deq str; first econs.
    s; destruct shead as [i2 [|]]; try case_decide; eauto.
    rewrite NoDup_cons; split; eauto.
    intros ?%proph_data_deq; ss; set_solver.
  }
  split; last apply NoDup_elements.
  intros ? ? ?%elem_of_elements; eapply proph_data_deq; eauto.
Qed.

(* Wrapper for the Iris [proph] proposition, using our data abstraction. *)
Definition hwq_proph (blk : nat) sz (deq : gset nat) pvs :=
  (∃ str, stream_proph ("hwq", (Vptr (blk, 0%Z))↑↑) str ∗
  ∃ fuel, ⌜enough_fuel sz deq str fuel ∧ pvs = proph_data fuel sz deq str⌝)%I.
Definition syn_hwq_proph {n} (blk : nat) sz (deq : gset nat) pvs : GTerm.t n :=
  (∃ (str : τ{stream (nat * bool)}),
    syn_stream_proph ("hwq", (Vptr (blk, 0%Z))↑↑) str ∗
    ∃ (fuel : τ{nat}), ⌜enough_fuel sz deq str fuel ∧ pvs = proph_data fuel sz deq str⌝)%SAT.

Definition block  : Type := nat * list nat.
Definition blocks : Type := list block.

(* A block is valid if it follows the structure described above. *)
Definition block_valid slots (b : block) :=
  slots !! b.1 = None ∧
  ∀ i, i ∈ b.2 → was_committed <$> (slots !! i) = Some false.

Fixpoint glue_blocks (b : block) (i : nat) (bs : blocks) : blocks :=
  match bs with
  | []               => [b]
  | (j, pends) :: bs => if decide (i = j) then (b.1, b.2 ++ i :: pends) :: bs
                        else b :: glue_blocks (j, pends) i bs
  end.

Fixpoint flatten_blocks bs : list nat :=
  match bs with
  | []               => []
  | (i, pends) :: bs => i :: pends ++ flatten_blocks bs
  end.

Lemma blocks_elem1 b blocks :
  b ∈ blocks → b.1 ∈ flatten_blocks blocks.
Proof.
  intros Ha. induction blocks as [|b' blocks IH]; first by inversion Ha.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. by apply elem_of_list_here.
  - destruct b' as [b'_u b'_bs]. simpl.
    apply elem_of_list_further. apply elem_of_app; right.
    apply IH. apply elem_of_cons in Ha as [Ha|Ha]; last done.
    by rewrite Ha in Hb_not_b'.
Qed.

Lemma blocks_elem2 b blocks :
  b ∈ blocks → ∀ i, i ∈ b.2 → i ∈ flatten_blocks blocks.
Proof.
  intros Ha. induction blocks as [|b' blocks IH]; first by inversion Ha.
  destruct (decide (b' = b)) as [->|Hb_not_b'].
  - destruct b as [b_u b_ps]. intros i Hi. simpl in *.
    apply elem_of_list_further. apply elem_of_app. by left.
  - destruct b' as [b'_u b'_bs]. simpl. intros i Hi.
    apply elem_of_list_further. apply elem_of_app; right.
    apply IH; last done. apply elem_of_cons in Ha as [Ha|Ha]; last done.
    by rewrite Ha in Hb_not_b'.
Qed.

Lemma glue_blocks_valid slots i b_unused b_pendings blocks l γ :
  slots !! i = None →
  b_unused ≠ i →
  NoDup (b_unused :: b_pendings ++ flatten_blocks blocks) →
  (∀ b : block, b ∈ (b_unused, b_pendings) :: blocks → block_valid slots b) →
  ∀ b, b ∈ glue_blocks (b_unused, b_pendings) i blocks → block_valid (<[i:=(l, Pend γ, false)]> slots) b.
Proof using Type*.
  intros Hi. revert b_unused b_pendings.
  induction blocks as [|[b_u b_ps] blocks IH];
    intros b_unused b_pendings Hb_unused_not_i HND Hblocks_valid [b_u' b_ps'] Hb.
  - apply Hblocks_valid in Hb as Hvalid.
    apply elem_of_list_singleton in Hb. simplify_eq.
    destruct Hvalid as (Hvalid1 & Hvalid2). split.
    + by rewrite lookup_insert_ne.
    + simpl in *. intros k Hk. specialize (Hvalid2 _ Hk) as Hvalid_k.
      destruct (decide (k = i)) as [->|Hk_not_i].
      * by rewrite lookup_insert.
      * by rewrite lookup_insert_ne.
  - simpl in Hb. destruct (decide (i = b_u)) as [->|Hi_not_b_u].
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2).
        assert ((b_u, b_ps) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid'%Hblocks_valid by set_solver.
        destruct Hvalid' as (Hvalid1' & Hvalid2').
        split; simpl.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. apply elem_of_app in Hk as [Hk|Hk].
           *** assert (k ≠ b_u) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & HND & _). apply HND in Hk.
                 simpl in Hk. by apply not_elem_of_cons in Hk as (Hk & _). }
               rewrite lookup_insert_ne; last done. by apply Hvalid2.
           *** apply elem_of_cons in Hk as [->|Hk]; first by rewrite lookup_insert.
               assert (b_u ≠ k) as HNEq2.
               { apply NoDup_cons in HND as (_ & HND).
                 apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
                 apply NoDup_cons in HND as (HND & _).
                 apply not_elem_of_app in HND as (HND & _).
                 intros ->. apply HND, Hk. }
               rewrite lookup_insert_ne; last done. by apply Hvalid2'.
      * assert ((b_u', b_ps') ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). rewrite /block_valid.
        assert (b_u ≠ b_u') as HNeq1.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by apply blocks_elem1 in Hb. }
        rewrite lookup_insert_ne; last done. split; first done.
        intros k Hk. simpl in Hk.
        assert (b_u ≠ k) as HNeq2.
        { apply NoDup_cons in HND as (_ & HND).
          apply NoDup_app in HND as (_ & _ & HND). simpl in HND.
          apply NoDup_cons in HND as (HND & _). intros <-.
          apply not_elem_of_app in HND as (_ & HND). apply HND.
          by eapply blocks_elem2 in Hb. }
        rewrite lookup_insert_ne; last done. by apply Hvalid2.
    + apply elem_of_cons in Hb as [Hb|Hb].
      * simplify_eq.
        assert ((b_unused, b_pendings) ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hvalid%Hblocks_valid by set_solver.
        destruct Hvalid as (Hvalid1 & Hvalid2). split.
        ** by rewrite lookup_insert_ne.
        ** intros k Hk. simpl in *.
           assert (k ≠ i) as HNEq.
           { intros ->. apply Hvalid2 in Hk. rewrite Hi in Hk. by inversion Hk. }
           rewrite lookup_insert_ne; last done. by apply Hvalid2.
      * eapply IH; last done; first done.
        { apply NoDup_cons in HND as (_ & HND).
          by apply NoDup_app in HND as (_ & _ & HND). }
        intros b' Hb'.
        assert (b' ∈ (b_unused, b_pendings) :: (b_u, b_ps) :: blocks)
          as Hb'_valid%Hblocks_valid by set_solver. done.
Qed.

(* Contradiction status: either there is a contradiction going on with
   the given indices, or there is no contradiction. In the latter case
   the prophecy has well-formed pending blocks as a suffix. *)
Inductive cont_status :=
  | WithCont : nat → nat → cont_status
  | NoCont   : blocks    → cont_status.

Local Instance cont_status_inhabited : Inhabited cont_status.
Proof. constructor. refine (NoCont []). Qed.

Lemma initial_block_valid b pvs :
  b ∈ map (λ i : nat, (i, [])) pvs → block_valid ∅ b.
Proof.
  intros Ha. induction pvs as [|i pvs IH].
  - by inversion Ha.
  - simpl in Ha. apply elem_of_cons in Ha as [->|Ha].
    + split; first by apply lookup_empty. intros k Hk. by inversion Hk.
    + apply IH, Ha.
Qed.

Lemma flatten_blocks_initial pvs :
  pvs = flatten_blocks (map (λ i : nat, (i, [])) pvs).
Proof.
  induction pvs as [|i pvs IH]; first done.
  simpl. f_equal. by apply IH.
Qed.

Lemma flatten_blocks_glue b bs i :
  flatten_blocks (b :: bs) = flatten_blocks (glue_blocks b i bs).
Proof.
  revert b.
  induction bs as [|[b_u' b_ps'] bs IH]; intros [b_u b_ps]; first done.
  simpl. destruct (decide (i = b_u')) as [->|HNEq]; simpl.
  - by rewrite -app_assoc.
  - by rewrite -IH.
Qed.

Lemma flatten_blocks_mem1 blocks :
  ∀b, b ∈ blocks → b.1 ∈ flatten_blocks blocks.
Proof.
  intros b Hb. induction blocks as [|[i ps] bs IH]; first by inversion Hb.
  apply elem_of_cons in Hb as [->|Hb]; first by apply elem_of_list_here.
  simpl. apply elem_of_list_further. apply elem_of_app. right. by apply IH.
Qed.

Lemma flatten_blocks_mem2 blocks :
  ∀b, b ∈ blocks → ∀i, i ∈ b.2 → i ∈ flatten_blocks blocks.
Proof.
  intros b Hb. induction blocks as [|[i ps] bs IH]; first by inversion Hb.
  intros k Hk. apply elem_of_cons in Hb as [->|Hb]; simpl.
  - apply elem_of_list_further. apply elem_of_app. by left.
  - apply elem_of_list_further. apply elem_of_app. right. by apply IH.
Qed.

(** * Some definitions and lemmas about array content manipulation **********)

Definition array_get slots (deqs : gset nat) i :=
  match slots !! i with
  | None   => Vint 0
  | Some d => if decide (i ∈ deqs) then Vint 0
              else physical_value d
  end.

Fixpoint array_content n slots deqs :=
  match n with
  | 0 => []
  | S n   => array_content n slots deqs ++ [array_get slots deqs n]
  end.

Lemma length_array_content sz slots deqs :
  length (array_content sz slots deqs) = sz.
Proof.
  induction sz as [|sz IH]; first done.
  by rewrite /= length_app Nat.add_comm /= IH.
Qed.

Lemma array_content_lookup sz slots deqs i :
  i < sz →
  array_content sz slots deqs !! i = Some (array_get slots deqs i).
Proof.
  intros ?. induction sz as [|sz IH]; first lia.
  destruct (decide (i = sz)) as [->|Hi_not_sz]; simpl.
  - rewrite lookup_app_r length_array_content; last done.
    by rewrite Nat.sub_diag /=.
  - rewrite lookup_app_l; first (apply IH; by lia).
    rewrite length_array_content. lia.
Qed.

Lemma array_content_empty sz :
  array_content sz ∅ ∅ = replicate sz (Vint 0).
Proof.
  induction sz as [|sz IH]; first done.
  rewrite replicate_S_end /= IH. done.
Qed.

Lemma array_content_NONEV sz i d slots deqs :
  physical_value d = Vint 0 → slots !! i = None → i ∉ deqs →
  array_content sz (<[i:=d]> slots) deqs = array_content sz slots deqs.
Proof.
  intros Ha H2 H3. induction sz as [|sz IH]; first done.
  rewrite /= /array_get. destruct (decide (i = sz)) as [->|Hi_not_sz].
  - rewrite lookup_insert H2 decide_False; last done. by rewrite IH Ha.
  - rewrite lookup_insert_ne; last done. by rewrite IH.
Qed.

Lemma array_content_is_Some sz i slots deqs :
  i < sz →
  is_Some (array_content sz slots deqs !! i).
Proof.
  intros ?. apply lookup_lt_is_Some. by rewrite length_array_content.
Qed.

Lemma array_content_ext sz slots1 slots2 deqs :
  (∀ i, i < sz → array_get slots1 deqs i = array_get slots2 deqs i) →
  array_content sz slots1 deqs = array_content sz slots2 deqs.
Proof.
  induction sz as [|sz IH]; intros Ha; first done.
  simpl. rewrite Ha; last by lia. f_equal. apply IH.
  intros i Hi. apply Ha. by lia.
Qed.

Lemma array_content_more_deqs sz slots deqs i :
  sz ≤ i →
  array_content sz slots ({[i]} ∪ deqs) = array_content sz slots deqs.
Proof.
  intros ?. induction sz as [|sz IH]; first done.
  rewrite /= IH; last by lia. f_equal.
  rewrite /array_get. destruct (slots !! sz) as [d|]; last done.
  destruct (decide (sz ∈ deqs)) as [Helem|Hnot_elem].
  - rewrite decide_True; [ done | by set_solver ].
  - rewrite decide_False; [ done | .. ].
    apply not_elem_of_union. split; last done.
    apply not_elem_of_singleton. by lia.
Qed.

Lemma array_content_update_slot_ge sz slots deqs f i :
  sz ≤ i →
  array_content sz slots deqs = array_content sz (update_slot i f slots) deqs.
Proof.
  intros ?. induction sz as [|sz IH]; first done.
  rewrite /= IH; last by lia. f_equal.
  rewrite /array_get /update_slot.
  destruct (slots !! i) as [d|]; last done.
  rewrite insert_delete_insert. rewrite lookup_insert_ne; [ done | by lia ].
Qed.

Lemma array_content_dequeue sz i slots deqs :
  i < sz →
  i ∉ deqs →
  array_content sz slots ({[i]} ∪ deqs) = <[i:=(Vint 0)]> (array_content sz slots deqs).
Proof using Type*.
  revert i. induction sz as [|sz IH]; intros i ? H2; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0 (Vint 0)).
    rewrite /= /array_get. destruct (slots !! i) as [d|].
    + rewrite decide_True; last by set_solver. f_equal.
      rewrite array_content_more_deqs; [ done | by lia ].
    + f_equal. rewrite array_content_more_deqs; [ done | by lia ].
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done ]. f_equal.
    rewrite /array_get. destruct (slots !! sz) as [d|]; last done.
    destruct (decide (sz ∈ deqs)) as [?|?].
    * rewrite decide_True; [ done | by set_solver ].
    * rewrite decide_False; [ done | by set_solver ].
Qed.

Lemma array_content_set_written sz i (l : val) slots deqs :
  i < sz →
  val_of <$> slots !! i = Some l →
  ¬ i ∈ deqs →
  <[i:=l]> (array_content sz slots deqs) = array_content sz (update_slot i set_written slots) deqs.
Proof using Type*.
  revert i. induction sz as [|sz IH]; intros i ? H2 H3; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0).
    erewrite array_content_update_slot_ge; [ f_equal | by lia ].
    rewrite /= /array_get /update_slot. destruct (slots !! i) as [d|].
    + rewrite lookup_insert decide_False; last done.
      destruct d as [[ld sd] wd]. inversion H2; subst ld. done.
    + inversion H2.
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done | done ]. f_equal.
    rewrite /array_get /update_slot. destruct (slots !! i) as [d|]; last done.
    by rewrite insert_delete_insert lookup_insert_ne.
Qed.

(* FIXME similar to previous lemma. Share stuff? *)
Lemma array_content_set_written_and_done sz i (l : val) slots deqs :
  i < sz →
  val_of <$> slots !! i = Some l →
  ¬ i ∈ deqs →
  <[i:=l]> (array_content sz slots deqs) = array_content sz (update_slot i set_written_and_done slots) deqs.
Proof.
  revert i. induction sz as [|sz IH]; intros i ? H2 H3; first done.
  destruct (decide (sz = i)) as [->|Hsz_not_i]; simpl.
  - assert (i = length (array_content i slots deqs) + 0) as HEq.
    { rewrite length_array_content. by lia. }
    rewrite [X in <[X:=_]> _]HEq.
    rewrite (insert_app_r (array_content i slots deqs) _ 0).
    erewrite array_content_update_slot_ge; [ f_equal | by lia ].
    rewrite /= /array_get /update_slot. destruct (slots !! i) as [d|].
    + rewrite lookup_insert decide_False; last done.
      destruct d as [[ld sd] wd]. inversion H2; subst ld. done.
    + inversion H2.
  - rewrite insert_app_l; last (rewrite length_array_content; by lia).
    rewrite IH; [ .. | by lia | done | done ]. f_equal.
    rewrite /array_get /update_slot. destruct (slots !! i) as [d|]; last done.
    by rewrite insert_delete_insert lookup_insert_ne.
Qed.

Lemma update_slot_lookup i f slots :
  update_slot i f slots !! i = f <$> slots !! i.
Proof.
  rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq; last done.
  by rewrite lookup_insert.
Qed.

Lemma update_slot_lookup_ne i k f slots :
  i ≠ k →
  update_slot i f slots !! k = slots !! k.
Proof.
  intros ?. rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq; last done.
  rewrite lookup_insert_ne; last done.
  by rewrite lookup_delete_ne.
Qed.

Lemma update_slot_update_slot i f g slots :
  update_slot i f (update_slot i g slots) = update_slot i (f ∘ g) slots.
Proof.
  rewrite /update_slot.
  destruct (slots !! i) as [d|] eqn:HEq.
  - rewrite lookup_insert. repeat rewrite insert_delete_insert.
    rewrite insert_insert. done.
  - rewrite HEq. done.
Qed.

Definition get_value slots (deqs : gset nat) i : val :=
  match slots !! i with
  | None   => inhabitant
  | Some d => val_of d
  end.

Definition map_get_value_not_in_pref i d pref slots deqs :
  was_written d = false →
  i ∉ pref →
  map (get_value (<[i:=d]> slots) deqs) pref = map (get_value slots deqs) pref.
Proof.
  intros Hd. induction pref as [|k pref IH]; intros Hi; first done.
  rewrite /= IH; last by set_solver. f_equal. rewrite /get_value.
  rewrite lookup_insert_ne; first done. set_solver.
Qed.

(** * Definition of the main ************************************************)

(*
When a contradiction is going on, we have [cont = WithCont i1 i2] where:
 - [i1] is the index reserved by the enqueue operation the initiated the
   contradiction,
 - [i2] is the first index in the prophecy that was not yet reserved for
   an enqueue operation (when the contradiction was initiated).
*)

Definition per_slot_own γe γs i d :=
  (match val_of d with
  | Vptr (blk, ofs) => ∃ q v, (blk, ofs) ↦{q} v
  | _ => emp
  end ∗
  slot_val_wit γs i (val_of d) ∗
  (if was_written d then slot_written_wit γs i else emp) ∗
  match state_of d with
  | Pend γ => ∃ N, slot_pending_tok γs i ∗ HelpPend γ (Some N) (val_of d, γe)↑↑
  | Help γ => slot_committed_wit γs i ∗ HelpDone γ Vundef↑↑
  | Done   => slot_committed_wit γs i ∗ slot_token γs i
  end)%I.
Definition syn_per_slot_own {n} γe γs i d : GTerm.t n :=
  (match val_of d with
  | Vptr (blk, ofs) => ∃ (q : τ{Qp}) (v : τ{val}), (blk, ofs) ↦{q} v
  | _ => emp
  end ∗
  syn_slot_val_wit γs i (val_of d) ∗
  (if was_written d then syn_slot_written_wit γs i else emp) ∗
  match state_of d with
  | Pend γ => ∃ (N : τ{namespace}), syn_slot_pending_tok γs i ∗ syn_HelpPend _ γ (Some N) (val_of d, γe)↑↑
  | Help γ => syn_slot_committed_wit γs i ∗ syn_HelpDone _ γ Vundef↑↑
  | Done   => syn_slot_committed_wit γs i ∗ syn_slot_token γs i
  end)%SAT.
Instance per_slot_own_red {n} γe γs i d :
  SLRed n (syn_per_slot_own γe γs i d) (per_slot_own γe γs i d).
Proof. solve_sl_red. Qed.

Definition syn_inv_hwq
    {n} (sz : nat) (γb γi γe γc γs : gname) blk : GTerm.t n :=
  (∃ (back  : τ{nat})                (** Physical value of [q.back]. *)
     (pvs   : τ{list nat})           (** Full contents of the prophecy. *)
     (pref  : τ{list nat})           (** Commit prefix of the prophecy *)
     (rest  : τ{list val})           (** Logical queue after commit prefix. *)
     (cont  : τ{cont_status})        (** Contradiction or prophecy suffix. *)
     (slots : τ{gmap nat slot_data}) (** Per-slot data for used indices. *)
     (deqs  : τ{gset nat}),          (** Dequeued indices. *)
  (** Physical data. *)
  (blk, 0%Z) ↦{1/2} Vint sz ∗ (blk, 1%Z) ↦ Vint back ∗
  ([∗ list] i ↦ v ∈ array_content sz slots deqs, (blk, i + 2)%Z ↦ v) ∗
  (** Logical contents of the queue and prophecy contents. *)
  syn_back_value γb back ∗
  syn_i2_lower_bound γi (match cont with WithCont _ i2 => i2 | NoCont _ => back `min` sz end) ∗
  sown γe (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
  sown γs (● (of_slot_data <$> slots : gmap nat per_slot)) ∗
  syn_hwq_proph blk sz deqs pvs ∗
  (** Per-slot ownership. *)
  ([∗ map] i ↦ d ∈ slots, syn_per_slot_own γe γs i d) ∗
  (** Contradiction status. *)
  match cont with NoCont _ => syn_no_contra γc | WithCont i1 i2 => syn_contra γc i1 i2 end ∗
  (** Tying the logical and physical data and some other pure stuff. *)
  ⌜(∀ i, (i < back `min` sz) ↔ is_Some (slots !! i)) ∧
   (∀ i, (was_committed <$> slots !! i = Some false → was_written <$> slots !! i = Some false) ∧
         (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
   (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ i ∉ deqs ∧
                    match cont with WithCont i1 _ => i ≠ i1 | _ => True end) ∧
   (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                    was_committed <$> slots !! i = Some true ∧
                    array_get slots deqs i = Vint 0) ∧
   (NoDup (pvs ++ elements deqs) ∧ ∀ i, i ∈ pvs → i < sz) ∧
   match cont with
   | NoCont bs      =>
     (∀ b, b ∈ bs → block_valid slots b) ∧
     (bs ≠ [] → rest = []) ∧
     pvs = pref ++ flatten_blocks bs
   | WithCont i1 i2 =>
     (i1 < i2 < sz ∧ i1 < back) ∧
     was_committed <$> slots !! i1 = Some true ∧
     was_written <$> slots !! i1 = Some true ∧ ¬ i1 ∈ deqs ∧
     array_get slots deqs i1 ≠ Vint 0 ∧
     pref ++ [i2] `prefix_of` pvs
  end ∧
  (∀ i v, val_of <$> slots !! i = Some v → v = Vint 0 ∨ ∃ blk ofs, v = Vptr (blk, ofs))⌝)%SAT.

Definition inv_hwq
    (sz : nat) (γb γi γe γc γs : gname) blk : iProp :=
  (∃ (back  : nat)                (** Physical value of [q.back]. *)
     (pvs   : list nat)           (** Full contents of the prophecy. *)
     (pref  : list nat)           (** Commit prefix of the prophecy *)
     (rest  : list val)           (** Logical queue after commit prefix. *)
     (cont  : cont_status)        (** Contradiction or prophecy suffix. *)
     (slots : gmap nat slot_data) (** Per-slot data for used indices. *)
     (deqs  : gset nat),          (** Dequeued indices. *)
  (** Physical data. *)
  (blk, 0%Z) ↦{1/2} Vint sz ∗ (blk, 1%Z) ↦ Vint back ∗
  ([∗ list] i ↦ v ∈ array_content sz slots deqs, (blk, i + 2)%Z ↦ v) ∗
  (** Logical contents of the queue and prophecy contents. *)
  back_value γb back ∗
  i2_lower_bound γi (match cont with WithCont _ i2 => i2 | NoCont _ => back `min` sz end) ∗
  own γe (● (Excl' (map (get_value slots deqs) pref ++ rest))) ∗
  own γs (● (of_slot_data <$> slots : gmap nat per_slot)) ∗
  hwq_proph blk sz deqs pvs ∗
  (** Per-slot ownership. *)
  ([∗ map] i ↦ d ∈ slots, per_slot_own γe γs i d) ∗
  (** Contradiction status. *)
  match cont with NoCont _ => no_contra γc | WithCont i1 i2 => contra γc i1 i2 end ∗
  (** Tying the logical and physical data and some other pure stuff. *)
  ⌜(∀ i, (i < back `min` sz) ↔ is_Some (slots !! i)) ∧
   (∀ i, (was_committed <$> slots !! i = Some false → was_written <$> slots !! i = Some false) ∧
         (was_written <$> slots !! i = Some false → i ∉ deqs)) ∧
   (∀ i, i ∈ pref → was_committed <$> slots !! i = Some true ∧ i ∉ deqs ∧
                    match cont with WithCont i1 _ => i ≠ i1 | _ => True end) ∧
   (∀ i, i ∈ deqs → was_written <$> slots !! i = Some true ∧
                    was_committed <$> slots !! i = Some true ∧
                    array_get slots deqs i = Vint 0) ∧
   (NoDup (pvs ++ elements deqs) ∧ ∀ i, i ∈ pvs → i < sz) ∧
   match cont with
   | NoCont bs      =>
     (∀ b, b ∈ bs → block_valid slots b) ∧
     (bs ≠ [] → rest = []) ∧
     pvs = pref ++ flatten_blocks bs
   | WithCont i1 i2 =>
     (i1 < i2 < sz ∧ i1 < back) ∧
     was_committed <$> slots !! i1 = Some true ∧
     was_written <$> slots !! i1 = Some true ∧ ¬ i1 ∈ deqs ∧
     array_get slots deqs i1 ≠ Vint 0 ∧
     pref ++ [i2] `prefix_of` pvs
  end ∧
  ∀ i v, val_of <$> slots !! i = Some v → v = Vint 0 ∨ ∃ blk ofs, v = Vptr (blk, ofs)⌝)%I.

Global Instance inv_hwq_red {n} sz γb γi γe γc γs blk :
  SLRed n (syn_inv_hwq sz γb γi γe γc γs blk) (inv_hwq sz γb γi γe γc γs blk).
Proof. solve_sl_red. Qed.

Definition is_hwq (n : nat) (N : namespace) sz γe v : iProp :=
  ∃ γb γi γc γs γh blk, ⌜v = Vptr (blk, 0%Z)⌝ ∗ hinv N γh (syn_inv_hwq sz γb γi γe γc γs blk : GTerm.t n).

(** * Some useful instances *************************************************)

Local Instance blocks_match_persistent (bs : blocks) γc i1 :
  Persistent (match bs with
              | []           => True
              | (i2, _) :: _ => contra γc i1 i2
              end)%I.
Proof. destruct bs as [|[i2 _] _]; apply _. Qed.

Local Instance cont_match_persistent cont γc :
  Persistent (match cont with
              | NoCont _       => True
              | WithCont i1 i2 => contra γc i1 i2
              end)%I.
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

Local Instance contra_timeless cont γc :
  Timeless (match cont with
            | NoCont _       => no_contra γc
            | WithCont i1 i2 => contra γc i1 i2
            end).
Proof. destruct cont as [i1 i2|_]; apply _. Qed.

(** * Some important lemmas for the specification of [enqueue] **************)

Definition get_values (slots : gmap nat slot_data) (p : list nat) :=
  fold_right (λ i acc, match val_of <$> slots !! i with
                       | None   => acc
                       | Some l => l :: acc end) [] p.

Definition get_values_not_in n ps d s :
  n ∉ ps → get_values (<[n:=d]> s) ps = get_values s ps.
Proof.
  intros ?. induction ps as [|p ps IH]; first done. simpl.
  assert (n ≠ p) as Hn_not_p by set_solver.
  rewrite lookup_insert_ne; last done.
  rewrite IH; first done. set_solver.
Qed.

Definition helped (p : list nat) (i : nat) d :=
  match state_of d with
  | Pend γ => if decide (i ∈ p) then
                Some (val_of d, Help γ, was_written d)
              else
                Some d
  | _      => Some d
  end.

Lemma is_Some_helped (p : list nat) i d : is_Some (helped p i d).
Proof.
  rewrite /helped. destruct (state_of d); try by eexists.
  destruct (decide (i ∈ p)); by eexists.
Qed.

Lemma map_imap_helped_nil slots : map_imap (helped []) slots = slots.
Proof.
  apply map_eq. intros i. rewrite map_lookup_imap.
  destruct (slots !! i) as [d|] eqn:HEq.
  - rewrite /helped /= HEq. by destruct (state_of d).
  - by rewrite /= HEq.
Qed.

Lemma annoying_lemma_1 slots deqs pref i l b_pendings :
  (∀ k, k ∈ pref → was_committed <$> slots !! k = Some true ∧ k ∉ deqs) →
  NoDup (pref ++ i :: b_pendings) →
  map (get_value (map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)) deqs) pref =
  map (get_value slots deqs) pref.
Proof.
  intros Hpref HND.
  induction pref as [|pref_hd pref IH]; first done.
  assert (NoDup (pref ++ i :: b_pendings)) as HND_IH.
  { simpl in HND. apply NoDup_cons in HND as [_ HND]. done. }
  assert (∀ k, k ∈ pref → was_committed <$> slots !! k = Some true ∧
                          k ∉ deqs) as Hpref_IH.
  { intros k Hk. by apply Hpref, elem_of_list_further, Hk. }
  rewrite /= IH; try done. clear IH HND_IH Hpref_IH. f_equal.
  assert (i ≠ pref_hd) as Hi_not_pref_hd.
  { simpl in HND. apply NoDup_cons in HND as (HND & _).
    apply not_elem_of_app in HND as (_ & HND).
    by apply not_elem_of_cons in HND as (HND & _). }
  rewrite /get_value map_lookup_imap lookup_insert_ne; last done.
  destruct (slots !! pref_hd) as [[[lp sp] wp]|]; last done.
  destruct sp; try done. rewrite /= /helped /=.
  rewrite decide_False; first done.
  simpl in HND. apply NoDup_cons in HND as (HND & _).
  apply not_elem_of_app in HND as (_ & HND).
  by apply not_elem_of_cons in HND as (_ & HND).
Qed.

Lemma annoying_lemma_2 slots deqs pref i l b_pendings :
  block_valid slots (i, b_pendings) →
  NoDup (pref ++ i :: b_pendings) →
  map (get_value (map_imap (helped b_pendings) (<[i:=(l, Done, false)]> slots)) deqs) b_pendings =
  get_values (<[i:=(l, Done, false)]> slots) b_pendings.
Proof.
  intros (Hvalid_1 & Hvalid_2) HND.
  induction b_pendings as [|p ps IH]; first done. simpl in *.
  assert (i ≠ p) as Hi_not_p.
  { intros ->. apply NoDup_app in HND as (_ & _ & HND).
    apply NoDup_cons in HND as (HND & _). by set_solver +HND. }
  rewrite lookup_insert_ne; last done.
  assert (p ∈ p :: ps) as Hcomm%Hvalid_2 by set_solver.
  destruct (slots !! p)
    as [[[lp sp] wp]|] eqn:Hslots_p; [ f_equal | by inversion Hcomm ].
  - rewrite /= map_imap_insert /helped /= /get_value.
    rewrite lookup_insert_ne; last done. rewrite map_lookup_imap Hslots_p /=.
    destruct sp; try done. rewrite decide_True; [ done | by set_solver ].
  - rewrite -IH; first last; try done.
    { apply NoDup_app in HND as (HND1 & HND2 & HND3).
      apply NoDup_app. split; first done. split.
      - intros e He. apply HND2 in He. apply not_elem_of_cons.
        split; by set_solver +He.
      - apply NoDup_cons in HND3 as (HND3_1 & HND3_2).
        apply NoDup_cons. split; first by set_solver +HND3_1.
        apply NoDup_cons in HND3_2 as (HND3_2_1 & HND3_2_2). done. }
    { intros k Hk. by apply Hvalid_2, elem_of_list_further, Hk. }
    apply map_ext_in. intros k Hk.
    rewrite /get_value map_lookup_imap map_lookup_imap.
    assert (i ≠ k) as Hi_not_k.
    { intros ->. apply NoDup_app in HND as (_ & _ & HND).
      apply NoDup_cons in HND as (HND & _).
      apply not_elem_of_cons in HND as (_ & HND).
      by apply HND, elem_of_list_In, Hk. }
    rewrite lookup_insert_ne; last done.
    assert (k ∈ p :: ps) as Hk_p_ps
      by by apply elem_of_list_further, elem_of_list_In.
    specialize (Hvalid_2 _ Hk_p_ps) as Hcomm_k.
    destruct (slots !! k) as [[[lk sk] wk]|]; last by inversion Hcomm_k.
    destruct sk; try done. rewrite /= /helped /=.
    rewrite decide_True; last done.
    rewrite decide_True; [ done | by apply elem_of_list_In ].
Qed.

Lemma array_contents_cases γs slots deqs i li :
  own γs (● (of_slot_data <$> slots) : slotUR) -∗
  slot_val_wit γs i li -∗
    ⌜array_get slots deqs i = li ∨ array_get slots deqs i = Vint 0⌝.
Proof.
  iIntros "Hs● Hval_wit_i".
  iDestruct (use_val_wit with "Hs● Hval_wit_i") as %Hslots_i.
  destruct (slots !! i) as [d|] eqn:HEq; last by inversion Hslots_i.
  destruct d as [[li' si] wi]. inversion Hslots_i as [a]; subst li'.
  rewrite /array_get HEq. simpl. iPureIntro.
  destruct (decide (i ∈ deqs)); first by right.
  destruct wi; by [ left | right ].
Qed.
End herlihy_wing_queue.
