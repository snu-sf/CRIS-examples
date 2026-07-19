(* Definition of resource algebras needed for WMM specs *)
Require Import CRIS.common.CRIS.
From CRIS.promise_free.lib Require Import Basic Val.
From CRIS.promise_free.model Require Import Cell.
From CRIS.promise_free.lib Require Import Loc.
From CRIS.promise_free.model Require Import
  Time View TView Memory Local Global Configuration.
From CRIS.promise_free.gpfsl Require Import LatticeRA.
From CRIS.promise_free.algebra Require Import ToAgree.

(* Corresponds to gpfsl's view explicit *)
Definition view_at `(P : View.t → iProp Σ) (V : View.t) := P V.
Notation "'@{' V '}' P" := (view_at P V) (at level 25, format "@{ V }  P") : bi_scope.
Definition syn_view_at `{!crisG Γ Σ α β τ _S _I} `(P : View.t → GTerm.t n) (V : View.t) : GTerm.t n := P V.
Notation "'@{' V '}' P" := (syn_view_at P V) (at level 25, format "@{ V }  P") : SAT_scope.

Global Instance Loc_eq_dec : EqDecision Loc.t.
Proof. ii; apply Loc.eq_dec. Qed.

Canonical Structure CellO := (leibnizO Cell.t).
Canonical Structure TViewO := (leibnizO TView.t).

(* Standard memory points-to *)
Local Definition histR_aux : cmra := Loc.t -d> optionUR (prodR dfracR (agreeR CellO)).
Definition histR : ucmra := authUR histR_aux.
(* Cmra to manage views, which include thread-local simple views and SC views. *)
Definition viewR : ucmra := authR (Ident.t -d> optionUR (exclR TViewO)).
(* RA to manage block deallocation *)
Definition hist_freeableUR : ucmra :=
  authUR (Tid.t * Bid.t -d> optionUR (prodR fracR (exclR ZO))).

Class histGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] histGS_view :: inG viewR Γ;
  #[local] histGS_hist :: inG histR Γ;
  #[local] histGS_free :: inG hist_freeableUR Γ;
}.
Class histGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] histGS_histGpreS :: histGpreS;
  view_name : gname;
  hist_name : gname;
  free_name : gname;
}.
Definition histΓ : HRA := #[viewR; histR; hist_freeableUR].
Global Instance subG_histGS `{!crisG Γ Σ α β τ _S _I} : subG histΓ Γ → histGpreS.
Proof. solve_inG. Defined.

Local Existing Instances histGS_histGpreS histGS_view histGS_hist histGS_free.

Implicit Types
  (l : Loc.t) (t : Time.t) (V : View.t) (C ζ : Cell.t) (M : Memory.t) (q : Qp)
  (tid : Ident.t) (𝓥 : TView.t).

Section preds.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  (* Hist predicate *)
  Definition hist_def l q C : iProp Σ :=
    own hist_name (◯ (discrete_fun_singleton l (Some (DfracOwn q, to_agree C)))).
  Definition hist_aux : seal (@hist_def). Proof. by eexists. Qed.
  Definition hist := unseal hist_aux.
  Definition hist_eq : @hist = @hist_def := seal_eq hist_aux.

  Definition hist_auth_def (m : Memory.t) : iProp Σ :=
    own hist_name (● ((λ l,
      if Memory.accessible l m
      then
        Some (DfracOwn 1, to_agree (Memory.get_cell l m))
      else None) : histR_aux)).
  Definition hist_auth_aux : seal (@hist_auth_def). Proof. by eexists. Qed.
  Definition hist_auth := unseal hist_auth_aux.
  Definition hist_auth_eq : @hist_auth = @hist_auth_def := seal_eq hist_auth_aux.

  (* Tview pred which threads manage *)
  Definition tview_def tid 𝓥 : iProp Σ :=
    own view_name (◯ (discrete_fun_singleton tid (Some (Excl 𝓥)))).
  Definition tview_aux : seal (@tview_def). Proof. by eexists. Qed.
  Definition tview := unseal tview_aux.
  Definition tview_eq : @tview = @tview_def := seal_eq tview_aux.

  Definition tview_auth_def (ths : Threads.t) : iProp Σ :=
    own view_name (● ((λ tid, (option_map (Excl ∘ Local.tview ∘ snd) (IdentMap.find tid ths)))
      : Ident.t -d> optionUR (exclR TViewO))).
  Definition tview_auth_aux : seal (@tview_auth_def). Proof. by eexists. Qed.
  Definition tview_auth := unseal tview_auth_aux.
  Definition tview_auth_eq : @tview_auth = @tview_auth_def := seal_eq tview_auth_aux.

  (* Freeable block tokens *)
  Definition hist_freeable_def l q n : iProp Σ :=
    ∃ tid bid,
      ⌜l = Loc.mk (Some tid) bid 0⌝
      ∗ own free_name (◯ (discrete_fun_singleton (tid, bid) (Some (q, Excl n)))).
  Definition hist_freeable_aux : seal (@hist_freeable_def). Proof. by eexists. Qed.
  Definition hist_freeable := unseal hist_freeable_aux.
  Definition hist_freeable_eq : @hist_freeable = @hist_freeable_def :=
    seal_eq hist_freeable_aux.

  Definition hist_freeable_auth_def (m : Memory.t) : iProp Σ :=
    own free_name (● ((λ '(tid, bid),
      if Memory.is_freeable (Loc.mk (Some tid) bid 0) m
      then
        match Memory.get_size (Loc.mk (Some tid) bid 0) m with
        | Some sz => Some (1%Qp, Excl sz)
        | None => None
        end
      else None
    ) : Tid.t * Bid.t -d> optionUR (prodR fracR (exclR ZO)))).
  Definition hist_freeable_auth_aux : seal (@hist_freeable_auth_def). Proof. by eexists. Qed.
  Definition hist_freeable_auth := unseal hist_freeable_auth_aux.
  Definition hist_freeable_auth_eq : @hist_freeable_auth = @hist_freeable_auth_def :=
    seal_eq hist_freeable_auth_aux.

  (* Local observations *)
  Definition seen_local l t V := t ⊑ ((View.rlx V) l).
  Definition seen_view l t V' V := seen_local l t V ∧ V' ⊑ V.
  Definition alloc_local l C V :=
    View.alloc_view V (Loc.get_tbid l) ∧ ∃ t m, (Cell.get t C) = Some m ∧ seen_local l t V.
End preds.

Section syn_preds.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  Definition syn_hist n loc q C : GTerm.t n :=
    sown hist_name (◯ (discrete_fun_singleton loc (Some (DfracOwn q, to_agree C)))).
  Lemma syn_hist_red n loc q C :
    ⟦syn_hist n loc q C⟧ ⊣⊢ hist loc q C.
  Proof. solve_base_sl_red; rewrite /hist seal_eq //. Qed.
End syn_preds.

Notation "†{ q } l … n" := (hist_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (hist_freeable l 1 n) (at level 20) : bi_scope.
(* Notation "†{ q } l" := (hist_freeable l q)
  (at level 20, q at level 50, format "†{ q } l") : bi_scope.
Notation "† l" := (hist_freeable l 1) (at level 20) : bi_scope. *)

(* TODO : move to Loc.v or find canonical way *)
Definition shift (loc : Loc.t) (n : nat) : Loc.t :=
  match loc with
  | Loc.mk tid bid ofs => Loc.mk tid bid (ofs + (Z.of_nat n))%Z
  end.
Infix ">>" := shift (at level 50, left associativity) : stdpp_scope.
Notation "(>>)" := shift (only parsing) : stdpp_scope.
Notation "( l >>)" := (shift l) (only parsing) : stdpp_scope.
Arguments shift : simpl never.

Lemma shift_0 loc : loc >> 0 = loc.
Proof. case loc => ???; rewrite /shift /= Z.add_0_r //. Qed.

Lemma shift_nat_assoc l (n1 n2: nat) : (l >> n1) >> n2 = l >> (n1 + n2).
Proof. case l => ???; rewrite /shift -Z.add_assoc; f_equiv; lia. Qed.

Section hist.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  Lemma hist_own_to_hist_lookup m loc q C :
    hist_auth m -∗ hist loc q C -∗ ⌜ Memory.get_cell loc m = C ⌝.
  Proof.
    rewrite hist_eq /hist_def hist_auth_eq /hist_auth_def.
    iIntros "A F"; iCombine "A" "F" gives %WF; iPureIntro.
    move : WF => /auth_both_valid_discrete [WF _].
    eapply (discrete_fun_included_spec_1 _ _ loc) in WF.
    move : WF; rewrite discrete_fun_lookup_singleton /=; des_ifs.
    2:{ intros HS; inv HS; destruct x; inv H. }
    move => /Some_included; case.
    { intros EQ; inv EQ; ss. apply to_agree_inj in H0; inv H0; ss. }
    { move => /pair_included [_ Hin]; move: Hin => /to_agree_included -> //. }
  Qed.

  Lemma hist_own_hist_cut m Vcut loc q C :
    hist_auth (Memory.cut Vcut m) -∗ hist loc q C -∗
      ⌜∃ t, (View.rlx Vcut) loc = t
          ∧ C = Cell.cut (Memory.get_cell loc m) t
          ∧ Memory.accessible loc m⌝.
  Proof.
    iIntros "HA hist".
    iDestruct (hist_own_to_hist_lookup with "HA hist") as %<-.
    rewrite Memory.cut_get_cell.
    rewrite hist_auth_eq /hist_auth_def hist_eq /hist_def.
    iCombine "HA" "hist" gives %WF%auth_both_valid_discrete; destruct WF as [WF _].
    apply (discrete_fun_included_spec_1 _ _ loc) in WF.
    rewrite discrete_fun_lookup_singleton in WF; des_ifs; cycle 1.
    { apply Some_included_is_Some in WF; inv WF. }
    iPureIntro; esplits; eauto.
  Qed.
End hist.

Section tview.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  Lemma tview_both_valid (ths : Threads.t) tid 𝓥 :
    tview_auth ths -∗ tview tid 𝓥
    -∗ ⌜∃ lang lc, IdentMap.find tid ths = Some (lang, lc) ∧ Local.tview lc = 𝓥⌝.
  Proof.
    rewrite tview_auth_eq /tview_auth_def tview_eq /tview_def.
    iIntros "A F"; iCombine "A F" as "AF" gives %WF.
    eapply auth_both_valid_discrete in WF as [WF1%discrete_fun_included_spec_1 WF2].
    instantiate (1:=tid) in WF1; rewrite discrete_fun_lookup_singleton in WF1.
    apply Some_included_is_Some in WF1 as ISSOME.
    destruct (IdentMap.find tid ths) as [[lang lc]|]; last inv ISSOME; ss.
    apply Excl_included in WF1; inv WF1.
    iPureIntro. esplits; eauto.
  Qed.

  Lemma tview_auth_update {lang} (ths ths' : Threads.t) tid 𝓥 𝓥' st lc
      (UPDATE : ths' = IdentMap.add tid (existT lang st, lc) ths)
      (UPDATEV : Local.tview lc = 𝓥') :
    tview_auth ths -∗ tview tid 𝓥 ==∗ tview_auth ths' ∗ tview tid 𝓥'.
  Proof.
    iIntros "A F"; iPoseProof (tview_both_valid with "A F") as "[%l [%lctid [%FIND %EQ]]]".
    iRevert "A F".
    rewrite tview_auth_eq /tview_auth_def tview_eq /tview_def.
    iIntros "A F"; iCombine "A" "F" as "AF"; iMod (own_update with "AF") as "[A F]";
      [|(iModIntro; iFrame)].
    etrans; first eapply auth_update, discrete_fun_local_update => x; cycle 1.
    { rewrite comm; refl. }
    destruct (decide (x = tid)).
    { subst x ths'; rewrite IdentMap.gss FIND ?discrete_fun_lookup_singleton; ss; clarify.
      eapply option_local_update, exclusive_local_update; ss.
    }
    rewrite ?discrete_fun_lookup_singleton_ne; try (ii; clarify; fail).
    subst ths'; rewrite (IdentMap.gso); ss.
  Qed.

  Lemma tview_auth_alloc ths tid 𝓥 lc lang :
    IdentMap.find tid ths = None →
    Local.tview lc = 𝓥 →
    tview_auth ths ==∗ tview_auth (IdentMap.add tid (lang, lc) ths) ∗ tview tid 𝓥.
  Proof.
    rewrite tview_auth_eq /tview_auth_def tview_eq /tview_def -own_op.
    iIntros (NIN EQ) "?"; iApply (own_update with "[$]").
    apply auth_update_alloc, discrete_fun_local_update; intros x; destruct (decide (x = tid)).
    { subst x; rewrite NIN /= IdentMap.gss //= discrete_fun_lookup_singleton EQ.
      by apply alloc_option_local_update.
    }
    { by rewrite discrete_fun_lookup_singleton_ne // IdentMap.gso //. }
  Qed.
End tview.

Section hist_freeable.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  Lemma hist_freeable_auth_alloc lc1 gl1 sz lc2 gl2 loc
      (WF : Global.wf gl1)
      (STEP : Local.alloc_step lc1 gl1 loc sz lc2 gl2) :
    hist_freeable_auth (Global.memory gl1)
    ==∗ hist_freeable loc 1 sz ∗ hist_freeable_auth (Global.memory gl2).
  Proof.
    rewrite hist_freeable_auth_eq /hist_freeable_auth_def hist_freeable_eq /hist_freeable_def.
    destruct loc as [[tid | ] bid ofs]; last (inv STEP; inv ALLOC).
    iIntros "A"; iMod (own_update with "A") as "[A F]"; cycle 1.
    { iModIntro; iSplitR "A"; last done.
      iExists tid, bid; iSplitR "F"; ss.
      inv STEP; inv ALLOC; ss.
    }
    apply auth_update_alloc, discrete_fun_local_update; intros [tid' bid']; ss.
    inv STEP. inv WF.
    hexploit Memory.alloc_is_freeable; eauto.
    instantiate (1:=Loc.mk (Some tid') bid' 0); ss; intros [[NEW [F1 F2]] | [NEQ EQ]].
    { do 2 destruct (Memory.is_freeable _ _); ss. rewrite /Loc.get_tbid in NEW; ss; clarify.
      rewrite discrete_fun_lookup_singleton /Memory.get_size.
      inv ALLOC; ss; des_ifs; ss; des; clarify.
      rewrite /Block.get_size in Heq; ss; inv Heq.
      eapply alloc_option_local_update; ss.
    }
    rewrite /Loc.get_tbid in NEQ; ss.
    rewrite discrete_fun_lookup_singleton_ne; last ii; clarify.
    rewrite EQ; des_if; ss.
    remember (Loc.mk _ _ 0) as loc.
    hexploit (Memory.alloc_get_size); eauto; i; des.
    { exfalso; apply NEQ; instantiate (1:=loc) in H1; revert H1; rewrite /Loc.get_tbid; i; clarify. }
    rewrite H0; des_ifs.
  Qed.

  Lemma hist_freeable_auth_write lc1 gl1 loc from to val releasedm released ord lc2 gl2
      (WF : Global.wf gl1)
      (STEP : Local.write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2) :
    hist_freeable_auth (Global.memory gl1)
    ==∗ hist_freeable_auth (Global.memory gl2).
  Proof.
    rewrite hist_freeable_auth_eq /hist_freeable_auth_def.
    iIntros "H"; iApply (own_update with "H").
    eapply auth_update_auth, discrete_fun_local_update; intros [tid bid]; s.
    inv STEP; hexploit (Memory.add_preserve); eauto.
    hexploit Memory.add_get_size; eauto; intros ->.
    rewrite /Memory.is_freeable /Block.is_freeable /Memory.get_state.
    intros [-> _]; ss; refl.
  Qed.
End hist_freeable.

Section na_defs.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  Definition own_loc_prim l q C V : iProp Σ :=
    ⌜alloc_local l C V⌝ ∗ hist l q C.

  Definition own_loc_na_def l q v V : iProp Σ :=
    ∃ f t (LT : Time.lt f t) V' b,
      own_loc_prim l q (@Cell.singleton f t (Message.message v V' b) LT) V
      ∗ ⌜V' ⊑ V⌝.
  Definition own_loc_na_aux : seal (@own_loc_na_def). Proof. by eexists. Qed.
  Definition own_loc_na := unseal (@own_loc_na_aux).
  Definition own_loc_na_eq : @own_loc_na = _ := seal_eq _.
  Definition own_loc_na_any l q V : iProp Σ := (∃ v, own_loc_na l q v V)%I.

  Definition own_loc_def l q V : iProp Σ :=
    (∃ f t (LT : Time.lt f t) m, own_loc_prim l q (Cell.singleton m LT) V)%I.
  Definition own_loc_aux : seal (@own_loc_def). Proof. by eexists. Qed.
  Definition own_loc := unseal (@own_loc_aux).
  Definition own_loc_eq : @own_loc = _ := seal_eq _.

  (* TODO : find a way to handle this *)
  Definition own_loc_na_vec l q (vl : list Val.t) V : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, own_loc_na (l >> i) q v V)%I.
  Definition own_loc_vec l q (n : nat) V : iProp Σ :=
    ⌜View.alloc_view V (Loc.get_tbid l)⌝ ∗ ([∗ list] i ∈ seq 0 n, own_loc (l >> i) q V)%I.
End na_defs.

Section syn_preds.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.

  Definition syn_own_loc_prim n l q C V : GTerm.t n :=
    ⌜alloc_local l C V⌝ ∗ syn_hist n l q C.

  Definition syn_own_loc_na_def n loc q v V : GTerm.t n :=
    (∃ (f t : τ{Time.t}) (LT : τ{Time.lt f t}) (V' : τ{View.t}) (b : τ{bool}),
      syn_own_loc_prim n loc q (@Cell.singleton f t (Message.message v V' b) LT) V
      ∗ ⌜V' ⊑ V⌝)%SAT.
  Definition syn_own_loc_na_aux : seal (@syn_own_loc_na_def). Proof. by eexists. Qed.
  Definition syn_own_loc_na := unseal (@syn_own_loc_na_aux).
  Definition syn_own_loc_na_eq : @syn_own_loc_na = _ := seal_eq _.

  Lemma syn_own_loc_na_red n loc q v V :
    ⟦syn_own_loc_na n loc q v V⟧ ⊣⊢ @{V} own_loc_na loc q v.
  Proof.
    rewrite own_loc_na_eq /own_loc_na_def syn_own_loc_na_eq /syn_own_loc_na_def.
    solve_base_sl_red. rewrite /view_at /own_loc_prim hist_eq //.
  Qed.
End syn_preds.

Notation "l p↦ C" := (own_loc_prim l 1 C)
  (at level 20, format "l  p↦  C")  : bi_scope.
Notation "l p↦{ q } C" := (own_loc_prim l q C)
  (at level 20, format "l  p↦{ q }  C")  : bi_scope.

Notation "l ↦ v" := (own_loc_na l 1 v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "l ↦ -" := (own_loc_na_any l 1)
  (at level 20, format "l  ↦  -") : bi_scope.
Notation "l ↦ ?" := (own_loc l 1) (at level 20, format "l  ↦  ?")  : bi_scope.
Notation "l ↦∗ vl" := (own_loc_na_vec l 1 vl) (at level 20) : bi_scope.
Notation "l ↦∗: P " := (∃ vl, l ↦∗ vl ∗ P vl)%I
  (at level 20, format "l  ↦∗:  P") : bi_scope.

Notation "l ↦{ q } v" := (own_loc_na l q v)
  (at level 20, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦{ q } -" := (own_loc_na_any l q)
  (at level 20, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦{ q } ?" := (own_loc l q) (at level 20, format "l  ↦{ q }  ?").
Notation "l ↦∗{ q } vl" := (own_loc_na_vec l q vl)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
Notation "l ↦∗{ q }: P" := (∃ vl, l ↦∗{ q } vl ∗ P vl)%I
  (at level 20, q at level 50, format "l  ↦∗{ q }:  P") : bi_scope.

(* SAT notations *)
Notation "l ↦ v" := (syn_own_loc_na _ l 1 v)
  (at level 20, format "l  ↦  v") : SAT_scope.
Notation "l ↦{ q } v" := (syn_own_loc_na _ l q v)
  (at level 20, format "l  ↦{ q }  v") : SAT_scope.

(* TODO : a lot of properties regarding predicates defined above needs to be stated and proven,
   Let's first check out if the spec really works & feasible *)

(* Typeclass for manually doing what vProp did in gpfsl *)
Class MonPred `(P : View.t → iProp Σ) := { MonPred_at :: Proper ((⊑) ==> (⊢)) P }.
#[global] Instance view_at_mon_pred `{MonPred Σ P} : MonPred (view_at P).
Proof. ss. Qed.
#[global] Instance view_at_cur_mon_pred `{MonPred Σ P} :
  Proper ((TView.le) ==> (⊢)) (λ V : TView.t, @{TView.cur V} P)%I.
Proof.
  intros ?? Hle; inversion_clear Hle as [? CUR ?]; rewrite /view_at; iIntros "H".
  assert (TView.cur x ⊑ TView.cur y) by ss; rewrite H0 //.
Qed.

(* Tactic for synchronizing mem-related iProps, i.e. @{V} P *)
Ltac tview_sync H :=
  let T := type of H in
  let name := fresh "H" in
  let CUR := fresh "H" in
  let ACQ := fresh "H" in
  let RLX := fresh "H" in
  match T with
  | TView.le ?V1 ?V2 =>
      match goal with
      | |- _ =>
        inversion H as [RLX CUR ACQ]; assert (name : TView.cur V1 ⊑ TView.cur V2) by ss;
        rewrite name;
        clear name CUR ACQ RLX 
      end
  end.

Section na_props.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS}.
  #[global] Instance alloc_local_mon_pred l C : MonPred (λ V, ⌜alloc_local l C V⌝ : iProp Σ)%I.
  Proof.
    econs; intros ?? Hle; rewrite /view_at /alloc_local /seen_local.
    iIntros "[%AV %]"; iPureIntro; split; eauto.
    { inv AV. inv Hle. eapply ALLOC_VIEW. done. }
    { des; esplits; eauto. etrans; eauto. inv Hle; ss. }
  Qed.

  #[global] Instance own_loc_na_mon_pred l q v : MonPred (l ↦{ q } v)%I.
  Proof.
    econs; ii; rewrite /view_at own_loc_na_eq; iIntros "[% [% [% [% [% [[H ?] %]]]]]]"; iFrame.
    iSplit; last (iPureIntro; etrans; eauto).
    pose proof (alloc_local_mon_pred l (Cell.singleton (Message.message v V' b) LT)).
    inv H1. rewrite MonPred_at0 //.
  Qed.
  
  #[global] Instance own_loc_mon_pred l q : MonPred (l ↦{ q } ?).
  Proof.
    econs; intros ?? Heq; rewrite own_loc_eq; iIntros "[% [% [% [% [H $]]]]]".
    epose proof (alloc_local_mon_pred l (Cell.singleton _ LT)).
    inv H; rewrite MonPred_at0 //.
  Qed.

  Lemma own_loc_mon_pred_gen l q v V1 V2 : V1 ⊑ V2 → @{V1} l ↦ v ⊢ @{V2} l ↦ v.
  Proof. intros H1; rewrite H1 //. Qed.

  Lemma own_loc_na_own_loc l v q V : @{V} l ↦{q} v -∗ @{V} l ↦{q} ?.
  Proof.
    rewrite own_loc_na_eq own_loc_eq.
    iDestruct 1 as (t m ???) "[own ?]". iExists _,_. by iFrame.
  Qed.

  Lemma own_loc_na_vec_nil l q V : @{V} l ↦∗{q} [] ⊣⊢ True.
  Proof. rewrite /own_loc_na_vec bi.True_emp //. Qed.

  Lemma own_loc_na_vec_app l q vl1 vl2 V :
    @{V} l ↦∗{q} (vl1 ++ vl2) ⊣⊢ @{V} l ↦∗{q} vl1 ∗ @{V} (l >> length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /view_at /= /own_loc_na_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite shift_nat_assoc.
  Qed.

  Lemma own_loc_na_vec_singleton l q v V : @{V} l ↦∗{q} [v] ⊣⊢ @{V} l ↦{q} v.
  Proof. rewrite /own_loc_na_vec /view_at /= shift_0 right_id //. Qed.

  Lemma own_loc_na_vec_cons l q v vl V :
    @{V} l ↦∗{q} (v :: vl) ⊣⊢ @{V} l ↦{q} v ∗ @{V} (l >> 1) ↦∗{q} vl.
  Proof. rewrite (own_loc_na_vec_app l q [v] vl) own_loc_na_vec_singleton //. Qed.
End na_props.
