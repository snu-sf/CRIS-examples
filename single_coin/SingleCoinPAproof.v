Require Import CRIS.
Require Import SingleCoinHeader SingleCoinP SingleCoinA.
Require Import ProphecyHeader ProphecyA.

Local Program Definition coin_proph : Prophecy.t := {|
  Prophecy.Pro := bool;
  Prophecy.Obs := bool;
  Prophecy.consistent := λ l p, l = [] ∨ ∃ tl, l = tl ++ [p];
  Prophecy.obs_default := true;
|}.
Next Obligation.
  intros seq; exists (seq 0); intros i; induction i.
  { left; ss. }
  { right; ss. destruct i; s; [exists nil; ss|]. destruct IHi as [H|H]; [inv H|].
    destruct H as [tl H].
    exists (seq (S i) :: tl); ss; rewrite H; ss.
  }
Qed.

Module SingleCoinPA. Section SingleCoinPA.
  Import SingleCoinAS SingleCoinP.
  Context `{_crisG: !crisG Γ Σ α β τ _I _S}.
  Context `{_prophG: !prophG}.
  Context `{_coinG: !coinG}.

  Context (sp : string → option fspec).

  Local Definition MA := SingleCoinA.t sp.
  Local Definition MI := SingleCoinP.t ★ ProphecyA.t sp.

  Local Definition Ist : alist key Any.t → alist key Any.t → iProp Σ :=
    (λ st_s st_t,
      ∃ (l_s : list bool) (l_t : list (option bool)),
        ⌜st_s = [] ∧ st_t = [(v_coins, l_t↑)] ∧ length l_s = length l_t⌝
        ∗ ProphecyRA.free_id (λ i, i.1 = "SingleCoin" ∧ ∃ n, i.2↓↓ = Some n ∧ n >= length l_t)%type
        ∗ coin_auth l_s
        ∗ [∗ list] i ↦ ob ∈ l_t,
          ∃ b ol, ProphecyRA.has_proph (proph_coins i) (existT coin_proph (b, ol))
          ∗ ⌜nth_error l_s i = Some b
            ∧ (match ob with Some b' => b' = b ∧ ol = [b] | None => ol = [] end)
            ∧ (Prophecy.consistent coin_proph ol b)⌝
        )%I.

  (* Lemma simF_new : HSim.sim_fun open MA MI Ist SingleCoinHdr.new. *)
  (* Proof. *)
  (*   init_simF. *)

  (*   iDestruct "IST" as (l_s l_t) "[[-> [-> %EQ]] [F [AUTH PL]]]". *)

  (*   steps_l. iDestruct "ASM" as "[-> ->]". hss. *)

  (*   steps_r. hss. steps_r. hss. *)
  (*   inline_r. force_r (proph_coins (length l_t), coin_proph). steps_r. *)
  (*   force_r ((proph_coins (length l_t))↑). steps_r. *)
  (*   iPoseProof (ProphecyAS.free_id_split _ (proph_coins (length l_t)) with "F") as "> [F1 F2]". *)
  (*   { ss; hss; esplits; eauto. } *)
  (*   force_r; iFrame; iSplit; eauto. *)
  (*   steps_r. iDestruct "GRT" as "[[%b [-> P]] ->]". hss. steps_r. *)
  (*   (* alloc coin *) *)
  (*   iMod (coin_alloc _ b with "AUTH") as "[AUTH COIN]". *)

  (*   iAssert (Ist nths [] [(v_coins, (l_t ++ [None])↑)]) with "[F2 PL P AUTH]" as "IST". *)
  (*   { rewrite /Ist /=. iExists (l_s ++ [b]), (l_t ++ [None]). iSplit; eauto. *)
  (*     { iPureIntro; splits; ss; eauto. rewrite ?length_app; s; lia. } *)
  (*     iSplitL "F2". *)
  (*     { iApply ProphecyAS.free_id_iff; [|iFrame]. *)
  (*       intros [name a]; split; ss; des_ifs. *)
  (*       { intros H; inv H; des; clarify. inv e. hss. rewrite length_app in H0. ss. lia. } *)
  (*       { intros H; des; esplits; eauto. rewrite length_app in H1; ss; lia. } *)
  (*       { intros [-> [n0 [EQ' GT]]]; esplits; eauto. *)
  (*         assert (n0 <> length l_t). *)
  (*         { ii; clarify; eapply n; rewrite /proph_coins; f_equal. hexploit SAny.downcast_upcast; eauto. } *)
  (*         rewrite length_app; ss; lia. *)
  (*       } *)
  (*     } *)
  (*     iFrame. *)
  (*     iApply (big_sepL_app). iSplitL "PL"; cycle 1. *)
  (*     { s. iSplit; [|done]. iExists b, []; iSplit. *)
  (*       { rewrite Nat.add_0_r; iFrame. } *)
  (*       iPureIntro. rewrite -EQ. rewrite nth_error_app2; rewrite Nat.add_0_r // Nat.sub_diag /=. *)
  (*       splits; ss. *)
  (*       eauto. *)
  (*     } *)
  (*     iApply (big_sepL_impl with "PL"). *)
  (*     iModIntro; iIntros (k x) "% [%b' [%ol' H]]". *)
  (*     apply lookup_lt_Some in H; rewrite -EQ in H. rewrite nth_error_app1 //. *)
  (*     iExists _, _; iFrame. *)
  (*   } *)

  (*   forces_l. iFrame. iSplit; eauto. *)
  (*   steps_l. step. iFrame. rewrite EQ; done. *)
  (* Qed. *)

  (* Lemma simF_read : HSim.sim_fun open MA MI Ist SingleCoinHdr.read. *)
  (* Proof. *)
  (*   init_simF. *)
  (*   steps_l. iDestruct "ASM" as "[[-> C] ->]". hss. rename q1 into n, q2 into b. *)
  (*   iDestruct "IST" as (l_s l_t) "[[-> [-> %EQ]] [F [AU PL]]]". *)
  (*   iPoseProof (coin_both_valid with "AU C") as "%NTH". *)

  (*   steps_r. hss. steps_r. *)
  (*   assert (n < length l_s) by (apply nth_error_Some; ii; clarify). *)
  (*   destruct (nth_error l_t n) eqn : LTN; cycle 1. *)
  (*   { apply nth_error_None in LTN. lia. } *)
  (*   destruct o as [bn'|]. *)
  (*   { (* after initialization *) *)
  (*     iPoseProof (big_sepL_lookup_acc _ _ n with "PL") as "[P PL]". *)
  (*     { edestruct (nth_lookup_or_length l_t n); eauto. lia. } *)
  (*     iDestruct "P" as "[%bn [%oln [P %P]]]". *)
  (*     eapply nth_error_nth in LTN. rewrite LTN in P. rewrite LTN. destruct P as [NTH' [EQ' ?]]. *)
  (*     hexploit EQ'; ss; i; des; clarify. *)
  (*     forces_l. iFrame. iSplit; eauto. *)
  (*     steps_l. steps_r. step. iSplit; eauto. *)
  (*     iFrame. iSplit; eauto. iApply "PL". iExists _, _; iFrame. rewrite NTH'. *)
  (*     iPureIntro; splits; ss. right; esplits; eauto. *)
  (*   } *)
  (*   { (* before initialization *) *)
  (*     hexploit nth_error_split; eauto. *)
  (*     intros [lt_1 [lt_2 [-> LEN1]]]. *)
  (*     steps_r. rewrite take_app Nat.sub_diag /= app_nil_r firstn_all drop_app. *)
  (*     rewrite drop_ge; [|lia]; rewrite /= Nat.sub_succ_l // Nat.sub_diag /= drop_0. *)
  (*     iPoseProof (big_sepL_app with "PL") as "[PL1 [P PL2]]". *)
  (*     iDestruct "P" as "[%bn [%oln [P %HP]]]". *)
  (*     inline_r. force_r (proph_coins _, existT coin_proph (_, _, _)). forces_r. iFrame. *)
  (*     rewrite Nat.add_0_r. iSplit; eauto. *)
  (*     steps_r. iDestruct "GRT" as "[[[-> %GRT] P] ->]". hss. *)
  (*     destruct GRT as [|[tl EQ']]; [clarify|]. *)
  (*     destruct tl; cycle 1. *)
  (*     { inv EQ'. eapply app_cons_not_nil in H2; ss. } *)
  (*     inv EQ'. *)

  (*     steps_r. *)
  (*     forces_l. iFrame. iSplit; eauto. steps_l. step. *)
  (*     rewrite Nat.add_0_r in HP; clarify. *)
  (*     iSplit; eauto. *)
  (*     iExists l_s, _. iSplit; [iPureIntro; splits; eauto|]. *)
  (*     { rewrite EQ ?length_app /= //. } *)
  (*     iSplitL "F". *)
  (*     { iApply ProphecyAS.free_id_iff; ss. rewrite ?length_app //. } *)
  (*     iFrame. *)
  (*     iExists b, [b]; rewrite Nat.add_0_r. iFrame. *)
  (*     iPureIntro; ss; esplits; eauto. right; exists []; eauto. *)
  (*   } *)
  (*   Unshelve. all: exact None. *)
  (* Qed. *)

  (* Theorem sim : HSim.t MA MI ? IstFull.
  Proof.
    init_sim.
    - iIntros "A". iExists _,_,[],[]. iSplit.
      { rewrite !app_nil_r. eauto. }
      iSplit; [iSplit|]; eauto. iExists _,_. iSplit; et.
    - eapply simF_new; eauto.
    - eapply simF_read; eauto.
  Qed. *)
End SingleCoinPA. End SingleCoinPA.

(* Require Import Coqlib ITreelib sflib.
Require Import SingleCoinHeader SingleCoinP SingleCoinA SingleCoinASpec SMod ModSim.
Require Import Any Skeleton.
Require Import PCM IPM.
Require Import Events Behavior.
Require Import ProphecyHeader ProphecyA STB.

Require Import ISim HMod PMod Events ITactics.
Require Import Mod ModSimFacts.

Require Import sProp sWorld World SRF.
Require Import Ensembles.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module SingleCoinPA.
Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
  Context `{_S: SingleCoinAR.t (Γ:=Γ)}.
  Context `{_M: ProphecyAR.t (Γ:=Γ)}.

  Fixpoint initialized_until (l_tgt : list (option bool)) (l_src: list bool) (hi: nat) : iProp :=
    match hi with
    | S hi' =>
        SingleCoinAS.readable hi' ∗
        (⌜exists b, nth_error l_tgt hi' = Some (Some b) /\ nth_error l_src hi' = Some b⌝
         ∨
         (∃ (b : bool) nth,
          ProphecyAS.has_proph ("SingleCoin", hi'↑↑) (existT SingleCoinPrT.t (Full_set _, b, nth))
            ∗ ⌜nth_error l_src hi' = Some b /\ nth_error l_tgt hi' = Some None⌝))
        ∗ initialized_until l_tgt l_src hi'
    | O => emp%I
    end.

  Lemma free_from_split i:
    SingleCoinAS.free_from i -∗ SingleCoinAS.free_from (S i) ∗ (ProphecyAS.free_id (SingleCoinP.proph_coins i)).
  Proof.
    iIntros "H". unfold SingleCoinAS.free_from, ProphecyAS.free_id.
    replace (SingleCoinAS.free_from_r i) with (SingleCoinAS.free_from_r (S i) ⋅ ProphecyAS.free_id_r (SingleCoinP.proph_coins i)).
    { iDestruct "H" as "($ & $)". }
    unfold SingleCoinAS.free_from_r, ProphecyAS.free_id_r. ur. unfold Auth.white. f_equal.
    unfold SingleCoinAS.SingleCoinFree_r. ur. extensionalities.
    unfold SingleCoinP.proph_coins. des_ifs; try solve [ur; des_ifs]; try nia.
    - rewrite SAny.upcast_downcast in Heq. clarify. nia.
    - rewrite SAny.upcast_downcast in Heq. clarify.
    - exfalso. apply n1. f_equal. apply SAny.downcast_upcast. rewrite Heq. f_equal.
      nia.
    - rewrite SAny.upcast_downcast in Heq. clarify.
  Qed.

  Lemma uninitialized_from_split i:
    SingleCoinAS.uninitialized_from i -∗ SingleCoinAS.uninitialized_from (S i) ∗ (SingleCoinAS.uninitialized i).
  Proof.
    iIntros "H". unfold SingleCoinAS.uninitialized_from, SingleCoinAS.uninitialized.
    replace (SingleCoinAS.uninitialized_from_r i) with (SingleCoinAS.uninitialized_from_r (S i) ⋅ SingleCoinAS.uninitialized_r i).
    { iDestruct "H" as "($ & $)". }
    unfold SingleCoinAS.uninitialized_from_r, SingleCoinAS.uninitialized_r. ur.
    extensionalities. des_ifs; try nia; try solve [ur; des_ifs].
  Qed.

  Lemma update_to_readable l :
    SingleCoinAS.uninitialized l ==∗ SingleCoinAS.readable l.
  Proof.
    iIntros "H". unfold SingleCoinAS.uninitialized, SingleCoinAS.readable.
    iPoseProof (OwnM_Upd with "H") as "D"; et. ii. ur. ur in H2. i.
    specialize (H2 k). unfold SingleCoinAS.uninitialized_r, SingleCoinAS.readable_r in *.
    destruct dec; clarify. ur in H2. ur. des_ifs.
  Qed.

  Lemma uninitialized_from_update i:
    SingleCoinAS.uninitialized_from i ==∗ SingleCoinAS.uninitialized_from (S i) ∗ (SingleCoinAS.readable i).
  Proof.
    iIntros "H". iPoseProof (uninitialized_from_split with "H") as "(H0 & H1)".
    iPoseProof (update_to_readable with "H1") as "> H1". iModIntro. iFrame.
  Qed.

  Lemma initialized_until_readable l l0 i:
    initialized_until l l0 (S i) -∗ initialized_until l l0 (S i) ∗ SingleCoinAS.readable i.
  Proof.
    iIntros "H". ss. unfold SingleCoinAS.readable. set (SingleCoinAS.readable_r i) at 1.
    replace c with ((SingleCoinAS.readable_r i) ⋅ (SingleCoinAS.readable_r i)).
    { iDestruct "H" as "(($ & $) & $ & $)". }
    unfold c, SingleCoinAS.readable_r. ur. extensionalities. des_ifs; ur; des_ifs.
  Qed.

  Lemma _initialized_update l_tgt l_src i b (EQ : List.length l_tgt = List.length l_src) (LE : i ≤ List.length l_src):
    initialized_until l_tgt l_src i
      -∗ SingleCoinAS.uninitialized_from i
      -∗ ProphecyAS.has_proph (SingleCoinP.proph_coins i) (existT SingleCoinPrT.t (Full_set bool, b, 0))
      ==∗ initialized_until (firstn i l_tgt ++ [None] ++ skipn (S i) l_tgt) (firstn i l_src ++ [b] ++ skipn (S i) l_src) (S i) ∗ SingleCoinAS.uninitialized_from (S i).
  Proof.
    iIntros "H0 H1 H2". ss. iPoseProof (uninitialized_from_update with "H1") as ">[? ?]".
    iModIntro. iFrame. iSplitL "H2".
    - iRight. iExists _,_. iFrame. iPureIntro. rewrite !nth_error_app2.
      2:{ rewrite take_length. nia. }
      2:{ rewrite take_length. nia. }
      rewrite !take_length. replace (i - _) with 0 by nia. replace (i - _) with 0 by nia.
      ss.
    - set i at 1 6. assert (LE0 : n ≤ i) by nia. clearbody n.
      iInduction n as [|n'] "IH" forall (LE0); ss.
      iDestruct "H0" as "(R & D & I)"; iFrame.
      iSplitR "I". 2:{ iApply "IH"; et. iPureIntro. nia. }
      iDestruct "D" as "[%yes|no]".
      + des. iLeft. iPureIntro.
        rewrite <- (take_drop i l_tgt) in yes.
        rewrite <- (take_drop i l_src) in yes0.
        rewrite !nth_error_app1 in *; try solve [rewrite take_length; nia]; et.
      + iRight. iDestruct "no" as "(%b0 & %nth & P & %X)". iExists _,_. iFrame.
        iPureIntro.
        rewrite <- (take_drop i l_src) in X.
        rewrite <- (take_drop i l_tgt) in X.
        rewrite !nth_error_app1 in *; try solve [rewrite take_length; nia]; et.
  Qed.

  Lemma initialized_update l_tgt l_src b (EQ : List.length l_tgt = List.length l_src) :
    initialized_until l_tgt l_src (List.length l_src)
      -∗ SingleCoinAS.uninitialized_from (List.length l_src)
      -∗ ProphecyAS.has_proph (SingleCoinP.proph_coins (List.length l_src)) (existT SingleCoinPrT.t (Full_set bool, b, 0))
      ==∗ initialized_until (l_tgt ++ [None]) (l_src ++ [b]) (S (List.length l_src)) ∗ SingleCoinAS.uninitialized_from (S (List.length l_src)).
  Proof.
    eassert (l_tgt ++ [None] = _); cycle 1.
    eassert (l_src ++ [b] = _); cycle 1. rewrite H2. rewrite H3.
    apply _initialized_update; et.
    - destruct (drop _ l_src) eqn:E; et.
      2:{ apply (f_equal List.length) in E. rewrite drop_length in E. ss. nia. }
      rewrite app_nil_r. f_equal. set l_src at 1.
      rewrite <- (take_drop (List.length l_src) l). unfold l. clear l.
      destruct (drop (List.length l_src) l_src) eqn:E0; et.
      2:{ apply (f_equal List.length) in E0. rewrite drop_length in E0. ss. nia. }
      rewrite app_nil_r. et.
    - destruct (drop _ l_tgt) eqn:E; et.
      2:{ apply (f_equal List.length) in E. rewrite drop_length in E. ss. nia. }
      rewrite app_nil_r. f_equal. set l_tgt at 1.
      rewrite <- (take_drop (List.length l_src) l). unfold l. clear l.
      destruct (drop (List.length l_src) l_tgt) eqn:E0; et.
      2:{ apply (f_equal List.length) in E0. rewrite drop_length in E0. ss. nia. }
      rewrite app_nil_r. et.
  Qed.

  Lemma uninitialized_readable_disjoint i j:
       SingleCoinAS.uninitialized_from i -∗ SingleCoinAS.readable j -∗ ⌜j < i⌝.
  Proof.
    iIntros "A B". unfold SingleCoinAS.uninitialized_from, SingleCoinAS.readable.
    unfold SingleCoinAS.uninitialized_from_r, SingleCoinAS.readable_r.
    destruct (le_dec i j). 2:{ iPureIntro. nia. }
    iCombine "A B" as "C". iOwnWf "C" as wfc. exfalso.
    ur in wfc. specialize (wfc j). des_ifs; try nia. ur in wfc. et.
  Qed.

  Lemma initialized_until_same i j l_src l_tgt b b0 (ran : i < j)
    (E : nth_error l_src i = Some b) (E0 : nth_error l_tgt i = Some (Some b0)) :
  initialized_until l_tgt l_src j -∗ ⌜b = b0⌝.
  Proof.
    iInduction j as [|j'] "IH"; try nia.
    iIntros "H". destruct (dec i j'); cycle 1.
    { ss. iDestruct "H" as "(_ & _ & H)". iApply "IH"; iFrame. iPureIntro. nia. }
    clarify. ss. iDestruct "H" as "(_ & [%yes|no] & _)".
    - des. rewrite E0 in yes. rewrite E in yes0. clarify.
    - iDestruct "no" as "(%b1 & %nth & _ & %E1)". des. clarify.
  Qed.

  Lemma initialized_until_update_proph b i j l_src l_tgt (ran : i < j) 
    (E : nth_error l_src i = Some b)
    (E0 : nth_error l_tgt i = Some None) :
  initialized_until l_tgt l_src j -∗
  (initialized_until (take i l_tgt ++ Some b :: drop (S i) l_tgt) l_src j
   ∗ ∃ nth, ProphecyAS.has_proph ("SingleCoin", i↑↑) (existT SingleCoinPrT.t (Full_set _, b, nth))).
  Proof.
    iInduction j as [|j'] "IH"; try nia.
    iIntros "H". destruct (dec i j'); cycle 1.
    - ss. iDestruct "H" as "(A & B & H)".
      assert (X: i < j') by nia. iPoseProof ("IH" $! X with "H") as "[I P]". 
      iFrame. iDestruct "B" as "[%yes|no]".
      + des. iLeft. iPureIntro. rewrite yes0. esplits; et.
        rewrite <- (take_drop (S i) l_tgt) in yes.
        rewrite !nth_error_app2 in *. 2:{ rewrite take_length. nia. }
        2:{ rewrite take_length. nia. }
        rewrite take_length in *.
        assert (i < List.length l_tgt).
        { rewrite <- nth_error_Some. rewrite E0. et. }
        replace (_ `min` _) with i by nia.
        replace (_ `min` _) with (S i) in yes by nia.
        change (Some b :: _) with ([Some b] ++ (drop (S i) l_tgt)).
        rewrite nth_error_app2; ss. 2:{ nia. }
        rewrite <- yes. f_equal. nia.
      + iDestruct "no" as "(%b0 & %nth & P & %L)".
        des. iRight. iExists _,_. iFrame. iPureIntro. split; et.
        rewrite <- (take_drop (S i) l_tgt) in L0.
        rewrite !nth_error_app2 in *; rewrite take_length in *; try nia.
        assert (i < List.length l_tgt).
        { rewrite <- nth_error_Some. rewrite E0. et. }
        replace (_ `min` _) with i by nia.
        replace (_ `min` _) with (S i) in L0 by nia.
        change (Some b :: _) with ([Some b] ++ (drop (S i) l_tgt)).
        rewrite nth_error_app2; ss. 2:{ nia. }
        rewrite <- L0. f_equal. nia.
    - clarify. ss. iDestruct "H" as "($ & [%yes|no] & I)". { des. clarify. }
      iDestruct "no" as "(%b0 & %nth & P & %L)". des. iSplitR "P". 2:{ rewrite E in L. clarify. et. }
                                                                 iSplitR.
      + iLeft. iExists b0. iPureIntro. rewrite E in L. clarify. split; et.
        rewrite nth_error_app2. 2:{ rewrite take_length. nia. }
        rewrite take_length. 
        assert (j' < List.length l_tgt).
        { rewrite <- nth_error_Some. rewrite L0. et. }
        replace (_ - _) with 0 by nia. ss.
      + iClear "IH". set (take j' l_tgt ++ Some b :: drop (S j') l_tgt).
        assert (j' < List.length l_tgt).
        { rewrite <- nth_error_Some. rewrite L0. et. }
        assert (forall i, i < j' -> nth_error l_tgt i = nth_error l i).
        { i. unfold l. set l_tgt at 1. rewrite <- (take_drop j' l0).
          unfold l0. rewrite !nth_error_app1; et.
          all: try solve [rewrite take_length; nia]. }
        clearbody l. clear - H3.
        iInduction j' as [|j'] "IH" forall (H3); ss.
        iDestruct "I" as "($ & H & I)". iSplitR "I". 2:{ iApply "IH"; et. }
        iDestruct "H" as "[%yes|no]".
        { iLeft. iPureIntro. des. esplits; et. rewrite <- H3; try nia. et. }
        iRight. iDestruct "no" as "(%b0 & %nth & P & %L)". des.
        iExists _,_. iFrame. iPureIntro. split; et. rewrite <- H3; et.
   Qed.

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ _ st_src st_tgt =>
      ∃ l_tgt l_src,
      ⌜st_tgt = [(SingleCoinP.v_coins, (l_tgt : list (option bool))↑)] /\
       st_src = [(SingleCoinA.v_coins, (l_src : list bool)↑)] /\
       List.length l_tgt = List.length l_src⌝ ∗
      initialized_until l_tgt l_src (List.length l_src) ∗
      SingleCoinAS.free_from (List.length l_src) ∗ SingleCoinAS.uninitialized_from (List.length l_src))%I.

  Variable ginv: Sk.t -> invspec.
  Variable StbProph: Sk.t -> gname -> option fspec.
  Variable StbSingleCoin: Sk.t -> gname -> option fspec.

  Local Notation ProphecyA := (ProphecyA.t ginv StbProph).
  Local Notation SingleCoinA := (SingleCoinA.t ginv StbSingleCoin).
  Local Notation SingleCoinAMod := (SingleCoinA ★ ProphecyA).
  Local Notation SingleCoinPMod := (SingleCoinP.t ★ ProphecyA).
  Local Notation IstFull := (IstProd (IstSB SingleCoinA Ist) IstEq).

  (**********)

  Lemma simF_new:
    HSim.sim_fun SingleCoinAMod SingleCoinPMod IstFull SingleCoinName.new.
  Proof.
    init_simF. unfold IstFull, IstProd0.
    iDestruct "IST" as "(%st_srcL & %st_tgtL & %st_srcR & %st_tgtR & (#-> & #->) & IST)".
    iDestruct "IST" as "((% & IST) & #->)". unfold Ist. rename H2 into INCL.
    iDestruct "IST" as "(%l_tgt & %l_src & (#-> & #-> & %LEN) & (ACTIVATED & FREE & UNACTIVATED))".
    steps_l. hss. rename q2 into l_src. iDestruct "ASM" as "(_ & #<-)". hss.
    steps_r. hss. steps_r. inline_r. steps_r. do 3 force_r.
    instantiate (1 := (_, SingleCoinPrT.t)). ss.
    iPoseProof (free_from_split with "FREE") as "[FREE ARG]". iSplitL "ARG".
    { iSplit; ss. iSplit; ss. rewrite LEN. et. }
    steps_r. iDestruct "GRT" as "((%b & #-> & P) & _)". hss. steps_r.
    iEval (rewrite LEN) in "P".
    iPoseProof (initialized_update with "ACTIVATED") as "D"; et.
    iPoseProof ("D" with "UNACTIVATED") as "D".
    iPoseProof ("D" with "P") as "D". iApply isim_upd. iMod "D" as "[ACTIVATED UNACTIVATED]".
    iModIntro. Local Opaque initialized_until.
    force_l. instantiate (1 := b). steps_l. hss. do 2 force_l.
    iPoseProof (initialized_until_readable with "ACTIVATED") as "[ACTIVATED POST]".
    iSplitL "POST". { iSplit; ss. et. }
    step. iSplit; et. iExists [_],[_],_,_. iSplit; et.
    iSplit; et. iSplit; et. iExists _,_. iSplit; ss.
    { iPureIntro. splits; et. rewrite !app_length. ss. nia. }
    rewrite app_length. ss. rewrite plus_comm. ss. iFrame.
  Qed.

  Lemma simF_read:
    HSim.sim_fun SingleCoinAMod SingleCoinPMod IstFull SingleCoinName.read.
  Proof.
    init_simF. unfold IstFull, IstProd0.
    iDestruct "IST" as "(%st_srcL & %st_tgtL & %st_srcR & %st_tgtR & (#-> & #->) & IST)".
    iDestruct "IST" as "((% & IST) & #->)". unfold Ist. rename H2 into INCL.
    iDestruct "IST" as "(%l_tgt & %l_src & (#-> & #-> & %LEN) & (ACTIVATED & FREE & UNACTIVATED))".
    steps_l. hss. rename q2 into l_src. iDestruct "ASM" as "((% & R) & %)". hss.
    steps_r. hss. steps_r. iPoseProof (uninitialized_readable_disjoint with "UNACTIVATED R") as "%ran".
    destruct nth_error eqn: E. 2:{ rewrite nth_error_None in E. nia. }
    destruct (nth_error l_tgt) eqn: E0. 2:{ rewrite nth_error_None in E0. nia. }
    destruct o.
    - iPoseProof (initialized_until_same with "ACTIVATED") as "%"; et.
      steps_r. steps_l. do 2 force_l. iFrame. iSplit; et. step.
      iSplit; et. iExists [_],[_],_,_. iSplit; et.
      iSplit; et. iSplit; et. iExists _,_. iSplit; ss. iFrame.
    - steps_r. hss. iPoseProof (initialized_until_update_proph with "ACTIVATED") as "[A (%nth & P)]"; et.
      inline_r. steps_r. do 3 force_r.
      instantiate (1 := (_,_, existT _ (_,_,_))). ss. iSplitL "P". { iSplit; ss. iSplit; ss. ss. }
      steps_r. iDestruct "GRT" as "((% & P) & _)". hss. steps_r. steps_l. do 2 force_l.
      iFrame. iSplit; et. step. inv H3. 2:{ exfalso. apply NIN. econs. }
      iSplit; et. iExists [_],[_],_,_. iSplit; et.
      iSplit; et. iSplit; et. iExists _,_. iSplit; ss; iFrame.
      iPureIntro. splits; et. rewrite <- (take_drop (S q) l_src).
      rewrite !app_length. ss. rewrite !take_length. rewrite !drop_length. nia.
  Qed.

  Theorem sim:
    HSim.t SingleCoinAMod SingleCoinPMod SingleCoinA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "A". iExists _,_,[],[]. iSplit.
      { rewrite !app_nil_r. eauto. }
      iSplit; [iSplit|]; eauto. iExists _,_. iSplit; et.
    - eapply simF_new; eauto.
    - eapply simF_read; eauto.
  Qed.

End SIMMODSEM.
End SingleCoinPA. *)
