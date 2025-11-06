(* Require Import Coqlib ITreelib sflib.
Require Import MultiCoinHeader MultiCoinP MultiCoinA MultiCoinASpec SMod ModSim.
Require Import Any Skeleton.
Require Import PCM IPM.
Require Import Events Behavior.
Require Import ProphecyHeader ProphecyA STB.

Require Import ISim HMod PMod Events ITactics.
Require Import Mod ModSimFacts.

Require Import sProp sWorld World SRF.
Require Import Ensembles Streams.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MultiCoinPA.
Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
  Context `{_S: MultiCoinAR.t (Γ:=Γ)}.
  Context `{_M: ProphecyAR.t (Γ:=Γ)}.

  Fixpoint initialized_until (l_tgt : list bool) (l_src: list (Stream bool)) (hi: nat) : iProp :=
    match hi with
    | S hi' =>
        MultiCoinAS.available hi' ∗
        ∃ P nth bs,
        ⌜exists b, nth_error l_tgt hi' = Some b /\ nth_error l_src hi' = Some (Cons b (Str_nth_tl nth bs)) /\ (MultiCoinPrT.t).(ProphecyT.wf) nth P⌝
        ∗ ProphecyAS.has_proph ("MultiCoin", hi'↑↑) (existT MultiCoinPrT.t (P, bs, nth))
        ∗ initialized_until l_tgt l_src hi'
    | O => emp%I
    end.

  Lemma free_from_split i:
    MultiCoinAS.free_from i -∗ MultiCoinAS.free_from (S i) ∗ (ProphecyAS.free_id (MultiCoinP.proph_coins i)).
  Proof.
    iIntros "H". unfold MultiCoinAS.free_from, ProphecyAS.free_id.
    replace (MultiCoinAS.free_from_r i) with (MultiCoinAS.free_from_r (S i) ⋅ ProphecyAS.free_id_r (MultiCoinP.proph_coins i)).
    { iDestruct "H" as "($ & $)". }
    unfold MultiCoinAS.free_from_r, ProphecyAS.free_id_r. ur. unfold Auth.white. f_equal.
    unfold MultiCoinAS.MultiCoinFree_r. ur. extensionalities.
    unfold MultiCoinP.proph_coins. des_ifs; try solve [ur; des_ifs]; try nia.
    - rewrite SAny.upcast_downcast in Heq. clarify. nia.
    - rewrite SAny.upcast_downcast in Heq. clarify.
    - exfalso. apply n1. f_equal. apply SAny.downcast_upcast. rewrite Heq. f_equal.
      nia.
    - rewrite SAny.upcast_downcast in Heq. clarify.
  Qed.

  Lemma uninitialized_from_split i:
    MultiCoinAS.uninitialized_from i -∗ MultiCoinAS.uninitialized_from (S i) ∗ (MultiCoinAS.uninitialized i).
  Proof.
    iIntros "H". unfold MultiCoinAS.uninitialized_from, MultiCoinAS.uninitialized.
    replace (MultiCoinAS.uninitialized_from_r i) with (MultiCoinAS.uninitialized_from_r (S i) ⋅ MultiCoinAS.uninitialized_r i).
    { iDestruct "H" as "($ & $)". }
    unfold MultiCoinAS.uninitialized_from_r, MultiCoinAS.uninitialized_r. ur.
    extensionalities. des_ifs; try nia; try solve [ur; des_ifs].
  Qed.

  Lemma update_to_available l :
    MultiCoinAS.uninitialized l ==∗ MultiCoinAS.available l.
  Proof.
    iIntros "H". unfold MultiCoinAS.uninitialized, MultiCoinAS.available.
    iPoseProof (OwnM_Upd with "H") as "D"; et. ii. ur. ur in H2. i.
    specialize (H2 k). unfold MultiCoinAS.uninitialized_r, MultiCoinAS.available_r in *.
    destruct dec; clarify. ur in H2. ur. des_ifs.
  Qed.

  Lemma available_dup l :
    MultiCoinAS.available l -∗ MultiCoinAS.available l ∗ MultiCoinAS.available l.
  Proof.
    iIntros "H". unfold MultiCoinAS.available. set MultiCoinAS.available_r at 1.
    replace (c l) with (MultiCoinAS.available_r l ⋅ MultiCoinAS.available_r l).
    { iDestruct "H" as "($ & $)". }
    unfold c. extensionalities. ur. unfold MultiCoinAS.available_r. des_ifs; ur; des_ifs.
  Qed.

  Lemma uninitialized_from_update i:
    MultiCoinAS.uninitialized_from i ==∗ MultiCoinAS.uninitialized_from (S i) ∗ (MultiCoinAS.available i).
  Proof.
    iIntros "H". iPoseProof (uninitialized_from_split with "H") as "(H0 & H1)".
    iPoseProof (update_to_available with "H1") as "> H1". iModIntro. iFrame.
  Qed.

  Lemma initialized_until_available l l0 i:
    initialized_until l l0 (S i) -∗ initialized_until l l0 (S i) ∗ MultiCoinAS.available i.
  Proof.
    iIntros "H". ss. unfold MultiCoinAS.available. set (MultiCoinAS.available_r i) at 1.
    replace c with ((MultiCoinAS.available_r i) ⋅ (MultiCoinAS.available_r i)).
    { iDestruct "H" as "(($ & $) & $)". }
    unfold c, MultiCoinAS.available_r. ur. extensionalities. des_ifs; ur; des_ifs.
  Qed.

  Lemma _initialized_update l_tgt l_src i b bs (EQ : List.length l_tgt = List.length l_src) (LE : i ≤ List.length l_src):
    initialized_until l_tgt l_src i
      -∗ MultiCoinAS.uninitialized_from i
      -∗ ProphecyAS.has_proph (MultiCoinP.proph_coins i) (existT MultiCoinPrT.t (Full_set (Stream bool), bs, 0))
      ==∗ initialized_until (firstn i l_tgt ++ [b] ++ skipn (S i) l_tgt) (firstn i l_src ++ [Cons b bs] ++ skipn (S i) l_src) (S i) ∗ MultiCoinAS.uninitialized_from (S i).
  Proof.
    iIntros "H0 H1 H2". ss. iPoseProof (uninitialized_from_update with "H1") as ">[? ?]".
    iModIntro. iFrame. iExists _,_,_. iFrame. iSplit.
    - iPureIntro. exists b. splits.
      + rewrite nth_error_app2. 2:{ rewrite take_length. nia. }
        rewrite take_length. replace (i - _) with 0 by nia. ss.
      + rewrite nth_error_app2. 2:{ rewrite take_length. nia. }
        rewrite take_length. replace (i - _) with 0 by nia. ss.
      + exists []. split; ss.
    - set i at 1 6. assert (LE0 : n ≤ i) by nia. clearbody n.
      iInduction n as [|n'] "IH" forall (LE0); ss.
      iDestruct "H0" as "($ & H0)".
      iDestruct "H0" as "(%P & %nth & %bs0 & %PURE & P & I)". des.
      iExists _,_,_. iFrame.
      iSplitR "I". 2:{ iApply "IH"; et. iPureIntro. nia. }
      iPureIntro. exists b0. rewrite <- (take_drop i l_tgt) in PURE.
      rewrite <- (take_drop i l_src) in PURE0.
      rewrite nth_error_app1 in PURE. 2:{ rewrite take_length. nia. }
      rewrite nth_error_app1 in PURE0. 2:{ rewrite take_length. nia. }
      splits.
      + rewrite nth_error_app1; et. rewrite take_length. nia.
      + rewrite nth_error_app1; et. rewrite take_length. nia.
      + eexists. split; ss. et.
  Qed.

  Lemma initialized_update l_tgt l_src b bs (EQ : List.length l_tgt = List.length l_src) :
    initialized_until l_tgt l_src (List.length l_src)
      -∗ MultiCoinAS.uninitialized_from (List.length l_src)
      -∗ ProphecyAS.has_proph (MultiCoinP.proph_coins (List.length l_src)) (existT MultiCoinPrT.t (Full_set (Stream bool), bs, 0))
      ==∗ initialized_until (l_tgt ++ [b]) (l_src ++ [Cons b bs]) (S (List.length l_src)) ∗ MultiCoinAS.uninitialized_from (S (List.length l_src)).
  Proof.
    eassert (l_tgt ++ [b] = _); cycle 1.
    eassert (l_src ++ [Cons b bs] = _); cycle 1. rewrite H2. rewrite H3.
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
       MultiCoinAS.uninitialized_from i -∗ MultiCoinAS.available j -∗ ⌜j < i⌝.
  Proof.
    iIntros "A B". unfold MultiCoinAS.uninitialized_from, MultiCoinAS.available.
    unfold MultiCoinAS.uninitialized_from_r, MultiCoinAS.available_r.
    destruct (le_dec i j). 2:{ iPureIntro. nia. }
    iCombine "A B" as "C". iOwnWf "C" as wfc. exfalso.
    ur in wfc. specialize (wfc j). des_ifs; try nia. ur in wfc. et.
  Qed.

  Lemma initialized_same i j s b l_src l_tgt (RAN: i < j)
    (E : nth_error l_src i = Some s) (E0 : nth_error l_tgt i = Some b) :
  initialized_until l_tgt l_src j -∗ ⌜hd s = b⌝.
  Proof.
    iIntros "A". iInduction j as [|j] "IH" forall (RAN); i; ss; try nia.
    iDestruct "A" as "(A & B)".
    iDestruct "B" as "(%P & %nth & %bs & %PURE & P & I)".
    destruct (dec i j); clarify. 2:{ iApply "IH"; et. iPureIntro. nia. }
    des. rewrite E0 in PURE. rewrite E in PURE0. clarify.
  Qed.

  Lemma initialized_until_same j l_tgt l_src l_tgt' l_src'
   (EQ : ∀ i : nat, i < j → nth_error l_tgt i = nth_error l_tgt' i)
   (EQ0 : ∀ i : nat, i < j → nth_error l_src i = nth_error l_src' i) :
  initialized_until l_tgt l_src j -∗ initialized_until l_tgt' l_src' j.
  Proof.
    iInduction j as [|j] "IH" forall (EQ EQ0); et.
    ss. iIntros "($ & I)".
    iDestruct "I" as "(%P & %nth & %bs & %PURE & P & I)".
    iExists _,_,_. iFrame. iSplitR "I". 2:{ iApply "IH"; et. }
    iPureIntro. des. esplits; et.
    { instantiate (1 := b). rewrite <- EQ; et. }
    { rewrite <- EQ0; et. }
  Qed.

  Lemma initialized_until_update_proph i j l_src l_tgt (LE: j ≤ List.length l_tgt)
    (LE0: j ≤ List.length l_src) (ran : i < j) :
    initialized_until l_tgt l_src j
    ⊢ (∃ P nth bs,
      ⌜exists b, nth_error l_tgt i = Some b /\ nth_error l_src i = Some (Cons b (Str_nth_tl nth bs)) /\ (MultiCoinPrT.t).(ProphecyT.wf) nth P⌝
      ∗ ProphecyAS.has_proph ("MultiCoin", i↑↑) (existT MultiCoinPrT.t (P, bs, nth))
      ∗ (∀ b', (⌜Str_nth nth bs = b'⌝ ∗ ProphecyAS.has_proph ("MultiCoin", i↑↑) (existT MultiCoinPrT.t ((MultiCoinPrT.t).(ProphecyT.resolve) nth b' P, bs, S nth))) -∗ initialized_until (take i l_tgt ++ b' :: drop (S i) l_tgt) (take i l_src ++ (Cons b' (Str_nth_tl (S nth) bs)) :: drop (S i) l_src) j))%I.
  Proof.
    iInduction j as [|j] "IH" forall (LE LE0 ran); try nia.
    iIntros "A". destruct (dec i j); clarify; cycle 1. 
    - ss. iDestruct "A" as "(A & B)".
      iDestruct "B" as "(%P & %nth & %bs & %PURE & P & I)".
      assert (A1: j ≤ List.length l_tgt) by nia.
      assert (A2: j ≤ List.length l_src) by nia.
      assert (A3: i < j) by nia.
      iPoseProof ("IH" $! A1 A2 A3 with "I") as "I".
      iDestruct "I" as "(%P0 & %nth0 & %bs0 & %IPURE & P0 & I0)".
      iExists _,_,_. iFrame. iSplit; ss. iIntros "%x (% & D)".
      iPoseProof ("I0" with "[$D]") as "I0"; et. iExists _,_,_. iFrame.
      des. iPureIntro. esplits. 4: apply PURE2. 3: et.
      + instantiate (1 := b0).
        replace (take i l_tgt ++ x :: drop (S i) l_tgt) with ((take i l_tgt ++ [x]) ++ drop (S i) l_tgt). 2:{ rewrite <- app_assoc. et. }
        rewrite nth_error_app2. 2:{ rewrite app_length. rewrite take_length. ss. nia. }
        rewrite app_length. rewrite take_length.
        rewrite <- (take_drop (S i) l_tgt) in PURE.
        rewrite nth_error_app2 in PURE. 2:{ rewrite take_length. nia. }
        rewrite take_length in PURE. simpl. rewrite <- PURE. f_equal. nia.
      + set (Cons _ _).
        replace (take i l_src ++ s :: drop (S i) l_src) with ((take i l_src ++ [s]) ++ drop (S i) l_src). 2:{ rewrite <- app_assoc. et. }
        rewrite nth_error_app2. 2:{ rewrite app_length. rewrite take_length. ss. nia. }
        rewrite app_length. rewrite take_length.
        rewrite <- (take_drop (S i) l_src) in PURE0.
        rewrite nth_error_app2 in PURE0. 2:{ rewrite take_length. nia. }
        rewrite take_length in PURE0. simpl. rewrite <- PURE0. f_equal. nia.
    -  ss. iDestruct "A" as "(A & B)".
      iDestruct "B" as "(%P & %nth & %bs & %PURE & P & I)".
      iExists _,_,_. iFrame. iSplit; et. iIntros "%x (% & P)".
      iExists _,_,_. iFrame. iSplit.
      + iPureIntro. des. exists x. splits.
        { rewrite nth_error_app2. 2:{ rewrite take_length. nia. }
          rewrite take_length. replace (j - _) with 0 by nia. ss. }
        { rewrite nth_error_app2. 2:{ rewrite take_length. nia. }
          rewrite take_length. replace (j - _) with 0 by nia. ss. }
        exists (bs_pre ++ [x]). rewrite app_length. ss. split; try nia. i.
        red. split.
        { rewrite <- MultiCoinPrT.app_prelist_app. et. }
        apply MultiCoinPrT.Str_nth_prelist_app. rewrite nth_error_app2; try nia.
        replace (_ - _) with 0 by nia. ss.
      + iClear "IH". iApply initialized_until_same. 3:et.
        * i. set l_tgt at 1. rewrite <- (take_drop j l).
          unfold l. rewrite !nth_error_app1; et.
          all: try solve [rewrite take_length; nia].
        * i. set l_src at 1. rewrite <- (take_drop j l).
          unfold l. rewrite !nth_error_app1; et.
          all: try solve [rewrite take_length; nia].
  Qed.

  Definition Ist: Sk.t -> nat -> alist key Any.t -> alist key Any.t -> iProp :=
    (fun _ _ st_src st_tgt =>
      ∃ l_tgt l_src,
      ⌜st_tgt = [(MultiCoinP.v_coins, (l_tgt : list bool)↑)] /\
       st_src = [(MultiCoinA.v_coins, (l_src : list (Stream bool))↑)] /\
       List.length l_tgt = List.length l_src⌝ ∗
      initialized_until l_tgt l_src (List.length l_src) ∗
      MultiCoinAS.free_from (List.length l_src) ∗ MultiCoinAS.uninitialized_from (List.length l_src))%I.

  Variable ginv: Sk.t -> invspec.
  Variable StbProph: Sk.t -> gname -> option fspec.
  Variable StbMultiCoin: Sk.t -> gname -> option fspec.

  Local Notation ProphecyA := (ProphecyA.t ginv StbProph).
  Local Notation MultiCoinA := (MultiCoinA.t ginv StbMultiCoin).
  Local Notation MultiCoinAMod := (MultiCoinA ★ ProphecyA).
  Local Notation MultiCoinPMod := (MultiCoinP.t ★ ProphecyA).
  Local Notation IstFull := (IstProd (IstSB MultiCoinA Ist) IstEq).

  (**********)

  Lemma simF_new:
    HSim.sim_fun MultiCoinAMod MultiCoinPMod IstFull MultiCoinName.new.
  Proof.
    init_simF. unfold IstFull, IstProd0.
    iDestruct "IST" as "(%st_srcL & %st_tgtL & %st_srcR & %st_tgtR & (#-> & #->) & IST)".
    iDestruct "IST" as "((% & IST) & #->)". unfold Ist. rename H2 into INCL.
    iDestruct "IST" as "(%l_tgt & %l_src & (#-> & #-> & %LEN) & (ACTIVATED & FREE & UNACTIVATED))".
    steps_l. hss. rename q2 into l_src. iDestruct "ASM" as "(_ & #<-)". hss.
    steps_r. hss. steps_r. rename q into b.
    inline_r. steps_r. do 3 force_r.
    instantiate (1 := (_, MultiCoinPrT.t)). ss.
    iPoseProof (free_from_split with "FREE") as "[FREE ARG]". iSplitL "ARG".
    { iSplit; ss. iSplit; ss. rewrite LEN. et. }
    steps_r. iDestruct "GRT" as "((%bs & #-> & P) & _)". hss. steps_r.
    hss. force_l. instantiate (1:= Cons b bs). steps_l. hss. 
    iEval (rewrite LEN) in "P".
    iPoseProof (initialized_update with "ACTIVATED") as "D"; et.
    iPoseProof ("D" with "UNACTIVATED") as "D".
    iPoseProof ("D" with "P") as "D". iApply isim_upd. iMod "D" as "[ACTIVATED UNACTIVATED]".
    iModIntro. Local Opaque initialized_until.
    do 2 force_l.
    iPoseProof (initialized_until_available with "ACTIVATED") as "[ACTIVATED POST]".
    iSplitL "POST". { iSplit; ss. et. }
    step. iSplit; et. iExists [_],[_],_,_. iSplit; et.
    iSplit; et. iSplit; et. iExists _,_. iSplit; ss.
    { iPureIntro. splits; et. rewrite !app_length. ss. nia. }
    rewrite app_length. ss. rewrite plus_comm. ss. iFrame.
  Qed.

  Lemma simF_read:
    HSim.sim_fun MultiCoinAMod MultiCoinPMod IstFull MultiCoinName.read.
  Proof.
    init_simF. unfold IstFull, IstProd0.
    iDestruct "IST" as "(%st_srcL & %st_tgtL & %st_srcR & %st_tgtR & (#-> & #->) & IST)".
    iDestruct "IST" as "((% & IST) & #->)". unfold Ist. rename H2 into INCL.
    iDestruct "IST" as "(%l_tgt & %l_src & (#-> & #-> & %LEN) & (ACTIVATED & FREE & UNACTIVATED))".
    steps_l. hss. rename q2 into l_src. iDestruct "ASM" as "((% & R) & %)". hss.
    steps_r. hss. steps_r. iPoseProof (uninitialized_readable_disjoint with "UNACTIVATED R") as "%ran".
    destruct nth_error eqn: E. 2:{ rewrite nth_error_None in E. nia. }
    destruct (nth_error l_tgt) eqn: E0. 2:{ rewrite nth_error_None in E0. nia. }
    iPoseProof (initialized_same with "ACTIVATED") as "%"; et. clarify.
    steps_r. steps_l. do 2 force_l. iPoseProof (available_dup with "R") as "($ & R)".
    iSplit; ss. step. iSplit; et. iExists [_],[_],_,_. iSplit; et.
    iSplit; et. iSplit; et. iExists _,_. iSplit; ss; iFrame.
  Qed.

  Lemma simF_toss:
    HSim.sim_fun MultiCoinAMod MultiCoinPMod IstFull MultiCoinName.toss.
  Proof.
    init_simF. unfold IstFull, IstProd0.
    iDestruct "IST" as "(%st_srcL & %st_tgtL & %st_srcR & %st_tgtR & (#-> & #->) & IST)".
    iDestruct "IST" as "((% & IST) & #->)". unfold Ist. rename H2 into INCL.
    iDestruct "IST" as "(%l_tgt & %l_src & (#-> & #-> & %LEN) & (ACTIVATED & FREE & UNACTIVATED))".
    steps_l. hss. rename q2 into l_src. iDestruct "ASM" as "((% & R) & %)". hss.
    steps_r. hss. steps_r. iPoseProof (uninitialized_readable_disjoint with "UNACTIVATED R") as "%ran".
    destruct nth_error eqn: E. 2:{ rewrite nth_error_None in E. nia. }
    destruct (nth_error l_tgt) eqn: E0. 2:{ rewrite nth_error_None in E0. nia. }
    iPoseProof (initialized_same with "ACTIVATED") as "%"; et. clarify.
    iPoseProof (initialized_until_update_proph with "ACTIVATED") as "P"; try nia; et.
    iDestruct "P" as "(%P & %nth & %bs & %PURE & P & I)".
    steps_r. inline_r. steps_r. do 3 force_r. instantiate (1 := (_,_,existT _ (_,_,_))).
    ss. iSplitL "P". { iSplit; ss. iSplit; ss. ss. }
    steps_r. iDestruct "GRT" as "((% & P) & _)". hss. steps_r. steps_l.
    iPoseProof ("I" with "[$P]") as "I". { iPureIntro. inv H3. et. }
    do 2 force_l. iPoseProof (available_dup with "R") as "($ & R)". iSplit; ss.
    step. iSplit; et. iExists [_],[_],_,_. iSplit; et.
    iSplit; et. iSplit; et. iExists _,_. iSplit.
    { iPureIntro. splits; et. rewrite !app_length. ss. rewrite !take_length. rewrite !drop_length. nia. }
    replace (List.length (_ ++ _)) with (List.length l_src).
    2:{ splits; et. rewrite !app_length. ss. rewrite !take_length. rewrite !drop_length. nia. }
    iFrame. eassert (tl s = _). 2:{ rewrite H2. et. }
    rewrite <- H4. ss. inv H3. set (List.length bs_pre). clearbody n.
    clear. revert bs. induction n; ss. { unfold Str_nth. ss. destruct bs; ss. }
    i. apply IHn.
  Qed.

  Theorem sim:
    HSim.t MultiCoinAMod MultiCoinPMod MultiCoinA.InitCond IstFull.
  Proof.
    init_sim.
    - iIntros "A". iExists _,_,[],[]. iSplit.
      { rewrite !app_nil_r. eauto. }
      iSplit; [iSplit|]; eauto. iExists _,_. iSplit; et.
    - eapply simF_new; eauto.
    - eapply simF_read; eauto.
    - eapply simF_toss; eauto.
  Qed.

End SIMMODSEM.
End MultiCoinPA. *)
