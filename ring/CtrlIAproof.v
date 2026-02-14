Require Import CRIS.
Require Import ImpPrelude.
Require Import CellHeader CellA RingHeader RingA CtrlI.

Lemma mod_addL_app `{Σ : GRA} l l' : Mod.addL (l ++ l') = (Mod.addL l) ★ (Mod.addL l').
Proof using.
  induction l; s.
  - rewrite -mod_add_empty_l. eauto.
  - rewrite mod_add_assoc. rewrite IHl. eauto.
Qed.

(* Simulation Proof *)
Module CtrlIA. Section CtrlIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.

  Variable max_size : nat.

  Context (spt sps : specmap).

  (* Definitions of a list of Cell modules *)
  Local Definition CellA := (λ idx, CellA.t idx spt).
  Definition CellG start len : Mod.t := Mod.addL (List.map CellA (seq start len)).
  Definition CellGS := (CellG 0 max_size).

  (* Definitions of RingA module and RingI module *)
  Local Definition RingA := (RingA.t max_size sps).
  Local Definition CtrlI := (CtrlI.t max_size).
  Local Definition RingAMod := (RingA ★ CellGS).
  Local Definition RingIMod := (CtrlI ★ CellGS).

  (* Splits a cell group [CellG] ranging from [start] to [start+len-1] into three parts around an index [idx].
     Isolates a single cell [CellA idx] from other cells *)
  Lemma cellgroup_split idx start len (RANGE : start <= idx < start + len):
    CellG start len =
      (CellG start (idx-start)) ★ (CellA idx) ★
        (CellG (S idx) (start + len - idx - 1)).
  Proof.
    unfold CellG.
    assert (EQ : seq start len =
                seq start (idx-start) ++ seq idx (S (start + len - idx - 1))).
    { etrans; [|etrans]; cycle 1.
      - apply (seq_app (idx-start) (start + len - idx) start).
      - f_equal. f_equal; nia.
      - f_equal. nia.
    }
    rewrite EQ map_app mod_addL_app. eauto.
  Qed.

  Lemma big_sepL_mod {T} (φ : nat -> T -> iProp Σ) (l : list T):
     ([∗ list] i↦x ∈ l, φ (i mod List.length l) x) -∗
     ([∗ list] i↦x ∈ l, φ i x).
  Proof.
    iIntros "H". iApply (big_sepL_impl with "H").
    iModIntro. iIntros (? ?) "% H".
    eapply eq_ind; try iAssumption. f_equal.
    destruct (lookup_lt_is_Some l k).
    eauto using Nat.mod_small.
  Qed.

  Lemma mod_add_ex (a b c : nat)
    (NEQ : c ≠ 0)
    (EX : exists x, a = b + x * c):
    a mod c = b mod c.
  Proof. destruct EX. subst. eapply Nat.Div0.mod_add; eauto. Qed.

  Lemma big_sepL_rotate {T} (φ : nat -> T -> iProp Σ) n (l : list T):
    ([∗ list] i↦x ∈ l, φ ((n+i) mod List.length l) x) -∗
    ([∗ list] i↦x ∈ rotate (List.length l - n mod List.length l) l, φ i x).
  Proof.
    destruct (Nat.eq_decidable (List.length l) 0) as [|LENL].
    { destruct l; ss; iIntros "H"; iFrame. }
    iIntros "H". iApply big_sepL_mod. rewrite length_rotate.

    destruct (Nat.eq_decidable (n mod List.length l) 0) as [|LENN].
    { rewrite H Nat.sub_0_r.
      unfold rotate. rewrite Nat.Div0.mod_same; eauto.
      rewrite drop_0 take_0 app_nil_r.
      eapply eq_ind; try iAssumption. f_equal. extensionalities. f_equal.
      rewrite Nat.Div0.add_mod; eauto. rewrite H Nat.Div0.mod_mod; eauto.
    }
    assert (LE:= Nat.mod_upper_bound n _ LENL).

    iApply big_sepL_app. rewrite length_drop.
    rewrite Nat.mod_small; try nia.
    iPoseProof ((big_sepL_take_drop _ l (List.length l - n mod List.length l)) with "H") as "[H1 H2]".
    iSplitL "H2";
      (eapply eq_ind; try iAssumption; f_equal; extensionalities; f_equal).
    - eapply mod_add_ex; eauto.
      rewrite {1}(Nat.div_mod_eq n (List.length l)).
      exists (S (n / List.length l)). nia.
    - eapply mod_add_ex; eauto.
      rewrite {1}(Nat.div_mod_eq n (List.length l)).
      exists (n / List.length l). nia.
  Qed.

  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
     ∃ (q q' : list Z) (hd tl : nat),
       ⌜st_src = {[RingA.v_que := Some q↑]} ∧
       st_tgt = {[CtrlI.v_hd := Some hd↑; CtrlI.v_tl := Some tl↑]} /\
       hd = (tl + List.length q)%nat /\ List.length (q ++ q') = max_size⌝ ∗
       ([∗ list] i↦x ∈ q, CellA.cell ((tl+i) mod max_size) x) ∗
       ([∗ list] i↦x ∈ q', (CellA.pending ((hd+i) mod max_size) ∨ CellA.cell ((hd+i) mod max_size) x)))%I.

  Notation IstFull := (IstProd (IstSB (RingA.t max_size sps).(Mod.scopes) Ist) IstEq).

  Lemma simF_init : ISim.sim_fun open RingAMod RingIMod IstFull (Some RingHdr.init).
  Proof using.
    iStartSim.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. destruct Any.downcast; last (steps_l; case_match; steps_l; ss).
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    (* TGT, SRC: take steps *)
    steps_r. steps_l. step. iSplitL "". { eauto. }

    (* Prove the IST *)
    iExists _, _, st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    iExists [], (rotate (max_size - tl mod max_size) (q++q')%list), 0, 0.
    iSplit.
    { iPureIntro. esplits; eauto. s. rewrite length_rotate. eauto. }

    iSplit; eauto. rewrite -H4.
    iApply big_sepL_rotate. iApply big_sepL_app.
    iSplitL "LIVE".
    + iApply (big_sepL_impl with "LIVE").
      iModIntro. iIntros (k x) "% LIVE". iRight. s.
      rewrite Nat.Div0.mod_mod; eauto.
    + iApply (big_sepL_impl with "FREE").
      iModIntro. iIntros (k x) "% FREE". s.
      rewrite Nat.add_assoc.
      rewrite Nat.Div0.mod_mod; eauto.
  (*SLOW*)Qed.

  Lemma simF_get_size : ISim.sim_fun open RingAMod RingIMod IstFull (Some RingHdr.get_size).
  Proof using.
    iStartSim.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. destruct Any.downcast; last (steps_l; case_match; steps_l; ss).
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst. hss.

    (* TGT, SRC: take steps *)
    steps_r. steps_l. step. iSplitL "". { rewrite Nat.add_comm Nat.add_sub. eauto. }

    (* Prove the IST *)
    iExists _, _, st_tgtR, st_tgtR.
    repeat iSplit; eauto.
    repeat iExists _. iFrame. eauto.
  (*SLOW*)Qed.

  Lemma simF_enqueue : ISim.sim_fun open RingAMod RingIMod IstFull (Some RingHdr.enqueue).
  Proof using.
    unfold RingAMod, RingIMod, CellGS.
    iStartSim.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. destruct Any.downcast; last (steps_l; case_match; steps_l; ss).
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst.
    steps_l.
    rename q into v. rename q' into l.

    (* TGT: check the length of the queue *)
    steps_r. rewrite Nat.add_sub'; des_ifs; cycle 1.
    { step. ss. }

    (* SRC: take steps *)
    steps_l.

    apply Nat.ltb_lt in Heq. rewrite length_app in H4.
    assert (UBND:= Nat.mod_upper_bound (tl + List.length v) max_size).
    revert WFS WFT.
    rewrite (@cellgroup_split ((tl+ List.length v) mod max_size)); try nia.
    i; move_aux.

    (* TGT: inline CellHdr.set *)
    steps_r. inline_r.
    destruct l; [ss; nia|].
    force_r (_,_). forces_r.
    iDestruct "FREE" as "(Q & FREE)".
    (* rewrite !Nat.add_0_l in NODUPFS NODUPFT WFS WFT. *)
    rewrite !Nat.add_0_r.
    iSplitL "Q".
    { iFrame. eauto. }

    (* TGT: take steps using GRT from set_spec *)
    steps_r. iDestruct "GRT" as "(% & % & CELL)". subst.
    steps_r. step.
    iSplitL ""; eauto.

    (* Prove the IST *)
    iExists _, _, st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    iExists (v++[z]), l, ((tl + List.length v)+1), tl.
    iSplitL "".
    { iPureIntro. esplits; eauto.
      - rewrite length_app. s. nia.
      - rewrite !length_app. s. hss. nia.
    }
    iSplitL "LIVE CELL".
    + iApply big_sepL_app. iFrame. s. rewrite Nat.add_0_r. eauto.
    + iApply (big_sepL_impl with "FREE").
      iModIntro. iIntros (k x FIND) "H".
      rewrite <-!Nat.add_assoc. eauto.
  (*SLOW*)Qed.

  Lemma simF_dequeue : ISim.sim_fun open RingAMod RingIMod IstFull (Some RingHdr.dequeue).
  Proof using.
    unfold RingAMod, RingIMod, CellGS.
    iStartSim.

    (* Simulation Starts Here *)
    (* SRC: precondition *)
    steps_l. destruct Any.downcast; last (steps_l; case_match; steps_l; ss).
    steps_l; steps_r.
    iDestruct "IST" as (? ? ? ?) "(% & (% & IST) & %)". des; subst.
    iDestruct "IST" as (? ? ? ?) "(% & LIVE & FREE)". des; subst.

    (* TGT: check the length of the queue *)
    steps_l. steps_r.
    destruct q; ss.
    { rewrite Nat.add_0_r Nat.sub_diag. s. step. ss. }
    replace (tl + S(List.length q) - tl) with (S(List.length q)) by nia. s.
    rewrite !length_app in H4.

    (* SRC: take steps *)
    steps_l.
    assert (UBND:= Nat.mod_upper_bound tl max_size).
    revert WFS WFT.
    rewrite (@cellgroup_split (tl mod max_size)); try nia.
    i; move_aux.

    (* TGT: inline CellHdr.get *)
    steps_r. inline_r. forces_r. iDestruct "LIVE" as "(Q & LIVE)".
    rewrite !Nat.add_0_r.
    iSplitL "Q". { iFrame. eauto. }

    (* TGT: take steps using GRT from get_spec *)
    steps_r. iDestruct "GRT" as "(% & % & CELL)". subst. hss.
    steps_r. hss. forces_l. step.
    iSplitL ""; eauto.

    (* Prove the IST *)
    iExists _, _, st_tgtR, st_tgtR.
    do 3 (iSplit; eauto).
    iExists q, (q'++[z]), (tl + S(List.length q)), (S tl).
    iSplit.
    { iPureIntro. esplits; eauto; try nia.
      - repeat f_equal. nia.
      - rewrite !length_app. s. nia.
    }
    iSplitL "LIVE".
    + iApply (big_sepL_impl with "LIVE").
      iModIntro. iIntros (k x FIND) "H".
      rewrite Nat.add_succ_r. eauto.
    + iApply big_sepL_app. iFrame. s. iSplitR ""; eauto.
      iRight. erewrite <-mod_add_ex; eauto; try nia.
      exists 1. nia.
  (*SLOW*)Qed.

  Theorem sim : ISim.t open RingAMod RingIMod (RingA.init_cond max_size) IstFull.
  Proof using.
    init_sim.
    - eapply simF_init; eauto.
    - eapply simF_get_size; eauto.
    - eapply simF_enqueue; eauto.
    - eapply simF_dequeue; eauto.
    - iIntros "R".
      repeat iExists _; repeat iSplit; eauto.
      iExists [], (replicate max_size 0%Z), 0, 0.
      iSplitR. { iPureIntro. esplits; s; eauto; rewrite length_replicate //. }
      s. iSplitR; eauto.
      iApply (big_sepL_impl with "R").
      iModIntro. iIntros (? ? FIND) "P".
      iLeft. rewrite Nat.mod_small; eauto.
      eapply lookup_replicate_1. eauto.
  (*SLOW*)Qed.
End CtrlIA. End CtrlIA.
