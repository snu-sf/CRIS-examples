From CRIS Require Import CRIS.

Require Import ImpPrelude MemHdr MemLib HybridMem DetMem.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.

Local Notation _memRA := (Z -d> optionUR (dfrac_agreeR (optionO (leibnizO val))))%type.
Local Notation memRA := (authUR _memRA)%type.

Section RA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.
  
  Definition mem_wf (m0: Mem.t): Prop :=
    (0 < Mem.next_loc m0)%Z
    ∧ (forall loc v, m0.(Mem.cnts) loc = Some v -> (loc < Mem.next_loc m0)%Z)
  .

  Definition mem_ra_upd (mem: _memRA) loc r : _memRA :=
    fun loc0 =>
      if bool_decide (loc = loc0) then r else mem loc0.

  Variable (mem_r: _memRA) (mem_s mem_t: Mem.t).

  Definition not_allocated loc :=
    mem_r loc = None ∧ Mem.cnts mem_s loc = None ∧ Mem.cnts mem_t loc = None.
  
  Definition alloc_by_spec loc :=
    ∃ v, mem_r loc = Some (to_frac_agree 1 (Some v)) ∧ Mem.cnts mem_s loc = None ∧ Mem.cnts mem_t loc = Some v.

  Definition alloc_by_impl loc :=
    ∃ v, mem_r loc = None ∧ Mem.cnts mem_s loc = Some v ∧ Mem.cnts mem_t loc = Some v.

  Definition _sim_mem : Prop :=
    ∀ loc,
      not_allocated loc ∨ alloc_by_spec loc ∨ alloc_by_impl loc.

  Definition sim_mem : Prop :=
    _sim_mem ∧ (∀ loc (OUT: (loc >= Mem.next_loc mem_t)%Z), not_allocated loc)
             ∧ (∀ loc (OUT: (loc <= 0)%Z), not_allocated loc).

  Lemma mem_ra_alloc_next sz
    (WF: mem_wf mem_t)
    (MEM: _sim_mem)
    :
    mem_own mem_name (● mem_r)
    ⊢ |==>
    mem_own mem_name ((● (mem_r ⋅ _points_to_r (Mem.next_loc mem_t) 1 (repeat Vundef sz))))
    ∗ mem_own mem_name (((◯ _points_to_r (Mem.next_loc mem_t) 1 (repeat Vundef sz)))).
  Proof using _MEM. 
    iIntros "P". rewrite -own_op.
    iApply (own_update with "P"). apply auth_update_alloc.
    apply local_update_discrete. i. rewrite H0.
    split; cycle 1.
    - destruct mz; simpl opM in *.
      + rewrite left_id (comm _ c). et.
      + rewrite left_id. et.
    - rewrite -H0. ii. rewrite !discrete_fun_lookup_op /_points_to_r.
      case_bool_decide as Hcase; s; cycle 1.
      { rewrite right_id. apply H. }
      hexploit (MEM x). destruct WF as [_ WF].
      unfold _sim_mem, not_allocated, alloc_by_spec, alloc_by_impl; i; subst; des; rewrite H1; try des_ifs;
      exploit WF; et. nia.
  Qed.

  Lemma mem_ra_lookup loc nloc q v (sz: Z) mem_t'
    (SIM: sim_mem)
    (MEM: mem_t' = (Mem.alloc mem_t sz).2)
    (NLOC: nloc = Mem.next_loc mem_t)
    (SZ: (0 <= sz)%Z)
    (LOC: (0 <? loc)%Z && (loc <? nloc + sz)%Z = true)
    :
    mem_own mem_name ((● (mem_r ⋅ _points_to_r (Mem.next_loc mem_t) 1 (repeat Vundef (Z.to_nat sz))))) ∗ loc ⤇{q} v
    ⊢
    ⌜∃ v, (mem_r ⋅ _points_to_r (Mem.next_loc mem_t) 1 (repeat Vundef (Z.to_nat sz))) loc ≡ Some (to_frac_agree 1 (Some v)) ∧
     Mem.cnts mem_t' loc = Some v⌝.
  Proof using.
    iIntros "P".
    apply andb_true_iff in LOC as [LOC_POS LOC_RANGE].
    apply Z.ltb_lt in LOC_POS.
    apply Z.ltb_lt in LOC_RANGE.
    unfold _points_to_r.
    rewrite repeat_length !discrete_fun_lookup_op.
    destruct (loc <? nloc)%Z eqn:NL; cycle 1.
    {
      assert (NL0: (nloc <= loc)%Z) by (apply Z.ltb_ge in NL; nia).
      assert (PTS: bool_decide (Mem.next_loc mem_t <= loc < Mem.next_loc mem_t + Z.of_nat (Z.to_nat sz))%Z = true).
      { subst nloc. rewrite Z2Nat.id; [|nia]. apply bool_decide_eq_true_2. nia. }
      assert (POS: bool_decide (0 < loc)%Z = true).
      { apply bool_decide_eq_true_2. exact LOC_POS. }
      assert (OLD: bool_decide (loc < Mem.next_loc mem_t)%Z = false).
      { subst nloc. apply bool_decide_eq_false_2. nia. }
      assert (NEW: bool_decide (loc < Mem.next_loc mem_t + sz)%Z = true).
      { subst nloc. apply bool_decide_eq_true_2. nia. }
      subst mem_t'. rewrite /Mem.alloc /= /Mem.update_cnts POS OLD NEW.

      destruct SIM as [_ [NEXT _]].
      specialize (NEXT loc (ltac:(nia))).
      destruct NEXT as [Hnone [_ _]].
      iPureIntro. exists Vundef.
      rewrite Hnone.
      rewrite PTS nth_error_repeat; [|apply Z2Nat.inj_lt; nia].
      split; [rewrite left_id; reflexivity|reflexivity].
    }

    assert (NL0: (loc < nloc)%Z) by (apply Z.ltb_lt in NL; nia).
    rewrite -own_op.
    iPoseProof (own_valid with "P") as "%WF".
    dup WF. rewrite auth_both_valid_discrete in WF. ss; des.
    unfold included in *. des. specialize (WF loc).
    rewrite !discrete_fun_lookup_op in WF.
    assert (PTS: bool_decide (Mem.next_loc mem_t <= loc < Mem.next_loc mem_t + Z.of_nat (Z.to_nat sz))%Z = false).
    { subst nloc. rewrite Z2Nat.id; [|nia]. apply bool_decide_eq_false_2. nia. }
    rewrite PTS right_id in WF.
    rewrite ->!discrete_fun_lookup_singleton in *.
    destruct SIM as [SIM _].
    specialize (SIM loc). des; cycle 2.
    {
      exfalso. unfold alloc_by_impl in SIM. des.
      rewrite SIM in WF. destruct (z loc); inv WF.
    }
    {
      exfalso. unfold not_allocated in SIM. des.
      rewrite SIM in WF. destruct (z loc); inv WF.
    }

    unfold alloc_by_spec in SIM. des.
    iPureIntro. exists v0.
    rewrite PTS right_id SIM. split; [reflexivity|].
    subst mem_t' nloc. rewrite /Mem.alloc /= /Mem.update_cnts.
    assert (POS: bool_decide (0 < loc)%Z = true).
    { apply bool_decide_eq_true_2. exact LOC_POS. }
    assert (OLD: bool_decide (loc < Mem.next_loc mem_t)%Z = true).
    { apply bool_decide_eq_true_2. nia. }
    rewrite POS OLD. exact SIM1.
  Qed.
    

  Lemma mem_ra_lookup_point loc q v
    (SIM: _sim_mem)
    :
    mem_own mem_name ((● mem_r)) ∗ loc ⤇{q} v
    ⊢
    ⌜mem_r loc ≡ Some (to_frac_agree 1 (Some v)) ∧ (Mem.cnts mem_t) loc = Some v⌝.
  Proof using.
    iIntros "P". rewrite -own_op.
    iPoseProof (own_valid with "P") as "%WF".
    dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
    unfold included in *. des. specialize (WF loc). iris_tac.
    rewrite ->!discrete_fun_lookup_singleton in *.
    destruct (SIM loc); unfold not_allocated, alloc_by_spec, alloc_by_impl in *; des; rewrite H in WF; swap 2 3.
    { destruct (z loc); ss; rewrite -?Some_op ?right_id in WF; inv WF. }
    { destruct (z loc); ss; rewrite -?Some_op ?right_id in WF; inv WF. }

    rewrite -WF. destruct (z loc); rr in WF; depdes WF.
    - assert (EXT: to_frac_agree q (Some v) ≼ to_frac_agree 1 (Some v0)) by (rewrite H2; et).
      eapply dfrac_agree_included in EXT. des; subst. inv EXT0. et.
    - eapply to_frac_agree_inv in H2. ss. des. depdes H3. et.
  Qed.

  Lemma mem_ra_lookup_list mem_r' mem_t' sz
    (SIM: sim_mem)
    (MEM: mem_t' = (Mem.alloc mem_t sz).2)
    (WF: mem_wf mem_t)
    (MEMR: mem_r' = (mem_r ⋅ _points_to_r (Mem.next_loc mem_t) 1 (repeat Vundef (Z.to_nat sz))))
    (SZ: (0 <= sz)%Z)
    :
    (mem_own mem_name ((● mem_r')) ∗ [∗ list] i↦v ∈ repeat Vundef (Z.to_nat sz), ((Mem.next_loc mem_t) + i)%Z ⤇ v)%I
    ⊢
    ⌜∀ loc (LOC: (Mem.next_loc mem_t <=? loc)%Z && (loc <? (Mem.next_loc mem_t) + sz)%Z = true), ∃ v, mem_r' loc ≡ Some (to_frac_agree 1 (Some v)) ∧ (Mem.cnts mem_t') loc = Some v⌝.
  Proof using.
    iIntros "[P PTS] %loc %P". rewrite MEMR.
    apply andb_true_iff in P as [LOC0 LOC1].
    apply Z.leb_le in LOC0.
    apply Z.ltb_lt in LOC1.
    iDestruct (big_sepL_lookup_acc _ _ (Z.to_nat (loc - (Mem.next_loc mem_t))) with "PTS") as "[PT _]".
    { eapply lookup_nth_inbounds. rewrite repeat_length. apply Z2Nat.inj_lt; nia. }
    erewrite nth_repeat.
    assert (LOC_EQ: (Mem.next_loc mem_t + Z.to_nat (loc - Mem.next_loc mem_t) = loc)%Z) by nia.
    rewrite LOC_EQ.
    assert (LOC': (0 <? loc)%Z && (loc <? (Mem.next_loc mem_t) + sz)%Z = true).
    {
      apply andb_true_iff. split.
      - apply Z.ltb_lt. destruct WF as [POS _]. nia.
      - apply Z.ltb_lt. exact LOC1.
    }
    iPoseProof (mem_ra_lookup loc (Mem.next_loc mem_t) 1 Vundef sz mem_t' SIM MEM eq_refl SZ LOC' with "[$P $PT]") as "%Hlookup".
    iPureIntro. exact Hlookup.
  Qed.

  Lemma mem_ra_free loc v
    :
    mem_own mem_name ((● mem_r)) ∗ loc ⤇{1} v
    ⊢ |==>
    mem_own mem_name ((● mem_ra_upd mem_r loc None)).
  Proof using _MEM.
    Local Transparent mem_points_to_singleton_r.
    iIntros "[Auth Frag]".
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r auth_update_dealloc //=.
    apply discrete_fun_local_update; intros loc1.
    destruct (dec loc1 loc); subst.
    - rewrite discrete_fun_lookup_singleton /mem_ra_upd.
      case_bool_decide; [|naive_solver].
      apply delete_option_local_update; eauto; apply _.
    - rewrite discrete_fun_lookup_singleton_ne // /mem_ra_upd.
      case_bool_decide; [naive_solver|ss].
  Qed.


  Lemma mem_ra_store v_new v loc
    (SIM: _sim_mem)
    :
    mem_own mem_name ((● mem_r)) ∗ loc ⤇{1} v
    ⊢ |==>
    mem_own mem_name ((● mem_ra_upd mem_r loc (Some (to_frac_agree 1 (Some v_new))))) ∗ loc ⤇{1} v_new.
  Proof using.
    Local Transparent mem_points_to_singleton_r.
    iIntros "[Auth Frag]".
    iPoseProof ((mem_ra_lookup_point _ _ _ SIM) with "[Auth Frag]") as "%Hlu"; [iFrame|].
    destruct Hlu as [Hpt _].
    rewrite -own_op.
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r /= auth_update //.
    apply discrete_fun_local_update; intros loc1.
    destruct (dec loc1 loc); subst.
    - rewrite Hpt ?discrete_fun_lookup_singleton /mem_ra_upd.
      case_bool_decide; [|naive_solver].
      apply option_local_update, exclusive_local_update; ss.
    - rewrite ?discrete_fun_lookup_singleton /mem_ra_upd.
      case_bool_decide; [naive_solver|].
      rewrite ?discrete_fun_lookup_singleton_ne //.
  Qed.

  Lemma mem_ra_cmp p0 q0 v0 p1 q1 v1 succ
    (SIM: _sim_mem)
    (CMP: HybMem.compare_val p0 p1 = Vint succ)
    :
    (mem_own mem_name (● mem_r) ∗ HybMem.val_r p0 q0 v0 ∗ HybMem.val_r p1 q1 v1)
    ⊢
    ⌜Mem.vcmp mem_t p0 p1 = Some (bool_decide (succ = 1))⌝.
  Proof using.
    rewrite /HybMem.val_r.
    iIntros "(B & P1 & P2)".
    destruct p0 as [i0|[b0 ofs0]|];
      destruct p1 as [i1|[b1 ofs1]|]; simpl in CMP; try discriminate.
    - case_bool_decide as POS0; case_bool_decide as POS1.
      + iPoseProof (mem_ra_lookup_point i0 q0 v0 SIM with "[$B $P1]") as "%HP0".
        iPoseProof (mem_ra_lookup_point i1 q1 v1 SIM with "[$B $P2]") as "%HP1".
        destruct HP0 as [_ HP0]. destruct HP1 as [_ HP1].
        iPureIntro.
        assert (VP0: Mem.valid_ptr mem_t i0 = true).
        { rewrite /Mem.valid_ptr HP0. ss. }
        assert (VP1: Mem.valid_ptr mem_t i1 = true).
        { rewrite /Mem.valid_ptr HP1. ss. }
        assert (BPOS0: bool_decide (0 < i0)%Z = true).
        { apply bool_decide_eq_true_2. exact POS0. }
        assert (BPOS1: bool_decide (0 < i1)%Z = true).
        { apply bool_decide_eq_true_2. exact POS1. }
        rewrite /Mem.vcmp.
        rewrite BPOS0 BPOS1.
        rewrite VP0 VP1. ss.
        inv CMP. destruct (bool_decide (i0 = i1)); ss.
      + case_bool_decide as NULL1.
        * iPoseProof (mem_ra_lookup_point i0 q0 v0 SIM with "[$B $P1]") as "%HP0".
          destruct HP0 as [_ HP0].
          iPureIntro.
          assert (VP0: Mem.valid_ptr mem_t i0 = true).
          { rewrite /Mem.valid_ptr HP0. ss. }
          assert (BPOS0: bool_decide (0 < i0)%Z = true).
          { apply bool_decide_eq_true_2. exact POS0. }
          assert (BPOS1: bool_decide (0 < i1)%Z = false).
          { apply bool_decide_eq_false_2. exact POS1. }
          assert (BNULL1: bool_decide (i1 = 0)%Z = true).
          { apply bool_decide_eq_true_2. exact NULL1. }
          rewrite /Mem.vcmp.
          rewrite BPOS0 BPOS1 BNULL1.
          rewrite VP0. ss.
          inv CMP. ss.
        * exfalso.
          discriminate.
      + case_bool_decide as NULL0.
        * iPoseProof (mem_ra_lookup_point i1 q1 v1 SIM with "[$B $P2]") as "%HP1".
          destruct HP1 as [_ HP1].
          iPureIntro.
          assert (VP1: Mem.valid_ptr mem_t i1 = true).
          { rewrite /Mem.valid_ptr HP1. ss. }
          assert (BPOS0: bool_decide (0 < i0)%Z = false).
          { apply bool_decide_eq_false_2. exact POS0. }
          assert (BPOS1: bool_decide (0 < i1)%Z = true).
          { apply bool_decide_eq_true_2. exact POS1. }
          assert (BNULL0: bool_decide (i0 = 0)%Z = true).
          { apply bool_decide_eq_true_2. exact NULL0. }
          rewrite /Mem.vcmp.
          rewrite BPOS0 BPOS1 BNULL0.
          rewrite VP1. ss.
          inv CMP. ss.
        * exfalso.
          discriminate.
      + iPureIntro.
        assert (BPOS0: bool_decide (0 < i0)%Z = false).
        { apply bool_decide_eq_false_2. exact POS0. }
        assert (BPOS1: bool_decide (0 < i1)%Z = false).
        { apply bool_decide_eq_false_2. exact POS1. }
        rewrite /Mem.vcmp.
        rewrite BPOS0 BPOS1.
        inv CMP. destruct (bool_decide (i0 = i1)); ss.
  Qed.

End RA.

Module MemDH. Section MemDH.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition Ist: gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      ((∃ (mem_src mem_tgt: Mem.t) (mem_res: _memRA),
      ⌜st_src = {[HybMem.v_mem #  mem_src↑]} ∧ st_tgt = {[DetMem.v_mem # mem_tgt↑]}⌝ ∗ 
      ⌜mem_wf mem_src ∧ mem_wf mem_tgt ∧ (Mem.next_loc mem_src <= Mem.next_loc mem_tgt)%Z⌝ ∗
      ⌜sim_mem mem_res mem_src mem_tgt⌝ ∗
      ( |==> mem_own mem_name ((● mem_res)))))%I.

  Local Definition HybMem := HybMem.t.
  Local Definition DetMem := DetMem.t.
  Local Definition IstFull := (IstProd (IstSB HybMem.(Mod.scopes) Ist) IstEq).

  Lemma compare_val_bool_decide arg0 arg1 succ
    (COMP: HybMem.compare_val arg0 arg1 = Vint succ)
    :
    Vint succ = Vint (if bool_decide (succ = 1) then 1 else 0).
  Proof.
    move: COMP. rewrite /HybMem.compare_val.
    destruct arg0 as [i0|[b0 ofs0]|];
      destruct arg1 as [i1|[b1 ofs1]|]; ss; try discriminate.
    all: repeat case_bool_decide; ss; i; clarify; case_bool_decide; ss.
  Qed.

  Definition mem_get (mem: _memRA) loc :=
    match or_else (mem loc) (to_frac_agree 1 (Some Vundef)) with
    | (_,v) => or_else (nth_error v.(agree_car) 0) (Some Vundef)
    end.

  Lemma mem_get_sound mem loc v
      (HIT : mem loc ≡ Some (to_frac_agree 1 (Some v))) :
    mem_get mem loc = Some v.
  Proof using.
    rr in HIT. depdes HIT. rewrite /mem_get -x. s. destruct x0.
    symmetry in H. eapply to_frac_agree_inv in H. des. ss. subst.
    rewrite H0. et.
  Qed.

  Lemma points_to_r_outside loc q vs loc0
    (OUT: ~ (loc <= loc0 < loc + Z.of_nat (length vs))%Z) :
    _points_to_r loc q vs loc0 = None.
  Proof.
    rewrite /_points_to_r.
    assert (BOOL: bool_decide (loc <= loc0 < loc + Z.of_nat (length vs))%Z = false).
    { apply bool_decide_eq_false_2. exact OUT. }
    rewrite BOOL. reflexivity.
  Qed.

  Lemma sim_mem_valid_ptr mem_res mem_src mem_tgt loc
    (SIM: _sim_mem mem_res mem_src mem_tgt)
    (VALID: Mem.valid_ptr mem_src loc)
    :
    Mem.valid_ptr mem_tgt loc.
  Proof.
    specialize (SIM loc).
    unfold _sim_mem, not_allocated, alloc_by_spec, alloc_by_impl in SIM.
    unfold Mem.valid_ptr in *.
    destruct SIM as [[_ [Hsrc _]]|[[v [_ [Hsrc _]]]|[v [_ [Hsrc Htgt]]]]].
    - rewrite Hsrc in VALID. discriminate.
    - rewrite Hsrc in VALID. discriminate.
    - rewrite Htgt. exact eq_refl.
  Qed.

  Lemma sim_mem_vcmp mem_res mem_src mem_tgt arg0 arg1 f
    (SIM: _sim_mem mem_res mem_src mem_tgt)
    (CMP: Mem.vcmp mem_src arg0 arg1 = Some f)
    :
    Mem.vcmp mem_tgt arg0 arg1 = Some f.
  Proof.
    destruct arg0 as [i0|bo0|];
      destruct arg1 as [i1|bo1|]; ss.
    rewrite /Mem.vcmp in CMP |- *.
    destruct (bool_decide (0 < i0)%Z) eqn:BPOS0.
    - destruct (bool_decide (0 < i1)%Z) eqn:BPOS1.
      + destruct (bool_decide (Mem.valid_ptr mem_src i0 ∧ Mem.valid_ptr mem_src i1)) eqn:BVP; ss.
        apply bool_decide_eq_true_1 in BVP.
        assert (TVP: bool_decide (Mem.valid_ptr mem_tgt i0 ∧ Mem.valid_ptr mem_tgt i1) = true).
        {
          apply bool_decide_eq_true_2.
          destruct BVP as [VP0 VP1]. split.
          - eapply sim_mem_valid_ptr; eauto.
          - eapply sim_mem_valid_ptr; eauto.
        }
        rewrite TVP. exact CMP.
      + destruct (bool_decide (i1 = 0)%Z) eqn:BNULL1; ss.
        destruct (bool_decide (Mem.valid_ptr mem_src i0)) eqn:BVP; ss.
        apply bool_decide_eq_true_1 in BVP.
        assert (TVP: bool_decide (Mem.valid_ptr mem_tgt i0) = true).
        {
          apply bool_decide_eq_true_2.
          eapply sim_mem_valid_ptr; eauto.
        }
        rewrite TVP. exact CMP.
    - destruct (bool_decide (0 < i1)%Z) eqn:BPOS1.
      + destruct (bool_decide (i0 = 0)%Z) eqn:BNULL0; ss.
        destruct (bool_decide (Mem.valid_ptr mem_src i1)) eqn:BVP; ss.
        apply bool_decide_eq_true_1 in BVP.
        assert (TVP: bool_decide (Mem.valid_ptr mem_tgt i1) = true).
        {
          apply bool_decide_eq_true_2.
          eapply sim_mem_valid_ptr; eauto.
        }
        rewrite TVP. exact CMP.
      + exact CMP.
  Qed.

  Lemma simF_alloc : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.alloc).
  Proof using.
    cStartFunSim. rewrite /HybMem.alloc /DetMem.alloc.
    
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM [NEXT NEG]].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT.
    destruct _q; cycle 1.
    { (* using physical memory *)
      case_bool_decide as SIZE; cycle 1.
      { ss. rewrite /triggerUB. cStepsS; ss. }
      destruct SIZE as [SIZE2 SIZE3].
      cStepsS.
      cForceS (Z.to_nat (Mem.next_loc mem_tgt - Mem.next_loc mem_src)). cStepsS.
      set (nloc := Mem.next_loc mem_tgt).
      replace (Mem.next_loc mem_src + Z.of_nat (Z.to_nat (nloc - Mem.next_loc mem_src)))%Z with nloc by nia.
      assert (NLOC: ∀ loc (LOC: (loc >= nloc)%Z), mem_res loc = None).
      { i. destruct (NEXT loc (ltac:(nia))). ss. }

      cStepsT. cStep. iSplitR; [eauto|].
      iExists {[HybMem.v_mem #  _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _. fold nloc.
      iSplitR. { iPureIntro. esplits; try refl. }
      iSplitR.
      {
        iPureIntro.
        destruct H2 as [POSsrc WFsrc].
        destruct H4 as [POStgt WFtgt].
        assert (VSZ: (0 <= v)%Z) by nia.
        splits; ss.
        - split. { rewrite /Mem.alloc /Mem.mem_pad /=. nia. }
          ii. rewrite /Mem.alloc /Mem.update_cnts /Mem.mem_pad /= in H |- *.
          destruct (bool_decide (0 < loc)%Z) eqn:POS; ss.
          destruct (bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z) eqn:OLD.
          * apply bool_decide_eq_true_1 in OLD.
            assert (EQN: (Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z = nloc) by nia.
            nia.
          * destruct (bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src) + v)%Z) eqn:NEW; ss.
            apply bool_decide_eq_true_1 in NEW.
            assert (EQN: (Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z = nloc) by nia.
            nia.
        - split. { rewrite /Mem.alloc /=. nia. }
          ii. rewrite /Mem.alloc /Mem.update_cnts /= in H |- *.
          destruct (bool_decide (0 < loc)%Z) eqn:POS; ss.
          destruct (bool_decide (loc < Mem.next_loc mem_tgt)%Z) eqn:OLD.
          * apply bool_decide_eq_true_1 in OLD. nia.
          * destruct (bool_decide (loc < Mem.next_loc mem_tgt + v)%Z) eqn:NEW; ss.
            apply bool_decide_eq_true_1 in NEW. nia.
        - nia.
      }
      iFrame. iSplitL; eauto.
      iSplitL; cycle 1.
      {
        iSplitL.
        {
          iPureIntro. intros loc OUT.
          cbn in OUT.
          unfold not_allocated in *.
          specialize (NEXT loc (ltac:(nia))).
          destruct NEXT as [Hra [Hsrc Htgt]].
          split; [exact Hra|]. split.
          - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
            destruct (bool_decide (0 < loc)%Z) eqn:POS; [|reflexivity].
            destruct (bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z) eqn:OLD.
            { apply bool_decide_eq_true_1 in OLD. nia. }
            destruct (bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src) + v)%Z) eqn:NEW.
            { apply bool_decide_eq_true_1 in NEW. nia. }
            reflexivity.
          - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
            destruct (bool_decide (0 < loc)%Z) eqn:POS; [|reflexivity].
            destruct (bool_decide (loc < Mem.next_loc mem_tgt)%Z) eqn:OLD.
            { apply bool_decide_eq_true_1 in OLD. nia. }
            destruct (bool_decide (loc < Mem.next_loc mem_tgt + v)%Z) eqn:NEW.
            { apply bool_decide_eq_true_1 in NEW. nia. }
            reflexivity.
        }
        {
          iPureIntro. intros loc OUT.
          unfold not_allocated in *.
          specialize (NEG loc (ltac:(nia))).
          destruct NEG as [Hra [Hsrc Htgt]].
          split; [exact Hra|]. split.
          - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
            assert (POS: bool_decide (0 < loc)%Z = false).
            { apply bool_decide_eq_false_2. nia. }
            rewrite POS. reflexivity.
          - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
            assert (POS: bool_decide (0 < loc)%Z = false).
            { apply bool_decide_eq_false_2. nia. }
            rewrite POS. reflexivity.
        }
      }

      iIntros "%loc". destruct (loc <? nloc + v)%Z eqn:SZ; cycle 1.
      {
        iLeft. iPureIntro.
        unfold not_allocated in *.
        specialize (NEXT loc (ltac:(nia))). destruct NEXT as [Hra [Hsrc Htgt]].
        split; [exact Hra|]. split.
        - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
          destruct (bool_decide (0 < loc)%Z) eqn:POS; [|reflexivity].
          destruct (bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z) eqn:OLD.
          { apply bool_decide_eq_true_1 in OLD. nia. }
          destruct (bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src) + v)%Z) eqn:NEW.
          { apply bool_decide_eq_true_1 in NEW. apply Z.ltb_ge in SZ. nia. }
          reflexivity.
        - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
          destruct (bool_decide (0 < loc)%Z) eqn:POS; [|reflexivity].
          destruct (bool_decide (loc < Mem.next_loc mem_tgt)%Z) eqn:OLD.
          { apply bool_decide_eq_true_1 in OLD. nia. }
          destruct (bool_decide (loc < Mem.next_loc mem_tgt + v)%Z) eqn:NEW.
          { apply bool_decide_eq_true_1 in NEW. apply Z.ltb_ge in SZ. nia. }
          reflexivity.
      }
      destruct (bool_decide (0 < loc)%Z) eqn:POS; cycle 1.
      {
        iLeft. iPureIntro.
        unfold not_allocated in *.
        apply bool_decide_eq_false_1 in POS.
        specialize (NEG loc (ltac:(nia))). destruct NEG as [Hra [Hsrc Htgt]].
        split; [exact Hra|]. split.
        - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
          assert (BPOS: bool_decide (0 < loc)%Z = false).
          { apply bool_decide_eq_false_2. exact POS. }
          rewrite BPOS. reflexivity.
        - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
          assert (BPOS: bool_decide (0 < loc)%Z = false).
          { apply bool_decide_eq_false_2. exact POS. }
          rewrite BPOS. reflexivity.
      }
      destruct (loc <? nloc)%Z eqn:NL; cycle 1.
      {
        iRight. iRight.
        unfold alloc_by_impl. ss.
        iPureIntro. exists Vundef.
        split.
        { apply NLOC. nia. }
        split.
        - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
          assert (BOLD: bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z = false).
          { apply bool_decide_eq_false_2. apply Z.ltb_ge in NL. nia. }
          assert (BNEW: bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src) + v)%Z = true).
          { apply bool_decide_eq_true_2. apply Z.ltb_ge in NL. apply Z.ltb_lt in SZ. nia. }
          rewrite POS BOLD BNEW. reflexivity.
        - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
          assert (BOLD: bool_decide (loc < Mem.next_loc mem_tgt)%Z = false).
          { apply bool_decide_eq_false_2. apply Z.ltb_ge in NL. nia. }
          assert (BNEW: bool_decide (loc < Mem.next_loc mem_tgt + v)%Z = true).
          { apply bool_decide_eq_true_2. apply Z.ltb_ge in NL. apply Z.ltb_lt in SZ. nia. }
          rewrite POS BOLD BNEW. reflexivity.
      }
      destruct (SIM loc).
      {
        iLeft. iPureIntro.
        unfold not_allocated in H. destruct H as [Hra [Hsrc Htgt]].
        split; [exact Hra|]. split.
        - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
          assert (BOLD: bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z = true).
          { apply bool_decide_eq_true_2. apply Z.ltb_lt in NL. nia. }
          rewrite POS BOLD. exact Hsrc.
        - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
          assert (BOLD: bool_decide (loc < Mem.next_loc mem_tgt)%Z = true).
          { apply bool_decide_eq_true_2. apply Z.ltb_lt in NL. nia. }
          rewrite POS BOLD. exact Htgt.
      }
      destruct H.
      {
        iRight. iLeft. iPureIntro.
        unfold alloc_by_spec in H. destruct H as [v1 [Hra [Hsrc Htgt]]].
        exists v1. split; [exact Hra|]. split.
        - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
          assert (BOLD: bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z = true).
          { apply bool_decide_eq_true_2. apply Z.ltb_lt in NL. nia. }
          rewrite POS BOLD. exact Hsrc.
        - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
          assert (BOLD: bool_decide (loc < Mem.next_loc mem_tgt)%Z = true).
          { apply bool_decide_eq_true_2. apply Z.ltb_lt in NL. nia. }
          rewrite POS BOLD. exact Htgt.
      }
      iRight. iRight. iPureIntro.
      unfold alloc_by_impl in H. destruct H as [v1 [Hra [Hsrc Htgt]]].
      exists v1. split; [exact Hra|]. split.
      - rewrite /Mem.alloc /= /Mem.update_cnts /Mem.mem_pad. cbn.
        assert (BOLD: bool_decide (loc < Mem.next_loc mem_src + Z.to_nat (nloc - Mem.next_loc mem_src))%Z = true).
        { apply bool_decide_eq_true_2. apply Z.ltb_lt in NL. nia. }
        rewrite POS BOLD. exact Hsrc.
      - rewrite /Mem.alloc /= /Mem.update_cnts. cbn.
        assert (BOLD: bool_decide (loc < Mem.next_loc mem_tgt)%Z = true).
        { apply bool_decide_eq_true_2. apply Z.ltb_lt in NL. nia. }
        rewrite POS BOLD. exact Htgt.
    }

    (* using logical memory *)
    cStepsS. iDestruct "ASM" as "%SIZE". des. rename v into sz.
    case_bool_decide as SIZE'; cycle 1.
    { exfalso. nia. }
    destruct SIZE' as [SIZE2 SIZE3].
    cStepsT.
    cForceS (Mem.next_loc mem_tgt). cStepsS.
    iPoseProof (mem_ra_alloc_next with "B") as ">[B W]"; eauto.

    iPoseProof (points_to_transform with "W") as "W".
    assert (SSIM: sim_mem mem_res mem_src mem_tgt).
    { unfold sim_mem. esplits; eauto. }
    iPoseProof
      (@mem_ra_lookup_list _ _ _ _ _ _ _ _ _
         mem_res mem_src mem_tgt
         (mem_res ⋅ _points_to_r (Mem.next_loc mem_tgt) 1 (repeat Vundef (Z.to_nat sz)))
         ((Mem.alloc mem_tgt sz).2) sz
         SSIM eq_refl H4 eq_refl (ltac:(nia))
       with "[B W]") as "%RES".
    { iFrame. }

    cForcesS. iSplitL "W".
    { destruct H4. eauto. }
    set (nloc := Mem.next_loc mem_tgt). cStepsS.

    cStep. iSplitR; [eauto|].
    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _.
    iSplitR. { iPureIntro. esplits; try refl. }
    iSplitR.
    {
      iPureIntro.
      destruct H4 as [POStgt WFtgt].
      splits; ss.
      - split. { rewrite /Mem.alloc /=. nia. }
        ii. rewrite /Mem.alloc /Mem.update_cnts /= in H |- *.
        destruct (bool_decide (0 < loc)%Z) eqn:POS; ss.
        destruct (bool_decide (loc < Mem.next_loc mem_tgt)%Z) eqn:OLD.
        * apply bool_decide_eq_true_1 in OLD. nia.
        * destruct (bool_decide (loc < Mem.next_loc mem_tgt + sz)%Z) eqn:NEW; ss.
          apply bool_decide_eq_true_1 in NEW. nia.
      - nia.
    }
    iFrame. iSplitL; eauto.
    iSplitL; cycle 1.
    {
      iSplitL.
      {
        iPureIntro. intros loc OUT.
        unfold not_allocated in *.
        rewrite discrete_fun_lookup_op.
        rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
        2: {
          intro RANGE. destruct RANGE as [_ RANGE].
          cbn in OUT.
          rewrite repeat_length in RANGE.
          assert (EQSZ: Z.of_nat (Z.to_nat sz) = sz) by (apply Z2Nat.id; nia).
          rewrite EQSZ in RANGE. nia.
        }
        rewrite right_id.
        cbn in OUT.
        specialize (NEXT loc (ltac:(nia))). destruct NEXT as [Hra [Hsrc Htgt]].
        split; [exact Hra|]. split; [exact Hsrc|].
        rewrite /Mem.alloc /Mem.update_cnts /=.
        destruct (bool_decide (0 < loc)%Z) eqn:POS; ss.
        destruct (bool_decide (loc < Mem.next_loc mem_tgt)%Z) eqn:OLD.
        * apply bool_decide_eq_true_1 in OLD. nia.
        * destruct (bool_decide (loc < Mem.next_loc mem_tgt + sz)%Z) eqn:NEW.
          { apply bool_decide_eq_true_1 in NEW. nia. }
          { reflexivity. }
      }
      {
        iPureIntro. intros loc OUT.
        destruct H4 as [POStgt WFtgt].
        unfold not_allocated in *.
        rewrite discrete_fun_lookup_op.
        rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
        2: { intro RANGE. destruct RANGE as [RANGE _]. nia. }
        rewrite right_id.
        specialize (NEG loc (ltac:(nia))). destruct NEG as [Hra [Hsrc Htgt]].
        split; [exact Hra|]. split; [exact Hsrc|].
        rewrite /Mem.alloc /Mem.update_cnts /=.
        destruct (bool_decide (0 < loc)%Z) eqn:POS; ss.
        apply bool_decide_eq_true_1 in POS. nia.
      }
    }

    iIntros "%loc". destruct (loc <? nloc + sz)%Z eqn:SZ; cycle 1.
    {
      iLeft. iPureIntro. unfold not_allocated in *.
      rewrite discrete_fun_lookup_op.
      rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
      2: {
        intro RANGE. destruct RANGE as [_ RANGE].
        apply Z.ltb_ge in SZ.
        rewrite repeat_length in RANGE.
        assert (EQSZ: Z.of_nat (Z.to_nat sz) = sz) by (apply Z2Nat.id; nia).
        rewrite EQSZ in RANGE. nia.
      }
      rewrite right_id.
      apply Z.ltb_ge in SZ.
      specialize (NEXT loc (ltac:(nia))). destruct NEXT as [Hra [Hsrc Htgt]].
      split; [exact Hra|]. split; [exact Hsrc|].
      rewrite /Mem.alloc /Mem.update_cnts /=.
      destruct (bool_decide (0 < loc)%Z) eqn:POS; ss.
      destruct (bool_decide (loc < Mem.next_loc mem_tgt)%Z) eqn:OLD.
      - apply bool_decide_eq_true_1 in OLD. nia.
      - destruct (bool_decide (loc < Mem.next_loc mem_tgt + sz)%Z) eqn:NEW.
        { apply bool_decide_eq_true_1 in NEW. nia. }
        { reflexivity. }
    }
    destruct (bool_decide (0 < loc)%Z) eqn:POS; cycle 1.
    {
      iLeft. iPureIntro. unfold not_allocated in *.
      rewrite discrete_fun_lookup_op.
      rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
      2: { intro RANGE. destruct RANGE as [RANGE _]. apply bool_decide_eq_false_1 in POS. destruct H4. nia. }
      rewrite right_id.
      apply bool_decide_eq_false_1 in POS.
      specialize (NEG loc (ltac:(nia))). destruct NEG as [Hra [Hsrc Htgt]].
      split; [exact Hra|]. split; [exact Hsrc|].
      rewrite /Mem.alloc /Mem.update_cnts /=.
      destruct (bool_decide (0 < loc)%Z) eqn:POS'; ss.
      apply bool_decide_eq_true_1 in POS'. nia.
    }
    destruct (loc <? nloc)%Z eqn:NL; cycle 1.
    { (* alloced *)
      iRight. iLeft.
      unfold alloc_by_spec. ss.
      apply Z.ltb_ge in NL.
      apply Z.ltb_lt in SZ.
      assert (PTS: bool_decide (nloc <= loc < nloc + Z.of_nat (Z.to_nat sz))%Z = true).
      { rewrite Z2Nat.id; [|nia]. apply bool_decide_eq_true_2. nia. }
      assert (OLD: bool_decide (loc < nloc)%Z = false).
      { apply bool_decide_eq_false_2. nia. }
      assert (NEW: bool_decide (loc < nloc + sz)%Z = true).
      { apply bool_decide_eq_true_2. nia. }
      destruct (NEXT loc (ltac:(nia))) as [HNONE [HSRC _]].
      iPureIntro. exists Vundef.
      rewrite discrete_fun_lookup_op /_points_to_r repeat_length HNONE PTS.
      rewrite nth_error_repeat; [|apply Z2Nat.inj_lt; nia].
      rewrite left_id.
      rewrite /Mem.update_cnts POS OLD NEW.
      split; [reflexivity|]. split; [exact HSRC|reflexivity].
    }

    destruct (SIM loc).
    {
      iLeft. iPureIntro.
      unfold not_allocated in *. destruct H as [HRA [HSRC HTGT]].
      apply Z.ltb_lt in NL.
      assert (OLD: bool_decide (loc < nloc)%Z = true).
      { apply bool_decide_eq_true_2. nia. }
      rewrite discrete_fun_lookup_op.
      rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
      2: { intro RANGE. destruct RANGE as [RANGE _]. nia. }
      rewrite right_id.
      cbn.
      rewrite /Mem.update_cnts POS OLD.
      split; [exact HRA|]. split; [exact HSRC|exact HTGT].
    }
    destruct H as [H|H].
    {
      iRight. iLeft. iPureIntro.
      unfold alloc_by_spec in *. destruct H as [v0 [HRA [HSRC HTGT]]].
      apply Z.ltb_lt in NL.
      assert (OLD: bool_decide (loc < nloc)%Z = true).
      { apply bool_decide_eq_true_2. nia. }
      exists v0.
      rewrite discrete_fun_lookup_op.
      rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
      2: { intro RANGE. destruct RANGE as [RANGE _]. nia. }
      rewrite right_id.
      cbn.
      rewrite /Mem.update_cnts POS OLD.
      split; [exact HRA|]. split; [exact HSRC|exact HTGT].
    }
    iRight. iRight. iPureIntro.
    unfold alloc_by_impl in *. destruct H as [v0 [HRA [HSRC HTGT]]].
    apply Z.ltb_lt in NL.
    assert (OLD: bool_decide (loc < nloc)%Z = true).
    { apply bool_decide_eq_true_2. nia. }
    exists v0.
    rewrite discrete_fun_lookup_op.
    rewrite (points_to_r_outside nloc 1 (repeat Vundef (Z.to_nat sz)) loc).
    2: { intro RANGE. destruct RANGE as [RANGE _]. nia. }
    rewrite right_id.
    cbn.
    rewrite /Mem.update_cnts POS OLD.
    split; [exact HRA|]. split; [exact HSRC|exact HTGT].
  (* SLOW *)Qed.

  Lemma simF_free : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.free).
  Proof using.
    cStartFunSim. rewrite /HybMem.free /DetMem.free.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM [NEXT NEG]].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT.
    destruct _q; cycle 1.
    { (* physical memory *)
      cStepsS. cSimpl. cStepsS. rename v into loc.
      hexploit (SIM loc). intro SIM0.
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
      rewrite /Mem.free.
      destruct SIM0 as [SIMna|[SIMsp|SIMimpl]];
        [destruct SIMna as [Hra [Hsrc Htgt]]
        |destruct SIMsp as [v0 [Hra [Hsrc Htgt]]]
        |destruct SIMimpl as [v0 [Hra [Hsrc Htgt]]]];
        des_ifs; cStepsS; des_ifs.
      cStepsT.
      cStep. iSplit; eauto.

      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR.
      {
        iPureIntro. splits; ss; try nia.
        - split. { cbn. destruct H2. nia. }
          ii. cbn in H |- *. unfold update in *.
          des_ifs; eapply H2; eauto.
        - split. { cbn. destruct H4. nia. }
          ii. cbn in H |- *. unfold update in *.
          des_ifs; eapply H4; eauto.
      }
      iFrame. iSplit; eauto.
      iSplitL; cycle 1.
      {
        iPureIntro. split.
        - i. specialize (NEXT loc0 OUT).
          unfold not_allocated, update in *. ss. des.
          esplits; eauto; des_ifs.
        - i. specialize (NEG loc0 OUT).
          unfold not_allocated, update in *. ss. des.
          esplits; eauto; des_ifs.
      }
      iPureIntro. ii. unfold not_allocated, alloc_by_spec, alloc_by_impl, update; ss.
      des_ifs; esplits; eauto.
    }

    (* logical memory *)
    cStepsS.
    iDestruct "ASM" as (?) "POINTS".
    rename v into loc.

    iPoseProof (mem_ra_lookup_point with "[B POINTS]") as "%P"; [eauto|iFrame|].
    des. rewrite /Mem.free.
    rewrite P0. cStepsT.

    iPoseProof (mem_ra_free with "[B POINTS]") as ">P"; iFrame.

    cStep. iSplit; eauto.
    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _. iSplit. { iPureIntro. esplits; try refl. }
    iSplitR.
    {
      iPureIntro. splits; ss; try nia.
      - split. { cbn. destruct H4. nia. }
        ii. cbn in H |- *. unfold update in *. des_ifs; eapply H4; eauto.
    }
    iFrame; iSplit; eauto.
    iPureIntro. split; cycle 1.
    {
      split.
      - i. specialize (NEXT loc0 OUT).
        unfold not_allocated, update in *. ss. des.
        unfold mem_ra_upd. esplits; eauto; des_ifs.
      - i. specialize (NEG loc0 OUT).
        unfold not_allocated, update in *. ss. des.
        unfold mem_ra_upd. esplits; eauto; des_ifs.
    }
    intros loc0. specialize (SIM loc0).
    destruct (bool_decide (loc = loc0)) eqn:EQ.
    - apply bool_decide_eq_true_1 in EQ. subst loc0.
      left. unfold not_allocated, mem_ra_upd, update.
      destruct SIM as [SIMna|[SIMsp|SIMimpl]].
      + destruct SIMna as [Hra [Hsrc Htgt]]. rewrite Hra in P. inv P.
      + destruct SIMsp as [v1 [Hra [Hsrc Htgt]]].
        rewrite bool_decide_eq_true_2; [|reflexivity].
        split; [reflexivity|]. split; [exact Hsrc|].
        cbn. rewrite /dec. destruct (Z_Dec loc loc); ss.
      + destruct SIMimpl as [v1 [Hra [Hsrc Htgt]]]. rewrite Hra in P. inv P.
    - apply bool_decide_eq_false_1 in EQ.
      unfold mem_ra_upd, not_allocated, alloc_by_spec, alloc_by_impl, update in *.
      destruct SIM as [SIMna|[SIMsp|SIMimpl]].
      + left. destruct SIMna as [Hra [Hsrc Htgt]].
        rewrite bool_decide_eq_false_2; [|exact EQ].
        split; [exact Hra|]. split; [exact Hsrc|].
        cbn. rewrite /dec. destruct (Z_Dec loc loc0); [congruence|exact Htgt].
      + right. left. destruct SIMsp as [v1 [Hra [Hsrc Htgt]]].
        rewrite bool_decide_eq_false_2; [|exact EQ].
        exists v1. split; [exact Hra|]. split; [exact Hsrc|].
        cbn. rewrite /dec. destruct (Z_Dec loc loc0); [congruence|exact Htgt].
      + right. right. destruct SIMimpl as [v1 [Hra [Hsrc Htgt]]].
        rewrite bool_decide_eq_false_2; [|exact EQ].
        exists v1. split; [exact Hra|]. split; [exact Hsrc|].
        cbn. rewrite /dec. destruct (Z_Dec loc loc0); [congruence|exact Htgt].
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.load).
  Proof using.
    cStartFunSim. rewrite /HybMem.load /DetMem.load.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM [NEXT NEG]].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT.
    destruct _q; cycle 1.
    { (* physical memory *)
      cStepsS. cSimpl. cStepsS.
      rename v into loc.
      hexploit (SIM loc). intro SIM0.
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
      rewrite /Mem.load.
      des; des_ifs; try by (rewrite SIM1; cStepsS; ss).
      rewrite SIM1 SIM2. cStepsS; cStepsT.
      cStep. iSplit; eauto.

      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia. }
      iFrame. iSplit; eauto.
    }

    (* logical memory *)
    cStepsS. destruct _q as [v0 q]. cStepsS.
    rename v into loc.
    hexploit (SIM loc). intro SIM0.
    unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
    rewrite /Mem.load.
    des; swap 2 3.
    {
      iPoseProof (mem_ra_lookup_point with "[B ASM]") as "%P"; [eauto|iFrame|].
      des; clarify.
    }
    {
      iPoseProof (mem_ra_lookup_point with "[B ASM]") as "%P"; [eauto|iFrame|].
      des. rewrite SIM0 in P. inv P.
    }
    
    s. rewrite SIM2. cStepsT.
    cStepsS.
    iPoseProof (mem_ra_lookup_point with "[B ASM]") as "%P";[eauto|iFrame|].
    des. inv P0.
    cForcesS. iSplitL "ASM"; eauto. cStepsS.
    cStep. iSplit; [eauto|].
    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _.  
    iSplit. { iPureIntro. esplits; try refl. }
    iSplitR. 
    { iPureIntro. splits; ss; try nia. }
    iFrame. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.store).
  Proof using.
    cStartFunSim. rewrite /HybMem.store /DetMem.store.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM [NEXT NEG]].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. destruct v as [loc v]. cStepsT.
    cStepsS.
    destruct _q; cycle 1.
    { (* physical memory *)
      cStepsS.
      hexploit (SIM loc). intro SIM0.
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
      unfold Mem.store in *.
      des; des_ifs.
      - cStepsS. ss.
      - cStepsS. ss.
      - cStepsT. cStepsS.
      cStep. iSplit; [eauto|].

      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia.
        - split. { destruct H2. ss. }
          ii. ss. unfold update in *.
          des_ifs; eapply H2; eauto.
        - split. { destruct H4. ss. }
          ii. ss. unfold update in *.
          des_ifs; eapply H4; eauto.
      }
      iFrame. iSplit; eauto.
      iPureIntro. split; cycle 1.
      {
        split.
        {
          i. specialize (NEXT loc0 OUT).
          unfold not_allocated, update in *. ss. des.
          esplits; eauto; des_ifs.
        }
        {
          i. specialize (NEG loc0 OUT).
          unfold not_allocated, update in *. ss. des.
          esplits; eauto; des_ifs.
        }
      }
      ii. unfold not_allocated, alloc_by_spec, alloc_by_impl, update; ss.
      des_ifs; esplits; eauto.
      right. right. eauto.
    }

    (* logical memory *)
    cStepsS. iDestruct "ASM" as ( ? )  "ASM".
    iPoseProof (mem_ra_lookup_point with "[B ASM]") as "%POINT"; [eauto|iFrame|].
    
    hexploit (SIM loc). intro SIM0.
    unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
    des; des_ifs; cycle 1. { rewrite SIM0 in POINT. inv POINT. }

    iPoseProof (mem_ra_store with "[B ASM]") as ">[B P]"; [eauto|iFrame|].
    cForcesS. iSplitL "P"; eauto. cStepsS.

    cStepsT. rewrite /Mem.store SIM2. cStepsT.
    cStep. iSplit; [eauto|].

    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _.  
    iSplit. { iPureIntro. esplits; try refl. }
    iSplitR.
    { iPureIntro. splits; ss; try nia.
      split. { destruct H4. ss. }
      ii. ss. unfold update in *.
      des_ifs; eapply H4; eauto.
    }
    iFrame. iSplit; eauto.
    iPureIntro. split; cycle 1.
    {
      split.
      {
        i. specialize (NEXT loc0 OUT).
        unfold not_allocated in *. destruct NEXT as [Hra [Hsrc Htgt]].
        unfold mem_ra_upd, update.
        destruct (bool_decide (loc = loc0)) eqn:EQ.
        - apply bool_decide_eq_true_1 in EQ. subst loc0.
          rewrite Htgt in SIM2. inv SIM2.
        - apply bool_decide_eq_false_1 in EQ.
          split.
          { rewrite bool_decide_eq_false_2; [exact Hra|exact EQ]. }
          split; [exact Hsrc|].
          cbn. unfold update. rewrite /dec.
          destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
      }
      {
        i. specialize (NEG loc0 OUT).
        unfold not_allocated in *. destruct NEG as [Hra [Hsrc Htgt]].
        unfold mem_ra_upd, update.
        destruct (bool_decide (loc = loc0)) eqn:EQ.
        - apply bool_decide_eq_true_1 in EQ. subst loc0.
          rewrite Htgt in SIM2. inv SIM2.
        - apply bool_decide_eq_false_1 in EQ.
          split.
          { rewrite bool_decide_eq_false_2; [exact Hra|exact EQ]. }
          split; [exact Hsrc|].
          cbn. unfold update. rewrite /dec.
          destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
      }
    }
    intros loc0.
    unfold mem_ra_upd, not_allocated, alloc_by_spec, alloc_by_impl, update; ss.
    destruct (bool_decide (loc = loc0)) eqn:EQ.
    - apply bool_decide_eq_true_1 in EQ. subst loc0.
      right. left. exists v.
      split; [reflexivity|]. split; [exact SIM1|].
      cbn. unfold update. rewrite /dec. destruct (Z_Dec loc loc); ss.
    - apply bool_decide_eq_false_1 in EQ.
      cbn. unfold update. rewrite /dec.
      destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [congruence|].
      specialize (SIM loc0).
      destruct SIM as [SIMna|[SIMsp|SIMimpl]].
      + left. destruct SIMna as [Hra [Hsrc Htgt]].
        split; [exact Hra|]. split; [exact Hsrc|exact Htgt].
      + right. left. destruct SIMsp as [v1 [Hra [Hsrc Htgt]]].
        exists v1. split; [exact Hra|]. split; [exact Hsrc|exact Htgt].
      + right. right. destruct SIMimpl as [v1 [Hra [Hsrc Htgt]]].
        exists v1. split; [exact Hra|]. split; [exact Hsrc|exact Htgt].
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.cmp).
  Proof using.
    cStartFunSim. rewrite /HybMem.cmp /DetMem.cmp.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM [NEXT NEG]].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. destruct v as [arg0 arg1]. cStepsT.
    cStepsS.
    destruct _q.
    { (* logical memory *)
      cStepsS. destruct _q as [[v0 q0] [v1 q1]]. cStepsS.
      iDestruct "ASM" as "[%COMP ASM]". des.

      iPoseProof (mem_ra_cmp with "[B ASM]") as "%CMP"; eauto; [iFrame|].
      cForceS. iSplitL "ASM"; eauto. cStepsS.
      rewrite CMP. cStepsT.
      cStep. iSplit.
      { iPureIntro. rewrite COMP. f_equal. eapply compare_val_bool_decide; eauto. }
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
	      { iPureIntro. splits; ss; try nia. }
	      iFrame. iSplit; eauto.
	    }

	    cStepsS.
	    destruct (Mem.vcmp mem_src arg0 arg1) eqn:S; cycle 1.
	    { cStepsS; des_ifs. }
	    rename b into f.
	    destruct (Mem.vcmp mem_tgt arg0 arg1) as [r|] eqn:E; ss; cycle 1.
	    {
	      exfalso.
	      pose proof (sim_mem_vcmp _ _ _ _ _ _ SIM S) as T.
	      rewrite E in T. discriminate.
	    }
	    cStepsT.
	    pose proof (sim_mem_vcmp _ _ _ _ _ _ SIM S) as T.
	    rewrite E in T. inv T.
	    cStep. iSplit; eauto.
	    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
	    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
	    iExists _, _, _.
	    iSplit. { iPureIntro. esplits; try refl. }
	    iSplitR.
	    { iPureIntro. splits; ss; try nia. }
	    iFrame. iSplit; eauto.
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.cas).
  Proof using.
    cStartFunSim. rewrite /HybMem.cas /DetMem.cas.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
	    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
	    { cStepsS. des_ifs. }
	    cStepsS. cStepsT.
	    destruct v as [loc [v_old v_new]]. cStepsS.

    destruct _q; cycle 1.
    { (* physical memory *)
      cSimpl. cStepsT. cStepsS.
      cCall "IST". iIntros (???) "IST". cStepsS. cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS; des_ifs. }
      cStepsS. cStepsT.
      cCall "IST". iIntros (???) "IST". cStepsS. cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS; des_ifs. }
      cStepsS. cStepsT.
      destruct (bool_decide (v0 = Vint 1)) eqn:EQV0; cycle 1.
      { cStepsS. cStepsT. cStep; eauto. iFrame. eauto. }
      cStepsS. cStepsT. 
      cCall "IST". iIntros (???) "IST". cStepsS. cStepsT.
      rewrite {1}/unwrapU. des_ifs; cycle 1.
      { cStepsS; des_ifs. }
      cStepsS. cStepsT.
      cStep; iFrame; eauto.
    }

	    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
	    destruct SIM as [SIM [NEXT NEG]]. cStepsS.
	    destruct _q as [[[v_cur succ] [v0 q0]] [v1 q1]]. cStepsS.
	    iDestruct "ASM" as "(%CMP & CUR & CMP0 & CMP1)". cStepsT.

	    cInlineT. cStepsT.
	    iPoseProof (mem_ra_lookup_point with "[B CUR]") as "%PT"; [eauto|iFrame|]. des.
	    pose proof (SIM loc) as SIMCUR.
	    unfold not_allocated, alloc_by_spec, alloc_by_impl in SIMCUR.
	    destruct SIMCUR as [SIMna|[SIMsp|SIMimpl]].
	    { destruct SIMna as [Hra _]. rewrite Hra in PT. inv PT. }
	    2: { destruct SIMimpl as [v2 [Hra _]]. rewrite Hra in PT. inv PT. }
	    destruct SIMsp as [v2 [SIM0 [SIM1 SIM2]]].
	    rewrite /Mem.load PT0. cStepsT.
    cInlineT. cStepsT.
    iPoseProof (mem_ra_cmp with "[B CUR CMP0 CMP1]") as "%CP"; eauto; [iFrame|].
	    rewrite CP. cStepsT.

	    repeat case_bool_decide; simplify_eq.
	    - cStepsT. cInlineT. cStepsT. rewrite /Mem.store PT0. cStepsT.
	      iPoseProof (mem_ra_store with "[B CUR]") as ">[B P]"; [eauto|iFrame|].
	      cForcesS. iSplitR "B"; iFrame. cStepsS.
      cStep; iFrame.
      iSplit; eauto.
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
	      iExists _, _.
	      iSplit. { iPureIntro. esplits; try refl. }
	      iSplitR.
	      { iPureIntro.
	        destruct H4 as [POStgt WFtgt].
	        splits; ss; try nia.
	        split. { exact POStgt. }
	        ii. ss. unfold update in *.
	        des_ifs; eauto.
	      }
	      iFrame. iSplit; eauto.
	      iPureIntro. split; cycle 1.
	      {
	        split.
	        {
	          i. specialize (NEXT loc0 OUT).
	          unfold not_allocated in *. destruct NEXT as [Hra [Hsrc Htgt]].
	          unfold mem_ra_upd, update.
	          destruct (bool_decide (loc = loc0)) eqn:EQ.
	          - apply bool_decide_eq_true_1 in EQ. subst loc0.
	            rewrite Htgt in PT0. inv PT0.
	          - apply bool_decide_eq_false_1 in EQ.
	            split.
	            { exact Hra. }
	            split; [exact Hsrc|].
	            cbn. unfold update. rewrite /dec.
	            destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
	        }
	        {
	          i. specialize (NEG loc0 OUT).
	          unfold not_allocated in *. destruct NEG as [Hra [Hsrc Htgt]].
	          unfold mem_ra_upd, update.
	          destruct (bool_decide (loc = loc0)) eqn:EQ.
	          - apply bool_decide_eq_true_1 in EQ. subst loc0.
	            rewrite Htgt in PT0. inv PT0.
	          - apply bool_decide_eq_false_1 in EQ.
	            split.
	            { exact Hra. }
	            split; [exact Hsrc|].
	            cbn. unfold update. rewrite /dec.
	            destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
	        }
	      }
	      intros loc0.
	      unfold mem_ra_upd, not_allocated, alloc_by_spec, alloc_by_impl, update; ss.
	      destruct (bool_decide (loc = loc0)) eqn:EQ.
	      + apply bool_decide_eq_true_1 in EQ. subst loc0.
	        right. left. exists v_new.
	        split; [reflexivity|]. split; [exact SIM1|].
	        cbn. unfold update. rewrite /dec. destruct (Z_Dec loc loc); ss.
	      + apply bool_decide_eq_false_1 in EQ.
	      specialize (SIM loc0).
	      unfold mem_ra_upd, update.
	      destruct SIM as [SIMna|[SIMsp|SIMimpl]].
	      * left. destruct SIMna as [Hra [Hsrc Htgt]].
	        split.
	        { exact Hra. }
	        split; [exact Hsrc|].
	        cbn. unfold update. rewrite /dec.
	        destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
	      * right. left. destruct SIMsp as [v1' [Hra [Hsrc Htgt]]].
	        exists v1'. split.
	        { exact Hra. }
	        split; [exact Hsrc|].
	        cbn. unfold update. rewrite /dec.
	        destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
	      * right. right. destruct SIMimpl as [v1' [Hra [Hsrc Htgt]]].
	        exists v1'. split.
	        { exact Hra. }
	        split; [exact Hsrc|].
	        cbn. unfold update. rewrite /dec.
	        destruct (Z_Dec loc loc0) as [EQ'|NEQ']; [exfalso; apply EQ; exact EQ'|exact Htgt].
	    - cStepsT.
	      cForcesS. iSplitR "B"; iFrame. cStepsS.
	      cStep; iFrame.
	      iSplit; eauto.
	      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
	      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open HybMem DetMem HybMem.init_cond IstFull.
  Proof using.
    cStartModSim.
    - rewrite /IstFull /HybMem /DetMem. unfold_mod. s. 
      iIntros "P". 
      iExists {[HybMem.v_mem:=Some _]}, {[DetMem.v_mem:=Some _]}, ∅, ∅; ss.
      repeat iSplit; et.
      iExists _, _, _. iSplit; eauto.
      iSplit.
      { iPureIntro. esplits; ii; ss. }
      iFrame. iSplit; eauto.
      iPureIntro.      
      split; ss.
      ii. left. ss.
    - apply simF_alloc.
    - apply simF_free.
    - apply simF_load.
    - apply simF_store.
    - apply simF_cmp.
    - apply simF_cas.
  (*SLOW*)Qed.

  Lemma ctxr :
    ctx_refines
      (DetMem, emp%I)
      (HybMem, HybMem.init_cond).
  Proof using. eapply main_adequacy, sim; eauto. Qed.
End MemDH. End MemDH.
