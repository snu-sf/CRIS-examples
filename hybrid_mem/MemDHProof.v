From CRIS Require Import CRIS.

Require Import ImpPrelude MemHdr MemLib HybridMem DetMem.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.

Local Notation _memRA := (mblock -d> Z -d> optionUR (dfrac_agreeR (optionO (leibnizO val))))%type.
Local Notation memRA := (authUR _memRA)%type.

Section RA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.
  
  Definition mem_wf (m0: Mem.t): Prop :=
    forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> b < m0.(Mem.nb)
  .

  Definition mem_ra_upd mem b ofs r : _memRA :=
    fun b0 ofs0 =>
      if bool_decide (b = b0 ∧ ofs = ofs0) then r else mem b0 ofs0.

  Variable (mem_r: _memRA) (mem_s mem_t: Mem.t).

  Definition not_allocated b ofs := 
    mem_r b ofs = None ∧ Mem.cnts mem_s b ofs = None ∧ Mem.cnts mem_t b ofs = None.
  
  Definition alloc_by_spec b ofs := 
    ∃ v, mem_r b ofs = Some (to_frac_agree 1 (Some v)) ∧ Mem.cnts mem_s b ofs = None ∧ Mem.cnts mem_t b ofs = Some v.

  Definition alloc_by_impl b ofs := 
    ∃ v, mem_r b ofs = None ∧ Mem.cnts mem_s b ofs = Some v ∧ Mem.cnts mem_t b ofs = Some v.

  Definition _sim_mem : Prop :=
    ∀ b ofs, 
      not_allocated b ofs ∨ alloc_by_spec b ofs ∨ alloc_by_impl b ofs.

  Definition sim_mem : Prop :=
    _sim_mem ∧ (∀ b ofs (OUT: b >= Mem.nb mem_t), not_allocated b ofs).

  Lemma mem_ra_alloc_next sz
    (WF: mem_wf mem_t)
    (MEM: _sim_mem)
    :
    mem_own mem_name (● mem_r)
    ⊢ |==>
    mem_own mem_name ((● (mem_r ⋅ _points_to_r (Mem.nb mem_t, 0%Z) 1 (repeat Vundef sz))))
    ∗ mem_own mem_name (((◯ _points_to_r (Mem.nb mem_t, 0%Z) 1 (repeat Vundef sz)))).
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
      hexploit (MEM (Mem.nb mem_t) x0). destruct Hcase as [-> Hcase].  
      unfold _sim_mem, not_allocated, alloc_by_spec, alloc_by_impl; i; subst; des; rewrite H1; try des_ifs;
      exploit WF; et. nia.
  Qed.

  Lemma mem_ra_lookup b ofs q v (sz: Z) mem_t'
    (SIM: sim_mem)
    (MEM: mem_t' = Mem.mk (update (Mem.cnts mem_t) (Mem.nb mem_t) (λ ofs : Z, if bool_decide (0 <= ofs < sz)%Z then Some Vundef else None)) (S (Mem.nb mem_t)))
    (OFS: bool_decide (0 <= ofs < sz)%Z = true)
    :
    mem_own mem_name ((● (mem_r ⋅ _points_to_r (Mem.nb mem_t, 0%Z) 1 (repeat Vundef (Z.to_nat sz))))) ∗ (b, ofs) ⤇{q} v
    ⊢
    ⌜∃ v, (mem_r ⋅ _points_to_r (Mem.nb mem_t, 0%Z) 1 (repeat Vundef (Z.to_nat sz))) b ofs ≡ Some (to_frac_agree 1 (Some v)) ∧
     Mem.cnts mem_t' b ofs = Some v⌝.
  Proof using.
    iIntros "P".
    pose proof OFS as OFS_RANGE.
    apply bool_decide_eq_true_1 in OFS_RANGE.
    assert (SZ: Z.add 0 (Z.to_nat sz) = sz) by nia.
    s. rewrite repeat_length !discrete_fun_lookup_op.
    set (nb := Mem.nb mem_t).
    destruct (dec b nb); subst; s.
    {
      (* b = nb*)
      destruct SIM as [SIM NEXT]. 
      specialize (SIM nb ofs). rewrite SZ.
      specialize (NEXT nb ofs (ltac:(nia))).  
      des; unfold not_allocated, alloc_by_spec, alloc_by_impl in *; des; clarify.
      clear NEXT NEXT0 NEXT1.
      iExists Vundef.
      rewrite SIM right_id.
      rewrite /update. fold nb.
      destruct (dec nb nb); try nia.
      rewrite nth_error_repeat; [|nia].
      assert (BOOL: bool_decide (nb = nb ∧ (0 <= ofs < sz)%Z) = true).
      { apply bool_decide_eq_true_2. split; [reflexivity|nia]. }
      rewrite BOOL left_id OFS. ss.
    }
    (* b ≠ nb *)
    unfold update. fold nb. 
    destruct (dec nb b); try nia.

    rewrite -own_op.
     
    iPoseProof (own_valid with "P") as "%WF".
    dup WF. rewrite auth_both_valid_discrete in WF. ss; des.
    unfold included in *. des. specialize (WF b ofs). 
    rewrite !discrete_fun_lookup_op in WF.
    rewrite SZ in WF.
    case_bool_decide; try nia.
    (* destruct (dec b nb); destruct (bool_decide (0 <= ofs < sz)%Z); try nia. ss. *)
    rewrite ->!discrete_fun_lookup_singleton in *.
    rewrite right_id in WF.
    destruct SIM as [SIM NEXT]. 
    specialize (SIM b ofs). des; cycle 2.
    { 
      exfalso. unfold alloc_by_impl in SIM. des.
      rewrite SIM in WF. destruct (z b ofs); inv WF.
    } 
    { 
      exfalso. unfold not_allocated in SIM. des.
      rewrite SIM in WF. destruct (z b ofs); inv WF.
    }

    unfold alloc_by_spec in SIM. des.
    iPureIntro. exists v0.
    assert (BOOL: bool_decide (b = nb ∧ (0 <= ofs < 0 + Z.to_nat sz)%Z) = false).
    { rewrite SZ. apply bool_decide_eq_false_2. intros [EQ _]. subst. contradiction. }
    rewrite BOOL right_id SIM. split; [reflexivity|].
    rewrite /update. fold nb.
    destruct (dec nb b); [contradiction|exact SIM1].

  Qed.
    

  Lemma mem_ra_lookup_point b ofs q v
    (SIM: _sim_mem)
    :
    mem_own mem_name ((● mem_r)) ∗ (b, ofs) ⤇{q} v
    ⊢
    ⌜mem_r b ofs ≡ Some (to_frac_agree 1 (Some v)) ∧ (Mem.cnts mem_t) b ofs = Some v⌝.
  Proof using.
    iIntros "P". rewrite -own_op.
    iPoseProof (own_valid with "P") as "%WF".
    dup WF. rewrite auth_both_valid_discrete in WF. ss. des.
    unfold included in *. des. specialize (WF b ofs). iris_tac.
    rewrite ->!discrete_fun_lookup_singleton in *.
    destruct (SIM b ofs); unfold not_allocated, alloc_by_spec, alloc_by_impl in *; des; rewrite H in WF; swap 2 3.
    { destruct (z b ofs); ss; rewrite -?Some_op ?right_id in WF; inv WF. }
    { destruct (z b ofs); ss; rewrite -?Some_op ?right_id in WF; inv WF. }

    rewrite -WF. destruct (z b ofs); rr in WF; depdes WF.
    - assert (EXT: to_frac_agree q (Some v) ≼ to_frac_agree 1 (Some v0)) by (rewrite H2; et).
      eapply dfrac_agree_included in EXT. des; subst. inv EXT0. et.
    - eapply to_frac_agree_inv in H2. ss. des. depdes H3. et.
  Qed.

  Lemma mem_ra_lookup_list nb mem_r' mem_t' sz
    (SIM: sim_mem)
    (MEM: mem_t' = Mem.mk (update (Mem.cnts mem_t) (Mem.nb mem_t) (λ ofs : Z, if bool_decide (0 <= ofs < sz)%Z then Some Vundef else None)) (S (Mem.nb mem_t)))
    (MEMR: mem_r' = (mem_r ⋅ _points_to_r (Mem.nb mem_t, 0%Z) 1 (repeat Vundef (Z.to_nat sz))))
    :
    (mem_own mem_name ((● mem_r')) ∗ [∗ list] i↦v ∈ repeat Vundef (Z.to_nat sz), (nb, (0 + i)%Z) ⤇ v)%I
    ⊢
    ⌜∀ ofs (OFS: bool_decide (0 <= ofs < sz)%Z = true), ∃ v, mem_r' nb ofs ≡ Some (to_frac_agree 1 (Some v)) ∧ (Mem.cnts mem_t') nb ofs = Some v⌝.
  Proof using.
    iIntros "[P PTS] %ofs %P". rewrite MEMR.
    pose proof P as OFS.
    apply bool_decide_eq_true_1 in OFS.
    (* Search ([∗ list] _ ∈ _,  _)%I. *)
    iPoseProof (big_sepL_lookup_acc _ _ (Z.to_nat ofs) with "PTS") as "[PT PTS]".
    { eapply lookup_nth_inbounds. rewrite repeat_length. nia. }
    erewrite nth_repeat.
    assert (OFS_EQ: (0 + Z.to_nat ofs)%Z = ofs) by nia. rewrite OFS_EQ.
    iPoseProof (mem_ra_lookup with "[P PT]") as "%"; eauto; try iFrame.
  Qed.

  Lemma mem_ra_free b ofs v
    :
    mem_own mem_name ((● mem_r)) ∗ (b, ofs) ⤇{1} v
    ⊢ |==>
    mem_own mem_name ((● mem_ra_upd mem_r b ofs None)).
  Proof using _MEM.
    Local Transparent mem_points_to_singleton_r.
    iIntros "[Auth Frag]".
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r auth_update_dealloc //=.
    apply discrete_fun_local_update; intros b1.
    apply discrete_fun_local_update; intros o1.
    destruct (dec b1 b); subst.
    - rewrite discrete_fun_lookup_singleton.
      destruct (dec o1 ofs); subst.
      + rewrite ?discrete_fun_lookup_singleton /mem_ra_upd.
        case_bool_decide; [|naive_solver].
        apply delete_option_local_update; eauto; apply _.
      + rewrite discrete_fun_lookup_singleton_ne // /mem_ra_upd.
        case_bool_decide; [naive_solver|ss].
    - rewrite /mem_ra_upd. case_bool_decide; [naive_solver|].
      rewrite discrete_fun_lookup_singleton_ne; ss; eauto.
  Qed.


  Lemma mem_ra_store v_new v b ofs
    (SIM: _sim_mem)
    :
    mem_own mem_name ((● mem_r)) ∗ (b, ofs) ⤇{1} v
    ⊢ |==>
    mem_own mem_name ((● mem_ra_upd mem_r b ofs (Some (to_frac_agree 1 (Some v_new))))) ∗ (b, ofs) ⤇{1} v_new.
  Proof using.
    Local Transparent mem_points_to_singleton_r.
    iIntros "[Auth Frag]".
    iPoseProof ((mem_ra_lookup_point _ _ _ _ SIM) with "[Auth Frag]") as "%Hlu"; [iFrame|].
    destruct Hlu as [Hpt _].
    rewrite -own_op.
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r /= auth_update //.
    apply discrete_fun_local_update; intros b1.
    apply discrete_fun_local_update; intros o1.
    destruct (dec b1 b); subst.
    - destruct (dec o1 ofs); subst.
      + rewrite Hpt ?discrete_fun_lookup_singleton /mem_ra_upd.
        case_bool_decide; [|naive_solver].
        apply option_local_update, exclusive_local_update; ss.
      + rewrite ?discrete_fun_lookup_singleton /mem_ra_upd.
        case_bool_decide; [naive_solver|].
        rewrite ?discrete_fun_lookup_singleton_ne //.
    - rewrite /mem_ra_upd.
      case_bool_decide; [naive_solver|]; ss.
      assert (NE: b <> b1) by congruence.
      rewrite discrete_fun_lookup_singleton_ne; [|exact NE].
      rewrite discrete_fun_lookup_singleton_ne; [|exact NE].
      ss.
  Qed.

  Lemma mem_ra_cmp p0 q0 v0 p1 q1 v1 succ
    (SIM: _sim_mem)
    (CMP: HybMem.compare_val p0 p1 = Vint succ)
    :
    (mem_own mem_name (● mem_r) ∗ HybMem.val_r p0 q0 v0 ∗ HybMem.val_r p1 q1 v1)
    ⊢
    ⌜Mem.vcmp mem_t p0 p1 = Some (bool_decide (succ = 1))⌝.
  Proof using.
    iIntros "(B & P1 & P2)".
    destruct p0, p1; try destruct blkofs; try destruct blkofs0; ss.
    - des_ifs.
    - iPoseProof (mem_ra_lookup_point with "[B P2]") as "%"; et; iFrame.
      specialize (SIM n0 z). unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM; des; subst; ss.
      + rewrite SIM in H. r in H. depdes H.
      + rewrite SIM1. iPureIntro. des_ifs.
      + rewrite SIM in H. r in H. depdes H. 
    - destruct n; ss.
    - iPoseProof (mem_ra_lookup_point with "[B P1]") as "%"; et; iFrame.
      specialize (SIM n0 z). unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM; des; subst; ss.
      + rewrite SIM in H. rr in H. depdes H.
      + rewrite SIM1. iPureIntro. des_ifs.
      + rewrite SIM in H. rr in H. depdes H.
    - iPoseProof (mem_ra_lookup_point with "[B P1]") as "%"; et; iFrame.
      iPoseProof (mem_ra_lookup_point with "[B P2]") as "%"; et; iFrame.
      dup SIM. specialize (SIM n z). unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM; des; subst; ss; swap 2 3.
      { rewrite SIM in H. rr in H. depdes H. }
      { rewrite SIM in H. rr in H. depdes H. }
      specialize (SIM0 n0 z0). unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0; des; subst; ss; swap 2 3.
      { rewrite SIM0 in H0. rr in H0. depdes H0. }
      { rewrite SIM0 in H0. rr in H0. depdes H0. }
      rewrite SIM2 SIM4. s. des_ifs.
  Qed.

End RA.

Module MemDH. Section MemDH.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS}.

  Definition Ist: gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      ((∃ (mem_src mem_tgt: Mem.t) (mem_res: _memRA),
      ⌜st_src = {[HybMem.v_mem #  mem_src↑]} ∧ st_tgt = {[DetMem.v_mem # mem_tgt↑]}⌝ ∗ 
      ⌜mem_wf mem_src ∧ mem_wf mem_tgt ∧ (Mem.nb mem_src <= Mem.nb mem_tgt)⌝ ∗
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
    all: try (destruct i0; ss; try discriminate).
    all: try (destruct i1; ss; try discriminate).
    all: des_ifs; i; clarify; case_bool_decide; ss.
  Qed.

  Definition mem_get (mem: _memRA) b ofs :=
    match or_else (mem b ofs) (to_frac_agree 1 (Some Vundef)) with
    | (_,v) => or_else (nth_error v.(agree_car) 0) (Some Vundef)
    end.

  Lemma mem_get_sound mem b ofs v
      (HIT : mem b ofs ≡ Some (to_frac_agree 1 (Some v))) :
    mem_get mem b ofs = Some v.
  Proof using.
    rr in HIT. depdes HIT. rewrite /mem_get -x. s. destruct x0.
    symmetry in H. eapply to_frac_agree_inv in H. des. ss. subst.
    rewrite H0. et.
  Qed.

  Lemma simF_alloc : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.alloc).
  Proof using.
    cStartFunSim. rewrite /HybMem.alloc /DetMem.alloc.
    
    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM NEXT].
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
      cForceS (Mem.nb mem_tgt - Mem.nb mem_src). cStepsS.
      set (nb := Mem.nb mem_tgt).
      replace (Mem.nb mem_src + (nb - Mem.nb mem_src)) with nb by nia.
      assert (NB: ∀ ofs, mem_res nb ofs = None).
      { i. destruct (NEXT nb ofs (ltac:(nia))). ss. }

      cStepsT. cStep. iSplitR; [eauto|].
      iExists {[HybMem.v_mem #  _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _. fold nb.  
      iSplitR. { iPureIntro. esplits; try refl. }
      iSplitR.
      {
        iPureIntro. splits; ss.
        - ii. ss. unfold update in *. des_ifs. apply H2 in H. nia.
        - ii. ss. unfold update in *.  des_ifs. apply H4 in H. nia.
      }
      iFrame. iSplitL; eauto.
      iSplitL; cycle 1.
      {
        iPureIntro. i. unfold update, not_allocated. ss.
        destruct (dec nb b); try nia.
        eapply NEXT; nia.
      }

      iIntros "%b %ofs". destruct (dec nb b); subst; cycle 1.
      { (* nb ≠ b *)
        destruct (SIM b ofs).
        {
          iLeft. iPureIntro. 
          unfold not_allocated in *. des.
          esplits; ss; unfold update; des_ifs.
        }
        destruct H.
        {
          iRight. iLeft. iPureIntro.
          unfold alloc_by_spec in *. des.
          exists v0. esplits; ss; unfold update; des_ifs.
        }
        iRight. iRight. iPureIntro.
        unfold alloc_by_impl in *. des.
        exists v0. esplits; ss; unfold update; des_ifs.
      }
      (* nb = b *)
      destruct (bool_decide (0 <= ofs < v)%Z) eqn:SZ; cycle 1.
      {
        iLeft. iPureIntro. unfold not_allocated. s. unfold update.
        des_ifs.
      }
      iRight. iRight.
      unfold alloc_by_impl. ss.
      iPureIntro. unfold update; des_ifs; esplits; eauto.
    }

    (* using logical memory *)
    cStepsS. iDestruct "ASM" as "%SIZE". des. rename v into sz.
    case_bool_decide as SIZE'; cycle 1.
    { exfalso. nia. }
    destruct SIZE' as [SIZE2 SIZE3].
    cStepsT.
    cForceS (Mem.nb mem_tgt). cStepsS. 
    iPoseProof (mem_ra_alloc_next with "B") as ">[B W]"; eauto.

    iPoseProof (points_to_transform with "W") as "W".
    assert (SSIM: sim_mem mem_res mem_src mem_tgt).
    { unfold sim_mem. esplits; eauto. } 
    iPoseProof (mem_ra_lookup_list _ _ _ _ _ _ _ SSIM with "[B W]") as "%RES"; eauto.
    { iFrame. }

    cForcesS. iSplitL "W"; eauto. 
    (* cForcesS. iSplitR; eauto. cStepsS. *)
    set (nb := Mem.nb mem_tgt). cStepsS.

    cStep. iSplitR; eauto.
    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _.  
    iSplitR. { iPureIntro. esplits; try refl. }
    iSplitR. 
    {
      iPureIntro. splits; ss; try nia.
      ii. ss. unfold update in *.  des_ifs. apply H4 in H. nia. 
    }
    iFrame. iSplitL; eauto.
    iSplitL; cycle 1.
    {
      iPureIntro. i. unfold update, not_allocated. ss.
      do 2 rewrite discrete_fun_lookup_op.
      destruct (dec nb b); destruct (dec b nb); try nia.
      assert (BOOL:
        bool_decide
          (b = nb ∧
           (0 <= ofs < 0 + length (repeat Vundef (Z.to_nat sz)))%Z) = false).
      { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
      rewrite BOOL right_id.
      eapply NEXT; nia. 
    }

    iIntros "%b %ofs". destruct (dec nb b); subst; cycle 1.
    { (* nb ≠ b *)
      destruct (SIM b ofs).
      {
        iLeft. iPureIntro. 
        unfold not_allocated in *. des. ss.
        do 2 rewrite discrete_fun_lookup_op.
        destruct (dec b nb); try nia. ss. rewrite right_id.
        assert (BOOL:
          bool_decide
            (b = nb ∧
             (0 <= ofs < 0 + length (repeat Vundef (Z.to_nat sz)))%Z) = false).
        { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
        rewrite BOOL right_id.
        esplits; ss; unfold update; des_ifs.
      }
      destruct H.
      {
        iRight. iLeft. iPureIntro.
        unfold alloc_by_spec in *. des.
        exists v. esplits; ss; unfold update; des_ifs.
        do 2 rewrite discrete_fun_lookup_op.
        destruct (dec b nb); try nia. ss.
        assert (BOOL:
          bool_decide
            (b = nb ∧
             (0 <= ofs < 0 + length (repeat Vundef (Z.to_nat sz)))%Z) = false).
        { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
        rewrite BOOL right_id. ss.
      }
      iRight. iRight. iPureIntro.
      unfold alloc_by_impl in *. des.
      exists v. esplits; ss; unfold update; des_ifs.
      do 2 rewrite discrete_fun_lookup_op.
      destruct (dec b nb); try nia. ss.
      assert (BOOL:
        bool_decide
          (b = nb ∧
           (0 <= ofs < 0 + length (repeat Vundef (Z.to_nat sz)))%Z) = false).
      { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
      rewrite BOOL right_id. ss.
    }
    (* nb = b *)
    specialize (NEXT nb ofs (ltac:(nia))). 
    unfold not_allocated in NEXT; des.
    assert (Z.add 0 (Z.to_nat sz) = sz) by nia.

    destruct (bool_decide (0 <= ofs < sz)%Z) eqn:SZ; cycle 1.
    {
      iLeft. iPureIntro. unfold not_allocated. unfold update. s.
      do 2 rewrite discrete_fun_lookup_op.
      rewrite repeat_length H.
      pose proof SZ as SZ_FALSE.
      apply bool_decide_eq_false_1 in SZ_FALSE.
      assert (BOOL: bool_decide (nb = nb ∧ (0 <= ofs < sz)%Z) = false).
      { apply bool_decide_eq_false_2. intros [_ RANGE]. exact (SZ_FALSE RANGE). }
      rewrite BOOL NEXT right_id.
      destruct (dec nb nb); [|nia].
      rewrite SZ. esplits; eauto.
    }
    iRight. iLeft. iPureIntro.
    unfold alloc_by_spec. ss.
    pose proof SZ as SZ_RANGE.
    apply bool_decide_eq_true_1 in SZ_RANGE.
    do 2 rewrite discrete_fun_lookup_op.
    unfold update. destruct (dec nb nb); ss.
    rewrite repeat_length H nth_error_repeat; [|nia].
    assert (BOOL: bool_decide (nb = nb ∧ (0 <= ofs < sz)%Z) = true).
    { apply bool_decide_eq_true_2. split; [reflexivity|exact SZ_RANGE]. }
    rewrite BOOL NEXT left_id SZ. esplits; eauto.

  (* SLOW *)Qed.

  Lemma simF_free : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.free).
  Proof using.
    cStartFunSim. rewrite /HybMem.free /DetMem.free.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM NEXT].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT.
    destruct _q; cycle 1.
    { (* physical memory *)
      cStepsS. cSimpl. cStepsS.
      destruct v as [b ofs]. 
      hexploit (SIM b ofs). intro SIM0.
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
      rewrite /Mem.free.
      des; des_ifs; cStepsS; des_ifs.
      cStepsT. 
      cStep. iSplit; eauto.

      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      {
        iPureIntro. splits; ss; try nia.
        - ii. ss. unfold update in *.
          des_ifs; eapply H2; eauto.
        - ii. ss. unfold update in *.
          des_ifs; eapply H4; eauto.
      }
      iFrame. iSplit; eauto.
      iSplitL; cycle 1.
      {
        iPureIntro. i. specialize (NEXT b0 ofs0 OUT).
        unfold not_allocated, update in *. ss. des.
        destruct (dec b b0); esplits; eauto; des_ifs.
      }
      iPureIntro. ii. unfold not_allocated, alloc_by_spec, alloc_by_impl, update; ss.
      des_ifs; esplits; eauto. 
    }

    (* logical memory *)
    cStepsS. 
    iDestruct "ASM" as ( ? ) "POINTS".
    destruct v as [b ofs].

    iPoseProof (mem_ra_lookup_point with "[B POINTS]") as "%P"; [eauto|iFrame|].
    des. rewrite /Mem.free.
    rewrite P0. cStepsT.

    iPoseProof (mem_ra_free with "[B POINTS]") as ">P"; iFrame.
    
    cStep. iSplit; eauto.
    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _.  iSplit. { iPureIntro. esplits; try refl. }
    iSplitR.
    {
      iPureIntro. splits; ss; try nia.
      ii. ss. unfold update in *. des_ifs; eapply H4; eauto.
    }
    iFrame; iSplit; eauto.
    iPureIntro.
    assert (BLT: b < Mem.nb mem_tgt) by (eapply H4; exact P0).
    split; cycle 1.
    {
      intros b1 ofs1 OUT.
      specialize (NEXT b1 ofs1 OUT).
      destruct NEXT as [Hra [Hsrc Htgt]].
      unfold not_allocated, mem_ra_upd, update.
      destruct (dec b b1) as [EQb|NEb].
      - subst. simpl in OUT. nia.
      - case_bool_decide; [naive_solver|].
        destruct (dec b b1); [contradiction|].
        split; [exact Hra|].
        split; [exact Hsrc|].
        cbn.
        destruct (dec b b1); [contradiction|exact Htgt].
    }
    intros b1 ofs1.
    specialize (SIM b1 ofs1).
    unfold mem_ra_upd, update.
    destruct (dec b b1) as [EQb|NEb].
    - subst b1.
      destruct (dec ofs ofs1) as [EQofs|NEofs].
      + subst ofs1.
        left. unfold not_allocated.
        destruct SIM as [SIMna|[SIMsp|SIMimpl]].
        * unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
          rewrite Hra0 in P. inv P.
        * unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1 [Hra0 [Hsrc0 Htgt0]]].
          case_bool_decide; [|naive_solver].
          destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs); [|contradiction].
          split; [reflexivity|].
          split; [exact Hsrc0|].
          cbn.
          destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs); [reflexivity|contradiction].
        * unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1 [Hra0 [Hsrc0 Htgt0]]].
          rewrite Hra0 in P. inv P.
      + destruct (dec b b); [|contradiction].
        destruct (dec ofs ofs1); [contradiction|].
        assert (BOOL: bool_decide (b = b ∧ ofs = ofs1) = false).
        { apply bool_decide_eq_false_2. intros [_ EQ]. contradiction. }
        destruct SIM as [SIMna|[SIMsp|SIMimpl]].
        * left. unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
          split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|exact Htgt0].
        * right. left. unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1 [Hra0 [Hsrc0 Htgt0]]].
          exists v1. split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|exact Htgt0].
        * right. right. unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1 [Hra0 [Hsrc0 Htgt0]]].
          exists v1. split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|exact Htgt0].
    - destruct (dec b b1); [contradiction|].
      assert (BOOL: bool_decide (b = b1 ∧ ofs = ofs1) = false).
      { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
      destruct SIM as [SIMna|[SIMsp|SIMimpl]].
      + left. unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
        split; [rewrite BOOL; exact Hra0|].
        split; [exact Hsrc0|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt0].
      + right. left. unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1 [Hra0 [Hsrc0 Htgt0]]].
        exists v1. split; [rewrite BOOL; exact Hra0|].
        split; [exact Hsrc0|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt0].
      + right. right. unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1 [Hra0 [Hsrc0 Htgt0]]].
        exists v1. split; [rewrite BOOL; exact Hra0|].
        split; [exact Hsrc0|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt0].
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.load).
  Proof using.
    cStartFunSim. rewrite /HybMem.load /DetMem.load.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM NEXT].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT.
    destruct _q; cycle 1.
    { (* physical memory *)
      cStepsS. cSimpl. cStepsS.
      destruct v as [b ofs].
      hexploit (SIM b ofs). intro SIM0.
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
    destruct v as [b ofs].
    hexploit (SIM b ofs). intro SIM0.
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
    destruct SIM as [SIM NEXT].
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. destruct v as [[b ofs] v]. cStepsT.
    cStepsS.
    destruct _q; cycle 1.
    { (* physical memory *)
      cStepsS.
      hexploit (SIM b ofs). intro SIM0.
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
      des; des_ifs; cStepsS; ss. cStepsT. 
      cStep. iSplit; [eauto|].

      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia. 
        - ii. ss. unfold update in *.
          des_ifs; eapply H2; eauto. 
          destruct (dec b b0); destruct (dec ofs ofs0); ss; subst.
          eapply Heq1.
        - ii. ss. unfold update in *.
          des_ifs; eapply H4; eauto.
          destruct (dec b b0); destruct (dec ofs ofs0); ss; subst.
          eapply Heq2.
      }
      iFrame. iSplit; eauto.
      iPureIntro. split; cycle 1.
      {
        i. specialize (NEXT b0 ofs0 OUT).
        unfold not_allocated, update in *. ss. des.
        destruct (dec b b0); destruct (dec ofs ofs0); esplits; eauto; des_ifs. 
      }
      ii. unfold not_allocated, alloc_by_spec, alloc_by_impl, update; ss.
      des_ifs; esplits; eauto. 
      destruct (dec b b0); destruct (dec ofs ofs0); des_ifs.
      right. right. eauto. 
    }

    (* logical memory *)
    cStepsS. iDestruct "ASM" as ( ? )  "ASM".
    iPoseProof (mem_ra_lookup_point with "[B ASM]") as "%POINT"; [eauto|iFrame|].
    
    hexploit (SIM b ofs). intro SIM0. 
    unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0.
    des; des_ifs; cycle 1. { rewrite SIM0 in POINT. inv POINT. }

    iPoseProof (mem_ra_store with "[B ASM]") as ">[B P]"; [eauto|iFrame|].
    cForcesS. iSplitL "P"; eauto. cStepsS.

    cStepsT. cStep. iSplit; [eauto|].

    iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
    instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
    iExists _, _, _.  
    iSplit. { iPureIntro. esplits; try refl. }
    iSplitR. 
    { iPureIntro. splits; ss; try nia. 
      ii. ss. unfold update in *.
      des_ifs; eapply H4; eauto.
      destruct (dec b b0); destruct (dec ofs ofs0); ss; subst.
      eapply Heq1.
    }
    iFrame. iSplit; eauto.
    iPureIntro. split; cycle 1.
    {
      intros b1 ofs1 OUT.
      assert (BLT: b < Mem.nb mem_tgt) by (eapply H4; exact Heq1).
      specialize (NEXT b1 ofs1 OUT).
      destruct NEXT as [Hra [Hsrc Htgt]].
      unfold mem_ra_upd, not_allocated, update.
      destruct (dec b b1) as [EQb|NEb].
      - subst. simpl in OUT. nia.
      - case_bool_decide; [naive_solver|].
        destruct (dec b b1); [contradiction|].
        split; [exact Hra|].
        split; [exact Hsrc|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt].
    }
    intros b1 ofs1.
    specialize (SIM b1 ofs1).
    unfold mem_ra_upd, update.
    destruct (dec b b1) as [EQb|NEb].
    - subst b1.
      destruct (dec ofs ofs1) as [EQofs|NEofs].
      + subst ofs1.
        right. left. exists v.
        split.
        * case_bool_decide; [reflexivity|naive_solver].
        * split; [exact SIM1|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs); [reflexivity|contradiction].
      + assert (BOOL: bool_decide (b = b ∧ ofs = ofs1) = false).
        { apply bool_decide_eq_false_2. intros [_ EQ]. contradiction. }
        destruct (dec b b); [|contradiction].
        destruct (dec ofs ofs1); [contradiction|].
        destruct SIM as [SIMna|[SIMsp|SIMimpl]].
        * left. unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
          split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|exact Htgt0].
        * right. left. unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1 [Hra0 [Hsrc0 Htgt0]]].
          exists v1. split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|exact Htgt0].
        * right. right. unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1 [Hra0 [Hsrc0 Htgt0]]].
          exists v1. split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|exact Htgt0].
    - assert (BOOL: bool_decide (b = b1 ∧ ofs = ofs1) = false).
      { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
      destruct (dec b b1); [contradiction|].
      destruct SIM as [SIMna|[SIMsp|SIMimpl]].
      + left. unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
        split; [rewrite BOOL; exact Hra0|].
        split; [exact Hsrc0|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt0].
      + right. left. unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1 [Hra0 [Hsrc0 Htgt0]]].
        exists v1. split; [rewrite BOOL; exact Hra0|].
        split; [exact Hsrc0|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt0].
      + right. right. unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1 [Hra0 [Hsrc0 Htgt0]]].
        exists v1. split; [rewrite BOOL; exact Hra0|].
        split; [exact Hsrc0|].
        cbn. destruct (dec b b1); [contradiction|exact Htgt0].
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.cmp).
  Proof using.
    cStartFunSim. rewrite /HybMem.cmp /DetMem.cmp.

    iDestruct "IST" as (? ? ? ?) "(% & [% [% [% [% [% [% [%SIM >B]]]]]]] & %)". des; subst; cSimpl.
    destruct SIM as [SIM NEXT].
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
    destruct (Mem.vcmp mem_tgt arg0 arg1) as [r|] eqn: E; ss; cycle 1.
    {
      exfalso. unfold Mem.vcmp in *; ss. 
      destruct arg0 eqn: ARG0; destruct arg1 eqn: ARG1; ss.
      - destruct blkofs as [b ofs]. specialize (SIM b ofs). 
        unfold not_allocated, alloc_by_spec, alloc_by_impl in *; des;
        rewrite SIM0 in S; rewrite SIM1 in E; des_ifs.
      - destruct blkofs as [b ofs]. specialize (SIM b ofs). 
        unfold not_allocated, alloc_by_spec, alloc_by_impl in *; des;
        rewrite SIM0 in S; rewrite SIM1 in E; des_ifs.
      - destruct blkofs as [b ofs]; destruct blkofs0 as [b0 ofs0].
        hexploit (SIM b0 ofs0). intro SIM0. specialize (SIM b ofs).
        unfold not_allocated, alloc_by_spec, alloc_by_impl in *; des;
        rewrite SIM3 SIM1 in S; rewrite SIM4 SIM2 in E; des_ifs.
      - destruct blkofs as [b ofs]. ss. 
    }
    cStepsT.
    destruct arg0 eqn: ARG0; destruct arg1 eqn: ARG1; ss.
    - rewrite S in E. inv E.
      cStep. iSplit; eauto. 
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia. } 
      iFrame. iSplit; eauto.
    - destruct blkofs as [b ofs]. hexploit (SIM b ofs). intro SIM0. 
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0; des;     
      rewrite SIM1 in S; rewrite SIM2 in E; des_ifs.
      cStep. iSplit; eauto. 
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia. } 
      iFrame. iSplit; eauto.        
    - destruct blkofs as [b ofs]. hexploit (SIM b ofs). intro SIM0. 
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0; des;     
      rewrite SIM1 in S; rewrite SIM2 in E; des_ifs.
      cStep. iSplit; eauto. 
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia. } 
      iFrame. iSplit; eauto.        
    - destruct blkofs as [b ofs]; destruct blkofs0 as [b0 ofs0].
      hexploit (SIM b0 ofs0). intro SIM0. hexploit (SIM b ofs). intro SIM1.
      unfold not_allocated, alloc_by_spec, alloc_by_impl in SIM0, SIM1; des;
      rewrite SIM4 SIM2 in S; rewrite SIM5 SIM3 in E; ss.
      rewrite S in E. inv E.
      cStep. iSplit; eauto. 
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia. } 
      iFrame. iSplit; eauto. 
    - destruct blkofs; ss.
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open HybMem DetMem IstFull (fid MemHdr.cas).
  Proof using.
    cStartFunSim. rewrite /HybMem.cas /DetMem.cas.
    cStepsS. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. rewrite {1}/unwrapU. des_ifs; cycle 1.
    { cStepsS. des_ifs. }
    cStepsS. cStepsT. 
    destruct v as [[b ofs] [v_old v_new]]. cStepsS.

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
    destruct SIM as [SIM NEXT]. cStepsS.
    destruct _q as [[[v_cur succ] [v0 q0]] [v1 q1]]. cStepsS.
    iDestruct "ASM" as "(%CMP & CUR & CMP0 & CMP1)". cStepsT.

    cInlineT. cStepsT.
    iPoseProof (mem_ra_lookup_point with "[B CUR]") as "%PT"; [eauto|iFrame|]. des.
    pose proof (SIM b ofs) as SIMCUR.
    unfold not_allocated, alloc_by_spec, alloc_by_impl in SIMCUR.
    destruct SIMCUR as [SIMna|[SIMsp|SIMimpl]].
    { destruct SIMna as [Hra _]. rewrite Hra in PT. inv PT. }
    2: { destruct SIMimpl as [v2 [Hra _]]. rewrite Hra in PT. inv PT. }
    destruct SIMsp as [v2 [SIM0 [SIM1 SIM2]]].
    rewrite PT0. cStepsT.
    cInlineT. cStepsT.
    iPoseProof (mem_ra_cmp with "[B CUR CMP0 CMP1]") as "%CP"; eauto; [iFrame|].
    rewrite CP. cStepsT.

    repeat case_bool_decide; simplify_eq.
    - cStepsT. cInlineT. cStepsT. rewrite PT0. cStepsT.
      iPoseProof (mem_ra_store with "[B CUR]") as ">[B P]"; [eauto|iFrame|].
      cForcesS. iSplitR "B"; iFrame. cStepsS.
      cStep; iFrame.
      iSplit; eauto.
      iExists {[HybMem.v_mem # _↑]}, _, st_tgtR, st_tgtR.
      instantiate (1 := {[DetMem.v_mem # _↑]}). repeat (iSplit; eauto).
      iExists _, _.  
      iSplit. { iPureIntro. esplits; try refl. }
      iSplitR. 
      { iPureIntro. splits; ss; try nia.
        ii. ss. unfold update in *.
        des_ifs; eapply H4; eauto.
        destruct (dec b b0); destruct (dec ofs ofs0); ss; subst.
        eapply PT0.
      }
      iFrame. iSplit; eauto.
      iPureIntro. split; cycle 1.
      {
        intros b1 ofs1 OUT.
        assert (BLT: b < Mem.nb mem_tgt) by (eapply H4; exact PT0).
        specialize (NEXT b1 ofs1 OUT).
        destruct NEXT as [Hra [Hsrc Htgt]].
        unfold mem_ra_upd, not_allocated, update.
        destruct (dec b b1) as [EQb|NEb].
        - subst. simpl in OUT. nia.
        - case_bool_decide; [naive_solver|].
          destruct (dec b b1); [contradiction|].
          split; [exact Hra|].
          split; [exact Hsrc|].
          cbn. destruct (dec b b1); [contradiction|exact Htgt].
      }
      intros b1 ofs1.
      specialize (SIM b1 ofs1).
      unfold mem_ra_upd, update.
      destruct (dec b b1) as [EQb|NEb].
      + subst b1.
        destruct (dec ofs ofs1) as [EQofs|NEofs].
        * subst ofs1.
          right. left. exists v_new.
          split.
          { case_bool_decide; [reflexivity|naive_solver]. }
          { split; [exact SIM1|].
            cbn. destruct (dec b b); [|contradiction].
            destruct (dec ofs ofs); [reflexivity|contradiction]. }
        * assert (BOOL: bool_decide (b = b ∧ ofs = ofs1) = false).
          { apply bool_decide_eq_false_2. intros [_ EQ]. contradiction. }
          destruct (dec b b); [|contradiction].
          destruct (dec ofs ofs1); [contradiction|].
          destruct SIM as [SIMna|[SIMsp|SIMimpl]].
          { left. unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
            split; [rewrite BOOL; exact Hra0|].
            split; [exact Hsrc0|].
            cbn. destruct (dec b b); [|contradiction].
            destruct (dec ofs ofs1); [contradiction|exact Htgt0]. }
          { right. left. unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1' [Hra0 [Hsrc0 Htgt0]]].
            exists v1'. split; [rewrite BOOL; exact Hra0|].
            split; [exact Hsrc0|].
            cbn. destruct (dec b b); [|contradiction].
            destruct (dec ofs ofs1); [contradiction|exact Htgt0]. }
          { right. right. unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1' [Hra0 [Hsrc0 Htgt0]]].
            exists v1'. split; [rewrite BOOL; exact Hra0|].
            split; [exact Hsrc0|].
            cbn. destruct (dec b b); [|contradiction].
            destruct (dec ofs ofs1); [contradiction|exact Htgt0]. }
      + assert (BOOL: bool_decide (b = b1 ∧ ofs = ofs1) = false).
        { apply bool_decide_eq_false_2. intros [EQ _]. contradiction. }
        destruct (dec b b1); [contradiction|].
        destruct SIM as [SIMna|[SIMsp|SIMimpl]].
        { left. unfold not_allocated in SIMna. destruct SIMna as [Hra0 [Hsrc0 Htgt0]].
          split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b1); [contradiction|exact Htgt0]. }
        { right. left. unfold alloc_by_spec in SIMsp. destruct SIMsp as [v1' [Hra0 [Hsrc0 Htgt0]]].
          exists v1'. split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b1); [contradiction|exact Htgt0]. }
        { right. right. unfold alloc_by_impl in SIMimpl. destruct SIMimpl as [v1' [Hra0 [Hsrc0 Htgt0]]].
          exists v1'. split; [rewrite BOOL; exact Hra0|].
          split; [exact Hsrc0|].
          cbn. destruct (dec b b1); [contradiction|exact Htgt0]. }
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
