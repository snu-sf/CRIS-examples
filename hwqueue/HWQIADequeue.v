Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI HWQA SchTactics.
From stdpp Require Import streams list.

Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !memGS, !prophGS, !hwqGS}.
  Context (mnh mnp : string).
  Context (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (∃ (X : gset val),
      free_id (λ x, x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type ∗
      [∗ set] x ∈ X, ∃ ptr ofs, ⌜x = Vptr (ptr, ofs)⌝ ∗ ∃ v, (ptr, ofs) ↦{1/2} v)%I.
  Definition IstFull : ist_type Σ := IstHelp_gen Ist mnh ⊤.

  Notation HWQM := (HWQM.t mnh).
  Notation HWQP := (HWQP.t mnp).
  Notation HelpOn := (HelpingOn.t mnh HWQM.jobCode).
  Notation HelpDummy := (HelpingDummy.t mnh).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mnp ∅).

  Lemma simF_dequeue :
    ISim.sim_fun open
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA) ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      IstFull (fid HWQHdr.dequeue).
  Proof.
    cStartFunSim. rewrite /HWQA.dequeue /HWQP.dequeue; cStepsS; cStepsT.
    aStepS (N γq) "[%q [%n [%sz [-> #Hinv]]]]".
    iDestruct "Hinv" as (γb γi γc γs γh blk ->) "#Inv". cStepsT. aAddY. sYields.

    iApply wsim_reset.
    cCoind CIH g __ with st_src st_tgt. iIntros "[#Inv IST]".
    set (tgt_out := λ _ : (), _) at 2.
    aUnfoldT. rewrite {1}/tgt_out. sYields.

    iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
    iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
    mLoadT "H_sz".
    iMod ("Close" with "[//] [$] IST") as "> > IST".
    clear back pvs pref rest slots deqs cont.

    sYields. rewrite left_id.

    iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
    iDestruct "HInv" as (back pvs pref rest cont slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
    mLoadT "H_back".

    (* If there is a contradiction, remember that. *)
    iAssert (match cont with
            | NoCont _       => True
            | WithCont i1 i2 => contra γc i1 i2
            end)%I with "[Hcont]" as "#Hinit_cont".
    { destruct cont as [i1 i2|bs]; [ by iDestruct "Hcont" as "#C" | done ]. }
    (* We remember the current back value. *)
    iMod (back_snapshot with "Hb●") as "[Hb● Hback_snap]".
    iMod (i2_lower_bound_snapshot with "Hi●") as "[Hi● Hi2_lower_bound]".
    (* We close the invariant again. *)
    iMod ("Close" with "[//] [$] IST") as "> > IST".
    clear pref rest slots deqs pvs.
    sYields. rewrite /HWQP.dequeue_aux. sYields.
    set (tgt_in := λ _ : nat, _).

    (* The range is the min between [q.back - 1] and [q.size - 1]. *)
    (* We now prove the inner loop part by induction in the index. *)
    replace (Z.to_nat (sz `min` back)) with (back `min` sz) by lia.
    assert (back `min` sz ≤ back `min` sz) as Hn by done.
    assert (match cont with
          | NoCont _      => True
          | WithCont i1 _ => back `min` sz - back `min` sz ≤ i1
          end) as Hcont_i1 by (destruct cont as [i1 _|_]; lia).
    revert Hn Hcont_i1. rename n into idx. generalize (back `min` sz) at 1 4 6 as n.
    intros n Hn Hcont_i1.
    iInduction n as [|n] "IH_loop" forall (st_src st_tgt Hn Hcont_i1).
    { aUnfoldT. rewrite {1}/tgt_in. sYields. cByCoind CIH. iFrame. eauto.
    }
    aUnfoldT. rewrite {2}/tgt_in. cStepsT.
    sYields.
    (* Now the induction case: we need to open the invariant for the load. *)
    iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
    iDestruct "HInv" as (back' pvs pref rest cont' slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
    (* We use our snapshot to show that back is smaller that back'. *)
    iDestruct (back_le with "Hb● Hback_snap") as %Hback.
    (* We define the loop index as [i]. *)
    pose (i := (back `min` sz) - S n).
    assert ((Z.to_nat (sz `min` back)) - S n = i)%nat as -> by lia.
    iPoseProof (big_sepL_lookup_acc _ _ (i) with "H_ar") as "[↦ H_ar]".
    { apply array_content_lookup; lia. }
    rewrite left_id (comm _ 2%Z). mLoadT "↦".
    (* If there was an initial contradiction, it is still here. *)
    iAssert ⌜match cont with
            | NoCont _       => True
            | WithCont i1 i2 => cont' = cont ∧ (back `min` sz - S n ≤ i1)
            end⌝%I as %Hinitial_cont.
    { destruct cont as [i1 i2|bs]; destruct cont' as [i1' i2'|bs']; try done.
      - iDestruct (contra_agree with "Hinit_cont Hcont") as %[-> ->].
        iPureIntro. split; first done. lia.
      - by iDestruct (contra_not_no_contra with "Hcont Hinit_cont") as "False". }
    iPoseProof ("H_ar" with "↦") as "H_ar".
    (* We then reason by cas on the physical contents of slot [i]. *)
    destruct (decide (array_get slots deqs i = Vint 0)) as [Hi_NULL|Hi_not_NULL].
    { rewrite Hi_NULL.
      iMod ("Close" with "[-IST Hback_snap Hi2_lower_bound] IST") as "> > IST".
      { iFrame. iPureIntro; repeat split_and; des; eauto. }
      sYields. rewrite Nat.sub_0_r.
      iApply ("IH_loop" with "[] [] Hback_snap Hi2_lower_bound IST").
      - iPureIntro. lia.
      - iPureIntro. destruct cont as [i1 i2|bs]; last done.
        destruct Hinitial_cont as [-> Hi1].
        destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6).
        apply Nat.lt_eq_cases in Hcont_i1 as [Ha|Ha]; rewrite -/i in Ha; first by lia.
        exfalso. subst i1.
        assert (is_Some (slots !! i)) as [d Hslots_i] by (apply Hslots; lia).
        destruct d as [[li si] wi]. rewrite /array_get Hslots_i /= in Hi_NULL.
        apply HC5; rewrite /array_get Hslots_i; eauto.
    }
    (* We know that a non-null value [li] at index [i], we get a witness. *)
    assert (is_Some (slots !! i)) as [[[li si] wi] Hslots_i].
    { rewrite /array_get in Hi_not_NULL. destruct (slots !! i) as [d|]; last done. by eexists. }
    assert (array_get slots deqs i = li) as ->.
    { rewrite /array_get Hslots_i /=. rewrite /array_get Hslots_i in Hi_not_NULL.
      revert Hi_not_NULL. destruct (decide (i ∈ deqs)); intros ?; first done.
      by destruct wi. }
    iMod (val_wit_from_auth γs i li with "Hs●") as "[Hs● #Hval_wit_i]"; first by rewrite Hslots_i.
    pose proof Hlem as Hlem2; specialize (Hlem2 i li); rewrite Hslots_i /= in Hlem2.
    destruct Hlem2 as [->|[iblk [iofs ->]]]; auto.
    { rewrite /array_get Hslots_i //= in Hi_not_NULL; repeat case_match; ss. }
    iDestruct (big_sepM_lookup_acc with "Hbig") as "[Hq Hbig]"; first apply Hslots_i.
    iDestruct "Hq" as "[[%q [%iv [Hi1 Hi2]]] Hi3] /=".
    iPoseProof ("Hbig" with "[Hi2 Hi3]") as "Hbig"; first iFrame.

    (* Close the invariant and clean up the context. *)
    iMod ("Close" with "[-Hi1 Hback_snap Hi2_lower_bound IST] IST") as ">> IST".
    { iFrame; iPureIntro; repeat split_and; eauto; try by des. }

    clear Hslots Hstate Hpref Hdeqs Hcont Hinitial_cont Hback back' Hpvs_OK Hlem.
    clear pvs pref rest cont' Hslots_i si wi Hi_not_NULL slots deqs.
    sYields.
    (* Finally, the interesting where the cell was non-NULL on the load. *)
    iInv "Inv" with "[IST]" as "[IST HInv]" "Close"; first by iFrame.
    iDestruct "HInv" as (back' pvs pref rest cont' slots deqs) "HInv".
    iDestruct "HInv" as "[H_sz [H_back [H_ar [Hb● [Hi● [He● [Hs● HInv]]]]]]]".
    iDestruct "HInv" as "[Hproph [Hbig [Hcont Hpures]]]".
    iDestruct "Hpures" as %(Hslots & Hstate & Hpref & Hdeqs & Hpvs_OK & Hcont & Hlem).
    destruct Hpvs_OK as (Hpvs_ND & Hpvs_sz).
    (* If there was an initial contradiction, it is still here. *)
    iAssert ⌜match cont with
            | NoCont _       => True
            | WithCont i1 i2 => cont' = cont ∧ back `min` sz - S n ≤ i1
            end⌝%I as %Hinitial_cont.
    { destruct cont as [i1 i2|bs]; destruct cont' as [i1' i2'|bs']; try done.
      - iDestruct (contra_agree with "Hinit_cont Hcont") as %[-> ->].
        iPureIntro. split; first done. destruct Hcont as (((? & ?) & ?) & _). done.
      - by iDestruct (contra_not_no_contra with "Hcont Hinit_cont") as "False". }

    (* We reason by case on the success of the CAS. *)
    iDestruct (array_contents_cases γs slots deqs with "Hs● Hval_wit_i") as %[Hi|Hi].
    * (* The CmpXchg succeeded. *) iClear "IH_loop".
      assert (array_content sz slots deqs !! i = Some (Vptr (iblk, iofs))).
      { rewrite array_content_lookup; last by lia. by rewrite Hi. }
      (* Note that [i] is used (otherwise the CmpXchg would have failed). *)
      iDestruct (use_val_wit with "Hs● Hval_wit_i") as %Hval_wit_i.
      iDestruct (back_le with "Hi● Hi2_lower_bound") as %Hi2.
      assert (is_Some (slots !! i)) as [[[dl ds] dw] Hslots_i].
      { destruct (slots !! i) as [d|]; [ by exists d | by inversion Hval_wit_i ]. }
      assert (dl = Vptr (iblk, iofs)) as Hdl_li; last subst dl.
      { rewrite Hslots_i in Hval_wit_i. by inversion Hval_wit_i. }
      (* We now reason by case on whether the enqueue at [i] was committed. *)
      destruct (was_committed (Vptr (iblk, iofs), ds, dw)) eqn:Hcommitted.
      { (* We first consider the case where it was committed. *)
        (* If [i] has been dequeued alread: contradiction. *)
        assert (i ∉ deqs) as Hi_not_deq.
        { intros Hi_deq. specialize (Hdeqs i Hi_deq) as (Ha1 & ? & ?).
          rewrite Hslots_i /= in Ha1. inversion Ha1; subst dw.
          rewrite /array_get Hslots_i in Hi. rewrite decide_True in Hi; last done.
          inversion Hi. }
        iPoseProof (big_sepL_insert_acc _ _ (i) with "H_ar") as "[Hi H_ar]".
        { rewrite array_content_lookup; last by lia. by auto. }
        assert (dw = true) as ->.
        { rewrite /array_get Hslots_i decide_False in Hi; last done.
          rewrite /physical_value in Hi. destruct dw; first done. by inversion Hi. }
        iApply (wsim_mem_cas with "Hi Hi1 []"); [simpl_map; s; f_equal|ss|..].
        { rewrite /MemA.compare_val /array_get Hslots_i decide_False //.
          ss; case_bool_decide; first refl; naive_solver.
        }
        { iIntros "[? ?] !>"; iExists (q/2/2)%Qp, (q/2/2)%Qp, iv, iv.
          rewrite /array_get Hslots_i ?decide_False //=; iFrame.
          iIntros "[a ?]"; iSplitL "a"; iFrame; auto.
        }
        case_bool_decide; last ss.
        iIntros "Hi Hi2". cStepsT. iPoseProof ("H_ar" with "Hi") as "H_ar".
        rewrite /array_get Hslots_i ?decide_False //= bool_decide_eq_true_2 //.
        (* We resolve. *)
        iDestruct "Hproph" as (p str rs) "[Hp Hpvs]". iDestruct "Hpvs" as %Hpvs.
        cInlineT. cForceT (_, existT _ (p, rs, (i, true))). cForcesT. iSplitL "Hp".
        { repeat iSplit; eauto. }
        cStepsT. iDestruct "GRT" as "[-> [[-> %Hp] Hp]]".
        pose proof (stake_S p (length rs)) as Htemp; simpl in Htemp.
        rewrite Htemp in Hp; clear Htemp. rewrite reverse_cons app_inj_tail_iff in Hp.
        destruct Hp as [Hp1 Hp2]; symmetry in Hp2.
        destruct Hpvs as [-> [fuel [Hpvs ->]]].
        rewrite (lookup_list_stream_app_r _ str (length rs)) in Hp2; last by rewrite length_reverse.
        rewrite length_reverse Nat.sub_diag /= in Hp2.
        destruct pref as [|i' new_pref].
        { exfalso. destruct cont as [i1 i2|_].
          - destruct Hinitial_cont as [-> Hi1].
            destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
            destruct fuel as [|fuel]; first apply prefix_nil_inv in HC8; first inv HC8.
            simpl in HC8; rewrite Hp2 decide_True in HC8; last (split; eauto; try lia).
            destruct HC8 as [junk HEq].
            inversion HEq as [[HEq1 HEq2]]. lia.
          - destruct cont' as [i1' i2'|bs].
            + destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
              destruct fuel as [|fuel]; first apply prefix_nil_inv in HC8; first inv HC8.
              simpl in HC8; rewrite Hp2 decide_True in HC8; last (split; eauto; try lia).
              destruct HC8 as [junk HEq].
              inversion HEq as [[HEq1 HEq2]]. lia.
            + destruct Hcont as (HC1 & HC2 & HC3).
              destruct bs as [|[b_u b_ps] bs]; first inversion HC3 as [HC4].
              { specialize (Hpvs 0 i); rewrite HC4 in Hpvs.
                hexploit Hpvs; eauto; last by set_solver+.
                lia.
              }
              simpl in HC3. inversion HC3 as [[HEq1 HEq2]].
              assert (block_valid slots (b_u, b_ps)) as [Hvalid _] by apply HC1, elem_of_list_here.
              destruct fuel as [|fuel]; ss.
              rewrite Hp2 decide_True in HEq1; last by (split; [auto|lia]).
              inversion HEq1 as [Heq1].
              rewrite /= -Heq1 Hslots_i in Hvalid. inversion Hvalid.
        }
        assert (i' = i) as ->.
        { destruct cont' as [i1' i2'|bs].
          - destruct Hcont as (_ & _ & _ & _ & _ & HC).
            destruct fuel as [|fuel]; ss.
            { apply prefix_nil_inv in HC; set_solver+HC. }
            rewrite Hp2 decide_True // in HC; last (split; [auto|lia]).
            by apply prefix_cons_inv_1 in HC.
          - destruct Hcont as (_ & _ & HC).
            destruct fuel as [|fuel]; ss.
            rewrite Hp2 decide_True // in HC; last (split; [auto|lia]).
            by inversion HC. }
        (* We commit. *)
        pose (new_elts := map (get_value slots ({[i]} ∪ deqs)) new_pref ++ rest).
        pose (new_pvs := proph_data (fuel - 1) sz ({[i]} ∪ deqs) (stail str)).
        sYieldS. aUnfoldS. sYieldS. cStepsS. iRename "ASM" into "He◯".
        iDestruct (sync_elts with "He● He◯") as %<-.
        iMod (update_elts _ _ _ new_elts with "He● He◯") as "[He● He◯]".
        cForceS (inr ((Vptr (iblk, iofs))↑)). cForcesS. iSplitL "He◯".
        { iFrame. iPureIntro. rewrite /new_elts /=. by eexists; rewrite /get_value Hslots_i. }
        iMod ("Close" with "[//][-IST Hback_snap Hi2]IST") as ">>IST".
        { pose (new_deqs := {[i]} ∪ deqs).
          iExists back', new_pvs, new_pref, rest, cont', slots, new_deqs.
          subst new_deqs. iFrame. iSplitL "H_ar".
          { rewrite array_content_dequeue; [ done | by lia | done ]. }
          iPureIntro. repeat split_and; try done.
          - exists (stail str).
            rewrite reverse_cons. subst new_pvs; split.
            { rewrite list_stream_app_app /=; f_equal; destruct str; ss; clarify. }
            exists (fuel - 1); split; last done.
            destruct fuel as [|fuel].
            { specialize (Hpvs 0 i); exfalso; ss; hexploit Hpvs; ss; last set_solver+. lia. }
            intros x2 i2 Hi2sz Hi2deq Hi2lookup.
            replace (S fuel - 1) with fuel by lia. specialize (Hpvs (S x2) i2).
            rewrite /= Hp2 decide_True // in Hpvs; last (split; auto; try lia).
            hexploit Hpvs; eauto; first set_solver.
            rewrite elem_of_cons; intros [->|?]; auto; set_solver.
          - intros k. split; intros Hk; first by apply Hstate.
            intros Hk_in_deqs. apply elem_of_union in Hk_in_deqs.
            destruct Hk_in_deqs as [Hk_is_i|Hk_in_deqs].
            + apply elem_of_singleton_1 in Hk_is_i. subst k.
              rewrite /array_get Hslots_i decide_False in Hi; last done.
              rewrite /physical_value in Hi. rewrite Hslots_i in Hk.
              inversion Hk; subst dw.
            + apply Hdeqs in Hk_in_deqs as (HContra & _).
              rewrite HContra in Hk. inversion Hk.
          - intros k Hk.
            assert (k ∈ i :: new_pref) as HH%Hpref by set_solver +Hk.
            destruct HH as (Ha1 & Ha2 & Ha3). repeat split; try done.
            apply not_elem_of_union. split; last done.
            apply not_elem_of_singleton. intros ->.
            destruct cont' as [i1' i2'|bs].
            + destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & [junk HC6]).
              rewrite HC6 in Hpvs_ND.
              apply NoDup_app in Hpvs_ND as (HND & _ & _).
              apply NoDup_app in HND as (HND & _ & _).
              apply NoDup_app in HND as (HND & _ & _).
              apply NoDup_cons in HND as (HND & _). apply HND, Hk.
            + destruct Hcont as (HC1 & HC2 & HC3). rewrite HC3 in Hpvs_ND.
              apply NoDup_app in Hpvs_ND as (HND & _ & _).
              apply NoDup_app in HND as (HND & _ & _).
              apply NoDup_cons in HND as (HND & _). apply HND, Hk.
          - intros k Hk. apply elem_of_union in Hk as [Hk%elem_of_singleton_1|Hk].
            + subst k. rewrite Hslots_i /=.
              repeat split_and; [ done | by f_equal | .. ].
              rewrite /array_get Hslots_i decide_True; [ done | by set_solver ].
            + destruct (Hdeqs k Hk) as (? & ? & ?). repeat split_and; try done.
              rewrite /array_get. destruct (slots !! k) as [[[lk sk] wk]|]; last done.
              rewrite decide_True; first done. by set_solver +Hk.
          - by apply proph_data_NoDup.
          - intros k Hk. by eapply proph_data_sz.
          - destruct cont' as [i1' i2'|bs].
            + destruct Hcont as (((HC1 & HC2) & HC3) & HC4 & HC5 & HC6 & HC7 & HC8).
              assert (i1' ≠ i) as Hi1'_not_i.
              { intros ->. assert (i ∈ i :: new_pref) as Hpref_i%Hpref by set_solver.
                by destruct Hpref_i as (_ & _ & Hpref_i). }
              repeat split_and; try done.
              * apply not_elem_of_union. split; last done. by apply not_elem_of_singleton.
              * revert HC7. rewrite /array_get.
                destruct (slots !! i1') as [di1'|] eqn : Hil'; last by inversion HC2.
                destruct di1' as [[li1' si1'] wi1'].
                rewrite ?decide_False; set_solver.
              * rewrite /new_pvs.
                destruct fuel as [|fuel]; [ss; apply prefix_nil_inv in HC8; inv HC8|].
                replace (S fuel - 1) with fuel by lia.
                rewrite /= Hp2 decide_True in HC8; last (split; auto; lia).
                by eapply prefix_cons_inv_2.
            + destruct Hcont as (HC1 & HC2 & HC3).
              repeat split_and; try done.
              destruct fuel as [|fuel]; first done.
              subst new_pvs. replace (S fuel - 1) with fuel by lia.
              rewrite /= Hp2 decide_True in HC3; last by (split; try lia).
              by inversion HC3.
        }
        cStepsS. sYields.
        iApply (wsim_mem_cmp with "Hi2 []"); [simpl_map; s; f_equal|ss|..].
        { ss; case_bool_decide; first refl; naive_solver. }
        { ss; iIntros "[$ $] !> [Ha Hb]"; iSplitL "Ha"; by iFrame. }
        iIntros "_". cStepsT. sYields. sYieldS. cStep; iFrame; done.
      }
      (* If the enqueue at index [i] was not committed: contradiction. *)
      exfalso.
      assert (was_committed <$> slots !! i = Some false) as Hcom_i.
      { rewrite Hslots_i. simpl. by f_equal. }
      apply Hstate in Hcom_i. rewrite Hslots_i in Hcom_i.
      inversion Hcom_i; subst dw. rewrite /array_get Hslots_i /= in Hi.
      destruct (decide (i ∈ deqs)); by inversion Hi.
    * (* The CmpXchg failed, we continue looping. *)
      assert (array_content sz slots deqs !! i = Some (Vint 0)) as Hcont_i.
      { rewrite array_content_lookup; last by lia. by rewrite Hi. }
      iPoseProof (big_sepL_lookup_acc _ _ (i) with "H_ar") as "[Hi H_ar]".
      { rewrite Hcont_i //. }
      iApply (wsim_mem_cas with "Hi Hi1 []"); [simpl_map; s; f_equal|ss|..].
      { rewrite /MemA.compare_val //. }
      { iIntros "$ !>"; iExists 1%Qp, Vundef; iIntros "[_ $] !> //". }
      case_bool_decide; first ss.
      iIntros "Hi Hi2". cStepsT. iPoseProof ("H_ar" with "Hi") as "H_ar".
      (* We resolve. *)
      iDestruct "Hproph" as (p str rs) "[Hp Hpvs]". iDestruct "Hpvs" as %Hpvs.
      cInlineT. cForceT (_, existT _ (p, rs, (i, false))). cForcesT. iSplitL "Hp".
      { repeat iSplit; eauto. }
      cStepsT. iDestruct "GRT" as "[-> [[-> %Hp] Hp]]".
      pose proof (stake_S p (length rs)) as Htemp; simpl in Htemp.
      rewrite Htemp in Hp; clear Htemp. rewrite reverse_cons app_inj_tail_iff in Hp.
      destruct Hp as [Hp1 Hp2]; symmetry in Hp2.
      destruct Hpvs as [-> [fuel [Hpvs ->]]].
      rewrite lookup_list_stream_app_r length_reverse // Nat.sub_diag /= in Hp2.
      (* We can close the invariant. *)
      iMod ("Close" with "[//] [- IST Hback_snap Hi2_lower_bound Hi2] IST") as ">> IST".
      { iExists _, _, _, _, cont', _, _. iFrame. iSplit; last done. iPureIntro.
        s; exists (stail str).
        rewrite reverse_cons; split.
        { replace str with (scons (shead str) (stail str)) at 1; last by (destruct str; ss).
          rewrite list_stream_app_app //=; destruct str; ss; clarify.
        }
        exists (fuel - 1); destruct fuel as [|fuel]; s.
        { split; last done.
          intros x2 i2 Hi2sz Hi2deq Hi2lookup. eapply (Hpvs (S x2) i2); eauto.
        }
        rewrite Hp2 Nat.sub_0_r; split; last done.
        intros x2 i2 Hi2sz Hi2deq Hi2lookup. specialize (Hpvs (S x2) i2); ss.
        rewrite Hp2 in Hpvs; apply Hpvs; eauto.
      }
      sYields.
      iApply (wsim_mem_cmp with "Hi2 []"); [simpl_map; s; f_equal|ss|..].
      { ss. }
      { ss; iIntros "$ !>"; iExists 1%Qp, Vundef; iIntros "[_ $] !> //". }
      iIntros "_". cStepsT. sYields.
      (* And conclude using the loop induction hypothesis. *)
      rewrite Nat.sub_0_r.
      iClear "Hval_wit_i".
      iApply ("IH_loop" with "[] [] Hback_snap Hi2_lower_bound IST").
      - iPureIntro. lia.
      - iPureIntro. destruct cont as [i1 i2|bs]; last done.
        apply Nat.lt_eq_cases in Hcont_i1. destruct Hcont_i1 as [Hi1|Hi1]; first lia.
        exfalso. destruct Hinitial_cont as [-> Hinitial_cont].
        destruct Hcont as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7).
        assert (is_Some (slots !! i1)) as Hslots_i1. { apply Hslots. lia. }
        destruct Hslots_i1 as [[[li1 si1] wi1] Hslots_i1].
        rewrite /array_get Hslots_i1 decide_False in HC5; last done.
        simpl in HC5. destruct wi1; last done.
        rewrite array_content_lookup in Hcont_i; last by lia.
        rewrite /array_get in Hcont_i. subst i i1. rewrite Hslots_i1 in Hcont_i.
        rewrite decide_False in Hcont_i; last done. by inversion Hcont_i.
  Qed.
End HWQPM.