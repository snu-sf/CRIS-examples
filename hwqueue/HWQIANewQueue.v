Require Export CRIS ImpPrelude HWQHeader SchHeader MemHeader ProphecyHeader HelpingHeader.
Require Export CallFilter MemA SchA ProphecyA.
Require Export HWQRA.
Require Import MemI MemIAproof MemTactics.
Require Import ProphecyI ProphecyFacts.
Require Import HelpingTactics.
Require Import HWQI HWQP SchI HWQA SchTactics.
From stdpp Require Import streams list.

Section HWQPM.
  Context `{!crisG Γ Σ α β τ Hinv Hsub, !concGS, !schGS, !hwqG, !memGS, !prophGS}.
  Context (mn : string).
  Context (N : namespace) (sp_mem : specmap).

  Definition Ist : ist_type Σ := λ st_src st_tgt,
    (IstHelp mn st_src st_tgt ∗
    ∃ (X : gset val),
      free_id (λ x, (x.1 = "hwq" ∧ match (x.2↓↓) with | Some x => x ∉ X | None => True end)%type) ∗
      [∗ set] x ∈ X,
        □ ∃ blk ofs nx, ⌜x = Vptr (blk, ofs)⌝ ∗
          ∀ X, helping_auth 1 X =| nx, ↑N |={↑N, ∅}=∗ ∃ v, (blk, ofs) ↦ v)%I.
  Definition IstFull : ist_type Σ :=
    IstProd (IstSB (Mod.scopes (HWQP.t mn) ++ Mod.scopes (HelpingDummy.t mn)) Ist) IstEq.
  Lemma Ist_help : Ist_helping mn IstFull.
  Proof.
    iIntros (??) "[% [% [% [% [[-> ->] [[%Ha [[% [[-> ->] ?]] ?]] ->]]]]]]".
    iModIntro; iExists _, _; iFrame; iSplit; auto.
    iIntros (?) "$ !>"; iExists _, _, _, _; repeat iSplit; eauto.
    iPureIntro. set_solver.
  Qed.

  Notation sp := (SchA.sp ∅ (↑N)).
  Notation HWQM := (HWQM.t N mn).
  Notation HWQP := (HWQP.t mn).
  Notation HelpOn := (HelpingOn.t mn HWQM.jobCode sp).
  Notation HelpDummy := (HelpingDummy.t mn).
  Notation MemA := (MemA.t sp_mem).
  Notation ProphA := (ProphecyA.t mn ∅).

  Lemma simF_new_queue : 
    ISim.sim_fun open
      ((HWQM ★ HelpOn) ★ MemA ★ ProphA) ((HWQP ★ HelpDummy) ★ MemA ★ ProphA)
      IstFull (fid HWQHdr.new_queue).
  Proof.
    cStartFunSim. s.
    cStepsS. destruct _q as [[mtid stid] [n sz]]; s.
    iDestruct "ASM" as "[TID [-> [-> %Hsz]]]".
    cStepsS. cStepsT.
    rewrite /HWQP.new_queue /HWQA.new_queue.
    cStepsT. sYieldIR "IST" "TID". sYieldIR "IST" "TID".
    iApply wsim_mem_alloc; [try by simpl_map|ss|try lia|].
    replace (Z.to_nat (2 + sz)) with (2 + sz) by lia.
    iIntros (blk); rewrite replicate_add big_sepL_app; iIntros "[[sz [back _]] ar]". cStepsT.
    sYieldIR "IST" "TID". sYieldIR "IST" "TID".
    mStoreT "sz". sYieldIR "IST" "TID".
    mStoreT "back". sYieldIR "IST" "TID".
    replace sz with ((sz - sz) + sz) at 1 by lia. rewrite replicate_add.
    replace (replicate (sz - sz) Vundef) with (replicate (sz - sz) (Vint 0))
      by rewrite Nat.sub_diag //=.
    rewrite -[X in ITree.iter _ X](Nat.sub_diag sz).
    assert (sz ≤ sz) as Hle by lia; revert Hle.
    generalize sz at 1 4 5 10 as i; intros i Hle.
    iInduction i as [|i] forall (Hle st_src st_tgt).
    { rewrite Nat.sub_0_r /= app_nil_r.
      unfoldIterT. cStepsT. sYieldIR "IST" "TID".
      rewrite Nat2Z.id Nat.ltb_irrefl. cStepsT. sYieldIR "IST" "TID".
      iDestruct "IST" as "[% [% [% [% [[-> ->] [[% IST] ->]]]]]]".
      iDestruct "IST" as "[IST [%X [free alloc]]]".
      destruct (decide (Vptr (blk, 0%Z) ∈ X)) as [HblkX|HblkX].
      { iPoseProof (big_sepS_elem_of_acc with "alloc") as "[#acc _]"; auto using HblkX.
        iDestruct "acc" as "[% [% [% [% acc]]]]"; clarify.
        iDestruct "IST" as "[% [? IST]]".
        iMod ("acc" with "IST") as "[% acc2]".
        by iPoseProof (mem_points_to_singleton_valid with "acc2 sz") as "%".
      }
      iPoseProof (free_id_split_singleton _ ("hwq", ((Vptr (blk, 0%Z))↑↑)) with "free") as "[tok free]".
      { split; ss. rewrite SAny.upcast_downcast //. }
      cStepsT. cInlineT. cForceT (_, hwq_prophecy). cForcesT. iSplitL "tok".
      { repeat iSplit; first iPureIntro; ss. }
      cStepsT. iDestruct "GRT" as "[-> [%p [-> Proph]]]".
      (* invariant construction *)
      iMod new_back as (γb) "Hb●".
      iMod new_back as (γi) "Hi●". (* FIXME not about back. *)
      iMod (new_elts []) as (γe) "[He● He◯]".
      iMod new_no_contra as (γc) "HC".
      iMod new_slots as (γs) "Hs●".
      iMod (inv_alloc (syn_inv_hwq sz γb γi γe γc γs blk) (n:=n) (S n) _ _ N
        with "[ar sz back Proph Hb● Hi● He● HC Hs●]") as "#InvN"; auto.
      { pose proof (enough_fuel_exists sz ∅ p) as [fuel Hfuel].
        pose (pvs := proph_data fuel sz ∅ p).
        pose (cont := NoCont (map (λ i, (i, [])) pvs)).
        rewrite inv_hwq_red. iRight.
        iExists 0, pvs, [], [], cont, ∅, ∅.
        rewrite array_content_empty fmap_empty /=.
        iFrame. iSplitL "ar".
        { iApply (big_sepL_impl with "ar"); iModIntro; iIntros (k?).
          replace (k + 2)%Z with (Z.of_nat (S (S k))) by lia. iIntros "% ? //=".
        }
        repeat (iSplit; first done). iSplit.
        { ss; iPureIntro; ss; esplits; ss; eauto. }
        iSplit; first done. iPureIntro.
        repeat split_and; try done.
        - intros i. split; intros Hi; [ by lia | by inversion Hi].
        - intros e He. set_solver.
        - apply proph_data_NoDup.
        - apply proph_data_sz.
        - intros b. apply initial_block_valid.
        - simpl. apply flatten_blocks_initial. }
      sYieldS. cForceS (Vptr (blk, 0%Z)). cForcesS. iFrame.
      repeat iSplit; first auto.
      { iExists _; iSplit; first auto. iExists _, _, _, _, _; iSplit; eauto. }
      iIst "IST" with "[-]".
      { iExists _, _, _, _. repeat iSplit; des; eauto.
        iFrame "IST". iExists (X ∪ {[Vptr (blk, 0%Z)]}). 
        iSplitL "free".
        { iApply (free_id_iff with "free").
          intros i; case_decide; subst; ss.
          { rewrite SAny.upcast_downcast; split; ss.
            rewrite elem_of_union; intros [_ a]; apply a; right; set_solver+.
          }
          split; intros [? ?]; split; try done.
          { case_match; set_solver. }
          case_match; auto. rewrite elem_of_union; intros [|?%elem_of_singleton].
          { set_solver. }
          subst; destruct i; ss; cSimpl.
        }
        rewrite big_sepS_union; last set_solver.
        iFrame. rewrite big_sepS_singleton; iModIntro.
        iExists _, _, (S n); iSplit; eauto.
        clear. iIntros (X) "X".
        iInv "InvN" as "[[% X2]|[% [% [% [% [% [% [% [$ ?]]]]]]]]]" "close".
        { iCombine "X X2" gives %[WF _]%gmap_view_auth_dfrac_op_valid. ss. }
        iApply fupd_mask_intro; eauto. solve_ndisj.
      }
      cStep. iFrame. auto.
    }
    (* inductive case *)
    unfoldIterT. cStepsT. sYieldIR "IST" "TID".
    destruct Nat.ltb eqn : Hltb; first clear Hltb; last first.
    { apply Nat.ltb_ge in Hltb; lia. }
    iPoseProof (big_sepL_insert_acc _ _ (sz - (S i)) with "ar") as "[↦ ar]".
    { rewrite lookup_app_r length_replicate // Nat.sub_diag //=. }
    cStepsT.
    replace (0 + 2 + (sz - S i)%nat)%Z with (Z.of_nat (2 + (sz - S i))) by lia.
    mStoreT "↦". iPoseProof ("ar" with "↦") as "ar".
    replace (sz - S i) with (length (replicate (sz - S i) (Vint 0)) + 0) at 1
      by (rewrite length_replicate; lia).
    rewrite insert_app_r /=.
    replace (S (sz - S i)) with (sz - i) by lia.
    iApply ("IHi" with "[] [ar] sz back IST TID"); first (iPureIntro; lia).
    replace (sz - i) with ((sz - S i) + 1) by lia; rewrite replicate_add /=.
    rewrite -(assoc app) //=.
  Qed.
End HWQPM.
