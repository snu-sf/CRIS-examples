Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section CAS.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Local Definition MA := (PFMemA.t sp).
  Local Definition MI := (PFMemI.t syn size).

  Lemma simF_cas : ISim.sim_fun open MA MI Ist (Some PFMemHdr.cas).
  Proof.
    (* prologue *)
    iStartSim.
    step_l.
    destruct _q as [[[[[[[[[[[[[tid loc] old] new] ordr] ordw] 𝓥] γ] ζ'] Vb] tx] ζn] mode] Pr].
    steps_l.
    iDestruct "ASM" as "[-> [[-> [%RLXR [%RLXW %COMPARABLE]]] [TV [SN [PT [AW [PR #CMP]]]]]]]".
    iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA HFA]]]]]]".
    hss. steps_r.

    (* conditions *)
    iPoseProof (tview_both_valid with "TA TV") as "%IN".
    destruct IN as [l [lc [FIND <-]]].
    iPoseProof (AtomicSeen_alloc_view with "SN") as "%AV".
    iPoseProof (AtomicSeen_non_empty' with "SN") as "%NE'".
    iPoseProof (AtomicSeen_non_empty with "SN") as "%NE".
    iPoseProof (AtomicSeen_max_ts with "SN") as "%MAXZETA".

    rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def AtomicSeen_eq /AtomicSeen_def.
    iDestruct "SN" as "((%ALLOC & %SN) & #AR & %GOODHIST & (%Va & %VACUR & #ALN))".
    iDestruct "PT" as "[%C [% [-> [%SYNCLOCAL [HIST [AA PTA]]]]]]".
    iPoseProof (hist_own_hist_cut with "HA HIST") as "[%t_cut [% [%EQZETA %]]]".
    iPoseProof (at_auth_reader_latest with "AA AR") as "%ZETALE".
    assert (CUTLC : Time.le t_cut (View.rlx (TView.cur (Local.tview lc)) loc)).
    { subst. destruct NE' as [x [? [? NE']]].
      hexploit (ZETALE x); eauto. rewrite Cell.cut_spec; des_if; ss.
      i; etrans; eauto. apply SN; ss.
    }

    (* ident check *)
    rewrite /PFMemI.check_ident FIND.
    steps_r. destruct _q as [[[e valret] config'] [valr [EV STEP]]].
    destruct e; inv EV; s; destruct (excluded_middle_informative _); ss; cycle 1.
    { (* racy cas *)
      inv STEP; ss. rename STEP0 into STEP.
      inv STEP. inv LOCAL. clear STATE. inv LOCAL. rename LOCAL0 into LOCAL.
      inv LOCAL. { destruct ordr; ss. } { destruct ordw; ss. }
      inv RACE. { inv PFG. rewrite H /Promises.Promises.bot // in GET. }
      hexploit MSG; eauto; intros ->; clear MSG.
      rename to0 into to.
      hexploit (CUT loc to); eauto; intros TOCUT.
      iPoseProof (at_auth_reader_latest with "AA AR") as "%LE".
      exfalso.
      eapply (TimeFacts.le_not_lt to (View.rlx (TView.TView.cur (Local.tview lc2)) loc)); eauto.
      etrans; eauto.
    }
    { (* inaccessible cas *)
      inv STEP. ss. rename STEP0 into STEP; inv STEP. inv LOCAL. clear STATE EVENT t.
      inv LOCAL. inv RACE; ss.
      { inv PFG. rewrite H1 in FREEPROMISE.
        hexploit PFL; eauto; intros INV; inv INV; des; rewrite H4 in FREEPROMISE.
      }
    }
    { (* inaccessible cmp cas *)
      inv STEP; ss. clear EVENT. rename STEP0 into STEP. inv STEP; inv LOCAL; ss.
      clear STATE. inv LOCAL0. inv COMPARE.
      { (* inaccessible ptr cmp *)
        iPoseProof ("CMP" with "PR") as "> EX". inv CMP.
        { (* read ptr is inaccessible *)
          iPoseProof (bi.and_elim_r with "EX") as "EX".
          inv RACE.
          { inv PFG; rewrite H1 in FREEPROMISE. inv LOCAL; ss. }
          { (* inaccessible read ptr *)
            inv LOCAL. ss. destruct val'; ss; cycle 1.
            { exfalso. hexploit (COMPARABLE to from Val.Vundef); last (intros ?; des; eauto).
              { inv READABLE. etrans; eauto. }
              { rewrite Cell.cut_spec; des_if.
                { move : GET. rewrite /Memory.get_cell /Cell.get /Memory.get /Block.get /Cell.get //=. }
                { exfalso; eapply TimeFacts.le_not_lt; last eauto.
                  inv READABLE. etrans; eauto.
                }
              }
            }
            eapply Loc.eqb_eq in VAL; clarify.
            iSpecialize ("EX" $! to from with "[]").
            { iPureIntro. split.
              { inv READABLE. etrans; eauto. }
              split.
              { rewrite Cell.cut_spec; des_if.
                { move : GET. rewrite /Memory.get_cell /Cell.get /Memory.get /Block.get /Cell.get //=. }
                { exfalso; eapply TimeFacts.le_not_lt; last eauto.
                  inv READABLE. etrans; eauto.
                }
              }
              ii; clarify. apply BLOCK. destruct (TBid.eq_dec _ _); ss.
            }
            iDestruct "EX" as "[% [% [% [_ HIST']]]]".
            iPoseProof (hist_own_hist_cut with "HA HIST'") as "%F"; des; done.
          }
        }
        { (* expected ptr inaccessible *)
          inv RACE.
          { inv PFG; rewrite H1 in FREEPROMISE. inv LOCAL; ss. }
          { iPoseProof (bi.and_elim_l with "EX") as "EX".
            iDestruct "EX" as "[%qr [%Cr [%Vr [% [% [[? HIST'] ?]]]]]]".
            iPoseProof (hist_own_hist_cut with "HA HIST'") as "[% [? [? %ACC]]]"; done.
          }
        }
      }
      { (* type error *)
        inv LOCAL. hexploit (COMPARABLE to from val' released).
        { inv READABLE; etrans; eauto. }
        { rewrite Cell.cut_spec; des_if.
          { move : GET. rewrite /Memory.get_cell /Cell.get /Memory.get /Block.get /Cell.get //=. }
          { exfalso; eapply TimeFacts.le_not_lt; last eauto.
            inv READABLE. etrans; eauto.
          }
        }
        intros [CMP _]. destruct old, valr, val'; ss.
      }
    }

    (* valid cas step *)
    clear n. iClear "CMP".
    inv STEP; ss. clear EVENT. inv STEP0; inv LOCAL; ss.
    { (* success case*)
      steps_r.
      assert (TRW : Time.lt tsr tsw).
      { inv LOCAL1. inv READABLE.
        inv LOCAL2. inv WRITE; ss. inv ADD; ss. inv ADD0; ss.
      }
      assert (REL : Time.le (View.rlx releasedr loc) tsr).
      { inv LOCAL1. inv WF. inv GL_WF. inv MEM_CLOSED; ss.
        hexploit CLOSED; eauto; i; des.
        inv MSG_TS; ss.
      }
      (* update resources *)
      iPoseProof (hist_freeable_auth_write with "HFA") as "> HFA"; eauto.
      { inv WF; ss. }
      iPoseProof (hist_auth_write_vs with "HA HIST") as "> [% [%ADD [HA HIST]]]"; eauto.
      { etrans; eauto. inv LOCAL1; ss. inv READABLE. etrans; eauto. left. done. }
      (* update atomic resources *)
      remember (IdentMap.add _ _ _) as ths'.
      iMod (tview_auth_update _ ths' with "TA TV") as "[TA TV]"; eauto.
      remember (Message.message new _ _) as msg.
      hexploit (@Cell.add_exists ζ' tsr tsw msg); eauto.
      { intros ??? GET%ZETALE; inv ADD. eapply DISJOINT; eauto. }
      intros [ζ'' ADD''].
      iPoseProof (at_auth_at_last_na_agree with "AA ALN") as "->".
      iAssert ( |==>
        at_auth γ ζn tx Va
        ∗ match mode with
          | SingleWriter => True
          | CASOnly => at_writer γ ζn
          | ConcurrentWriter => at_writer γ ζn ∗ at_exclusive_write γ tx 1
          end
        ∗ (if mode is SingleWriter then at_writer γ ζn else True)
        ∗ at_reader γ ζ'')%I
        with "[AA AW PTA]" as ">(AA & PTA & AW & #AR')".
      { destruct mode; s.
        { iDestruct "AA" as "[AAW [AAE _]]".
          iMod (at_writer_update with "AAW AW") as "[AAW AW]"; last iFrame "AAW".
          { intros ts ?? GET; erewrite Cell.add_get1; eauto. }
          iPoseProof (at_writer_fork_at_reader with "AW") as "#AR'".
          iFrame. iModIntro. iFrame "ALN".
          iApply (at_reader_extract with "AR'"); eauto.
          intros ts ??; erewrite Cell.add_o; eauto; des_if.
          { intros INV; inv INV. erewrite Cell.add_o; eauto; des_ifs. }
          move /ZETALE => GET; erewrite Cell.add_o; eauto; des_ifs.
        }
        { iDestruct "AA" as "[AAW [AAE _]]". iClear "AW".
          iMod (at_writer_update with "AAW PTA") as "[AAW AW]"; last iFrame "AAW".
          { intros ts ?? GET; erewrite Cell.add_get1; eauto. }
          iPoseProof (at_writer_fork_at_reader with "AW") as "#AR'".
          iFrame. iModIntro. iFrame "ALN". iSplitR; first done.
          iApply (at_reader_extract with "AR'"); eauto.
          intros ts ??; erewrite Cell.add_o; eauto; des_if.
          { intros INV; inv INV. erewrite Cell.add_o; eauto; des_ifs. }
          move /ZETALE => GET; erewrite Cell.add_o; eauto; des_ifs.
        }
        { iFrame "AW".
          iDestruct "PTA" as "[AW AEW]". iDestruct "AA" as "[AAW [AAE _]]".
          iMod (at_writer_update with "AAW AW") as "[AAW AW]"; last iFrame "AAW".
          { intros ts ?? GET; erewrite Cell.add_get1; eauto. }
          iPoseProof (at_writer_fork_at_reader with "AW") as "#AR'".
          iFrame. iModIntro. iFrame "ALN".
          iApply (at_reader_extract with "AR'"); eauto.
          intros ts ??; erewrite Cell.add_o; eauto; des_if.
          { intros INV; inv INV. erewrite Cell.add_o; eauto; des_ifs. }
          move /ZETALE => GET; erewrite Cell.add_o; eauto; des_ifs.
        }
      }
      iAssert (∃ (ζ3 : Cell.t),
        ⌜ Cell.le ζ' ζ3
        ∧ Cell.le ζ3 ζn
        ∧ Cell.get tsr ζ3 = Memory.get loc tsr (Global.memory gl)
        ∧ Cell.get tsw ζ3 = Some (tsr, msg)
        ∧ ∀ ts, ts ≠ tsr ∧ ts ≠ tsw → Cell.get ts ζ3 = Cell.get ts ζ' ⌝
        (* ∧ Cell.add ζ' tsr tsw msg ζ3 ⌝ *)
        )%I as "%EX".
      { destruct (Cell.get tsr ζ') as [[? ?] | ] eqn : GET'.
        { iExists ζ''; iPureIntro.
          split; first by eapply Cell.add_le.
          split; first by eapply Cell.le_add_le.
          (* split; ss. *)
          erewrite Cell.add_o; eauto; des_if.
          { subst tsr. timetac. }
          rewrite GET'; revert GET'; move /ZETALE; rewrite Cell.cut_spec; des_if; ss.
          intros INV; split.
          { revert INV; rewrite /Memory.get_cell /Memory.get /Block.get /Cell.get; intros ->; split; ss. }
          erewrite Cell.add_o; eauto; des_if; split; ss.
          intros ? [??]; erewrite Cell.add_o; eauto; des_ifs.
        }
        inv LOCAL1; ss.
        remember (Message.message val' _ _) as msgr.
        hexploit (@Cell.add_exists ζ'' from tsr msgr); eauto using Cell.get_ts.
        { intros ???; erewrite Cell.add_o; eauto; des_if; ss.
          { subst to2; intros INV; inv INV. by apply Interval.disjoint_imm. }
          intros GET2. dup GET2; revert GET0.
          move /ZETALE; rewrite Cell.cut_spec; des_if; last ss.
          intros GET3; hexploit Memory.get_disjoint; first apply GET.
          { move : GET3; rewrite /Memory.get /Block.get //. }
          i; des; clarify.
        }
        intros [ζ3 ADD3].
        iExists ζ3; iPureIntro.
        split; first by (etrans; eapply Cell.add_le).
        split.
        { intros ???; erewrite Cell.add_o; eauto; des_if; first subst to.
          { intros INV; inv INV.
            erewrite Cell.add_o; eauto; des_if; ss.
            { timetac. }
            rewrite Cell.cut_spec; des_if; ss.
            exfalso; eapply TimeFacts.le_not_lt; last eauto.
            etrans; eauto. apply READABLE.
          }
          eapply Cell.le_add_le; eauto.
        }
        split. { erewrite Cell.add_o; eauto; des_if; ss. }
        split.
        { erewrite Cell.add_o; eauto; des_if; ss; first timetac.
          erewrite Cell.add_o; eauto; des_if; ss.
        }
        intros ? [??]; erewrite Cell.add_o; eauto; des_if; ss.
        erewrite Cell.add_o; eauto; des_if; ss.
      }
      destruct EX as [ζ3 [LE13 [LE3n [GETR [GETW GETO]]]]].
      iPoseProof (at_auth_fork_at_reader with "AA") as "#ARn".
      iPoseProof (at_reader_extract with "ARn") as "#AR3"; first apply LE3n.
      (* AtomicSeen assertion *)
      iAssert ( |==> @{TView.cur (Local.tview lc2)} loc sn⊒{γ} ζ3)%I with "[AR3]" as "# > SN3".
      { rewrite /view_at AtomicSeen_eq /AtomicSeen_def /=; iFrame "AR3 ALN".
        iSplitL.
        { iModIntro; iPureIntro; split; ss.
          { inv LOCAL1; ss. inv LOCAL2; ss. rewrite ?AllocView.join_bot_r.
            rewrite /AllocView.join /orb; des_ifs.
          }
          intros t; destruct (decide (t = tsw)).
          { inv LOCAL1. inv LOCAL2; ss. intros _; rewrite /seen_local /= /TimeMap.join.
            etrans; last apply Time.join_r.
            rewrite /TimeMap.singleton /LocFun.add; des_if; ss.
          }
          destruct (decide (t = tsr)).
          { inv LOCAL1. inv LOCAL2; ss. intros _; rewrite /seen_local /= /TimeMap.join.
            etrans; last apply Time.join_r.
            rewrite /TimeMap.singleton /LocFun.add; des_if; ss. left; apply TRW.
          }
          rewrite GETO; ss. inv LOCAL1; inv LOCAL2; ss.
          intros ?; rewrite /seen_local /View.join /= /TimeMap.join.
          do 3 (etrans; last eapply Time.join_l).
          by eapply SN.
        }
        iModIntro; iSplit; iPureIntro; ss.
        { ii; clarify. rewrite Cell.bot_get in GETW; ss. }
        { etrans; eauto. inv LOCAL1; inv LOCAL2; ss.
          do 3 (etrans; last eapply View.join_l); refl.
        }
      }
      force_l (Val.one ↑). steps_l. force_l (Val.one ↑). steps_l. force_l.
      iSplitR "HA HFA TA".
      { iSplit; first done. iFrame "PR TV".
        inv LOCAL1; ss.
        unshelve (iExists Val.one, _, ζn, tsr, from, _, valr); eauto.
        { inv WF. eapply Memory.get_ts; eauto. }
        iExists _, _.
        iSplit.
        { iPureIntro. esplits; eauto.
          { hexploit (COMPARABLE tsr from val'); eauto.
            { inv READABLE; etrans; eauto. }
            { rewrite Cell.cut_spec; des_if; ss.
              { move: GET; rewrite /Memory.get /Block.get /Cell.get //. }
              { inv READABLE. exfalso; eapply TimeFacts.le_not_lt; first eapply RLX.
                eapply TimeFacts.lt_le_lt; eauto.
              }
            }
            destruct valr, val'; ss; intros [? _]; ss; try (destruct old; done); rewrite GETR GET.
            { eapply Z.eqb_eq in VAL; subst; refl. }
            { eapply Loc.eqb_eq in VAL; subst; refl. }
          }
          { etrans; eauto. inv READABLE; ss. }
          { inv LOCAL2; ss. etrans; last eapply TViewFacts.write_tview_incr; ss.
            { eapply TViewFacts.read_tview_incr. }
            eapply TViewFacts.read_future1; eauto.
            inv WF. inv WF0. hexploit THREADS; eauto. intros INV; inv INV; ss.
          }
        }
        iSplitL "SN3".
        { rewrite AtomicSeen_eq /AtomicSeen_def; ss. }
        iRight.
        remember (TView.write_released _ _ _ _ _) as V_w. iExists V_w. iSplit.
        { iPureIntro. split; first done.
          split.
          { inv COMPARE.
            { eapply Z.eqb_eq in H3; subst; ss. }
            { inv CMP. symmetry in EQ; revert BlOCK EQ; rewrite /Loc.get_tbid.
              destruct loc1, loc2, (TBid.eq_dec _ _); ss.
              intros _ ?%Z.eqb_eq; clarify.
            }
          }
          exists tsw; split; eauto.
          { revert ADD; destruct ordw; ss. }
          split.
          { subst V_w; rewrite /TView.write_released; des_if; first eapply View.join_l.
            destruct ordw; ss.
          }
          split.
          { intros VEQ; clarify.
            rewrite /TView.write_released RLXW /TView.write_tview /= in VEQ.
            inv WF. inv GL_WF. inv MEM_CLOSED; ss.
            hexploit CLOSED; eauto; i; des.
            inv MSG_TS.
            eapply TimeFacts.le_not_lt; eauto.
            rewrite VEQ /View.join /= /LocFun.add; des_if; ss.
            rewrite /TimeMap.join; des_if; ss;
            do 2 (eapply TimeFacts.lt_le_lt; last eapply Time.join_r);
            rewrite /TimeMap.singleton /LocFun.add; des_if; ss.
          }
          split.
          { intros INV; inv INV.
            eapply TimeFacts.le_not_lt.
            { etrans; last apply REL; eauto. }
            inv LOCAL2; ss.
            rewrite /TimeMap.join.
            eapply TimeFacts.lt_le_lt; first apply TRW.
            etrans; last eapply Time.join_r.
            rewrite /TimeMap.singleton /LocFun.add; des_if; ss; refl.
          }
          split.
          { inv LOCAL2; ss.
            rewrite /TView.write_tview /TView.read_tview /=.
            intros EQ; rewrite -EQ in READABLE; ss.
            eapply TimeFacts.le_not_lt; first eapply READABLE.
            eapply TimeFacts.lt_le_lt; first apply TRW.
            rewrite /View.join /= /TimeMap.join.
            etrans; last eapply Time.join_r.
            rewrite /TimeMap.singleton /LocFun.add; des_if; ss. refl.
          }
          destruct (Ordering.le Ordering.acqrel ordw) eqn : ORDW.
          { destruct (Ordering.le Ordering.acqrel ordr) eqn : ORDR.
            { subst V_w. rewrite /TView.read_tview /TView.write_released /=; des_ifs.
              rewrite /LocFun.add; des_ifs.
              inv LOCAL2; ss.
              rewrite -View.join_assoc (View.join_comm releasedr) ORDR.
              rewrite (View.join_assoc _ releasedr releasedr).
              repeat f_equal. by apply View.le_join_l.
            }
            { subst V_w. rewrite /TView.read_tview /TView.write_released /=; des_ifs.
              rewrite /LocFun.add; des_ifs.
              inv LOCAL2; ss.
              rewrite ORDR. apply View.join_r.
            }
          }
          { split.
            { inv LOCAL2; ss.
              rewrite /TView.write_released /TView.read_tview /=.
              rewrite ORDW /LocFun.add; des_if; ss.
              des_if; last destruct ordw; ss.
              apply View.join_r.
            }
            inv LOCAL2; ss.
            rewrite /TView.write_released /TView.read_tview /TView.write_tview /=.
            des_if; last (destruct ordw; ss).
            rewrite /LocFun.add; des_if; ss.
            rewrite ORDW. des_ifs.
            { rewrite -View.join_assoc; apply View.join_le; last refl.
              rewrite View.join_comm; apply View.join_le; last refl.
              etrans; last apply View.join_l.
              inv WF. inv WF0. hexploit THREADS; eauto. intros INV; inv INV. inv TVIEW_WF. done.
            }
            { rewrite -View.join_assoc; apply View.join_le; last refl.
              rewrite View.join_comm; apply View.join_le; last refl.
              etrans; last apply View.join_l.
              inv WF. inv WF0. hexploit THREADS; eauto. intros INV; inv INV. inv TVIEW_WF.
              etrans; eauto.
            }
          }
        }
        iFrame "AW".
        rewrite /view_at AtomicPtsToX_eq /AtomicPtsToX_def.
        iFrame "HIST AA PTA".
        iSplit; auto.
        des.
        iPureIntro; ss; split.
        { split.
          { rewrite /AllocView.join /orb; des_ifs; ss. }
          { intros t; erewrite Cell.add_o; eauto; des_if; subst.
            { intros _; rewrite /seen_local /View.join /= /TimeMap.join.
              inv LOCAL2; ss; do 2 (etrans; last apply Time.join_r).
              rewrite /TimeMap.singleton /LocFun.add; des_ifs.
            }
            intros SOME%SYNCLOCAL1; rr; etrans; first apply SOME.
            rewrite /View.join /=; eapply Time.join_l.
          }
        }
        intros ts????; erewrite Cell.add_o; eauto; des_if.
        { subst; intros INV; inv INV; ss.
          split.
          { rewrite /seen_local; etrans; last apply View.join_r.
            inv LOCAL2; ss. rewrite /TimeMap.join.
            rewrite /TimeMap.singleton /LocFun.add; des_if; ss.
            by apply Time.join_r.
          }
          inv LOCAL2; ss.
          rewrite /TView.write_released /TView.read_tview RLXR RLXW /= /LocFun.add Loc.eq_dec_eq.
          apply View.join_spec.
          { etrans; last apply View.join_l.
            hexploit (SYNCLOCAL0 x2 from val'); eauto.
            { rewrite Cell.cut_spec; eauto; des_if; ss.
              { move : GET; rewrite /Memory.get /Block.get /Cell.get //=. }
              { exfalso; eapply TimeFacts.le_not_lt; first apply READABLE.
                eapply TimeFacts.lt_le_lt; eauto.
              }
            }
            intros [??]; done.
          }
          etrans; last apply View.join_r.
          des_if; first refl.
          apply View.join_le; last refl.
          do 2 (etrans; last apply View.join_l).
          inv WF. inv WF0. hexploit THREADS; eauto. intros INV; inv INV. inv TVIEW_WF; done.
        }
        intros SV%SYNCLOCAL0; split; inv SV.
        { rewrite /seen_local; etrans; eauto. rewrite /join /lat_join /= /TimeMap.join.
          by apply Time.join_l.
        }
        { etrans; eauto. by apply View.join_l. }
      }
      steps_l. step.
      iSplit; auto.
      iFrame "HA HFA TA".
      iPureIntro; ss.
      split; first done.
      split.
      { inv LOCAL1; inv LOCAL2; ss; intros ?????.
        erewrite Memory.add_o; eauto. des_if.
        { ss; des; i; clarify. destruct ordw; ss. }
        i; eapply CUT; eauto.
        erewrite <-Memory.add_accessible; eauto.
      }
      split.
      { inv LOCAL1; inv LOCAL2; ss. eapply Memory.add_closed_view; eauto. }
      split.
      { eapply PFConfiguration.estep_future; eauto.
        subst.
        econs; eauto; ss.
        { econs; eauto; ss. }
        { ss. }
      }
      split.
      { inv LOCAL1; inv LOCAL2; ss. eapply wf_prealloc_write; eauto. }
      split.
      { inv LOCAL1; inv LOCAL2; ss. inv PFG. econs; ss.
        rewrite H in FULFILL. apply Promises.Promises.fulfill_bot_inv in FULFILL. des; ss.
      }
      { intros ???. subst. rewrite IdentMap.Facts.add_o; des_if; intros INV; inv INV; ss.
        { inv LOCAL1; ss. inv LOCAL2; ss. econs; ss.
          { hexploit PFL; eauto; intros INV; inv INV; rewrite H in FULFILL.
            apply Promises.Promises.fulfill_bot in FULFILL; des; ss.
          }
          { hexploit PFL; eauto; intros INV; inv INV; ss. }
        }
        { hexploit PFL; eauto; intros INV; inv INV; ss. }
      }
    }
    { (* fail case *)
      steps_r.
      iAssert (∃ ζ_read,
        ⌜Cell.le ζ' ζ_read
        ∧ ∀ ts, Cell.get ts ζ_read =
          if (decide (ts = tsr))
          then Memory.get loc tsr (Global.memory gl2)
          else Cell.get ts ζ'⌝)%I as "[%ζ_read [%LE %GET]]".
      { destruct (Cell.get tsr ζ') as [[fromr msgr] | ] eqn : GETZETA'.
        { iExists ζ'; iPureIntro; split; first done.
          i; des_if; ss.
          subst; rewrite GETZETA'.
          apply ZETALE in GETZETA'; revert GETZETA'.
          rewrite Cell.cut_spec; des_if; ss.
        }
        { inv LOCAL1; ss.
          hexploit (@Cell.add_exists ζ' from tsr); eauto.
          { intros ??? GET2; dup GET2; move : GET0 => /ZETALE.
            rewrite Cell.cut_spec; des_if; ss.
            intros ?; hexploit Memory.get_disjoint; first done; first apply GET.
            i; des.
            { clarify. }
            done.
          }
          { eapply Memory.get_ts; eauto. }
          intros [ζ_read ?]; iExists ζ_read; iPureIntro; split; eauto using Cell.add_le.
          intros ?; erewrite Cell.add_o; eauto; des_if; subst; des_if; ss.
          rewrite GET; refl.
        }
      }

      iMod ((tview_auth_update ths (IdentMap.add tid (existT lang st2, lc2) ths)) with "TA TV")
        as "[TA TV]"; ss.

      iAssert (Ist st_src _) with "[HA TA HFA]" as "IST".
      { iExists _, (IdentMap.add _ _ _), Vcut. iFrame "HFA HA TA".
        iPureIntro; split; first refl.
        split.
        { inv LOCAL1; ss. }
        split.
        { eapply Memory.future_closed_view; eauto.
          inv LOCAL1; ss. inv WF. inv GL_WF; ss.
          econs; ss. refl.
        }
        split.
        { eapply PFConfiguration.estep_future; eauto.
          econs; eauto; ss.
          { apply Thread.Thread.step_program; cycle 1.
            { apply Local.program_step_cas_fail; eauto. }
            { ss; eauto. }
          }
          ss.
        }
        split.
        { inv LOCAL1; ss. }
        split.
        { inv LOCAL1; ss. }
        { intros ???; rewrite IdentMap.gsspec; des_if; ss; clarify.
          { hexploit PFL; eauto; inv LOCAL1; ss. by intros ? INV; inv INV; ss. }
          { i; eapply PFL; eauto. }
        }
      }
      iPoseProof (at_auth_fork_at_reader with "AA") as "#AR'".

      force_l (Val.zero ↑). steps_l. force_l (Val.zero ↑). steps_l. force_l. iSplitR "IST".
      { iSplit; first done.
        iFrame "PR TV".
        inv LOCAL1; ss.
        remember (Cell.cut _ _) as ζn.
        iExists Val.zero, ζ_read, ζn, tsr, from; subst ζn.
        unshelve (iExists _); eauto using Cell.get_ts.
        iExists val', releasedr, na.
        iSplit.
        { iPureIntro. split; first done.
          split.
          { intros ????; rewrite GET; des_if; ss; subst.
            apply ZETALE in LHS; rewrite Cell.cut_spec in LHS; revert LHS; des_if; ss.
          }
          split.
          { intros ???; rewrite GET; des_if; ss; subst; eauto using ZETALE.
            intros ?; rewrite Cell.cut_spec; des_if; ss.
            exfalso; eapply TimeFacts.le_not_lt; last done.
            etrans; eauto. apply READABLE.
          }
          split.
          { rewrite GET; des_if; ss. }
          split.
          { etrans; eauto. apply READABLE. }
          by apply TViewFacts.read_tview_incr.
        }
        iSplitR.
        { rewrite /view_at AtomicSeen_eq. iFrame "ALN"; iSplit.
          { rewrite /SeenLocal; iPureIntro; split.
            { rewrite /View.join /= /AllocView.join /orb; des_ifs. }
            intros ?; rewrite /seen_local /= GET; des_if; subst.
            { i; rewrite /TimeMap.join.
              etrans; last apply Time.join_l. etrans; last apply Time.join_r.
              rewrite /TimeMap.singleton /LocFun.add; des_if; ss.
            }
            { intros ?%SN.
              by do 2 (etrans; last apply Time.join_l).
            }
          }
          iSplit.
          { iApply (at_reader_extract with "AR'").
            intros ???; rewrite GET; des_if; subst; ss.
            { rewrite Cell.cut_spec; des_if; ss.
              exfalso; eapply TimeFacts.le_not_lt; last done; etrans; eauto. eapply READABLE.
            }
            { intros ?%ZETALE; ss. }
          }
          iSplit.
          { iPureIntro; ii; subst ζ_read.
            hexploit GET; rewrite Cell.bot_get; des_if; ss.
            rewrite GET0; ss.
          }
          { iPureIntro.
            etrans; first apply VACUR.
            by do 2 (etrans; last apply View.join_l).
          }
        }
        iLeft. iSplit.
        { iPureIntro; esplits; eauto.
          { inv COMPARE; ii; clarify.
            { inv VAL; clarify. }
            { inv VAL. inv CMP.
              { apply Loc.eqb_eq in H1; subst.
                symmetry in EQ; apply Z.eqb_neq in EQ; clarify.
              }
              { apply Loc.eqb_eq in H1; subst.
                destruct (TBid.eq_dec _ _); ss.
              }
            }
          }
          des_if.
          { apply View.join_r. }
          { by rewrite RLXR; apply View.join_r. }
        }
        (* Atomic pts-to *)
        rewrite AtomicPtsToX_eq.
        iFrame "HIST AA PTA". iSplit; first done.
        des. iSplit; done.
      }
      step_l. step.
      iFrame. done.
    }
    Unshelve. all: auto.
  (*SLOW*)Qed.
End CAS.
