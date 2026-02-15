Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section alloc.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma hist_auth_alloc_vs lc1 gl1 sz lc2 gl2 loc Vcut
      (WF : Global.wf gl1)
      (WFP : wf_prealloc (Global.memory gl1))
      (STEP : Local.alloc_step lc1 gl1 loc sz lc2 gl2)
      (CUT : Memory.closed_view Vcut (Global.memory gl1)) :
    hist_auth (Memory.cut Vcut (Global.memory gl1))
    ==∗ hist_auth (Memory.cut (View.join Vcut (View.alloc_view_singleton loc sz)) (Global.memory gl2))
        ∗ [∗ list] i ↦ C ∈ (repeat (Cell.init Val.Vundef) (Z.to_nat sz)), hist (loc >> i) 1 C.
  Proof using _ATOMIC.
    iIntros "H". rewrite hist_auth_eq /hist_auth_def.
    iMod (own_update with "H") as "[H1 H2]"; [| iSplitL "H1"; [iModIntro; done|]].
    { eapply auth_update_alloc, discrete_fun_local_update; intros l.
      rewrite ?Memory.cut_accessible.
      instantiate (1:=λ l,
        if (decide (¬ Memory.accessible l (Global.memory gl1) ∧ Memory.accessible l (Global.memory gl2)))
        then (Some (DfracOwn 1, to_agree (Cell.init Val.Vundef))) else None).
      inv STEP; ss.
      destruct (Memory.accessible l mem2) eqn : ACC2.
      { hexploit Memory.alloc_accessible3; eauto. { inv WF; ss. }
        intros [ALLOCED | NALLOC].
        { des. destruct (Memory.accessible l (Global.memory gl1)) eqn : Hacc; ss.
          { exfalso; eapply Memory.prealloced_is_not_accessible; eauto. }
          rewrite Memory.cut_get_cell.
          etrans; first eapply alloc_option_local_update; cycle 1.
          (* Newly alloced = Cell.init *)
          { remember (Cell.cut _ _) as C; enough (EQ : C = Cell.init Val.Vundef); [rewrite EQ //|].
            apply Cell.ext; subst; intros ts.
            rewrite /View.join /= /TimeMap.join.
            hexploit (Memory.alloc_closed_view_bot); eauto. { inv WF; ss. }
            instantiate (1:=Loc.ofs l).
            remember (Loc.mk _ _ _) as l'; assert (Heq : l' = l).
            { clarify. destruct loc; destruct l; ss; clarify; refl. }
            subst. rewrite Heq. intros ->.
            rewrite DenseOrderFacts.le_join_r; eauto using Time.bot_spec.
            hexploit Memory.alloc_get_cell; eauto; intros ->.
            rewrite TimeMap.singletons_spec; des_ifs; cycle 1.
            { inv ALLOC; ss; exfalso; apply n; split; destruct l; rewrite /Loc.get_tbid; clarify; ss. }
            inv ALLOC; ss.
            hexploit (WFP l).
            { inv WF. inv MEM_WELL_ALLOCED. destruct l; ss. }
            intros ->.
            rewrite Cell.cut_spec Cell.init_get; des_ifs.
            apply TimeFacts.le_not_lt in l0; ss; refl.
          }
          ss.
        }
        { des. rewrite ACCESSIBLE. des_ifs; des; ss.
          (* previous cells = identical *)
          rewrite ?Memory.cut_get_cell. hexploit Memory.alloc_get_cell; eauto; intros ->.
          rewrite /View.join /= /TimeMap.join.
          rewrite TimeMap.singletons_spec; des_ifs.
          { des; clarify; destruct l, loc; rewrite /Loc.get_tbid in LOC; ss; clarify. }
          rewrite DenseOrderFacts.le_join_l; eauto using Time.bot_spec. ss.
        }
      }
      destruct (Memory.accessible l (Global.memory gl1)) eqn:ACC1.
      { hexploit Memory.alloc_accessible; eauto. { inv WF; ss. }
        i; clarify.
      }
      des_ifs; des; ss.
    }
    assert (Loc.ofs loc = 0)%Z.
    { inv STEP; inv ALLOC; ss. }
    assert (SZ : ∃ n, sz = Z.of_nat n).
    { exists (Z.to_nat sz); inv STEP; inv ALLOC. rewrite Z2Nat.id; ss. }
    destruct SZ as [n ->]. rewrite Nat2Z.id.
    iAssert ( |==> own hist_name (◯ ((λ l : Loc.t,
      if (decide (Loc.get_tbid l = Loc.get_tbid loc ∧ (0 <= (Loc.ofs l) < n)%Z))
      then Some (DfracOwn 1, to_agree (Cell.init Val.Vundef))
      else None) : HistoryRA.histR_aux))
    )%I with "[H2]" as "> H".
    { iApply (own_update with "H2"). f_equiv; extensionality l; ss.
      des_ifs; des.
      { inv STEP. inv WF. exfalso; apply n0; hexploit (Memory.alloc_accessible3); eauto; i; des; ss. }
      { inv STEP. inv ALLOC; ss.
        hexploit (Memory.alloc_accessible1); eauto.
        { instantiate (1:=l). destruct l; rewrite /Loc.get_tbid; clarify; split; ss. subst tid; ss. }
        intros ACC1; hexploit Memory.alloc_accessible3; eauto. { inv WF; ss. }
        intros [ACC1' | CONT]; cycle 1.
        { des; exfalso; apply LOC; rewrite /Loc.get_tbid H0 a; ss. }
        { exfalso; apply n0; split; des; eauto.
          { ii; eapply Memory.prealloced_is_not_accessible; eauto. }
          rewrite H0 in ACC1; done.
        }
      }
    }
    iStopProof. clear STEP; revert n; induction n; [iIntros "_"; ss|].
    iIntros "F"; iMod (own_update with "F") as "[F1 F2]"; cycle 1.
    { iMod (IHn with "F1") as "F1".
      replace (S n) with (n + 1) by lia; rewrite repeat_app /= big_sepL_app /=; iFrame "F1".
      iModIntro; iSplitL "F2"; last done.
      rewrite hist_eq /hist_def; done.
    }
    rewrite repeat_length Nat.add_0_r -auth_frag_op.
    f_equiv. extensionality l; rewrite discrete_fun_lookup_op. des_ifs.
    { rewrite discrete_fun_lookup_singleton_ne; ss.
      revert a a0; rewrite /Loc.get_tbid; destruct loc, l; ss; i; des; clarify. 
      rewrite /HistoryRA.shift. ii. inv H. lia.
    }
    { enough (l = loc >> n).
      { subst l; rewrite discrete_fun_lookup_singleton; ss. }
      revert a n0; rewrite /Loc.get_tbid.
      destruct l, loc; ss; i; des; clarify.
      enough (ofs = n). { rewrite /HistoryRA.shift; clarify. }
      destruct (decide (ofs >= n))%Z; first lia.
      exfalso; apply n0; split; ss; lia.
    }
    { exfalso; apply n0; split; des; ss; try lia. }
    { enough (l <> loc >> n).
      { rewrite discrete_fun_lookup_singleton_ne; ss; ii; clarify. }
      ii; clarify; apply n0; split; destruct loc; rewrite /Loc.get_tbid; ss; subst; lia.
    }
  (*SLOW*)Qed.

  Lemma simF_alloc : ISim.sim_fun open MA MI Ist (fid PFMemHdr.alloc).
  Proof using.
    iStartSim.
    steps_l. destruct _q as [[tid sz] V].
    iDestruct "ASM" as "[-> [-> TV]]".
    iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
    rewrite /PFMemI.check_ident.
    steps_r.
    iPoseProof (tview_both_valid with "TA TV") as "%F"; des; clarify. rewrite F. steps_r.
    destruct _q as [[loc config'] STEP].
    dup STEP; inv STEP0. inv STEP1; inv LOCAL.
    iMod (hist_auth_alloc_vs with "HA") as "[HA PTS]"; eauto.
    { inv WF; ss. }
    steps_r. hss. remember (Configuration.mk (IdentMap.add _ _ _) _) as config'.
    iPoseProof (tview_auth_update with "TA TV") as "> [TA TV]"; ss.
    iMod (hist_freeable_auth_alloc with "FA") as "[F FA]"; eauto. { inv WF; ss. }
    iAssert (Ist st_src _) with "[HA TA FA]" as "IST".
    { iExists gl2,
        (Configuration.threads config'),
        (View.join Vcut (View.alloc_view_singleton loc sz)). iSplitR.
      { iPureIntro; split; first eauto. splits.
        { intros loc1 ???? FIND Acc.
          inv LOCAL0; hexploit (Memory.alloc_accessible3); eauto.
          { inv WF; inv GL_WF; eauto. }
          intros [?|?].
          { des; ss. eapply WF2 in H1. hexploit Memory.alloc_get_cell; eauto.
            intros Heq; rewrite -Heq in H1; rewrite -Memory.get_memory_cell H1 in FIND.
            rewrite Cell.init_get in FIND; case_match; ss; clarify.
            etrans; last eapply TimeMap.join_r.
            rewrite TimeMap.singletons_spec; case_decide as temp; [refl|exfalso].
            destruct loc1, loc; ss; clarify.
            apply temp; split; first ss.
            inv ALLOC; lia.
          }
          { ss. etrans; last eapply TimeMap.join_l.
            eapply CUT; des; eauto. erewrite <-Memory.alloc_o; eauto.
          }
        }
        { apply Memory.join_closed_view.
          { inv LOCAL0. eapply Memory.alloc_closed_view; eauto. inv WF. inv GL_WF; eauto. }
          { inv LOCAL0. eapply Memory.alloc_view_singleton_closed_view; eauto.
            inv WF. inv GL_WF. inv MEM_CLOSED. eauto.
          }
        }
        { eapply PFConfiguration.estep_future; eauto. subst config'. eauto. }
        { inv WF. inv GL_WF. inv LOCAL0. eapply wf_prealloc_alloc; eauto. }
        { destruct gl, gl2; inv LOCAL0; ss. }
        { ii; destruct (decide (tid0 = tid)); subst.
          { hexploit (PFL tid); eauto. s in H; rewrite IdentMap.gss in H; inv H.
            inv LOCAL0; inv ALLOC; ss.
          }
          { rewrite IdentMap.gso in H; clarify; hexploit (PFL tid0); eauto. }
        }
      }
      subst config'; iFrame.
    }
    force_l ((Val.Vptr loc)↑). steps_l. force_l ((Val.Vptr loc)↑). steps_l.
    force_l. iSplitL "PTS TV F".
    { iSplit; eauto. iFrame "TV F".
      iSplit.
      { iPureIntro; split; first done. hexploit Local.alloc_step_future; eauto.
        { inv WF. inv WF0; eauto. }
        { inv WF; eauto. }
        { i; des; eauto. }
      }
      rewrite /own_loc_na_vec /view_at Nat2Z.id.
      iStopProof.
      assert (ACC : ∀ n, n < sz → Memory.accessible (loc >> n) (Global.memory gl2)).
      { intros n LE; inv LOCAL0; ss. hexploit Memory.alloc_accessible1; eauto.
        destruct loc; rewrite /Loc.get_tbid; ss; split; eauto.
        inv ALLOC; ss; lia.
      }
      assert (LE : sz <= sz) by lia.
      revert ACC LE; generalize sz at 2 4 5 as n. induction n; first ss.
      intros ACC LE; iIntros "H"; replace (S n) with (n + 1) by lia.
      rewrite !repeat_app !big_sepL_app.
      iDestruct "H" as "[H1 H2]"; iPoseProof (IHn with "H1") as "$".
      { intros n0 ?; eapply ACC; eauto. }
      { lia. }
      ss. iDestruct "H2" as "[H _]"; iSplitL; ss.
      rewrite own_loc_na_eq /own_loc_na_def.
      unshelve (iExists Time.bot, Time.init, _, View.bot, true); eauto using Time.init_spec.
      iSplit; last (iPureIntro; eapply View.bot_spec).
      rewrite ?repeat_length Nat.add_0_r /own_loc_prim.
      iSplit.
      { iPureIntro. split.
        { inv LOCAL0; ss. rewrite /AllocView.join /orb; des_ifs.
          rewrite /AllocView.singleton; des_ifs; ss. destruct loc; ss.
        }
        exists Time.init, (Time.bot, Message.elt Val.Vundef). split.
        { rewrite Cell.singleton_get; ss. }
        rewrite /seen_local.
        inv LOCAL0; ss. clear STEP.
        etrans; last apply TimeMap.join_r.
        rewrite TimeMap.singletons_spec; destruct loc; rewrite /Loc.get_tbid; des_ifs.
        exfalso; apply n0; splits; ss; try lia.
      }
      eapply eq_ind; first iExact "H".
      f_equal. apply Cell.ext; intros ts.
      rewrite Cell.init_get Cell.singleton_get; des_ifs.
    }
    step_l. step.
    subst config'; iFrame. done.
  Unshelve. all: eauto.
  (*SLOW*)Qed.
End alloc.
