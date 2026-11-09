Require Import CRIS.common.CRIS.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemI PFMemA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.gpfsl Require Import base.
From CRIS.promise_free.model Require Import
  Time TView View Cell Memory Global Time.
From CRIS.promise_free.pfmem Require Import PFMemIAproof.

Section fence.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Section SIM_FUNS.
    Context `{STATE : !stateGS Σ}.

  Lemma simF_fence :
    ⊢ ISim.sim_fun open MA MI Ist (fid PFMemHdr.fence).
  Proof.
    cStartFunSim.
    cStepsS. destruct _q as [[[tid ordr] ordw] V].
    iDestruct "ASM" as "[-> [[-> %] TV]]". cStepsT.
    iDestruct "IST" as (gl ths Vcut)
      "[[%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]] [HA [TA [FA CONFIG]]]]".
    cStepsT. set (config_any := ((Configuration.mk ths gl)↑ : Any.t)).
    subst config_any. cStepsT. rewrite /PFMemI.check_ident.
    des_ifs; last (iPoseProof (tview_both_valid with "TA TV") as "%F"; des; ss; clarify).
    rewrite F. cStepsT. destruct _q as [config' STEP].
    inv STEP. s in STEP0. inv STEP0; [inv LOCAL|].
    s in STATE. inv LOCAL. inv LOCAL0.
    rewrite F in HTID; inv HTID.
    
    set (TView.write_fence_sc _ _ ordw) as glsc.
    assert (GL: glsc = Global.sc gl).
    { subst glsc. rewrite /TView.write_fence_sc. destruct ordw; ss. }
    subst glsc. rewrite GL. ss.

    set (gl2:=_: Global.t) at 5.
    assert (gl2 = gl) by (subst gl2; destruct gl; ss).
    rewrite H0. clear H0.
    set (lc2 := Local.mk
      (TView.write_fence_tview
        (TView.read_fence_tview (Local.tview lc1) ordr)
        (Global.sc gl) ordw)
      (Local.promises lc1) (Local.reserves lc1)
      (Local.free_promises lc1) (Local.tid lc1)).

    cStepsT.

    iMod ((tview_auth_update ths (IdentMap.add tid (existT _ st2, lc2) ths)) with "TA TV") as "[TA TV]"; eauto.

    cStepsT.
    iAssert Ist%I with "[HA FA TA CONFIG]" as "IST".
    { iFrame. iPureIntro; esplits; eauto.
      { hexploit (@PFConfiguration.step_future ThreadEvent.get_machine_event); eauto.
        { econs; eauto. econs; eauto.
          { econs 2.
            { instantiate (2:=(ThreadEvent.fence ordr ordw)); eauto. }
            eauto.
          }
          { econs. }
        }
        i; des; eauto. ss. subst lc2; eauto.
        rewrite GL in WF0. destruct gl; ss.
      }
      { i. destruct (decide (tid0 = tid)).
        { subst. rewrite IdentMap.gss in H0; inv H0.
          hexploit PFL; eauto. }
        { rewrite IdentMap.gso in H0; eauto. }
      }
    }

    cForceS (Val.zero↑). cStepsS. cForcesS. iSplitL "TV".
    { iFrame. iSplit; eauto. iPureIntro. esplits; eauto.
      { subst lc2. rewrite /TView.write_fence_tview /=.
        destruct (Ordering.le Ordering.seqcst ordw) eqn:SEQ; last done.
        exfalso; viewtac. }
      { subst lc2. rewrite /TView.write_fence_tview /=.
        destruct (Ordering.le Ordering.seqcst ordw) eqn:SEQ;
          last (rewrite View.join_bot_r; done).
        exfalso; viewtac. }
    }
    cStep. iSplit; eauto.
  (*SLOW*)Qed.
  End SIM_FUNS.

End fence.
