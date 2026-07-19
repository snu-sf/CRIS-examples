Require Import CRIS.common.CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section fence.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma simF_fence : ISim.sim_fun open MA MI Ist (fid PFMemHdr.fence).
  Proof.
    cStartFunSim.
    cStepsS. destruct _q as [[[tid ordr] ordw] V].
    iDestruct "ASM" as "[-> [[-> %] TV]]". cStepsT.
    iDestruct "IST" as "[%gl [%ths [%Vcut [[-> [%CUT [%CUTCL [%WF [%WF2 [%PFG %PFL]]]]]] [HA [TA FA]]]]]]".
    cStepsT. rewrite /PFMemI.check_ident.
    des_ifs; last (iPoseProof (tview_both_valid with "TA TV") as "%F"; des; ss; clarify).
    cStepsT. destruct _q as [config' STEP].
    inv STEP. s in STEP0. inv STEP0; [inv LOCAL|].
    s in STATE. inv LOCAL. inv LOCAL0.
    
    set (TView.write_fence_sc _ _ ordw) as glsc.
    assert (GL: glsc = Global.sc gl).
    { subst glsc. rewrite /TView.write_fence_sc. destruct ordw; ss. }
    subst glsc. rewrite GL. ss.

    set (gl2:=_: Global.t) at 5.
    assert (gl2 = gl) by (subst gl2; destruct gl; ss).
    rewrite H0. clear H0. set (lc2:=_: Local.t).

    cStepsT. set (st_tgt:={[_ := _]}).

    iPoseProof (tview_both_valid with "TA TV") as "%IN". des. subst V.

    iMod ((tview_auth_update ths (IdentMap.add tid (existT lang st2, lc2) ths)) with "TA TV") as "[TA TV]"; eauto.

    iAssert (Ist st_src st_tgt)%I with "[HA FA TA]" as "IST".
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
      { subst lc2; ss. rewrite IN in Heq. inv Heq.
        rewrite /TView.write_fence_sc /TView.read_fence_tview /=. destruct ordw; ss. }
      { subst lc2; ss. rewrite IN in Heq. inv Heq.
        rewrite /TView.write_fence_sc /TView.read_fence_tview /=. destruct ordw; ss. }
      { subst lc2; ss. rewrite IN in Heq. inv Heq.
        rewrite /TView.write_fence_sc /TView.read_fence_tview /=.
        destruct ordw; ss; rewrite View.join_bot_r; ss. }
    }
    cStep. iSplit; eauto.
  (*SLOW*)Qed.
End fence.
