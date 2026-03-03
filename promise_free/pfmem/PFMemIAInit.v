(* Require Import CRIS.
Require Import PFMemHeader PFMemI PFMemA HistoryRA AtomicRA.
Require Import base Time TView View Cell Memory Global Time.
Require Import PFMemIAproof.

Section init.
  Import PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  Lemma simF_init : ISim.sim_fun open MA MI (init_cond syn size) Ist (fid PFMemHdr.init).
  Proof.
    cStartFunSim. cStepsS. iDestruct "ASM" as "[[-> TV] ->]". cStepsT.
    rename q2 into 𝓥, q3 into tid, q4 into tid_spawner.
    iDestruct "IST" as "[% [% [% [[-> [% [% [%WF [% [%PFG %PFL]]]]]] [HA [TA HFA]]]]]]".
    cStepsT.

    iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND %]]]"; rewrite FIND.
    destruct (IdentMap.find tid ths) eqn : FIND2; first by cStepsT. cStepsT. cSimpl.
    remember (Local.mk _ _ _ _ _) as lc_new.
    iMod (tview_auth_alloc ths tid _ lc_new with "TA") as "[TA TV2]"; eauto.
    cForceS (Val.zero↑). cStepsS. cForceS (Val.zero↑). cStepsS. cForceS.
    subst lc_new; ss.
    iFrame "TV TV2". iSplit; [iSplit | ]; ss. cStepsS. cStep.
    iFrame "HA HFA".
    iSplit; first done.
    iExists _; iSplit.
    (* initial local preserves well-formedness *)
    { iPureIntro; split; first done.
      split; first done.
      split; first done.
      split.
      { inv WF; econs; ss. inv WF0; econs; ss.
        { intros tid1 ??? tid2 ??? NEQ; rewrite ?IdentMap.gsspec; des_ifs; ss; last by eapply DISJOINT.
          { intros INV GET2; inv INV; econs; ss; eauto using Memory.bot_disjoint.
            erewrite TID; eauto.
          }
          { intros GET1 INV; inv INV; econs; ss; first symmetry; eauto using Memory.bot_disjoint.
            erewrite TID; eauto.
          }
        }
        { destruct lang. hexploit (THREADS tid_spawner); eauto; intros INV; inv INV.
          intros ????; rewrite IdentMap.gsspec; des_ifs; ss.
          { intros INV; inv INV; econs; ss. 
            { apply Promises.Promises.bot_finite. }
            { apply Promises.FreePromises.bot_finite. }
            { apply Memory.bot_le. }
            { apply Memory.bot_reserve_only. }
            { apply Memory.bot_finite. }
          }
          eapply THREADS; eauto.
        }
        { inv PFG; rewrite H4; intros ?; rewrite /Promises.Promises.bot //. }
        { inv PFG; rewrite H5; intros ?; rewrite /Promises.Promises.bot //. }
        { intros ????; rewrite IdentMap.gsspec; des_ifs; ss.
          { intros INV; inv INV; ss. }
          { intros ?; eapply TID; eauto. }
        }
      }
      split; ss.
      split; ss.
      { intros ???; rewrite IdentMap.gsspec; des_ifs; ss.
        { intros INV; inv INV; ss. }
        { intros ?; eapply PFL; eauto. }
      }
    }
    iFrame "TA".
  Qed.
End init. *)
