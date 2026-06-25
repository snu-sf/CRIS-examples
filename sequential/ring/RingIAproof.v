Require Import CRIS.

Require Import RingHeader CellHeader
  RingA CtrlI CellA CellI
  CtrlIAproof CellIAproof.

(* Contextual Refinement Proof *)
Module RingIA. Section RingIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.

  Definition CellIG start len :=
    Mod.addL (List.map CellI.t (seq start len)).

  Lemma ctxr max_size (sps spt : specmap) :
    ctx_refines
      ((CtrlI.t max_size)     ★ (CellIG 0 max_size),
       emp%I)
      ((RingA.t max_size sps) ★ (CtrlIA.CellG spt 0 max_size),
       (RingA.init_cond max_size) ∗ ([∗ list] i↦x ∈ seq 0 max_size, CellA.init_cond i))%I.
  Proof using.
    etrans; cycle 1.
    - eapply ctxr_cond_frameR.
      eapply main_adequacy.
      apply CtrlIA.sim.
    - rewrite mod_addc_empty_l.
      eapply ctxr_frameL.
      induction max_size; i.
      + eapply ctxr_consequence. eauto.
      + unfold CellIG, CtrlIA.CellGS, CtrlIA.CellG.
        rewrite !seq_S !map_app !mod_addL_app.
        etrans; [etrans|]; [|apply ctxr_compose_hor|]; cycle 3.
        * eapply ctxr_consequence.
          i. rewrite {1}big_sepL_app.
          iIntros "(H1 & H2)". iSplitL "H1"; [iApply "H1"|iApply "H2"].
        * eapply ctxr_consequence.
          i. do 2 instantiate (1:=emp%I). eauto.
        * etrans. { apply IHmax_size. }
          eapply ctxr_consequence.
          i. eauto.
        * s. rewrite !right_id.
          etrans.
          { eapply main_adequacy. eapply CellIA.sim. }
          eapply ctxr_consequence.
          i. rewrite length_seq. et.
  Qed.

End RingIA. End RingIA.
