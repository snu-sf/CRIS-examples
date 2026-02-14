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
      ((RingA.t max_size sps) ★ (CtrlIA.CellG spt 0 max_size),
       (RingA.init_cond max_size) ∗ ([∗ list] i↦x ∈ seq 0 max_size, CellA.init_cond i))%I
      ((CtrlI.t max_size)     ★ (CellIG 0 max_size),
       emp%I).
  Proof using.
    etrans.
    - eapply ctxr_cond_frameR.
      eapply main_adequacy.
      apply CtrlIA.sim.
    - rewrite -mod_addc_empty_l.
      eapply ctxr_frameL.
      induction max_size; i.
      + eapply ctxr_cond_strengthen. eauto.
      + unfold CellIG, CtrlIA.CellGS, CtrlIA.CellG.
        rewrite !seq_S !map_app !mod_addL_app.
        etrans; [|etrans]; [|apply ctxr_compose_hor|]; cycle 3.
        * eapply ctxr_cond_strengthen.
          i. do 2 instantiate (1:=emp%I). eauto.
        * eapply ctxr_cond_strengthen.
          i. rewrite {1}big_sepL_app.
          iIntros "(H1 & H2)". iSplitL "H1"; [iApply "H1"|iApply "H2"].
        * etrans; cycle 1. { apply IHmax_size. }
          eapply ctxr_cond_strengthen.
          i. eauto.
        * s. rewrite -!mod_add_empty_r.
          etrans; cycle 1.
          { eapply main_adequacy. eapply CellIA.sim. }
          eapply ctxr_cond_strengthen.
          i. rewrite Nat.add_0_r length_seq. iIntros "(H &_)". eauto.
  Qed.

End RingIA. End RingIA.
