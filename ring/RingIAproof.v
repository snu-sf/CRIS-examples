Require Import CRIS.

Require Import RingHeader CellHeader
  RingA CtrlI CellA CellI
  CtrlIAproof CellIAproof.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Contextual Refinement Proof *)
Module RingIA. Section RingIA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !CellAGΓ Γ}.

  Definition CellIG start len :=
    HMod.addL (List.map CellI.t (seq start len)).

  Theorem correct max_size (SpcR SpcC : string -> option fspec)
    :
    ctx_refines
      ((RingA.t max_size SpcR) ★ (CtrlIA.CellG SpcC 0 max_size),
       (RingA.InitCond max_size) ∗ ([∗ list] i↦x ∈ seq 0 max_size, CellA.InitCond i))%I
      ((CtrlI.t max_size)      ★ (CellIG 0 max_size),
       emp%I).
  Proof.
    etrans.
    - eapply ctxr_cond_frameR.
      eapply main_adequacy.
      apply CtrlIA.sim.
      exact 0.
    - rewrite hmod_addc_empty_l.
      eapply ctxr_frameL.
      induction max_size; i.
      + eapply ctxr_cond_strengthen. eauto.
      + unfold CellIG, CtrlIA.CellGS, CtrlIA.CellG.
        rewrite !seq_S !map_app !hmod_addL_app.
        etrans; [|etrans]; [|apply ctxr_compose_hor|]; cycle 3.
        * eapply ctxr_cond_strengthen.
          i. do 2 instantiate (1:=emp%I). eauto.
        * eapply ctxr_cond_strengthen.
          i. rewrite {1}big_sepL_app.
          iIntros "(H1 & H2)". iSplitL "H1"; [iApply "H1"|iApply "H2"].
        * etrans; cycle 1. { apply IHmax_size. }
          eapply ctxr_cond_strengthen.
          i. eauto.
        * s. rewrite !hmod_add_empty_r.
          etrans; cycle 1.
          { eapply main_adequacy. eapply CellIA.sim. exact 0. }
          eapply ctxr_cond_strengthen.
          i. rewrite Nat.add_0_r length_seq. iIntros "(H &_)". eauto.
  Qed.

End RingIA. End RingIA.
