From CRIS.common Require Import CRIS.

From CRIS.ring Require Import RingHeader CellHeader RingA CtrlI CellA CellI
  CtrlIAproof CellIAproof.

(* Contextual Refinement Proof *)
Module RingIA. Section RingIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELL: !cellGS}.

  Definition CellIG start len :=
    Mod.addL (List.map CellI.t (seq start len)).

  Lemma ctxr max_size (sps spt : specmap) :
    RingA.init_cond max_size ∗
      ([∗ list] i↦x ∈ seq 0 max_size, CellA.init_cond i) ⊢
    ctx_refines
      (CtrlI.t max_size ★ CellIG 0 max_size)
      (RingA.t max_size sps ★ CtrlIA.CellG spt 0 max_size).
  Proof using.
    assert (Hcells : ∀ n,
      ([∗ list] i↦x ∈ seq 0 n, CellA.init_cond i) ⊢
        ctx_refines (CellIG 0 n) (CtrlIA.CellG spt 0 n)).
    { intros n. induction n as [|n IH].
      + iIntros "_". rewrite /CellIG /CtrlIA.CellG /CtrlIA.CellGS /=.
        ctxr_refl.
      + rewrite /CellIG /CtrlIA.CellG /CtrlIA.CellGS.
        rewrite !seq_S !map_app !mod_addL_app big_sepL_app.
        iIntros "[HCs HC]".
        iApply ctxr_compose_hor. iSplitL "HCs".
        * iApply IH. iExact "HCs".
        * rewrite /= !right_id length_seq.
          iApply main_adequacy.
          -- eapply CellIA.sim.
          -- iExact "HC".
    }
    iIntros "[HR HC]".
    iApply (ctxr_trans _ (CtrlI.t max_size ★ CtrlIA.CellG spt 0 max_size) _).
    iSplitL "HC".
    - iApply ctxr_frameL. iApply Hcells. iExact "HC".
    - iApply main_adequacy.
      + apply CtrlIA.sim.
      + iExact "HR".
  Qed.

End RingIA. End RingIA.
