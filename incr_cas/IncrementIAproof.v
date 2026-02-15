Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA MemTactics.
Require Import IncrementHeader IncrementI IncrementA.

Module IncrementIA. Section IncrementIA.
  Context `{!crisG Γ Σ α β τ _S _I, _MEM: !memGS, _SCH: !schGS}.
  Context (sp : specmap).

  Local Definition IstFull := (IstProd (IstSB IncrementA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (IncrementA.t ★ (MemA.t sp)).
  Local Definition MI := (IncrementI.t ★ (MemA.t sp)).

  Lemma increment_simF : ISim.sim_fun open MA MI IstFull (fid IncrementHdr.increment).
  Proof.
    iStartSim.
    steps_r. steps_l.
    destruct (arg ↓) as [[|v [|v' l]]|]; step_l; ss.
    destruct v as [|[blk ofs]|]; step_l; ss. steps_r.

    sch_yield_rr "IST". sch_yield_rr "IST".
    sch_yield_l. norm_l.

    iApply wsim_reset.
    iStopProof. revert st_src. combine_quant st_tgt.
    eapply wsim_coind.
    iIntros (g' _ CIH [st_t st_s]) "IST /=".
    destruct_quant CIH.

    unfold_iterC_r. steps_r.
    unfold_iterC_l. steps_l.
    sch_yield_rr "IST".

    sch_yield_l. steps_l. rename _q into v.

    load_r "ASM". force_l false. steps_l. force_l; iFrame "ASM". steps_l. sch_yield_l. steps_l.
    unfold_iterC_l. steps_l.

    sch_yield_rr "IST". sch_yield_rr "IST".

    sch_yield_l. steps_l. rename _q into v'.
    iApply (wsim_mem_cas with "ASM"); [prove_inline_cond|ss|eauto| | | ].
    { rewrite /MemA.compare_val; des_ifs. }
    { instantiate (1:=emp%I); done. }
    { iIntros "_"; iExists 1%Qp, 1%Qp, Vundef, Vundef; ss. }
    iIntros "↦ _".

    steps_r.
    repeat case_bool_decide; subst; ss.
    { force_l true. steps_l. force_l; iFrame "↦"; steps_l.
      sch_yield_rr "IST". sch_yield_rr "IST".
      case_decide; [|ss].
      steps_r.
      sch_yield_l. steps_l. step. iSplit; done.
    }
    { force_l false.
      forces_l. iFrame "↦". steps_l.
      sch_yield_rr "IST". sch_yield_rr "IST".
      case_decide; first clarify.
      steps_r.
      sch_yield_l. steps_l.
      iApply wsim_progress. iApply wsim_base.
      iIntros "?". iApply (CIH). iFrame.
    }
  (*SLOW*)Qed.
End IncrementIA. End IncrementIA.
