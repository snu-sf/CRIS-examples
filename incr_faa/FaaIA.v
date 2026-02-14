Require Import CRIS.
Require Import SchTactics MemTactics.
Require Export FaaHeader FaaI FaaA.

Module FaaIA. Section FaaIA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _MEM: !memGS, _SCH: !schGS}.
  Context (sp : specmap).

  Local Definition IstFull := (IstProd (IstSB FaaA.t.(Mod.scopes) IstTrue) IstEq).
  Local Definition MA := (FaaA.t ★ MemA.t sp).
  Local Definition MI := (FaaI.t ★ MemA.t sp).

  Lemma faa2_simF : ISim.sim_fun open MA MI IstFull (Some FaaHdr.faa2).
  Proof using.
    iStartSim.

    steps_l.
    destruct (arg ↓) as [[|v [|v' l]]|]; steps_l; ss.
    destruct v as [|[blk ofs]|]; step_l; ss.

    steps_r. sch_yield_rr "IST". steps_r.
    rewrite /MemHdr.faa; steps_r.

    sch_yield_l; steps_l. rename _q into v.
    load_r "ASM". store_r "ASM". force_l; iFrame "ASM". steps_l.
    sch_yield_rr "IST".

    sch_yield_l; steps_l. clear v. rename _q into v.
    load_r "ASM". store_r "ASM".
    force_l; iFrame "ASM".
    sch_yield_rr "IST". sch_yield_l. step. iFrame; done.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI emp%I IstFull.
  Proof.
    init_sim.
    { eapply faa2_simF. }
    { iIntros "_"; iExists _, _, _, _; iSplit; eauto. }
  Qed.
End FaaIA. End FaaIA.
