Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import RRSHeader RRSA.
Require Import NDSHeader NDSA.
(** NonDet Mem **)
Require Import MemHeader MemA.
(** Det Mem **)
Require Import MemHdr MemLib HybridMem.
Require Import RRSNodeHeader RRSNodeI RRSNodeA.
Require Import NDSNodeHeader NDSNodeI NDSNodeA.
Require Import SCHMainI SCHMainA.
Require Import ltac2_lib.

Module SCHMainIA. Section SCHMainIA.
  Import SCHMainA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !SchA.schGS}.
  Context `{_rrsG: !RRSA.rrsGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemA.memGS}.
  Context `{_hymG: !MemLib.memGS}.
  Context `{_nodeG: !RRSNodeA.nodeGS}.

  Context (sp sp_sch_user sp_rrs_user sp_nds_user: specmap).
  Context (Hschglob: sp_sch_user ⊆ sp).
  (* Context (Hschrrs: sp_rrs_user ⊆ sp_sch_user). *)
  (* Context (Hschnds: sp_nds_user ⊆ sp_sch_user). *)
  Context (Hsch: (SchA.sp sp_sch_user ⊤) ⊆ sp).
  Context (Hrrs: (RRSAS.sp sp_rrs_user ⊤ snd SchA.PYIP) ⊆ sp_sch_user).
  Context (Hnds: (NDSA.sp sp_nds_user ⊤ _ snd SchA.PYIP) ⊆ sp_sch_user).
  Context (Hrrsnode: (RRSNodeAS.sp ⊤) ⊆ sp_rrs_user).
  Context (Hndsnode: (NDSNodeA.sp ⊤) ⊆ sp_nds_user).

  Local Definition MA := (SCHMainA.t sp).
  Local Definition MI := (SCHMainI.t).

  Lemma simF_main : ISim.sim_fun open MA MI IstTrue entry.
  Proof using Hschglob (* Hschrrs Hschnds *) Hsch Hrrs Hnds Hrrsnode Hndsnode.
    cStartFunSim.

    cStepsS. iDestruct "ASM" as "(-> & RI & RV & NI & T)". rewrite /SCHMainI.main. cStepsS.
    simpl_sp. destruct _q; ss.

    rewrite /SchA.spawn_spec.
    set (pre := (λ svarg sarg, ⌜svarg = RRSNodeHdr.f_main↑↑ ∧ svarg = sarg⌝ ∗ RRSAS.InitRRS ∗ RRSNodeAS.full_val (Vint 0))%I).
    set (postS := (λ (svret sret : SAny.t), existT 0 (⌜False⌝)%SAT)%I).
    cForceS (pre, postS). subst pre postS.
    cStepsS. cForcesS. iSplitL "RI RV".
    { do 3 iExists _. iSplit; eauto. iFrame. rewrite /SchA.fn_spawnable. iSplit; eauto. iExists _. iSplit; eauto.
      { iPureIntro. simpl_sp. et. }
      rewrite /SchA.fspec_spawnable. iIntros (??) "%".
      destruct H as [x [Hpre Hpost]]; ss. rewrite /precond /= /precond in Hpre. rewrite /postcond /= /postcond in Hpost.
      destruct x as [[stid mtid] []].
      set (m := (mtid, stid, (λ (svarg sarg : SAny.t), ⌜svarg = sarg ∧ sarg = tt↑↑⌝ ∗ RRSNodeAS.full_val (Vint 0))%I, existT 0 (RRSNodeAS.x_value_tid 0)%I)).
      iExists (precond (RRSAS.init_spec sp_rrs_user ⊤ snd SchA.PYIP) m).
      iExists (postcond (RRSAS.init_spec sp_rrs_user ⊤ snd SchA.PYIP) m).
      iSplit; eauto.
      { iPureIntro. rewrite /RRSAS.init_spec /fspec_winv /fspec_virtual /precond /postcond; ss.
        eexists m; esplits; eauto. }
      iIntros (??) "PRE". iModIntro. iSplitL "PRE".
      { rewrite /RRSAS.init_spec /precond /= /fspec_virtual /precond /=. subst P1.
        iDestruct "PRE" as "(W & T & % & % & % & % & RI & RN)"; des; subst; cSimpl. iFrame "W".
        iExists _. iSplitR; eauto. iExists _. iSplitR; eauto. iFrame.
        iDestruct "T" as "(t & T & Y)". iFrame. iSplit; eauto.
        rewrite /RRSAS.fn_spawnable_rr_init. iExists _. iSplit; eauto.
        { iPureIntro. simpl_sp; et. }
        rewrite /RRSAS.fspec_spawnable_rr_init. iIntros (??) "%".
        rewrite /fspec_winv /fspec_virtual in H; ss; destruct H as [x [Hpre Hpost]]; ss; rewrite /precond /= /precond in Hpre; rewrite /postcond /= /postcond in Hpost.
        destruct x as [[mtid0 stid0] ssch].
        set (m0 := (stid0, ssch)).
        iExists (precond (RRSNodeAS.f_main_spec ⊤) m0).
        iExists (postcond (RRSNodeAS.f_main_spec ⊤) m0).
        iSplit; eauto.
        { iPureIntro. exists m0. esplits; eauto. }
        iIntros (??) "PRE". iModIntro. iSplitL; eauto.
        { rewrite /precond /RRSNodeAS.f_main_spec /=. subst P1.
          iDestruct "PRE" as "(W & % & % & T & RI & % & % & % & % & RN)"; des; subst; cSimpl.
          iFrame; eauto. }
        iIntros (??) "POST". iModIntro. subst Q1.
        rewrite /postcond /RRSNodeAS.f_main_spec /=.
        iDestruct "POST" as "(W & % & % & T)"; des; subst; cSimpl.
        iFrame; eauto.
      }
      iIntros (??) "POST". iModIntro. subst Q1. rewrite /postcond /RRSAS.init_spec /=.
      iDestruct "POST" as "(W & % & % & F)". ss.
    }
    cStepsS. cStepsT. cCall "IST" as (???) "IST".
    cStepsS.
    iDestruct "ASM" as "(% & % & Join)"; des; subst; cSimpl. simpl_sp.
    cStepsT. cStepsS.

    rewrite /SchA.spawn_spec.
    set (pre := (λ svarg sarg, ⌜svarg = NDSNodeHdr.f_main↑↑ ∧ svarg = sarg⌝ ∗ NDSA.InitNDS)%I).
    set (postS := (λ svret sret, existT 0 (⌜svret = tt↑↑ ∧ svret = sret⌝)%SAT)%I).
    cForceS (pre, postS). subst pre postS.
    cStepsS. cForcesS. iSplitL "NI Join".
    { do 3 iExists _. iSplit; eauto. iFrame. rewrite /SchA.fn_spawnable. iSplit; eauto. iExists _. iSplit; eauto.
      { iPureIntro. simpl_sp; et. }
      rewrite /SchA.fspec_spawnable. iIntros (??) "%".
      destruct H as [x [Hpre Hpost]]; ss. rewrite /precond /= /precond in Hpre. rewrite /postcond /= /postcond in Hpost.
      destruct x as [[stid mtid] []].
      set (m := ((mtid, stid), ((λ svarg sarg, (⌜svarg = tt↑↑ ∧ svarg = sarg⌝ : iProp Σ)%I) : SAny.t -d> SAny.t -d> iProp Σ), ((λ svarg sarg, existT 0 (⌜svarg = tt↑↑ ∧ svarg = sarg⌝))%SAT : SAny.t -d> SAny.t -d> {n : level & GTerm.t n}))).
      iExists (precond (NDSA.init_spec sp_nds_user ⊤ _ snd SchA.PYIP) m).
      iExists (postcond (NDSA.init_spec sp_nds_user ⊤ _ snd SchA.PYIP) m).
      iSplit; eauto.
      { iPureIntro. rewrite /NDSA.init_spec /fspec_winv /fspec_virtual /precond /postcond; ss.
        eexists m; esplits; eauto. }
      iIntros (??) "PRE". iModIntro. iSplitL "PRE".
      { rewrite /NDSA.init_spec /precond /= /fspec_virtual /precond /=. subst P1.
        iDestruct "PRE" as "(W & T & % & % & % & % & NI)"; des; subst; cSimpl. iFrame "W".
        iExists _. iSplitR; eauto. iExists _. iSplitR; eauto. iFrame.
        iDestruct "T" as "(t & T & Y)". iFrame. iSplit; eauto.
        rewrite /NDSA.fn_spawnable. iExists _. iSplit; eauto.
        { iPureIntro. simpl_sp; et. }
        rewrite /NDSA.fspec_spawnable. iIntros (??) "%".
        rewrite /fspec_winv /fspec_virtual in H; ss; destruct H as [x [Hpre Hpost]]; ss; rewrite /precond /= /precond in Hpre; rewrite /postcond /= /postcond in Hpost.
        destruct x as [[mtid0 stid0] ssch].
        set (m0 := (mtid0, stid0, ssch, tt)).
        iExists (precond (NDSNodeA.f_main_spec ⊤) m0).
        iExists (postcond (NDSNodeA.f_main_spec ⊤) m0).
        iSplit; eauto.
        { iPureIntro. exists m0. esplits; eauto. }
        iIntros (??) "PRE". iModIntro. iSplitL; eauto.
        { rewrite /precond /NDSNodeA.f_main_spec /=. subst P1.
          iDestruct "PRE" as "(W & % & % & T & % & % & %)"; des; subst; cSimpl.
          iFrame; eauto. }
        iIntros (??) "POST". iModIntro. subst Q1.
        rewrite /postcond /NDSNodeA.f_main_spec /=.
        iDestruct "POST" as "(W & T & %)"; des; subst; cSimpl.
        iFrame; eauto. iExists _; iSplit; eauto. iExists _; iSplit; eauto.
        solve_base_sl_red.
      }
      iIntros (??) "POST". iModIntro. subst Q1. rewrite /postcond /NDSA.init_spec /=.
      iDestruct "POST" as "(W & % & % & F)". ss.
    }

    cStepsS. cCall "IST" as (???) "IST". cStepsT. cStepsS.
    iDestruct "ASM" as "(% & % & JoinF')"; des; subst; cSimpl.

    sYieldIR "IST" "T". sYieldS.
    cStepsS. cForcesS. iSplitR; eauto.
    cStep. iFrame; eauto.
  Qed.

  Lemma sim : ISim.t open MA MI emp%I IstTrue.
  Proof using Hschglob (* Hschrrs Hschnds *) Hsch Hrrs Hnds Hrrsnode Hndsnode.
    cStartModSim.
    - eauto.
    - eapply simF_main.
  Qed.

End SCHMainIA. End SCHMainIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !SchA.schGS}.
  Context `{_rrsG: !RRSA.rrsGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemA.memGS}.
  Context `{_hymG: !MemLib.memGS}.
  Context `{_nodeG: !RRSNodeA.nodeGS}.

  Lemma ctxr sp sp_sch_user sp_rrs_user sp_nds_user
    (Hschglob: sp_sch_user ⊆ sp)
    (* (Hschrrs: sp_rrs_user ⊆ sp_sch_user) *)
    (* (Hschnds: sp_nds_user ⊆ sp_sch_user) *)
    (Hsch: (SchA.sp sp_sch_user ⊤) ⊆ sp)
    (Hrrs: (RRSAS.sp sp_rrs_user ⊤ snd SchA.PYIP) ⊆ sp_sch_user)
    (Hnds: (NDSA.sp sp_nds_user ⊤ _ snd SchA.PYIP) ⊆ sp_sch_user)
    (Hrrsnode: (RRSNodeAS.sp ⊤) ⊆ sp_rrs_user)
    (Hndsnode: (NDSNodeA.sp ⊤) ⊆ sp_nds_user) :
    ctx_refines
      (SCHMainI.t   , emp%I)
      (SCHMainA.t sp, emp%I).
  Proof using. eapply main_adequacy, (SCHMainIA.sim sp sp_sch_user sp_rrs_user sp_nds_user); eauto. Qed.

End ctxr.
