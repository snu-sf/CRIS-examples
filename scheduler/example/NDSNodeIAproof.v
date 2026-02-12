Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import NDSHeader NDSA NDSTactics.
Require Import MemHdr MemLib HybridMem.
Require Import NDSNodeHeader NDSNodeI NDSNodeA.
Require Import ltac2_lib.

Module NDSNodeIA. Section NDSNodeIA.
  Import NDSNodeA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemLib.memGS}.

  Context (sp sp_user: specmap).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).
  Context (Hschnds: sp_user ⊆ sp).
  Context (Hnds: (NDSA.sp sp_user ⊤ T get_stid PYIP) ⊆ sp).
  Context (Hnode: (NDSNodeA.sp ⊤) ⊆ sp_user).

  Local Definition IstFull := (IstProd (IstSB (NDSNodeA.t sp).(Mod.scopes) IstTrue) IstEq).
  Local Definition init_cond := NDSNodeA.init_cond.
  Local Definition MA := (NDSNodeA.t sp ★ HybMem.t).
  Local Definition MI := (NDSNodeI.t ★ HybMem.t).

  Lemma simF_main : ISim.sim_fun open MA MI IstFull (Some NDSNodeHdr.f_main).
  Proof using Hschnds Hnds Hnode.
    iStartSim.
    
    steps_l. destruct _q as [[[mtid stid] ssch] []].
    iDestruct "ASM" as "(tidF & % & %)"; des; subst; hss.
    steps_l. steps_r.

    inline_r. hss. steps_r. force_r true. steps_r. forces_r. iSplitR; eauto.
    steps_r. iDestruct "GRT" as "[PT _]".
    rename _q into blk. replace (0 + 0%nat)%Z with 0%Z by nia.

    nds_yield_global_ir "IST" "tidF". steps_r. inline_r. steps_r. force_r true.
    steps_r. forces_r. iSplitL "PT"; [eauto|].
    steps_r. iDestruct "GRT" as "PT". nds_yield_global_ir "IST" "tidF". nds_yield_global_l.

    steps_l. steps_r. simpl_sp.
    force_l (mtid, stid, ssch,
              (λ varg arg, ⌜varg = (tt↑↑) ∧ arg = ((Vptr (blk, 0%Z))↑↑)⌝ ∗ inv_x_points_to (blk, 0%Z))%I,
              (λ vret ret, existT 0 (⌜vret = tt↑↑ ∧ ret = tt↑↑⌝%SAT))).
    steps_l.
    iMod ((inv_alloc (∃ (v: τ{ ⇣nat }), sown mem_name (mem_points_to_singleton_r (blk, 0%Z) 1 (Vint v)))%SAT) with "[PT]") as "#I"; eauto.
    { solve_base_sl_red. iExists 0. iFrame. }
    forces_l. iSplitL "tidF".
    { iExists _. iSplit; eauto. do 3 iExists _. iSplit; eauto. iSplitR "tidF"; eauto.
      rewrite /NDSA.fn_spawnable. iExists _; iSplit; eauto.
      { iPureIntro. erewrite lookup_weaken; try eapply Hnode; eauto. rewrite /NDSNodeA.sp; simpl_map; refl. }
      rewrite /NDSA.fspec_spawnable. iIntros (??) "[%x [%Hpre %Hpost]]"; ss.
      destruct x as [[mtid' stid'] ssch'].
      set (m := (mtid', stid', ssch', (blk, 0%Z)) : meta (f_spec ⊤)).
      iExists (precond (f_spec ⊤) m), (postcond (f_spec ⊤) m).
      iSplit; eauto.
      { iPureIntro. exists m. esplits; eauto. }
      iIntros (??) "PRE". iModIntro. iSplitL "PRE"; eauto.
      { subst P1. rewrite /precond /fspec_winv /fspec_virtual /= /precond /=.
        iDestruct "PRE" as "(W & % & % & T & % & % & % & INV)"; des; subst; hss.
        iFrame. iExists _; iSplit; eauto. }
      iIntros (??) "POST". iModIntro.
      subst Q1. rewrite /postcond /fspec_winv /fspec_virtual /= /postcond /=.
      iDestruct "POST" as "(W & T & % & % & %)"; des; subst; hss.
      iFrame. iExists _; iSplit; eauto. iExists _; iSplit; eauto.
      solve_base_sl_red.
    }

    steps_l. steps_l.
    call "IST". iIntros (???) "IST".
    steps_l. iDestruct "ASM" as "(% & % & % & % & TID & JoinF)"; des; subst; hss.
    steps_r. nds_yield_global_ir "IST" "TID".
    steps_r. nds_yield_global_l. steps_l.
    nds_yield_ir "IST" "TID". nds_yield_l. steps_r.

    inline_r. steps_r. force_r true. steps_r.
    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    force_r (Vint z, 1%Qp). steps_r. forces_r. iSplitL "PT"; iFrame.
    steps_r.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists _. solve_base_sl_red. }

    force_l z. nds_yield_global_ir "IST" "TID".
    steps_r. nds_yield_global_ir "IST" "TID".

    steps_r. inline_r. steps_r. force_r true. steps_r.
    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    force_r. iSplitL "PT"; iFrame.
    steps_r.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists (z + 1). solve_base_sl_red.
      replace (Z.of_nat (z + 1)%nat) with (Z.of_nat z + 1)%Z by nia. iFrame. }
    nds_yield_global_ir "IST" "TID".
    nds_yield_global_l. step. steps_r. steps_l.
    nds_yield_global_ir "IST" "TID". nds_yield_global_l. steps_l. steps_r.
    nds_yield_ir "IST" "TID". nds_yield_l. steps_l. steps_r. forces_l. iSplitL "TID"; iFrame; eauto.
    step. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma simF_f : ISim.sim_fun open MA MI IstFull (Some NDSNodeHdr.f).
  Proof using Hschnds Hnds Hnode.
    iStartSim.

    steps_l. destruct _q as [[[mtid stid] ssch] [blk ofs]].
    iDestruct "ASM" as "[TID (% & % & % & #I)]"; des; subst; hss.

    steps_l. steps_r. nds_yield_global_ir "IST" "TID".

    steps_r. inline_r. steps_r. force_r true. steps_r.

    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    force_r (Vint z, 1%Qp). steps_r. force_r. iSplitL "PT"; iFrame; eauto.
    steps_r.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists z. solve_base_sl_red. }
    nds_yield_global_ir "IST" "TID". steps_r. nds_yield_global_ir "IST" "TID". steps_r.

    inline_r. steps_r. force_r true. steps_r.
    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    force_r. iSplitL "PT"; eauto.
    steps_r.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists (z + 1). solve_base_sl_red. replace (Z.of_nat (z + 1)%nat) with (Z.of_nat z + 1)%Z by nia. iFrame. }
    nds_yield_global_ir "IST" "TID". nds_yield_global_l.
    force_l z. steps_l. nds_yield_global_l. step. steps_r. steps_l.
    nds_yield_global_ir "IST" "TID". nds_yield_global_l.
    steps_l; steps_r. nds_yield_ir "IST" "TID". nds_yield_l. steps_l.
    forces_l. iSplitL "TID"; eauto.
    step. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof using Hschnds Hnds Hnode.
    init_sim.
    - eapply simF_main.
    - eapply simF_f.
    - iIntros "I". iFrame. do 4 iExists _. iSplit; eauto.
  Qed.

End NDSNodeIA. End NDSNodeIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS}.
  Context `{_schG: !SchA.schGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemLib.memGS}.

  Lemma ctxr sp sp_user
    (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ)
    (Hschnds: sp_user ⊆ sp)
    (Hnds: (NDSA.sp sp_user ⊤ T get_stid PYIP) ⊆ sp)
    (Hnode: (NDSNodeA.sp ⊤) ⊆ sp_user) :
    ctx_refines
      (NDSNodeA.t sp ★ HybMem.t, NDSNodeA.init_cond)
      ((NDSNodeI.t   ★ HybMem.t, emp%I)).
  Proof using. eapply main_adequacy, (NDSNodeIA.sim sp sp_user); eauto. Qed.

End ctxr.
