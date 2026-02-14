Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import RRSHeader RRSA.
Require Import MemHeader MemA.
Require Import RRSNodeHeader RRSNodeI RRSNodeA RRSTactics.
Require Import ltac2_lib.

Module RRSNodeIA. Section RRSNodeIA.
  Import RRSNodeAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_rrsG: !RRSA.rrsGS}.
  Context `{_memGS: !MemA.memGS}.
  Context `{_nodeG: !RRSNodeA.nodeGS}.

  Context (sp sp_user: specmap).
  Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).
  Context (Hschrrs: sp_user ⊆ sp).
  Context (Hrrs: (RRSAS.sp sp_user ⊤ get_stid PYIP) ⊆ sp).
  Context (Hnode: (RRSNodeAS.sp ⊤) ⊆ sp_user).

  Local Definition IstFull := (IstProd (IstSB (RRSNodeA.t sp).(Mod.scopes) IstTrue) IstEq).
  Local Definition init_cond := RRSNodeA.init_cond.
  Local Definition MA := (RRSNodeA.t sp ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user get_stid PYIP)).
  Local Definition MI := (RRSNodeI.t ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user get_stid PYIP)).

  Lemma f_spawnable n b Invs
    (RNG: 0 < n < size Invs)
    (INV: forall m, m < size Invs -> Invs !! m = Some (existT 0 (x_value_tid m))) :
    ⊢ RRSAS.fn_spawnable_rr sp_user ⊤ RRSNodeHdr.f n (f_precond (b, 0%Z)) Invs.
  Proof using Hnode.
    iIntros. rewrite /RRSAS.fn_spawnable_rr. iExists _. iSplit; eauto.
    { iPureIntro. erewrite lookup_weaken; try eapply Hnode; eauto.
      rewrite /RRSNodeAS.sp. simpl_map. refl. }
    rewrite /RRSAS.fspec_spawnable_rr. iIntros (??) "[%x [%Hpre %Hpost]]"; ss.
    destruct x as [[mtid stid] ssch].
    rewrite /precond /fspec_winv /fspec_virtual /= /precond /= in Hpre.
    rewrite /postcond /fspec_winv /fspec_virtual /= /postcond /= in Hpost.
    set (m := (existT n (mtid, stid, ssch, (b, 0%Z), Invs)) : meta (f_spec ⊤)).
    iExists (precond (f_spec ⊤) m), (postcond (f_spec ⊤) m).
    iSplit; eauto.
    { iPureIntro. exists m. esplits; eauto. }
    iIntros (??) "PRE". iModIntro. iSplitL; eauto.
    { subst P1 m. rewrite /precond /f_spec /fspec_rrsch /per_tid_fspec /precond /per_tid_fspec_rrsch /fspec_winv /precond /=.
      iDestruct "PRE" as "(W & % & % & RT & RP & (% & % & RI & % & INV) & % & % & PRE)"; des; subst; hss.
      iPoseProof (RRSAS.rrinv_prev_subset with "[RP RI]") as "%SUB"; iFrame.
      destruct mtid; try nia.
      hexploit (INV (pred_rr (S mtid) (size Invs'))).
      { eapply map_subseteq_size in SUB as SZ.
        erewrite <-(pred_rr_subst (S mtid) (size Invs) (size Invs')); eauto.
        eapply pred_rr_upperbound; eauto. }
      intros INVS.
      hexploit (INV (S mtid)); try nia. intros INVS0.
      eapply lookup_weaken in SUB as SUB0; try eapply INVS; eauto.
      eapply lookup_weaken in SUB as SUB1; try eapply INVS0; eauto.
      rewrite SUB0 in H2. inv H2.
      iFrame; eauto.
    }
    iIntros (??) "POST". iModIntro. subst Q1.
    rewrite /postcond /f_spec /fspec_rrsch /per_tid_fspec /precond /per_tid_fspec_rrsch /fspec_winv /postcond /=.
    iDestruct "POST" as "(W & % & T & % & % & % & POST)"; des; subst; hss.
    iFrame; eauto.
  Qed.

  Lemma simF_main : ISim.sim_fun open MA MI IstFull (Some RRSNodeHdr.f_main).
  Proof using Hschrrs Hrrs Hnode.
    iStartSim.

    steps_l. destruct _q as [stid ssch].
    iDestruct "ASM" as "(% & (-> & tidF & RRI & F))"; hss.

    (** alloc **)
    steps_r. inline_r. steps_r.
    forces_r. iSplit; eauto; ss.
    { instantiate (1:=1). instantiate (1:=[Vint 1]↑). iPureIntro; esplits; eauto; ss. }
    ss. steps_r. iDestruct "GRT" as "[% [% (-> & PT & _)]]".
    replace (0 + 0%nat)%Z with 0%Z by nia. rewrite <-H.
    steps_r. steps_l.

    assert (rrs_in_sp : (RRSAS.sp sp_user ⊤ get_stid PYIP) ⊆ sp).
    { etrans; eauto. }

    rrs_yield_ir "IST" "tidF".

    (** store **)
    steps_r. inline_r. steps_r. forces_r. iSplitL "PT"; eauto; ss.
    { instantiate (2 := (b, 0%Z, Vundef, Vint 0)); ss. iFrame; eauto. }
    ss. steps_r. iDestruct "GRT" as "[% [PT ->]]".
    rewrite <-H0. steps_r.

    rrs_yield_ir "IST" "tidF". rrs_yield_l. steps_l.
    erewrite lookup_weaken; try eapply Hrrs; eauto; cycle 1.
    { rewrite /RRSAS.sp. simpl_map. refl. }

    (** invariant *)
    iPoseProof (full_merge with "F") as "[H H0]".
    iMod (inv_alloc (ex_x_points_to (b, 0%Z)) with "[PT H0]") as "#I"; eauto.
    { solve_base_sl_red. iExists (Vint 0). solve_base_sl_red; iFrame. rewrite /half_val. unseal "Node". iFrame. }

    (** 1st spawn **)
    force_l (0, stid, ssch, RRSNodeAS.f_precond (b, 0%Z), {[0 := existT 0 (x_value_tid 0)]}, existT 0 (x_value_tid 1)).
    steps_l. forces_l; ss. iSplitL "RRI tidF".
    { iExists _. iFrame. iFrame "I". iSplit; eauto.
      do 3 iExists _. iSplit; eauto. iSplit; eauto.
      iApply f_spawnable; eauto.
      i. assert (m = 0 ∨ m = 1).
      { vm_compute in H1. nia. }
      { des; subst; ss. }
    }

    steps_l; steps_r. call "IST". iIntros (???) "IST".
    steps_l. rewrite map_size_insert map_size_empty lookup_empty.
    iDestruct "ASM" as (?) "[% [tidF [RRI [% %]]]]"; des; subst; hss.
    steps_r.

    rrs_yield_ir "IST" "tidF". rrs_yield_l. steps_l.
    erewrite lookup_weaken; try eapply Hrrs; eauto; cycle 1.
    { rewrite /RRSAS.sp. simpl_map. refl. }

    (** 2nd spawn **)
    steps_l; steps_r. set (Invs := _ : gmap nat InvO).
    force_l (0, stid, ssch, RRSNodeAS.f_precond (b, 0%Z), Invs, existT 0 (x_value_tid 2)).

    subst Invs. steps_l. forces_l; ss. iSplitL "RRI tidF".
    { iExists _. iFrame. iFrame "I". iSplit; eauto.
      do 3 iExists _. iSplit; eauto. iSplit; eauto.
      iApply f_spawnable; eauto.
      { split; eauto. vm_compute. econs. refl. }
      { i. vm_compute in H. do 3 (destruct m; ss); nia. }
    }

    steps_l; steps_r. call "IST". iIntros (???) "IST".
    steps_l. rewrite !map_size_insert map_size_empty lookup_empty.
    rewrite lookup_insert_ne // lookup_empty.
    iDestruct "ASM" as (?) "[% [tidF [RRI [% %]]]]"; des; subst; hss.
    steps_r; hss. steps_r.

    rrs_yield_ir "IST" "tidF". rrs_yield_l. steps_l.

    (** Round-Robin yield *)
    unfold RRS.yield. unseal "RRS". steps_r. steps_l.
    erewrite lookup_weaken; try eapply Hrrs; eauto; cycle 1.
    { rewrite /RRSAS.sp. simpl_map. refl. }

    set (Invs := _ : gmap nat InvO).
    force_l (0, stid, ssch, Invs). subst Invs. forces_l. iSplitL "RRI tidF H".
    { iFrame. repeat iSplit; eauto. iExists _.
      do 2 (rewrite lookup_insert_ne; eauto).
      rewrite lookup_insert. iSplit; eauto.
      solve_base_sl_red. rewrite /half_val. unseal "Node". iFrame. }

    steps_l; steps_r. call" IST". iIntros (???) "IST".
    steps_l. steps_r. iDestruct "ASM" as "(% & (% & tidF & % & % & RRI & % & INV))"; hss.

    forces_l. iSplitL "tidF"; eauto.
    step; eauto. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma unit_nat_neq (TEQ: @eq Type nat unit) : False.
  Proof using.
    set (a:=1). set (b:=2).
    assert (a = b).
    { gen a. gen b. rewrite TEQ. i; hss. }
    subst a b. inv H.
  Qed.

  Lemma simF_f : ISim.sim_fun open MA MI IstFull (Some RRSNodeHdr.f).
  Proof using Hschrrs Hrrs Hnode.
    iStartSim.

    steps_l. depdes _q. rename x into mtid'. destruct p as [[[[mtid stid] ssch] [blk ofs]] Invs].
    iDestruct "ASM" as "(WI & % & % & tidF & RRIP & RRI & [% | HALF] & % & % & % & [% #inv])"; des; hss.
    steps_l; steps_r; hss. steps_r. solve_base_sl_red. destruct mtid as [|mtid]; ss.

    assert (rrs_in_sp : (RRSAS.sp sp_user ⊤ get_stid PYIP) ⊆ sp).
    { etrans; eauto. }

    iApply wsim_fold; iFrame.
    rrs_yield_ir "IST" "tidF". steps_r.

    (** Open invariant **)
    rewrite /inv_x_points_to /ex_x_points_to.
    iInv "inv" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT". iDestruct "PT" as "[PT HALF0]".
    iPoseProof (RRSNodeAS.half_match with "[HALF HALF0]") as "%PREV".
    { rewrite /half_val. unseal "Node". iFrame. }
    rewrite PREV.
    
    inline_r. steps_r. forces_r. instantiate (1 := (blk, ofs, 1%Qp, _)); ss.
    iSplitL "PT"; iFrame; eauto.
    steps_r. iDestruct "GRT" as "[% [PT ->]]". subst. steps_r.

    (** Close invariant **)
    iMod ("CLOSE" with "[PT HALF0]") as "_".
    { iExists _. solve_base_sl_red. rewrite /half_val. unseal "Node". iFrame. }

    rrs_yield_ir "IST" "tidF". steps_r.

    inline_r. steps_r. force_r (S mtid, stid, ssch).
    forces_r. iSplitL "tidF"; iFrame; eauto. steps_r.
    iApply wsim_sget_tgt. steps_r. rewrite /mjoin /option_join.
    destruct (st_tgt1 !! RRSI.RRSI.v_tid) eqn:F; cycle 1.
    { rewrite F. s. destruct (@Any.downcast nat tt↑) eqn:A; steps_r; ss.
      iDestruct "GRT" as "[<- [-> tid]]"; hss.
      exfalso. eapply unit_nat_neq; eauto. }
      
    rewrite F. steps_r. destruct o; ss; cycle 1.
    { destruct (@Any.downcast nat tt↑) eqn:A; steps_r; ss.
      iDestruct "GRT" as "[<- [-> tid]]"; hss.
      exfalso. eapply unit_nat_neq; eauto. }

    destruct (@Any.downcast nat t) eqn:A; steps_r; ss.
    iDestruct "GRT" as "[% [% tidF]]"; subst. steps_r.

    do 3 (rrs_yield_ir "IST" "tidF"; steps_r).

    (** Open invariant **)
    rewrite /inv_x_points_to /ex_x_points_to.
    iInv "inv" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT". iDestruct "PT" as "[PT HALF0]".
    iPoseProof (RRSNodeAS.half_match with "[HALF HALF0]") as "%PREV".
    { rewrite /half_val. unseal "Node". iFrame. }
    rewrite PREV.

    inline_r. steps_r. forces_r.
    instantiate (1 := (blk, ofs, Vint _, Vint _)); ss.
    iSplitL "PT"; iFrame; eauto. steps_r.
    iDestruct "GRT" as "[% [PT ->]]". hss. steps_r. steps_r.
    replace (S mtid - mtid)%Z with 1%Z by nia.

    (** Close invariant **)
    iCombine "HALF HALF0" as "FULL".
    iPoseProof (full_update (Vint mtid) (Vint (mtid + 1)) with "[FULL]") as ">FULL".
    { rewrite /full_val; unseal "Node"; iFrame. }
    iPoseProof (full_merge with "FULL") as "[HALF HALF0]".
    iMod ("CLOSE" with "[PT HALF0]") as "_".
    { iExists _. solve_base_sl_red. rewrite /half_val. unseal "Node". iFrame. }

    rrs_yield_ir "IST" "tidF". rrs_yield_l. steps_l; steps_r.
    step. steps_r. steps_l.
    rrs_yield_ir "IST" "tidF". rrs_yield_l. steps_l; steps_r.

    unfold RRS.yield. unseal "RRS". steps_l.
    erewrite lookup_weaken; try eapply Hrrs; eauto; cycle 1.
    { rewrite /RRSAS.sp. simpl_map. refl. }
    force_l (mtid + 1, stid, ssch, Invs').
    forces_l. iSplitL "tidF RRI HALF".
    { replace (mtid + 1)%Z with (Z.of_nat (S mtid)) by nia.
      replace (mtid + 1) with (S mtid) by nia.
      iSplit; eauto. iFrame. iSplit; eauto. iExists _; iSplit; eauto. solve_base_sl_red.
      rewrite /half_val. unseal "Node". iFrame. }
     
    steps_l. steps_r. call "IST". iIntros (???) "IST".
    steps_l. iDestruct "ASM" as "[% (% & tidF & % & % & RRI & % & INV)]"; hss.
    steps_r. forces_l. replace (mtid + 1) with (S mtid) by nia.
    iFrame. iSplit; eauto.
    step. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof using Hschrrs Hrrs Hnode.
    init_sim.
    - eapply simF_main.
    - eapply simF_f.
    - iIntros "RI". do 4 iExists _. iFrame. iSplit; eauto.
  Qed.

End RRSNodeIA. End RRSNodeIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !SchA.schGS}.
  Context `{_rrsG: !RRSA.rrsGS}.
  Context `{_memGS: !MemA.memGS}.
  Context `{_nodeG: !RRSNodeA.nodeGS}.

  Lemma ctxr sp sp_user
    {T} (get_stid : T → nat) (PYIP : T → iProp Σ)
    (Hschrrs: sp_user ⊆ sp)
    (Hrrs: (RRSAS.sp sp_user ⊤ get_stid PYIP) ⊆ sp)
    (Hnode: (RRSNodeAS.sp ⊤) ⊆ sp_user) :
    ctx_refines
      ((RRSNodeA.t sp ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user get_stid PYIP)), RRSNodeA.init_cond)
      ((RRSNodeI.t    ★ (MemA.t sp) ★ (RRSA.t SchHdr.yield sp sp_user get_stid PYIP)), emp%I).
  Proof using. eapply main_adequacy, (RRSNodeIA.sim sp sp_user); eauto. Qed.

End ctxr.
