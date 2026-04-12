Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import NDSHeader NDSA NDSTactics.
Require Import MemHdr MemLib HybridMem.
Require Import NDSNodeHeader NDSNodeI NDSNodeA.
Require Import ltac2_lib.

Module NDSNodeIA. Section NDSNodeIA.
  Import NDSNodeA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
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

  Lemma simF_main : ISim.sim_fun open MA MI IstFull (fid NDSNodeHdr.f_main).
  Proof using Hschnds Hnds Hnode.
    cStartFunSim. rewrite /NDSNodeI.f_main /f_main.
    
    cStepsS. destruct _q as [[[mtid stid] ssch] []].
    iDestruct "ASM" as "(tidF & % & %)"; des; subst; cSimpl.
    cStepsS. cStepsT.

    cInlineT. cStepsT. cForceT true. cStepsT. cForcesT. iSplitR; eauto.
    cStepsT. rename _q into blk. iDestruct "GRT" as "[% [PT _]]". rewrite right_id. 
    ndsYieldGlobalIR "IST" "tidF". cStepsT. cInlineT. cStepsT. cForceT true.
    cStepsT. cForcesT. iSplitL "PT"; et.
    cStepsT. ndsYieldGlobalIR "IST" "tidF". ndsYieldGlobalS.

    cStepsS. cStepsT. cSimpl.
    cForceS (mtid, stid, ssch,
             (λ varg arg, ⌜varg = (tt↑↑) ∧ arg = ((Vint blk)↑↑)⌝ ∗ inv_x_points_to blk)%I,
             (λ vret ret, existT 0 (⌜vret = tt↑↑ ∧ ret = tt↑↑⌝%SAT))).
    cStepsS.
    iMod ((inv_alloc (∃ (v: τ{ ⇣nat }), sown mem_name (mem_points_to_singleton_r blk 1 (Vint v)))%SAT) with "[GRT]") as "#I"; eauto.
    { solve_base_sl_red. iExists 0. iFrame. }
    cForcesS. iSplitL "tidF".
    { iExists _. iSplit; eauto. do 3 iExists _. iSplit; eauto. iSplitR "tidF"; eauto.
      rewrite /NDSA.fn_spawnable. iExists _; iSplit; eauto.
      { iPureIntro. cSimpl; et. }
      rewrite /NDSA.fspec_spawnable. iIntros (??) "[%x [%Hpre %Hpost]]"; ss.
      destruct x as [[mtid' stid'] ssch'].
      set (m := (mtid', stid', ssch', blk) : meta (f_spec ⊤)).
      iExists (precond (f_spec ⊤) m), (postcond (f_spec ⊤) m).
      iSplit; eauto.
      { iPureIntro. exists m. esplits; eauto. }
      iIntros (??) "PRE". iModIntro. iSplitL "PRE"; eauto.
      { subst P1. rewrite /precond /fspec_winv /fspec_virtual /= /precond /=.
        iDestruct "PRE" as "(W & % & % & T & % & % & % & INV)"; des; subst; cSimpl.
        iFrame. iExists _; iSplit; eauto. }
      iIntros (??) "POST". iModIntro.
      subst Q1. rewrite /postcond /fspec_winv /fspec_virtual /= /postcond /=.
      iDestruct "POST" as "(W & T & % & % & %)"; des; subst; cSimpl.
      iFrame. iExists _; iSplit; eauto. iExists _; iSplit; eauto.
      solve_base_sl_red.
    }

    cStepsS. cStepsS.
    cCall "IST" as (???) "IST".
    cStepsS. iDestruct "ASM" as "(% & % & % & % & TID & JoinF)"; des; subst; cSimpl.
    cStepsS. cStepsT. ndsYieldGlobalIR "IST" "TID".
    cStepsT. ndsYieldGlobalS. cStepsS.
    ndsYieldIR "IST" "TID". ndsYieldS. cStepsT.

    cInlineT. cStepsT. cForceT true. cStepsT.
    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    cForceT (Vint z, 1%Qp). cStepsT. cForcesT. iSplitL "PT"; iFrame.
    cStepsT.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists _. solve_base_sl_red. }

    cForceS z. ndsYieldGlobalIR "IST" "TID".
    cStepsT. ndsYieldGlobalIR "IST" "TID".

    cStepsT. cInlineT. cStepsT. cForceT true. cStepsT.
    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    cForceT. iSplitL "PT"; iFrame.
    cStepsT.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists (z + 1). solve_base_sl_red.
      replace (Z.of_nat (z + 1)%nat) with (Z.of_nat z + 1)%Z by nia. iFrame. }
    ndsYieldGlobalIR "IST" "TID".
    ndsYieldGlobalS. cStep. cStepsT. cStepsS.
    ndsYieldGlobalIR "IST" "TID". ndsYieldGlobalS. cStepsS. cStepsT.
    ndsYieldIR "IST" "TID". ndsYieldS. cStepsS. cStepsT. cForcesS. iSplitL "TID"; iFrame; eauto.
    cStep. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma simF_f : ISim.sim_fun open MA MI IstFull (fid NDSNodeHdr.f).
  Proof using Hschnds Hnds Hnode.
    cStartFunSim. rewrite /NDSNodeI.f /f.

    cStepsS. destruct _q as [[[mtid stid] ssch] blk].
    iDestruct "ASM" as "[TID (% & % & % & #I)]"; des; subst; cSimpl.

    cStepsS. cStepsT. ndsYieldGlobalIR "IST" "TID".

    cStepsT. cInlineT. cStepsT. cForceT true. cStepsT.

    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    cForceT (Vint z, 1%Qp). cStepsT. cForceT. iSplitL "PT"; iFrame; eauto.
    cStepsT.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists z. solve_base_sl_red. }
    ndsYieldGlobalIR "IST" "TID". cStepsT. ndsYieldGlobalIR "IST" "TID". cStepsT.

    cInlineT. cStepsT. cForceT true. cStepsT.
    iInv "I" as "PT" "CLOSE". solve_base_sl_red. iDestruct "PT" as (?) "PT".
    cForceT. iSplitL "PT"; eauto.
    cStepsT.
    iMod ("CLOSE" with "[GRT]") as "_".
    { iExists (z + 1). solve_base_sl_red. replace (Z.of_nat (z + 1)%nat) with (Z.of_nat z + 1)%Z by nia. iFrame. }
    ndsYieldGlobalIR "IST" "TID". ndsYieldGlobalS.
    cForceS z. cStepsS. ndsYieldGlobalS. cStep. cStepsT. cStepsS.
    ndsYieldGlobalIR "IST" "TID". ndsYieldGlobalS.
    cStepsS; cStepsT. ndsYieldIR "IST" "TID". ndsYieldS. cStepsS.
    cForcesS. iSplitL "TID"; eauto.
    cStep. iFrame; eauto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MA MI init_cond IstFull.
  Proof using Hschnds Hnds Hnode.
    cStartModSim.
    - eapply simF_main.
    - eapply simF_f.
    - iIntros "I". iFrame. do 4 iExists _. iSplit; eauto.
  Qed.

End NDSNodeIA. End NDSNodeIA.

Section ctxr.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_schG: !SchA.schGS}.
  Context `{_ndsG: !NDSA.ndsGS}.
  Context `{_memGS: !MemLib.memGS}.

  Lemma ctxr sp sp_user
    (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ)
    (Hschnds: sp_user ⊆ sp)
    (Hnds: (NDSA.sp sp_user ⊤ T get_stid PYIP) ⊆ sp)
    (Hnode: (NDSNodeA.sp ⊤) ⊆ sp_user) :
    ctx_refines
      ((NDSNodeI.t   ★ HybMem.t, emp%I))
      (NDSNodeA.t sp ★ HybMem.t, NDSNodeA.init_cond).
  Proof using. eapply main_adequacy, (NDSNodeIA.sim sp sp_user); eauto. Qed.

End ctxr.
