From CRIS.common Require Import CRIS.
From CRIS.imp_system.mem Require Import MemA MemTactics.
From CRIS.celliostk Require Import CellioHeader CellioA CellioI.

Local Open Scope nat_scope.

Module CellioIA. Section CellioIA.
  Import CellioA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_MEM: !memGS}.

  Context (sp : specmap).
  
  Local Definition MemA := MemA.t sp.
  Local Definition CellioIMod := (CellioI.t ★ MemA).
  Local Definition CellioAMod := (CellioA.t ★ MemA).
  Section SIM_FUNS.

    Context `{STATE : !stateGS Σ}.

    Local Notation IstFull :=
      (True ∗ IstEq MemA)%I.

    Lemma simF_new :
      ⊢ ISim.sim_fun open CellioAMod CellioIMod IstFull (fid CellioHdr.new).
    Proof using.
      cStartFunSim. rewrite /CellioI.new /new.

      cStepsT. cStepsS. destruct Any.downcast; [|cStepsS; ss].
      cStepsT. cStepsS. cForceS Vnullptr. cStepsS.
      cForceS. iSplit; et. cStepsS. cStep. iFrame. et.
    Qed.

    Lemma simF_push :
      ⊢ ISim.sim_fun open CellioAMod CellioIMod IstFull (fid CellioHdr.push).
    Proof using.
      cStartFunSim. rewrite /CellioI.push /push.

      cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs. cStepsS. cStepsT.

      cCall "IST" as (?) "IST".
      cStepsS. cStepsT.
      destruct Any.downcast; cStepsS; des_ifs. cStepsT. rename z into v_new.

      mAllocT as (?) "[P0 [P1 _]]". rewrite /scale_int; ss. cStepsT.
      mStoreT "P0".
      mStoreT "P1".

      cForceS. cStepsS. cForceS. iSplitL "P0 P1 ASM".
      { iExists (blk,0%Z), v. iSplit; et. iFrame. et. }

      cStepsS. cStep. iFrame. et.
    (*SLOW*)Qed.

    Lemma simF_pop :
      ⊢ ISim.sim_fun open CellioAMod CellioIMod IstFull (fid CellioHdr.pop).
    Proof using.
      cStartFunSim. rewrite /pop /CellioI.pop.

      cStepsS. cStepsT. destruct Any.downcast; cStepsS; des_ifs. cStepsT. des_if.
      { subst. cStepsT. destruct _q; cycle 1.
        { iDestruct "ASM" as (??) "[% _]". ss. }
        cForceS Vnullptr. cStepsS. cForceS. iSplit; et. cStepsS. cStep.
        iFrame. et.
      }

      destruct _q. { iDestruct "ASM" as "%"; ss. }
      iDestruct "ASM" as ([b o]?) "[-> [[P0 [P1 _]] PT]]". rewrite right_id.
      cStepsT. rewrite /scale_int; ss. cStepsT.

      mLoadT "P0". mLoadT "P1". mFreeT "P0". mFreeT "P1".

      cForceS. cStepsS. cForceS. iFrame.
      cStepsS. cStep. iFrame. et.
    (*SLOW*)Qed.

  End SIM_FUNS.

  Lemma sim :
    CellioA.init_cond ⊢ ISim.t open CellioAMod CellioIMod.
  Proof using.
    iIntros "INIT".
    iApply (ISim_reflR open CellioA.t CellioI.t MemA
      (λ _ : stateGS Σ, True%I) with "[INIT] []").
    - iIntros (STATE). rewrite /ISim.init_ist. iIntros (WF). iSplit.
      { iPureIntro. mod_tac. }
      iIntros "SRC TGT". rewrite /init_cond /=. done.
    - iIntros (STATE). rewrite /ISim.sim_funs. iIntros (WF). iSplit.
      { iPureIntro. split; mod_tac. }
      iIntros (fn) "%Hfn".
      repeat rewrite Mod.dom_fnsems_add in Hfn.
      set_unfold in Hfn; des; subst.
      + iApply simF_new.
      + iApply simF_push.
      + iApply simF_pop.
  Qed.
End CellioIA. End CellioIA.
