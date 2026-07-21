Require Import CRIS.common.CRIS CRIS.cancellation.Cancel.
From CRIS.imp_system Require Import imp.ImpPrelude.
From CRIS.scheduler Require Import SchI SchA SchIAproof.
From CRIS.scheduler Require Import RRS.RRSI RRS.RRSA RRS.RRSIAproof.
From CRIS.scheduler Require Import NDS.NDSI NDS.NDSA NDS.NDSIAproof.
From CRIS.imp_system Require Import mem.MemI mem.MemA mem.MemIAproof.
From CRIS.hybrid_mem Require Import DetMem HybridMem MemDHProof.
From CRIS.scheduler Require Import example.RRSNodeI example.RRSNodeA.
From CRIS.scheduler Require Import example.RRSNodeIAproof.
From CRIS.scheduler Require Import example.NDSNodeI example.NDSNodeA.
From CRIS.scheduler Require Import example.NDSNodeIAproof.
From CRIS.scheduler Require Import example.SCHMainI example.SCHMainA.
From CRIS.scheduler Require Import example.SCHMainIAproof.

Section SCHMainAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, _SCH: !schGS, _RRS: !rrsGS, _NDS: !ndsGS, _MEM: !memGS, _MEMLIB: !MemLib.memGS, _NODE: !nodeGS}.
  Context (genv : GEnv.t).

  (* source module *)
  Local Definition sp_rrs : specmap := RRSNodeAS.sp ⊤.
  Local Definition sp_nds : specmap := NDSNodeA.sp ⊤.
  Local Definition sp_sch : specmap :=
    (SCHMainA.sp ⊤)
    ∪ (RRSAS.sp sp_rrs ⊤ snd SchA.PYIP)
    ∪ (NDSA.sp sp_nds ⊤ _ snd SchA.PYIP)
    ∪ sp_rrs
    ∪ sp_nds.

  Local Definition smod_src : SMod.t :=
    (SCHMainA.smod ⊤)
      ☆ (SchA.smod sp_sch ⊤)
      ☆ (RRSA.smod SchHeader.SchHdr.yield.1 sp_rrs ⊤ snd SchA.PYIP)
      ☆ (NDSA.smod SchHeader.SchHdr.yield.1 ⊤ sp_nds _ snd SchA.PYIP)
      ☆ (RRSNodeA.smod ⊤)
      ☆ (NDSNodeA.smod ⊤).
  Local Definition mod_top : Mod.t := (SMod.to_mod ∅ (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t :=
    SCHMainI.t
      ★ SchI.t
      ★ (RRSI.t SchHeader.SchHdr.yield.1)
      ★ (NDSI.t SchHeader.SchHdr.yield.1)
      ★ RRSNodeI.t
      ★ NDSNodeI.t
      ★ (MemI.t genv)
      ★ DetMem.t.
  
  Local Definition sp : specmap := SMod.sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition init_cond : iProp Σ :=
    SchA.init_cond ∗ RRSA.init_cond ∗ NDSA.init_cond ∗ HybMem.init_cond ∗ MemA.init_cond genv.

  Ltac ctac :=
    rewrite /=;
    match goal with
    | [ |- map_Forall _ (?X _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _ _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _ _ _) ] => rewrite /X; mod_tac ss
    | [ |- map_Forall _ (?X _ _ _ _ _) ] => rewrite /X; mod_tac ss
    end.

  Local Transparent SCH.
  Local Transparent NDSHeader.NDS.
  Local Transparent RRSHeader.RRS.
  Local Transparent RRSNodeHeader.RRSNODE.
  Local Transparent NDSNodeHeader.NDSNODE.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    SCHMainA.init_cond ∗ Cancel.init_res ⊢ refines mod_src mod_top.
  Proof.
    iIntros "[H1 H2]".
    iApply refines_trans. iSplitR.
    { iApply ctxr_refines. iApply Cancel.prepare; et; clarify. }
    iApply Cancel.cancel.
    { do 5 (eapply SMod.cancellable_add; r; [ctac|]). ctac. }
    { ss. exists (). esplits; refl. }
    { i. iIntros "(W & % & _)". eauto. }
    { iDestruct "H2" as "(TID & YIELD & WINV & $ & $)".
      iDestruct "H1" as "(HINITRRS & HNODE & HINITNDS & HTIDFRAG)".
      unfoldPrePost. rewrite /SchA.Tid. iFrame; eauto.
    }
  (*SLOW*)Qed.

  Section SP.

    Ltac single :=
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.

    Lemma spsch_in_sp : sp_sch ⊆ sp.
    Proof.
      split; et.
      do 4 (eapply map_union_least; [|single]). single.
    (*SLOW*)Qed.

    Lemma sch_in_sp : (SchA.sp sp_sch ⊤) ⊆ sp.
    Proof. split; et. single. Qed.

    Lemma rrs_in_spsch : (RRSAS.sp sp_rrs ⊤ snd SchA.PYIP) ⊆ sp_sch.
    Proof.
      split; et.
      rewrite /sp_sch /SCHMainA.sp /sp_nds /NDSNodeA.sp /RRSAS.sp /NDSA.sp.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
    Qed.

    Lemma nds_in_spsch : (NDSA.sp sp_nds ⊤ _ snd SchA.PYIP) ⊆ sp_sch.
    Proof.
      split; et.
      rewrite /sp_sch /SCHMainA.sp /sp_nds /NDSNodeA.sp /RRSAS.sp /NDSA.sp.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq; mod_tac.
    Qed.

    Lemma rrsnode_in_sprrs : (RRSNodeAS.sp ⊤) ⊆ sp_rrs.
    Proof. by reflexivity. Qed.

    Lemma ndsnode_in_sprrs : (NDSNodeA.sp ⊤) ⊆ sp_nds.
    Proof. by reflexivity. Qed.

    Lemma sprrs_in_sp : sp_rrs ⊆ sp.
    Proof. split; et. single. Qed.

    Lemma spnds_in_sp : sp_nds ⊆ sp.
    Proof. split; et. single. Qed.

    Lemma yield_in_sp : sp.1 !! (fid SchHeader.SchHdr.yield) = fsp_some (SchA.yield_spec ⊤).
    Proof. split; et. Qed.

    Lemma yield_spec_cond :
      ⊢ fspec_imply (SchA.yield_spec ⊤)
          (fspec_winv ⊤
             (fspec_mk 
                (λ x varg arg, 
                  TID (snd x) ∗ YIELD (snd x) ∗ PYIP x ∗ ⌜varg = arg ∧ varg = tt↑⌝)
                (λ x vret ret, 
                  TID (snd x) ∗ YIELD (snd x) ∗ PYIP x ∗ ⌜vret = ret ∧ vret = tt↑⌝))%I).
    Proof.
      iIntros (??) "[%x [%Hpre %Hpost]] % % Pre !>"; ss.
      destruct x as [mtid stid].
      iExists (precond (SchA.yield_spec ⊤) (stid, mtid, tt)), (postcond (SchA.yield_spec ⊤) (stid, mtid, tt)).
      iSplit.
      { iPureIntro. exists (stid, mtid, tt). esplits; eauto. }
      iSplitL "Pre".
      { subst P1. iDestruct "Pre" as "(W & T & Y & P & %)"; des; subst; cSimpl. iFrame; eauto. }
      iIntros (??) "POST". iModIntro.
      subst Q1. iDestruct "POST" as "(W & (tid & T & Y) & %)"; des; subst; cSimpl. iFrame; eauto.
    Qed.
  End SP.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : init_cond ⊢ refines mod_tgt mod_src.
  Proof.
    iIntros "(HSCH & HRRS & HNDS & HHYB & HMEM)".
    iApply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src.

    iApply ctxr_trans. iSplitR.
    { ctxr_rotate. do 7 ctxr_drop. iApply SCHMainIAproof.ctxr.
      { eapply spsch_in_sp. }
      { eapply sch_in_sp. }
      { eapply rrs_in_spsch. }
      { eapply nds_in_spsch. }
      { eapply rrsnode_in_sprrs. }
      { eapply ndsnode_in_sprrs. }
    }

    iApply ctxr_trans. iSplitL "HSCH".
    { ctxr_rotate. do 7 ctxr_drop. iApply SchIA.ctxr.
      { eapply sch_in_sp. }
      { eapply spsch_in_sp. }
      { et. }
      { iExact "HSCH". }
    }

    iApply ctxr_trans. iSplitL "HRRS".
    { ctxr_rotate. do 7 ctxr_drop. iApply RRSIA.ctxr.
      { eapply yield_in_sp. }
      { etrans; [eapply rrs_in_spsch| eapply spsch_in_sp]. }
      { eapply sprrs_in_sp. }
      { eapply yield_spec_cond. }
      { et. }
      { iExact "HRRS". }
    }

    iApply ctxr_trans. iSplitL "HNDS".
    { ctxr_rotate. do 7 ctxr_drop. iApply NDSIA.ctxr.
      { eapply yield_in_sp. }
      { etrans; [eapply nds_in_spsch| eapply spsch_in_sp]. }
      { eapply spnds_in_sp. }
      { eapply yield_spec_cond. }
      { et. }
      { iExact "HNDS". }
    }

    iApply ctxr_trans. iSplitL "HMEM".
    { do 3 ctxr_rotate. do 7 ctxr_drop. iApply MemIA.ctxr. iExact "HMEM". }

    iApply ctxr_trans. iSplitL "HHYB".
    { ctxr_rotate. do 7 ctxr_drop. iApply MemDH.ctxr. iExact "HHYB". }
    
    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_drop. do 3 (ctxr_rotate; ctxr_drop). ctxr_rotate. iApply RRSNodeIAproof.ctxr.
      { eapply sprrs_in_sp. }
      { etrans; [eapply rrs_in_spsch|eapply spsch_in_sp]. }
      { eapply rrsnode_in_sprrs. }
      { done. }
    }

    iApply ctxr_trans. iSplitR.
    { do 3 ctxr_drop. do 2 ctxr_rotate. do 3 ctxr_drop. iApply NDSNodeIAproof.ctxr.
      { eapply spnds_in_sp. }
      { etrans; [eapply nds_in_spsch|eapply spsch_in_sp]. }
      { eapply ndsnode_in_sprrs. }
      { done. }
    }

    iApply ctxr_trans. iSplitR.
    { do 4 ctxr_drop. ctxr_rotate. do 3 ctxr_drop. iApply elim_module. }
    rewrite !mod_add_empty_r.

    iApply ctxr_trans. iSplitR.
    { do 6 ctxr_drop. iApply elim_module. }

    rewrite !mod_add_empty_r.

    iApply ctxr_trans. iSplitR.
    { do 2 ctxr_drop. do 2 ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_refl. }

    rewrite !SMod.to_mod_add.
    rewrite /SCHMainA.t /SchA.t /RRSA.t /NDSA.t /RRSNodeA.t /NDSNodeA.t.

    iApply ctxr_refl.
  (*SLOW*)Qed.

  Lemma top_tgt :
    init_cond ∗ SCHMainA.init_cond ∗ Cancel.init_res ⊢
      refines mod_tgt mod_top.
  Proof.
    iIntros "(H1 & H2 & H3)".
    iApply refines_trans. iSplitL "H1".
    - iApply src_tgt; iFrame.
    - iApply cancel_src; iFrame.
  Qed.

  Local Ltac ttac := econs; eauto; [mod_tac|prove_nodup].

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt.
    eapply Mod.add_wf; [ttac|    |mod_tac|prove_nodup; set_solver].
    eapply Mod.add_wf; [ttac|    |mod_tac|prove_nodup; set_solver].
    eapply Mod.add_wf; [ttac|    |mod_tac|prove_nodup; set_solver].
    eapply Mod.add_wf; [ttac|    |mod_tac|prove_nodup; set_solver].
    eapply Mod.add_wf; [ttac|    |mod_tac|prove_nodup; set_solver].
    eapply Mod.add_wf; [ttac|    |mod_tac|prove_nodup; set_solver].
    eapply Mod.add_wf; [ttac|ttac|mod_tac|prove_nodup; set_solver].
  Qed.
End SCHMainAux.

Module SCHMainAll.
  Import inv_instances.
  (* mem *)
  (* global environment - not used in this example *)
  Local Definition genv : GEnv.t := [].

  Local Instance Γ : HRA := ##[invΓ; concΓ; newschΓ; rrsΓ; ndsΓ; MemLib.memΓ; memΓ; nodeΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ; rrsΣ; ndsΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv)
      (_ : SchA.schGS) (_ : RRSA.rrsGS) (_ : NDSA.ndsGS)
      (_ : MemLib.memGS) (_ : MemA.memGS) (_ : RRSNodeA.nodeGS)
      src_res tgt_res,
    refines_lmod
      (Mod.to_lmod (mod_tgt genv) tgt_res)
      (Mod.to_lmod mod_top src_res).
  Proof.
    apply own_admin_soundness.
    iMod cris_alloc as "(% & % & % & % & [WINV HCONC])".
    iPoseProof (winv_split_empty with "WINV") as "[WINV WINV∅]".
    iMod sch_alloc as "(% & HSCH & HTIDFRAG)".
    iMod rrs_alloc as "(% & HRRS & HINITRRS)".
    iMod nds_alloc as "(% & HNDS & HINITNDS)".
    iMod MemLib.mem_alloc as "(% & HMEMLIB)".
    iMod (mem_alloc genv) as "(% & HMEM)".
    iMod rrsnode_alloc as "(% & HNODE)".
    do 10 iExists _.
    iPoseProof (top_tgt genv with "[-WINV∅]") as "REF".
    { iDestruct "HMEMLIB" as "[HHYB _]".
      iDestruct "HMEM" as "[HMEM _]".
      rewrite /init_cond /SCHMainA.init_cond /Cancel.init_res
        /HybMem.init_cond /MemA.init_cond.
      iFrame.
    }
    iAssert (⌜∃ src_res, ✓ src_res /\ refines_lmod
      (Mod.to_lmod (mod_tgt genv) ε)
      (Mod.to_lmod mod_top src_res)⌝)%I
      with "[WINV∅ REF]" as "%Href".
    { iApply refines_adequacy. { eapply tgt_wf. } iFrame. }
    destruct Href as [src_res [_ Href]].
    iPureIntro. exists src_res, ε. exact Href.
  (*SLOW*)Qed.
End SCHMainAll.
(* Print Assumptions SCHMainAll.behavioral_refinement. *)
