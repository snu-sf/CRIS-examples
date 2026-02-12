Require Import CRIS Cancel.
Require Import ImpPrelude.
Require Import SchI SchA SchIAproof.
Require Import RRSI RRSA RRSIAproof.
Require Import NDSI NDSA NDSIAproof.
Require Import MemI MemA MemIAproof.
Require Import DetMem HybridMem MemDHProof.
Require Import RRSNodeI RRSNodeA RRSNodeIAproof.
Require Import NDSNodeI NDSNodeA NDSNodeIAproof.
Require Import SCHMainI SCHMainA SCHMainIAproof.

Section SCHMainAux.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !concGS, !schGS, !rrsGS, !ndsGS, !memGS, !MemLib.memGS, !nodeGS}.
  Context (csl : string → bool) (genv : GEnv.t).

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
      ☆ (RRSA.smod SchHeader.SchHdr.yield sp_rrs ⊤ snd SchA.PYIP)
      ☆ (NDSA.smod SchHeader.SchHdr.yield ⊤ sp_nds _ snd SchA.PYIP)
      ☆ (RRSNodeA.smod ⊤)
      ☆ (NDSNodeA.smod ⊤).
  Local Definition mod_top : Mod.t := (SMod.to_mod ∅ (SMod.cancel smod_src)).
  Local Definition mod_tgt : Mod.t :=
    SCHMainI.t
      ★ SchI.t
      ★ (RRSI.t SchHeader.SchHdr.yield)
      ★ (NDSI.t SchHeader.SchHdr.yield)
      ★ RRSNodeI.t
      ★ NDSNodeI.t
      ★ (MemI.t csl genv)
      ★ DetMem.t.
  
  Local Definition sp : specmap := SMod.conc_sp_from smod_src.
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.

  Local Definition init_cond : iProp Σ :=
    SchA.init_cond ∗ RRSA.init_cond ∗ NDSA.init_cond ∗ HybMem.init_cond ∗ MemA.init_cond csl genv.

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
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ SCHMainA.init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    { do 5 (eapply SMod.cancellable_add; r; [ctac|]). ctac. }
    { assert (Ht : SMod.conc_sp_from smod_src !! speckey_entry =
        fsp_some (SCHMainA.main_spec ⊤)); last (rewrite Ht; clear Ht).
      { rewrite lookup_insert_ne // lookup_kmap_Some; exists None; split; ss. }
      exists (precond (SCHMainA.main_spec ⊤) tt), (postcond (SCHMainA.main_spec ⊤) tt); splits.
      { ss. exists (). esplits; refl. }
      { iIntros "(T & Y & W & A & B & C & D)". iFrame. iModIntro. eauto. }
      { i. iIntros "(W & % & _)". eauto. }
    }
  (*SLOW*)Qed.

  Section SP.

    Ltac single :=
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss.
    Ltac entry :=
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
      rewrite lookup_insert_ne // lookup_kmap_Some; eexists None; split; ss.

    Lemma spsch_in_sp : sp_sch ⊆ sp.
    Proof.
      do 4 (eapply map_union_least; [|single]). entry.
    (*SLOW*)Qed.

    Lemma sch_in_sp : (SchA.sp sp_sch ⊤) ⊆ sp.
    Proof. single. Qed.

    Lemma rrs_in_spsch : (RRSAS.sp sp_rrs ⊤ snd SchA.PYIP) ⊆ sp_sch.
    Proof.
      rewrite /sp_sch /SCHMainA.sp /sp_nds /NDSNodeA.sp /RRSAS.sp /NDSA.sp.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
        rewrite !lookup_union;
        repeat (rewrite lookup_insert_ne; [|by (intros F; inv F)]);
        rewrite lookup_insert;
        repeat (rewrite lookup_insert_ne; [|intros F; inv F]);
        rewrite !lookup_empty; ss.
    Qed.

    Lemma nds_in_spsch : (NDSA.sp sp_nds ⊤ _ snd SchA.PYIP) ⊆ sp_sch.
    Proof.
      rewrite /sp_sch /SCHMainA.sp /sp_nds /NDSNodeA.sp /RRSAS.sp /NDSA.sp.
      repeat try eapply insert_subseteq_l; last apply map_empty_subseteq;
        rewrite !lookup_union;
        repeat (rewrite lookup_insert_ne; [|by (intros F; inv F)]);
        rewrite lookup_insert;
        repeat (rewrite lookup_insert_ne; [|intros F; inv F]);
        rewrite !lookup_empty; ss.
    Qed.

    Lemma rrsnode_in_sprrs : (RRSNodeAS.sp ⊤) ⊆ sp_rrs.
    Proof. by reflexivity. Qed.

    Lemma ndsnode_in_sprrs : (NDSNodeA.sp ⊤) ⊆ sp_nds.
    Proof. by reflexivity. Qed.

    Lemma sprrs_in_sp : sp_rrs ⊆ sp.
    Proof. single. Qed.

    Lemma spnds_in_sp : sp_nds ⊆ sp.
    Proof. single. Qed.

    Lemma yield_in_sp : sp !! (speckey_fn SchHeader.SchHdr.yield) = fsp_some (SchA.yield_spec ⊤).
    Proof. rewrite lookup_insert_ne // lookup_kmap_Some; eexists (Some _); split; ss. Qed.

    Lemma yield_spec_cond :
      ⊢ fspec_imply (SchA.yield_spec ⊤)
          (fspec_winv ⊤
             (fspec_mk 
                (λ x varg arg, 
                  TID (snd x) ∗ YIELD (snd x) ∗ PYIP x ∗ ⌜varg = arg ∧ varg = tt↑⌝)
                (λ x vret ret, 
                  TID (snd x) ∗ YIELD (snd x) ∗ PYIP x ∗ ⌜vret = ret ∧ vret = tt↑⌝))%I).
    Proof.
      iIntros (??) "[%x [%Hpre %Hpost]]"; ss.
      destruct x as [mtid stid].
      iExists (precond (SchA.yield_spec ⊤) (stid, mtid, tt)), (postcond (SchA.yield_spec ⊤) (stid, mtid, tt)).
      iSplit.
      { iPureIntro. exists (stid, mtid, tt). esplits; eauto. }
      iIntros (??) "PRE". iModIntro. iSplitL "PRE".
      { subst P1. iDestruct "PRE" as "(W & T & Y & P & %)"; des; subst; hss. iFrame; eauto. }
      iIntros (??) "POST". iModIntro.
      subst Q1. iDestruct "POST" as "(W & (tid & T & Y) & %)"; des; subst; hss. iFrame; eauto.
    Qed.
  End SP.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt /smod_src.

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply SCHMainIAproof.ctxr.
      { eapply spsch_in_sp. }
      { eapply sch_in_sp. }
      { eapply rrs_in_spsch. }
      { eapply nds_in_spsch. }
      { eapply rrsnode_in_sprrs. }
      { eapply ndsnode_in_sprrs. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply SchIA.ctxr.
      { eapply sch_in_sp. }
      { eapply spsch_in_sp. }
      { unfold sp, SMod.conc_sp_from; rewrite dom_insert; eapply elem_of_union_l; set_solver. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply RRSIA.ctxr.
      { eapply yield_in_sp. }
      { etrans; [eapply rrs_in_spsch| eapply spsch_in_sp]. }
      { eapply sprrs_in_sp. }
      { eapply yield_spec_cond. }
      { unfold sp, SMod.conc_sp_from; rewrite dom_insert; eapply elem_of_union_l; set_solver. }
    }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply NDSIA.ctxr.
      { eapply yield_in_sp. }
      { etrans; [eapply nds_in_spsch| eapply spsch_in_sp]. }
      { eapply spnds_in_sp. }
      { eapply yield_spec_cond. }
      { unfold sp, SMod.conc_sp_from; rewrite dom_insert; eapply elem_of_union_l; set_solver. }
    }

    etrans; cycle 1.
    { do 3 ctxr_rotate. do 7 ctxr_drop. eapply MemIA.ctxr. }

    etrans; cycle 1.
    { ctxr_rotate. do 7 ctxr_drop. eapply MemDH.ctxr. }
    
    etrans; cycle 1.
    { do 2 ctxr_drop. do 3 (ctxr_rotate; ctxr_drop). ctxr_rotate. eapply RRSNodeIAproof.ctxr; cycle 1.
      { etrans; [eapply rrs_in_spsch|eapply spsch_in_sp]. }
      { eapply rrsnode_in_sprrs. }
      { eapply sprrs_in_sp. }
    }

    etrans; cycle 1.
    { do 3 ctxr_drop. do 2 ctxr_rotate. do 3 ctxr_drop. eapply NDSNodeIAproof.ctxr; cycle 1.
      { etrans; [eapply nds_in_spsch|eapply spsch_in_sp]. }
      { eapply ndsnode_in_sprrs. }
      { eapply spnds_in_sp. }
    }

    etrans; cycle 1.
    { do 4 ctxr_drop. ctxr_rotate. do 3 ctxr_drop. eapply elim_module. }

    etrans; cycle 1.
    { do 6 ctxr_drop. ctxr_rotate. ctxr_drop. eapply elim_module. }

    rewrite -!mod_add_empty_r.

    etrans; cycle 1.
    { do 2 ctxr_drop. do 2 ctxr_rotate. ctxr_drop. ctxr_rotate. ctxr_refl. }

    rewrite /init_cond.
    rewrite !SMod.to_mod_add /init_cond.
    rewrite /SCHMainA.t /SchA.t /RRSA.t /NDSA.t /RRSNodeA.t /NDSNodeA.t.

    eapply ctxr_cond_strengthen.
    iIntros "(? & ? & ? & ? & ?)". iFrame.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond ∗ TID 0 ∗ YIELD 0 ∗ winv (⊤, ⊤) ∗ SCHMainA.init_cond ∗ TIDAUTH 0 ∗ YIELDAUTH 1)%I
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Ltac ttac := econs; eauto; [mod_tac|prove_nodup].
  Ltac tolv := rewrite !Mod.dom_fnsems_add; set_solver.
  Ltac solv := prove_nodup; des_ifs; set_solver.

  Lemma tgt_wf: Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt.
    eapply Mod.add_wf; [ttac| |tolv|solv].
    eapply Mod.add_wf; [ttac| |tolv|solv].
    eapply Mod.add_wf; [ttac| |tolv|solv].
    eapply Mod.add_wf; [ttac| |tolv|solv].
    eapply Mod.add_wf; [ttac| |tolv|solv].
    eapply Mod.add_wf; [ttac| |tolv|solv].
    eapply Mod.add_wf; [ttac|ttac| |solv].
    set_solver.
  Qed.
End SCHMainAux.

Module SCHMainAll.
  Import inv_instances.
  (* mem *)
  Local Definition csl : string → bool := λ _, false.
  (* global environment - not used in this example *)
  Local Definition genv : GEnv.t := [].

  Local Instance Γ : HRA := ##[invΓ; concΓ; newschΓ; rrsΓ; ndsΓ; MemLib.memΓ; memΓ; nodeΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ; newschΣ; rrsΣ; ndsΣ].

  Theorem behavioral_refinement :
    ∃ β τ (Hinv : invGS Γ Σ α) (_ : crisG Γ Σ α β τ _ Hinv) (_ : concGS)
      (_ : SchA.schGS) (_ : RRSA.rrsGS) (_ : NDSA.ndsGS)
      (_ : MemLib.memGS) (_ : MemA.memGS) (_ : RRSNodeA.nodeGS)
      src_res tgt_res,
    refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod (mod_tgt csl genv) tgt_res).
  Proof.
    apply own_admin_soundness.
    iMod winv_alloc as "[% [% [% [% ?]]]]"; iExists _, _, _, _.
    iMod conc_alloc as "[% ?]". iExists _.
    iMod sch_alloc as "[% ?]". iExists _.
    iMod rrs_alloc as "[% [? ?]]"; iExists _.
    iMod nds_alloc as "[% [? ?]]"; iExists _.
    iMod MemLib.mem_alloc as "[% ?]"; iExists _.
    iMod (mem_alloc csl genv) as "[% ?]"; iExists _.
    iMod rrsnode_alloc as "[% ?]"; iExists _.
    pose proof (top_tgt csl genv) as Href.
    iStopProof. eapply entails_pointwise; iIntros (res Hres) "R".
    iPoseProof (Own_valid with "R") as "%".
    rewrite /refines in Href; hexploit Href; eauto using tgt_wf.
    clear Href; intros [? Href].
    iPureIntro; hexploit (Href res); eauto.
    { rewrite Hres /=. iIntros "(W & ($ & $ & $ & $) & ($ & $) & $ & $ & $ & $ & [$ _] & [$ _] & $)".
      rewrite {1}winv_split_empty comm //. }
    intros [rt ?].
    exists res, rt; by des.
  (*SLOW*)Qed.
End SCHMainAll.
(* Print Assumptions SCHMainAll.behavioral_refinement. *)
