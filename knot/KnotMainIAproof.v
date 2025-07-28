Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotMainI KnotMainA KnotA KnotI KnotIAproof.
Require Import APCHeader APC APCA APCC APCTactics.

Set Implicit Arguments.

Module KnotMainIA. Section KnotMainIA.
  Import KnotA KnotMainA APCA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I}.
  Context `{_memG: !memG}.
  Context `{_knotG: !knotG}.

  (* 1. global environment *)
  Context (genv: GEnv.t).
  (* 3. spec tables *)
  Context (Sp: string -> option fspec).
  Context (SpRec SpFun SpPure: spl_type).
  (* 4. hypotheses for genv *)
  Context (GEnvWF: GEnv.wf genv).
  Context (GEnvIncl: incl KnotMainGEnv.t genv).
  (* 5. hypotheses for sp *)
  Context (MainInFun: spl_sub (MainFunSp genv SpRec) SpFun).
  Context (KnotInSp: sp_incl KnotRecSp Sp).
  Context (APCInSp: sp_incl APCA.Sp Sp).
  (* 6. hypotheses for pure sp *)
  Context (RecInSpPure: spl_sub SpRec SpPure).
  Context (PureInGlobal : sp_incl SpPure Sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, True%I.

  Local Definition APCA := (APCA.t SpPure Sp).
  Local Definition MemP := MemP.t.
  Local Definition KnotA := (KnotA.t genv SpRec SpFun Sp).
  Local Definition KnotAMod := (KnotA ★ MemP ★ APCA).
  Local Definition KnotMainA := (KnotMainA.t true genv SpRec Sp).
  Local Definition KnotMainI := (KnotMainI.t genv).
  Local Definition KnotMainAMod := (KnotMainA ★ KnotAMod).
  Local Definition KnotMainIMod := (KnotMainI ★ KnotAMod).
  Local Definition IstFull := (IstProd (IstSB KnotMainA.(Mod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_fib:
    ISim.sim_fun open KnotMainAMod KnotMainIMod KnotMainA.init_cond IstFull (Some KnotMainHdr.fib).
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    init_simF.

    steps_l. iDestruct "ASM" as "[[% INV] %]". des; subst. hss.
    steps_r. inv H3. des. rewrite FBLOCK; hss. steps_r.
    unfold assume. assert (T:true) by auto. force_r T. steps_r.
    des_ifs.
    { (* base case *)
      steps_r. steps_l. forces_l. iSplitR; et. steps_l.
      inline_l. steps_l.
      iDestruct "ASM" as "%"; des; subst; hss. steps_l.
      unfold apc_body, APC. force_l 0. steps_l. 
      (* SRC: change to skip *)
      apc_l. steps_l. forces_l. iSplitR; et. steps_l.
      forces_l. iSplitL "INV"; iFrame; et.
      assert (q1 >= 0)%Z by nia. assert (q1 = 1 \/ q1 = 0) by nia. assert (Z.of_nat (Fib q1) = 1)%Z.
      { des; subst; reflexivity. }
      rewrite H3. step. iSplit; et.
    }
    { (* recursive call *)
      steps_r. steps_l. forces_l. iSplitR; et. steps_l.
      inline_l. steps_l.
      iDestruct "ASM" as "%"; des; subst; hss. steps_l. unfold apc_body, APC.
      force_l 2. steps_l.
      
      (* first call - rec(n - 1) *)
      dup SPEC. inv SPEC.
      apc_call_weaker "IST INV"; et.
      { instantiate (1 := 1). apply OrdArith.lt_from_nat. ss. }
      { instantiate (1 := (2 * (q1 - 1) + 1)%ord). eapply Ord.lt_le_lt; [|et]. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.lt_from_nat. nia. }
      { unfold precond. ss. instantiate (1:= (q1 - 1) ). iFrame. iSplit; et. iSplit; et.
        - iPureIntro. repeat f_equal. nia.
        - iPureIntro. unfold intrange_64 in *.
          bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss.
        - iPureIntro. eexists; esplits; et. refl. 
      }
      iDestruct "ISTPOST" as "[IST [% INV]]". subst. steps_r. hss. steps_r.

      (* second call - rec(n - 2) *)
      apc_call_weaker "IST INV"; et.
      { instantiate (1:=0). apply OrdArith.lt_from_nat. ss. }
      { instantiate (1 := (2 * (q1 - 1))%ord). eapply Ord.lt_le_lt; [|et]. rewrite -!OrdArith.mult_from_nat. eapply OrdArith.lt_from_nat. nia. }
      { iFrame. instantiate (1:= (q1 - 2)). iSplit; et. iSplit; et.
        - iPureIntro. repeat f_equal. nia.
        - iPureIntro. unfold intrange_64 in *.
          bsimpl; des; split; des_sumbool; repeat destruct Z_le_gt_dec; unfold min_64, max_64, modulus_64_half in *; try nia; ss.
        - iPureIntro. eexists; esplits; et. rewrite -!OrdArith.mult_from_nat -OrdArith.add_from_nat. eapply OrdArith.le_from_nat. nia.
      }
      iDestruct "ISTPOST" as "[IST [% INV]]". subst. steps_r. hss. steps_r.

      apc_l. steps_l. forces_l. iSplit; et. steps_l. forces_l. iFrame. iSplit; et.

      step. iSplit; et.
      iPureIntro. repeat f_equal. rewrite unfold_fib; nia.
    }
    Unshelve. all: ss. exact (0↑).
  (*SLOW*)Admitted.

  Lemma simF_main:
    ISim.sim_fun open KnotMainAMod KnotMainIMod KnotMainA.init_cond IstFull None.
  Proof using APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    init_simF.

    (* SKINCL *)
    pose proof (@CEnv.incl_incl_env KnotMainGEnv.t genv) as INCLENV.
    unfold KnotMainGEnv.t in GEnvIncl; ss.
    eapply INCLENV in GEnvIncl; et. unfold CEnv.incl_env in GEnvIncl.
    specialize (@GEnvIncl KnotMainHdr.fib Gfun↑) as SF.
    hexploit SF; [left; ss|intro SKINCL_F].
    des. clear SF INCLENV. inv KnotInSp.

    (* SKWF *)
    apply CEnv.load_genv_wf in GEnvWF. unfold CEnv.wf in GEnvWF.
    specialize (GEnvWF KnotMainHdr.fib blk). apply GEnvWF in FIND; et. apply GEnvWF in FIND as FINDF.

    (* SRC: precondition *)
    steps_l. destruct q; ss. iDestruct "IST" as "[% FG]". des; subst. hss.

    (* TGT: find a block of the function "fib" using SKINCL *)
    steps_r. rewrite FINDF; hss. steps_r.

    (* TGT: inlining "fib" *)
    inline_r. steps_r. force_r Fib. forces_r. iSplitL "FG"; et.
    { (* prove the precondition of "fib" *)
      iFrame. iSplit; et. iPureIntro. eexists. esplits; et. econs; esplits; et.
      eapply fn_has_weaker_spec_in.
      { econs; [|refl]. apply MainInFun. unfold MainFunSp. unseal CRIS. ss. }
      { unfold fspec_imply, precond, postcond, fun_gen, fib_spec, fun_gen, fib_spec, fspec_apc; ss. 
        ii. exists (x1, (knot_frag (Some Fib))%I). split; red.
        { i. iIntros "[[% FG] %]". unfold precond, fun_gen, fib_spec; ss.
          des; subst; hss. iModIntro. iSplit; et. iSplit; et; cycle 1.
          iPureIntro. exists fb. esplits; et. inv H5. econs; et. eapply fn_has_weaker_spec_in; et.
          unfold fspec_imply, precond, postcond, fun_gen, fib_spec, fun_gen, fib_spec, fspec_apc; ss.
          ii. eexists. split; red.
          { red. instantiate (1:=(_, x0)). ss. iIntros; iFrame; et. }
          { i. ss. iIntros; et. }
        }
        { i. ss. iIntros; et. }
      }
    }

    (* TGT: take a postcondition of "fib" *)
    steps_r. iDestruct "GRT" as "[[% FG] %]"; des; subst; hss. steps_r. inv H3.

    (* TGT: find a block of the function "rec" using the postcondition of "fib" *)
    rewrite FBLOCK; hss. steps_r.
    
    (* SRC: handle pure (APC) *)
    unfold pure. steps_l.
    force_l 30%ord. steps_l. inv SPEC. force_l.
    forces_l. iSplitR; et. steps_l.

    (* SRC: inlining APC *)
    inline_l. steps_l. iDestruct "ASM" as "%"; des; subst; hss. steps_l.
    unfold apc_body, APC. force_l 1. steps_l. 
    
    (* SRC, TGT: call "fib" using APC tactic *)
    apc_call_weaker "FG"; et.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat; et. }
    { instantiate (1:= 29). eapply OrdArith.lt_from_nat; nia. }
    { unfold precond. ss. instantiate (1:=(Fib, 10)). iFrame. iSplit; et.
      { iPureIntro. eexists; esplits; ss.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.le_from_nat; nia. }
      { do 4 iExists []. ss. iPureIntro; hrepeat do 6 unfold_mod; ss; esplits; eauto; prove_scope. }
    }
    iDestruct "ISTPOST" as "[IST [% FG]]". subst. steps_r. hss. steps_r.

    (* SRC: jump APC *)
    apc_l. steps_l. forces_l. iSplit; et. steps_l. 
    step. iSplitR; et.
    Unshelve. all: ss.
  (*SLOW*)Admitted.

  Theorem sim : ISim.t open KnotMainAMod KnotMainIMod KnotMainA.init_cond IstFull.
  Proof.
    init_sim.
    - exfalso. revert H. unfold_mod; ss.
    - eapply simF_fib; et.
    - eapply simF_main; et.
  Qed.

  Theorem ctxr :
    ctx_refines
      (KnotMainA.t true genv SpRec Sp
        ★ KnotA.t genv SpRec SpFun Sp
        ★ MemP.t
        ★ APCA.t SpPure Sp,
      KnotMainA.init_cond)
      (KnotMainI.t genv
        ★ KnotA.t genv SpRec SpFun Sp
        ★ MemP.t
        ★ APCA.t SpPure Sp,
      emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.

  Theorem ctxr_close:
    ctx_refines
      (KnotMainA.t false genv SpRec Sp ★ APCC.t Sp, emp%I)
      (KnotMainA.t true  genv SpRec Sp ★ APCC.t Sp, emp%I).
  Proof using _crisG _memG APCInSp GEnvIncl GEnvWF KnotInSp MainInFun PureInGlobal RecInSpPure.
    eapply main_adequacy.
    init_sim.
    { exfalso. revert H. hrepeat do 1 unfold_mod. i; inv H. }
    { init_simF.
      steps_l. iDestruct "ASM" as "[[% PRE] %]"; des; hss.
      steps_l. force_l vo. steps_l. forces_l.
      iSplitR; eauto. steps_l. force_r (q1, q2).
      forces_r. iSplitL "PRE".
      { iFrame; iPureIntro; esplits; eauto. }
      hss. steps_r. iDestruct "GRT" as "%"; des; hss.
      call "IST"; eauto.
      steps_l. steps_r. forces_r. iSplitL "ASM"; eauto.
      steps_r. iDestruct "GRT" as "[% POST]". forces_l.
      iSplitL "POST"; iFrame; eauto.
      step. iFrame; eauto.
    }
    { init_simF.
      steps_l. hss. iDestruct "IST" as "%"; des; hss.
      steps_r. rewrite /pure. steps_r. inline_r. forces_r.
      iDestruct "GRT" as "(% & %)". hss. iSplitR; et.
      steps_r. forces_r. iSplitR; et.
      steps_r. forces_l. step.
      iSplit; eauto.
    }
  Unshelve. all: et.
  (*SLOW*)Admitted.

End KnotMainIA. End KnotMainIA.
