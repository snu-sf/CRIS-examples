Require Import CRIS.

Require Import KnotHeader KnotMainHeader KnotMainI KnotMainA KnotA KnotI KnotIAproof.
Require Import APCHeader APC APCA APCTactics.

Set Implicit Arguments.

Module KnotMainIA. Section KnotMainIA.
  Import KnotA KnotMainA APCA.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ, !KnotAGΓ Γ, !memGΓ Γ}.

  (* 1. global environment *)
  Context (genv: GEnv.t).
  (* 3. spec tables *)
  Context (SpRec SpFun SpPure Sp: string -> option fspec).
  (* 4. hypotheses for genv *)
  Context (GEnvWF: GEnv.wf genv).
  Context (GEnvIncl: incl KnotMainGEnv.t genv).
  (* 5. hypotheses for sp *)
  Context (MainInFun: sp_incl (MainFunSp genv SpRec) SpFun).
  Context (KnotInSp: sp_incl KnotRecSp Sp).
  Context (APCInSp: sp_incl APCA.Sp Sp).
  (* 6. hypotheses for pure sp *)
  Context (RecInSpPure: sp_sub SpRec SpPure).
  Context (PureInGlobal : sp_sub SpPure Sp).

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ _ _, True%I.  

  Local Definition APCA := (APCA.t SpPure Sp).
  Local Definition MemA := (MemA.t Sp).
  Local Definition KnotA := (KnotA.t genv SpRec SpFun Sp).
  Local Definition KnotAMod := (KnotA ★ MemA ★ APCA).
  Local Definition KnotMainA := (KnotMainA.t genv SpRec Sp).
  Local Definition KnotMainI := (KnotMainI.t genv).
  Local Definition KnotMainAMod := (KnotMainA ★ KnotAMod).
  Local Definition KnotMainIMod := (KnotMainI ★ KnotAMod).
  Local Definition IstFull := (IstProd (IstSB KnotMainA.(HMod.scopes) Ist) IstEq).
  
  (*************)

  Lemma simF_fib:
    HSim.sim_fun open KnotMainAMod KnotMainIMod IstFull KnotMainHdr.fib.
  Proof.
    init_simF 0 0.

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
  (*FAST*)Qed.

  Lemma simF_main:
    HSim.sim_fun open KnotMainAMod KnotMainIMod IstFull KnotMainHdr.main.
  Proof.
    init_simF 0 0.

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
    steps_l. destruct q; ss. iDestruct "ASM" as "[[% FG] %]". des; subst. hss.

    (* TGT: find a block of the function "fib" using SKINCL *)
    steps_r. rewrite FINDF; hss. steps_r.

    (* TGT: inlining "fib" *)
    inline_r. steps_r. force_r Fib. forces_r. iSplitL "FG"; et.
    { (* prove the precondition of "fib" *)
      iFrame. iSplit; et. iPureIntro. eexists. esplits; et. econs; esplits; et.
      eapply fn_has_spec_weaker.
      { econs; [|refl]. apply MainInFun. unfold MainFunSp. unseal CRIS. ss. }
      { unfold fspec_weaker, precond, postcond, fun_gen, fib_spec, fun_gen, fib_spec, fspec_apc; ss. 
        ii. exists (x_src, (knot_frag (Some Fib))%I). split; red.
        { i. iIntros "[[% FG] %]". unfold precond, fun_gen, fib_spec; ss.
          des; subst; hss. iModIntro. iSplit; et. iSplit; et; cycle 1.
          iPureIntro. exists fb. esplits; et. inv H5. econs; et. eapply fn_has_spec_weaker; et.
          unfold fspec_weaker, precond, postcond, fun_gen, fib_spec, fun_gen, fib_spec, fspec_apc; ss.
          ii. eexists. split; red.
          { red. instantiate (1:=(_, x_src0)). ss. iIntros; iFrame; et. }
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
    apc_call_weaker "IST FG"; et.
    { instantiate (1:=0). eapply OrdArith.lt_from_nat; et. }
    { instantiate (1:= 29). eapply OrdArith.lt_from_nat; nia. }
    { unfold precond. ss. instantiate (1:=(Fib, 10)). iFrame. iSplit; et. iPureIntro. eexists; esplits; ss.
      rewrite -OrdArith.mult_from_nat -OrdArith.add_from_nat. apply OrdArith.le_from_nat; nia. }
    iDestruct "ISTPOST" as "[IST [% FG]]". subst. steps_r. hss. steps_r.

    (* SRC: jump APC *)
    apc_l. steps_l. forces_l. iSplit; et. steps_l. force_l. steps_l. forces_l. iSplit; et.
    steps_r. hss. steps_r.
    step. iSplitR; et.
    Unshelve. all: ss.
  (*FAST*)Qed.

  Theorem sim : HSim.t open KnotMainAMod KnotMainIMod KnotMainA.init_cond IstFull.
  Proof.
    init_sim.
    - iIntros "IC". iExists [], [], [], []. do 4 (iSplit; et); iPureIntro; ss.
    - eapply simF_fib; et.
    - eapply simF_main; et.
  Qed.
End KnotMainIA.

Section ctxr.
  Context `{!invG α Σ Γ, !subG Γ Σ, !sinvG Σ Γ α β τ}.
  Context `{!KnotAGΓ Γ, !memGΓ Γ}.
  
  Theorem ctxr (genv: GEnv.t)
    (SpRec SpFun SpPure Sp: string -> option fspec)
    (GEnvWF: GEnv.wf genv)
    (GEnvIncl: incl KnotMainGEnv.t genv)
    (MainInFun: sp_incl (KnotMainA.MainFunSp genv SpRec) SpFun)
    (KnotInSp: sp_incl KnotA.KnotRecSp Sp)
    (APCInSp: sp_incl APCA.Sp Sp)
    (RecInSpPure: sp_sub SpRec SpPure)
    (PureInGlobal : sp_sub SpPure Sp)
  :
    ctx_refines
      (KnotMainA.t genv SpRec Sp
        ★ KnotA.t genv SpRec SpFun Sp
        ★ MemA.t Sp
        ★ APCA.t SpPure Sp,
      KnotMainA.init_cond)
      (KnotMainI.t genv
        ★ KnotA.t genv SpRec SpFun Sp
        ★ MemA.t Sp
        ★ APCA.t SpPure Sp,
      emp%I).
  Proof. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End KnotMainIA.
