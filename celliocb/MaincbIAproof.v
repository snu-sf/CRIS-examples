Require Import CRIS.
From CRIS.celliocb Require Import CelliocbHeader CelliocbA MaincbHeader MaincbA MaincbI CtxcbA.

Set Implicit Arguments.

Module MaincbIA. Section MaincbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _I _S}.
  Context `{_celliocbG: !celliocbG}.

  Definition Ist: nat -> alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ _ st_src st_tgt, emp%I.

  Context (sp_s: string -> option fspec).
  Context (CtxInSp: sp_incl CtxcbAS.sp sp_s). (* Specs of Ctxrary functions *)

  Local Definition CelliocbA := (CelliocbA.t).
  Local Definition MaincbA := (MaincbA.t sp_s).
  Local Definition IstFull := (IstProd (IstSB MaincbA.(HMod.scopes) Ist) IstEq).

  Lemma simF_main:
    HSim.sim_fun open MaincbA (MaincbI.t ★ CelliocbA) MaincbA.InitCond IstFull MaincbHdr.main.
  Proof using CtxInSp.
    init_simF.
    
    (* Take cell(0) *)
    steps_l; iDestruct "ASM" as "[ASM %]"; subst.

    steps_r. inline_r.
    (* Give cell(0) *)
    steps_r. force_r tt. steps_r. forces_r. iSplit; eauto.
    steps_r. hss. steps_r.
    forces_r. iFrame.

    steps_r. inline_r.
    steps_r. step. rename ret into i. 
    steps_r. hss.
    steps_r. iDestruct "GRT'" as "<-".
    hss. steps_r.
    steps_l.
    call "IST".
    {
      iDestruct "IST" as "[[-> [-> ->]] IC]".
      repeat iExists []. iSplit; eauto;
      repeat unfold_hmod; ss;
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    }

    steps_l.
    steps_r. hss. steps_r.
    inline_r.
    steps_r. force_r tt. steps_r. forces_r. iSplit; eauto.
    steps_r.
    forces_r. iFrame.
    steps_r. iDestruct "GRT'" as "<-". hss. 
    steps_r.
    step.
    steps_l.
    forces_l. iSplit; et.
    step.
    iSplit; et.

  (*SLOW*)Qed.

  Theorem sim :
    HSim.t open MaincbA (MaincbI.t ★ CelliocbA) MaincbA.InitCond IstFull.
  Proof using CtxInSp.
    init_sim.
    - exfalso. revert H0. rewrite /MaincbI.t /CelliocbA. unseal CRIS; ss.
    - eapply simF_main; eauto.
  Qed.
End MaincbIA. End MaincbIA.
