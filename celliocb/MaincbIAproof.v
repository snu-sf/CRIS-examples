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
    steps_l; iDestruct "IST" as "[IST ASM ]"; subst.

    (* Give cell(0) *)
    steps_r. inline_r.
    steps_r. hss. 
    steps_r. forces_r. iFrame.
    
    (* Inline input_stdin() *)
    steps_r. inline_r.
    steps_r. 
    
    (* trigger IO together *)
    step. rename ret into i. 
    steps_r. hss.
    
    (* Take cell(i) *)
    steps_r.
    hss. steps_r.
    steps_l.

    (* TGT : inline CellioA.get() *)
    inline_r.
    steps_r. 
    forces_r. 
    iFrame.

    steps_r. hss. steps_r.

    (* call foo together *)
    call "IST".
    {
      iDestruct "IST" as "[-> [-> ->]]".
      repeat iExists []. iSplit; eauto;
      repeat unfold_hmod; ss;
      repeat (iSplit; eauto); iPureIntro; prove_scope.
    }

    (* TGT : handle set(input_db) *)
    steps_l.
    steps_r. hss. steps_r.
    
    (* TGT : inline set *)
    inline_r.
    steps_r. hss.
    forces_r.

    (* TGT : give cell i *)
    iFrame.
    steps_r.
    
    (* TGT : inline input_db *)
    inline_r.
    steps_r.

    (* handle IO together *)
    step.
    steps_r. hss. 
    steps_r. hss. 
    steps_r. 
    
    (* TGT : inline get *)
    inline_r.
    steps_r. force_r ret.
    
    (* TGT : get cell ret *)
    forces_r. iFrame.
    
    steps_r. hss. steps_r. 
    steps_l. 
    
    (* handle IO together *)
    step. step. iSplit; done.
  (*SLOW*)Qed.

  Theorem sim :
    HSim.t open MaincbA (MaincbI.t ★ CelliocbA) MaincbA.InitCond IstFull.
  Proof using CtxInSp.
    init_sim.
    - exfalso. revert H0. rewrite /MaincbI.t /CelliocbA. unseal CRIS; ss.
    - eapply simF_main; eauto.
  Qed.
End MaincbIA. End MaincbIA.
