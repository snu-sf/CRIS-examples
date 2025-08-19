Require Import CRIS.
From CRIS.celliocb Require Import CelliocbHeader CelliocbA MaincbHeader MaincbA MaincbI CtxcbHeader.

Set Implicit Arguments.

Module MaincbIA. Section MaincbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I}.
  Context `{_celliocbG: !celliocbG}.

  Definition Ist: alist key Any.t -> alist key Any.t -> iProp Σ :=
    λ st_src st_tgt, emp%I.

  Context (sp: string -> option fspec).
  Context (sp_foo: sp CtxcbHdr.foo = None).
  
  Local Definition CelliocbA := (CelliocbA.t).
  Local Definition MaincbA := (MaincbA.t sp).
  Local Definition IstFull := (IstProd (IstSB MaincbA.(Mod.scopes) Ist) IstEq).

  Lemma simF_main:
    ISim.sim_fun open MaincbA (MaincbI.t ★ CelliocbA) MaincbA.init_cond IstFull MaincbHdr.main.
  Proof using sp_foo.
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
    steps_l. rewrite sp_foo.

    (* TGT : inline CellioA.get() *)
    inline_r.
    steps_r. 
    forces_r. 
    iFrame.

    steps_r. hss. steps_r.

    (* call foo together *)
    call "IST".
    {
      iDestruct "IST" as "[-> ->]".
      repeat iExists []. iSplit; eauto;
      repeat unfold_mod; ss;
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
    ISim.t open MaincbA (MaincbI.t ★ CelliocbA) MaincbA.init_cond IstFull.
  Proof using sp_foo.
    init_sim.
    (* - exfalso. revert H0. rewrite /MaincbI.t /CelliocbA. unseal CRIS; ss. *)
    - eapply simF_main; eauto.
  Qed.
End MaincbIA. End MaincbIA.
