Require Import CRIS.
From CRIS.celliocb Require Import CelliocbHeader CelliocbA MaincbHeader MaincbA MaincbI CtxcbHeader.


Module MaincbIA. Section MaincbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS}.
  Context `{_celliocbG: !celliocbGS}.

  Context (sp : specmap).
  Context (sp_foo: sp !! speckey_fn CtxcbHdr.foo = None).
  
  Local Definition CelliocbAMod := (CelliocbA.t).
  Local Definition MaincbA := (MaincbA.t sp).
  Local Definition IstFull := (IstProd (IstSB MaincbA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_main:
    ISim.sim_fun open MaincbA (MaincbI.t ★ CelliocbAMod) IstFull MaincbHdr.main.
  Proof using sp_foo.
    iStartSim.
    unfold MaincbA.main, MaincbI.main.
    
    (* Take cell(0) *)
    steps_l.
    iDestruct "ASM" as "[-> ASM]".

    (* Give cell(0) *)
    steps_r. inline_r.
    steps_r. hss. 
    steps_r. forces_r. iFrame.
    
    (* Inline input_stdin() *)
    steps_r. inline_r.
    steps_r. unfold MaincbI.input_stdin. 
    
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
    unfold get. 
    forces_r. 
    iFrame.

    steps_r. hss. steps_r.

    (* call foo together *)
    call "IST". iIntros "% % % IST".

    (* TGT : handle set(input_db) *)
    steps_l. steps_r.
    destruct Any.downcast; steps_l; des_ifs. hss. steps_r.
    
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
    unfold MaincbI.input_db.
    step.
    steps_r. hss. 
    steps_r. hss. 
    steps_r. 
    
    (* TGT : inline get *)
    inline_r.
    steps_r. unfold get. force_r ret0.
    
    (* TGT : get cell ret *)
    forces_r. iFrame.
    
    steps_r. hss. steps_r. 
    steps_l. 
    
    (* handle IO together *)
    step. steps_l. steps_r. forces_l. iSplit; et. steps_l. step. iFrame; et. 
  (*SLOW*)Qed.

  Theorem sim :
    ISim.t open MaincbA (MaincbI.t ★ CelliocbAMod) MaincbA.init_cond IstFull.
  Proof using sp_foo.
    init_sim.
    - unfold Mod.scopes. hss. unfold MaincbA.scopes. Search submseteq. ⊆+ admit.
    (* - exfalso. revert H0. rewrite /MaincbI.t /CelliocbA. unseal CRIS; ss. *)
    - iIntros "_". unfold IstFull, IstProd. repeat (iExists ∅). ss. 
    - eapply simF_main; eauto.
  Qed.
End MaincbIA. End MaincbIA.
