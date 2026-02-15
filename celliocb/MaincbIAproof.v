Require Import CRIS.
From CRIS.celliocb Require Import CelliocbHeader CelliocbA MaincbHeader MaincbA MaincbI CtxcbHeader.


Module MaincbIA. Section MaincbIA.
  Import CelliocbA.
  Context `{!crisG Γ Σ α β τ _S _I, _CELLIOCB: !celliocbGS}.

  Context (sp : specmap).
  Context (sp_foo: sp.1 !! fid CtxcbHdr.foo = None).
  
  Local Notation CelliocbAMod := (CelliocbA.t).
  Local Notation MaincbA := (MaincbA.t sp).
  Local Notation IstFull := (IstProd (IstSB MaincbA.(Mod.scopes) IstTrue) IstEq).

  Lemma simF_main : ISim.sim_fun open MaincbA (MaincbI.t ★ CelliocbAMod) IstFull entry.
  Proof using sp_foo.
    iStartSim.
    unfold MaincbA.main, MaincbI.main.
    
    (* Take cell(0) *)
    steps_l.
    iDestruct "ASM" as "[-> ASM]".

    (* Give cell(0) *)
    steps_r. inline_r. steps_r. forces_r. iFrame.
    
    (* Inline input_stdin() *)
    steps_r. inline_r. steps_r. unfold MaincbI.input_stdin. 
    
    (* trigger IO together *)
    step. rename ret into i. 
    steps_r. steps_l. rewrite sp_foo.

    (* Take cell(i) *)
    inline_r. rewrite /get. steps_r. forces_r. iFrame. steps_r.

    (* call foo together *)
    call "IST". iIntros "% % % IST".

    (* TGT : handle set(input_db) *)
    steps_l. steps_r.
    destruct Any.downcast; steps_l; des_ifs. steps_r.
    
    (* TGT : inline set *)
    inline_r. steps_r. forces_r.

    (* TGT : give cell i *)
    iFrame. steps_r.
    
    (* TGT : inline input_db *)
    inline_r. rewrite /MaincbI.input_db. steps_r.

    (* handle IO together *)
    step. steps_r.

    (* TGT : inline get *)
    inline_r.
    steps_r. unfold get. force_r ret0.
    
    (* TGT : get cell ret *)
    forces_r. iFrame.

    steps_r. steps_l. 
    
    (* handle IO together *)
    step. steps_l. steps_r. forces_l. iSplit; et. step. iFrame; et. 
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MaincbA (MaincbI.t ★ CelliocbAMod) MaincbA.init_cond IstFull.
  Proof using sp_foo.
    init_sim.
    { iIntros "_". unfold IstFull, IstProd. repeat (iExists ∅). ss. } 
    { eapply simF_main; eauto. }
  Qed.
End MaincbIA. End MaincbIA.
