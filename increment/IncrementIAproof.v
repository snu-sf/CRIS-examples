Require Import CRIS.
Require Import SchHeader SchA SchTactics.
Require Import ImpPrelude MemHeader MemA.
Require Import IncrementHeader IncrementI IncrementA.

Module IncrementIA. Section IncrementIA.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_memG: !memG}.
  Context `{_schG: !schG}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ := λ _ _ _, emp%I.

  Context (u_s : univ_id).
  Context (sp_s sp_user_s sp_mem : string → option fspec).

  Context (SchInSpS : sp_incl (SchAS.sp u_s sp_user_s) sp_s).

  Local Definition MemA := (MemA.t sp_mem).
  Local Definition IncrementA := (IncrementA.t u_s sp_s).
  Local Definition IncrementI := (IncrementI.t).
  Local Definition IstFull := (IstProd (IstSB IncrementA.(HMod.scopes) Ist) IstEq).
  Local Definition MA := (IncrementA ★ MemA).
  Local Definition MI := (IncrementI ★ MemA).

  Lemma increment_simF : HSim.sim_fun open MA MI IstFull IncrementHdr.increment.
  Proof using SchInSpS.
    init_simF u_s 0.
    steps_l. iDestruct "ASM" as "[TID [-> ->]]".
    destruct q2 as [blk ofs]. rename q1 into tid. hss.
    steps_l.
    {
      rewrite /IncrementA.increment2.
      steps_l. steps_r.

      sch_yield_r. iFrame "IST TID".
      clear dependent nths st_src st_tgt; iIntros (nths st_s st_t _ _) "IST TID". steps_r.

      sch_yield_r. iFrame "IST TID".
      clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID". steps_r. sch_yield_l.

      iApply wsim_reset.
      iStopProof. revert nths. combine_quant st_s. combine_quant st_t.
      eapply wsim_coind.
      iIntros (g' [st_t [st_s nths]]) "[IST TID] %GG' #CIH /=".

      unfold_iter_l. unfold_iter_r.
      steps_l. steps_r.

      sch_yield_r. iFrame "IST TID".
      clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID". sch_yield_l.

      steps_l.
      inline_r. forces_r. instantiate (1:=(_, _, _, _)); iFrame "ASM". iSplit; first eauto.
      steps_r. iDestruct "GRT" as "[[PT ->] ->]". hss_r. steps_r.

      force_l false; steps_l. forces_l. iFrame "PT". steps_l. sch_yield_l. steps_l.
      unfold_iter_l. steps_l.
      sch_yield_r. iFrame "IST TID".
      clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID".
      sch_yield_r. iFrame "IST TID".
      clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID".

      (* We are getting memory resource for cas here *)
      sch_yield_l. steps_l.

      inline_r.
      destruct (decide (q0 = q)) eqn: _EQ; first subst q.
      { force_r (_,_,_,_,_,_,_,_,_,_).
        steps_r. hss. forces_r. iFrame "ASM".
        iSplitL "". { repeat (iSplitL; et). s. des_ifs. }
        steps_r. iDestruct "GRT" as "[[% [PT _]] %]". hss_r. steps_r. des_ifs.
        force_l true. steps_l. forces_l. iFrame "PT". steps_l.
        sch_yield_r. iFrame "IST TID".
        clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID". steps_r.
        sch_yield_r. iFrame "IST TID".
        clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID".
        rewrite _EQ. steps_r.

        sch_yield_l. steps_l. forces_l. iFrame "TID"; iSplit; first eauto.
        steps_l. step. iFrame. done.
      }
      { force_r (_,_,_,_,_,_,_,_,_,_).
        forces_r. iFrame "ASM". iSplitL "".
        { repeat iSplitL; et. s. des_ifs. }
        steps_r. iDestruct "GRT" as "[[% [PT _]] %]". hss_r. steps_r. des_ifs.
        force_l false; steps_l. force_l; iFrame "PT". steps_l.
        sch_yield_r. iFrame "IST TID".
        clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID". steps_r.
        sch_yield_r. iFrame "IST TID".
        clear nths st_s st_t; iIntros (nths st_s st_t _ _) "IST TID".
        rewrite _EQ. steps_r. sch_yield_l. steps_l.
        by_coind "CIH". iFrame.
      }
    }
  Unshelve. all: try exact 1%Qp. all: try exact Vundef.
  (*SLOW*)Qed.
End IncrementIA. End IncrementIA.
