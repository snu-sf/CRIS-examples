Require Import CRIS Cancel.

Require Import MutHeader MutFA MutGA MutMainA.
Require Import MutFI MutGI MutMainI.
Require Import MutFIAproof MutGIAproof MutMainIAproof.
Require Import APCHeader APC APCI APCA APCC.
Require Import APCIAproof APCACproof.

Module MutAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Definition irΓ : Γ := **[ir_invΓ].
  Definition irΣ : Σ := **[irΓ; ir_invΣ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof. solve_ir_valid. Qed.

  Local Definition smod_src : SMod.t := MutMainA.Mod false ☆ MutFA.Mod ☆ MutGA.Mod ☆ APCC.Mod.
  Local Definition sp : sp_type := ElimRel.sp_from smod_src.

  Local Definition smod_pure : SMod.t := MutFA.Mod ☆ MutGA.Mod.
  Local Definition sp_pure : spl_type := MutFA.SpF ++ MutGA.SpG.

  Local Definition mod_cancel : HMod.t := SMod.to_hmod sp_none (SMod.cancel smod_src).
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := MutMainI.t ★ MutFI.t ★ MutGI.t ★ APCI.t.

  Local Definition init_cond : iProp Σ := MutFA.init_cond ∗ MutGA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, init_cond)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply Cancel.cancellation.
    - ii; des; subst; inv FIND; ss; rewrite !eq_rel_dec_correct in H0; des_ifs.
    - econs; [refl|]; i; inv NS; des; inv H; des; inv H1;
      rewrite !eq_rel_dec_correct in H2; des_ifs.
    - econs; unfold_hmod; ss; prove_nodup.
  Qed.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt !add_interp_comm.

    (* abstraction of APCI to APCA *)
    etrans; cycle 1.
    { do 3 ctxr_drop.
      eapply APCIA.ctxr.
    }

    (* abstraction of MutF *)
    etrans; cycle 1.
    { ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply MutFIA.ctxr with (Sp:=sp) (SpPure:=sp_pure).
      { rewrite /sp /sp_incl /APCA.Sp. unseal CRIS.
        split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_pure /MutGA.SpG /spl_sub /MutFA.SpF. unseal CRIS.
        i. eapply alist_find_comm; try prove_nodup; eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_incl /MutFA.SpF /MutGA.SpG /ElimRel.sp_from. unseal CRIS.
        split; try prove_nodup. i; ss. des_ifs;
        i; des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
    }

    (* abstraction of MutG *)
    etrans; cycle 1.
    { ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply MutGIA.ctxr with (Sp:=sp) (SpPure:=sp_pure).
      { rewrite /sp /sp_incl /APCA.Sp. unseal CRIS.
        split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_pure /MutGA.SpG /spl_sub /MutFA.SpF. unseal CRIS.
        i. eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_incl /MutFA.SpF /MutGA.SpG /ElimRel.sp_from. unseal CRIS.
        split; try prove_nodup. i; ss. des_ifs;
        i; des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
    }

    (* abstraction of MutMain *)
    etrans; cycle 1.
    { ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      eapply MutMainIA.ctxr with (Sp:=sp) (SpPure:=sp_pure).
      { rewrite /sp /sp_incl /APCA.Sp. unseal CRIS.
        split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_pure /MutGA.SpG /spl_sub /MutFA.SpF. unseal CRIS.
        i. eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_incl /MutFA.SpF /MutGA.SpG /ElimRel.sp_from. unseal CRIS.
        split; try prove_nodup. i; ss. des_ifs;
        i; des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
    }
    
    (* abstraction of APCA to APCC *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_drop. eapply APCAC.ctxr.
      { rewrite /sp /sp_incl /APCA.Sp. unseal CRIS.
        split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_pure /sp /sp_incl /MutFA.SpF /MutGA.SpG /ElimRel.sp_from. unseal CRIS.
        split; try prove_nodup. i; ss. des_ifs;
        i; des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_pure /MutFA.SpF /MutGA.SpG /find_body; unfold_hmod.
        i; ss; des_ifs.
        { do 2 eexists. unfold_hmod; ss; des_ifs. }
        { do 2 eexists. hrepeat do 2 unfold_hmod; ss; des_ifs. }
      }
    }

    (* elimination of pure call *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 2 ctxr_drop.
      eapply MutMainIA.ctxr_close with (Sp:=sp) (SpPure:=sp_pure).
      { rewrite /sp /sp_incl /APCA.Sp. unseal CRIS.
        split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_pure /MutGA.SpG /spl_sub /MutFA.SpF. unseal CRIS.
        i. eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_incl /MutFA.SpF /MutGA.SpG /ElimRel.sp_from. unseal CRIS.
        split; try prove_nodup. i; ss. des_ifs;
        i; des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
    }

    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_swap. ctxr_rotate. ctxr_refl. }

    rewrite /MutMainA.t /MutFA.t /MutGA.t /APCC.t. unseal CRIS.
    eapply ctxr_cond_strengthen.
    iIntros "[? ?]". iFrame.
  (*SLOW*)Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, init_cond)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel (irΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H.
    { rewrite /mod_tgt /MutMainI.t /MutFI.t /MutGI.t /APCI.t; unseal CRIS; prove_nodup. }
    clear H; intros [_ H].
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      { eauto. }
      all: solve_res.
    }
    { exists x; des; eauto. }
  (*SLOW*)Qed.
End MutAll.
(* Print Assumptions MutAll.behavioral_refinement. *)
