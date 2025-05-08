Require Import CRIS Cancel.

Require Import MutHeader MutMainHeader MutFA MutGA MutMainA.
Require Import MutFI MutGI MutMainI.
Require Import MutFIAproof MutGIAproof MutMainIAproof.
Require Import APCHeader APC APCI APCA APCC.
Require Import APCIAproof APCACproof.

Module MutAll.
  Import inv_instances.

  Local Instance Γ : HRA := ##[invΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  Definition irΓ : Γ := **[ir_invΓ 0].
  Definition irΣ : Σ := **[irΓ; ir_invΣ 0].

  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof. solve_ir_valid. Qed.

  Local Definition smod_src : SMod.t := MutMainA.Mod false ☆ MutFA.Mod ☆ MutGA.Mod ☆ APCC.Mod.
  Local Definition sp : string → option fspec := sp_from smod_src.

  Local Definition smod_pure : SMod.t := MutFA.Mod ☆ MutGA.Mod.
  Local Definition sp_pure : string → option fspec := sp_from smod_pure.

  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.
  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.
  Local Definition mod_tgt : HMod.t := MutMainI.t ★ MutFI.t ★ MutGI.t ★ APCI.t.

  Local Definition main_fsp : fspec := MutMainA.main_spec.
  Local Definition init_cond : iProp Σ := MutFA.init_cond ∗ MutGA.init_cond.

  (* Apply cancellation to linked spec module *)
  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof. eapply cancellation; try by econs. i. iIntros "%POST". iPureIntro. des; eauto. Qed.

  Ltac prove_sp :=
    rewrite /APCA.Sp /MutFA.SpF /MutGA.SpG /sp /smod_src /sp_pure /sp_incl /sp_sub /find_body
      /pure_specbody /sp_from /smod_pure /option_map; try unseal CRIS; try prove_nodup;
    ii; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs; eexists; ss.

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
      eapply MutFIA.ctxr with (Sp:=sp) (SpPure:=sp_pure); try prove_sp.
    }

    (* abstraction of MutG *)
    etrans; cycle 1.
    { ctxr_drop. ctxr_rotate. ctxr_drop. ctxr_rotate.
      eapply MutGIA.ctxr with (Sp:=sp) (SpPure:=sp_pure); try prove_sp.
    }

    (* abstraction of MutMain *)
    etrans; cycle 1.
    { ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      eapply MutMainIA.ctxr with (Sp:=sp) (SpPure:=sp_pure); try prove_sp.
    }
    
    (* abstraction of APCA to APCC *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_drop. eapply APCAC.ctxr.
      - prove_sp.
      - prove_sp.
      - rewrite /MutFA.t /MutGA.t. unseal CRIS. prove_sp.
    }

    (* elimination of pure call *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 2 ctxr_drop.
      eapply MutMainIA.ctxr_close with (Sp:=sp) (SpPure:=sp_pure); try prove_sp.
    }

    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_swap. ctxr_rotate. ctxr_refl. }

    rewrite /MutMainA.t /MutFA.t /MutGA.t /APCC.t. unseal CRIS.
    eapply ctxr_cond_strengthen.
    iIntros "[? ?]". iFrame.
  (*SLOW*)Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
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
