Require Import CRIS Cancel CallFilter.
Require Import MemHeader MemI MemA MemIAproof.
Require Import APCHeader APC APCI APCA APCC APCACproof APCIAproof.
Require Import KnotHeader KnotMainHeader KnotI KnotMainI.
Require Import KnotA KnotMainA.
Require Import KnotIAproof KnotMainIAproof.

Module KnotAll.
  Import inv_instances.

  (* mem *)
  Local Definition csl : string → bool := λ _, false.
  (* global environment *)
  Local Definition genv : GEnv.t := KnotGEnv.t ++ KnotMainGEnv.t.
  
  Local Instance Γ : HRA := ##[invΓ; memΓ; knotΓ].
  Local Instance Σ : GRA := ##[Γ; invΣ].
  (* initial resource *)
  Local Definition irΓ : Γ := **[ir_invΓ; ir_memΓ csl genv; ir_knotAΓ].
  Local Definition irΣ : Σ := **[irΓ; ir_invΣ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ ir_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply ir_knotRA_valid.
  Qed.

  (* pure sp *)
  Local Definition sp_rec : spl_type := KnotA.KnotRecSp.
  Local Definition sp_fun : spl_type := KnotMainA.MainFunSp genv sp_rec.
  Local Definition sp_pure : spl_type :=
    (KnotMainA.MainFunSp genv sp_rec) ++ KnotA.KnotRecSp.

  Local Definition smod_src : SMod.t :=
    (KnotMainA.smod false genv sp_rec) ☆ (KnotA.smod genv sp_rec sp_fun)
    ☆ APCC.smod.
  Local Definition sp : sp_type := sp_from smod_src.

  Local Definition mod_top : Mod.t := SMod.to_mod sp_none (SMod.cancel smod_src).
  Local Definition mod_src : Mod.t := SMod.to_mod sp smod_src.
  Local Definition mod_tgt : Mod.t :=
    KnotMainI.t genv ★ KnotI.t genv ★ MemI.t csl genv ★ APCI.t.

  Local Lemma genv_wf : GEnv.wf genv.
  Proof. cbn. prove_nodup. Qed.

  Local Definition init_cond : iProp Σ :=
    winv (⊤,⊤) ∗ KnotMainA.init_cond ∗ (KnotA.init_cond genv) ∗ (MemP.init_cond csl genv).

  Lemma cancel_src :
    refines (mod_top, init_cond)
            (mod_src, init_cond).
  Proof.
    eapply Cancel.cancellation.
    - ii; des; subst; inv FIND; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs.
    - econs; [refl|]; i; inv NS; des; inv H; des; inv H1;
      rewrite ->!eq_rel_dec_correct in *; des_ifs.
    - econs; prove_nodup.
  Qed.

  (* Ltac prove_sp :=
    rewrite /APCA.Sp /KnotA.KnotRecSp /KnotA.KnotSp /KnotMainA.MainFunSp /KnotMainA.MainSp;
    rewrite /sp /sp_pure /sp_fun /sp_rec /smod_src /sp_pure /sp_incl /sp_sub /find_body /pure_specbody /sp_from /option_map;
    rewrite /sp_fun /sp_rec /APCA.Sp /KnotA.KnotRecSp /KnotA.KnotSp /KnotMainA.MainFunSp /KnotMainA.MainSp;
    try unseal CRIS; try prove_nodup;
    ii; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs; ss; eexists; ss. *)

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    rewrite /mod_src /mod_tgt !add_interp_comm.

    (* abstraction of Mem *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 3 ctxr_drop.
      eapply MemIP.ctxr.
    }

    (* abstraction of APCI to APCA *)
    etrans; cycle 1.
    { ctxr_rotate. do 3 ctxr_drop.
      eapply APCIA.ctxr.
    }

    (* abstraction of Knot *)
    etrans; cycle 1.
    { ctxr_drop.
      eapply KnotIA.ctxr with (Sp:=sp) (SpPure:=sp_pure) (SpRec:=sp_rec) (SpFun:=sp_fun).
      { eapply genv_wf. }
      { unfold genv. eapply incl_appl; refl. }
      { unfold sp_rec. ss. }
      { unfold sp, APCA.Sp. unseal CRIS.
        rewrite /sp_from /= /to_sp /= /sp_incl; split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_fun /sp_pure /spl_sub. i. eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_from /to_sp /sp_incl /=.
        rewrite /KnotMainA.MainFunSp /KnotA.KnotRecSp /KnotMainA.fib_spec
          /KnotA.rec_spec /KnotA.knot_spec /APCA.apc_spec; unseal CRIS; ss; i;
        des; try prove_nodup; i; des_ifs. }
    }

    (* abstraction of KnotMain *)
    etrans; cycle 1.
    { ctxr_norm. eapply KnotMainIA.ctxr.
    { eapply genv_wf. }
      { unfold genv. eapply incl_appr; refl. }
      { unfold sp_rec. ss. }
      { unfold sp, KnotA.KnotRecSp. unseal CRIS.
        rewrite /sp_from /= /to_sp /= /sp_incl; split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /APCA.Sp /sp /sp_incl. unseal CRIS; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_rec /sp_pure /spl_sub. i. eapply alist_find_comm.
        { rewrite /KnotA.KnotRecSp /KnotMainA.MainFunSp. unseal CRIS. prove_nodup. }
        eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_from /to_sp /sp_incl /=.
        rewrite /KnotMainA.MainFunSp /KnotA.KnotRecSp /KnotMainA.fib_spec
          /KnotA.rec_spec /KnotA.knot_spec /APCA.apc_spec; unseal CRIS; ss; i;
        des; try prove_nodup; i; des_ifs. }
    }

    (* abstraction of APCA to APCC *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_drop.
      eapply APCAC.ctxr.
      - rewrite /APCA.Sp /sp /sp_incl; unseal CRIS; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs.
      - rewrite /sp_incl /sp_pure /sp /KnotMainA.MainFunSp /KnotA.KnotRecSp.
        unseal CRIS; split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs.
      - rewrite /sp_pure /KnotMainA.MainFunSp /KnotA.KnotRecSp /KnotMainA.t /KnotA.t.
        unseal CRIS.
        i; des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs.
        + do 2 eexists. rewrite /find_body; ss.
        + do 2 eexists. rewrite /find_body; ss.
    }

    (* elimination of pure call *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      eapply KnotMainIA.ctxr_close with (Sp:=sp) (SpPure:=sp_pure).
      { eapply genv_wf. }
      { unfold genv. eapply incl_appr; refl. }
      { rewrite /spl_sub; i; eauto. }
      { unfold sp, KnotA.KnotRecSp. unseal CRIS.
        rewrite /sp_from /= /to_sp /= /sp_incl; split; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /APCA.Sp /sp /sp_incl. unseal CRIS; try prove_nodup.
        i. des_ifs; ss; unfold dec, option_Dec, AList.option_Dec_obligation_1 in *; des_ifs. }
      { rewrite /sp_rec /sp_pure /spl_sub. i. eapply alist_find_comm.
        { rewrite /KnotA.KnotRecSp /KnotMainA.MainFunSp. unseal CRIS. prove_nodup. }
        eapply alist_find_app; eauto. }
      { rewrite /sp_pure /sp /sp_from /to_sp /sp_incl /=.
        rewrite /KnotMainA.MainFunSp /KnotA.KnotRecSp /KnotMainA.fib_spec
          /KnotA.rec_spec /KnotA.knot_spec /APCA.apc_spec; unseal CRIS; ss; i;
        des; try prove_nodup; i; des_ifs. }
    }

    (* elimination of mem *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 3 ctxr_drop. eapply CFilter.elim_module. }
    rewrite -mod_add_empty_r.

    etrans; cycle 1.
    { ctxr_swap. ctxr_rotate. ctxr_refl. }

    rewrite /KnotMainA.t /KnotA.t /MemA.t /APCC.t. unseal CRIS.
    eapply ctxr_cond_strengthen.
    iIntros "[? [? ?]]". iFrame.
  (*SLOW*)Qed.

  Lemma top_tgt :
    refines (mod_top, init_cond)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Lemma tgt_wf:
    Mod.wf mod_tgt.
  Proof.
    rewrite /mod_tgt /KnotMainI.t /KnotI.t /MemI.t /APCI.t. unseal CRIS. prove_nodup. 
  Qed.

  Local Transparent mem_points_to_singleton_r.
  Local Transparent CEnv.load_genv.
  
  Lemma init_cond_valid:
    ∃ rs, ✓ rs ∧ (Own rs ⊢ init_cond).
  Proof.
    exists (irΣ ⋅ ir_own_admin). split.
    - apply irΣ_valid.
    - simplify_res.
      { rewrite make_own_admin; iFrame.
        iDestruct "H14" as "[A F]". iFrame.
        iDestruct "H16" as "[A F]". iFrame.
        rewrite /KnotA.var_points_to; s.
        assert (mem_init_frag_r csl genv ≡
                mem_points_to_singleton_r (2, 0%Z) 1 (Vint 0)).
        { rewrite /mem_init_frag_r /mem_points_to_singleton_r /=. f_equiv.
          intros blk ofs. rewrite /mem_init_val; ss. do 3 (destruct blk; hss).
          { rewrite discrete_fun_lookup_singleton. destruct ofs; hss. }
          do 3 (destruct blk; hss).
        }
        rewrite H. iFrame.
      }
      all: solve_res.
  Qed.
  
  Theorem behavioral_refinement :
    ∃ src_res tgt_res, refines_lmod
      (Mod.to_lmod mod_top src_res)
      (Mod.to_lmod mod_tgt tgt_res).
  Proof.
    move: (top_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H; eauto using tgt_wf. clear H; intros [WF H].
    assert (IV:= init_cond_valid). des.
    destruct (H rs); des; et.
    rewrite IV0 /init_cond {1}winv_split_empty. iIntros "[[? ?] ?]". iFrame; done.
  (*SLOW*)Qed.
End KnotAll.

(* Print Assumptions KnotAll.behavioral_refinement. *)
