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

  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply ir_knotRA_valid.
  Qed.

  (* pure sp *)
  Local Definition sp_rec : string → option fspec := 
    to_sp KnotA.KnotRecSp.
  Local Definition sp_fun : string → option fspec :=
    to_sp (KnotMainA.MainFunSp genv sp_rec).
  Local Definition sp_pure : string → option fspec :=
    to_sp ((KnotMainA.MainFunSp genv sp_rec) ++ KnotA.KnotRecSp).

  Local Definition smod_src : SMod.t :=
    (KnotMainA.Mod false genv sp_rec) ☆ (KnotA.Mod genv sp_rec sp_fun)
    ☆ APCC.Mod.
  Local Definition sp : string → option fspec := sp_from smod_src.

  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  Local Definition mod_src : HMod.t := SMod.to_hmod sp smod_src.

  Local Definition mod_tgt : HMod.t :=
    KnotMainI.t genv ★ KnotI.t genv ★ MemI.t csl genv ★ APCI.t.

  Local Definition main_fsp : fspec := KnotMainA.main_spec.

  Local Lemma genv_wf : GEnv.wf genv.
  Proof. cbn. prove_nodup. Qed.

  Local Definition init_cond : iProp Σ :=
    KnotMainA.init_cond ∗ (KnotA.init_cond genv) ∗ (MemP.init_cond csl genv).

  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  Ltac prove_sp :=
    rewrite /APCA.Sp /KnotA.KnotRecSp /KnotA.KnotSp /KnotMainA.MainFunSp /KnotMainA.MainSp;
    rewrite /sp /sp_pure /sp_fun /sp_rec /smod_src /sp_pure /sp_incl /sp_sub /find_body /pure_specbody /sp_from /option_map;
    rewrite /sp_fun /sp_rec /APCA.Sp /KnotA.KnotRecSp /KnotA.KnotSp /KnotMainA.MainFunSp /KnotMainA.MainSp;
    try unseal CRIS; try prove_nodup;
    ii; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs; ss; eexists; ss.

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
      eapply KnotIA.ctxr with (Sp:=sp) (SpPure:=sp_pure) (SpRec:=sp_rec) (SpFun:=sp_fun); try prove_sp.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }

    (* abstraction of KnotMain *)
    etrans; cycle 1.
    { ctxr_norm. eapply KnotMainIA.ctxr; try prove_sp.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }

    (* abstraction of APCA to APCC *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. ctxr_drop.
      eapply APCAC.ctxr.
      - prove_sp.
      - prove_sp.
      - rewrite /KnotMainA.t /KnotA.t. unseal CRIS. prove_sp.
    }

    (* elimination of pure call *)
    etrans; cycle 1.
    { do 3 ctxr_rotate. do 2 ctxr_drop. ctxr_rotate.
      eapply KnotMainIA.ctxr_close with (Sp:=sp) (SpPure:=sp_pure); try prove_sp.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }

    (* elimination of mem *)
    etrans; cycle 1.
    { do 2 ctxr_rotate. do 3 ctxr_drop. eapply CFilter.elim_module. }
    rewrite hmod_add_empty_r.

    etrans; cycle 1.
    { ctxr_swap. ctxr_rotate. ctxr_refl. }

    rewrite /KnotMainA.t /KnotA.t /MemA.t /APCC.t. unseal CRIS.
    eapply ctxr_cond_strengthen.
    iIntros "[? [? ?]]". iFrame.
  (*SLOW*)Qed.

  Lemma cancel_tgt :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            (mod_tgt, emp%I).
  Proof.
    etrans.
    { eapply cancel_src. }
    { eapply src_tgt. }
  Qed.

  Local Transparent mem_points_to_singleton_r.
  Local Transparent CEnv.load_genv.

  Theorem behavioral_refinement :
    ∃ target_resource, refines_mod
      (HMod.to_mod mod_cancel (irΣ ⋅ initial_resource_own_admin))
      (HMod.to_mod mod_tgt target_resource).
  Proof.
    move: (cancel_tgt)=>H; rewrite /refines in H; des; ss.
    hexploit H.
    { rewrite /mod_tgt /KnotMainI.t /KnotI.t /MemI.t /APCI.t. unseal CRIS. prove_nodup. }
    clear H; intros [WF H].
    destruct (H (irΣ ⋅ initial_resource_own_admin)).
    { apply irΣ_valid. }
    { clear H. simplify_res.
      { iClear "H1 U W".
        rewrite /init_cond /KnotA.init_cond /KnotMainA.init_cond /MemA.init_cond.
        rewrite /KnotA.var_points_to /KnotA.knot_full /precond /mem_init_auth /main_fsp /KnotMainA.main_spec /KnotA.knot_init /= /KnotA.knot_frag.
        rewrite /ir_knotRA /knot_init_res /ir_memRA.
        iDestruct "H14" as "[A F]". iFrame. iSplitL; eauto.
        iDestruct "H16" as "[A F]". iFrame.
        rewrite /mem_points_to_singleton.
        assert (mem_init_frag_r csl genv ≡ mem_points_to_singleton_r (2, 0%Z) 1 (Vint 0)).
        { rewrite /mem_init_frag_r /mem_points_to_singleton_r /=. f_equiv.
          intros blk ofs. rewrite /mem_init_val. ss. do 3 (destruct blk; hss).
          { rewrite discrete_fun_lookup_singleton. destruct ofs; hss. }
          do 3 (destruct blk; hss).
        }
        rewrite H. iFrame.
      }
      all: solve_res.
    }
    { exists x; des; eauto. }
  (*SLOW*)Qed.
End KnotAll.

(* Print Assumptions KnotAll.behavioral_refinement. *)
