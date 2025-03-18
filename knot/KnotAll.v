Require Import CRIS Cancel.
Require Import MemHeader MemI MemA MemIAproof.
Require Import APCHeader APC APCI APCA APCC APCACproof APCIAproof.
Require Import KnotHeader KnotMainHeader KnotI KnotMainI.
Require Import KnotA KnotMainA.
Require Import KnotIAproof KnotMainIAproof.

Module KnotAll.
  Import inv_instances.
  Local Instance Γ : HRA := ##[invΓ; memΓ; KnotAΓ].
  Local Instance Σ : GRA := ##[invΣ; Γ].
  
  (* universe *)
  Local Definition u: univ_id := 1.
  (* global invariant *)
  Local Definition ginv : iProp Σ := wsim_ginv u ⊤.
  (* mem *)
  Local Definition csl : string → bool := λ _, false.
  (* global environment *)
  Local Definition genv : GEnv.t := KnotGEnv.t ++ KnotMainGEnv.t.

  (* initial resource *)
  Local Definition irΓ : Γ := **[ir_invΓ u; ir_memΓ csl genv; ir_knotAΓ].
  Local Definition irΣ : Σ := **[ir_invΣ u; irΓ].

  Lemma irΣ_valid : ✓ (irΣ ⋅ initial_resource_own_admin).
  Proof.
    solve_ir_valid.
    - apply ir_memRA_valid.
    - apply ir_knotRA_valid.
  Qed.

  (* pure spc *)
  Local Definition spc_rec : string → option fspec := 
    to_spc KnotA.KnotRecSpc.
  Local Definition spc_fun : string → option fspec :=
    to_spc (KnotMainA.MainFunSpc genv spc_rec).
  Local Definition spc_pure : string → option fspec :=
    to_spc (KnotA.KnotRecSpc ++ (KnotMainA.MainFunSpc genv spc_rec)).

  Local Definition smod_src : SMod.t :=
    (KnotMainA.Mod genv spc_rec) ☆ (KnotA.Mod genv spc_rec spc_fun)
    ☆ MemA.Mod ☆ APCC.Mod.
  Local Definition spc : string → option fspec := spc_from smod_src.

  Local Definition mod_cancel : HMod.t := SModCancel.to_hmod smod_src.

  Local Definition mod_src : HMod.t := SMod.to_hmod ginv spc smod_src.

  Local Definition mod_tgt : HMod.t :=
    KnotMainI.t genv ★ KnotI.t genv ★ MemI.t csl genv ★ APCI.t.

  Local Definition main_fsp : fspec := KnotMainA.main_spec.

  Local Lemma genv_wf : GEnv.wf genv.
  Proof. cbn. prove_nodup. Qed.

  Local Definition init_cond : iProp Σ :=
    KnotMainA.init_cond ∗ (KnotA.init_cond genv) ∗ (MemA.init_cond csl genv).

  Lemma cancel_src :
    refines (mod_cancel, (init_cond ∗ main_fsp.(precond) tt tt↑ tt↑)%I)
            ((mod_src, init_cond) : HMod.modc).
  Proof.
    eapply cancellation; try by econs.
    i. iIntros "%POST". iPureIntro.
    des; eauto.
  Qed.

  Ltac prove_spc :=
    rewrite /MemA.spc /APCA.Spc /KnotA.KnotRecSpc /KnotA.KnotSpc /KnotMainA.MainFunSpc /KnotMainA.MainSpc;
    rewrite /spc /spc_pure /spc_fun /spc_rec /smod_src /spc_pure /spc_incl /spc_sub /find_body /pure_specbody /spc_from /option_map;
    rewrite /spc_fun /spc_rec /APCA.Spc /KnotA.KnotRecSpc /KnotA.KnotSpc /KnotMainA.MainFunSpc /KnotMainA.MainSpc;
    try unseal CRIS; try prove_nodup;
    ii; ss; rewrite ->!eq_rel_dec_correct in *; des_ifs; ss; eexists; ss.

  (* Refinement between spec/impl of whole program (linked module) *)
  Lemma src_tgt : refines (mod_src, init_cond) (mod_tgt, emp%I).
  Proof.
    eapply ctxr_refines.
    unfold mod_src, mod_tgt. rewrite !add_interp_comm.

    replace (SMod.to_hmod _ spc (KnotMainA.Mod _ _)) with (KnotMainA.t genv u spc_rec spc); cycle 1.
    { unfold KnotMainA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ spc (KnotA.Mod _ _ _)) with (KnotA.t genv u spc_rec spc_fun spc); cycle 1.
    { unfold KnotA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ spc MemA.Mod) with (MemA.t u spc); cycle 1.
    { unfold MemA.t; unseal CRIS; ss. }
    replace (SMod.to_hmod _ spc APCC.Mod) with (APCC.t u spc); cycle 1.
    { unfold APCC.t; unseal CRIS; ss. }

    rewrite -!hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans. 
    { rewrite !hmod_add_assoc. rewrite -hmod_addc_empty_l. eapply ctxr_cond_frameR.
      eapply APCAC.ctxr.
      { instantiate (1:=spc). prove_spc. }
      { instantiate (1:=spc_pure). prove_spc. }
      { prove_spc; rewrite /KnotMainA.t /KnotA.t /= alist_find_map_snd /o_map; unseal CRIS; ss. }
    }
    rewrite !hmod_add_assoc.
    etrans. { eapply ctxr_comm. }
    etrans.
    { rewrite !hmod_add_assoc hmod_addc_empty_l /init_cond.
      eapply ctxr_cond_frameR.
      eapply KnotMainIA.ctxr; try prove_spc.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }
    eapply ctxr_frameL.
    etrans.
    { rewrite hmod_addc_empty_l.
      eapply ctxr_cond_frameR.
      eapply KnotIA.ctxr; try prove_spc.
      rewrite /genv /incl; ss. i; des; ss; tauto.
    }
    eapply ctxr_frameL. unfold KnotIAproof.KnotIA.MemA.
    rewrite hmod_addc_empty_l.
    rewrite -hmod_addc_empty_r -[(MemI.t csl genv ★ _, emp%I)]hmod_addc_empty_r.
    eapply ctxr_compose_hor.
    { eapply MemIA.ctxr; prove_spc. }
    { eapply APCIA.ctxr; prove_spc. }
  Qed.

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
        iDestruct "H12" as "[A F]". iFrame. iSplitL; eauto.
        iDestruct "H14" as "[A F]". iFrame.
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
  Qed.
End KnotAll.

(* Print Assumptions KnotAll.behavioral_refinement. *)
