Require Import CRIS.

Require Import MemA.
From CRIS.map Require Import Header MapI MapM.

Set Implicit Arguments.

Local Open Scope nat_scope.

(* Auxiliary lemmas *)
Definition fun_to_list (f : Z → Z) (sz : nat) : list val :=
  List.map (λ i : nat, Vint (f i)) (seq 0 sz).

Lemma fun_to_list_repeat (n : nat) : fun_to_list (λ _, 0%Z) n = repeat (Vint 0) n.
Proof.
  rewrite /fun_to_list.
  induction n; eauto.
  replace (S n) with (n+1) by nia.
  rewrite seq_app /= map_app /= IHn repeat_app; ss.
Qed.

Lemma fun_to_list_lookup (f : Z → Z) (sz : nat) (i : nat) (LT : i < sz) :
  fun_to_list f sz !! i = Some (Vint (f i)).
Proof.
  rewrite /fun_to_list list_lookup_fmap lookup_seq_lt; try nia; eauto.
Qed.

Lemma fun_to_list_update (f : Z → Z) (sz : nat) (i : nat) (v : Z) :
  <[i := Vint v]> (fun_to_list f sz) = fun_to_list (<[Z.of_nat i := v]> f) sz.
Proof.
  unfold fun_to_list. revert i. induction sz; i; eauto.
  replace (S sz) with (sz + 1) by nia.
  rewrite !seq_app !map_app.
  assert (CASE : i < sz \/ i >= sz) by nia.
  des.
  - rewrite insert_app_l; cycle 1.
    { rewrite length_map length_seq. nia. }
    rewrite IHsz. s. do 3 f_equal.
    rewrite fn_lookup_insert_ne; eauto. nia.
  - assert (Iadd : List.length (List.map (λ i0 : nat, Vint (f i0)) (seq 0 sz)) + (i - sz) = i).
    { rewrite length_map length_seq. nia. }
    s. rewrite -IHsz -{1 2}Iadd -{4}(app_nil_r (seq 0 sz)) map_app. 
    rewrite !insert_app_r -app_assoc. f_equal. s.
    assert (CASE' : i = sz \/ i > sz) by nia.
    des; subst.
    + rewrite fn_lookup_insert Nat.sub_diag. eauto.
    + rewrite fn_lookup_insert_ne; try nia.
      destruct (i-sz) eqn : EQ; try nia. eauto.
Qed.

Lemma repeat_update {A} i n (v v' w : A):
  <[i:=v]> (repeat v i ++ v' :: repeat w n) = repeat v (i+1) ++ repeat w n.
Proof.
  replace i with (List.length (repeat v i) + 0) at 1; cycle 1.
  { rewrite repeat_length. nia. }
  rewrite ->insert_app_r, repeat_app, <-app_assoc. eauto.
Qed.

(* Simulation proof *)
Module MapIM. Section MapIM.
  Import MapMS.
  Context `{!crisG Γ Σ α β τ _S _I, !mapMG, !memG}.

  Definition Ist : nat → alist key Any.t → alist key Any.t → iProp Σ :=
    (λ _ st_src st_tgt,
      ⌜st_src = [(MapM.v_size, 0%Z↑); (MapM.v_map, (λ _ : Z, 0%Z)↑)]
        ∧ st_tgt = [(MapI.v_hptr, Vnullptr↑)]⌝
      ∨ pending
        ∗ ∃ bofs (f : Z → Z) (sz : Z),
          ⌜st_src = [(MapM.v_size,sz↑);(MapM.v_map,f↑)]
            ∧ st_tgt = [(MapI.v_hptr,(Vptr bofs)↑)]⌝
          ∗ bofs |-> (fun_to_list f (Z.to_nat sz)))%I.

  (* sps of src/mem modules *)
  Context (sp_s : sp_type).
  Context (MapInSp : sp_incl MapMS.sp sp_s).

  Local Definition MemA := (MemA.t).
  Local Definition MapM := (MapM.t sp_s).
  Local Definition MapMMod := (MapM ★ MemA).
  Local Definition MapIMod := (MapI.t ★ MemA).
  Local Definition IstFull := (IstProd (IstSB MapM.(Mod.scopes) Ist) IstEq).

  Lemma simF_init : ISim.sim_fun open MapMMod MapIMod MapM.init_cond IstFull (Some MapHdr.init).
  Proof using MapInSp.
    init_simF.

    (* preprocess given assumptions *)
    steps_l.
    iDestruct "ASM" as "[[[-> %] P] ->]". hss.

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (????) "([-> ->] & (% & [% | (P' & IST)]) & %)";
      [|iDestruct "IST" as (????) "M"];
      hss; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    rename _q into sz.

    (* SRC: prove the postcond of init *)
    force_l (Vundef ↑).
    force_l; iSplitL ""; first done. steps_l.

    (* TGT : inline alloc *)
    steps_r. inline_r.

    (* TGT: prove the precond of alloc *)
    steps_r. force_r sz. force_r ([Vint sz] ↑).
    force_r; iSplit; first done.

    (* TGT: handle the postcond of alloc *)
    steps_r. iDestruct "GRT" as "[[%b [-> PTS]] ->]".
    hss. steps_r. hss.

    (* prepare and start an induction *)
    replace (repeat Vundef sz) with (repeat (Vint 0) (sz-sz) ++ repeat Vundef sz); cycle 1.
    { rewrite Nat.sub_diag. eauto. }
    rewrite // -[X in iterC _ X](Z.sub_diag (sz%Z)).
    iStopProof. cut (sz <= sz); [|lia].
    generalize sz at 1 4 5 10. intros n'.
    induction n'; i; iIntros "(PD & PTS)".

    (* Base case *)
    { (* TGT : unwind the loop *)
      unfold_iter_r. des_ifs; try nia. steps_r.

      (* prove the IST of Map *)
      step. repeat (iSplit; eauto).
      iExists [_;_], [_], _, _.
      repeat iSplit; eauto.
      iRight. iFrame. iExists _, _, _. iSplitR; eauto. inv G0.
      rewrite app_nil_r Nat.sub_0_r fun_to_list_repeat Nat2Z.id //=.
    }

    (* Inductive case *)
    { (* TGT : unwind the loop *)
      unfold_iter_r. des_ifs; try nia.
      (* TGT : compute the input to store *)
      unfold scale_int at 1. des_ifs; cycle 1.
      { exfalso. eapply n. eapply Z.divide_factor_r. }
      s. steps_r.
      
      (* TGT : inline store *)
      inline_r. steps_r.

      (* TGT: prove the precond of store *)
      force_r (_, (sz - S n')%Z, _, _).
      force_r ([Vptr (_, (sz - (S n'))%Z); _]↑).
      force_r.
      iPoseProof (big_sepL_insert_acc with "PTS") as "(PT & CTN)".
      { instantiate (2:= (sz - (S n'))).
        rewrite lookup_app_r; rewrite repeat_length; try nia.
        rewrite Nat.sub_diag. s. eauto.
      }
      rewrite !Z.add_0_l Nat2Z.inj_sub; try nia.
      (* , Zpos_P_of_succ_nat, <-Nat2Z.inj_succ, Nat2Z.inj_sub; try nia. *)
      iSplitL "PT".
      { iSplitL; cycle 1.
        { iPureIntro. do 3 f_equal. rewrite Z.div_mul; eauto. }
        iSplit; et. rewrite Z.div_mul; eauto.
      }

      (* TGT: handle the postcond of store *)
      steps_r. iDestruct "GRT" as "[[GRT ->] ->]". hss.
      iSpecialize ("CTN" $! (Vint 0)). iPoseProof ("CTN" with "GRT") as "PTS".
      (* rewrite -> !Zpos_P_of_succ_nat, <-!Nat2Z.inj_succ. *)
      replace (sz - S n' + 1)%Z with (sz - n')%Z by nia.

      (* apply the induction hypothesis and complete *)
      steps_r.
      iApply IHn'; try nia. iFrame.
      rewrite repeat_update.
      eapply eq_ind; [iAssumption |].
      do 3 f_equal. nia.
    }
  (*SLOW*)Admitted.

  Lemma simF_get : ISim.sim_fun open MapMMod MapIMod MapM.init_cond IstFull (Some MapHdr.get).
  Proof using MapInSp.
    init_simF.

    (* SRC: handle the IST of Map and the precond of get *)
    steps_l.
    iDestruct "ASM" as "[-> ->]". hss.
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";
      [|iDestruct "IST" as (? ? ?) "(% & M)"];
      des; hss.
    { nia. }
    destruct bofs as [blk ofs]. inv G0.
    rename _q2 into idx.
    
    (* SRC: prove the postcond of get *)
    force_l. force_l. iSplitL "". { eauto. }

    (* TGT : compute the input to load *)
    steps_r. hss. steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    s. steps_r. rewrite Z_div_mult; try nia.

    (* TGT : inline load *)
    inline_r.

    (* TGT: prove the precond of load *)
    step_r. force_r (_, (ofs + _)%Z, 1%Qp, _). force_r. force_r.
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    
    (* TGT: handle the postcond of load *)
    steps_r. iDestruct "GRT" as "[[GRT ->] ->]". hss. steps_r.

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    iExists [_;_], [_], _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _. iSplit; eauto.
    iPoseProof ("M" with "GRT") as "M". iFrame.
  (*SLOW*)Admitted.

  Lemma simF_set : ISim.sim_fun open MapMMod MapIMod MapM.init_cond IstFull (Some MapHdr.set).
  Proof using MapInSp.
    init_simF.

    steps_l.
    iDestruct "ASM" as "[-> ->]". hss. inv G0. steps_l.

    (* SRC: handle the IST of Map and the precond of set *)
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";
      [|iDestruct "IST" as (? ? ?) "(% & M)"];
      des; hss.
    { nia. }
    destruct bofs as [blk ofs].
    rename _q1 into idx.

    (* TGT : compute the input to store *)
    steps_r. hss. steps_r.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    rewrite Z_div_mult; try nia.
    s. steps_r.

    (* TGT : inline load *)
    inline_r.

    (* TGT: prove the precond of store *)
    step_r. force_r (blk, (ofs + idx)%Z, _, _). force_r. force_r.
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). hss. nia. }
    rewrite Z2Nat.id; try nia.
    iSplitL "IP". { eauto. }

    (* TGT: handle the postcond of load *)
    steps_r. iDestruct "GRT" as "[[GRT ->] ->]". hss. steps_r.

    (* SRC: prove the postcond of set *)
    force_l. force_l. iSplitL "". { eauto. }

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    iExists [_;_], [_], _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _. iSplit; eauto.
    iPoseProof ("M" with "GRT") as "M".
    rewrite -> fun_to_list_update, Z2Nat.id; try nia. iFrame.
  (*SLOW*)Admitted.

  Lemma simF_set_by_user : ISim.sim_fun open MapMMod MapIMod MapM.init_cond IstFull (Some MapHdr.set_by_user).
  Proof using MapInSp.
    init_simF.

    steps_l.
    iDestruct "ASM" as "[-> ->]".
    hss. inv G0. rename _q2 into k.

    (* SRC: handle the IST of Map and the precond of set_by_user *)

    (* process an input *)
    steps_r. step.
    
    (* SRC: prove the precond of set *)
    steps_l. force_l (_,_); s. force_l. force_l.
    iSplitL "". { eauto. }

    (* make a call to set *)
    steps_r. call "IST".

    (* SRC: handle the postcond of set *)
    steps_l. iDestruct "ASM" as "(_ & ->)". hss.

    (* SRC: prove the postcond of set_by_user *)
    force_l. force_l. iSplitL "". { eauto. }

    (* prove the IST of Map *)
    steps_r. hss. steps_r. step. eauto.
  (*SLOW*)Admitted.

  Lemma sim : ISim.t open MapMMod MapIMod MapM.init_cond IstFull.
  Proof using MapInSp.
    init_sim.
    - split; eauto. iIntros "_". iSplit.
      iSplit; eauto.
      + iPureIntro. prove_scope.
      + iLeft. eauto.
    - eapply simF_init; eauto.
    - eapply simF_get; eauto.
    - eapply simF_set; eauto.
    - eapply simF_set_by_user; eauto.
  Qed.
End MapIM.

Section MapIM.
  Context `{!crisG Γ Σ α β τ _S _I, !mapMG, !memG}.

  Lemma ctxr (sp_s : sp_type) :
    sp_incl MapMS.sp sp_s →
    ctx_refines
      (MapM.t sp_s ★ MemA.t, MapM.init_cond)
      (MapI.t      ★ MemA.t, emp%I).
  Proof. i; eapply main_adequacy, MapIM.sim; eauto. Qed.
End MapIM. End MapIM.
