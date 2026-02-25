Require Import CRIS ImpPrelude MemTactics.
Require Export MemA MapI MapM.

(* Auxiliary lemmas *)
Definition fun_to_list (f : Z → Z) (sz : nat) : list val :=
  List.map (λ i : nat, Vint (f i)) (seq 0 sz).

Lemma fun_to_list_replicate (n : nat) : fun_to_list (λ _, 0%Z) n = replicate n (Vint 0).
Proof.
  rewrite /fun_to_list.
  induction n; eauto.
  replace (S n) with (n+1) by nia.
  rewrite seq_app /= map_app /= IHn replicate_add //.
Qed.

Lemma fun_to_list_lookup (f : Z → Z) (sz : nat) (i : nat) (LT : i < sz) :
  fun_to_list f sz !! i = Some (Vint (f i)).
Proof. rewrite /fun_to_list list_lookup_fmap lookup_seq_lt; try nia; eauto. Qed.

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
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MEM: !memGS}.
  Import MapM.

  Definition Ist : ist_type Σ :=
    (λ st_src st_tgt,
      ⌜st_src = {[MapM.v_size # 0%Z↑; MapM.v_map # (λ _ : Z, 0%Z)↑]}
        ∧ st_tgt = {[MapI.v_hptr # Vnullptr↑]}⌝
      ∨ pending
        ∗ ∃ bofs (f : Z → Z) (sz : Z),
          ⌜st_src = {[MapM.v_size # sz↑; MapM.v_map # f↑]}
            ∧ st_tgt = {[MapI.v_hptr # (Vptr bofs)↑]}⌝
          ∗ bofs |-> (fun_to_list f (Z.to_nat sz)))%I.

  (* sps of src/mem modules *)
  Context (sp_s sp_mem : specmap).
  Context (MapInSp : MapM.sp ⊆ sp_s).

  Local Notation MemA := (MemA.t sp_mem).
  Local Notation MapM := (MapM.t sp_s).
  Local Notation MapMMod := (MapM ★ MemA).
  Local Notation MapIMod := (MapI.t ★ MemA).
  Local Notation IstFull := (IstProd (IstSB MapM.(Mod.scopes) Ist) IstEq).

  Lemma simF_init : ISim.sim_fun open MapMMod MapIMod IstFull (fid MapHdr.init).
  Proof using MapInSp.
    iStartSim. rewrite /MapI.init /init.

    (* preprocess given assumptions *)
    steps_l. rename _q into sz.
    iDestruct "ASM" as "[-> [[-> %] P]]".

    (* SRC: handle the IST of Map and the precond of init *)
    iDestruct "IST" as (????) "([-> ->] & (% & [[-> ->] | (P' & IST)]) & %)";
      [|iDestruct "IST" as (????) "M"]; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    subst. steps_l.

    (* SRC: prove the postcond of init *)
    force_l (Vundef ↑).
    force_l; iSplitL ""; first done. steps_l.

    (* TGT : inline alloc *)
    steps_r. inline_r.

    (* TGT: prove the precond of alloc *)
    force_r sz. force_r ([Vint sz] ↑).
    force_r; iSplit; first done.

    (* TGT: handle the postcond of alloc *)
    steps_r. iDestruct "GRT" as "[-> [%b [-> PTS]]]". steps_r.

    (* prepare and start an induction *)
    replace (replicate sz Vundef) with (replicate (sz - sz) (Vint 0) ++ replicate sz Vundef); cycle 1.
    { rewrite Nat.sub_diag. eauto. }
    rewrite // -[X in iterC _ X](Z.sub_diag (sz%Z)).
    iStopProof. cut (sz <= sz); [|lia].
    (* iInduction sz as [|sz]. *)
    generalize sz at 1 4 5 12. intros n.
    iInduction n as [|n]; iIntros "% [PD PTS]".

    (* Base case *)
    { (* TGT : unwind the loop *)
      unfold_iterC_r. case_decide; try nia. steps_r.

      (* prove the IST of Map *)
      step. repeat (iSplit; eauto).
      iExists _, _, _, _.
      repeat iSplit; eauto.
      iRight. iFrame. iExists _, _, _. iSplitR; eauto.
      rewrite app_nil_r Nat.sub_0_r fun_to_list_replicate Nat2Z.id //=.
    }

    (* Inductive case *)
    (* TGT : unwind the loop *)
    unfold_iterC_r. case_match; try nia.
    (* TGT : compute the input to store *)
    unfold scale_int at 2. case_match; cycle 1.
    { exfalso. eapply n0. eapply Z.divide_factor_r. }
    s. steps_r.

    iPoseProof (big_sepL_insert_acc with "PTS") as "(PT & CTN)".
    { instantiate (2:= (sz - (S n))). rewrite lookup_app_r length_replicate // Nat.sub_diag //=. }
      
    (* TGT : inline store *)
    rewrite ?Z.add_0_l Z.div_mul // Nat2Z.inj_sub //.
    store_r "PT".

    (* TGT: handle the postcond of store *)
    iSpecialize ("CTN" $! (Vint 0)). iPoseProof ("CTN" with "PT") as "PTS".
    (* rewrite -> !Zpos_P_of_succ_nat, <-!Nat2Z.inj_succ. *)
    replace (sz - S n + 1)%Z with (sz - n)%Z by nia.

    (* apply the induction hypothesis and complete *)
    iApply "IHn"; first (iPureIntro; nia). iFrame.
    rewrite insert_app_r_alt length_replicate // Nat.sub_diag.
    eapply eq_ind; [iClear "IHn"; iAssumption |]. s.
    replace (sz - n) with (S (sz - S n)); last lia.
    rewrite replicate_S_end; f_equal. rewrite -app_assoc //=.
  (*SLOW*)Qed.

  Lemma simF_get : ISim.sim_fun open MapMMod MapIMod IstFull (fid MapHdr.get).
  Proof using MapInSp.
    iStartSim. rewrite /MapI.get /get.

    (* SRC: handle the IST of Map and the precond of get *)
    steps_l. rename _q into idx. iDestruct "ASM" as "[-> ->]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & (% & [[-> ->] | (P & IST)]) & %)";
      [|iDestruct "IST" as (? ? ?) "([-> ->] & M)"].
    { steps_l. rewrite /assume. steps_l. nia. }
    steps_l. rewrite /assume. steps_l.
    destruct bofs as [blk ofs].
    
    (* SRC: prove the postcond of get *)
    force_l. force_l. iSplitL "". { eauto. }

    (* TGT : compute the input to load *)
    steps_r.
    unfold scale_int. case_match; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    steps_r. rewrite Z_div_mult; try nia.

    (* TGT : inline load *)
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). nia. }
    rewrite Z2Nat.id; try nia.
    load_r "IP".

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    iExists _, _, _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _. iSplit; eauto.
    iPoseProof ("M" with "IP") as "M". iFrame.
  (*SLOW*)Qed.

  Lemma simF_set : ISim.sim_fun open MapMMod MapIMod IstFull (fid MapHdr.set).
  Proof using MapInSp.
    iStartSim. rewrite /MapI.set /set.

    steps_l. destruct _q as [idx v]. iDestruct "ASM" as "[-> ->]". steps_l.

    (* SRC: handle the IST of Map and the precond of set *)
    iDestruct "IST" as (? ? ? ?) "(%& (% & [%|(P & IST)]) &%)";
      [|iDestruct "IST" as (? ? ?) "(% & M)"];
      des; subst.
    { steps_l. rewrite /assume; steps_l. nia. }
    destruct bofs as [blk ofs].
    steps_l. rewrite /assume. steps_l.

    (* TGT : compute the input to store *)
    steps_r. unfold scale_int. case_match; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    rewrite Z_div_mult; try nia.
    s. steps_r.

    (* TGT : inline load *)
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat idx). hss. nia. }
    rewrite Z2Nat.id; try nia.
    store_r "IP".

    (* SRC: prove the postcond of set *)
    force_l. force_l. iSplitL "". { eauto. }

    (* prove the IST of Map *)
    step. repeat (iSplit; eauto).
    iExists _, _, _, _.
    do 3 (iSplit; eauto).
    iRight. iFrame. iExists _, _, _. iSplit; eauto.
    iPoseProof ("M" with "IP") as "M".
    rewrite -> fun_to_list_update, Z2Nat.id; try nia. iFrame.
  (*SLOW*)Qed.

  Lemma simF_set_by_user : ISim.sim_fun open MapMMod MapIMod IstFull (fid MapHdr.set_by_user).
  Proof using MapInSp.
    iStartSim. rewrite /MapI.set_by_user /set_by_user.

    steps_l. rename _q into idx. iDestruct "ASM" as "[-> ->]". steps_l.

    (* process an input *)
    steps_r. step.
    
    (* SRC: prove the precond of set *)
    steps_l. simpl_sp. force_l (_,_); s. force_l. force_l. iSplit; first eauto.

    (* make a call to set *)
    steps_r. call "IST". clear_st. iIntros (ret2 st_src st_tgt) "IST".

    (* SRC: handle the postcond of set *)
    steps_l. iDestruct "ASM" as "(-> & _)". steps_r.
    destruct Any.downcast; steps_l; ss.

    (* SRC: prove the postcond of set_by_user *)
    force_l. force_l. iSplit; eauto.

    (* prove the IST of Map *)
    step. iFrame. done.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MapMMod MapIMod emp%I IstFull.
  Proof using MapInSp.
    init_sim.
    { eapply simF_init; eauto. }
    { eapply simF_get; eauto. }
    { eapply simF_set; eauto. }
    { eapply simF_set_by_user; eauto. }
    { iIntros "_". repeat iExists _; repeat iSplit; eauto. iLeft. eauto. }
  Qed.
End MapIM.

Section MapIM.
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS, _MEM: !memGS}.

  Lemma ctxr (sp_s sp_mem : specmap) :
    MapM.sp ⊆ sp_s →
    ctx_refines
      (MapM.t sp_s ★ MemA.t sp_mem, emp%I)
      (MapI.t      ★ MemA.t sp_mem, emp%I).
  Proof. i; eapply main_adequacy, MapIM.sim; eauto. Qed.
End MapIM. End MapIM.
