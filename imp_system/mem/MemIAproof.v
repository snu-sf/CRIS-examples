From CRIS Require Import CRIS MemHeader MemA MemI ImpPrelude CallFilter.
From iris.algebra Require Import auth excl agree csum functions dfrac_agree.

Section RA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.

  Definition mem_wf (m : Mem.t) : Prop := ∀ b ofs v, m.(Mem.cnts) b ofs = Some v → b < m.(Mem.nb).

  Definition sim_mem (mem_s : MemA._memRA) (mem_t : Mem.t) : Prop :=
    ∀ b ofs,
      (mem_s b ofs = None ∧ Mem.cnts mem_t b ofs = None) ∨
      (∃ v, mem_s b ofs = Some (to_dfrac_agree (DfracOwn 1) v) ∧
        Mem.cnts mem_t b ofs = Some v).

  Definition mem_ra_upd (mem : MemA._memRA) b ofs r : MemA._memRA :=
    λ b0 ofs0, if bool_decide (b = b0 ∧ ofs = ofs0) then r else mem b0 ofs0.

  Lemma split_points_to_r blk ofs q a l :
    _points_to_r (blk, ofs) q (a :: l)
    ≡ (_points_to_r (blk, ofs) q [a]) ⋅ (_points_to_r (blk, (ofs + 1)%Z) q l).
  Proof using.
    intros b o. rewrite !discrete_fun_lookup_op /=.
    repeat case_bool_decide; des; simplify_eq; try nia; ss.
    { destruct (decide (o = ofs)); subst; [|nia]; rewrite ?Z.sub_diag //=. }
    { rewrite left_id. replace (o - (ofs + 1))%Z with (o - ofs - 1)%Z by nia.
      replace (Z.to_nat (o - ofs)) with (S (Z.to_nat (o - ofs - 1))) by nia.
      ss.
    }
  Qed.

  Lemma points_to_singleton blk ofs q a :
    _points_to_r (blk, ofs) q [a]
    ≡ (discrete_fun_singleton blk (discrete_fun_singleton ofs (Some (to_dfrac_agree q a)))).
  Proof using.
    intros b o; ss.
    ss; case_bool_decide as H'; des; simplify_eq; ss.
    { destruct (decide (o = ofs)); subst; try nia.
      rewrite Z.sub_diag /= ?discrete_fun_lookup_singleton //.
    }
    apply not_and_or in H'; des; try by rewrite discrete_fun_lookup_singleton_ne //.
    destruct (decide (b = blk)); subst;
      [rewrite discrete_fun_lookup_singleton discrete_fun_lookup_singleton_ne //; ii; clarify; nia
      |rewrite discrete_fun_lookup_singleton_ne //].
  Qed.

  Local Transparent mem_points_to_singleton_r.
  Local Existing Instances memGS_memGSpreS mem_inG.
  Lemma points_to_transform blk ofs q l :
    own mem_name ((◯ _points_to_r (blk, ofs) (DfracOwn q) l): MemA.memRA)
    ⊢ [∗ list] i↦v ∈ l, (blk, (ofs + i)%Z) ↦{q} v.
  Proof using.
    gen ofs. induction l.
    - iIntros; eauto.
    - i. rewrite split_points_to_r. iIntros "[P L]".
      rewrite big_sepL_cons. rewrite points_to_singleton.
      iPoseProof (IHl with "L") as "L".
      set (λ _ _, _). set (λ _ _, _).
      assert (Heq : y = y0).
      { extensionality a1; extensionality a2. subst y y0. ss.
        replace (ofs + 1 + a1)%Z with (ofs + S a1)%Z by nia. refl.
      }
      rewrite Heq. iFrame. unfold mem_points_to_singleton, mem_points_to_singleton_r; ss.
      rewrite Z.add_0_r. iFrame.
  Qed.

  Lemma to_frac_agree_inv A q (v: leibnizO A) f
    (EQ: to_dfrac_agree q v ≡ f)
    :
    f.1 = q ∧ ∃ tl, f.2.(agree_car) = v :: tl.
  Proof using.
    rr in EQ. des; ss. ltac2:(renames EQ into EQqf, EQvf). rewrite EQqf; split; et.
    specialize (EQvf 0). rr in EQvf. des; ss. ltac2:(renames EQvf into EQvf, EQfv).
    edestruct EQvf as [b [INbf EQvb]]; s; eauto using elem_of_list.
    destruct (agree_car f.2) eqn: EQf.
    - rewrite EQf in INbf. inv INbf.
    - exists l. f_equal. rr in EQvb. depdes EQvb. rewrite EQf in EQfv.
      edestruct (EQfv o) as [a [INav EQao]]; eauto using elem_of_list.
      rr in EQao. depdes EQao. set_solver.
  Qed.

  Lemma to_frac_full_valid_inv A c (v: leibnizO A)
    (VALID: ✓ (Some (to_dfrac_agree (DfracOwn 1) v) ⋅ c))
    :
    c = None.
  Proof using.
    destruct c; et. rewrite -?Some_op in VALID.
    rr in VALID. des. ss. exfalso. eapply dfrac_full_exclusive; et.
  Qed.

  Lemma mem_ra_alloc γ (mem_src : MemA._memRA) mem_tgt blk sz pad
    (SIM: sim_mem mem_src mem_tgt)
    (BLK: blk = Mem.nb mem_tgt + pad)
    (WF: mem_wf mem_tgt)
    :
    own γ ((● mem_src): MemA.memRA)
    ⊢ |==>
    own γ ((● (mem_src ⋅ _points_to_r (blk, 0%Z) (DfracOwn 1) (replicate sz Vundef))): MemA.memRA)
    ∗ own γ ((◯ _points_to_r (blk, 0%Z) (DfracOwn 1) (replicate sz Vundef)): MemA.memRA).
  Proof using.
    iIntros "P". rewrite -own_op.
    iApply (own_update with "P"). apply auth_update_alloc.
    apply local_update_discrete. intros mz Hwf Hwf2; rewrite Hwf2.
    split; cycle 1.
    - destruct mz; simpl opM in *.
      + rewrite left_id (comm _ c). et.
      + rewrite left_id. et.
    - rewrite -Hwf2. ii. rewrite !discrete_fun_lookup_op /_points_to_r.
      case_bool_decide as Hcase; s; cycle 1.
      { rewrite right_id. apply Hwf. }
      hexploit (SIM blk x0). destruct Hcase as [-> Hcase].
      intros [[-> Ha1]|Ha2]; clarify.
      + case_match; ss.
      + des; exploit WF; eauto. by nia.
  Qed.

  Lemma mem_ra_lookup (mem_s: MemA._memRA) mem_t b ofs q v
    (SIM: sim_mem mem_s mem_t)
    :
    own mem_name (● mem_s) ∗ (b, ofs) ↦{q} v
    ⊢
    ⌜mem_s b ofs ≡ Some (to_dfrac_agree (DfracOwn 1%Qp) v) ∧
     Mem.cnts mem_t b ofs = Some v⌝.
  Proof using.
    iIntros "P". rewrite -own_op.
    iPoseProof (own_valid with "P") as "%WF"; iPureIntro.
    pose proof WF as WF1; rewrite auth_both_valid_discrete in WF1; ss.
    destruct WF1 as [Hincl Hwf]; apply (discrete_fun_included_spec_1 _ _ b) in Hincl.
    apply (discrete_fun_included_spec_1 _ _ ofs) in Hincl.
    rewrite !discrete_fun_lookup_singleton in Hincl.
    destruct (SIM b ofs) as [[Heq Hsim]|[v0 [Heq Hsim]]].
    { rewrite Heq in Hincl; apply Some_included_is_Some in Hincl; inv Hincl. }
    rewrite Heq Some_included in Hincl.
    destruct Hincl as [Hincl|Hincl].
    { apply to_dfrac_agree_inj in Hincl as [Hincl1 Hincl2]; inv Hincl1.
      rewrite Heq Hsim; splits; done.
    }
    apply dfrac_agree_included in Hincl; inv Hincl; rewrite Heq Hsim; splits; done.
  Qed.

  Lemma mem_ra_update v_new v (mem_s: MemA._memRA) mem_t b ofs :
    sim_mem mem_s mem_t →
    own mem_name (● mem_s) ∗ (b, ofs) ↦{1} v ⊢
    |==> own mem_name (● mem_ra_upd mem_s b ofs (Some (to_dfrac_agree (DfracOwn 1) v_new))) ∗
      (b, ofs) ↦{1} v_new.
  Proof using.
    iIntros "%SIM [Auth Frag]".
    iPoseProof ((mem_ra_lookup _ _ _ _ _ _ SIM) with "[Auth Frag]") as "[%H' %_]"; iFrame.
    rewrite -own_op.
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r /= auth_update //; apply discrete_fun_local_update.
    intros b2; apply discrete_fun_local_update; intros o2.
    destruct (decide (b2 = b)); subst.
    { destruct (decide (o2 = ofs)); subst.
      { rewrite H' ?discrete_fun_lookup_singleton /mem_ra_upd; case_bool_decide; [|naive_solver].
        apply option_local_update, exclusive_local_update; ss.
      }
      rewrite ?discrete_fun_lookup_singleton /mem_ra_upd; case_bool_decide; [naive_solver|].
      rewrite ?discrete_fun_lookup_singleton_ne //.
    }
    rewrite ?discrete_fun_lookup_singleton_ne /mem_ra_upd //.
    case_bool_decide; [naive_solver|]; ss.
  Qed.

  Lemma mem_ra_free (mem_s : MemA._memRA) mem_t b ofs v :
    sim_mem mem_s mem_t →
    mem_wf mem_t →
    own mem_name (● mem_s) ∗ (b, ofs) ↦{1} v ⊢
    |==> own mem_name (● mem_ra_upd mem_s b ofs None).
  Proof using.
    iIntros "% % [Auth Frag]".
    iApply (own_update_2 with "Auth Frag").
    rewrite /mem_points_to_singleton_r auth_update_dealloc //=.
    apply discrete_fun_local_update; intros b1; apply discrete_fun_local_update; intros o1.
    destruct (decide (b1 = b)); subst.
    { rewrite discrete_fun_lookup_singleton.
      destruct (decide (o1 = ofs)); subst.
      { rewrite ?discrete_fun_lookup_singleton /mem_ra_upd; case_bool_decide; [|naive_solver].
        apply delete_option_local_update; eauto; apply _.
      }
      rewrite discrete_fun_lookup_singleton_ne // /mem_ra_upd; case_bool_decide; [naive_solver|ss].
    }
    rewrite /mem_ra_upd; case_bool_decide; [naive_solver|].
    rewrite discrete_fun_lookup_singleton_ne; ss; eauto.
  Qed.

  Lemma mem_ra_cmp (mem_s: MemA._memRA) mem_t p0 q0 v0 p1 q1 v1 succ
    (SIM: sim_mem mem_s mem_t)
    (CMP: MemA.compare_val p0 p1 = Vint succ)
    :
    (own mem_name (● mem_s) ∗ MemA.val_r p0 q0 v0 ∗ MemA.val_r p1 q1 v1)
    ⊢
    ⌜Mem.vcmp mem_t p0 p1 = Some (bool_decide (succ = 1))⌝.
  Proof using.
    iIntros "(B & P1 & P2)".
    destruct p0, p1; try destruct blkofs; try destruct blkofs0; ss.
    - des_ifs.
    - iPoseProof (mem_ra_lookup with "[B P2]") as "%Hlu"; et; iFrame.
      specialize (SIM n0 z). des; subst; ss.
      + rewrite SIM in Hlu. r in Hlu. depdes Hlu.
      + rewrite SIM0. iPureIntro. des_ifs.
    - destruct n; ss.
    - iPoseProof (mem_ra_lookup with "[B P1]") as "%Hlu"; et; iFrame.
      specialize (SIM n0 z). des; subst; ss.
      + rewrite SIM in Hlu. rr in Hlu. depdes Hlu.
      + rewrite SIM0. iPureIntro. des_ifs.
    - iPoseProof (mem_ra_lookup with "[B P1]") as "%Hlu1"; et; iFrame.
      iPoseProof (mem_ra_lookup with "[B P2]") as "%Hlu2"; et; iFrame.
      dup SIM. specialize (SIM n z). des; subst; ss.
      { rewrite SIM in Hlu1. rr in Hlu1. depdes Hlu1. }
      specialize (SIM0 n0 z0). des; subst; ss.
      { rewrite SIM0 in Hlu2. rr in Hlu2. depdes Hlu2. }
      rewrite SIM1 SIM2. s.
      repeat case_bool_decide; ss; des; simplify_eq.
  Qed.
End RA.

Module MemIA. Section MemIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS}.
  Local Existing Instances memGS_memGSpreS mem_inG.

  Context (csl : string → bool).
  Context (genv : GEnv.t).
  Context (sp: specmap).

  Definition Ist : gmap key (option Any.t) → gmap key (option Any.t) → iProp Σ :=
    λ st_src st_tgt,
      ((∃ (mem_tgt : Mem.t) (mem_src : MemA._memRA),
      ⌜st_tgt = {[MemI.v_mem # mem_tgt↑]} ∧ sim_mem mem_src mem_tgt ∧ mem_wf mem_tgt⌝ ∗
      ( |==> own mem_name (● mem_src))))%I.

  Local Definition MemA := (MemA.t sp).
  Local Definition MemI := (MemI.t csl genv).
  Local Definition IstFull := (IstProd (IstSB MemA.(Mod.scopes) Ist) IstEq).

  Definition mem_get (mem: MemA._memRA) b ofs :=
    match or_else (mem b ofs) (to_dfrac_agree (DfracOwn 1) Vundef) with
    | (_,v) => or_else (nth_error v.(agree_car) 0) Vundef
    end.

  Local Definition state : Type := gmap key (option Any.t).
  Local Definition post (R_s R_t : Type) : Type := state * R_s → state * R_t → iProp Σ.

  Local Definition rel : Type := ∀ R_s R_t : Type,
    post R_s R_t → bool → bool → state * itree crisE R_s → state * itree crisE R_t → iProp Σ.

  Lemma simF_alloc : ISim.sim_fun open MemA MemI IstFull (fid MemHdr.alloc).
  Proof using.
    cStartFunSim. rewrite /MemI.alloc. cStepsS.
    rename _q into sz, _q0 into varg.
    iDestruct "ASM" as "[-> [-> %]]".

    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [%Hsim %Hwf]] >B]]]] & ->)".
    cStepsT. case_bool_decide; [|lia]. cStepsT.

    rename _q into pad.
    set (blk := Mem.nb mem_tgt + pad).
    iPoseProof (own_valid with "B") as "%".
    iPoseProof (mem_ra_alloc with "B") as ">B"; et.
    iDestruct "B" as "[BLK WHT]". iPoseProof (points_to_transform with "WHT") as "WHT".

    cForceS ((Vptr (blk, 0%Z)) ↑). cStepsS. cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame.
    repeat (iSplit; first done).
    iExists _, _, _, _; iSplit; [iPureIntro; split; refl|iSplit; eauto].
    repeat (iSplit; eauto).
    iExists _; iSplit; eauto.
    iPureIntro; esplits; eauto; cycle 1.
    { intros ??? Hwf2; ss.
      rewrite /update in Hwf2; case_match; subst; ss.
      rewrite /mem_wf in Hwf; exploit Hwf; eauto; nia.
    }

    intros blk' ofs'; rewrite ?discrete_fun_lookup_op /= Z.add_0_l Z.sub_0_r length_replicate.
    destruct (mem_tgt.(Mem.cnts) blk ofs') eqn:E.
    { exfalso. exploit Hwf; et. nia. }
    ss. hexploit (Hsim blk ofs'); et.
    rewrite E. intro U. des; ss.

    case_bool_decide as Hblkofs; [destruct Hblkofs as [Hblk Hofs]|].
    { rewrite lookup_replicate_2; [subst|lia]; rewrite U left_id; right; esplits; eauto.
      rewrite /update; destruct (dec _ _); ss; case_bool_decide; ss.
    }
    rewrite right_id /update; destruct (_ blk' ofs') eqn : ?; hexploit (Hsim blk' ofs');
        i; des; destruct (dec _ _); ss; try case_bool_decide; naive_solver.
  (*SLOW*)Qed.

  Lemma simF_free : ISim.sim_fun open MemA MemI IstFull (fid MemHdr.free).
  Proof using.
    cStartFunSim. rewrite /MemI.free.
    cStepS. destruct _q as [[blk ofs] v].
    cStepS. rename _q into varg. cStepS.
    iDestruct "ASM" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [%Hsim %Hwf]] >B]]]] & ->)".

    cStepsS. cStepsT.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT ->]"; et; iFrame. cStepsT.

    cForceS. iMod (mem_ra_free with "[B ↦]") as "H"; et; iFrame.
    cForcesS; iSplit; eauto.
    cStep; iFrame. repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
    iExists _; iSplit; eauto.
    iPureIntro. esplits; eauto.
    - ii. s. rewrite /mem_ra_upd /update.
      repeat destruct dec; case_bool_decide; des; ss; subst; naive_solver.
    - rewrite /update. ii. ss. repeat destruct dec; ss; subst; et.
  (*SLOW*)Qed.

  Lemma simF_load : ISim.sim_fun open MemA MemI IstFull (fid MemHdr.load).
  Proof using.
    cStartFunSim. rewrite /MemI.load.
    cStepS. destruct _q as [[[blk ofs] q] v]. cStepsS.

    iDestruct "ASM" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [%Hsim %Hwf]] >B]]]] & ->)".

    cStepsT.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT ->]"; et; iFrame. cStepsT.
    cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame. repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
  (*SLOW*)Qed.

  Lemma simF_store : ISim.sim_fun open MemA MemI IstFull (fid MemHdr.store).
  Proof using.
    cStartFunSim. rewrite /MemI.store.
    cStepS. destruct _q as [[[blk ofs] q] v]. cStepsS.

    iDestruct "ASM" as "[-> [-> ↦]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> [%Hsim %Hwf]] >B]]]] & ->)".

    cStepsS. cStepsT.

    iPoseProof (mem_ra_lookup with "[B ↦]") as "[%HIT %HIT2]"; et; iFrame; rewrite HIT2. cStepsT.
    iMod (mem_ra_update with "[B ↦]") as "[B ↦]"; et; iFrame.

    cForcesS. iFrame. iSplit; eauto.
    cStep. iFrame. repeat (iSplit; et).
    iExists _, _, _, _; repeat (iSplit; et).
    iExists _; iSplit; et.
    iPureIntro. split; eauto. split.
    - ii. s. rewrite /mem_ra_upd /update.
      repeat destruct dec; ss; subst; case_bool_decide; des; naive_solver.
    - ii; ss; repeat destruct dec; ss; subst; eauto.
  (*SLOW*)Qed.

  Lemma simF_cmp : ISim.sim_fun open MemA MemI IstFull (fid MemHdr.cmp).
  Proof using.
    cStartFunSim. rewrite /MemI.cmp.
    cStepS. destruct _q as [[[v_old v_new] v_cmp] Cmp]. cStepsS.
    iDestruct "ASM" as "[-> [[-> %Hcmp2] [Cmp Cmp2]]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> %] >B]]]] & ->)"; des.

    cStepsT.

    iMod ("Cmp2" with "Cmp") as (????) "[C1 [C2 C3]]".
    iPoseProof (mem_ra_cmp with "[B C1 C2]") as "->"; eauto; iFrame.
    iMod ("C3" with "[$]").

    cStepsT. cForcesS. iFrame. iSplit; eauto. cStep. iFrame.

    iSplit; [case_bool_decide; clarify; ss|].
    { iPureIntro; move : Hcmp2; rewrite /MemA.compare_val; des_ifs; i; clarify. }
    iExists _, _, _, _; iSplit; eauto.
  (*SLOW*)Qed.

  Lemma simF_cas : ISim.sim_fun open MemA MemI IstFull (fid MemHdr.cas).
  Proof using.
    cStartFunSim. rewrite /MemI.cas.
    cStepS. destruct _q as [[[[[[blk ofs ] v_old] v_new] v_upd] v_cmp] Cmp]. cStepsS.
    iDestruct "ASM" as "[-> [[-> %Hcmp2] [↦ [Cmp Cmp2]]]]".
    iDestruct "IST" as (? ? ? ?) "([-> ->] & [% [% [% [[-> %] >B]]]] & ->)"; des.

    cStepsT.
    iPoseProof (mem_ra_lookup with "[B ↦]") as "[% %Hlookup]"; eauto; [iFrame|].
    iMod ("Cmp2" with "Cmp") as (????) "[C1 [C2 C3]]".
    iPoseProof (mem_ra_cmp with "[B C1 C2]") as "%Hcmp3"; eauto; iFrame.
    iMod ("C3" with "[$]").

    (* Load *)
    cInlineT. cStepsT. rewrite Hlookup. cStepsT.

    (* Cmp *)
    cInlineT. cStepsT. rewrite Hcmp3. cStepsT.

    repeat case_bool_decide; simplify_eq.
    { (* Store *)
      cStepsT. cInlineT. cStepsT. rewrite Hlookup. cStepsT.
      iMod ((mem_ra_update v_upd) with "[B ↦]") as "[B ↦]"; et; [iFrame|].

      cForcesS. iFrame. iSplit; eauto. cStep. iFrame.

      repeat (iSplit; eauto).
      iExists _, _, _, _; repeat (iSplit; eauto).
      iExists _; iSplit; eauto.
      iPureIntro. split; eauto. split.
      - ii. s. rewrite /mem_ra_upd /update.
        repeat destruct dec; ss; subst; case_bool_decide; des; naive_solver.
      - ii; ss; repeat destruct dec; ss; subst; eauto.
    }

    cStepsT. cForcesS.
    case_bool_decide; simplify_eq. iFrame. iSplit; eauto. cStep. iFrame.
    repeat (iSplit; eauto).
    iExists _, _, _, _; repeat (iSplit; eauto).
  (*SLOW*)Qed.

  Lemma sim : ISim.t open MemA MemI (MemA.init_cond csl genv) IstFull.
  Proof using.
    cStartModSim.
    { iIntros "?"; iFrame.
      iExists _, _, ∅, ∅; iSplit; eauto.
      { rewrite ?right_id //. }
      repeat (iSplit; ss).
      iExists _; iSplit; ss. iPureIntro; split; ss.
      split.
      { ii. rewrite /mem_init_val /Mem.load_mem.
        uo; des_ifs; bsimpl; des; des_sumbool; subst; ss; rewrite ?Heq0 ?Heq1 ?Heq2; des_ifs; et.
      }
      { intros ? ? ? H'. revert H'. rewrite /Mem.load_mem; uo; s. des_ifs.
        i. inv H'. eapply lookup_lt_Some; eauto.
      }
    }
    { apply simF_alloc. }
    { apply simF_free. }
    { apply simF_load. }
    { apply simF_store. }
    { apply simF_cmp. }
    { apply simF_cas. }
  (*SLOW*)Qed.
End MemIA.
Section MemIA.
  Context `{!crisG Γ Σ α β τ Hsub Hinv, !memGS}.

  Lemma ctxr sp csl genv : ctx_refines (MemI.t csl genv, emp%I) (MemA.t sp, MemA.init_cond csl genv).
  Proof using.
    eapply main_adequacy, sim; eauto.
  Qed.
End MemIA. End MemIA.
