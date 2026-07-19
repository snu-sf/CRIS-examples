Require Import CRIS.common.CRIS CRIS.scheduler.Atomic.
From CRIS.imp_system Require Import mem.MemHeader mem.MemA mem.MemTactics.
From CRIS.scheduler Require Import SchHeader SchI SchA SchTactics.
From CRIS.elimination_stack Require Import StackHeader StackA.
From CRIS.priority_queue Require Import PQueueHeader PQueueI.
From iris.algebra Require Import excl_auth.

Class queueG `{!crisG Γ Σ α β τ _S _I} := QueueG {
  queue_stateG :: inG (excl_authR (listO (prodO valO gnameO))) Γ;
}.
Definition queueΓ : HRA := #[excl_authR (listO (prodO valO gnameO))].
Global Instance subG_queueG `{!crisG Γ Σ α β τ _S _I} :
  subG queueΓ Γ → queueG.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS, !queueG}.
  Context (N : namespace).

  Definition queueN : namespace := N.@"queue".

  Definition syn_queue_inv
      (n : nat) (γq : gname) (range : nat) (qb : mblock) (qofs : ptrofs)
      (entries : list (val * gname))
      : GTerm.t n := (
    sown γq (excl_auth_frag entries) ∗
    (qb, qofs) ↦ Vint range ∗
    [∗ list] i ↦ x ∈ entries, (qb, qofs + i + 1)%Z ↦ x.1
  )%SAT.
  Definition queue_inv
      (n : nat) (γq : gname) (range : nat) (qb : mblock) (qofs : ptrofs) 
      (entries : list (val * gname))
      : iProp Σ := (
    own γq (◯E entries) ∗
    (qb, qofs) ↦ Vint range ∗
    [∗ list] i ↦ x ∈ entries, (qb, qofs + Z.of_nat i + 1)%Z ↦ x.1
  )%I.
  Global Instance queue_inv_SLRed n γq range qb qofs entries :
    SLRed n (syn_queue_inv n γq range qb qofs entries) (queue_inv n γq range qb qofs entries).
  Proof. solve_base_sl_red. Qed.

  Definition syn_is_queue (n : nat) (γq : gname) (range : nat) (q : val) : GTerm.t n := (
    ∃ (qb : τ{mblock}) (qofs : τ{ptrofs}), ⌜q = Vptr (qb, qofs)⌝ ∗
      ∃ (entries : τ{list (val * gname)}),
        ⌜length entries = range⌝ ∗
        syn_inv queueN (syn_queue_inv n γq range qb qofs entries) ∗
        [∗ list] i ↦ e ∈ entries, syn_is_stack (stackN N) n e.2 e.1
  )%SAT.
  Definition is_queue (n : nat) (γq : gname) (range : nat) (q : val) : iProp Σ :=
    ∃ (qb : mblock) (qofs : ptrofs), ⌜q = Vptr (qb, qofs)⌝ ∗
      ∃ (entries : list (val * gname)),
        ⌜length entries = range⌝ ∗
        inv n queueN (syn_queue_inv n γq range qb qofs entries) ∗
        [∗ list] i ↦ e ∈ entries, is_stack (stackN N) n e.2 e.1.
  Global Instance is_queue_SLRed n γq q range :
    SLRed n (syn_is_queue n γq q range) (is_queue n γq q range).
  Proof. solve_base_sl_red. Qed.
  Global Instance is_queue_persistent n γq q range :
    Persistent (is_queue n γq q range).
  Proof. apply _. Qed.

  Definition queue_contents (γq : gname) (bins : list (list val)) : iProp Σ :=
    ∃ (entries : list (val * gname)), ⌜length entries = length bins⌝ ∗
      own γq (●E entries) ∗
      [∗ list] i ↦ e ∈ entries, stack_content e.2 (bins !!! i).
  Definition syn_queue_contents {n} (γq : gname) (bins : list (list val)) : GTerm.t n :=
    (∃ (entries : τ{list (val * gname)}), ⌜length entries = length bins⌝ ∗
      sown γq (●E entries) ∗
      [∗ list] i ↦ e ∈ entries, syn_stack_content e.2 (bins !!! i))%SAT.
  Global Instance queue_contents_red n γq bins :
    SLRed n (syn_queue_contents γq bins) (queue_contents γq bins).
  Proof. solve_sl_red. Qed.
End definitions.

Module PQueueA. Section PQueueA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS, !queueG}.

  Definition scopes : list string := [].

  Definition new : fbody := λ arg,
    {{{ ∀∀ '((n, range) : nat * nat), ⌜arg = [Vint range]↑ ∧ 8 * (range + 1) < modulus_64⌝%Z }}}
      𝒴@{Some N};;; trigger (Choose (Any.t * ()))
    {{{ RET ret, ∃ q γq, ⌜ret = q↑⌝ ∗
      is_queue N n γq range q ∗ queue_contents γq (replicate range []) }}} @ N.

  Definition add : fbody := λ arg,
    {{{ ∀∀ (x : gname * nat * val),
        ∃ range q n, ⌜arg = [q; Vint x.1.2; x.2]↑ ∧ x.1.2 < range⌝ ∗ is_queue N n x.1.1 range q }}}
      <<{ ∀∀ (l : list (list valO)), queue_contents x.1.1 l,
        queue_contents x.1.1 (<[x.1.2 := x.2 :: (l !!! x.1.2)]> l) }>> @ N
    {{{ RET ret, ⌜ret = Vundef↑⌝ }}} @ N.

  Definition remove_min : fbody := λ arg,
    {{{ ∀∀ '((γq, range) : gname * nat), ∃ q n, ⌜arg = [q]↑⌝ ∗ is_queue N n γq range q }}}
      yield_namespace_iter (Some N) (λ n,
        if (decide (n = range))
        then Ret (inr (Vundef↑, tt))
        else
          '(ret, _) : Any.t * _ <-
            <<{ ∀∀ (l : list (list valO)), queue_contents γq l,
              ∃∃ ret, let l_p := l !!! n in
              queue_contents γq (<[n := tail l_p]> l) ∗
              ⌜ret = match l_p with | [] | Vundef :: _ => inl (S n) | v :: _ => inr v end↑⌝ }>> @ N;;
          'ret : nat + val <- (ret)↓?;;
          match ret with
          | inl n => Ret (inl n)
          | inr v => Ret (inr (v↑, tt))
          end) 0
    {{{ emp }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid PQueueHdr.new # (msk_scp scopes msk_true, (None, new));
      fid PQueueHdr.add # (msk_scp scopes msk_true, (None, add));
      fid PQueueHdr.remove_min # (msk_scp scopes msk_true, (None, remove_min))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End PQueueA. End PQueueA.

Module PQueueIA. Section PQueueIA.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS, !queueG}.

  Context (sp : specmap).

  (* Local Definition sp_stack : specmap := SchA.sp ∅ (↑(stackN N)). *)
  Local Definition PQueueA := PQueueA.t ★ (StackA.t ★ SchI.t ★ MemA.t sp).
  Local Definition PQueueI := PQueueI.t ★ (StackA.t ★ SchI.t ★ MemA.t sp).
  Local Definition IstFull := IstProd (IstSB (Mod.scopes (PQueueA.t)) IstTrue) IstEq.

  Lemma new_simF : ISim.sim_fun open PQueueA PQueueI IstFull (fid PQueueHdr.new).
  Proof.
    cStartFunSim. rewrite /PQueueI.new /PQueueA.new. cStepsS.
    aStepS (N [n range]) "[-> %Hrange]".

    cStepsT. sYields. mAllocT as (queueb) "↦queue"; first lia. sYields.
    rewrite (comm Z.add) Z2Nat.inj_add //; try lia.
    rewrite replicate_add /=; iDestruct "↦queue" as "[↦range ↦queue]".
    mStore.

    iApply wsim_yy_y_namespace. iApply wsim_bind_strong.
    rewrite ?Nat2Z.id.
    iAssert (∃ entries,
      ⌜length entries = range⌝ ∗
      [∗ list] i ↦ v ∈ entries,
        if (decide (0%Z ≤ i)%Z)
        then (queueb, (Z.of_nat i) + 1)%Z ↦ Vundef
        else is_stack (stackN N) n v.2 v.1 ∗ (queueb, (Z.of_nat i) + 1)%Z ↦ v.1 ∗
        stack_content v.2 [])%I
      with "[↦queue]" as "↦queue".
    { iExists (repeat (Vundef, 1%positive) range).
      rewrite repeat_length; iSplit; first done.
      iInduction (range) as [|range]; first ss.
      rewrite -Nat.add_1_r !replicate_add !repeat_app /= ?big_sepL_app /=; case_decide; try lia.
      rewrite ?repeat_length /=.
      iDestruct "↦queue" as "[↦queues [↦queue _]]".
      iPoseProof ("IHrange" with "[] [↦queues]") as "↦queues"; eauto.
      { iPureIntro; lia. }
      iFrame.
      rewrite length_replicate Nat.add_0_r Z.add_1_r Nat2Z.inj_succ; iFrame.
    }
    set (var := range).
    rewrite {1 2 3 4}/var.
    replace (0%Z) with (range - var)%Z by lia.
    iEval (rewrite /var Z.sub_diag) in "↦range".
    rewrite {5}Z.sub_diag.
    iAssert (⌜var ≤ range⌝)%I as "#Hvar"; first (iPureIntro; lia).
    generalize var. clear var. iIntros (var).
    iInduction (var) as [|var] forall (st_src st_tgt).
    { aUnfoldT. cStepsT. appendRetS. sYields. sYieldS.
      iDestruct "↦queue" as "[%entries [% ↦queues]]". rewrite Z.sub_0_r.
      iAssert ([∗ list] i ↦ v ∈ entries,
        is_stack (stackN N) n v.2 v.1 ∗ (queueb, Z.of_nat i + 1)%Z ↦ v.1 ∗ stack_content v.2 [])%I
        with "[↦queues]" as "↦queues".
      { iApply (big_sepL_impl with "↦queues").
        iIntros "!> %%%Hlookup"; apply lookup_lt_Some in Hlookup; case_decide; try lia.
        iIntros "[$ $]".
      }
      iPoseProof (big_sepL_sep with "↦queues") as "[#↦stacks ↦queues]".
      iPoseProof (big_sepL_sep with "↦queues") as "[↦queues ↦stack_contents]".
      iMod (own_alloc (●E entries ⋅ ◯E entries)) as "[%γq [●q ◯q]]".
      { eauto using excl_auth_valid. }
      iMod (inv_alloc (syn_queue_inv n γq range queueb 0 entries) _ _ _ (queueN N)
        with "[◯q ↦queues ↦range]") as "#Qinv"; eauto.
      { apply nclose_subseteq. }
      { solve_base_sl_red; iFrame. }
      cStep; iFrame.
      sYields. sYieldS. cForceS (_, tt). cStep; iFrame "∗#".
      rewrite length_replicate. iModIntro. iSplit; ss. iExists _; repeat iSplit; auto.
      iApply (big_sepL_impl with "↦stack_contents").
      iIntros "!> %% %Hk ?". rewrite list_lookup_total_alt lookup_replicate_2 //=.
      apply lookup_lt_Some in Hk; lia.
    }

    iPoseProof "Hvar" as "%".
    aUnfoldT. cStepsT. appendRetS. sYields.

    (* stack allocation *)
    cInlineT. rewrite /StackA.new_stack. cStepsT.
    aForceT (stackN N) with ""; first eauto. sYields. destruct _q as [ret_t []].
    cStepsT. iDestruct "GRT" as "[%stack [%γs [-> [#is_stack stack]]]]".
    cStepsT. sYields.

    iDestruct "↦queue" as "[%entries [%Hentries ↦queue]]".
    hexploit (lookup_lt_is_Some_2 entries (range - S var)); first lia; intros [p Hp].
    iPoseProof (big_sepL_insert_acc _ _ (range - S var) with "↦queue") as "[↦ ↦queue]"; eauto.
    case_decide; last lia.
    iSpecialize ("↦queue" $! (stack, γs) with "↦").
    iPoseProof (big_sepL_lookup_acc_impl (range - S var) with "↦queue")
      as "[↦queue ↦close]"; eauto.
    { rewrite list_lookup_insert //; lia. }
    case_decide; last lia.

    rewrite Nat2Z.inj_sub //.
    mStore.
    replace (length entries - S var + 1)%Z with (length entries - var)%Z by lia.
    sYields.

    replace (range - S var + 1 + 1)%Z with (range - var + 1)%Z by lia.
    rewrite bind_ret_r.
    iApply ("IHvar" with "[] IST ↦range [-]").
    { iIntros "!>"; iPureIntro; lia. }
    iExists (<[length entries - S var := (stack, γs)]> entries); iSplit.
    { rewrite length_insert //. }

    subst range.
    iApply ("↦close" with "[] [↦queue stack]").
    { iModIntro; iIntros (??) "%% H"; do 2 case_decide; try lia; iFrame. }
    { case_decide; try lia. ss.
      iFrame "is_stack". rewrite Nat2Z.inj_sub //.
      replace (length entries - S var + 1)%Z with (length entries - var)%Z by lia; iFrame.
    }
  Qed.

  Lemma add_simF : ISim.sim_fun open PQueueA PQueueI IstFull (fid PQueueHdr.add).
  Proof.
    cStartFunSim. rewrite /PQueueA.add /PQueueI.add. cStepsS; cStepsT.
    aStepS (N [[γq priority] v]) "/= [%range [%q [%n [[-> %Hp] #HQ]]]]".
    iDestruct "HQ" as "[%queueblk [%queueofs [-> [%entries [%Hlen [#qinv #stacks]]]]]]".

    cStepsT. aAddY. sYields.
    iInv "qinv" as "[◯entries [↦range ↦]]" "close".
    iCombine "stacks" "↦" as "↦"; rewrite -big_sepL_sep. ss.
    hexploit (lookup_lt_is_Some_2 entries priority); first lia; intros [[stack γs] Hstack].
    iPoseProof (big_sepL_lookup_acc_impl priority with "↦") as "[[#stack ↦] ↦s]"; eauto; s.
    mLoad.
    iMod ("close" with "[↦s ↦range ↦ ◯entries]") as "_".
    { iFrame. iApply ("↦s" with "[] [↦]"); iFrame. iIntros "!> %%%% [?$]". }
    sYields.

    (* stack push *)
    cInlineT. rewrite /StackA.push. cStepsT. sYieldS.
    aForceT (stackN N) with ""; try instantiate (1:=(_, _)); simpl; eauto with iFrame.
    aStep. iExists (S n). iAuIntro. iInv "qinv" as "[◯ inv]".
    iAaccIntro "%queue [%entries' [%Hlen' [● stack_contents]]] !>" with "".
    iCombine "●" "◯" gives %->%excl_auth_agree_L.
    set (entry := queue !!! priority).
    iPoseProof (big_sepL_lookup_acc_impl priority with "stack_contents") as "[s contents]"; eauto.
    iFrame "s"; iSplit.
    { iIntros "s !>"; iFrame. iSplit; first done. iApply ("contents" with "[] [s]"); eauto. }
    iIntros (ret_t) "s !>"; iFrame. iExists _; iSplitL.
    { iSplit; first rewrite length_insert //. iApply ("contents" with "[] [s]").
      { iIntros "!> %k %y %Hky % s". rewrite list_lookup_total_insert_ne //. }
      { s. rewrite list_lookup_total_insert // -Hlen'; lia. }
    }
    clear_st; iIntros "!>" (st_src st_tgt) "IST". cStepsT. iDestruct "GRT" as "->". cStepsT.
    sYields. sYieldS. cStep; iFrame. auto.
  Qed.

  Lemma remove_min_simF : ISim.sim_fun open PQueueA PQueueI IstFull (fid PQueueHdr.remove_min).
  Proof.
    cStartFunSim. rewrite /PQueueA.remove_min /PQueueI.remove_min. cStepsS; cStepsT.
    aStepS (N [γq range]) "/= [%q [%n [-> #[%queueb [%queueofs [-> Q]]]]]]".
    iDestruct "Q" as "[%entries [%Hlen [#queue_inv #stack_invs]]]".
    cStepsT. aAddY. sYields.

    (* range load *)
    iInv "queue_inv" as "[◯ [↦range ↦queues]]" "close".
    mLoad.
    iMod ("close" with "[◯ ↦range ↦queues]") as "_"; iFrame. sYields. sYieldS.

    (* induction *)
    rewrite !Nat2Z.id. replace 0 with (range - range) by lia.
    iAssert (⌜range ≤ length entries⌝)%I as "#Hrange"; first by subst.
    replace (queueofs + 1)%Z with (queueofs + (length entries - range) + 1)%Z by lia.
    generalize range at 2 8 9 10. subst range. iIntros (var).
    iInduction (var) as [|var'] forall (st_src st_tgt).
    { aUnfoldS. rewrite Nat.sub_0_r decide_True //.
      aUnfoldT. sYields. sYieldS. cNormS. sYieldS. by cStep; iFrame.
    }

    iPoseProof ("Hrange") as "%". aUnfoldT. aUnfoldS.
    rewrite decide_False; last by lia. sYields.

    (* stack load *)
    rewrite -?Nat2Z.inj_sub; try lia.
    set (index := (length entries - S var')).
    iInv "queue_inv" as "[◯ [↦range ↦queues]]" "close".
    hexploit (lookup_lt_is_Some_2 entries index); first lia; intros [[istack iγs] Hi].
    iPoseProof (big_sepL_lookup_acc _ _ index with "↦queues") as "[↦queue ↦queues]"; eauto; s.
    iPoseProof (big_sepL_lookup_acc _ _ index with "stack_invs") as "[stack _]"; eauto; s.
    mLoad.
    iPoseProof ("↦queues" with "↦queue") as "↦queues".
    iMod ("close" with "[◯ ↦range ↦queues]") as "_"; iFrame.
    sYields.

    (* stack pop *)
    cInlineT. rewrite /StackA.pop. cStepsT. sYieldS. cStepsS.
    aForceT (stackN N) with ""; first eauto with iFrame.
    aStep. iExists (S n). iAuIntro. iInv "queue_inv" as "[◯ inv]".
    iAaccIntro "%queue [%entries' [%Hlenq [● ↦stacks]]] !>" with "".
    iCombine "●" "◯" gives %->%excl_auth_agree_L.
    iPoseProof (big_sepL_lookup_acc_impl index with "↦stacks") as "[↦stack ↦stacks]"; first eauto.
    iFrame "↦stack". iSplit.
    { iIntros "↦ !>"; iFrame. iSplit; first done. iApply ("↦stacks" with "[] [-]"); eauto. }

    iIntros (ret_t) "↦stack !>"; iFrame; iExists _; iSplitL.
    { iSplit; first auto. iSplit; first rewrite length_insert //.
      iApply ("↦stacks" with "[] [-]").
      { iIntros "!> %%%%"; rewrite list_lookup_total_insert_ne //. iIntros "$". }
      { s; rewrite list_lookup_total_insert //.
        { destruct (queue !!! index); ss. }
        rewrite -Hlenq; lia.
      }
      auto.
    }

    iModIntro. clear_st; iIntros (st_src st_tgt) "IST". cStepsT. iDestruct "GRT" as "->".
    set (caseb :=
      match queue !!! index with
      | [] => true
      | Vundef :: _ => true
      | _ => false
      end
    ); destruct caseb eqn : Hcase.
    { set (case := match queue !!! index with | [] => Vundef | v :: _ => v end).
      assert (case = Vundef) as Heq by (subst case caseb; destruct (_ !!! _) as [|[?|?|]?]; ss).
      subst case; rewrite Heq.
      sYields. sYieldS. cStepS.
      set (case := match queue !!! index with | Vint _ as v :: _ => _ | _ => _ end).
      replace case with ((inl (S index)) : nat + val); cycle 1.
      { subst case caseb; destruct (queue !!! index) as [|[?|?|]?]; ss. }
      cStepsS. subst index.
      replace (queueofs + _ + 1 + 1)%Z with (queueofs + (length entries - var')%nat + 1)%Z by lia.
      replace (S (length entries - S var')) with (length entries - var') by lia.
      iApply ("IHvar'" $! st_src st_tgt with "[] IST"); iFrame; eauto.
      iPureIntro; lia.
    }

    assert (∃ v q', queue !!! index = v :: q' ∧ v ≠ Vundef) as [v [q' [Hq' Hv]]].
    { destruct (queue !!! index) as [|[?|?|]?]; ss; eauto. }
    rewrite Hq'; ss.
    replace (match v with | Vundef => _ | _ => _ end) with ((inr v) : (nat + val)); last des_ifs.
    cStepsT.
    set (case := match v with | Vundef => _ | _ => _ end).
    replace case with (𝒴;;; Ret (inr v) : itree crisE (nat * Z + val)); last (subst case; des_ifs).
    sYields. sYieldS. cStepsS. sYieldS. cStep; iFrame. auto.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open PQueueA PQueueI emp IstFull.
  Proof.
    cStartModSim.
    { apply new_simF. }
    { apply add_simF. }
    { apply remove_min_simF. }
    { iIntros "_"; repeat iExists _; iPureIntro; ss. }
  Qed.
End PQueueIA.
Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS, !queueG}.

  Lemma ctxr (sp : specmap) :
    ctx_refines
      (PQueueI.t ★ StackA.t ★ SchI.t ★ MemA.t sp, emp%I)
      (PQueueA.t ★ StackA.t ★ SchI.t ★ MemA.t sp, emp%I).
  Proof. intros Hsp. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End PQueueIA.
