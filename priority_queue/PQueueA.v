Require Import CRIS.
Require Import MemHeader MemA MemTactics.
Require Import SchHeader SchI SchA SchTactics.
Require Import StackHeader StackA.
Require Import PQueueHeader PQueueI.
From iris.algebra Require Import excl_auth.

Class queueG `{!crisG Γ Σ α β τ _S _I} := QueueG {
  queue_stateG :: inG (excl_authR (listO (prodO valO gnameO))) Γ;
}.
Definition queueΓ : HRA := #[excl_authR (listO (prodO valO gnameO))].
Global Instance subG_queueG `{!crisG Γ Σ α β τ _S _I} :
  subG queueΓ Γ → queueG.
Proof. solve_inG. Defined.
Hint Unfold subG_queueG queue_stateG : GRA_index.

Section definitions.
  Context `{!crisG Γ Σ α β τ _S _I, _SCH: !schGS, _MEM: !memGS}.
  Context `{!stackG StackM.jobID StackM.retID, _QUEUE: !queueG}.
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
        [∗ list] i ↦ e ∈ entries, syn_is_stack (stackN N) e.2 e.1 n
  )%SAT.
  Definition is_queue (n : nat) (γq : gname) (range : nat) (q : val) : iProp Σ :=
    ∃ (qb : mblock) (qofs : ptrofs), ⌜q = Vptr (qb, qofs)⌝ ∗
      ∃ (entries : list (val * gname)),
        ⌜length entries = range⌝ ∗
        inv n queueN (syn_queue_inv n γq range qb qofs entries) ∗
        [∗ list] i ↦ e ∈ entries, is_stack (stackN N) e.2 e.1 n.
  Global Instance is_queue_SLRed n γq q range :
    SLRed n (syn_is_queue n γq q range) (is_queue n γq q range).
  Proof. solve_base_sl_red. Qed.
  Global Instance is_queue_persistent n γq q range :
    Persistent (is_queue n γq q range).
  Proof. apply _. Qed.

  Definition queue_contents (γq : gname) (map : list (list val)) : iProp Σ :=
    ∃ (entries : list (val * gname)), ⌜length entries = length map⌝ ∗
      own γq (●E entries) ∗
      [∗ list] i ↦ e ∈ entries, stack_content e.2 (map !!! i).
End definitions.

Module PQueueA. Section PQueueA.
  Context `{!crisG Γ Σ α β τ _S _I, _SCH: !schGS, _MEM: !memGS}.
  Context `{!stackG StackM.jobID StackM.retID, _QUEUE: !queueG}.
  Context (N : namespace).

  Definition scopes : list string := [].

  Definition new_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, range) : nat * nat),
        ((λ arg, ⌜arg = [Vint range]↑ ∧ 8 * (range + 1) < modulus_64⌝)%Z,
         (λ ret, ∃ q γq, ⌜ret = q↑⌝ ∗
          is_queue N n γq range q ∗ queue_contents γq (repeat [] range)))%I)).

  Definition add_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((γq, range, priority, v) : gname * nat * nat * val),
        ((λ arg, ∃ (n : nat) (q : val),
          ⌜arg = [q; Vint priority; v]↑ ∧ priority < range⌝ ∗ is_queue N n γq range q)%Z,
         (λ ret, ⌜ret = Vundef↑⌝))%I)).

  Definition remove_min_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((γq, range) : gname * nat),
        ((λ arg, ∃ (n : nat) (q : val),
          ⌜arg = [q]↑⌝ ∗ is_queue N n γq range q)%Z,
         (λ ret, True))%I)).

  Definition new : Any.t → itree crisE Any.t := λ _,
    𝒴;;; fbody_trivial ()↑.

  Definition add : Any.t → itree crisE Any.t :=
    atomic_body (add_spec)
      (λ '(_, _, (γq, _, priority, v)) _,
        𝒴;;;
        l <- trigger (Take (list (list val)));;
        trigger (Assume (queue_contents γq l));;;
        let l_p := l !!! priority in
        trigger (Guarantee (queue_contents γq (<[priority := v :: l_p]> l)));;;
        𝒴;;;
        Ret Vundef↑).

  Definition remove_min : Any.t → itree crisE Any.t :=
    atomic_body (remove_min_spec)
      (λ '(_, _, (γq, range)) _,
        𝒴;;;
        'ret : val <- ITree.iter (λ n : nat,
          match n with
          | 0 => Ret (inr Vundef) (* exit loop if all priorities are traversed *)
          | S n' =>
              𝒴;;;
              l <- trigger (Take (list (list val)));;
              trigger (Assume (queue_contents γq l));;;
              let l_p := l !!! (range - n) in
              trigger (Guarantee (queue_contents γq (<[range - n := tail l_p]> l)));;;
              𝒴;;;
              match l_p with
              | []
              | Vundef :: _ => Ret (inl n') (* try next priority if the list is empty *)
              | v :: _ => Ret (inr v) (* exit loop if success pop *)
              end
          end
        ) range;;
        𝒴;;;
        Ret ret↑).

  Definition fnsems : fnsemmap :=
    {[Some PQueueHdr.new := Some (msk_scp scopes msk_true, (fsp_some new_spec, new));
      Some PQueueHdr.add := Some (msk_scp scopes msk_true, (None, add));
      Some PQueueHdr.remove_min := Some (msk_scp scopes msk_true, (None, remove_min))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp Mod.
End PQueueA. End PQueueA.

Module PQueueIA. Section PQueueIA.
  Context `{!crisG Γ Σ α β τ _S _I, _SCH: !schGS, _MEM: !memGS}.
  Context `{!stackG StackM.jobID StackM.retID, _QUEUE: !queueG}.

  Context (N : namespace) (sp sp_user : specmap).
  Context (Hsch : (SchA.sp sp_user (↑N)) ⊆ sp).

  Definition init_cond : iProp Σ := emp%I.

  (* Local Definition sp_stack : specmap := SchA.sp ∅ (↑(stackN N)). *)
  Local Definition StackA := StackA.t (stackN N) (SchA.sp ∅ (↑(stackN N))).
  Local Definition PQueueA := PQueueA.t N sp ★ (StackA ★ SchI.t ★ MemA.t sp).
  Local Definition PQueueI := PQueueI.t      ★ (StackA ★ SchI.t ★ MemA.t sp).
  Local Definition IstFull := IstProd (IstSB (Mod.scopes (PQueueA.t N sp)) IstTrue) IstEq.

  Lemma new_simF : ISim.sim_fun open PQueueA PQueueI IstFull (Some PQueueHdr.new).
  Proof.
    iStartSim.
    steps_l. destruct _q as [[stid mtid] [n range]].
    iDestruct "ASM" as "[TID [-> [-> %Hn]]]".

    steps_r. rewrite /PQueueA.new.
    sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    iApply wsim_mem_alloc; [try prove_inline_cond|try prove_sb_cond|ss|unfold_cris_defs].
    { lia. }
    iIntros (queueb) "↦queue". steps_r.
    sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    rewrite (comm Z.add) Z2Nat.inj_add //; try lia.
    rewrite replicate_add /=; iDestruct "↦queue" as "[↦range ↦queue]".
    store_r "↦range".

    iApply wsim_yy_y. iApply wsim_bind.
    instantiate (1:=(λ '(st_src, _) '(st_tgt, _),
      IstFull st_src st_tgt ∗ Tid mtid stid ∗ winv (↑N, ↑N) ∗
      ∃ γq, is_queue N n γq range (Vptr (queueb, 0%Z)) ∗
      queue_contents γq (repeat [] range))%I).
    iSplitL "↦range ↦queue IST TID".
    { rewrite ?Nat2Z.id.
      iAssert (∃ entries,
        ⌜length entries = range⌝ ∗
        [∗ list] i ↦ v ∈ entries,
          if (decide (0%Z ≤ i)%Z)
          then (queueb, (Z.of_nat i) + 1)%Z ↦ Vundef
          else is_stack (stackN N) v.2 v.1 n ∗ (queueb, (Z.of_nat i) + 1)%Z ↦ v.1 ∗
          stack_content v.2 [])%I
        with "[↦queue]" as "↦queue".
      { iExists (repeat (Vundef, 1%positive) range).
        rewrite repeat_length; iSplit; first done. clear Hn.
        iInduction (range) as [|range]; first ss.
        rewrite -Nat.add_1_r !replicate_add !repeat_app /= ?big_sepL_app /=; case_decide; try lia.
        rewrite ?repeat_length /=.
        iDestruct "↦queue" as "[↦queues [↦queue _]]".
        iPoseProof ("IHrange" with "[↦queues]") as "↦queues"; eauto. iFrame.
        rewrite length_replicate Nat.add_0_r Z.add_1_r Nat2Z.inj_succ; iFrame.
      }
      set (var := range).
      rewrite {1 2 3 4}/var.
      replace (0%Z) with (range - var)%Z by lia.
      rewrite {5}Z.sub_diag.
       (* rewrite {1 3 5 6 7 8 9 10 11 12 13 14 15 17}/var. *)
      iAssert (⌜var ≤ range⌝)%I as "#Hvar"; first (iPureIntro; lia).
      generalize var. clear var. iIntros (var).
      iInduction (var) as [|var] forall (st_src st_tgt).
      { unfold_iter_r. steps_r.
        add_ret_l.
        sch_yield_ir "IST" "TID".
        sch_yield_l.
        iDestruct "↦queue" as "[%entries [% ↦queues]]". rewrite Z.sub_0_r.
        iAssert ([∗ list] i ↦ v ∈ entries,
          is_stack (stackN N) v.2 v.1 n ∗ (queueb, Z.of_nat i + 1)%Z ↦ v.1 ∗ stack_content v.2 [])%I
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
        step. iFrame. iSplitR.
        { iExists _, _; iSplit; first done.
          iExists entries; iSplit; first done. iSplit; done.
        }
        subst range.
        rewrite repeat_length; iSplit; first done.
        iApply (big_sepL_impl with "↦stack_contents").
        iIntros "!> %%%Hlookup S"; set (elem := _ !!! _).
        assert (Hin : elem ∈ repeat [] (length entries)).
        { apply elem_of_list_lookup_total_2; rewrite repeat_length; eapply lookup_lt_Some; eauto. }
        rewrite elem_of_list_In in Hin; apply repeat_spec in Hin; rewrite Hin //.
      }

      iPoseProof "Hvar" as "%".
      unfold_iter_r. steps_r.
      add_ret_l. sch_yield_ir "IST" "TID".

      (* stack allocation *)
      inline_r. force_r (stid, mtid, n). forces_r.
      iFrame. iSplit; eauto.
      steps_r.
      sch_yield_ii "IST".
      steps_r. iDestruct "GRT" as "[TID [-> [%stack [%γs [-> [#is_stack stack]]]]]]".
      steps_r. sch_yield_ir "IST" "TID".

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
      store_r "↦queue".
      replace (length entries - S var + 1)%Z with (length entries - var)%Z by lia.
      sch_yield_ir "IST" "TID".

      replace (range - S var + 1 + 1)%Z with (range - var + 1)%Z by lia.
      rewrite bind_ret_r.
      iApply ("IHvar" with "[] ↦range IST TID [-]").
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
    }

    (* continuation *)
    clear_st. iIntros (st_s _ st_t _) "[IST [TID [W [%γq [#qinv queue]]]]]".
    iApply wsim_fold; iFrame "W".
    steps_r. sch_yield_ir "IST" "TID".
    sch_yield_l. forces_l. iFrame. iSplit; eauto. step. iSplit; done.
  (*SLOW*)Qed.

  Lemma add_simF : ISim.sim_fun open PQueueA PQueueI IstFull (Some PQueueHdr.add).
  Proof.
    iStartSim. rewrite /PQueueA.add /atomic_body.
    steps_l. destruct _q as [[stid mtid] [[[γq range] priority] v]].
    iDestruct "ASM" as "[TID [_ [%n [%q [[-> %] #[%queueb [%queueofs [-> is_queue]]]]]]]]".

    steps_r.
    sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    iDestruct "is_queue" as "[%entries [%Hlen [#qinv #stacks]]]".
    iInv "qinv" as "[◯entries [↦range ↦]]" "close".
    iCombine "stacks" "↦" as "↦"; rewrite -big_sepL_sep.
    hexploit (lookup_lt_is_Some_2 entries priority); first lia; intros [[stack γs] Hstack].
    iPoseProof (big_sepL_lookup_acc_impl priority with "↦") as "[[#stack ↦] ↦s]"; eauto; s.

    load_r "↦".
    iMod ("close" with "[↦s ↦range ↦ ◯entries]") as "_".
    { iFrame. iApply ("↦s" with "[] [↦]"); iFrame. iIntros "!> %%%% [?$]". }
    sch_yield_ir "IST" "TID".
    
    (* stack push *)
    inline_r. rewrite /StackA.push /atomic_body.
    steps_r. force_r (_, _, (n, stack, v, γs)); forces_r. iFrame. iSplit; eauto. steps_r.
    sch_yield_ii "IST".
    steps_r.

    (* atomic update *)
    sch_yield_l. steps_l. sch_yield_l. steps_l.
    rename _q into queue. set (entry := queue !!! priority).
    iDestruct "ASM" as "[%entries' [%Hlen' [● stack_contents]]]".
    iInv "qinv" as "[◯ inv]" "close". iCombine "●" "◯" gives %->%excl_auth_agree_L.
    iMod ("close" with "[◯ inv]") as "_"; first iFrame.
    iPoseProof (big_sepL_lookup_acc_impl priority with "stack_contents") as "[s contents]"; eauto.

    force_r entry. force_r. iFrame "s". steps_r.
    force_l. iSplitL "● contents GRT".
    { iExists entries; iFrame. rewrite length_insert; iSplit; first done.
      iApply ("contents" with "[] [GRT]").
      { iIntros "!> %k %y %Hky % s". rewrite list_lookup_total_insert_ne //. }
      { s. rewrite list_lookup_total_insert // -Hlen'; lia. }
    }

    steps_l. sch_yield_ii "IST".
    iDestruct "GRT" as "[TID _]".
    sch_yield_ir "IST" "TID".
    sch_yield_l. steps_l. sch_yield_l. force_l. iFrame. iSplit; eauto.
    step. iFrame. done.
  (*SLOW*)Qed.

  Lemma remove_min_simF : ISim.sim_fun open PQueueA PQueueI IstFull (Some PQueueHdr.remove_min).
  Proof.
    iStartSim. rewrite /PQueueA.remove_min /atomic_body.
    steps_l. destruct _q as [[stid mtid] [γq range]].
    iDestruct "ASM" as "[TID [_ [%n [%q [-> #[%queueb [%queueofs [-> Q]]]]]]]]".

    steps_r. sch_yield_ir "IST" "TID". sch_yield_ir "IST" "TID".
    iDestruct "Q" as "[%entries [%Hlen [#queue_inv #stack_invs]]]".
    iInv "queue_inv" as "[◯ [↦range ↦queues]]" "close".

    (* range load *)
    load_r "↦range".
    iMod ("close" with "[◯ ↦range ↦queues]") as "_"; iFrame.
    sch_yield_ir "IST" "TID". sch_yield_l. sch_yield_l. norm_l.
    rewrite !Nat2Z.id.
    iAssert (⌜range ≤ length entries⌝)%I as "#Hrange"; first by subst.
    replace (queueofs + 1)%Z with (queueofs + (length entries - range) + 1)%Z by lia.
    generalize range at 2 6 8 9. subst range. iIntros (var).
    iInduction (var) as [|var'] forall (st_src st_tgt).
    { unfold_iter_l; unfold_iter_r. steps_l; steps_r.
      sch_yield_ir "IST" "TID". sch_yield_l. steps_l. sch_yield_l.
      force_l. iFrame; iSplit; eauto.
      step; iFrame; done.
    }

    iPoseProof ("Hrange") as "%".
    unfold_iter_l. steps_l.
    unfold_iter_r. steps_r. sch_yield_ir "IST" "TID".

    (* stack load *)
    rewrite -?Nat2Z.inj_sub; try lia.
    set (index := (length entries - S var')).
    iInv "queue_inv" as "[◯ [↦range ↦queues]]" "close".
    hexploit (lookup_lt_is_Some_2 entries index); first lia; intros [[istack iγs] Hi].
    iPoseProof (big_sepL_lookup_acc _ _ index with "↦queues") as "[↦queue ↦queues]"; eauto; s.
    iPoseProof (big_sepL_lookup_acc _ _ index with "stack_invs") as "[stack _]"; eauto; s.
    load_r "↦queue".
    iPoseProof ("↦queues" with "↦queue") as "↦queues".
    iMod ("close" with "[◯ ↦range ↦queues]") as "_"; iFrame.
    sch_yield_ir "IST" "TID".

    inline_r. rewrite /StackA.pop /atomic_body. steps_r.
    force_r (stid, mtid, (n, istack, iγs)). forces_r. iFrame. iSplit; eauto.
    steps_r. sch_yield_ii "IST".

    (* atomic stack pop *)
    sch_yield_l. steps_l. rename _q into q. force_r (q !!! index). steps_r.
    iDestruct "ASM" as "[%entries' [%Hlenq [● ↦stacks]]]".
    iInv "queue_inv" as "[◯ inv]" "close".
    iCombine "●" "◯" gives %->%excl_auth_agree_L.
    iMod ("close" with "[◯ inv]") as "_"; first iFrame.
    iPoseProof (big_sepL_lookup_acc_impl index with "↦stacks") as "[↦stack ↦stacks]"; eauto; s.
    force_r; iFrame. steps_r. force_l. iSplitL "↦stacks GRT ●".
    { iFrame.
      iSplit; [rewrite length_insert //|].
      iApply ("↦stacks" with "[] [-]").
      { iIntros "!> %%%%"; rewrite list_lookup_total_insert_ne //. iIntros "$". }
      { s; rewrite list_lookup_total_insert // -Hlenq; lia. }
    }
    steps_l.

    (* remainder *)
    sch_yield_ii "IST".

    set (caseb :=
      match q !!! index with
      | [] => true
      | Vundef :: _ => true
      | _ => false
      end
    ); destruct caseb eqn : Hcase.
    {
      set (case := match q !!! index with | [] => Vundef | _ => _ end).
      replace case with Vundef; cycle 1.
      { subst case caseb; destruct (q !!! index) as [|[?|?|]?]; ss. }
      steps_r. iDestruct "GRT" as "[TID _]". sch_yield_ir "IST" "TID".
      sch_yield_l. steps_l. clear case.
      set (case := match q !!! index with | Vint _ as v :: _ => _ | _ => _ end).
      replace case with (Ret (inl var') : itree crisE (nat + val)); cycle 1.
      { subst case caseb; destruct (q !!! index) as [|[?|?|]?]; ss. }
      steps_l. subst index.
      replace (queueofs + _ + 1 + 1)%Z with (queueofs + (length entries - var')%nat + 1)%Z by lia.
      iApply ("IHvar'" $! st_src st_tgt with "[] IST TID"); iFrame; eauto.
      iPureIntro; lia.
    }

    assert (∃ v q', q !!! index = v :: q' ∧ v ≠ Vundef) as [v [q' [Hq' Hv]]].
    { destruct (q !!! index) as [|[?|?|]?]; ss; eauto. }
    rewrite Hq'; ss.
    replace (match v with | Vundef => _ | _ => _ end) with (Ret (inr v) : itree crisE (nat + val)).
    2:{ des_ifs. }
    set (case := match v with | Vundef => _ | _ => _ end).
    replace case with (𝒴;;; Ret (inr v) : itree crisE (nat * Z + val)).
    2:{ subst case; des_ifs; ss. }
    steps_r. iDestruct "GRT" as "[TID _]". sch_yield_ir "IST" "TID".
    sch_yield_l. steps_l. sch_yield_l. sch_yield_l. force_l. iFrame. iSplit; eauto.
    step. iFrame. done.
  (*SLOW*)Qed.

  Lemma sim : ISim.t open PQueueA PQueueI emp IstFull.
  Proof.
    init_sim.
    { apply new_simF. }
    { apply add_simF. }
    { apply remove_min_simF. }
    { iIntros "_"; repeat iExists _; iPureIntro; ss. }
  Qed.
End PQueueIA.
Section ctxr.
  Context `{!crisG Γ Σ α β τ _S _I, _SCH: !schGS, _MEM: !memGS}.
  Context `{!stackG StackM.jobID StackM.retID, _QUEUE: !queueG}.

  Lemma ctxr (N : namespace) (sp_user sp : specmap) :
    SchA.sp sp_user (↑N) ⊆ sp →
    ctx_refines
      (PQueueA.t N sp ★ StackA.t (stackN N) (SchA.sp ∅ (↑(stackN N))) ★ SchI.t ★ MemA.t sp, emp%I)
      (PQueueI.t      ★ StackA.t (stackN N) (SchA.sp ∅ (↑(stackN N))) ★ SchI.t ★ MemA.t sp, emp%I).
  Proof. intros Hsp. eapply main_adequacy, sim; eauto. Qed.
End ctxr. End PQueueIA.

