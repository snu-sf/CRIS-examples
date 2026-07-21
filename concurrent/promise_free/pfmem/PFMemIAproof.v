Require Import CRIS.common.CRIS.
From CRIS.promise_free.pfmem Require Import PFMemHeader PFMemI PFMemA.
From CRIS.promise_free.algebra Require Import HistoryRA AtomicRA.
From CRIS.promise_free.gpfsl Require Import base.
From CRIS.promise_free.model Require Import
  Time TView View Cell Memory Global Time.

Module PFMemIA. Section PFMemIA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG}.

  Context (sp : specmap).
  Context (syn : Threads.syntax).
  Context (size : list Z).

  (* additional well-formed condition for the memory *)
  Definition wf_prealloc (mem : Memory.t) : Prop :=
    ∀ loc,
      Memory.is_prealloced loc mem
      → Memory.get_cell loc mem = Cell.init Val.Vundef.

  Lemma add_get_state mem1 loc from to msg mem2
      (ADD : Memory.add mem1 loc from to msg mem2) :
    ∀ loc, Memory.get_state loc mem1 = Memory.get_state loc mem2.
  Proof.
    inv ADD; inv ADD0; intros l; rewrite /Memory.get_state /=; des_ifs; ss.
    destruct l, loc; des; ss; clarify; ss.
  Qed.

  Lemma wf_prealloc_init : wf_prealloc (Memory.init size).
  Proof. intros [[tid|] bid ofs]; rewrite /Memory.is_prealloced; ss. Qed.

  Lemma wf_prealloc_write mem1 loc from to msg mem2
      (ACC : Memory.accessible loc mem1)
      (WRITE : Memory.add mem1 loc from to msg mem2)
      (WF : wf_prealloc mem1) :
    wf_prealloc mem2.
  Proof.
    intros loc' PRE. hexploit (WF loc'); eauto.
    { move : PRE; hexploit add_get_state; eauto.
      rewrite /Memory.get_state /Memory.is_prealloced /Block.is_prealloced; intros ->; done.
    }
    assert (loc' ≠ loc).
    { ii; clarify.
      move : ACC PRE; rewrite /Memory.accessible /Memory.is_prealloced /Block.accessible /Block.is_prealloced.
      hexploit add_get_state; eauto; rewrite /Memory.get_state; intros ->; des_ifs; ss.
    }
    hexploit (Memory.add_get_cell); eauto.
    intros [C' [-> ADD]]; des_ifs.
  Qed.

  Lemma wf_prealloc_alloc mem1 tid sz mem2 loc
      (WALLOC : Memory.well_alloced mem1)
      (WRITE : Memory.alloc mem1 tid sz mem2 loc)
      (WF : wf_prealloc mem1) :
    wf_prealloc mem2.
  Proof.
    intros loc' PREALLOC.
    hexploit (Memory.alloc_get_state); eauto. instantiate (1:=loc').
    intros [[EQ [_ ALLOCED]] | [NEQ STATE]].
    { rewrite /Memory.get_state in ALLOCED.
      rewrite /Memory.is_prealloced /Block.is_prealloced ALLOCED // in PREALLOC.
    }
    erewrite Memory.alloc_get_cell; eauto.
    apply WF; move : PREALLOC; rewrite /Memory.is_prealloced /Block.is_prealloced.
    move : STATE; rewrite /Memory.get_state.
    intros ->; des_ifs.
  Qed.

  Definition view_na Vcut m : Prop :=
    ∀ loc t f val V,
      (Memory.get loc t m) = Some (f, Message.message val V true) →
      Memory.accessible loc m →
      Time.le t ((View.rlx Vcut) loc).

  Definition Ist : ist_type Σ :=
    λ st_s st_t,
      (∃ gl ths Vcut,
        let m := Global.memory gl in
        ⌜st_t = {[PFMemI.v_config # (Configuration.mk ths gl)↑]}
        ∧ view_na Vcut m
        ∧ Memory.closed_view Vcut m
        ∧ Configuration.wf (Configuration.mk ths gl)
        ∧ wf_prealloc m
        ∧ Global.promise_free gl
        ∧ ∀ tid l lc, IdentMap.find tid ths = Some (l, lc) → Local.promise_free lc⌝
        ∗ hist_auth (Memory.cut Vcut m)
        ∗ tview_auth ths (* authorative resource for thread views *)
        ∗ hist_freeable_auth m (* authorative resource for tokens of free *)
      )%I.

  Definition init_cond : iProp Σ :=
    hist_auth (Memory.init size) ∗
    tview_auth (Configuration.threads (Configuration.init syn size)) ∗
    hist_freeable_auth (Global.memory (Global.init size)).

  Definition MA := (PFMemA.t sp).
  Definition MI := (PFMemI.t syn size).

  (* TODO : MOVE *)
  Lemma atomic_is_inaccessible_impossible
      langst lm gm loc ord racy_prm Vcut γ ζ ζ' 𝓥 mode t Vb ths tid
      (CUT : view_na Vcut (Global.memory gm))
      (FIND : IdentMap.find tid ths = Some (langst, lm))
      (ORDRLX : Ordering.le Ordering.relaxed ord)
      (PFG : Global.promise_free gm)
      (PFL : ∀ tid l lc, IdentMap.find tid ths = Some (l, lc) → Local.promise_free lc)
      (RACE : Local.is_inaccessible lm gm loc racy_prm) :
    (hist_auth (Memory.cut Vcut (Global.memory gm))
    ∗ hist_freeable_auth (Global.memory gm)
    ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ'
    ∗ @{Vb} AtomicPtsToX loc γ t ζ mode
    ∗ tview_auth ths
    ∗ tview tid 𝓥)%I
    ⊢ ⌜False⌝.
  Proof.
    iIntros "[HA [FA [SEEN [PT [TA TV]]]]]".
    iPoseProof (tview_both_valid with "TA TV") as "[% [% [%FIND0 <-]]]".
    rewrite AtomicPtsToX_eq /AtomicPtsToX_def {2}/view_at.
    iDestruct "PT" as "[%ζhist [%Vna [-> [SYNC [HIST [AA AF]]]]]]".
    iPoseProof (hist_own_hist_cut with "HA HIST") as "[%t' [%WFHIST [%ZETACUT %ACC]]]".
    rewrite AtomicSeen_eq /AtomicSeen_def.
    iDestruct "SEEN" as "[[%SEENALLOC %SEEN] [AR [%GOODHIST [%Vna' [%VNATV NA]]]]]". ss.
    exfalso; inv RACE; try done.
    hexploit (PFL tid); eauto; clear PFL; intros PFL.
    inv PFL; inv PFG.
    des. rewrite H2 H3 in FREEPROMISE.
    rewrite Promises.FreePromises.minus_bot in FREEPROMISE. inv FREEPROMISE.
  Qed.

  Lemma atomic_is_racy_impossible
      langst lm gm loc to ord racy_prm Vcut γ ζ ζ' 𝓥 mode t Vb ths tid
      (CUT : view_na Vcut (Global.memory gm))
      (FIND : IdentMap.find tid ths = Some (langst, lm))
      (ORDRLX : Ordering.le Ordering.relaxed ord)
      (PFG : Global.promise_free gm)
      (RACE : Local.is_racy lm gm loc to ord racy_prm) :
    (hist_auth (Memory.cut Vcut (Global.memory gm))
    ∗ hist_freeable_auth (Global.memory gm)
    ∗ @{TView.cur 𝓥} loc sn⊒{γ} ζ'
    ∗ @{Vb} AtomicPtsToX loc γ t ζ mode
    ∗ tview_auth ths
    ∗ tview tid 𝓥)%I
    ⊢ ⌜False⌝.
  Proof.
    iIntros "[HA [FA [SEEN [PT [TA TV]]]]]".
    inv RACE.
    { inv PFG; rewrite H in GET; ss. }
    hexploit MSG; eauto; intros ->; clear MSG.
    iPoseProof (tview_both_valid with "TA TV") as "%IN".
    destruct IN as [l [lc [FOUND LCEQ]]].
    s; rewrite FOUND in FIND; inv FIND.
    rewrite AtomicPtsToX_eq /AtomicPtsToX_def /view_at.
    iDestruct "PT" as "[%ζhist [%Vna [-> [SYNC [HIST [AA AF]]]]]]".
    rewrite AtomicSeen_eq /AtomicSeen_def.
    iDestruct "SEEN" as "[[_ %SEEN] [AR [%GOODHIST [%Vna' [_ NA]]]]]".
    iPoseProof (hist_own_hist_cut with "HA HIST") as "[%t' [<- [%H2 %]]]".
    iDestruct "AA" as "[AA [AEXCLWRITE _]]".
    iPoseProof (at_writer_base_latest with "AA AR") as "%LE".
    destruct (classic (∃ ts' f' m', Cell.get ts' ζ' = Some (f', m'))) as [HEX|FAL]; cycle 1.
    { exfalso; apply GOODHIST, Cell.ext; i; rewrite Cell.bot_get.
      destruct (Cell.get ts ζ') eqn : GET'; ss. destruct p; exfalso; apply FAL; esplits; eauto.  
    }
    destruct HEX as [ts' [f' [m' FOUND']]].
    exfalso.
    hexploit (SEEN ts'); ss; intros TS.
    eapply (TimeFacts.le_not_lt to0 (View.rlx (TView.TView.cur (Local.tview lm)) loc)); eauto.
    hexploit (CUT loc to0); eauto => LECUT.
    etrans; first apply LECUT.
    etrans; last apply TS.
    hexploit (LE ts'); eauto; intros ZETA.
    rewrite H2 Cell.cut_spec in ZETA; des_ifs.
  Qed.

  Lemma hist_auth_write_vs lc1 gl1 loc from to val releasedm released ord lc2 gl2 Vcut ζ
      (WRITE : Local.write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2)
      (AFTER : Time.le (View.rlx Vcut loc) to) :
    let m :=
      Message.message val (TView.TView.write_released (Local.tview lc1) loc to releasedm ord)
        (Ordering.le ord Ordering.na) in
    hist_auth (Memory.cut Vcut (Global.memory gl1)) -∗
    hist loc 1 ζ ==∗
    ∃ ζn, ⌜ Cell.add ζ from to m ζn ⌝ ∗
      hist_auth (Memory.cut Vcut (Global.memory gl2)) ∗
      hist loc 1 ζn.
  Proof.
    inv WRITE. inv WRITE0. inv ADD. rename r into ζn.
    s. iIntros "HA HIST".
    iPoseProof (hist_own_to_hist_lookup with "HA HIST") as "<-".
    remember (Memory.mk _ _) as mem2.
    rewrite hist_auth_eq /hist_auth_def hist_eq /hist_def.
    iCombine "HA" "HIST" as "H".
    iMod (own_update with "H") as "[HA HIST]"; cycle 1.
    { iModIntro. iExists (Cell.cut ζn (View.rlx Vcut loc)). iSplit; cycle 1.
      { iSplitL "HA"; done. }
      iPureIntro.
      inv ADD0. econs; eauto.
      { ii. rewrite /Cell.cut /= DOMap.cut_spec in GET2; des_ifs. eapply DISJOINT; eauto. }
      rewrite {1}/Cell.cut /= CELL2 DOMap.cut_add; des_ifs.
      { destruct loc; ss. }
      exfalso; by eapply DenseOrderFacts.le_not_lt.
    }
    eapply auth_update, discrete_fun_local_update; intros l.
    rewrite ?Memory.cut_accessible.
    hexploit Memory.add_accessible.
    { econs; eauto. econs; eauto. }
    subst mem2; intros ->; des_ifs.
    { rewrite /Memory.get_cell /= /Memory.get_cell /=. destruct (decide (loc = l)).
      { subst loc. rewrite ?discrete_fun_lookup_singleton. destruct l; rewrite /Loc.get_tbid /=.
        des_ifs; ss; des; clarify. des_ifs.
        apply option_local_update, exclusive_local_update; ss.
      }
      { rewrite ?discrete_fun_lookup_singleton_ne; try done.
        des_ifs; ss; des_ifs.
        { exfalso; apply n; destruct loc, l; des; clarify; ss; clarify. }
        des; rewrite a a0 //.
      }
    }
    rewrite ?discrete_fun_lookup_singleton_ne //; ii; clarify.
  Qed.

  Lemma hist_auth_write_non_atomic lc1 gl1 loc from to val releasedm released ord lc2 gl2 Vcut
      msg' from' to' FT'
      (CUT : Time.le (View.rlx Vcut loc) to')
      (AFTER : Time.lt (View.rlx Vcut loc) to)
      (FT : Time.lt from to)
      (LT : Time.lt to' to)
      (WRITE : Local.write_step lc1 gl1 loc from to val releasedm released ord lc2 gl2)
      :
    let ζ := @Cell.singleton from' to' msg' FT' in
    let msg :=
      Message.message val (TView.TView.write_released (Local.tview lc1) loc to releasedm ord)
        (Ordering.le ord Ordering.na) in
    hist_auth (Memory.cut Vcut (Global.memory gl1)) -∗
    hist loc 1 ζ ==∗
      hist_auth (Memory.cut (View.join (View.singleton loc to) Vcut) (Global.memory gl2)) ∗
      hist loc 1 (Cell.singleton msg FT).
  Proof.
    s. iIntros "HA HIST".
    inv WRITE. inv WRITE0. inv ADD. rename r into ζn.
    iPoseProof (hist_own_to_hist_lookup with "HA HIST") as "%SINGLETON"; rewrite -SINGLETON.
    remember (Global.mk _ _ _ _) as gl2.
    remember (Memory.mk _ _) as mem2.
    remember (View.join (View.singleton loc to) Vcut) as Vcut2.
    rewrite hist_auth_eq /hist_auth_def hist_eq /hist_def.
    iCombine "HA" "HIST" as "H".
    iMod (own_update with "H") as "[HA HIST]"; cycle 1.
    { iModIntro. iSplitL "HA"; done. }
    eapply auth_update, discrete_fun_local_update; intros l.
    rewrite ?Memory.cut_accessible.
    hexploit Memory.add_accessible.
    { econs; eauto. econs; eauto. }
    subst mem2; intros. des_ifs.
    { rewrite /Memory.get_cell /= /Memory.get_cell /=. destruct (decide (loc = l)).
      { subst loc. rewrite ?discrete_fun_lookup_singleton. destruct l; rewrite /Loc.get_tbid /=.
        des_ifs; ss; des; clarify. des_ifs.
        apply option_local_update.
        rewrite /TimeMap.join /Time.join; des_ifs.
        { rewrite /TimeMap.singleton /LocFun.add in l; des_ifs.
          exfalso. eapply TimeFacts.le_not_lt; eauto.
        }
        { hexploit Cell.cut_singleton_add; eauto.
          { instantiate (1:=FT'). instantiate (1:=msg').
            rewrite -SINGLETON; ss. }
          instantiate (1:=FT); intro CELL_EQ.
          rewrite /TimeMap.singleton /LocFun.add; des_ifs.
          rewrite CELL_EQ.
          apply exclusive_local_update; ss.
        }
      }
      { rewrite ?discrete_fun_lookup_singleton_ne; try done.
        des_ifs; ss; des_ifs.
        { exfalso; apply n; destruct loc, l; des; clarify; ss; clarify. }
        { rewrite /TimeMap.join /Time.join. 
          des; rewrite a a0 //; des_ifs.
          rewrite /TimeMap.singleton /LocFun.add /LocFun.find /LocFun.init in l0; des_ifs.
          { exfalso. apply n0; inv e; auto. }
          { exfalso. eapply TimeFacts.le_not_lt; [apply DenseOrder.bot_spec | eapply l0]. }
        }
        { rewrite /TimeMap.join /Time.join.
          des; des_ifs.
          all: 
            rewrite /TimeMap.singleton /LocFun.add /LocFun.find /LocFun.init in l0; des_ifs;
            exfalso; eapply TimeFacts.le_not_lt; [apply DenseOrder.bot_spec | eapply l0].
        }
      }
    }
    { rewrite /Memory.get_cell /= /Memory.get_cell /=. destruct (decide (loc = l)).
      { subst loc. rewrite ?discrete_fun_lookup_singleton. destruct l; rewrite /Loc.get_tbid /=.
        des_ifs; ss; des; clarify. }
      { rewrite ?discrete_fun_lookup_singleton_ne; try done.
        destruct loc, l; rewrite /Memory.accessible /Block.accessible in Heq, Heq0.
        des; ss; des_ifs; ss; des; rewrite a a0 //; des_ifs;
        rewrite Heq2 in Heq1; inv Heq1; try lia.
      }
    }
    { rewrite /Memory.get_cell /= /Memory.get_cell /=. destruct (decide (loc = l)).
      { subst loc. rewrite ?discrete_fun_lookup_singleton. destruct l; rewrite /Loc.get_tbid /=.
        des_ifs; ss; des; clarify. }
      { rewrite ?discrete_fun_lookup_singleton_ne; try done.
        destruct loc, l; rewrite /Memory.accessible /Block.accessible in Heq, Heq0.
        des; ss; des_ifs; ss; des; rewrite a a0 //; des_ifs;
        rewrite Heq2 in Heq1; inv Heq1; try lia.
      }
    }
    rewrite ?discrete_fun_lookup_singleton_ne //; ii; clarify.
  Qed.

End PFMemIA. End PFMemIA.
