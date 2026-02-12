Require Import CRIS.
Require Import SchHeader SchA.
Require Import RRSHeader RRSI.
Require Import CallFilter.
From iris Require Import dfrac_agree gmap_view csum.

Set Implicit Arguments.

Canonical Structure InvO `{α : GAT.t} := leibnizO {n & GTerm.t n}.
Local Definition invRA `{α : GAT.t} := gmap_viewUR nat (agreeR InvO).
Local Definition tidRA := gmap_viewUR nat (agreeR natO).
Local Definition initRA := csumR (exclR unitO) (agreeR natO).
Local Definition ctlRA := (exclR unitO).
Local Definition pubRA := gmap_viewUR (option nat) (agreeR boolO).

Class rrsGpreS `{!crisG Γ Σ α β τ _S _I} := {
    #[local] rrs_inG_init :: inG initRA Γ;
    #[local] rrs_inG_ctl :: inG ctlRA Γ;
    #[local] rrs_inG_pub :: inG pubRA Γ;
    #[local] rrs_inG_tid :: inG tidRA Γ;
    #[local] rrs_inG_inv :: inG invRA Σ;
}.
Class rrsGS `{!crisG Γ Σ α β τ _S _I} := {
    #[local] rrsGS_rrsGpreS :: rrsGpreS;
    init_name : gname;
    ctl_name : gname;
    pub_name : gname;
    tid_name : gname;
    inv_name : gname;
}.

Definition rrsΓ : HRA := #[initRA; ctlRA; pubRA; tidRA].
Definition rrsΣ `{Γ : HRA, α : GAT.t} : GRA := #[invRA].
Global Instance subG_rrsGpreS `{!crisG Γ Σ α β τ _S _I} :
  subG rrsΓ Γ → subG rrsΣ Σ -> rrsGpreS.
Proof using.
  i. unfold rrsΓ, rrsΣ in *.
  eapply subG_inv in H; destruct H.
  eapply subG_inv in s0; destruct s0.
  eapply subG_inv in s1; destruct s1.
  eapply subG_inv in s2; destruct s2.
  eapply subG_inv in H0; destruct H0.
  eapply subG_inG in s, s0, s1, s2, s4.
  split; eauto.
Defined.

Local Open Scope Qp.

Module RRSAS. Section RRSAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, _concG: !concGS, _rrsG: !rrsGS}.

  (** init **)
  Definition Pending : iProp Σ := Seal.sealing RRS (own init_name (Cinl (Excl ()))).
  Definition Shot (n : nat) : iProp Σ := Seal.sealing RRS (own init_name (Cinr (to_agree n))).

  (** control **)
  Definition Control : iProp Σ := Seal.sealing RRS (own ctl_name ((Excl tt) : ctlRA)).
  
  (** public **)
  Definition PublicAuth (ths: RRSI.thpool) (tido: option nat) : iProp Σ :=
    Seal.sealing RRS
      (own pub_name
         (gmap_view_auth (DfracOwn 1)
            (<[None := (to_agree false)]> (list_to_map (map (λ '(i, x), (Some i, (to_agree (eq_dec (Some i) tido)))) (imap pair ths)))))).
  Definition Public (tido: option nat) (b: bool) : iProp Σ :=
    Seal.sealing RRS
      (own pub_name (gmap_view_frag tido (DfracOwn 1) (to_agree b))).

  (** inv **)
  Definition gmap_wf (I: gmap nat InvO): Prop := dom I ≡ set_seq 0 (size I).

  Definition rrinv_admin_r (q: Qp) (I: gmap nat InvO): invRA :=
    gmap_view_auth (DfracOwn q) ((λ x, to_agree x) <$> I).
  Definition rrinv_r (I: gmap nat InvO): invRA :=
    big_opL op
      (fun _ tid =>
         match I !! tid with
         | Some inv => (gmap_view_frag tid DfracDiscarded (to_agree inv) : invRA)
         | None => ε
         end) (elements (dom I)).

  Definition rrinv_half (I: gmap nat InvO): iProp Σ :=
    Seal.sealing RRS
      ((own inv_name ((rrinv_admin_r (1/4)%Qp I: invRA) ⋅ (rrinv_r I: invRA))) ∗ ⌜gmap_wf I⌝)%I.
  Definition rrinv (I: gmap nat InvO): iProp Σ :=
    Seal.sealing RRS
      ((own inv_name ((rrinv_admin_r (1/2)%Qp I: invRA) ⋅ (rrinv_r I: invRA))) ∗ ⌜gmap_wf I⌝)%I.
  Definition rrinv_admin (I: gmap nat InvO) : iProp Σ :=
    (own inv_name (rrinv_admin_r 1 I ⋅ rrinv_r I) ∗ ⌜gmap_wf I⌝)%I.
  Definition rrinv_prev (I: gmap nat InvO) : iProp Σ :=
    (own inv_name (rrinv_r I) ∗ ⌜gmap_wf I⌝)%I.

  (** tid **)
  Definition Tid (mtid stid ssch: nat) : iProp Σ :=
    own tid_name ((gmap_view_frag mtid (DfracOwn 1) (to_agree stid)) : tidRA) ∗ YIELD stid ∗ TID stid ∗ Shot ssch ∗ Control ∗ Public (Some mtid) true.
  Definition TidAuth (m : gmap nat nat): iProp Σ :=
    own tid_name ((gmap_view_auth (DfracOwn 1) (to_agree <$> m)) : tidRA).

  Lemma Tid_Auth_Tid (m : gmap nat nat) (mtid stid : nat) (q: Qp) :
    TidAuth m ∗ own tid_name (gmap_view_frag mtid (DfracOwn q) (to_agree stid)) -∗
    ⌜m !! mtid = Some stid⌝.
  Proof.
    iIntros "[A F]"; iCombine "A" "F" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
    destruct WF as [? [_ [_ [Hlookup [_ Hin]]]]]; rewrite lookup_fmap in Hlookup.
    destruct (m !! mtid) as [stid2|] eqn:L; ss; inv Hlookup.
    eapply to_agree_included in Hin. inv Hin; eauto.
  Qed.

  (** initial resource *)
  Definition ir_initRA : DRA_mk initRA := Cinl (Excl ()).
  Definition ir_initRA_valid : ✓ ir_initRA.
  Proof using. ss. Qed.

  Definition ir_ctlRA : DRA_mk ctlRA := (Excl tt).
  Definition ir_ctlRA_valid : ✓ ir_ctlRA.
  Proof using. ss. Qed.

  Definition ir_pubRA : DRA_mk pubRA := gmap_view_auth (DfracOwn 1) ∅.
  Definition ir_pubRA_valid : ✓ ir_pubRA.
  Proof using. rewrite /ir_pubRA. eapply gmap_view_auth_valid. Qed.

  Definition init_invmap: gmap nat InvO := ∅.
  Definition ir_invRA : DRA_mk invRA := (rrinv_admin_r 1 init_invmap) ⋅ (rrinv_r init_invmap).
  Definition ir_invRA_valid : ✓ ir_invRA.
  Proof using.
    rewrite /ir_invRA.
    rewrite /rrinv_admin_r /rrinv_r.
    replace (elements (dom init_invmap)) with ([]: list nat) by compute_done; ss.
    rewrite right_id.
    eapply gmap_view_auth_valid.
  Qed.

  Definition ir_tidRA : DRA_mk tidRA := 
    (gmap_view_auth (DfracOwn 1) ∅)%SAT.
  Lemma ir_newtidRA_valid : ✓ ir_tidRA.
  Proof. rewrite /ir_tidRA; apply gmap_view_auth_valid. Qed.

  Definition init_pub : iProp Σ :=
    Seal.sealing RRS (own pub_name (gmap_view_auth (DfracOwn 1) (∅: gmap (option nat) (agreeR boolO)))).
  Definition init_inv : iProp Σ := 
    Seal.sealing RRS (rrinv ∅).
  Definition init_tid : iProp Σ :=
    Seal.sealing RRS (TidAuth ∅).

  Definition InitRRS : iProp Σ := rrinv ∅ ∗ Pending ∗ Control.

  Section IST.
    Definition pub_init : iProp Σ :=
      own pub_name (gmap_view_auth (DfracOwn 1) ∅ : pubRA).
    Definition tid_global (tid stid: nat) : iProp Σ :=
      own tid_name (gmap_view_frag tid (DfracOwn (1/2)%Qp) ((to_agree stid))).
  End IST.

  Section RA.

    Lemma NoDup_map_imap {T R} (f: nat → R) (ths: list T) :
      NoDup (map (λ '(i, _), (Some i, f i)) (imap pair ths)).*1.
    Proof using.
      set (l := (map _ _).*1).
      assert (l = (map Some (seq 0 (length ths)))).
      { subst l. clear -Γ. pattern ths.
        eapply rev_ind; ss. i.
        rewrite last_length seq_S /= imap_app !map_app fmap_app /= Nat.add_0_r.
        f_equal. eauto. }
      rewrite H. eapply NoDup_ListNoDup, FinFun.Injective_map_NoDup; eauto.
      { ii. inv H0; ss. }
      { eapply seq_NoDup. }
    Qed.

    Lemma Public_Auth_Token ths tido tido' b :
      PublicAuth ths tido -∗ Public tido' b
      -∗ ⌜ match is_some tido, b with
         | true, true => tido = tido'
         | true, false => tido ≠ tido'
         | false, true => False
         | false, false => True
         end ⌝.
    Proof using.
      rewrite /PublicAuth /Public. unseal RRS.
      iIntros "PubA PubF". iCombine "PubA PubF" gives %wf.
      rewrite gmap_view_both_dfrac_valid_discrete in wf; des.
      inv wf2. destruct x.
      { destruct p. rewrite -Some_op -pair_op in H. inv H. rewrite H2 in wf1. inv wf1; ss.
        eapply dfrac_valid_own_l in H. ss. }
      inv H. inv H2; ss.
      destruct tido'; ss.
      { rewrite lookup_insert_ne // in wf0. destruct b; ss.
        { destruct tido; ss.
          { rewrite -elem_of_list_to_map in wf0; cycle 1.
            { eapply NoDup_map_imap. }
            iPureIntro. gen wf0. pattern ths. eapply rev_ind.
            { i. ss. inv wf0. }
            { i. rewrite imap_app map_app /= in wf0.
              eapply elem_of_app in wf0. des; eauto.
              eapply elem_of_list_singleton in wf0. inv wf0.
              rewrite /dec /option_Dec in H0. rewrite /AList.option_Dec_obligation_1 in H0. des_ifs. ss.
              assert (to_agree false ≼ to_agree true) by rewrite H0 //.
              eapply to_agree_included in H. inv H.
            }
          }
          { exfalso.
            rewrite -elem_of_list_to_map in wf0; cycle 1.
            { eapply NoDup_map_imap. }
            gen wf0. pattern ths. eapply rev_ind.
            { i; ss. inv wf0. }
            { i. rewrite imap_app map_app /= in wf0.
              eapply elem_of_app in wf0. des; eauto.
              eapply elem_of_list_singleton in wf0. inv wf0. 
              assert (to_agree false ≼ to_agree true) by rewrite H0 //.
              eapply to_agree_included in H. inv H.
            }
          }
        }
        { destruct tido; ss.
          { rewrite -elem_of_list_to_map in wf0; cycle 1.
            { eapply NoDup_map_imap. }
            iPureIntro. gen wf0. pattern ths. eapply rev_ind.
            { i. ss. inv wf0. }
            { i. rewrite imap_app map_app /= in wf0.
              eapply elem_of_app in wf0. des; eauto.
              eapply elem_of_list_singleton in wf0. inv wf0.
              rewrite /dec /option_Dec in H0. rewrite /AList.option_Dec_obligation_1 in H0. des_ifs.
              { ii. inv H. 
                assert (to_agree false ≼ to_agree true) by rewrite H0 //.
                eapply to_agree_included in H. inv H. }
              { ii. inv H. }
            }
          }
        }
      }
      { rewrite lookup_insert // in wf0. inv wf0. 
        assert (to_agree false ≼ to_agree b) by rewrite H0 //.
        eapply to_agree_included in H. rewrite <-!H.
        destruct tido; ss. }
    Qed.

    Lemma Public_update_private ths tid (IN: ∃ stid, ths !! tid = Some stid) :
      PublicAuth ths (Some tid) -∗ Public (Some tid) true
      ==∗ PublicAuth ths None ∗ Public (Some tid) false.
    Proof using.
      des. rewrite /PublicAuth /Public. unseal RRS.
      iIntros "A F". iCombine "A F" as "A".
      rewrite -own_op.
      iApply (own_update with "A").
      etrans; [eapply gmap_view_replace|].
      { instantiate (1 := (to_agree false)). ss. }
      set (m := _: gmap (option nat) ((agreeR boolO))).
      set (m' := _: gmap (option nat) ((agreeR boolO))) at 2.
      assert (m ≡ m').
      { subst m m'. ii. destruct i.
        { destruct (decide (tid = n)).
          { subst. rewrite lookup_insert. rewrite lookup_insert_ne; ss.
            gen IN. pattern ths. eapply rev_ind; ss.
            { i. rewrite lookup_app in IN. des_ifs.
              { rewrite imap_app map_app list_to_map_app.
                rewrite lookup_union. ss.
                rewrite lookup_insert_ne; cycle 1.
                { ii. inv H0. rewrite ->Nat.add_0_r in *.
                  eapply lookup_lt_Some in Heq. nia. }
                { rewrite lookup_empty. hexploit H; eauto. i. rewrite H0.
                  rewrite right_id. refl. }
              }
              { eapply list_lookup_singleton_Some in IN. des; subst.
                rewrite imap_app map_app list_to_map_app /=.
                rewrite lookup_union; ss.
                rewrite Nat.add_0_r.
                eapply lookup_ge_None in Heq.
                assert (n = length l) by nia; subst.
                rewrite lookup_insert.
                set (m := list_to_map _).
                destruct (m !! Some (length l)) eqn:L; cycle 1.
                { rewrite L left_id //. }
                { eapply elem_of_list_to_map in L; cycle 1.
                  { eapply NoDup_map_imap. }
                  exfalso. gen L. remember (length l) as len. assert (length l ≤ len)%nat by nia.
                  clear Heqlen IN Heq H.
                  gen len. pattern l. eapply rev_ind; ss; i. inv L. rewrite imap_app map_app in L.
                  rewrite last_length in H0. eapply elem_of_app in L. des; eauto.
                  { hexploit (H len); eauto. nia. }
                  ss. eapply elem_of_list_singleton in L. inv L. nia. }
              }
            }
          }
          { rewrite !lookup_insert_ne //; cycle 1. { ii; inv H. }
            set (l := imap pair ths). pattern l. eapply rev_ind; ss.
            { i. destruct x. rewrite !map_app !list_to_map_app; ss.
              rewrite !lookup_union. rewrite H. f_equiv.
              { refl. }
              destruct (decide (n = n1)); subst.
              { rewrite !lookup_insert. rewrite /dec /option_Dec /AList.option_Dec_obligation_1. des_ifs. }
              { rewrite !lookup_insert_ne; try (intro NEQ; inv NEQ; ss). refl. }
            }
          }
        }
        { rewrite lookup_insert_ne; ss. rewrite !lookup_insert; ss. }
      }
      rewrite H. refl.
    Qed.

    Lemma Public_update_public ths tid (IN: ∃ stid, ths !! tid = Some stid):
      PublicAuth ths None -∗ Public (Some tid) false
      ==∗ PublicAuth ths (Some tid) ∗ Public (Some tid) true.
    Proof using.
      des. rewrite /PublicAuth /Public. unseal RRS.
      iIntros "A F". iCombine "A F" as "A".
      rewrite -own_op.
      iApply (own_update with "A").
      etrans; [eapply gmap_view_replace|].
      { instantiate (1 := (to_agree true)). ss. }
      set (m := _: gmap (option nat) ((agreeR boolO))).
      set (m' := _: gmap (option nat) ((agreeR boolO))) at 2.
      assert (m ≡ m').
      { subst m m'. ii. destruct i.
        { destruct (decide (tid = n)).
          { subst. rewrite lookup_insert. rewrite lookup_insert_ne; ss.
            gen IN. pattern ths. eapply rev_ind; ss.
            { i. rewrite lookup_app in IN. des_ifs.
              { rewrite imap_app map_app list_to_map_app.
                rewrite lookup_union. ss.
                rewrite lookup_insert_ne; cycle 1.
                { ii. inv H0. rewrite ->Nat.add_0_r in *.
                  eapply lookup_lt_Some in Heq. nia. }
                { rewrite lookup_empty. hexploit H; eauto. i. rewrite H0.
                  rewrite right_id. refl. }
              }
              { eapply list_lookup_singleton_Some in IN. des; subst.
                rewrite imap_app map_app list_to_map_app /=.
                rewrite lookup_union; ss.
                rewrite Nat.add_0_r.
                eapply lookup_ge_None in Heq.
                assert (n = length l) by nia; subst.
                rewrite lookup_insert.
                set (m := list_to_map _).
                destruct (m !! Some (length l)) eqn:L; cycle 1.
                { rewrite L left_id //.
                  rewrite /dec /option_Dec /AList.option_Dec_obligation_1. des_ifs. }
                { eapply elem_of_list_to_map in L; cycle 1.
                  { eapply NoDup_map_imap. }
                  exfalso. gen L. remember (length l) as len. assert (length l ≤ len)%nat by nia.
                  clear Heqlen IN Heq H.
                  gen len. pattern l. eapply rev_ind; ss; i. inv L. rewrite imap_app map_app in L.
                  rewrite last_length in H0. eapply elem_of_app in L. des; eauto.
                  { hexploit (H len); eauto. nia. }
                  ss. eapply elem_of_list_singleton in L. inv L. nia. }
              }
            }
          }
          { rewrite !lookup_insert_ne //; cycle 1. { ii; inv H. }
            set (l := imap pair ths). pattern l. eapply rev_ind; ss.
            { i. destruct x. rewrite !map_app !list_to_map_app; ss.
              rewrite !lookup_union. rewrite H. f_equiv.
              { refl. }
              destruct (decide (n = n1)); subst.
              { rewrite !lookup_insert. rewrite /dec /option_Dec /AList.option_Dec_obligation_1. des_ifs. }
              { rewrite !lookup_insert_ne; try (intro NEQ; inv NEQ; ss). refl. }
            }
          }
        }
        { rewrite lookup_insert_ne; ss. rewrite !lookup_insert; ss. }
      }
      rewrite H. refl.
    Qed.

    Lemma Public_alloc ths stid_new tido (IN: tido = None ∨ ∃ tid stid, tido = Some tid ∧ ths !! tid = Some stid):
      PublicAuth ths tido ==∗ PublicAuth (ths ++ [stid_new]) tido ∗ Public (Some (length ths)) false.
    Proof using.
      rewrite /PublicAuth /Public. unseal RRS.
      iIntros "A".
      iMod (own_update with "A") as "[A F]".
      { etrans; first eapply (gmap_view_alloc _ (Some (length ths)) (DfracOwn 1) ((to_agree false))); ss.
        { clear IN. rewrite lookup_insert_ne; ss.
          remember (length ths) as len.
          assert (length ths ≤ len)%nat by nia. clear Heqlen.
          gen H. pattern ths. eapply rev_ind; ss. i.
          rewrite last_length in H0. rewrite imap_app map_app list_to_map_app lookup_union /= Nat.add_0_r.
          rewrite lookup_insert_ne; cycle 1.
          { ii. inv H1. nia. }
          rewrite lookup_empty right_id. eapply H. nia.
        }
        refl.
      }
      iFrame. rewrite imap_app map_app /= Nat.add_0_r list_to_map_app.
      rewrite insert_union_singleton_r.
      { ss. destruct (dec (Some (length ths)) tido) eqn:D.
        { rewrite /dec /option_Dec /AList.option_Dec_obligation_1 in D. des_ifs.
          des; ss. inv IN. eapply lookup_lt_Some in IN0; nia. }
        ss. iFrame. rewrite insert_empty. iModIntro. rewrite insert_union_l. eauto. }
      rewrite lookup_insert_ne; ss.
      remember (length ths) as len.
      assert (length ths ≤ len)%nat by nia. clear Heqlen.
      gen H. pattern ths. eapply rev_ind; ss. i.
      rewrite last_length in H0. rewrite imap_app map_app list_to_map_app lookup_union /= Nat.add_0_r.
      rewrite lookup_insert_ne; cycle 1.
      { ii. inv H1. nia. }
      rewrite lookup_empty right_id. eapply H. nia.
    Qed.

    Lemma Control_nodup :
      Control ∗ Control ⊢ ⌜False⌝.
    Proof.
      rewrite /Control. unseal RRS.
      iIntros "[E0 E1]". iCombine "E0 E1" gives %wf. ss.
    Qed.

    Lemma Pending_nodup :
      Pending ∗ Pending ⊢ ⌜False⌝.
    Proof using.
      rewrite /Pending. unseal RRS.
      iIntros "[P0 P1]". iCombine "P0 P1" gives %wf. ss.
    Qed.

    Lemma PendingShot_false n :
      Pending ∗ Shot n ⊢ ⌜False⌝.
    Proof using.
      rewrite /Pending /Shot. unseal RRS.
      iIntros "[P S]". iCombine "P S" gives %wf; ss.
    Qed.

    Lemma Pending_Shot n :
      Pending ⊢ |==> Shot n.
    Proof.
      rewrite /Pending /Shot. unseal RRS.
      iIntros "P". iPoseProof (own_update with "P") as ">Q".
      { instantiate (1 := Cinr ((to_agree n))).
        eapply cmra_update_exclusive. ss. }
      iFrame; eauto.
    Qed.

    Lemma Shot_dup n :
      Shot n ⊢ Shot n ∗ Shot n.
    Proof.
      rewrite /Shot. unseal RRS.
      rewrite -own_op -Cinr_op.
      rewrite -{1}(agree_idemp (to_agree n)). iIntros "$".
    Qed.

    Lemma Shot_match n0 n1 :
      Shot n0 -∗ Shot n1 -∗ ⌜n0 = n1⌝.
    Proof.
      rewrite /Shot. unseal RRS.
      iIntros "S0 S1". iCombine "S0 S1" gives %wf.
      rewrite -Cinr_op Cinr_valid in wf.
      eapply to_agree_op_valid in wf. ss.
    Qed.

    Lemma gmap_wf_lookup_exists i x (WF: gmap_wf i) (LT: (x < size i)%nat) :
      ∃ v, i !! x = Some v.
    Proof.
      r in WF. eapply elem_of_dom. rewrite WF.
      eapply elem_of_set_seq; nia.
    Qed.

    Lemma rrinv_wf i :
      rrinv i ⊢ ⌜gmap_wf i⌝.
    Proof. rewrite /rrinv. unseal RRS. iIntros "[_ %]"; eauto. Qed.

    Lemma rrinv_admin_wf i :
      rrinv_admin i ⊢ ⌜gmap_wf i⌝.
    Proof. rewrite /rrinv_admin. unseal RRS. iIntros "[_ %]"; eauto. Qed.

    Lemma rrinv_admin_inv_false i0 i1 :
      rrinv_admin i0 ∗ rrinv i1 ⊢ ⌜False⌝.
    Proof.
      rewrite /rrinv_admin /rrinv. unseal RRS.
      iIntros "[((A0 & F0) & %) ((A1 & F1) & %)]".
      iCombine "A0 A1" gives %wf. exfalso.
      rewrite /rrinv_admin_r in wf.
      eapply gmap_view_auth_dfrac_op_valid in wf. des.
      rewrite dfrac_op_own in wf. ss.
    Qed.

    Lemma rrinv_admin_half_inv_false i0 i1 :
      rrinv_admin i0 ∗ rrinv_half i1 ⊢ ⌜False⌝.
    Proof.
      rewrite /rrinv_admin /rrinv_half. unseal RRS.
      iIntros "[((A0 & F0) & %) ((A1 & F1) & %)]".
      iCombine "A0 A1" gives %wf. exfalso.
      rewrite /rrinv_admin_r in wf.
      eapply gmap_view_auth_dfrac_op_valid in wf. des.
      rewrite dfrac_op_own in wf. ss.
    Qed.

    Lemma rrinv_r_dup i :
      rrinv_r i ≡ rrinv_r i ⋅ rrinv_r i.
    Proof.
      rewrite /rrinv_r.
      set (l:=elements (dom i)).
      induction l; ss.
      destruct (i !! a).
      - set (r := big_opL _ _ _).
        set (f := gmap_view_frag a _ _).
        rewrite -assoc. rewrite (comm _ r _).
        rewrite !assoc. rewrite -assoc.
        f_equiv.
        { subst f. rewrite -gmap_view_frag_op agree_idemp //. }
        { subst r. eauto. }
      - rewrite !left_id. eauto.
    Qed.
    
    Lemma rrinv_match i0 i1 :
      rrinv i0 ∗ rrinv i1 ⊢ ⌜i0 = i1⌝.
    Proof.
      rewrite /rrinv. unseal RRS.
      iIntros "[[IA %] [I %]]". iCombine "IA I" gives %wf.
      rewrite -assoc in wf.
      rewrite (comm _ (rrinv_r i0) _) in wf.
      rewrite !assoc in wf.
      do 2 eapply cmra_valid_op_l in wf.
      rewrite /rrinv_admin_r in wf.
      eapply gmap_view_auth_dfrac_op_valid in wf. des.
      iPureIntro.
      eapply map_eq. i. specialize (wf0 i).
      rewrite !lookup_fmap in wf0.
      destruct (i0 !! i); destruct (i1 !! i); ss; inv wf0.
      f_equiv.
      assert (to_agree o ≼ to_agree o0).
      { rewrite H3. refl. }
      eapply to_agree_included in H1; eauto.
    Qed.

    Lemma rrinv_prev_gen i :
      rrinv i ⊢ rrinv i ∗ rrinv_prev i.
    Proof.
      rewrite /rrinv /rrinv_prev /rrinv_admin_r. unseal RRS.
      iIntros "[[A F] %]".
      iAssert (⌜gmap_wf i⌝)%I as "WF"; eauto. iFrame "WF".
      iApply own_op.
      rewrite {1}rrinv_r_dup.
      iCombine "A F" as "AF".
      rewrite assoc. iFrame.
    Qed.

    Lemma rrinv_prev_dup i :
      rrinv_prev i ⊢ rrinv_prev i ∗ rrinv_prev i.
    Proof.
      rewrite /rrinv_prev {1}rrinv_r_dup.
      iIntros "((R0 & R1) & %)"; iFrame; eauto.
    Qed.

    Lemma rrinv_prev_subset_aux i0 i1 :
      rrinv_prev i0 ∗ rrinv i1 ⊢ ⌜∀ tid v, i0 !! tid = Some v -> i1 !! tid = Some v⌝.
    Proof.
      rewrite /rrinv_prev /rrinv. unseal RRS.
      iIntros "[[P %WF0] [[A F] %WF1]]".
      rewrite /rrinv_r.
      iPoseProof (big_opL_own_1 with "P") as "P".
      iIntros (tid v L).
      iPoseProof (big_opS_elements with "P") as "P".
      iPoseProof (big_opM_dom with "P") as "P".
      rewrite big_opM_delete; eauto. rewrite L.
      iDestruct "P" as "[P PM]".
      rewrite /rrinv_admin_r.
      iCombine "A P" gives %wf.
      iPureIntro.
      eapply gmap_view_both_dfrac_valid_discrete_total in wf. des.
      rewrite lookup_fmap in wf1. destruct (i1 !! tid); ss.
      inv wf1. f_equiv.
      assert (to_agree v ≼ to_agree o).
      { des; eauto. } 
      eapply to_agree_included in H. rewrite H. eauto.
    Qed.

    Lemma rrinv_prev_subset i0 i1 :
      rrinv_prev i0 ∗ rrinv i1 ⊢ ⌜i0 ⊆ i1⌝.
    Proof.
      iIntros "H".
      iPoseProof (rrinv_prev_subset_aux with "H") as "%".
      iPureIntro. ii. unfold option_relation. des_ifs; specialize (H i o Heq); clarify.
    Qed.

    (** rrinv merge **)
    Lemma rrinv_merge i :
      rrinv i ∗ rrinv i ⊣⊢ rrinv_admin i.
    Proof.
      rewrite /rrinv /rrinv_admin /rrinv_prev /rrinv_admin_r. unseal RRS. iSplit.
      - iIntros "[[[A0 F0] %WF] [[A1 _] _]]".
        iCombine "A0 A1" as "A". iCombine "A F0" as "AF"; iFrame. eauto.
      - iIntros "[[A F] #WF]".
        rewrite {1}rrinv_r_dup. iDestruct "F" as "[F0 F1]".
        rewrite own_op. iFrame. iFrame "WF".
        rewrite -own_op.
        rewrite -gmap_view_auth_dfrac_op dfrac_op_own.
        rewrite Qp.half_half; by iFrame.
    Qed.

    Lemma rrinv_half_merge i :
      rrinv_half i ∗ rrinv_half i ⊣⊢ rrinv i.
    Proof.
      rewrite /rrinv /rrinv_half /rrinv_prev /rrinv_admin_r. unseal RRS. iSplit.
      - iIntros "[[[A0 F0] %WF] [[A1 _] _]]".
        iCombine "A0 A1" as "A". iCombine "A F0" as "AF"; iFrame.
        rewrite Qp.quarter_quarter. eauto.
      - iIntros "[[A F] #WF]".
        rewrite {1}rrinv_r_dup. iDestruct "F" as "[F0 F1]".
        rewrite own_op. iFrame. iFrame "WF".
        rewrite -own_op.
        rewrite -gmap_view_auth_dfrac_op dfrac_op_own.
        rewrite Qp.quarter_quarter; by iFrame.
    Qed.

    Lemma rrinv_prev_empty_false i tid v (LKUP: i !! tid = Some v):
      rrinv_prev i ∗ rrinv ∅ ⊢ ⌜False⌝.
    Proof.
      iIntros "[P F]".
      iPoseProof (rrinv_prev_subset with "[P F]") as "%"; iFrame.
      eapply lookup_weaken in LKUP; eauto; ss.
    Qed.

    (** rrinv alloc **)
    Lemma gmap_wf_lookup_size_none i (WF: gmap_wf i) :
      i !! (size i) = None.
    Proof.
      r in WF.
      eapply not_elem_of_dom. rewrite WF.
      set (n:=size i). clearbody n.
      eapply disjoint_singleton_l.
      replace n with (0 + n)%nat by nia.
      eapply set_seq_S_end_disjoint.
    Qed.

    Lemma rrinv_r_add i (WF: gmap_wf i) Q :
      rrinv_r i ⋅ gmap_view_frag (size i) DfracDiscarded ((to_agree Q))
      ≡ rrinv_r (<[size i:=Q]> i).
    Proof.
      rewrite /rrinv_r.
      rewrite -!big_opS_elements.
      rewrite -!big_opM_dom.
      rewrite big_opM_insert_delete.
      rewrite lookup_insert.
      hexploit gmap_wf_lookup_size_none; eauto. intros N.
      rewrite delete_notin; eauto.
      rewrite comm. f_equiv.
      eapply big_opM_proper. i.
      rewrite lookup_insert_ne; cycle 1.
      { ii. rewrite <-H0 in *. clarify. }
      rewrite !H. refl.
    Qed.

    Lemma rrinv_admin_alloc i Q :
      rrinv_admin i ⊢ |==> rrinv_admin (<[(size i) := Q]> i).
    Proof.
      rewrite /rrinv_admin.
      iIntros "[[A F] %WF]". iSplitL; cycle 1.
      - iPureIntro. r in WF. r.
        rewrite dom_insert. rewrite WF.
        rewrite map_size_insert.
        rewrite gmap_wf_lookup_size_none; eauto.
        rewrite set_seq_S_end_union_L.
        eauto.
      - rewrite /rrinv_admin_r.
        iPoseProof (own_update with "A") as ">A".
        { hexploit gmap_wf_lookup_size_none; eauto. intro N.
          eapply gmap_view_alloc.
          { rewrite lookup_fmap. erewrite N. ss. }
          { eapply dfrac_valid_discarded. }
          { instantiate (1 := (to_agree Q)). econs. }
        }
        iDestruct "A" as "[A F0]".
        iApply own_op.
        rewrite fmap_insert. iFrame.
        iCombine "F F0" as "F".
        rewrite rrinv_r_add; eauto.
    Qed.
    
  End RA.

  (* Scheduler specifications *)
  Section SPEC.
    Variable sp_user : specmap.
    Variable E : coPset.
    Variable T : Type.
    Variable get_stid : T -> nat.
    Variable PYIP: T → iProp Σ.

    Definition fspec_spawnable_rr fsp
      (my_tid: nat) (pre : SAny.t → SAny.t → iProp Σ) (Invs: gmap nat InvO) : iProp Σ :=
      fspec_imply fsp
        (fspec_winv E
           (fspec_virtual (λ '(mtid, stid, ssch),
              ((λ (varg: SAny.t) arg,
                 Tid mtid stid ssch ∗ rrinv_prev Invs ∗
                   (∃ Invs' Inv, rrinv Invs' ∗ ⌜my_tid = mtid ∧ Invs' !! (pred_rr my_tid (size Invs')) = Some Inv⌝ ∗ (⟦ projT2 Inv ⟧)) ∗
                   (∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg))%I,
                (λ (vret: SAny.t) ret,
                  Tid mtid stid ssch ∗ (∃ (sret: SAny.t), ⌜ret = sret↑⌝)))%I)))
    .

    Definition fspec_spawnable_rr_init fsp
      (my_tid: nat) (pre : SAny.t → SAny.t → iProp Σ) (Inv: InvO) : iProp Σ :=
      fspec_imply fsp
        (fspec_winv E
           (fspec_virtual (λ '(mtid, stid, ssch),
              ((λ (varg: SAny.t) arg,
                 Tid mtid stid ssch ∗ rrinv {[0:=Inv]} ∗
                   ⌜my_tid = mtid ∧ my_tid = 0⌝ ∗
                   (∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg))%I,
                (λ (vret: SAny.t) ret,
                  Tid my_tid stid ssch ∗ (∃ (sret: SAny.t), ⌜ret = sret↑⌝)))%I)))
    .

    Definition fn_spawnable_rr fn (my_tid: nat) (pre : SAny.t → SAny.t → iProp Σ) Invs : iProp Σ :=
      (∃ fsp, ⌜sp_user !! (speckey_fn fn) = Some fsp⌝ ∧ fspec_spawnable_rr fsp my_tid pre Invs)%I.
    
    Definition fn_spawnable_rr_init fn (my_tid: nat) (pre : SAny.t → SAny.t → iProp Σ) Inv : iProp Σ :=
      (∃ fsp, ⌜sp_user !! (speckey_fn fn) = Some fsp⌝ ∧
       fspec_spawnable_rr_init fsp my_tid pre Inv).

    Definition init_spec : fspec :=
      fspec_winv E
        (fspec_virtual (λ '(x, pre, Inv),
             ((λ varg arg, 
                ∃ fn,
                  ⌜varg = fn↑↑ ∧ arg = (fn↑↑)↑⌝ ∗ fn_spawnable_rr_init fn 0 pre Inv ∗
                  TID (get_stid x) ∗ YIELD (get_stid x) ∗ InitRRS ∗ pre (tt↑↑) (tt↑↑) ∗ PYIP x)%I,
              (λ (vret: SAny.t) ret, False)%I)))
    .
    
    Definition inner_spawn_spec : fspec :=
      fspec_mk
        (λ '(b, mtid, pre) varg arg,
          if (b: bool)
          then
            (∃ stid fvarg farg fn Invs,
                ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑ /\ Invs <> ∅⌝ ∗ fn_spawnable_rr fn mtid pre Invs ∗
                pre fvarg farg ∗ rrinv_prev Invs ∗ own tid_name (gmap_view_frag mtid (DfracOwn 1) ((to_agree stid))) ∗ winv (⊤, ⊤) ∗ TID stid ∗ YIELD stid) ∗
                Public (Some mtid) false
          else
            (∃ stid fvarg farg fn Inv,
                ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑ /\ mtid = 0⌝ ∗ fn_spawnable_rr_init fn mtid pre Inv ∗
                pre fvarg farg ∗ rrinv {[0:=Inv]} ∗ own tid_name (gmap_view_frag mtid (DfracOwn (1/2)%Qp) ((to_agree stid))) ∗ Control ∗
                Public (Some mtid) false ∗ winv (⊤, ⊤) ∗ TID stid ∗ YIELD stid))%I
        (λ _ _ _, False)%I
    .

    Definition spawn_spec : fspec :=
      fspec_winv E
        (fspec_virtual (λ '(mtid, stid, ssch, pre, Invs, nInv),
          ((λ varg arg,
             (∃ fvarg farg fn,
                 ⌜varg = ((fn, fvarg): string * SAny.t) 
                 ∧ arg = ((fn, farg): string * SAny.t)↑
                 ∧ Invs ≠ ∅⌝ ∗
                 fn_spawnable_rr fn (size Invs) pre (<[(size Invs) := nInv]> Invs) ∗
                 pre fvarg farg) ∗
             Tid mtid stid ssch ∗
             rrinv Invs)%I,
           (λ vret ret,
             Tid mtid stid ssch ∗
             rrinv (<[(size Invs) := nInv]> Invs) ∗
             ⌜vret = (size Invs) ∧ ret = vret↑⌝))%I))
    .

    Definition yield_spec : fspec :=
      fspec_winv E
        (fspec_simple (λ '(mtid, stid, ssch, Invs),
          ((λ varg, ⌜varg = tt↑⌝ ∗ 
                    Tid mtid stid ssch ∗ 
                    rrinv Invs ∗
                    ∃ Inv,
                      ⌜Invs !! mtid = Some Inv⌝ ∗
                      ⟦ projT2 Inv ⟧),
           (λ vret, ⌜vret = tt↑⌝ ∗ 
                    Tid mtid stid ssch ∗ 
                    ∃ Invs' Inv,
                      rrinv Invs' ∗
                      ⌜Invs ⊆ Invs' /\ Invs' !! (pred_rr mtid (size Invs')) = Some Inv⌝ ∗
                      ⟦ projT2 Inv ⟧)
          )))%I.

    Definition yield_global_spec : fspec :=
      fspec_winv E
        (fspec_simple (λ '(mtid, stid, ssch),
          ((λ varg, ⌜varg = tt↑⌝ ∗ Tid mtid stid ssch),
           (λ vret, ⌜vret = tt↑⌝ ∗ Tid mtid stid ssch))))%I.

    Definition get_tid_spec : fspec :=
      fspec_simple (λ '(mtid, stid, ssch),
       ((λ varg, (⌜varg = tt↑⌝ ∗ Tid mtid stid ssch)),
        (λ vret, (⌜vret = mtid↑⌝ ∗ Tid mtid stid ssch))))%I.

    Definition sp : specmap :=
      {[speckey_fn RRSHdr.init := fspec_to_rel init_spec;
        speckey_fn RRSHdr._spawn := fspec_to_rel inner_spawn_spec;
        speckey_fn RRSHdr.spawn := fspec_to_rel spawn_spec;
        speckey_fn RRSHdr.yield := fspec_to_rel yield_spec;
        speckey_fn RRSHdr.yield_global := fspec_to_rel yield_global_spec;
        speckey_fn RRSHdr.get_tid := fspec_to_rel get_tid_spec]}.

  End SPEC.
End RRSAS. End RRSAS.

Module RRSA. Section RRSA.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, !concGS}.
  Context `{_rrsG: !rrsGS}.

  (* Context (parent_yield : string). *)
  Import RRSI.

  Context (parent_yield : string).
  
  (* spawnable funciton *)
  Definition init : SAny.t → itree crisE unit :=
    λ sfn,
      (* initialize RRS with given function *)
      'fn: string <- (sfn↓↓)!;;
      stid <- trigger GetTid;;
      cput v_sch stid;;;
      'ths: thpool <- cgetN v_ths;;
      new_stid <- trigger (Spawn RRSHdr._spawn (fn, tt↑↑)↑);;
      cput v_ths (ths ++ [new_stid]);;;
      cput v_tid (length ths);;;
      trigger (Yield new_stid);;;
      (* infinite global yield *)
      iterC (λ _,
        trigger (Call parent_yield tt↑);;;
        'ths: thpool <- cgetN v_ths;;
        'mtid: nat <- cgetN v_tid;;
        match ths !! mtid with
        | Some stid => trigger (Yield stid);;; Ret (inl tt)
        | None => triggerNB
        end
      ) tt.

  (* spawnable function *)
  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      trigger (Call fn arg↑);;;
      RRS.spin.

  (* callable function *)
  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetN v_ths;;
      new_stid <- trigger (Spawn RRSHdr._spawn (fn, arg)↑);;
      cput v_ths (ths ++ [new_stid]);;;
      Ret (length ths).

  (* callable function *)
  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity checking *)
      'ths : thpool <- cgetN v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetN v_tid;;
      match ths !! mtid with
      | Some stid => if (decide (stid = tid)) then Ret () else triggerNB
      | None => triggerNB
      end;;;
      (* yield *)
      let mtid : nat := succ_rr mtid (length ths) in
      match ths !! mtid with
      | Some stid =>
          cput v_tid mtid;;;
          trigger (Yield stid)
      | None => triggerNB
      end.

  (* callable function *)
  Definition yield_global : unit → itree crisE unit :=
    λ _,
      'sch: nat <- cgetN v_sch;;
      trigger (Yield sch).

  (* callable function *)
  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetN v_tid.
  
  Definition fnsems (E: coPset) (sp_user: specmap) (T: Type) (get_stid : T → nat) (PYIP: T → iProp Σ): fnsemmap :=
    {[Some RRSHdr.init := Some (msk_scp scp msk_true, (fsp_some (RRSAS.init_spec sp_user E get_stid PYIP), cfunN init));
      Some RRSHdr._spawn := Some (msk_scp scp msk_true, (fsp_some (RRSAS.inner_spawn_spec sp_user E), cfunN inner_spawn));
      Some RRSHdr.spawn := Some (msk_scp scp msk_true, (fsp_some (RRSAS.spawn_spec sp_user E), cfunN spawn));
      Some RRSHdr.yield := Some (msk_scp scp msk_true, (fsp_some (RRSAS.yield_spec E), cfunN yield));
      Some RRSHdr.yield_global := Some (msk_scp scp msk_true, (fsp_some (RRSAS.yield_global_spec E), cfunN yield_global));
      Some RRSHdr.get_tid := Some (msk_scp scp msk_true, (fsp_some (RRSAS.get_tid_spec), cfunN get_tid))]}.

  Program Definition smod sp_user (E: coPset) (T: Type) (get_stid: T → nat) (PYIP : T → iProp Σ): SMod.t := {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems E sp_user get_stid PYIP;
    SMod.initial_st := (RRSI.smod parent_yield).(SMod.initial_st);
  |}.
  Solve All Obligations with rewrite /RRSI.smod /=; mod_tac.

  Definition init_cond : iProp Σ := RRSAS.init_inv ∗ RRSAS.init_tid ∗ RRSAS.init_pub.
  
  Definition t sp sp_user (T: Type) (get_stid: T → nat) (PYIP : T → iProp Σ) :=
    SMod.to_mod sp (smod sp_user ⊤ get_stid PYIP).

End RRSA. End RRSA.

Section FSPEC_RRSCH.
  Import RRSAS.
  Context `{_crisG: !crisG Γ Σ α β τ _S _I, !concGS, !rrsGS}.

  Definition per_tid_fspec (fspecf: nat -> fspec) : fspec :=
    fspec_mk (meta := { i : nat & meta (fspecf i) })
      (λ '(existT i meta_i), precond (fspecf i) meta_i)
      (λ '(existT i meta_i), postcond (fspecf i) meta_i).

  Definition per_tid_fspec_rrsch E (fsp: fspec) (Invf: nat -> InvO) (mtid : nat) : fspec :=
    fspec_winv E
      (fspec_mk (meta := meta fsp * (gmap nat InvO))
         (λ '(x,Invs) varg arg,
           ∃ stid ssch Invs',
             Tid mtid stid ssch ∗
             RRSAS.rrinv_prev Invs ∗
             RRSAS.rrinv Invs' ∗
             ⌜ Invs' !! (pred_rr mtid (size Invs')) = Some (Invf (pred_rr mtid (size Invs')))
               /\ Invs' !! mtid = Some (Invf mtid) ⌝ ∗
             ⟦ projT2 (Invf (pred_rr mtid (size Invs'))) ⟧ ∗
             precond fsp x varg arg)%I
         (λ '(x,Invs) vret ret, postcond fsp x vret ret)%I).

  Definition fspec_rrsch E (Invf: nat -> InvO) (fsp: fspec) : fspec :=
    per_tid_fspec (per_tid_fspec_rrsch E fsp Invf).

End FSPEC_RRSCH.

Lemma rrs_alloc `{!crisG Γ Σ α β τ Hsub Hinv, !rrsGpreS} :
  ⊢ o=> ∃ (_ : rrsGS), RRSA.init_cond ∗ RRSAS.InitRRS.
Proof.
  rewrite /RRSA.init_cond /RRSAS.InitRRS.
  rewrite /RRSAS.init_inv /RRSAS.init_tid /RRSAS.init_pub /RRSAS.rrinv /RRSAS.Pending /RRSAS.Control.
  rewrite /RRSAS.TidAuth.
  (* init *)
  iMod (own_alloc (Cinl (Excl ()))) as "[%γinit INIT]".
  { eapply RRSAS.ir_initRA_valid. }
  (* ctl *)
  iMod (own_alloc (Excl ())) as "[%γctl CTL]".
  { eapply RRSAS.ir_ctlRA_valid. }
  (* pub *)
  iMod (own_alloc ((gmap_view_auth (DfracOwn 1) ∅) : pubRA)) as "[%γpub PUB]".
  { eapply RRSAS.ir_pubRA_valid. }
  (* tid *)
  iMod (own_alloc ((gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)) : tidRA)) as "[%γtid TID]".
  { eapply RRSAS.ir_newtidRA_valid. }
  (* inv *)
  iMod (own_alloc (RRSAS.rrinv_admin_r (1/2) ∅ ⋅ RRSAS.rrinv_admin_r (1/2) ∅ ⋅ RRSAS.rrinv_r ∅ ⋅ RRSAS.rrinv_r ∅)) as "[%γinv [[[INV0 INV1] INV2] INV3]]".
  { rewrite /RRSAS.rrinv_admin_r -gmap_view_auth_dfrac_op dfrac_op_own Qp.half_half.
    rewrite /RRSAS.rrinv_r. rewrite dom_empty elements_empty. ss. rewrite !right_id.
    rewrite gmap_view_auth_dfrac_valid. ss. }
  pose (@Build_rrsGS _ _ _ _ _ _ _ _ _ γinit γctl γpub γtid γinv) as Hsch.
  iExists Hsch. unseal RRS. rewrite {3 4}own_op. iFrame. iPureIntro; done.
Qed.
