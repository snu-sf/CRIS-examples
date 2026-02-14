Require Import CRIS.
Require Import NDSHeader NDSI.
Require Import CallFilter.
From iris Require Import frac_auth dfrac_agree gmap_view csum.

Local Open Scope Qp.

Local Definition joinRA `{α : GAT.t} :=
  gmap_viewUR nat (agreeR (SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}))%type.
Local Definition tidRA := gmap_viewUR nat (agreeR natO).
Local Definition initRA := csumR fracR (agreeR natO).
Local Definition ctlRA := exclR unitO.
Local Definition pubRA := gmap_viewUR (option nat) (agreeR boolO).

Class ndsGpreS `{!crisG Γ Σ α β τ _S _I} := {
    #[local] inG_join :: inG joinRA Σ;
    #[local] inG_tid :: inG tidRA Γ;
    #[local] inG_init :: inG initRA Γ;
    #[local] inG_ctl :: inG ctlRA Γ;
    #[local] inG_pub :: inG pubRA Γ;
}.
Class ndsGS `{!crisG Γ Σ α β τ _S _I} := {
    #[local] ndsGS_ndsGpreS :: ndsGpreS;
    join_name : gname;
    tid_name : gname;
    init_name : gname;
    ctl_name : gname;
    pub_name : gname;
}.
Definition ndsΓ : HRA := #[initRA; ctlRA; pubRA; tidRA].
Definition ndsΣ `{Γ : HRA, α : GAT.t} : GRA := #[joinRA].
Global Instance subG_ndsGpreS `{!crisG Γ Σ α β τ _S _I} :
  subG ndsΓ Γ → subG ndsΣ Σ → ndsGpreS.
Proof using.
  i. unfold ndsΓ, ndsΣ in *.
  eapply subG_inv in H; destruct H.
  eapply subG_inv in s0; destruct s0.
  eapply subG_inv in s1; destruct s1.
  eapply subG_inv in s2; destruct s2.
  eapply subG_inv in H0; destruct H0.
  eapply subG_inG in s, s0, s1, s2, s4.
  split; eauto.
Defined.

Local Existing Instances ndsGS_ndsGpreS inG_join inG_tid inG_init inG_ctl inG_pub.

Section NDSRA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _NDS: !ndsGS}.
  (* Join-related predicates *)
  Definition JoinFrag dq mtid postS : iProp Σ :=
    own join_name ((gmap_view_frag mtid (DfracOwn (dq)%Qp) (to_agree postS)): joinRA).
  Definition JoinHandle mtid postS : iProp Σ :=
    JoinFrag (1/4) mtid postS.
  Definition JoinAuth m : iProp Σ :=
    own join_name ((gmap_view_auth (DfracOwn 1) m): joinRA).

    (** init **)
  Definition Pending : iProp Σ := Seal.sealing NDS (own init_name (Cinl (1/2)%Qp)).
  Definition Shot (n : nat) : iProp Σ := Seal.sealing NDS (own init_name (Cinr (to_agree n))).

  (** control **)
  Definition Control : iProp Σ := Seal.sealing NDS (own ctl_name (Excl tt : ctlRA)).

  (** public **)
  Definition PublicAuth (ths: NDSI.thpool) (tido: option nat) : iProp Σ :=
    Seal.sealing NDS
      (own pub_name
         (gmap_view_auth (DfracOwn 1)
            (<[None := to_agree false]> (list_to_map (map (λ '(i, x), (Some i, to_agree (eq_dec (Some i) tido))) (imap pair ths.*1)))))).
  Definition Public (tido: option nat) (b: bool) : iProp Σ :=
    Seal.sealing NDS
      (own pub_name (gmap_view_frag tido (DfracOwn 1) (to_agree b))).

  (* Thread-id-related predicates *)
  Definition Tid (mtid stid ssch : nat) : iProp Σ :=
    own tid_name (gmap_view_frag mtid (DfracOwn 1) (to_agree stid)) ∗
    TID stid ∗ YIELD stid ∗ Shot ssch ∗ Control ∗ Public (Some mtid) true.
  Definition TidAuth (m : gmap nat nat) : iProp Σ :=
    own tid_name (gmap_view_auth (DfracOwn 1) (to_agree <$> m)).

  Lemma Tid_Auth_Tid (m : gmap nat nat) (mtid stid : nat) q :
    TidAuth m ∗ own tid_name (gmap_view_frag mtid (DfracOwn q) (to_agree stid)) -∗
    ⌜m !! mtid = Some stid⌝.
  Proof.
    iIntros "[A F]". iCombine "A F" gives %WF%gmap_view_both_dfrac_valid_discrete_total.
    destruct WF as [? [_ [_ [Hlookup [_ Hin]]]]]; rewrite lookup_fmap in Hlookup.
    destruct (m !! mtid) as [stid2|]; ss; inv Hlookup.
    eapply to_agree_included in Hin; inv Hin; done.
  Qed.
End NDSRA.

Module NDSA. Section NDSA.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _NDS: !ndsGS}.

  (** Initial resource *)
  Definition ir_initRA : DRA_mk initRA := Cinl 1.
  Definition ir_initRA_valid : ✓ ir_initRA.
  Proof using. ss. Qed.

  Definition ir_ctlRA : DRA_mk ctlRA := Excl tt.
  Definition ir_ctlRA_valid : ✓ ir_ctlRA.
  Proof using. ss. Qed.
  
  Definition ir_joinRA : DRA_mk joinRA := 
    (gmap_view_auth (DfracOwn 1) ∅)%SAT.
  Lemma ir_joinRA_valid : ✓ ir_joinRA.
  Proof. rewrite /ir_joinRA; apply gmap_view_auth_valid. Qed.

  Definition ir_tidRA : DRA_mk tidRA := 
    (gmap_view_auth (DfracOwn 1) ∅)%SAT.
  Lemma ir_tidRA_valid : ✓ ir_tidRA.
  Proof. rewrite /ir_joinRA; apply gmap_view_auth_valid. Qed.

  Definition ir_pubRA : DRA_mk pubRA := gmap_view_auth (DfracOwn 1) ∅.
  Definition ir_pubRA_valid : ✓ ir_pubRA.
  Proof using. rewrite /ir_pubRA. eapply gmap_view_auth_valid. Qed.

  Definition InitNDS : iProp Σ := Pending ∗ Control.

  Section IST.
    Definition pub_priv : iProp Σ :=
      own pub_name ((gmap_view_auth (DfracOwn 1) (∅: gmap (option nat) (agreeR boolO))) : pubRA).
    Definition tid_global (mtid: nat) (stid: nat) : iProp Σ :=
      own tid_name ((gmap_view_frag mtid (DfracOwn (1/2)%Qp) (to_agree stid)) : tidRA).
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
      rewrite /PublicAuth /Public. unseal NDS.
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
            { i. rewrite fmap_app imap_app map_app /= in wf0.
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
            { i. rewrite fmap_app imap_app map_app /= in wf0.
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
            { i. rewrite fmap_app imap_app map_app /= in wf0.
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
        destruct tido; ss.
      }
    Qed.

    Lemma Public_update_private ths tid (IN: ∃ stid, ths !! tid = Some stid) :
      PublicAuth ths (Some tid) -∗ Public (Some tid) true
      ==∗ PublicAuth ths None ∗ Public (Some tid) false.
    Proof using.
      des. rewrite /PublicAuth /Public. unseal NDS.
      iIntros "A F". iCombine "A F" as "A".
      rewrite -own_op.
      iApply (own_update with "A").
      etrans; [eapply gmap_view_replace|].
      { instantiate (1 := to_agree false). ss. }
      set (m := _: gmap (option nat) (agreeR boolO)).
      set (m' := _: gmap (option nat) (agreeR boolO)) at 2.
      assert (m ≡ m').
      { subst m m'. ii. destruct i.
        { destruct (decide (tid = n)).
          { subst. rewrite lookup_insert. rewrite lookup_insert_ne; ss.
            gen IN. pattern ths. eapply rev_ind; ss.
            { i. rewrite lookup_app in IN. des_ifs.
              { rewrite fmap_app imap_app map_app list_to_map_app.
                rewrite lookup_union. ss.
                rewrite lookup_insert_ne; cycle 1.
                { ii. inv H0. rewrite ->Nat.add_0_r in *.
                  eapply lookup_lt_Some in Heq. rewrite length_fmap in Heq. nia. }
                { rewrite lookup_empty. hexploit H; eauto. i. rewrite H0; eauto.
                  rewrite right_id. refl. }
              }
              { eapply list_lookup_singleton_Some in IN. des; subst.
                rewrite fmap_app imap_app map_app list_to_map_app /=.
                rewrite lookup_union; ss.
                rewrite Nat.add_0_r.
                eapply lookup_ge_None in Heq.
                assert (n = length l) by nia; subst.
                rewrite length_fmap //.
                rewrite lookup_insert.
                set (m := list_to_map _).
                destruct (m !! Some (length l)) eqn:L; cycle 1.
                { rewrite L left_id //. }
                { eapply elem_of_list_to_map in L; cycle 1.
                  { eapply NoDup_map_imap. }
                  exfalso. gen L. remember (length l) as len. assert (length l ≤ len)%nat by nia.
                  clear Heqlen IN Heq H.
                  gen len. pattern l. eapply rev_ind; ss; i. inv L. rewrite fmap_app imap_app map_app in L.
                  rewrite last_length in H0. eapply elem_of_app in L. des; eauto.
                  { hexploit (H len); eauto. nia. }
                  ss. eapply elem_of_list_singleton in L. inv L.
                  rewrite length_fmap in H0. nia. }
              }
            }
          }
          { rewrite !lookup_insert_ne //; cycle 1. { ii; inv H. }
            set (l := imap pair ths.*1). pattern l. eapply rev_ind; ss.
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
      des. rewrite /PublicAuth /Public. unseal NDS.
      iIntros "A F". iCombine "A F" as "A".
      rewrite -own_op.
      iApply (own_update with "A").
      etrans; [eapply gmap_view_replace|].
      { instantiate (1 := to_agree true). ss. }
      set (m := _: gmap (option nat) (agreeR boolO)).
      set (m' := _: gmap (option nat) (agreeR boolO)) at 2.
      assert (m ≡ m').
      { subst m m'. ii. destruct i.
        { destruct (decide (tid = n)).
          { subst. rewrite lookup_insert. rewrite lookup_insert_ne; ss.
            gen IN. pattern ths. eapply rev_ind; ss.
            { i. rewrite lookup_app in IN. des_ifs.
              { rewrite fmap_app imap_app map_app list_to_map_app.
                rewrite lookup_union. ss.
                rewrite lookup_insert_ne; cycle 1.
                { ii. inv H0. rewrite ->Nat.add_0_r in *.
                  eapply lookup_lt_Some in Heq. rewrite length_fmap in Heq. nia. }
                { rewrite lookup_empty. hexploit H; eauto. i. rewrite H0.
                  rewrite right_id. refl. }
              }
              { eapply list_lookup_singleton_Some in IN. des; subst.
                rewrite fmap_app imap_app map_app list_to_map_app /=.
                rewrite lookup_union; ss.
                rewrite Nat.add_0_r.
                eapply lookup_ge_None in Heq.
                assert (n = length l) by nia; subst.
                rewrite length_fmap lookup_insert.
                set (m := list_to_map _).
                destruct (m !! Some (length l)) eqn:L; cycle 1.
                { rewrite L left_id //.
                  rewrite /dec /option_Dec /AList.option_Dec_obligation_1. des_ifs. }
                { eapply elem_of_list_to_map in L; cycle 1.
                  { eapply NoDup_map_imap. }
                  exfalso. gen L. remember (length l) as len. assert (length l ≤ len)%nat by nia.
                  clear Heqlen IN Heq H.
                  gen len. pattern l. eapply rev_ind; ss; i. inv L. rewrite fmap_app imap_app map_app in L.
                  rewrite last_length in H0. eapply elem_of_app in L. des; eauto.
                  { hexploit (H len); eauto. nia. }
                  ss. eapply elem_of_list_singleton in L. inv L.
                  rewrite length_fmap in H0. nia. }
              }
            }
          }
          { rewrite !lookup_insert_ne //; cycle 1. { ii; inv H. }
            set (l := imap pair ths.*1). pattern l. eapply rev_ind; ss.
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
      rewrite /PublicAuth /Public. unseal NDS.
      iIntros "A".
      iMod (own_update with "A") as "[A F]".
      { etrans; first eapply (gmap_view_alloc _ (Some (length ths)) (DfracOwn 1) (to_agree false)); ss.
        { clear IN. rewrite lookup_insert_ne; ss.
          remember (length ths) as len.
          assert (length ths ≤ len)%nat by nia. clear Heqlen.
          gen H. pattern ths. eapply rev_ind; ss. i.
          rewrite last_length in H0. rewrite fmap_app imap_app map_app list_to_map_app lookup_union /= Nat.add_0_r.
          rewrite lookup_insert_ne; cycle 1.
          { ii. inv H1. rewrite length_fmap in H0. nia. }
          rewrite lookup_empty right_id. eapply H. nia.
        }
        refl.
      }
      iFrame. rewrite fmap_app imap_app map_app /= Nat.add_0_r list_to_map_app.
      rewrite insert_union_singleton_r.
      { ss. destruct (dec (Some (length ths)) tido) eqn:D.
        { rewrite /dec /option_Dec /AList.option_Dec_obligation_1 in D. des_ifs.
          des; ss. inv IN. eapply lookup_lt_Some in IN0; nia. }
        ss. rewrite !length_fmap D /=. rewrite insert_empty. iModIntro. rewrite insert_union_l. eauto. }
      rewrite lookup_insert_ne; ss.
      remember (length ths) as len.
      assert (length ths ≤ len)%nat by nia. clear Heqlen.
      gen H. pattern ths. eapply rev_ind; ss. i.
      rewrite last_length in H0. rewrite fmap_app imap_app map_app list_to_map_app lookup_union /= Nat.add_0_r.
      rewrite lookup_insert_ne; cycle 1.
      { ii. inv H1. rewrite length_fmap in H0. nia. }
      rewrite lookup_empty right_id. eapply H. nia.
    Qed.

    Lemma Control_nodup :
      Control ∗ Control ⊢ ⌜False⌝.
    Proof.
      rewrite /Control. unseal NDS.
      iIntros "[E0 E1]". iCombine "E0 E1" gives %wf. ss.
    Qed.

    Lemma PendingShot_false n :
      Pending ∗ Shot n ⊢ ⌜False⌝.
    Proof using.
      rewrite /Pending /Shot. unseal NDS.
      iIntros "[P S]". iCombine "P S" gives %wf; ss.
    Qed.

    Lemma Pending_Shot n :
      Pending ∗ Pending ⊢ |==> Shot n.
    Proof.
      rewrite /Pending /Shot. unseal NDS.
      rewrite -own_op -Cinl_op frac_op Qp.half_half.
      iIntros "P". iPoseProof (own_update with "P") as ">Q".
      { instantiate (1 := Cinr (to_agree n)).
        eapply cmra_update_exclusive. ss. }
      iFrame; eauto.
    Qed.

    Lemma Shot_dup n :
      Shot n ⊢ Shot n ∗ Shot n.
    Proof.
      rewrite /Shot. unseal NDS.
      rewrite -{1}(agree_idemp (to_agree n)) Cinr_op.
      iIntros "[S0 S1]". iFrame.
    Qed.

    Lemma Shot_match n0 n1 :
      Shot n0 -∗ Shot n1 -∗ ⌜n0 = n1⌝.
    Proof.
      rewrite /Shot. unseal NDS.
      iIntros "S0 S1". iCombine "S0 S1" gives %wf.
      rewrite -Cinr_op Cinr_valid in wf.
      eapply to_agree_op_valid in wf. ss.
    Qed.

  End RA.

  (* Scheduler specifications *)
  Section SPEC.
    Context (sp_user : specmap) (E : coPset).
    Context (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ).

    Definition fspec_spawnable fsp
        (pre : SAny.t → SAny.t → iProp Σ)
        (postS : SAny.t → SAny.t → leibnizO {n & GTerm.t n}) : iProp Σ :=
      fspec_imply fsp
        (fspec_winv E
           (fspec_virtual (λ '(mtid, stid, ssch),
              ((λ (varg : SAny.t) arg,
                Tid mtid stid ssch ∗ ∃ sarg, ⌜arg = sarg↑⌝ ∗ pre varg sarg)%I,
               (λ (vret : SAny.t) ret,
                Tid mtid stid ssch ∗ ∃ sret, ⌜ret = sret↑⌝ ∗ interp_cond (postS vret sret)))%I))).

    Definition fn_spawnable fn
        (pre : SAny.t -d> SAny.t -d> iProp Σ)
        (postS : SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}) : iProp Σ :=
      (∃ fsp, ⌜sp_user !! (speckey_fn fn) = Some fsp⌝ ∗ fspec_spawnable fsp pre postS)%I.

    Definition init_spec : fspec :=
      fspec_winv E
        (fspec_virtual (λ '(x, pre, postS),
             ((λ varg arg, 
                ∃ fn,
                  ⌜varg = fn↑↑ ∧ arg = (fn↑↑)↑⌝ ∗ fn_spawnable fn pre postS ∗
                  TID (get_stid x) ∗ YIELD (get_stid x) ∗ InitNDS ∗ pre (tt↑↑) (tt↑↑) ∗ PYIP x)%I,
              (λ (vret: SAny.t) ret, False)%I)))
    .
    
    Definition inner_spawn_spec : fspec :=
      fspec_mk
        (λ '(b, pre, postS) varg arg,
          if (b: bool)
          then
            (∃ stid fvarg farg fn mtid,
                ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑⌝ ∗
                fn_spawnable fn pre postS ∗
                pre fvarg farg ∗ JoinFrag (3/4)%Qp mtid postS
                ∗ own tid_name (gmap_view_frag mtid (DfracOwn 1) (to_agree stid))
                ∗ Public (Some mtid) false
                ∗ winv (E, E) ∗ TID stid ∗ YIELD stid)
          else
            (∃ stid fvarg farg fn mtid,
                ⌜varg = (fn, fvarg)↑ ∧ arg = (fn, farg)↑ /\ mtid = 0⌝ ∗
                fn_spawnable fn pre postS ∗
                pre fvarg farg ∗ JoinFrag (3/4)%Qp mtid postS
                ∗ own tid_name (gmap_view_frag mtid (DfracOwn (1/2)%Qp) (to_agree stid)) ∗ Control
                ∗ Public (Some mtid) false
                ∗ winv (E, E) ∗ TID stid ∗ YIELD stid))%I
        (λ _ vret _, ∃ (vr : SAny.t), ⌜vret = vr↑⌝ ∗ False)%I.

    Definition spawn_spec : fspec :=
      fspec_virtual (λ '(mtid, stid, ssch, pre, postS),
        ((λ varg arg,
          ∃ fvarg farg fn,
            ⌜varg = ((fn, fvarg) : string * SAny.t) ∧
             arg = ((fn, farg) : string * SAny.t)↑⌝ ∗
            fn_spawnable fn pre postS ∗
            Tid mtid stid ssch ∗
            pre fvarg farg)%I,
          (λ vret ret,
            ∃ tid, ⌜vret = tid ∧ ret = tid↑⌝ ∗ Tid mtid stid ssch ∗ JoinHandle tid postS)%I)).

    Definition yield_spec : fspec :=
      fspec_winv E
        (fspec_simple (λ '(mtid, stid, ssch),
          ((λ varg, ⌜varg = tt↑⌝ ∗ Tid mtid stid ssch),
           (λ vret, ⌜vret = tt↑⌝ ∗ Tid mtid stid ssch))))%I.

    Definition yield_global_spec : fspec :=
      fspec_winv E
        (fspec_simple (λ '(mtid, stid, ssch),
          ((λ varg, ⌜varg = tt↑⌝ ∗ Tid mtid stid ssch),
           (λ vret, ⌜vret = tt↑⌝ ∗ Tid mtid stid ssch))))%I.

    Definition join_spec : fspec :=
      fspec_winv E
        (fspec_virtual (λ '(mtid, stid, ssch, tid, postS),
          ((λ varg arg,
            ⌜arg = tid↑ ∧ varg = tid⌝ ∗ Tid mtid stid ssch ∗ JoinHandle tid postS),
           (λ vret ret, 
            (∃ vsret sret, ⌜vret = (Some vsret) ∧ ret = (Some sret)↑⌝ ∗
            Tid mtid stid ssch ∗ interp_cond (postS vsret sret)))))%I).

    Definition get_tid_spec : fspec :=
      fspec_simple (λ '(mtid, stid, ssch),
        ((λ varg, (⌜varg = tt↑⌝ ∗ Tid mtid stid ssch)),
         (λ vret, (⌜vret = mtid↑⌝ ∗ Tid mtid stid ssch))))%I.

    Definition sp : specmap :=
      {[speckey_fn NDSHdr.init := fspec_to_rel init_spec;
        speckey_fn NDSHdr._spawn := fspec_to_rel inner_spawn_spec;
        speckey_fn NDSHdr.spawn := fspec_to_rel spawn_spec;
        speckey_fn NDSHdr.yield := fspec_to_rel yield_spec;
        speckey_fn NDSHdr.yield_global := fspec_to_rel yield_global_spec;
        speckey_fn NDSHdr.join := fspec_to_rel join_spec;
        speckey_fn NDSHdr.get_tid := fspec_to_rel get_tid_spec]}.
  End SPEC.

  Import NDSI.

  Variable (parent_yield : string).
  
  (* function which would be called by "spawn" of parent scheduler *)
  Definition init : SAny.t → itree crisE unit :=
    λ sfn,
      (* initialization with given function *)
      'fn: string <- (sfn↓↓)!;;
      stid <- trigger GetTid;;
      cput v_sch stid;;;
      'ths: thpool <- cgetN v_ths;;
      new_stid <- trigger (Spawn NDSHdr._spawn (fn, tt↑↑)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      cput v_tid (length ths);;;
      trigger (Yield new_stid);;;
      (* infinite global yield *)
      iterC (λ _,
        trigger (Call parent_yield tt↑);;;
        'ths: thpool <- cgetN v_ths;;
        'mtid: nat <- cgetN v_tid;;
        match ths !! mtid with
        | Some (stid, _) => trigger (Yield stid);;; Ret (inl tt)
        | None => triggerNB
        end
      ) tt.

  Definition inner_spawn : string * SAny.t → itree crisE unit :=
    λ '(fn, arg),
      'rv : SAny.t <- ccallN fn arg;;
      'ths : thpool <- cgetN v_ths;;
      'tid : nat <- cgetN v_tid;;
      match ths !! tid with
      | Some (stid, _) =>
          let ths2 := <[tid := (stid, Some rv)]> ths in
          cput v_ths ths2;;;
          NDS.terminate
      | _ => triggerNB
      end.

  Definition spawn : string * SAny.t → itree crisE nat :=
    λ '(fn, arg),
      'ths : thpool <- cgetN v_ths;;
      new_stid <- trigger (Spawn NDSHdr._spawn (fn, arg)↑);;
      cput v_ths (ths ++ [(new_stid, None)]);;;
      Ret (length ths).

  Definition yield : unit → itree crisE unit :=
    λ _,
      (* sanity checking *)
      'ths : thpool <- cgetN v_ths;;
      tid <- trigger GetTid;;
      'mtid : nat <- cgetN v_tid;;
      match ths !! mtid with
      | Some (stid, _) => if (decide (stid = tid)) then Ret () else triggerNB
      | None => triggerNB
      end;;;
      (* yield *)
      '(exist _ (mtid, stid) _) : _ <- trigger (Choose {p : nat * nat | ths.*1 !! p.1 = Some p.2});;
      cput v_tid mtid;;;
      trigger (Yield stid).

  Definition yield_global : unit → itree crisE unit :=
    λ _,
      'sch: nat <- cgetN v_sch;;
      trigger (Yield sch).

  Definition join : nat → itree crisE (option SAny.t) :=
    λ tid,
      (* possibly infinite loop while waiting for the thread to terminate *)
      orv <- (iterC (λ _,
        'ths : thpool <- cgetN v_ths;;
        match ths !! tid with
        | None => Ret (inr None)
        | Some (_, Some rv) => Ret (inr (Some rv))
        | Some (_, None) => '() : _ <- ccallN NDSHdr.yield tt;; Ret (inl tt)
        end
      ) tt);;
      Ret orv.

  Definition get_tid : unit → itree crisE nat :=
    λ _, cgetN v_tid.

  Definition fnsems (E : coPset) (sp_user: specmap) (T: Type) (get_stid: T → nat) (PYIP: T → iProp Σ): fnsemmap:=
    {[Some NDSHdr.init := Some (msk_scp scp msk_true, (fsp_some (init_spec sp_user E T get_stid PYIP), cfunN init));
      Some NDSHdr._spawn := Some (msk_scp scp msk_true, (fsp_some (inner_spawn_spec sp_user E), cfunN inner_spawn));
      Some NDSHdr.spawn := Some (msk_scp scp msk_true, (fsp_some (spawn_spec sp_user E), cfunN spawn));
      Some NDSHdr.yield := Some (msk_scp scp msk_true, (fsp_some (yield_spec E), cfunN yield));
      Some NDSHdr.yield_global := Some (msk_scp scp msk_true, (fsp_some (yield_global_spec E), cfunN yield_global));
      Some NDSHdr.join := Some (msk_scp scp msk_true, (fsp_some (join_spec E), cfunN join));
      Some NDSHdr.get_tid := Some (msk_scp scp msk_true, (fsp_some (get_tid_spec), cfunN get_tid))]}.

  Program Definition smod E sp_user T get_stid PYIP : SMod.t := {|
    SMod.scopes := scp;
    SMod.fnsems := fnsems E sp_user T get_stid PYIP;
    SMod.initial_st := (NDSI.smod parent_yield).(SMod.initial_st);
  |}.
  Solve All Obligations with rewrite /NDSI.smod /=; mod_tac.

  Definition init_cond : iProp Σ :=
    own tid_name ir_tidRA ∗ own join_name ir_joinRA ∗ own init_name (Cinl (1/2)%Qp)
      ∗ own pub_name (gmap_view_auth (DfracOwn 1) (∅: gmap (option nat) (agreeR boolO))).

  Definition t sp sp_user T get_stid PYIP := SMod.to_mod sp (smod ⊤ sp_user T get_stid PYIP).
End NDSA. End NDSA.

Section FSPEC_NDS.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _NDS: !ndsGS}.

  Definition fspec_nds E (fsp : fspec) : fspec :=
    fspec_winv E
      (fspec_mk
        (λ '(mtid, stid, ssch, x) varg arg, Tid mtid stid ssch ∗ precond fsp x varg arg)
        (λ '(mtid, stid, ssch, x) vret ret, Tid mtid stid ssch ∗ postcond fsp x vret ret))%I.
End FSPEC_NDS.

Lemma nds_alloc `{!crisG Γ Σ α β τ Hsub Hinv, _NDS: !ndsGpreS} :
  ⊢ o=> ∃ (_ : ndsGS), NDSA.init_cond ∗ NDSA.InitNDS.
Proof.
  (* join *)
  iMod (own_alloc NDSA.ir_joinRA) as "[%γjoin JOIN]".
  { eapply NDSA.ir_joinRA_valid. }
  (* tid *)
  iMod (own_alloc ((gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)) : tidRA)) as "[%γtid TID]".
  { eapply NDSA.ir_tidRA_valid. }
  (* init *)
  iMod (own_alloc (Cinl 1)) as "[%γinit INIT]".
  { eapply NDSA.ir_initRA_valid. }
  (* ctl *)
  iMod (own_alloc (Excl ())) as "[%γctl CTL]".
  { eapply NDSA.ir_ctlRA_valid. }
  (* pub *)
  iMod (own_alloc ((gmap_view_auth (DfracOwn 1) ∅) : pubRA)) as "[%γpub PUB]".
  { eapply NDSA.ir_pubRA_valid. }
  pose (@Build_ndsGS _ _ _ _ _ _ _ _ _ γjoin γtid γinit γctl γpub) as Hsch.
  iExists Hsch. unseal NDS. iFrame.
  rewrite /NDSA.InitNDS /Pending /Control. unseal NDS.
  rewrite assoc -own_op -Cinl_op frac_op Qp.half_half.
  iFrame; done.
Qed.
