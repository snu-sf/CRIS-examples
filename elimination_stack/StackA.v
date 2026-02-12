Require Import CRIS.
Require Import MemHeader MemA.
Require Import SchHeader SchA.
Require Import HelpingHeader HelpingTactics.
Require Export StackHeader.

Class stackG (jobID retID : Type) `{!crisG Γ Σ α β τ _S _I} := StackG {
  stack_tokG :: inG (exclR unitO) Γ;
  stack_stateG :: inG (authR (optionUR $ exclR (listO (leibnizO val)))) Γ;
  stack_helpingG :: inG (helpingR jobID retID) Γ;
}.
Definition stackΓ (jobID retID : Type) : HRA :=
  #[exclR unitO; authR (optionUR $ exclR (listO (leibnizO val))); helpingR jobID retID].
Global Instance subG_stackG (jobID retID : Type) `{!crisG Γ Σ α β τ _S _I} :
  subG (stackΓ jobID retID) Γ → (stackG jobID retID).
Proof. solve_inG. Defined.
Hint Unfold subG_stackG stack_tokG stack_stateG : GRA_index.

Section definitions.
  Definition jobID : Type := nat * nat * (nat * val * val * gname).
  Definition retID : Type := val.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !memGS, !stackG jobID retID, !schGS}.
  Context (N : namespace).

  Definition offerN := N .@ "offer".
  Definition stackN := N .@ "stack".

  Definition stack_content (γs : gname) (l : list (leibnizO val)) : iProp Σ :=
    (own γs (◯ Excl' l))%I.

  Lemma stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False.
  Proof.
    iIntros "Hl1 Hl2".
    iCombine "Hl1 Hl2" gives %[]%auth_frag_op_valid_1.
  Qed.

  Fixpoint syn_list_inv (l : list val) (rep : val) (n : nat) : GTerm.t n :=
    match l with
    | nil => ⌜rep = Vint 0⌝
    | v::l => ∃ (blk : τ{mblock}) (ofs : τ{ptrofs}) (rep' : τ{val}) (q0 q1 : τ{Qp}),
        ⌜rep = Vptr (blk, ofs)⌝ ∗
        (blk, ofs) ↦{q0} v ∗ (blk, ofs + 1)%Z ↦{q1} rep' ∗ syn_list_inv l rep' n
    end%SAT.

  Fixpoint list_inv (l : list val) (rep : val) (n : nat) : iProp Σ :=
    match l with
    | nil => ⌜rep = Vint 0⌝
    | v::l => ∃ (blk : mblock) (ofs : ptrofs) (rep' : val) (q0 q1 : Qp),
        ⌜rep = Vptr (blk, ofs)⌝ ∗
        (blk, ofs) ↦{q0} v ∗ (blk, ofs + 1)%Z ↦{q1} rep' ∗ list_inv l rep' n
    end%I.

  Global Instance list_inv_SLRed l n rep : SLRed n (syn_list_inv l rep n) (list_inv l rep n).
  Proof. revert n rep; induction l; i; solve_sl_red. Qed.
  Local Hint Extern 0 (environments.envs_entails _ (list_inv (_::_) _)) => simpl : core.

  Lemma list_inv_comparable l rep n :
    list_inv l rep n -∗
    list_inv l rep n ∗
    (∃ q v, MemA.val_r rep q v) ∗
    □ (∀ l' rep' n', list_inv l' rep' n' -∗ ∃ succ, ⌜MemA.compare_val rep' rep = Vint succ⌝).
  Proof.
    iIntros "L"; iAssert (⌜rep = Vint 0 ∨ ∃ b ofs, rep = Vptr (b, ofs)⌝)%I as "%".
    { destruct l; ss; first iPoseProof "L" as "%"; eauto.
      iDestruct "L" as "[% [% [% [% [% [-> ?]]]]]]"; iPureIntro; right; esplits; eauto.
    }
    iAssert (list_inv l rep n ∗ ∃ v q, MemA.val_r (rep) q v)%I
      with "[L]" as "[L [% [% $]]]".
    { destruct rep as [v'|v'|]; eauto. destruct v'; eauto.
      destruct l; eauto.
      { iPoseProof "L" as "%"; clarify. }
      { iDestruct "L" as "[% [% [% [% [% [% [↦ R]]]]]]]". clarify; eauto.
        iDestruct "↦" as "[↦1 ↦2]"; ss; iSplitR "↦1"; last iFrame.
        iExists _, _, _, _, _; iSplit; first done. iFrame "↦2 R".
      }
    }

    iFrame "L".
    iIntros "!> % % % L"; destruct l'; ss.
    { iPoseProof "L" as "->"; des; clarify; eauto. }
    { iPoseProof "L" as "[% [% [% [% [% [-> ?]]]]]]"; des; clarify; iPureIntro; eauto; ss.
      des_ifs; eauto.
    }
  Unshelve. all: try exact Vundef; try exact 1%Qp.
  Qed.

  Definition syn_offer_inv n γo (offer : mblock * ptrofs) (rid : nat) (jid : jobID) : GTerm.t n :=
    (∃ (offerst : τ{Z}),
      (offer.1, offer.2 + 1)%Z ↦ Vint offerst ∗
      if (decide (offerst = 0%Z))
      then offer ↦ jid.2.1.2 ∗ syn_helping_token n rid jid
      else if (decide (offerst = 1)) then syn_helping_done n rid Vundef
      else if (decide (offerst = 2)) then sown γo (Excl ())
      else ⌜False⌝)%SAT.
  Definition offer_inv γo (offer : mblock * ptrofs) (rid : nat) (jid : jobID) : iProp Σ :=
    (∃ (offerst : Z),
      (offer.1, offer.2 + 1)%Z ↦ Vint offerst ∗
      if (decide (offerst = 0%Z))
      then offer ↦ jid.2.1.2 ∗ helping_token rid jid
      else if (decide (offerst = 1)) then helping_done rid Vundef
      else if (decide (offerst = 2)) then own γo (Excl ())
      else ⌜False⌝)%I.
  Global Instance SLRed_offer_inv n γo offer rid jid :
    SLRed n (syn_offer_inv n γo offer rid jid) (offer_inv γo offer rid jid).
  Proof. solve_sl_red; repeat case_decide; ss. Qed.

  Definition syn_is_offer (γs : gname) (offer_rep : val) (n : nat) : GTerm.t n :=
    match offer_rep with
    | Vptr (offerb, offerofs) => 
      ∃ (γo : τ{gname}) (jid : τ{jobID}) (rid : τ{nat}),
        syn_inv offerN (syn_offer_inv n γo (offerb, offerofs) rid jid)
        ∗ ⌜jid.2.2 = γs⌝
    | Vint 0 => ⌜True⌝
    | _ => ⌜False⌝
    end%SAT.

  Definition syn_stack_inv (γs : gname) (stackb : mblock) (stackofs : ptrofs) (n : nat) : GTerm.t n :=
    ((∃ (stack_rep : τ{val}) (offer_rep : τ{val}) (l : τ{list val}), sown γs (● Excl' l) ∗
       (stackb, stackofs) ↦ stack_rep ∗ syn_list_inv l stack_rep n ∗
       (stackb, stackofs + 1)%Z ↦ offer_rep ∗ syn_is_offer γs offer_rep n) ∨
     (∃ (reqmap : τ{gmap nat (option _ * _)}), syn_helping_auth n (1/2)%Qp reqmap))%SAT.

  Definition is_stack (γs : gname) (s : val) (n : nat) : iProp Σ :=
    (∃ (stackb : mblock) (stackofs : ptrofs),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ inv n stackN (syn_stack_inv γs stackb stackofs n))%I.
  Definition syn_is_stack (γs : gname) (s : val) (n : nat) : GTerm.t n :=
    (∃ (stackb : τ{mblock}) (stackofs : τ{ptrofs}),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ syn_inv stackN (syn_stack_inv γs stackb stackofs n))%SAT.
  Global Instance SLRed_is_stack γs s n :
    SLRed n (syn_is_stack γs s n) (is_stack γs s n).
  Proof. solve_sl_red. Qed.

  Definition new_stack_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ n : nat,
        ((λ arg, ∃ (v : list val), ⌜arg = v↑⌝),
         (λ ret, ∃ v γs, ⌜ret = v↑⌝ ∗ is_stack γs v n ∗ stack_content γs []))%I)).

  Definition push_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, s, v, γs) : nat * val * val * gname),
        ((λ arg, ⌜arg = [s; v]↑⌝ ∗ is_stack γs s n),
         (λ ret, ⌜ret = Vundef↑⌝))))%I.

  Definition pop_spec : fspec :=
    fspec_sch (↑N)
      (fspec_simple (λ '((n, s, γs) : nat * val * gname),
        ((λ arg, ⌜arg = [s]↑⌝ ∗ is_stack γs s n),
         (λ ret, True))))%I.
End definitions.

Module StackM. Section StackM.
  Definition jobID : Type := nat * nat * (nat * val * val * gname).
  Definition retID : Type := val.

  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !schGS, !memGS, !stackG jobID retID}.
  Context (mn : string) (N : namespace).

  (* Module definitions *)
  Definition scopes : list string := [].

  Definition jobCode : jobID → itree crisE retID :=
    λ '(_, _, (_, _, v, γs)),
      l <- trigger (Take (list (leibnizO val)));;
      trigger (Assume (stack_content γs l));;;
      trigger (Guarantee (stack_content γs (v :: l)));;;
      Ret Vundef.

  Definition new_stack : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition push : Any.t → itree crisE Any.t :=
    atomic_body (push_spec N) (λ x _, trigger (Call (Helping.run mn) x↑)).

  Definition pop : Any.t → itree crisE Any.t :=
    atomic_body (pop_spec N)
      (λ x _,
        'b : _ <- trigger (Choose bool);;
        (if b : bool then trigger (Call (Helping.help mn) ()↑) else Ret ()↑);;;
        l <- trigger (Take (list (leibnizO val)));;
        trigger (Assume (stack_content x.2.2 l));;;
        trigger (Guarantee (stack_content x.2.2 (tail l)));;;
        let vret := match l with | v :: _ => v | _ => Vundef end in
        Ret (vret↑)).

  Definition fnsems : fnsemmap :=
    {[Some StackHdr.new_stack :=
        Some (msk_scp scopes msk_true, (fsp_some (new_stack_spec N), cfunU new_stack));
      Some StackHdr.push := Some (msk_scp scopes msk_true, (None, push));
      Some StackHdr.pop := Some (msk_scp scopes msk_true, (None, pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp Mod.
End StackM. End StackM.

Module StackA. Section StackA.
  Context `{!crisG Γ Σ α β τ _S _I, !concGS, !schGS, !memGS, !stackG jobID retID}.
  Context (N : namespace).

  (* Module definitions *)
  Definition scopes : list string := [].

  Definition new_stack : list val → itree crisE val :=
    λ _, 𝒴;;; trigger (Choose val).

  Definition push : Any.t → itree crisE Any.t :=
    atomic_body (push_spec N)
      (λ '(_, _, (_, _, v, γs)) _,
        l <- trigger (Take (list (leibnizO val)));;
        trigger (Assume (stack_content γs l));;;
        trigger (Guarantee (stack_content γs (v :: l)));;;
        Ret Vundef↑).

  Definition pop : Any.t → itree crisE Any.t :=
    atomic_body (pop_spec N)
      (λ '(_, _, (_, γs)) _, 
        l <- trigger (Take (list (leibnizO val)));;
        trigger (Assume (stack_content γs l));;;
        trigger (Guarantee (stack_content γs (tail l)));;;
        let vret := match l with | v :: _ => v | _ => Vundef end in
        Ret (vret↑)).

  Definition fnsems : fnsemmap :=
    {[Some StackHdr.new_stack :=
        Some (msk_scp scopes msk_true, (fsp_some (new_stack_spec N), cfunU new_stack));
      Some StackHdr.push := Some (msk_scp scopes msk_true, (None, push));
      Some StackHdr.pop := Some (msk_scp scopes msk_true, (None, pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp Mod.
End StackA. End StackA.