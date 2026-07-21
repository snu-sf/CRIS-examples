Require Import CRIS.common.CRIS.
From CRIS.imp_system Require Import mem.MemHeader mem.MemA.
From CRIS.scheduler Require Import SchHeader SchA.
From CRIS.helping Require Import HelpingHeader HelpingTactics.
From CRIS.elimination_stack Require Export StackHeader.
Require Export CRIS.scheduler.Atomic.

Class stackG `{!crisG Γ Σ α β τ _S _I} := StackG {
  stack_tokG :: inG (exclR unitO) Γ;
  stack_stateG :: inG (authR (optionUR $ exclR (listO (leibnizO val)))) Γ;
  stack_helpingG :: helpingGpreS;
}.
Definition stackΓ : HRA :=
  ##[#[exclR unitO; authR (optionUR $ exclR (listO (leibnizO val)))]; helpingΓ].
Global Instance subG_stackG `{!crisG Γ Σ α β τ _S _I} :
  subG stackΓ Γ → stackG.
Proof. solve_inG. Qed.

Class stackGS `{!crisG Γ Σ α β τ _S _I} := StackGS {
  stack_stackG :: stackG;
  stack_helpingGS :: helpingGS;
}.

Section definitions.
  Context `{!crisG Γ Σ α β τ _S _I, !memGS, !stackGS, !schGS}.
  Context (N : namespace).

  Definition offerN := N .@ "offer".
  Definition stackN := N .@ "stack".

  Definition stack_content (γs : gname) (l : list (leibnizO val)) : iProp Σ :=
    own γs (◯ Excl' l).
  Definition syn_stack_content {n} (γs : gname) (l : list (leibnizO val)) : GTerm.t n :=
    sown γs (◯ Excl' l).
  Global Instance stack_content_red n γs l :
    SLRed n (syn_stack_content γs l) (stack_content γs l).
  Proof. solve_sl_red. Qed.

  Lemma stack_content_exclusive γs l1 l2 :
    stack_content γs l1 -∗ stack_content γs l2 -∗ False.
  Proof. iIntros "Hl1 Hl2". iCombine "Hl1 Hl2" gives %[]%auth_frag_op_valid_1. Qed.

  Fixpoint syn_list_inv (l : list val) (rep : val) (n : nat) : GTerm.t n :=
    match l with
    | nil => ⌜rep = Vint 0⌝
    | v::l => ∃ (blk : τ{mblock}) (ofs : τ{ptrofs}) (rep' : τ{val}) (q0 q1 : τ{Qp}),
        ⌜rep = Vptr (blk, ofs)⌝ ∗
        (blk, ofs) ↦{q0} v ∗ (blk, ofs + 1)%Z ↦{q1} rep' ∗ syn_list_inv l rep' n
    end%SAT.

  Fixpoint list_inv (l : list val) (rep : val) : iProp Σ :=
    match l with
    | nil => ⌜rep = Vint 0⌝
    | v::l => ∃ (blk : mblock) (ofs : ptrofs) (rep' : val) (q0 q1 : Qp),
        ⌜rep = Vptr (blk, ofs)⌝ ∗
        (blk, ofs) ↦{q0} v ∗ (blk, ofs + 1)%Z ↦{q1} rep' ∗ list_inv l rep'
    end%I.

  Global Instance list_inv_SLRed n l rep : SLRed n (syn_list_inv l rep n) (list_inv l rep).
  Proof. revert n rep; induction l; i; solve_sl_red. Qed.
  Local Hint Extern 0 (environments.envs_entails _ (list_inv (_::_) _)) => simpl : core.

  Lemma list_inv_comparable l rep :
    list_inv l rep -∗
    list_inv l rep ∗
    (∃ q v, MemA.val_r rep q v) ∗
    □ (∀ l' rep', list_inv l' rep' -∗ ∃ succ, ⌜MemA.compare_val rep' rep = Vint succ⌝).
  Proof.
    iIntros "L"; iAssert (⌜rep = Vint 0 ∨ ∃ b ofs, rep = Vptr (b, ofs)⌝)%I as "%".
    { destruct l; ss; first iPoseProof "L" as "%"; eauto.
      iDestruct "L" as "[% [% [% [% [% [-> ?]]]]]]"; iPureIntro; right; esplits; eauto.
    }
    iAssert (list_inv l rep ∗ ∃ v q, MemA.val_r (rep) q v)%I
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
    iIntros "!> % % L"; destruct l'; ss.
    { iPoseProof "L" as "->"; des; clarify; eauto. }
    { iPoseProof "L" as "[% [% [% [% [% [-> ?]]]]]]"; des; clarify; iPureIntro; eauto; ss.
      des_ifs; eauto.
    }
  Unshelve. all: try exact Vundef; try exact 1%Qp.
  Qed.

  Definition syn_offer_inv
      n γo (offer : mblock * ptrofs) (rid : nat) (v : val) (γ : gname) : GTerm.t n :=
    (∃ (offerst : τ{Z}),
      (offer.1, offer.2 + 1)%Z ↦ Vint offerst ∗
      if (decide (offerst = 0%Z))
      then offer ↦ v ∗ syn_HelpPend n rid (Some N) (v, γ)↑↑
      else if (decide (offerst = 1)) then syn_HelpDone n rid Vundef↑↑
      else if (decide (offerst = 2)) then sown γo (Excl ())
      else ⌜False⌝)%SAT.
  Definition offer_inv
      γo (offer : mblock * ptrofs) (rid : nat) (v : val) (γ : gname) : iProp Σ :=
    ∃ (offerst : Z),
      (offer.1, offer.2 + 1)%Z ↦ Vint offerst ∗
      if (decide (offerst = 0%Z))
      then offer ↦ v ∗ HelpPend rid (Some N) (v, γ)↑↑
      else if (decide (offerst = 1)) then HelpDone rid (Vundef↑↑)
      else if (decide (offerst = 2)) then own γo (Excl ())
      else ⌜False⌝.
  Global Instance SLRed_offer_inv n γo offer rid v γ :
    SLRed n (syn_offer_inv n γo offer rid v γ) (offer_inv γo offer rid v γ).
  Proof. solve_sl_red; repeat case_decide; ss. Qed.

  Definition syn_is_offer (n : nat) (γs : gname) (offer_rep : val) : GTerm.t n :=
    match offer_rep with
    | Vptr (offerb, offerofs) =>
      ∃ (γ γo : τ{gname}) (v : τ{val}) (rid : τ{nat}),
        syn_hinv offerN γ (syn_offer_inv n γo (offerb, offerofs) rid v γs)
    | Vint 0 => ⌜True⌝
    | _ => ⌜False⌝
    end%SAT.
  Definition is_offer (n : nat) (γs : gname) (offer_rep : val) : iProp Σ :=
    match offer_rep with
    | Vptr (offerb, offerofs) =>
      ∃ (γ γo : gname) (v : val) (rid : nat),
        hinv offerN γ (syn_offer_inv n γo (offerb, offerofs) rid v γs)
    | Vint 0 => ⌜True⌝
    | _ => ⌜False⌝
    end.
  Global Instance SLRed_is_offer n γs offer_rep :
    SLRed n (syn_is_offer n γs offer_rep) (is_offer n γs offer_rep).
  Proof. solve_sl_red. Qed.

  Definition syn_stack_inv (n : nat) (γs : gname) (stackb : mblock) (stackofs : ptrofs) : GTerm.t n :=
    ((∃ (stack_rep : τ{val}) (offer_rep : τ{val}) (l : τ{list val}), sown γs (● Excl' l) ∗
       (stackb, stackofs) ↦ stack_rep ∗ syn_list_inv l stack_rep n ∗
       (stackb, stackofs + 1)%Z ↦ offer_rep ∗ syn_is_offer n γs offer_rep))%SAT.
  Definition stack_inv (n : nat) (γs : gname) (stackb : mblock) (stackofs : ptrofs) : iProp Σ :=
    ∃ (stack_rep offer_rep : val) (l : list val), 
      own γs (● Excl' l) ∗
      (stackb, stackofs) ↦ stack_rep ∗ list_inv l stack_rep ∗
      (stackb, stackofs + 1)%Z ↦ offer_rep ∗ is_offer n γs offer_rep.
  Global Instance SLRed_stack_inv n γs stackb stackofs :
    SLRed n (syn_stack_inv n γs stackb stackofs) (stack_inv n γs stackb stackofs).
  Proof. solve_sl_red. Qed.

  Definition is_stack (n : nat) (γs : gname) (s : val) : iProp Σ :=
    (∃ (stackb : mblock) (stackofs : ptrofs) (γ : gname),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ hinv stackN γ (syn_stack_inv n γs stackb stackofs))%I.
  Definition syn_is_stack (n : nat) (γs : gname) (s : val) : GTerm.t n :=
    (∃ (stackb : τ{mblock}) (stackofs : τ{ptrofs}) (γ : τ{gname}),
      ⌜s = Vptr (stackb, stackofs)⌝ ∗ syn_hinv stackN γ (syn_stack_inv n γs stackb stackofs))%SAT.
  Global Instance SLRed_is_stack γs s n :
    SLRed n (syn_is_stack n γs s) (is_stack n γs s).
  Proof. solve_sl_red. Qed.
End definitions.

Module StackM. Section StackM.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS, !memGS, !stackGS}.
  Context (mn : string).

  (* Module definitions *)
  Definition scopes : list string := [].

  Definition jobCode : SAny.t → itree crisE (SAny.t + SAny.t) := λ arg,
    '(v, γs) : val * gname <- arg↓↓?;;
    l <- trigger (Take (list valO));;
    trigger (Assume (stack_content γs l));;;
    trigger (Guarantee (stack_content γs (v :: l)));;;
    Ret (inr Vundef↑↑).

  Definition new_stack : fbody := λ arg,
    {{{ ∀∀ n, ∃ (v : list val), ⌜arg = v↑⌝ }}}
      𝒴@{Some N};;; trigger (Choose (Any.t * ()))
    {{{ RET ret, ∃ v γs, ⌜ret = v↑⌝ ∗ is_stack N n γs v ∗ stack_content γs [] }}} @ N.

  Definition push : fbody := λ arg,
    {{{ ∀∀ '((v, γs) : val * gname), ∃ (s : val), ⌜arg = [s; v]↑⌝ ∗ ∃ (n : nat), is_stack N n γs s }}}
      trigger (Call (Helping.run mn) (Some N, (v, γs)↑↑)↑);;; 𝒴@{Some N};;; Ret (Vundef↑, ())
    {{{ emp }}} @ N.

  Definition pop : fbody := λ arg,
    {{{ ∀∀ γs, ∃ (s : val), ⌜arg = [s]↑⌝ ∗ ∃ n, is_stack N n γs s }}}
      𝒴@{Some N};;;
        'b : bool <- trigger (Choose bool);;
        (if b then trigger (Call (Helping.help mn) (Some N)↑) else Ret ()↑);;;
        <<{ ∀∀ l, stack_content γs l,
          match l with [] => stack_content γs [] | v :: l => stack_content γs l end }>> @ N
    {{{ ∀∀ l, RET ret, ⌜ret = match l with [] => Vundef | v :: l => v end↑⌝ }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack # (msk_scp scopes msk_true, (None, new_stack));
      fid StackHdr.push # (msk_scp scopes msk_true, (None, push));
      fid StackHdr.pop # (msk_scp scopes msk_true, (None, pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End StackM. End StackM.

Module StackA. Section StackA.
  Context `{!crisG Γ Σ α β τ _S _I, !schGS, !memGS, !stackGS}.

  (* Module definitions *)
  Definition scopes : list string := [].

  Definition new_stack : fbody := λ arg,
    {{{ ∀∀ n, ∃ (v : list val), ⌜arg = v↑⌝ }}}
      𝒴@{Some N};;; trigger (Choose (Any.t * ()))
    {{{ RET ret, ∃ v γs, ⌜ret = v↑⌝ ∗ is_stack N n γs v ∗ stack_content γs [] }}} @ N.

  Definition push : fbody := λ arg,
    {{{ ∀∀ '((v, γs) : val * gname), ∃ (s : val), ⌜arg = [s; v]↑⌝ ∗ ∃ (n : nat), is_stack N n γs s }}}
      <<{ ∀∀ l, stack_content γs l, stack_content γs (v :: l) }>> @ N
    {{{ RET ret, ⌜ret = Vundef↑⌝ }}} @ N.

  Definition pop : fbody := λ arg,
    {{{ ∀∀ γs, ∃ (s : val), ⌜arg = [s]↑⌝ ∗ ∃ n, is_stack N n γs s }}}
      <<{ ∀∀ l, stack_content γs l,
        match l with [] => stack_content γs [] | v :: l => stack_content γs l end }>> @ N
    {{{ ∀∀ l, RET ret, ⌜ret = match l with [] => Vundef | v :: l => v end↑⌝ }}} @ N.

  Definition fnsems : fnsemmap :=
    {[fid StackHdr.new_stack # (msk_scp scopes msk_true, (None, new_stack));
      fid StackHdr.push # (msk_scp scopes msk_true, (None, push));
      fid StackHdr.pop # (msk_scp scopes msk_true, (None, pop))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t := SMod.to_mod ∅ Mod.
End StackA. End StackA.
