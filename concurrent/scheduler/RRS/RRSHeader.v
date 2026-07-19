Require Export CRIS.common.Common.
From CRIS.modules Require Export SMod Mod.
Require Import ImpPrelude.

Module RRSHdr.
  Definition init         := fnsig "RRS.init" (fntyp (SAny.t) ()).
  Definition _spawn       := fnsig "RRS._spawn" (fntyp (string * SAny.t) ()).
  Definition spawn        := fnsig "RRS.spawn" (fntyp (string * SAny.t) nat).
  Definition yield        := fnsig "RRS.yield" (fntyp () ()).
  Definition yield_global := fnsig "RRS.yield_global" (fntyp () ()).
  Definition get_tid      := fnsig "RRS.get_tid" (fntyp () nat).
End RRSHdr.

Definition RRS : string := "rrs".
Global Opaque RRS.

Module RRS. Section RRS.
  Import Events.

  Context {E : Type → Type}.
  Context `{coreE -< E, callE -< E}.

  Definition yield : itree E Any.t :=
    Seal.sealing "RRS"
      (trigger (Call RRSHdr.yield.1 tt↑)).

  Definition yield_global : itree E unit :=
    Seal.sealing "RRS"
     (iterC ((λ (_: unit),
        b <- trigger (Choose (option bool));;
        match b with
        | None => Ret (inr tt: () + ())
        | Some false => Ret (inl tt: () + ())
        | Some true => 
            ccallU RRSHdr.yield_global tt;;;
            Ret (inl tt: () + ())
        end)) tt).

  (** Currently, we require all threads to terminate simultaneously. **)
  Definition spin : itree E unit :=
    Seal.sealing "RRS"
      (iterC ((fun (_: unit) =>
        Ret (inl tt: () + ())
      )) tt).

End RRS. End RRS.

Section ROUNDROBIN.

  Definition pred_rr (tid: nat) (sz: nat) : nat :=
    match tid with
    | O => pred sz
    | S tid' => tid'
    end.

  Definition succ_rr (tid: nat) (sz: nat) : nat := (S tid) mod sz.

  Lemma pred_succ_id x sz (LT: (x < sz)%nat) :
    pred_rr (succ_rr x sz) sz = x.
  Proof.
    destruct sz; [ss|].
    unfold succ_rr. inv LT.
    { rewrite Nat.Div0.mod_same. unfold pred_rr. ss. }
    { rewrite Nat.mod_small; try nia. unfold pred_rr. des_ifs. }
  Qed.

  Lemma succ_pred_id x sz (LT: (x < sz)%nat) :
    succ_rr (pred_rr x sz) sz = x.
  Proof.
    destruct x.
    { destruct sz; [nia|]. rewrite /pred_rr /succ_rr.
      rewrite Nat.Div0.mod_same. refl. }
    { ss. rewrite /succ_rr. rewrite Nat.mod_small; eauto. }
  Qed.

  Lemma succ_rr_upperbound x sz (LE: (x < sz)%nat) :
    succ_rr x sz < sz.
  Proof.
    inv LE; rewrite /succ_rr.
    { rewrite Nat.Div0.mod_same. nia. }
    { rewrite Nat.mod_small; nia. }
  Qed.

  Lemma pred_rr_upperbound x sz (LE: (x < sz)%nat) :
    pred_rr x sz < sz.
  Proof.
    rewrite /pred_rr. destruct x; nia .
  Qed.

  Lemma pred_rr_subst x sz0 sz1 (RNG: (0 < x < sz0)%nat) (LTSZ: (sz0 <= sz1)%nat) :
    pred_rr x sz0 = pred_rr x sz1.
  Proof.
    unfold pred_rr. destruct x; nia.
  Qed.
  
End ROUNDROBIN.

Notation ℛℛ := (RRS.yield).
Notation ℛ𝒴 := (RRS.yield_global).

Lemma yield_unfold `{E : Type → Type, coreE -< E, callE -< E} :
  @RRS.yield_global E _ _ =
  tau;; b <- trigger (Choose (option bool));;
  match b with
  | None => Ret tt
  | Some false => RRS.yield_global
  | Some true => ccallU RRSHdr.yield_global tt;;; RRS.yield_global
  end.
Proof using.
  rewrite {1}/RRS.yield_global; unseal "RRS"; rewrite unfold_iterC.
  repeat f_equal. ired. repeat f_equal. extensionalities b. destruct b as [[|]|]; ss.
  { ired. f_equal. extensionalities x. rewrite /RRS.yield_global; unseal "RRS"; ss. }
  { ired. rewrite /RRS.yield_global; unseal "RRS"; ss. }
  { ired. done. }
Qed.
