Require Import CRIS.
Require Import Cell Time View.

Require Import SchHeader SchA.
Require Import PFMemHeader HistoryRA AtomicRA.
Require Import SystemHeader SystemA.
Require Import MPI.

From iris.algebra Require Import excl agree csum.

Definition one_shotR := csumR (exclR unitO) (agreeR ZO).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot (n : Z) : one_shotR := Cinr (to_agree n).

Section one_shot.
  Context `{!crisG  Γ Σ α β τ _S _I}.

  Class one_shotG := { #[local] one_shot_inG :: inG one_shotR Γ }.

  Definition one_shotΓ : HRA := #[one_shotR].
  Global Instance subG_one_shotG : subG one_shotΓ Γ → one_shotG.
  Proof. solve_inG. Defined.
End one_shot.

Module MPA. Section MPA.
  Context `{!crisG Γ Σ α β τ _S _I, _HIST: !histGS, _ATOMIC: !atomicG, _SYS: !sysGS, _ONESHOT: !one_shotG}.
  Local Existing Instances one_shot_inG.

  (* Invariants *)
  Definition mpN := nroot .@ "mpN".

  Definition mp_inv'_def n (x y : Loc.t) γ γx : GTerm.t n :=
    (∃ (ζ : τ{Cell.t}) (b na : τ{bool}) (Vx V0 : τ{View.t}) (f0 t0 : τ{Time.t}) (FT : τ{Time.lt f0 t0}), 
      let ζ0 : Cell.t := Cell.singleton (Message.message (Val.Vnum 0) V0 na) FT in
      @{Vx} x sw↦{γx} ζ (* flag *)
      ∗ match b with
        | false => ⌜ζ = ζ0⌝
        | true =>
            ∃ (t1 f1 : τ{Time.t}) (V1 : τ{View.t}),
              ⌜Time.lt t0 t1 ∧ Cell.add ζ0 f1 t1 (Message.message (Val.Vnum 1) V1 false) ζ⌝ ∗
              (sown γ Pending ∨ @{V1} y ↦ Val.Vnum 42) (* data *)
        end)%SAT.
  Definition mp_inv'_aux : seal (@mp_inv'_def). Proof. by eexists. Qed.
  Definition mp_inv' := unseal (@mp_inv'_aux).
  Definition mp_inv'_eq : @mp_inv' = _ := seal_eq _.
  Definition mp_inv n x y γ γx : iProp Σ := inv n mpN (mp_inv' n x y γ γx).

  (* Specifications *)
  Definition mp_spec : fspec :=
    fspec_winv ⊤ (fspec_simple (λ _ : unit, (λ arg, ⌜arg = tt↑⌝, λ ret, ⌜ret = (Val.Vnum 42)↑⌝)))%I.

  Definition mp2_precondition : TView.t → SAny.t → SAny.t → iProp Σ :=
    λ V varg arg,
      (∃ (loc : Loc.t) (γ γx : gname) (V0 : View.t) (f t : Time.t) (LT : Time.lt f t) (na : bool),
        ⌜varg = (Val.Vptr loc)↑↑ ∧ arg = varg⌝ ∗
        mp_inv 0 (loc >> 0) (loc >> 1) γ γx ∗
        @{TView.cur V} (loc >> 1) ↦ Val.Vnum 0 ∗
        @{TView.cur V} loc sw⊒{γx} Cell.singleton (Message.message (Val.Vnum 0) V0 na) LT)%I.

  Definition mp2_spec : fspec :=
    fspec_winv ⊤
      (fspec_virtual (λ '(tid, stid),
        (λ (varg : SAny.t) arg,
          ∃ sarg V, ⌜ arg = sarg↑ ⌝ ∗ mp2_precondition V varg sarg ∗ tview_sys tid stid V,
        λ (_ : SAny.t) _, ∃ V, tview_sys tid stid V)))%I.

  Definition main_spec : fspec :=
    fspec_winv ⊤
      (fspec_simple
        (λ (_ : unit), ((λ _, tview_sys 1%positive 0 (TView.init [])), (λ _, True))))%I.

  Definition sp : specmap :=
    {[fid MPHdr.mp2 @ mp2_spec]}.

  (* module definition *)
  Definition scopes : list string := [].
  Definition mp2 : Val.t → itree crisE Val.t :=
    λ _, 𝒴;;; Ret Val.zero.

  Definition mp : Any.t → itree crisE Any.t :=
    λ _,
      𝒴;;;
        m <- trigger (Choose Val.t);;
        '_ : () <- ccallU SystemHdr.spawn (MPHdr.mp2.1, m↑↑);;
      iterC (λ _,
        𝒴;;;
        'b : bool <- trigger (Choose bool);;
        if b then Ret (inr tt) else Ret (inl tt)) ();;;
      Ret (Val.Vnum 42)↑.

  Definition fnsems : fnsemmap :=
    {[fid MPHdr.mp2 # (msk_scp scopes msk_true, (fsp_some mp2_spec, (cfunN (fntyp _ _) (sfunN MPHdr.mp2 mp2))));
      entry         # (msk_scp scopes msk_true, (fsp_some main_spec, mp))]}.

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := ∅;
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp : Mod.t := SMod.to_mod sp Mod.
End MPA. End MPA.
