Require Import CRIS.
Require Export MapHeader.

(* Resource algebra for MapI ⊆ MapM *)

Class mapMGpreS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mapM_inG :: inG (exclR unitO) Γ;
}.
Class mapMGS `{!crisG Γ Σ α β τ _S _I} := {
  #[local] mapMGS_mapMGpreS :: mapMGpreS;
  mapM_name : gname;
}.
Definition mapMΓ : HRA := #[exclR unitO].
Global Instance subG_mapMG `{!crisG Γ Σ α β τ _S _I} : subG mapMΓ Γ → mapMGpreS.
Proof. solve_inG. Defined.

Module MapM. Section MapM.
  Context `{!crisG Γ Σ α β τ _S _I, _CONC: !concGS, _MAPM: !mapMGS}.

  Definition pending : iProp Σ := own mapM_name (Excl ()).

  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof. rewrite /pending. iIntros "P1 P2"; iCombine "P1 P2" as "P" gives %CONT; ss. Qed.

  Definition init_spec : fspec :=
    fspec_simple
      (λ (sz : nat),
        (λ varg, ⌜varg = [Vint sz]↑ ∧ (8 * sz < modulus_64)%Z⌝ ∗ pending,
         λ vret, emp))%I.

  Definition get_spec : fspec := 
    fspec_simple
      (λ k,
        (λ varg, ⌜varg = [Vint k]↑⌝,
         λ vret, emp))%I.

  Definition set_spec : fspec :=
    fspec_simple
      (λ '(k, v),
        (λ varg, ⌜varg = ([Vint k; Vint v])↑⌝,
         λ vret, emp))%I.

  Definition set_by_user_spec : fspec := 
    fspec_simple
      (λ k,
        (λ varg, ⌜varg = [Vint k]↑⌝,
         λ vret, emp))%I.

  Definition sp : specmap :=
    {[ speckey_fn MapHdr.init := fspec_to_rel init_spec;
       speckey_fn MapHdr.get := fspec_to_rel get_spec;
       speckey_fn MapHdr.set := fspec_to_rel set_spec;
       speckey_fn MapHdr.set_by_user := fspec_to_rel set_by_user_spec
    ]}.

  (*** module M Map
  private map := (fun k => 0)
  private size := 0

  def init(sz : int) ≡
    size := sz

  def get(k : int) : int ≡
    assume(0 ≤ k < size)
    return map[k]

  def set(k : int, v : int) ≡
    assume(0 ≤ k < size)
    map := map[k ← v]

  def set_by_user(k : int) ≡
    set(k, input())
  ***)

  Definition scopes := ["Map"].
  Definition v_size := "Map" ↯ "size".
  Definition v_map := "Map" ↯ "map".

  Definition init : list val → itree crisE val :=
    λ varg,
      size <- (pargs [Tint] varg)?;;
      cput v_size size;;;
      Ret Vundef.
  
  Definition get : list val → itree crisE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      size <- cgetU v_size;;
      assume(0 <= k < size)%Z;;;
      f <- cgetU v_map;;
      Ret (Vint (f k)).

  Definition set : list val → itree crisE val :=
    λ varg,
      '(k, v):_ <- (pargs [Tint; Tint] varg)?;;
      size <- cgetU v_size;;
      assume(0 <= k < size)%Z;;;
      f <- cgetU v_map;;
      cput v_map (<[k:=v]> (f : Z → Z));;;
      Ret Vundef.

  Definition set_by_user : list val → itree crisE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ());;
      ccallU MapHdr.set [Vint k; Vint v].

  Definition fnsems : fnsemmap :=
    {[Some MapHdr.init := Some (msk_scp scopes msk_true, (fsp_some init_spec, cfunU init));
      Some MapHdr.get := Some (msk_scp scopes msk_true, (fsp_some get_spec, cfunU get));
      Some MapHdr.set := Some (msk_scp scopes msk_true, (fsp_some set_spec, cfunU set));
      Some MapHdr.set_by_user := Some (msk_scp scopes msk_true, (fsp_some set_by_user_spec, cfunU set_by_user))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_size := Some 0%Z↑; v_map := Some (λ (_ : Z), 0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MapM. End MapM.