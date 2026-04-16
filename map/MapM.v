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
  Context `{!crisG Γ Σ α β τ _S _I, _MAPM: !mapMGS}.

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
    {[ fid MapHdr.init @ init_spec;
       fid MapHdr.get @ get_spec;
       fid MapHdr.set @ set_spec;
       fid MapHdr.set_by_user @ set_by_user_spec
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
    {[fid MapHdr.init # (msk_scp scopes msk_true, (fsp_some init_spec, cfunU MapHdr.init init));
      fid MapHdr.get  # (msk_scp scopes msk_true, (fsp_some get_spec, cfunU MapHdr.get get));
      fid MapHdr.set  # (msk_scp scopes msk_true, (fsp_some set_spec, cfunU MapHdr.set set));
      fid MapHdr.set_by_user # (msk_scp scopes msk_true, (fsp_some set_by_user_spec, cfunU MapHdr.set_by_user set_by_user))]}.

  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_size # 0%Z↑; v_map # (λ (_ : Z), 0%Z)↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t sp := SMod.to_mod sp smod.
End MapM. End MapM.
