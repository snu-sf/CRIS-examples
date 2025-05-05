Require Import CRIS.

Require Import MapHeader.

Set Implicit Arguments.

(* Resource algebra for MapI ⊆ MapM *)
Section RA.
  Context `{!sinvG Γ Σ α β τ _I _S}.
  
  Class mapMG `{!sinvG Γ Σ α β τ _I _S} := {
    mapM_inG :: inG (exclR unitO) Γ;
  }.
  Definition mapMΓ : HRA := #[exclR unitO].
  Global Instance subG_mapMG : subG mapMΓ Γ → mapMG.
  Proof. solve_inG. Defined.
End RA.
Hint Unfold subG_mapMG mapM_inG : GRA_index.

Module MapMS. Section MapMS.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_mapMG: !mapMG}.

  Definition pending : iProp Σ := own base_γ (Excl ()).
  Lemma pending_unique : pending -∗ pending -∗ False.
  Proof.
    rewrite /pending; unseal "MapMS".
    iIntros "P1 P2"; iCombine "P1 P2" as "P" gives %CONT; ss.
  Qed.

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

  Definition sp : alist string fspec :=
    Seal.sealing CRIS
      [(MapHdr.init, init_spec);
       (MapHdr.get, get_spec);
       (MapHdr.set, set_spec);
       (MapHdr.set_by_user, set_by_user_spec)].

  Lemma sp_nodup : List.NoDup (List.map fst sp).
  Proof. by rewrite /sp; unseal CRIS; prove_nodup. Qed.
End MapMS. End MapMS.

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
Module MapM. Section MapM.
  Context `{_sinvG: !sinvG Γ Σ α β τ _I _S}.
  Context `{_mapMG: !mapMG}.

  Definition scopes := ["Map"].
  Definition v_size := "Map" ↯ "size".
  Definition v_map := "Map" ↯ "map".

  Definition init : list val → itree hmodE val :=
    λ varg,
      size <- (pargs [Tint] varg)?;;
      cput v_size size;;;
      Ret Vundef.
  
  Definition get : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      size <- cgetU v_size;;
      assume(0 <= k < size)%Z;;;
      f <- cgetU v_map;;
      Ret (Vint (f k)).

  Definition set : list val → itree hmodE val :=
    λ varg,
      '(k, v):_ <- (pargs [Tint; Tint] varg)?;;
      size <- cgetU v_size;;
      assume(0 <= k < size)%Z;;;
      f <- cgetU v_map;;
      cput v_map (<[k:=v]> (f : Z → Z));;;
      Ret Vundef.

  Definition set_by_user : list val → itree hmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ());;
      ccallU MapHdr.set [Vint k; Vint v].

  Definition fnsems :=
    [(MapHdr.init, (wmask_all, scopes, mk_specbody MapMS.init_spec (cfunU init)));
     (MapHdr.get, (wmask_all, scopes, mk_specbody MapMS.get_spec (cfunU get)));
     (MapHdr.set, (wmask_all, scopes, mk_specbody MapMS.set_spec (cfunU set)));
     (MapHdr.set_by_user, (wmask_all, scopes, mk_specbody MapMS.set_by_user_spec (cfunU set_by_user)))].

  Program Definition Mod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_size, 0%Z↑);
                        (v_map,  (λ (_ : Z), 0%Z)↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition init_cond : iProp Σ := emp%I.

  Definition t Sp := Seal.sealing CRIS (@SMod.to_hmod Σ Sp Mod).
End MapM. End MapM.
