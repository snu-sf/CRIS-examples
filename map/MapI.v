Require Import CRIS.
Require Import MemHeader.
Require Export MapHeader.

(*** module I Map
private data := NULL

def init(sz : int) ≡
  data := calloc(sz)

def get(k : int) : int ≡
  return *(data + k)

def set(k : int, v : int) ≡
  *(data + k) := v

def set_by_user(k : int) ≡
  set(k, input())
***)

Module MapI. Section MapI.
  Context `{!crisG Σ Γ α β τ Hinv Hsub}.

  Definition scopes := ["Map"].
  Definition v_hptr := "Map" ↯ "hptr".

  Definition init : list val → itree crisE val :=
    λ varg,
      'sz : Z <- (pargs [Tint] varg)?;;
      'hptr : val <- ccallU MemHdr.alloc [Vint sz];;
      cput v_hptr hptr;;;
      (iterC
         (λ i,
            if (decide (i < sz)%Z)
            then
              vptr <- (vadd hptr (Vint (i * 8)))?;;
              'u : val <- ccallU MemHdr.store [vptr; Vint 0];;
              Ret (inl (i + 1)%Z)
            else
              Ret (inr tt)) 0%Z);;;
      Ret Vundef.

  Definition get : list val → itree crisE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      hptr <- cgetU v_hptr;;
      vptr <- (vadd hptr (Vint (k * 8)))?;;
      'r : val <- ccallU MemHdr.load [vptr];; r <- (unint r)?;;
      Ret (Vint r).

  Definition set : list val → itree crisE val :=
    λ varg,
      '(k, v):_ <- (pargs [Tint; Tint] varg)?;;
      hptr <- cgetU v_hptr;; 
      vptr <- (vadd hptr (Vint (k * 8)))?;;
      'u : val <- ccallU MemHdr.store [vptr; Vint v];;
      Ret Vundef.

  Definition set_by_user : list val → itree crisE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ());;
      ccallU MapHdr.set [Vint k; Vint v].

  Definition fnsems : fnsemmap :=
    {[Some MapHdr.init := Some (msk_scp scopes msk_true, (None, cfunU init));
      Some MapHdr.get := Some (msk_scp scopes msk_true, (None, cfunU get));
      Some MapHdr.set := Some (msk_scp scopes msk_true, (None, cfunU set));
      Some MapHdr.set_by_user := Some (msk_scp scopes msk_true, (None, cfunU set_by_user))]}.
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := {[v_hptr := Some Vnullptr↑]};
  |}.
  Solve All Obligations with mod_tac.

  Definition t : Mod.t := SMod.to_mod ∅ smod.
End MapI. End MapI.
