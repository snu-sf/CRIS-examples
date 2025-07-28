Require Import CRIS.

Require Import MemHeader.
From CRIS.map Require Import Header.

Set Implicit Arguments.

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
  Local Open Scope string_scope.
  Context `{Σ : GRA}.

  Definition scopes := ["Map"].
  Definition v_hptr := "Map" ↯ "hptr".

  Definition init : list val → itree crisE val :=
    λ varg,
      'sz : Z <- (pargs [Tint] varg)?;;
      'hptr : val <- ccallU MemHdr.alloc [Vint sz];;
      cput v_hptr hptr;;;
      (iterC
         (fun i =>
            if (Z_lt_le_dec i sz)
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

  Definition fnsems : fnsems_type :=
    [(Some MapHdr.init, (false, wmask_all, scopes, (None, cfunU init)));
     (Some MapHdr.get,  (false, wmask_all, scopes, (None, cfunU get)));
     (Some MapHdr.set,  (false, wmask_all, scopes, (None, cfunU set)));
     (Some MapHdr.set_by_user, (false, wmask_all, scopes, (None, cfunU set_by_user)))].
  
  Program Definition smod : SMod.t := {|
    SMod.scopes := scopes;
    SMod.fnsems := fnsems;
    SMod.initial_st := [(v_hptr, Vnullptr↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : Mod.t := Seal.sealing CRIS (SMod.to_mod sp_none smod).
End MapI. End MapI.
