Require Import CRIS.

Require Import MemHeader.
Require Import MapHeader.

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

  Definition init : list val → itree pmodE val :=
    λ varg,
      'sz : Z <- (pargs [Tint] varg)?;;
      'hptr : val <- ccallU MemName.alloc [Vint sz];;
      cput v_hptr hptr;;;
      (ITree.iter
         (fun i =>
            if (Z_lt_le_dec i sz)
            then
              vptr <- (vadd hptr (Vint (i * 8)))?;;
              'u : val <- ccallU MemName.store [vptr; Vint 0];;
              Ret (inl (i + 1)%Z)
            else
              Ret (inr tt)) 0%Z);;;
      Ret Vundef.

  Definition get : list val → itree pmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      hptr <- cgetU v_hptr;;
      vptr <- (vadd hptr (Vint (k * 8)))?;;
      'r : val <- ccallU MemName.load [vptr];; r <- (unint r)?;;
      Ret (Vint r).

  Definition set : list val → itree pmodE val :=
    λ varg,
      '(k, v):_ <- (pargs [Tint; Tint] varg)?;;
      hptr <- cgetU v_hptr;; 
      vptr <- (vadd hptr (Vint (k * 8)))?;;
      'u : val <- ccallU MemName.store [vptr; Vint v];;
      Ret Vundef.

  Definition set_by_user : list val → itree pmodE val :=
    λ varg,
      k <- (pargs [Tint] varg)?;;
      v <- trigger (IO "input" ());;
      ccallU MapName.set [Vint k; Vint v].

  Definition fnsems :=
    [(MapName.init, (scopes, cfunU init));
     (MapName.get,  (scopes, cfunU get));
     (MapName.set,  (scopes, cfunU set));
     (MapName.set_by_user, (scopes, cfunU set_by_user))].
  
  Program Definition Mod : PMod.t := {|
    PMod.scopes := scopes;
    PMod.fnsems := fnsems;
    PMod.initial_st := [(v_hptr, Vnullptr↑)];
  |}.
  Solve All Obligations with prove_scope.
  Next Obligation. prove_nodup. Qed.

  Definition t : HMod.t := Seal.sealing CRIS (PMod.to_hmod Mod).
End MapI. End MapI.
