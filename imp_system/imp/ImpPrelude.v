Require Import CRIS.
Require Export GEnv.

Set Implicit Arguments.

Local Open Scope nat_scope.

Notation mblock := nat (only parsing).
Notation ptrofs := Z (only parsing).

Inductive gdef :=
| Gfun
| Gvar (gv : Z)
.

Inductive val : Type :=
| Vint (n : Z) : val
| Vptr (blkofs : mblock * ptrofs) : val
| Vundef
.

Global Program Instance val_dec : Dec val.
Next Obligation.
  repeat (decide equality).
Defined.
Global Instance val_deq_eq : EqDecision val.
Proof. intros x y; destruct (dec x y); [left|right]; ss. Qed.

Global Instance val_countable : Countable val.
Proof.
  refine (inj_countable'
   (λ v, match v with Vint v => Some (inl v) | Vptr blkofs => Some (inr blkofs) | Vundef => None end)
   (λ v,
    match v with
    | Some (inl v) => Vint v
    | Some (inr bofs) => Vptr bofs
    | None => Vundef
    end) _).
   by intros [].
Defined.
Global Instance val_inhabited : Inhabited val := populate Vundef.

Definition wordsize_64 := 64.
Definition modulus_64 := two_power_nat wordsize_64.
Definition modulus_64_half := (modulus_64 / 2)%Z.
Definition max_64 := (modulus_64_half - 1)%Z.
Definition min_64 := (- modulus_64_half)%Z.

Definition intrange_64 : Z -> bool := fun z => (Z_le_gt_dec min_64 z) && (Z_le_gt_dec z max_64).
Definition modrange_64 : Z -> bool := fun z => (Z_le_gt_dec 0 z) && (Z_lt_ge_dec z modulus_64).


Ltac unfold_intrange_64 := unfold intrange_64, min_64, max_64 in *; unfold modulus_64_half, modulus_64, wordsize_64 in *.
Ltac unfold_modrange_64 := unfold modrange_64, modulus_64, wordsize_64 in *.

Definition scale_ofs (ofs : Z) := (8 * ofs)%Z.

Definition wf_val (v : val) :=
  match v with
  | Vint z => intrange_64 z
  | Vptr (_, z) => modrange_64 (scale_ofs z)
  | Vundef => false
  end.

Definition Vnullptr := Vint 0.

Definition scale_int (n : Z) : option Z :=
  if (Zdivide_dec 8 n) then Some (Z.div n 8) else None.

Definition vadd (x y : val) : option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.add n m))
  | Vptr (blk, ofs), Vint n =>
    scaled_n ← scale_int n; Some (Vptr (blk, Z.add ofs scaled_n))
  | Vint n, Vptr (blk, ofs) =>
    scaled_n ← scale_int n; Some (Vptr (blk, Z.add scaled_n ofs))
  | _, _ => None
  end
.

Definition vsub (x y : val) : option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.sub n m))
  | Vptr (blk, ofs), Vint n =>
    scaled_n ← scale_int n; Some (Vptr (blk, Z.sub ofs scaled_n))
  | Vptr (blk1, ofs1), Vptr (blk2, ofs2) =>
    if (Nat.eqb blk1 blk2) then Some (Vint (scale_ofs (ofs1 - ofs2))) else None
  | _, _ => None
  end
.

Definition vmul (x y : val) : option val :=
  match x, y with
  | Vint n, Vint m => Some (Vint (Z.mul n m))
  | _, _ => None
  end
.

Definition unptr (v : val) : option (mblock * ptrofs) :=
  match v with
  | Vptr bofs => Some bofs 
  | _ => None
  end.

Definition unint (v : val) : option Z :=
  match v with
  | Vint x => Some x
  | _ => None
  end.

Definition unbool (v : val) : option bool :=
  match v with
  | Vint x => Some (if (dec x 0%Z) then false else true)
  | _ => None
  end.

Definition unblk (v : val) : option mblock :=
  match v with
  | Vptr (b, ofs) =>
    if (Z.eq_dec ofs 0) then Some b else None
  | _ => None
  end.

Variant val_type : Set :=
| Tint
| Tbool
| Tptr
| Tblk
| Tuntyped
.

Definition val_type_sem (t : val_type) : Set :=
  match t with
  | Tint => Z
  | Tbool => bool
  | Tptr => (mblock * ptrofs)
  | Tblk => mblock
  | Tuntyped => val
  end.

Fixpoint val_types_sem (ts : list val_type) : Set :=
  match ts with
  | [] => unit
  | [hd] => val_type_sem hd
  | hd::tl => val_type_sem hd * val_types_sem tl
  end.

Definition parg (t : val_type) (v : val) : option (val_type_sem t) :=
  match t with
  | Tint => unint v
  | Tbool => unbool v
  | Tptr => unptr v
  | Tblk => unblk v
  | Tuntyped => Some v
  end.

Definition pargs (ts : list val_type) :
  forall (vs : list val), option (val_types_sem ts).
Proof.
  induction ts as [|thd ttl].
  - intros [|]; simpl.
    + exact (Some tt).
    + exact None.
  - simpl. destruct ttl as [|].
    + intros [|vhd []]; simpl.
      * exact None.
      * exact (parg thd vhd).
      * exact None.
    + intros [|vhd vtl].
      * exact None.
      * exact (match parg thd vhd with
               | Some vhd' =>
                 match IHttl vtl with
                 | Some vtl' => Some (vhd', vtl')
                 | None => None
                 end
               | None => None
               end).
Defined.

Arguments pargs : simpl never.

Definition imp_fun_t := fntyp (list val) val.
