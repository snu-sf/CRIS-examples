From Stdlib Require Import List Orders MSetList ZArith.

Require Import sflib Coqlib.

Require Import Basic DataStructure Language.
Require Import Loc Val Ordering.

Set Implicit Arguments.


(* NOTE (syscall): In fact, syscalls may change the memory, on the
 * contrary to what is currently defined.
 *)
(* NOTE (syscall): we disallow syscalls in the validation of the
 * consistency check, as syscall's results are not predictable.
 *)
Module Event.
  Structure t := mk {
    output: Z;
    inputs: list Z;
  }.

  Definition le (e0 e1: t): Prop :=
    e0.(output) = e1.(output) /\ Forall2 Z.eq e0.(inputs) e1.(inputs).
    (* e0.(output) = e1.(output) /\ Forall2 Val.le e0.(inputs) e1.(inputs). *)

  (* TODO: PromisingLib *)
  Global Program Instance PreOrder_Forall2 A R `{PreOrder A R}: PreOrder (Forall2 R).
  (*Next Obligation.*)
  (*Proof.*)
  (*  ii. induction x; ss. econs; ss. refl.*)
  (*Qed.*)
  (*Next Obligation.*)
  (*Proof.*)
  (*  intros x. induction x; ii.*)
  (*  { inv H0; inv H1. econs. }*)
  (*  { inv H0; inv H1. econs; eauto. etrans; eauto. }*)
  (*Qed.*)

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. red. splits; ss. refl.
  Qed.
  Next Obligation.
    ii. unfold le in *. des. splits; ss.
    { etrans; eauto. }
    { etrans; eauto. }
  Qed.
End Event.


Module MachineEvent.
  Inductive t :=
  | silent
  | syscall (e: Event.t)
  | failure
  .
End MachineEvent.


Module ProgramEvent.
  Inductive t :=
  | silent
  | read (loc:Loc.t) (val:Val.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Val.t) (ord:Ordering.t)
  | faa (loc:Loc.t) (valr addendum:Val.t) (ordr ordw:Ordering.t)
  | cas (loc:Loc.t) (valr old new:Val.t) (valret:option bool) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  | failure
  | alloc (loc:Loc.t) (size: Z)
  | free (loc:Loc.t)
  | ptr_eq (loc1 loc2:Loc.t) (valret:option bool)
  .

  Definition is_reading (e:t): option (Loc.t * Val.t * Ordering.t) :=
    match e with
    | read loc val ord => Some (loc, val, ord)
    | faa loc valr _ ordr _ => Some (loc, valr, ordr)
    | cas loc valr _ _ _ ordr _ => Some (loc, valr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Val.t * Ordering.t) :=
    match e with
    | write loc val ord => Some (loc, val, ord)
    | faa loc valr addendum _ ordw => Some (loc, Val.add valr addendum, ordw)
    | cas loc _ _ valw valret _ ordw => match valret with
                                        | Some true => Some (loc, valw, ordw)
                                        | _ => None
                                        end
    | _ => None
    end.

  Definition is_updating (e:t): option (Loc.t * Val.t * Ordering.t) :=
    match e with
    | faa loc valr _ ordr _ => Some (loc, valr, ordr)
    | cas loc valr _ _ valret ordr _ => match valret with
                                        | Some true => Some (loc, valr, ordr)
                                        | _ => None
                                        end
    | _ => None
    end.

  Inductive ord: forall (e1 e2:t), Prop :=
  | ord_silent:
      ord silent silent
  | ord_read
      l v o1 o2
      (O: Ordering.le o1 o2):
      ord (read l v o1) (read l v o2)
  | ord_write
      l v o1 o2
      (O: Ordering.le o1 o2):
      ord (write l v o1) (write l v o2)
  | ord_faa
      l vr vw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (faa l vr vw or1 ow1) (faa l vr vw or2 ow2)
  | ord_cas
      l vr vold vnew vret or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (cas l vr vold vnew vret or1 ow1) (cas l vr vold vnew vret or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (fence or1 ow1) (fence or2 ow2)
  | ord_syscall
      e:
      ord (syscall e) (syscall e)
  | ord_failure:
      ord failure failure
  | ord_alloc
    l sz:
      ord (alloc l sz) (alloc l sz)
  | ord_free
    l:
      ord (free l) (free l)
  | ord_eq
      loc1 loc2 valret:
      ord (ptr_eq loc1 loc2 valret) (ptr_eq loc1 loc2 valret)
  .

  Definition opt_bool_le (lhs rhs: option bool): Prop :=
    match lhs, rhs with
    | None, _ => True
    | Some b0, Some b1 => b0 = b1
    | _, _ => False
    end.

  Program Instance opt_bool_le_PreOrder: PreOrder opt_bool_le.
  Next Obligation.
    ii. destruct x; refl.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss; eauto.
  Qed.

  Definition le (e0 e1: t): Prop :=
    match e0, e1 with
    | write loc0 val0 ord0, write loc1 val1 ord1 =>
      loc0 = loc1 /\ Val.le val0 val1 /\ ord0 = ord1
    | faa loc0 valr0 valw0 ordr0 ordw0, faa loc1 valr1 valw1 ordr1 ordw1 =>
      loc0 = loc1 /\ valr0 = valr1 /\ Val.le valw0 valw1 /\ ordr0 = ordr1 /\ ordw0 = ordw1
    | cas loc0 valr0 valold0 valnew0 valret0 ordr0 ordw0,
      cas loc1 valr1 valold1 valnew1 valret1 ordr1 ordw1 =>
      loc0 = loc1 /\ valr0 = valr1 /\ valold0 = valold1 /\ Val.le valnew0 valnew1 /\
      valret0 = valret1 /\ ordr0 = ordr1 /\ ordw0 = ordw1
    | syscall e0, syscall e1 => Event.le e0 e1
    (* | ptr_eq loc01 loc02 valret0, ptr_eq loc11 loc12 valret1 => *)
    (*   loc01 = loc11 /\ loc02 = loc12 /\ opt_bool_le valret0 valret1 *)
    | _, _ => e0 = e1
    end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss; splits; try refl.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss; des; subst; splits; etrans; eauto.
  Qed.
End ProgramEvent.

Definition language: Type := Language.t ProgramEvent.t.
