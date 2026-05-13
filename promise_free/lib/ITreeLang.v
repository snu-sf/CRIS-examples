Require Import CRIS.

From ITree Require Export
     ITree
     ITreeFacts
     Events.MapDefault
     Events.State
     Events.StateFacts
     EqAxiom
     Subevent
.
From ExtLib Require Export
     Functor FunctorLaws
     Structures.Maps
.

Require Export ITreelib.

Require Import Basic.
Require Import Loc.
Require Import Val.
Require Import Language.

Require Import Event.
Require Import Ordering.
From Stdlib Require Export Program.

Open Scope cat_scope.
Open Scope monad_scope.
Open Scope itree_scope.

Set Implicit Arguments.

CoFixpoint itree_spin {E R} : itree E R := Tau itree_spin.

Module MemE.
  Variant t: Type -> Type :=
  | read (loc: Loc.t) (ord: Ordering.t): t Val.t
  | write (loc: Loc.t) (val: Val.t) (ord: Ordering.t): t unit
  | cas (loc: Loc.t) (old new:Val.t) (ordr ordw: Ordering.t): t (option bool)
  | faa (loc: Loc.t) (addendum:Val.t) (ordr ordw: Ordering.t): t Val.t
  | fence (ordr ordw: Ordering.t): t unit
  | alloc (size: Z): t Loc.t
  | free (loc: Loc.t): t unit
  | syscall (args: list Z): t Z
  | abort: t void
  | choose: t Z
  | ptr_eq (loc1 loc2: Loc.t): t (option bool)
  .

  Variant ord: forall R (i_src i_tgt:t R), Prop :=
  | ord_read
      l o1 o2 (O: Ordering.le o1 o2):
      ord (read l o1) (read l o2)
  | ord_write
      l v o1 o2 (O: Ordering.le o1 o2):
      ord (write l v o1) (write l v o2)
  | ord_faa
      l addendum or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (faa l addendum or1 ow1) (faa l addendum or2 ow2)
  | ord_cas
      l old new or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (cas l old new or1 ow1) (cas l old new or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (fence or1 ow1) (fence or2 ow2)
  | ord_alloc
      size:
      ord (alloc size) (alloc size)
  | ord_free
      l:
      ord (free l) (free l)
  | ord_syscall
      args:
      ord (syscall args) (syscall args)
  | ord_abort:
      ord abort abort
  | ord_choose:
      ord choose choose
  | ord_eq
      loc1 loc2:
      ord (ptr_eq loc1 loc2) (ptr_eq loc1 loc2)
  .

  Variant get_memory_event: forall R (e: ProgramEvent.t) (me: option (t R)), Prop :=
    | get_memory_event_read
        loc val ord:
      get_memory_event (ProgramEvent.read loc val ord) (Some (read loc ord))
    | get_memory_event_write
        loc val ord:
      get_memory_event (ProgramEvent.write loc val ord) (Some (write loc val ord))
    | get_memory_event_faa
        loc valr addendum ordr ordw:
      get_memory_event (ProgramEvent.faa loc valr addendum ordr ordw)
        (Some (faa loc addendum ordr ordw))
    | get_memory_event_cas
        loc valr old new valret ordr ordw:
      get_memory_event (ProgramEvent.cas loc valr old new valret ordr ordw)
        (Some (cas loc old new ordr ordw))
    | get_memory_event_fence
        ordr ordw:
      get_memory_event (ProgramEvent.fence ordr ordw) (Some (fence ordr ordw))
    | get_memory_event_syscall
        e:
      get_memory_event (ProgramEvent.syscall e) (Some (syscall (Event.inputs e)))
    | get_memory_event_failure:
      get_memory_event (ProgramEvent.failure) (Some (abort))
    | get_memory_event_alloc
        loc size:
      get_memory_event (ProgramEvent.alloc loc size) (Some (alloc size))
    | get_memory_event_free
        loc:
      get_memory_event (ProgramEvent.free loc) (Some (free loc))
    | get_memory_event_ptr_eq
        loc1 loc2 b:
      get_memory_event (ProgramEvent.ptr_eq loc1 loc2 b) (Some (ptr_eq loc1 loc2))
    | get_memory_event_silent:
      @get_memory_event void (ProgramEvent.silent) None
  .

  Lemma get_memory_event_exists e:
    exists R me, @get_memory_event R e me.
  Proof.
    destruct e; ss; esplits; econs.
  Qed.
End MemE.


Module ILang.
  Definition is_terminal R (s: itree MemE.t R): Prop :=
    exists r, s = Ret r.

  Inductive step R:
    forall (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | step_tau
      (itr: itree MemE.t R)
      itr1 (EQ: itr1 = itr)
    :
      @step R ProgramEvent.silent
            (Tau itr)
            itr1
  | step_choose
      (k: Z -> itree MemE.t R) n
      itr1 (EQ: itr1 = k n)
    :
      @step R ProgramEvent.silent
            (Vis (MemE.choose) k)
            itr1
  | step_read
      (k: Val.t -> itree MemE.t R) loc val ord
      itr1 (EQ: itr1 = k val)
    :
      @step R (ProgramEvent.read loc val ord)
            (Vis (MemE.read loc ord) k)
            itr1
  | step_write
      (k: unit -> itree MemE.t R) loc val ord
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.write loc val ord)
            (Vis (MemE.write loc val ord) k)
            itr1
  | step_faa
      (k: Val.t -> itree MemE.t R) loc addendum valr ordr ordw
      itr1 (EQ: itr1 = k valr)
    :
      @step R (ProgramEvent.faa loc valr addendum ordr ordw)
            (Vis (MemE.faa loc addendum ordr ordw) k)
            itr1
  | step_cas
      (k: option bool -> itree MemE.t R) valr loc old new valret ordr ordw
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.cas loc valr old new valret ordr ordw)
            (Vis (MemE.cas loc old new ordr ordw) k)
            itr1
  | step_fence
      (k: unit -> itree MemE.t R) ordr ordw
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.fence ordr ordw)
            (Vis (MemE.fence ordr ordw) k)
            itr1
  | step_alloc
      (k: Loc.t -> itree MemE.t R) loc size
      itr1 (EQ: itr1 = k loc)
    :
      @step R (ProgramEvent.alloc loc size)
            (Vis (MemE.alloc size) k)
            itr1
  | step_free
      (k: unit -> itree MemE.t R) loc
      itr1 (EQ: itr1 = k tt)
    :
      @step R (ProgramEvent.free loc)
            (Vis (MemE.free loc) k)
            itr1
  | step_syscall
      (k: Z -> itree MemE.t R) valret args
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.syscall (Event.mk valret args))
            (Vis (MemE.syscall args) k)
            itr1
  | step_abort
      (k: void -> itree MemE.t R)
    :
      @step R (ProgramEvent.failure)
            (Vis (MemE.abort) k)
            itree_spin
  | step_ptr_eq
      (k: option bool -> itree MemE.t R) valret loc1 loc2
      itr1 (EQ: itr1 = k valret)
    :
      @step R (ProgramEvent.ptr_eq loc1 loc2 valret)
            (Vis (MemE.ptr_eq loc1 loc2) k)
            itr1
  .
  #[export] Hint Constructors step: core.

  Variant opt_step R:
    forall (e:ProgramEvent.t) (s1: itree MemE.t R) (s2: itree MemE.t R), Prop :=
  | opt_step_none
      (st: itree MemE.t R):
      opt_step ProgramEvent.silent st st
  | opt_step_some
      e (st1 st2: itree MemE.t R)
      (STEP: step e st1 st2):
      opt_step e st1 st2
  .
End ILang.

From Paco Require Import paco.

Lemma bind_spin E A B (k: ktree E A B):
  itree_spin >>= k = itree_spin.
Proof.
  apply bisim_is_eq. revert k. pcofix CIH.
  i. pfold. red.
  change (observe (itree_spin: itree E B)) with (@TauF E B _ (itree_spin: itree E B)).
  change (observe (itree_spin >>= k)) with (@TauF E B _ (itree_spin >>= k)).
  econs. right. auto.
Qed.

Lemma lang_step_deseq
      R0 R1 ktr (itr1: itree MemE.t R0) (itr2: itree MemE.t R1) e
      (STEP: ILang.step e
                        (itr1 >>= ktr)
                        itr2):
  (exists r,
      itr1 = Ret r /\
      ILang.step e (ktr r) itr2) \/
  (exists itr2',
      itr2 = itr2' >>= ktr /\
      ILang.step e itr1 itr2') \/
  (itr1 = Vis MemE.abort (Empty_set_rect _) /\
   e = ProgramEvent.failure)
.
Proof.
  ides itr1.
  { rewrite bind_ret_l in STEP. left. esplits; eauto. }
  { rewrite bind_tau in STEP. dependent destruction STEP.
    right. left. esplits; eauto. econs. eauto. }
  { rewrite bind_vis in STEP.
    dependent destruction STEP; try by (right; left; esplits; eauto; econs; eauto).
    right. right. splits; auto. f_equal. f_equal. extensionality v. ss. }
Qed.

Lemma lang_step_bind R0 R1
      (itr0 itr1: itree MemE.t R0) (k: R0 -> itree MemE.t R1) e
      (STEP: ILang.step e itr0 itr1):
  ILang.step e
             (itr0 >>= k)
             (itr1 >>= k).
Proof.
  dependent destruction STEP; subst; ired; try rewrite bind_vis; try econs; eauto.
  rewrite bind_spin. econs; eauto.
Qed.


Module Op2.
  Variant t :=
  | add
  | sub
  | mul
  .

  Definition eval (op:t): forall (op1 op2:Val.t), Val.t :=
    match op with
    | add => Val.add
    | sub => Val.sub
    | mul => Val.mul
    end.

End Op2.

Definition reg_type := nat.

Module Operand.
  Variant t :=
  | const (z : Z)
  | register (r : reg_type)
  .
End Operand.

Module Inst.
  Definition reg := reg_type.

  Variant t :=
  | skip
  | var (lhs:reg) (rhs:Operand.t)
  | op (lhs:reg) (op:Op2.t) (rhs1 rhs2:Operand.t)
  | eq (lhs:reg) (rhs1 rhs:reg)
  | load (lhs:reg) (rhs:reg) (ord:Ordering.t)
  | store (lhs:reg) (rhs:reg) (ord:Ordering.t)
  | fetch_add (lhs:reg) (loc:reg) (addendum:reg) (ordr ordw:Ordering.t)
  | cas (lhs:reg) (loc old new:reg) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | malloc (lhs:reg) (rhs:reg)
  | free (lhs:reg)
  | syscall (lhs:reg) (rhses:list reg)
  | abort
  | choose (lhs:reg)
  .
End Inst.

Section Stmt.

  Inductive stmt :=
  | inst (i:Inst.t)
  | ite (cond:Inst.reg) (c1 c2:block)
  | while (cond:Inst.reg) (c:block)
  with block :=
  | nil
  | cons (hd:stmt) (tl:block)
  .

  Lemma block_ind2
        (P: block -> Prop)
        (NIL: P nil)
        (INST: forall hd tl, P tl -> P (cons (inst hd) tl))
        (ITE: forall c b1 b2 tl, P b1 -> P b2 -> P tl -> P (cons (ite c b1 b2) tl))
        (WHILE: forall c b tl, P b -> P tl -> P (cons (while c b) tl))
    :
      forall blk, P blk.
  Proof.
    fix IH 1.
    i. destruct blk.
    { auto. }
    destruct hd.
    - eapply INST. eauto.
    - eapply ITE; eauto.
    - eapply WHILE; eauto.
  Qed.

  Fixpoint add_block (b1 b2: block) : block :=
    match b1 with
    | nil => b2
    | cons hd tl => cons hd (add_block tl b2)
    end
  .

  Lemma add_block_assoc :
    forall a b c, (add_block (add_block a b) c) = add_block a (add_block b c).
  Proof.
    induction a; i; ss; clarify. f_equal. ss.
  Qed.

  Lemma cons_add_block_comm :
    forall hd a b, add_block (cons hd a) b = cons hd (add_block a b).
  Proof.
    induction a; i; ss; clarify.
  Qed.

  Lemma add_block_nil_unit:
    forall b, add_block nil b = b.
  Proof. ss. Qed.

  Lemma add_block_nil_unit_r:
    forall b, add_block b nil = b.
  Proof.
    induction b using block_ind2; ss; clarify.
    - rewrite IHb. ss.
    - rewrite IHb3. ss.
    - rewrite IHb2. ss.
  Qed.

  Lemma cons_to_add_block:
    forall a b, cons a b = add_block (cons a nil) b.
  Proof. ss. Qed.

  Lemma cons_add_block_comm_tail:
    forall hd a b, add_block a (cons hd b) = add_block (add_block a (cons hd nil)) b.
  Proof.
    i. rewrite add_block_assoc. rewrite <- cons_to_add_block. auto.
  Qed.

  Lemma add_block_nil_nil:
    forall a b (ADD: add_block a b = nil), (a = nil) /\ (b = nil).
  Proof.
    induction a; i; ss.
  Qed.

  Lemma add_block_inv_head0:
    forall a1 a2 hd (HEAD: add_block a1 (cons hd nil) = add_block a2 (cons hd nil)), a1 = a2.
  Proof.
    induction a1; i; ss.
    { destruct a2; ss. inv HEAD. exfalso. symmetry in H1. apply add_block_nil_nil in H1.
      des. clarify.
    }
    destruct a2; ss.
    { inv HEAD. apply add_block_nil_nil in H1. des; clarify. }
    inv HEAD. f_equal. eauto.
  Qed.

  Lemma add_block_inv_head0':
    forall a1 a2 hd1 hd2 (HEAD: add_block a1 (cons hd1 nil) = add_block a2 (cons hd2 nil)),
      (a1 = a2) /\ (hd1 = hd2).
  Proof.
    induction a1; i; ss.
    { destruct a2; ss.
      { inv HEAD. auto. }
      inv HEAD. exfalso. symmetry in H1. apply add_block_nil_nil in H1.
      des. clarify.
    }
    destruct a2; ss.
    { inv HEAD. apply add_block_nil_nil in H1. des; clarify. }
    inv HEAD. hexploit IHa1; eauto. i. des. split; eauto. f_equal. eauto.
  Qed.

  Lemma add_block_inv_head:
    forall b a1 a2 (HEAD: add_block a1 b = add_block a2 b), a1 = a2.
  Proof.
    induction b; i; ss.
    { rewrite ! add_block_nil_unit_r in HEAD. auto. }
    setoid_rewrite cons_add_block_comm_tail in HEAD.
    eapply IHb in HEAD. eapply add_block_inv_head0; eauto.
  Qed.

  Lemma add_block_head_nil:
    forall a b (HEAD: add_block a b = b), a = nil.
  Proof.
    i. rewrite <- add_block_nil_unit in HEAD. apply add_block_inv_head in HEAD. auto.
  Qed.

  Lemma add_block_head_nil_cons:
    forall a b hd1 hd2 (HEAD: add_block a (cons hd1 b) = cons hd2 b), (a = nil) /\ (hd1 = hd2).
  Proof.
    i. rewrite <- add_block_nil_unit in HEAD.
    setoid_rewrite cons_add_block_comm_tail in HEAD. apply add_block_inv_head in HEAD.
    apply add_block_inv_head0' in HEAD. auto.
  Qed.

End Stmt.
Coercion inst: Inst.t >-> stmt.

Section Env.

  (*
    local environment: only allocated variables can be used
    unallocated variables will return `None`.
  *)
  Definition lenv := Inst.reg -> option Val.t.

  (* register 0 (return register) is always allocated *)
  Definition init_le (glob : list Z) : lenv :=
    let initial_block := fun bid => Loc.mk None bid 0 in
    fun regid => if andb (0 <? regid)%nat ((Nat.sub regid 1) <? (List.length glob) )%nat
      then Some (Val.Vptr (initial_block (Nat.sub regid 1)))
      else None.

  Definition update (k : Inst.reg) (v : Val.t) (le : lenv) : lenv :=
    fun i => if (Nat.eqb k i) then Some v else (le i).

End Env.

Section Denote.
  Context {eff : Type -> Type}.
  Context `{HasMemE : MemE.t -< eff}.

  Definition lunit : Type := lenv * unit.

  Definition get_loc (v : Val.t) : itree eff Loc.t :=
    match v with
    | Val.Vundef => trigger MemE.abort;;; Ret (Loc.mk None 0 0)
    | Val.Vnum _ => trigger MemE.abort;;; Ret (Loc.mk None 0 0)
    | Val.Vptr loc => Ret loc
    end.

  Definition loc_add_offset (l : Loc.t) (offset : Z) : Loc.t :=
    Loc.mk l.(Loc.tid) l.(Loc.bid) (l.(Loc.ofs) + offset).

  Definition trigger_abort_return (le : lenv) : itree eff lunit :=
    trigger MemE.abort;;; Ret (le, tt).

  (*
    Checks if each register is allocated.
    If some register is not allocated, returns None.
  *)
  Fixpoint check_all_arguments (le : lenv) (args : list Inst.reg)
  : option (list Z) :=
    match args with
    | [] => Some []
    | hd :: tl =>
      match le hd with
      | Some arg_hd =>
          match arg_hd with
          | Val.Vnum n_hd =>
              match (check_all_arguments le tl) with
              | Some args_tl => Some (n_hd :: args_tl)
              | _ => None
              end
          | _ => None
        end
      | _ => None
      end
    end.

  (** Denotation of instructions *)
  Definition denote_inst (le: lenv) (i : Inst.t) : itree eff lunit :=
    match i with
    | Inst.skip =>
      tau;; Ret (le, tt)

    | Inst.var lhs rhs =>
      match (le lhs) with
      | Some _ =>
        match rhs with
        | Operand.const z => tau;; Ret (update lhs z le, tt)
        | Operand.register reg =>
          match (le reg) with
          | Some r => tau;; Ret (update lhs r le, tt)
          | _ => trigger_abort_return le
          end
        end
      | _ => trigger_abort_return le
      end

    | Inst.op lhs op rhs1 rhs2 =>
      match (le lhs) with
      | Some _ =>
        match rhs1, rhs2 with
        | Operand.const r1, Operand.const r2 =>
          let r := Op2.eval op (Val.Vnum r1) (Val.Vnum r2) in
          tau;; Ret (update lhs r le, tt)
        | Operand.const r1, Operand.register r2 =>
          match (le r2) with
          | Some r2' =>
            let r := Op2.eval op (Val.Vnum r1) r2' in
            tau;; Ret (update lhs r le, tt)
          | _ => trigger_abort_return le
          end
        | Operand.register r1, Operand.const r2 =>
          match (le r1) with
          | Some r1' =>
            let r := Op2.eval op r1' (Val.Vnum r2) in
            tau;; Ret (update lhs r le, tt)
          | _ => trigger_abort_return le
          end
        | Operand.register r1, Operand.register r2 =>
          match (le r1), (le r2) with
          | Some r1', Some r2' =>
            let r := Op2.eval op r1' r2' in
            tau;; Ret (update lhs r le, tt)
          | _, _ => trigger_abort_return le
          end
        end
      | _ => trigger_abort_return le
      end

    | Inst.eq lhs rhs1 rhs2 =>
      match (le lhs), (le rhs1), (le rhs2) with
      | Some _, Some r1, Some r2 =>
        r <- match r1, r2 with
          | Val.Vnum n1, Val.Vnum n2 =>
            if Z.eqb n1 n2 then tau;; Ret Val.one else tau;; Ret Val.zero
          | Val.Vptr loc1, Val.Vptr loc2 =>
            valret <- trigger (MemE.ptr_eq loc1 loc2);;
            match valret with
            | None => Ret Val.Vundef
            | Some b => if (b:bool) then Ret Val.one else Ret Val.zero
            end
          | _, _ => tau;; Ret Val.Vundef
          end;;
        Ret (update lhs r le, tt)
      | _, _, _ => trigger_abort_return le
      end

    | Inst.load lhs rhs ord =>
      match (le lhs), (le rhs) with
      | Some _, Some r =>
        loc <- get_loc r;;
        r <- trigger (MemE.read loc ord);;
        Ret (update lhs r le, tt)
      | _, _ => trigger_abort_return le
      end

    | Inst.store lhs rhs ord =>
      match (le lhs), (le rhs) with
      | Some l, Some r =>
        loc <- get_loc l;;
        trigger (MemE.write loc r ord);;;
        Ret (le, tt)
      | _, _ => trigger_abort_return le
      end

    | Inst.fetch_add lhs rhs0 rhs1 ord1 ord2 =>
      match (le lhs), (le rhs0), (le rhs1) with
      | Some _, Some r, Some addendum =>
        loc <- get_loc r;;
        r <- trigger (MemE.faa loc addendum ord1 ord2);;
        Ret (update lhs r le, tt)
      | _, _, _ => trigger_abort_return le
      end

    | Inst.cas lhs rhs0 rhs1 rhs2 ord1 ord2 =>
      match (le lhs), (le rhs0), (le rhs1), (le rhs2) with
      | Some _, Some r, Some old, Some new =>
        loc <- get_loc r;;
        t <- trigger (MemE.cas loc old new ord1 ord2);;
        let rv := match t with
                  | Some true => Val.one
                  | Some false => Val.zero
                  | _ => Val.Vundef
                  end in
        Ret (update lhs rv le, tt)
      | _, _, _, _ => trigger_abort_return le
      end

    | Inst.fence ord1 ord2 =>
      trigger (MemE.fence ord1 ord2);;; Ret (le, tt)

    | Inst.malloc lhs rhs =>
      match (le lhs), (le rhs) with
      | Some _, Some (Val.Vnum size) =>
        tau;; loc <- trigger (MemE.alloc size);;
        Ret (update lhs (Val.Vptr loc) le, tt)
      | _, _ => trigger_abort_return le
      end

    | Inst.free lhs =>
      match (le lhs) with
      | Some l =>
        loc <- get_loc l;;
        tau;; trigger (MemE.free loc);;; Ret (le, tt)
      | _ => trigger_abort_return le
      end

    | Inst.syscall lhs es =>
      match (le lhs), (check_all_arguments le es) with
      | Some _, Some args =>
        r <- trigger (MemE.syscall args);;
        Ret (update lhs (Val.Vnum r) le, tt)
      | _, _ => trigger_abort_return le
      end

    | Inst.abort =>
      trigger_abort_return le

    | Inst.choose lhs =>
      match (le lhs) with
      | Some _ =>
        v <- trigger (MemE.choose);;
        Ret (update lhs (Val.Vnum v) le, tt)
      | _ => trigger_abort_return le
      end
    end
  .

  (** Denotation of statements *)
  Definition while_itree (le: lenv) (step: lunit -> itree eff (lunit + lunit)) : itree eff lunit :=
    ITree.iter step (le, tt).

  Fixpoint denote_stmt (le: lenv) (s : stmt) : itree eff lunit :=
    match s with
    | inst i => denote_inst le i

    | ite cond sif selse =>
      match (le cond) with
      | Some cr =>
        let ift := denote_block le sif in
        let elset := denote_block le selse in
        tau;;
        (
          match (Val.is_zero cr) with
          | None => trigger_abort_return le
          | Some b => if b then elset else ift
          end
        )
      | _ => trigger_abort_return le
      end
    | while cond swhile =>
      while_itree le (
        fun lu =>
          tau;;
          let le0 := fst lu in
          match (le0 cond) with
          | Some cr =>
            (
              match (Val.is_zero cr) with
              | None => trigger (MemE.abort);;; Ret (inr (le0, tt))
              | Some b =>
                if b then ret (inr (le0, tt))
                else r <- denote_block le0 swhile;; ret (inl r)
              end
            )
          | _ => trigger (MemE.abort);;; Ret (inr (le0, tt))
          end
      )
    end
  with denote_block (le: lenv) (b: block) : itree eff lunit :=
    match b with
    | nil => Ret (le, tt)
    | cons s blk =>
      '(le1, _) : lunit <- denote_stmt le s;;
      denote_block le1 blk
    end
  .

End Denote.

Section Interp.

  Definition ret_reg : Inst.reg := 0.

  Definition effs := MemE.t.

  Fixpoint init_args params args (le: lenv) : option lenv :=
    match params, args with
    | [], [] => Some le
    | x :: part, v :: argt =>
      init_args part argt (update x v le)
    | _, _ => None
    end
  .

  Fixpoint init_regs (regs : list Inst.reg) (le : lenv) : option lenv :=
    match regs with
    | [] => Some le
    | reg :: tl => init_regs tl (update reg Val.Vundef le)
    end.

  Definition itr_code (blk: block) (le: lenv) : itree MemE.t (option Val.t) :=
    '(le1, _) : lunit <- (denote_block le blk);; Ret (le1 ret_reg).

  Definition eval_lang (glob : list Z) (body: block) : itree MemE.t Val.t :=
    '(le1, _) : lunit <- (denote_block (init_le glob) body);;
    match le1 ret_reg with
    | Some v => Ret v
    | None => trigger MemE.abort;;; Ret Val.Vundef
    end.
End Interp.
