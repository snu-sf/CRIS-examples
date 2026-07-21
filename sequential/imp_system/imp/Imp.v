(** * The Imp language  *)
From CRIS.common Require Import CRIS.

From CRIS.imp_system.imp Require Import ImpPrelude.
From CRIS.modules Require Import LModTr.
From CRIS.imp_system.mem Require Import MemHeader.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** GEnv *)

Fixpoint _find_idx {A} (f : A -> bool) (l : list A) (acc : nat) : option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f : A -> bool) (l : list A) : option (nat * A) := _find_idx f l 0.

Lemma find_idx_red {A} (f : A -> bool) (l : list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0%nat, hd)
    else
      p ← find_idx f tl; let '(n, a) := p in
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.

Module CEnv.

  Notation mblock := nat (only parsing).
  Notation ptrofs := Z (only parsing).

  Record t : Type := mk {
    blk2id : mblock -> option string;
    id2blk : string -> option mblock;
  }.
  
  Definition wf (genve : t) : Prop :=
    forall id blk, genve.(id2blk) id = Some blk <-> genve.(blk2id) blk = Some id.

  Definition load_genv (genv : GEnv.t) : t :=
    let n := List.length genv in
    {|
      blk2id := fun blk => p ← (List.nth_error genv blk); let '(gn, _) := p in Some gn;
      id2blk := fun id => p ← find_idx (fun '(id', _) => string_dec id id') genv; let '(blk, _) := p in Some blk
    |}
  .

  Lemma load_genv_wf
        genv
        (WF : GEnv.wf genv)
    :
      <<WF : wf (load_genv genv)>>.
  Proof.
    r in WF.
    rr. split; i; ss.
    - rewrite /mbind /option_bind in H |- *. des_ifs.
      + f_equal. ginduction genv; ss. i. inv WF.
        rewrite find_idx_red in Heq0. des_ifs; ss.
        { destruct string_dec; ss. subst. clarify. }
        destruct string_dec; ss. rewrite /mbind /option_bind in Heq0. des_ifs. ss.
        hexploit IHgenv; et.
      + exfalso. ginduction genv; ss. i. inv WF.
        rewrite find_idx_red in Heq0. des_ifs; ss.
        destruct string_dec; ss. rewrite /mbind /option_bind in Heq0. des_ifs. 
        hexploit IHgenv; et.
    - ginduction genv; ss.
      { i. destruct blk; ss. }
      i. destruct a. inv WF. destruct blk; ss; clarify.
      { rewrite find_idx_red. des_ifs; ss. rewrite /mbind /option_bind.
        des_ifs; destruct string_dec; ss. }
      hexploit IHgenv; et. i.
      rewrite find_idx_red. rewrite /mbind /option_bind in H0 |- *. des_ifs. exfalso.
      destruct string_dec; ss; subst.      
      clear - Heq H2. ginduction genv; ss. i.
      rewrite find_idx_red in Heq. des_ifs; destruct string_dec; ss; et.
      rewrite /mbind /option_bind in Heq. des_ifs. eapply IHgenv; et.
  Qed.

  Definition incl_env (genv0 : GEnv.t) (genvenv : t) : Prop :=
    forall gn gd (IN : List.In (gn, gd) genv0),
    exists blk, <<FIND : genvenv.(CEnv.id2blk) gn = Some blk>>.

  Lemma incl_incl_env genv0 genv1
    (WF: GEnv.wf genv1)
    (INCL : List.incl genv0 genv1)
    :
      incl_env genv0 (load_genv genv1).
  Proof.
    ii. exploit INCL; et. i. ss. rewrite /mbind /option_bind. des_ifs; et.
    exfalso. clear - x0 Heq. ginduction genv1; et.
    i. ss. rewrite find_idx_red in Heq. des_ifs.
    rewrite /mbind /option_bind in Heq. des_ifs. destruct string_dec; ss. des; clarify.
    eapply IHgenv1; et.
  Qed.

  Lemma in_env_in_genv :
    forall genv blk symb
      (WF: GEnv.wf genv)
      (FIND : blk2id (load_genv genv) blk = Some symb),
    exists def, In (symb, def) genv.
  Proof.
    i. cut (exists def, In (symb, def) genv).
    { i; des. eexists. eauto. }
    ss. rewrite /mbind /option_bind in FIND. des_ifs. eapply nth_error_In in Heq. et.
  Qed.

  Lemma in_genv_in_env :
    forall genv def symb
           (WF: GEnv.wf genv)
           (IN : In (symb, def) genv),
    exists blk, blk2id (load_genv genv) blk = Some symb.
  Proof.
    i. ss. eapply In_nth_error in IN. des.
    eexists. rewrite ->IN. et.
  Qed.

  Lemma env_range_some :
    forall genv blk
      (WF: GEnv.wf genv)
      (BLKRANGE : blk < Datatypes.length genv),
      <<FOUND : exists symb, blk2id (load_genv genv) blk = Some symb>>.
  Proof.
    i. depgen genv. induction blk; i; ss; clarify.
    { destruct genv; ss; clarify.
      { lia. }
      destruct p. exists s. ss. }
    destruct genv; ss; clarify.
    { lia. }
    apply PeanoNat.lt_S_n in BLKRANGE. eapply IHblk; eauto.
    r in WF. ss. apply NoDup_cons_iff in WF. des; eauto.
  Qed.

  Lemma env_found_range :
    forall genv symb blk
      (WF: GEnv.wf genv)
      (FOUND : id2blk (load_genv genv) symb = Some blk),
      <<BLKRANGE : blk < Datatypes.length genv>>.
  Proof.
    intros genv. ginduction genv; i; ss; clarify.
    rewrite /mbind /option_bind in FOUND. des_ifs. rewrite find_idx_red in Heq. des_ifs.
    { apply Nat.lt_0_succ. }
    destruct blk.
    { apply Nat.lt_0_succ. }
    rewrite /mbind /option_bind in Heq. des_ifs. eapply (Nat.succ_lt_mono blk).
    eapply IHgenv; eauto.
    { r in WF. ss. apply NoDup_cons_iff in WF. des; eauto. }
    instantiate (1:=symb). rewrite Heq1. ss.
  Qed.
  
End CEnv.

Coercion CEnv.load_genv : GEnv.t >-> CEnv.t.
Global Opaque CEnv.load_genv.

Section FB_HAS_SPEC.

  Context `{Σ : GRA}.

  Variable genvenv : GEnv.t.

  (* Variant fb_has_spec (stb : string -> option fspec) (fb : mblock) (fsp : fspec) : Prop :=
  | fb_has_spec_intro
      fn
      (FBLOCK : genvenv.(CEnv.blk2id) fb = Some fn)
      (SPEC : fn_has_spec stb fn fsp)
  . *)

  Variant fb_has_spec_in (stb : specmap) (fb : mblock) (fsp : fspec) : Prop :=
  | fb_has_spec_in_intro
      fn
      (FBLOCK : genvenv.(CEnv.blk2id) fb = Some fn)
      (SPEC : fn_has_spec_in stb fn fsp).

  (* Lemma fb_has_weaker_spec (stb : string -> option fspec) (fb : mblock) (fsp0 fsp1 : fspec)
        (SPEC : fb_has_spec stb fb fsp1)
        (WEAK : fspec_imply fsp1 fsp0)
    :
      fb_has_spec stb fb fsp0.
  Proof.
    inv SPEC. econs; eauto.
    eapply fn_has_weaker_spec; eauto.
  Qed. *)
  
End FB_HAS_SPEC.

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s : *)
Definition var : Set := string.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : Z)
| Eq (_ _ : expr)
| Lt (_ _ : expr)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr)
.

(** function cCall exists only as a statement *)
Inductive stmt : Type :=
| Skip                           (* ; *)
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| CallFun (x : var) (f : string) (args : list expr) (* x = f(args), cCall by name *)
| CallPtr (x : var) (p : expr) (args : list expr)  (* x = f(args), by pointer*)
| CallSys (x : var) (f : string) (args : list expr) (* x = f(args), system cCall *)
| AddrOf (x : var) (X : string)         (* x = &X *)
| Malloc (x : var) (s : expr)          (* x = malloc(s) *)
| Free (p : expr)                      (* free(p) *)
| Load (x : var) (p : expr)            (* x = *p *)
| Store (p : expr) (v : expr)          (* *p = v *)
| Cmp (x : var) (a : expr) (b : expr)  (* memory accessing equality comparison *)
.

(** information of a function *)
Record function : Type := mk_function {
  fn_params : list var;
  fn_vars : list var;     (* disjoint with fn_params *)
  fn_body : stmt
}.

(* prohibited names for Callfun/Ptr *)
Definition call_ban f :=
  rel_dec f MemHdr.alloc.1 || rel_dec f MemHdr.free.1 || rel_dec f MemHdr.load.1 || rel_dec f MemHdr.store.1 || rel_dec f MemHdr.cmp.1.

(** ** Supported System Calls by Imp *)
Definition syscalls : list (string * nat) :=
  [("print", 1); ("scan", 0)].

Global Opaque syscalls.


(** ** Program *)

(** program components *)
(* declared external global variables *)
Definition extVars := list string.
(* declared external functions with arg nums*)
Definition extFuns := list (string * nat).
(* defined global variables *)
Definition progVars := list (string * Z).
(* defined internal functions *)
Definition progFuns := list (string * function).

(** Imp program *)

(* Record programL : Type := mk_programL {
  nameL : list mname;
  ext_varsL : extVars;
  ext_funsL : extFuns;
  prog_varsL : progVars;
  prog_funsL : list (mname * (string * function));
  publicL : list string;
  defsL : list (string * GEnv.gdef);
}. *)

Record program : Type := mk_program {
  (* name : mname; *)
  ext_vars : extVars;
  ext_funs : extFuns;
  prog_vars : progVars;
  prog_funs : progFuns;
  public : list string :=
    let sys := List.map fst syscalls in
    let evs := ext_vars in
    let efs := List.map fst ext_funs in
    let ivs := List.map fst prog_vars in
    let ifs := List.map fst prog_funs in
    sys ++ evs ++ efs ++ ivs ++ ifs;
  defs : list (string * gdef) :=
    let fs := (List.map (fun '(fn, _) => (fn, Gfun)) prog_funs) in
    let vs := (List.map (fun '(vn, vv) => (vn, Gvar vv)) prog_vars) in
    (List.filter (negb ∘ call_ban ∘ fst) (fs ++ vs));
}.

(* Definition lift (p : program) : programL :=
  mk_programL
    [p.(name)]
    p.(ext_vars) p.(ext_funs)
    p.(prog_vars) (List.map (fun pf => (p.(name), pf)) p.(prog_funs))
    p.(public) p.(defs).

Coercion lift : program >-> programL. *)





(* ========================================================================== *)
(** ** Semantics *)

(** Get/Set function local variables *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

(** Get pointer to a global variable/function *)
Variant GlobEnv : Type -> Type :=
| GetPtr (x : string) : GlobEnv val
| GetName (p : val) : GlobEnv string.

Section Denote.

  Context {eff : Type -> Type}.
  Context {HasGlobVar : GlobEnv -< eff}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : coreE -< eff}.

  (** Denotation of expressions *)
  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => u <- trigger (GetVar v) ;; Ret u
    | Lit n     => tau;; Ret (Vint n)

    | Eq a b =>
      l <- denote_expr a ;; r <- denote_expr b ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (lv =? rv)%Z then Ret (Vint 1) else Ret (Vint 0)
      | _, _ => triggerUB
      end

    | Lt a b =>
      l <- denote_expr a ;; r <- denote_expr b ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (Z_lt_dec lv rv) then Ret (Vint 1) else Ret (Vint 0)
      | _, _ => triggerUB
      end

    | Plus a b  =>
      l <- denote_expr a ;; r <- denote_expr b ;; u <- (vadd l r)? ;; Ret u

    | Minus a b =>
      l <- denote_expr a ;; r <- denote_expr b ;; u <- (vsub l r)? ;; Ret u

    | Mult a b  =>
      l <- denote_expr a ;; r <- denote_expr b ;; u <- (vmul l r)? ;; Ret u

    end.

  (** Denotation of statements *)
  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  Fixpoint denote_exprs_acc (es : list expr) (acc : list val) : itree eff (list val) :=
    match es with
    | [] => Ret acc
    | e :: s =>
      v <- denote_expr e;; denote_exprs_acc s (acc ++ [v])
    end.

  Fixpoint denote_exprs (es : list expr) : itree eff (list val) :=
    match es with
    | [] => Ret []
    | e :: s =>
      v <- denote_expr e;;
      vs <- denote_exprs s;;
      Ret (v :: vs)
    end.

  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Skip => tau;; Ret Vundef
    | Assign x e =>
      v <- denote_expr e;; trigger (SetVar x v);;; tau;; Ret Vundef
    | Seq a b =>
      tau;; denote_stmt a;;; denote_stmt b
    | If i t e =>
      v <- denote_expr i;;
      (if (wf_val v) then Ret tt else triggerUB);;;
      'b : bool <- (is_true v)?;; tau;;
      if b then (denote_stmt t) else (denote_stmt e)

    | CallFun x f args =>
      (if (call_ban f) then triggerUB else Ret tt);;;
      eval_args <- denote_exprs args;;
      v <- ccallU (fnsig f imp_fun_t) eval_args;;
      trigger (SetVar x v);;; tau;; Ret Vundef

    | CallPtr x e args =>
      (if (match e with | Var _ => true | _ => false end) then Ret tt else triggerUB);;;
      p <- denote_expr e;; f <- trigger (GetName p);;
      eval_args <- denote_exprs args;;
      v <- ccallU (fnsig f imp_fun_t) eval_args;;
      trigger (SetVar x v);;; tau;; Ret Vundef

    | CallSys x f args =>
      sig <- (alist_find f syscalls)? ;;
      (if (sig =? List.length args)%nat then Ret tt else triggerUB);;;
      eval_args <- denote_exprs args;;
      (if (forallb (fun v => match v with | Vint _ => true | _ => false end) eval_args) then Ret tt else triggerUB);;;
      let eval_zs := List.map (fun v => match v with | Vint z => z | _ => 0%Z end) eval_args in
      (if (forallb intrange_64 eval_zs) then Ret tt else triggerUB);;;
      v <- trigger (IO f eval_zs);;
      trigger (SetVar x (Vint v));;; tau;; Ret Vundef

    | AddrOf x X =>
      v <- trigger (GetPtr X);; trigger (SetVar x v);;; tau;; Ret Vundef
    | Malloc x se =>
      s <- denote_expr se;;
      v <- ccallU MemHdr.alloc [s];;
      trigger (SetVar x v);;; tau;; Ret Vundef
    | Free pe =>
      p <- denote_expr pe;;
      't : val <- ccallU MemHdr.free [p];; tau;; Ret Vundef
    | Load x pe =>
      p <- denote_expr pe;;
      (if (wf_val p) then Ret tt else triggerUB);;;
      v <- ccallU MemHdr.load [p];;
      trigger (SetVar x v);;; tau;; Ret Vundef
    | Store pe ve =>
      p <- denote_expr pe;;
      (if (wf_val p) then Ret tt else triggerUB);;;
      v <- denote_expr ve;;
      't:val <- ccallU MemHdr.store [p; v];; tau;; Ret Vundef
    | Cmp x ae be =>
      a <- denote_expr ae;; b <- denote_expr be;;
      (if (wf_val a && wf_val b) then Ret tt else triggerUB);;;
      v <- ccallU MemHdr.cmp [a; b];;
      trigger (SetVar x v);;; tau;; Ret Vundef

    end.

End Denote.





(* ========================================================================== *)
(** ** Interpretation *)

Section Interp.

  Context `{Σ: GRA}.

  Definition effs := GlobEnv +' ImpState +' crisE.

  Definition handle_GlobEnv {eff} `{coreE -< eff} (ge : GEnv.t) : GlobEnv ~> (itree eff) :=
    fun _ e =>
      match e with
      | GetPtr X =>
        r <- (ge.(CEnv.id2blk) X)?;; Ret (Vptr (r, 0%Z))
      | GetName p =>
        match p with
        | Vptr (n, 0%Z) => x <- (ge.(CEnv.blk2id) n)?;; Ret (x)
        | _ => triggerUB
        end
      end.

  Definition interp_GlobEnv {eff} `{coreE -< eff} (ge : GEnv.t) : itree (GlobEnv +' eff) ~> (itree eff) :=
    interp (fun _ e =>
      match e with
      | inl1 e => @handle_GlobEnv eff H ge _ e
      | inr1 e => trigger e
      end).

  (** function local environment *)
  Definition lenv := alist var val.
  Definition handle_ImpState {eff} `{coreE -< eff} : ImpState ~> stateT lenv (itree eff) :=
    fun _ e le =>
      match e with
      | GetVar x => r <- unwrapU (alist_find x le);; Ret (le, r)
      | SetVar x v => Ret (alist_add x v le, tt)
      end.

  Definition interp_ImpState {eff} `{coreE -< eff}: itree (ImpState +' eff) ~> stateT lenv (itree eff) :=
    State.interp_state (case_ handle_ImpState LModTr.pure_state).

  (* Definition interp_imp ge le (itr : itree effs val) := *)
  (*   interp_ImpState (interp_GlobEnv ge itr) le. *)

  Definition interp_imp ge : itree effs ~> stateT lenv (itree crisE) :=
    fun _ itr le => interp_ImpState (interp_GlobEnv ge itr) le.

  Fixpoint init_lenv xs : lenv :=
    match xs with
    | [] => []
    | x :: t => (x, Vundef) :: (init_lenv t)
    end
  .

  Fixpoint init_args params args (acc : lenv) : option lenv :=
    match params, args with
    | [], [] => Some acc
    | x :: part, v :: argt =>
      init_args part argt (alist_add x v acc)
    | _, _ => None
    end
  .

  Lemma init_args_prop :
    forall params args acc le
      (INITSOME : init_args params args acc = Some le),
      <<INITLEN : List.length params = List.length args>>.
  Proof.
    induction params; i; ss; clarify.
    { destruct args; ss; clarify. }
    destruct args; ss; clarify. apply IHparams in INITSOME. red. rewrite INITSOME. ss.
  Qed.

  (* 'return' is a fixed register, holding the return value of this function. *)
  (* '_' is a black hole register, holding garbage *)
  Definition eval_imp (ge : GEnv.t) (f : function) (args : list val) : itree crisE val :=
    let vars := f.(fn_vars) ++ ["return"; "_"] in
    let params := f.(fn_params) in
    (if (ListDec.NoDup_dec string_dec (params ++ vars)) then Ret tt else triggerUB);;;
    match (init_args params args (init_lenv vars)) with
    | Some iargs =>
      '(_, retv) :_ <- (interp_imp ge (tau;; (denote_stmt f.(fn_body));;; retv <- (denote_expr (Var "return")) ;; Ret retv)
                               iargs);; Ret retv
    | None => triggerUB
    end
  .

End Interp.
