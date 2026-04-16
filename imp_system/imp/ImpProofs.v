Require Import CRIS.

Require Import ImpPrelude.
Require Import Imp.
Require Import LModTr.
Require Import MemHeader.

Set Implicit Arguments.

(** ** Rewriting Leamms *)
Section PROOFS.

  Context `{Σ : GRA}.

  (* expr *)
  Lemma denote_expr_Var
        ge le0 v
    :
      interp_imp ge (denote_expr (Var v)) le0 =
      interp_imp ge (u <- trigger (GetVar v);; Ret u) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_expr_Lit
        ge le0 n
    :
      interp_imp ge (denote_expr (Lit n)) le0 =
      interp_imp ge (tau;; Ret (Vint n)) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_expr_Eq
        ge le0 a b
    :
      interp_imp ge (denote_expr (Eq a b)) le0 =
      interp_imp ge (
      l <- denote_expr a ;; r <- denote_expr b ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (lv =? rv)%Z then Ret (Vint 1) else Ret (Vint 0)
      | _, _ => triggerUB
      end)le0.
  Proof using. reflexivity. Qed.

  Lemma denote_expr_Lt
        ge le0 a b
    :
      interp_imp ge (denote_expr (Lt a b)) le0 =
      interp_imp ge (
      l <- denote_expr a ;; r <- denote_expr b ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (Z_lt_dec lv rv) then Ret (Vint 1) else Ret (Vint 0)
      | _, _ => triggerUB
      end)le0.
  Proof using. reflexivity. Qed.

  Lemma denote_expr_Plus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Plus a b)) le0 =
      interp_imp ge (
                   ' l : val <- denote_expr a;; ' r : val <- denote_expr b;;
                   ' u : val <- unwrapU (vadd l r);; Ret u)le0.
  Proof using. reflexivity. Qed.

  Lemma denote_expr_Minus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Minus a b)) le0 =
      interp_imp ge (
                   ' l : val <- denote_expr a;; ' r : val <- denote_expr b;;
                   ' u : val <- unwrapU (vsub l r);; Ret u) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_expr_Mult
        ge le0 a b
    :
      interp_imp ge (denote_expr (Mult a b)) le0 =
      interp_imp ge (
                   ' l : val <- denote_expr a;; ' r : val <- denote_expr b;;
                   ' u : val <- unwrapU (vmul l r);; Ret u) le0.
  Proof using. reflexivity. Qed.

  (* stmt *)

  Lemma denote_stmt_Skip
        ge le0
    :
      interp_imp ge (denote_stmt (Skip)) le0 =
      interp_imp ge (tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Assign
        ge le0 x e
    :
      interp_imp ge (denote_stmt (Assign x e)) le0 =
      interp_imp ge (v <- denote_expr e ;; trigger (SetVar x v) ;;; tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Seq
        ge le0 a b
    :
      interp_imp ge (denote_stmt (Seq a b)) le0 =
      interp_imp ge (tau;; denote_stmt a ;;; denote_stmt b) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_If
        ge le0 i t e
    :
      interp_imp ge (denote_stmt (If i t e)) le0 =
      interp_imp ge (v <- denote_expr i ;;
                     (if (wf_val v) then Ret tt else triggerUB);;;
                     'b : bool <- (is_true v)? ;; tau;;
                     if b then (denote_stmt t) else (denote_stmt e)) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_AddrOf
        ge le0 x X
    :
      interp_imp ge (denote_stmt (AddrOf x X)) le0 =
      interp_imp ge (v <- trigger (GetPtr X);; trigger (SetVar x v);;; tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Malloc
        ge le0 x se
    :
      interp_imp ge (denote_stmt (Malloc x se)) le0 =
      interp_imp ge (s <- denote_expr se;;
      v <- ccallU MemHdr.alloc [s];;
      trigger (SetVar x v);;; tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Free
        ge le0 pe
    :
      interp_imp ge (denote_stmt (Free pe)) le0 =
      interp_imp ge (p <- denote_expr pe;;
      't : val <- ccallU MemHdr.free [p];; tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Load
        ge le0 x pe
    :
      interp_imp ge (denote_stmt (Load x pe)) le0 =
      interp_imp ge (
                   ' p : val <- denote_expr pe;;
                         (if wf_val p then Ret tt else triggerUB);;;
                         v0 <- ccallU MemHdr.load [p];;
                         trigger (SetVar x v0);;; (tau;; Ret Vundef)) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Store
        ge le0 pe ve
    :
      interp_imp ge (denote_stmt (Store pe ve)) le0 =
      interp_imp ge (
                   ' p : val <- denote_expr pe;;
                         (if wf_val p then Ret tt else triggerUB);;;
                          ' v : val <- denote_expr ve;;
                              't : val <- ccallU MemHdr.store [p; v];; tau;; Ret Vundef
                          ) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_Cmp
        ge le0 x ae be
    :
      interp_imp ge (denote_stmt (Cmp x ae be)) le0 =
      interp_imp ge ( a <- denote_expr ae;; b <- denote_expr be;;
                      (if (wf_val a && wf_val b) then Ret tt else triggerUB);;;
                        v <- ccallU MemHdr.cmp [a; b];;
                        trigger (SetVar x v);;; tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_CallFun
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallFun x f args)) le0 =
      interp_imp ge (
      (if (call_ban f) then triggerUB else Ret tt);;;
      eval_args <- (denote_exprs args);;
      v <- ccallU (fnsig f imp_fun_t) eval_args;;
      trigger (SetVar x v);;; tau;; Ret Vundef) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_CallPtr
        ge le0 x e args
    :
      interp_imp ge (denote_stmt (CallPtr x e args)) le0 =
      interp_imp ge (
      (if match e with
          | Var _ => true
          | _ => false
          end then Ret () else triggerUB);;;
      ' p : val <- denote_expr e;;
      ' f : string <- trigger (GetName p);;
      ' eval_args : list val <- denote_exprs args;; ' v : val <- ccallU (fnsig f imp_fun_t) eval_args;; trigger (SetVar x v);;; (tau;; Ret Vundef)) le0.
  Proof using. reflexivity. Qed.

  Lemma denote_stmt_CallSys
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallSys x f args)) le0 =
      interp_imp ge (
      ' sig : nat <- unwrapU (alist_find f syscalls);;
      (if (sig =? Datatypes.length args)%nat then Ret () else triggerUB);;;
      ' eval_args : list val <- denote_exprs args;;
      (if forallb (fun v : val => match v with
                                  | Vint _ => true
                                  | _ => false
                                  end) eval_args then Ret () else triggerUB);;;
      (let eval_zs := List.map (fun v : val => match v with
                                               | Vint z => z
                                               | _ => 0%Z
                                               end) eval_args in
       (if forallb intrange_64 eval_zs then Ret () else triggerUB);;;
       v <- trigger (IO f eval_zs);; trigger (SetVar x (Vint v));;; (tau;; Ret Vundef))) le0.
  Proof using. reflexivity. Qed.

  (* interp_imp *)

  Lemma interp_imp_bind
        T R (itr : itree _ T) (ktr : T -> itree _ R) ge le0
    :
      interp_imp ge (v <- itr ;; ktr v) le0 =
      '(le1, v): _ <- interp_imp ge itr le0;;
      interp_imp ge (ktr v) le1.
  Proof using.
    unfold interp_imp. unfold interp_GlobEnv.
    unfold interp_ImpState. grind. des_ifs.
  Qed.

  Lemma interp_imp_tau
        T (itr : itree _ T) ge le0
    :
      interp_imp ge (tau;; itr) le0 =
      tau;; interp_imp ge itr le0.
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_Ret
        T ge le0 (v : T)
    :
      interp_imp ge (Ret v) le0 = Ret (le0, v).
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_triggerUB
        T ge le0
    :
      (interp_imp ge (triggerUB) le0 : itree _ (lenv * T)) = triggerUB.
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, LModTr.pure_state, triggerUB, trivial_Handler.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerUB_bind
        U T ge le0 (ktr : U -> itree _ T)
    :
      (interp_imp ge (x <- triggerUB;; ktr x) le0 : itree _ (lenv *T)) = triggerUB.
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, LModTr.pure_state, triggerUB, trivial_Handler.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerNB
        T ge le0
    :
      (interp_imp ge (triggerNB) le0 : itree _ (lenv * T)) = triggerNB.
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, LModTr.pure_state, triggerNB, trivial_Handler.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerNB_bind
        U T ge le0 (ktr : U -> itree _ T)
    :
      (interp_imp ge (x <- triggerNB;; ktr x) le0 : itree _ (lenv * T)) = triggerNB.
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, LModTr.pure_state, triggerNB, trivial_Handler.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_unwrapU
        T x ge le0
    :
      (interp_imp ge (unwrapU x) le0 : itree _ (lenv * T)) =
      x <- unwrapU x;; Ret (le0, x).
  Proof using.
    unfold unwrapU. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerUB.
      unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_unwrapN
        T x ge le0
    :
      (interp_imp ge (unwrapN x) le0 : itree _ (lenv * T)) =
      x <- unwrapN x;; Ret (le0, x).
  Proof using.
    unfold unwrapN. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerNB.
      unfold triggerNB. grind.
  Qed.

  Lemma interp_imp_GetPtr
        ge le0 X
    :
      interp_imp ge (trigger (GetPtr X)) le0 =
      r <- (ge.(CEnv.id2blk) X)? ;; tau;; Ret (le0, Vptr (r, 0%Z)).
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, unwrapU.
    des_ifs; grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. unfold triggerUB, LModTr.pure_state. grind.
  Qed.

  Lemma interp_imp_GetName
        ge le0 x
    :
      interp_imp ge (trigger (GetName x)) le0 =
      match x with
      | Vptr (n, 0%Z) => u <- unwrapU (CEnv.blk2id ge n);; tau;; Ret (le0, u)
      | _ => triggerUB
      end
  .
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    destruct x as [?|[blk ofs]|]; try destruct ofs.
    1,3,4,5:(rewrite interp_trigger; grind; unfold triggerUB, LModTr.pure_state; grind).
    rewrite interp_trigger. grind. unfold unwrapU.
    destruct (CEnv.blk2id ge blk).
    { grind. }
    unfold triggerUB, LModTr.pure_state. grind.
  Qed.

  Lemma interp_imp_GetVar
        ge le0 x
    :
      (interp_imp ge (trigger (GetVar x)) le0 : itree crisE _) =
      r <- unwrapU (alist_find x le0);; tau;; tau;; Ret (le0, r).
  Proof using.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, trivial_Handler.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_SetVar
        ge le0 x v
    :
      interp_imp ge (trigger (SetVar x v)) le0 =
      tau;; tau;; Ret (alist_add x v le0, ()).
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, trivial_Handler.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_ccallU
        ge le0 f (args : list val)
    :
      (interp_imp ge (ccallU (fnsig f imp_fun_t) args) le0 : itree _ (_ * val)) =
      v <- trigger (Call f (args↑));; tau;; tau;; v <- (v↓)?;; Ret (le0, v).
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, ccallU, trivial_Handler. grind.
    unfold LModTr.pure_state. rewrite interp_trigger. grind.
    unfold unwrapU. des_ifs; grind. unfold triggerUB. grind.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_IO
        ge le0 I O f (args : I)
    :
      interp_imp ge (trigger (IO f args)) le0 =
      v <- trigger (IO f args);; tau;; tau;; Ret (le0, (v : O)).
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, trivial_Handler.
    unfold LModTr.pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_assume
        ge le0 p
    :
      interp_imp ge (assume p) le0 = assume p;;; tau;; tau;; Ret (le0, ()).
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, trivial_Handler.
    unfold assume. grind. rewrite interp_trigger. grind.
    unfold LModTr.pure_state. grind.
  Qed.

  Lemma interp_imp_guarantee
        ge le0 p
    :
      interp_imp ge (guarantee p) le0 = guarantee p;;; tau;; tau;; Ret (le0, ()).
  Proof using.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, trivial_Handler.
    unfold guarantee. grind. rewrite interp_trigger. grind.
    unfold LModTr.pure_state. grind.
  Qed.

  Lemma interp_modE_ext
        ge R (itr0 itr1 : itree _ R) le0
    :
      itr0 = itr1 -> interp_imp ge itr0 le0 = interp_imp ge itr1 le0
  .
  Proof using. i; subst; refl. Qed.

  Lemma interp_imp_expr_Var
        ge le0 v
    :
      interp_imp ge (denote_expr (Var v)) le0 =
      r <- unwrapU (alist_find v le0);; tau;; tau;; Ret (le0, r).
  Proof using.
    rewrite denote_expr_Var. rewrite interp_imp_bind. rewrite interp_imp_GetVar.
    grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Lit
        ge le0 n
    :
      interp_imp ge (denote_expr (Lit n)) le0 =
      tau;; Ret (le0, Vint n).
  Proof using.
    rewrite denote_expr_Lit. rewrite interp_imp_tau. grind; apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Eq
        ge le0 a b
    :
      interp_imp ge (denote_expr (Eq a b)) le0 =
      '(le1, l):_ <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r):_ <- interp_imp ge (denote_expr b) le1 ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (lv =? rv)%Z then Ret (le2, Vint 1) else Ret (le2, Vint 0)
      | _, _ => triggerUB
      end
  .
  Proof using.
    rewrite denote_expr_Eq. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. destruct (wf_val v && wf_val v0).
    2:{ rewrite interp_imp_triggerUB. unfold triggerUB; grind. }
    rewrite interp_imp_Ret. grind.
    des_ifs; try apply interp_imp_triggerUB.
    1,2 : apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Lt
        ge le0 a b
    :
      interp_imp ge (denote_expr (Lt a b)) le0 =
      '(le1, l):_ <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r):_ <- interp_imp ge (denote_expr b) le1 ;;
      (if (wf_val l && wf_val r) then Ret tt else triggerUB);;;
      match l, r with
      | Vint lv, Vint rv => if (Z_lt_dec lv rv) then Ret (le2, Vint 1) else Ret (le2, Vint 0)
      | _, _ => triggerUB
      end
  .
  Proof using.
    rewrite denote_expr_Lt. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. destruct (wf_val v && wf_val v0).
    2:{ rewrite interp_imp_triggerUB. unfold triggerUB; grind. }
    rewrite interp_imp_Ret. grind.
    des_ifs; try apply interp_imp_triggerUB.
    1,2 : apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Plus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Plus a b)) le0 =
      '(le1, l):_ <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r):_ <- interp_imp ge (denote_expr b) le1 ;;
      ' u : val <- unwrapU (vadd l r);; Ret (le2, u)
  .
  Proof using.
    rewrite denote_expr_Plus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_unwrapU. grind.
  Qed.

  Lemma interp_imp_expr_Minus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Minus a b)) le0 =
      '(le1, l):_ <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r):_ <- interp_imp ge (denote_expr b) le1 ;;
      ' u : val <- unwrapU (vsub l r);; Ret (le2, u)
  .
  Proof using.
    rewrite denote_expr_Minus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_unwrapU. grind.
  Qed.

  Lemma interp_imp_expr_Mult
        ge le0 a b
    :
      interp_imp ge (denote_expr (Mult a b)) le0 =
      '(le1, l):_ <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r):_ <- interp_imp ge (denote_expr b) le1 ;;
      ' u : val <- unwrapU (vmul l r);; Ret (le2, u)
  .
  Proof using.
    rewrite denote_expr_Mult. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_unwrapU. grind.
  Qed.

  Lemma interp_imp_Skip
        ge le0
    :
      interp_imp ge (denote_stmt (Skip)) le0 =
      tau;; Ret (le0, Vundef).
  Proof using.
    rewrite denote_stmt_Skip. rewrite interp_imp_tau.
    grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Assign
        ge le0 x e
    :
      interp_imp ge (denote_stmt (Assign x e)) le0 =
      '(le1, v):_ <- interp_imp ge (denote_expr e) le0 ;;
      tau;; tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof using.
    rewrite denote_stmt_Assign.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Seq
        ge le0 a b
    :
      interp_imp ge (denote_stmt (Seq a b)) le0 =
      tau;;
      '(le1, _):_ <- interp_imp ge (denote_stmt a) le0 ;;
      interp_imp ge (denote_stmt b) le1.
  Proof using.
    rewrite denote_stmt_Seq. rewrite interp_imp_tau; grind.
    apply interp_imp_bind.
  Qed.

  Lemma interp_imp_If
        ge le0 i t e
    :
      interp_imp ge (denote_stmt (If i t e)) le0 =
      '(le1, v):_ <- interp_imp ge (denote_expr i) le0 ;;
      (if (wf_val v) then Ret tt else triggerUB);;;
          'b : bool <- (is_true v)? ;; tau;;
              if b
              then interp_imp ge (denote_stmt t) le1
              else interp_imp ge (denote_stmt e) le1.
  Proof using.
    rewrite denote_stmt_If. rewrite interp_imp_bind. grind.
    des_ifs.
    2:{ rewrite interp_imp_bind. rewrite interp_imp_triggerUB. unfold triggerUB. grind. }
    destruct (is_true v); grind; des_ifs.
    1,2 : rewrite interp_imp_tau; grind.
    hexploit (@interp_imp_triggerUB_bind bool val ge l (λ u: bool, tau;; if u then denote_stmt t else denote_stmt e)).
    rewrite /triggerUB. i; ss. rewrite bind_bind in H. rewrite H. grind.
  Qed.

  Lemma interp_imp_AddrOf
        ge le0 x X
    :
      interp_imp ge (denote_stmt (AddrOf x X)) le0 =
      r <- (ge.(CEnv.id2blk) X)? ;; tau;;
      tau;; tau;; tau;; Ret (alist_add x (Vptr (r, 0%Z)) le0, Vundef).
  Proof using.
    rewrite denote_stmt_AddrOf. rewrite interp_imp_bind.
    rewrite interp_imp_GetPtr. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Malloc
        ge le0 x se
    :
      interp_imp ge (denote_stmt (Malloc x se)) le0 =
      '(le1, s):_ <- interp_imp ge (denote_expr se) le0;;
      v <- trigger (Call MemHdr.alloc.1 ([s]↑));;
      tau;; tau;; v <- unwrapU (v↓);;
      tau;; tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof using.
    rewrite denote_stmt_Malloc. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_ccallU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Free
        ge le0 pe
    :
      interp_imp ge (denote_stmt (Free pe)) le0 =
      '(le1, p):_ <- interp_imp ge (denote_expr pe) le0;;
      v <- trigger (Call MemHdr.free.1 ([p]↑));;
      tau;; tau;; 'v:val <- unwrapU (v↓);; tau;; Ret (le1, Vundef).
  Proof using.
    rewrite denote_stmt_Free. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_ccallU. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Load
        ge le0 x pe
    :
      interp_imp ge (denote_stmt (Load x pe)) le0 =
      '(le1, p):_ <- interp_imp ge (denote_expr pe) le0;;
      (if (wf_val p) then Ret tt else triggerUB);;;
      v <- trigger (Call MemHdr.load.1 ([p]↑));;
      tau;; tau;; v <- unwrapU (v↓);;
      tau;; tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof using.
    rewrite denote_stmt_Load. rewrite interp_imp_bind. grind.
    des_ifs.
    2:{ rewrite interp_imp_bind. rewrite interp_imp_triggerUB. unfold triggerUB. grind. }
    rewrite interp_imp_bind. grind. rewrite interp_imp_Ret. grind.
    rewrite interp_imp_bind. rewrite interp_imp_ccallU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Store
        ge le0 pe ve
    :
      interp_imp ge (denote_stmt (Store pe ve)) le0 =
      '(le1, p):_ <- interp_imp ge (denote_expr pe) le0;;
      (if (wf_val p) then Ret tt else triggerUB);;;
      '(le2, v):_ <- interp_imp ge (denote_expr ve) le1;;
      v <- trigger (Call MemHdr.store.1 ([p ; v]↑));;
      tau;; tau;; 'v:val <- (v↓)?;; tau;; Ret (le2, Vundef).
  Proof using.
    rewrite denote_stmt_Store. rewrite interp_imp_bind. grind.
    des_ifs.
    2:{ rewrite interp_imp_bind. rewrite interp_imp_triggerUB. unfold triggerUB; grind. }
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_Ret; grind.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_ccallU. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Cmp
        ge le0 x ae be
    :
      interp_imp ge (denote_stmt (Cmp x ae be)) le0 =
      '(le1, a):_ <- interp_imp ge (denote_expr ae) le0;;
      '(le2, b):_ <- interp_imp ge (denote_expr be) le1;;
      (if (wf_val a && wf_val b) then Ret tt else triggerUB);;;
          v <- trigger (Call MemHdr.cmp.1 ([a ; b]↑));;
          tau;; tau;; v <- unwrapU (v↓);;
          tau;; tau;; tau;; Ret (alist_add x v le2, Vundef).
  Proof using.
    rewrite denote_stmt_Cmp. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. grind.
    des_ifs.
    2:{ rewrite interp_imp_bind. rewrite interp_imp_triggerUB. unfold triggerUB; grind. }
    rewrite interp_imp_bind. rewrite interp_imp_Ret; grind.
    rewrite interp_imp_bind. rewrite interp_imp_ccallU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Call_args
        ge le0 x f args
    :
      interp_imp ge (
                   eval_args <- (denote_exprs args);;
                   v <- ccallU (fnsig f imp_fun_t) eval_args;;
                   trigger (SetVar x v);;; tau;; Ret Vundef) le0
      =
      '(le1, vals):_ <- interp_imp ge (denote_exprs args) le0;;
      v <- trigger (Call f (vals↑));;
      tau;; tau;; v <- unwrapU (v↓);;
      tau;; tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof using.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_ccallU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_CallFun
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallFun x f args)) le0 =
      (if (call_ban f) then triggerUB else Ret tt);;;
        '(le1, vals):_ <- interp_imp ge (denote_exprs args) le0;;
        v <- trigger (Call f (vals↑));;
        tau;; tau;; v <- unwrapU (v↓);;
        tau;; tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof using.
    rewrite denote_stmt_CallFun. des_ifs.
    { rewrite interp_imp_triggerUB_bind. unfold triggerUB. grind. }
    rewrite interp_imp_bind. rewrite interp_imp_Ret. grind. apply interp_imp_Call_args.
  Qed.

  Lemma interp_imp_CallPtr
        ge le0 x e args
    :
      interp_imp ge (denote_stmt (CallPtr x e args)) le0 =
      (if match e with
         | Var _ => true
         | _ => false
         end
       then Ret tt else triggerUB);;;
          '(le1, p):_ <- interp_imp ge (denote_expr e) le0;;
          match p with
          | Vptr (n, 0%Z) =>
            match (CEnv.blk2id ge n) with
            | Some f =>
                tau;;
                '(le2, vals):_ <- interp_imp ge (denote_exprs args) le1;;
                v <- trigger (Call f (vals↑));;
                tau;; tau;; v <- unwrapU (v↓);;
                tau;; tau;; tau;; Ret (alist_add x v le2, Vundef)
            | None => triggerUB
            end
          | _ => triggerUB
          end
  .
  Proof using.
    rewrite denote_stmt_CallPtr. des_ifs.
    2,3,4,5,6,7 : rewrite interp_imp_triggerUB_bind; unfold triggerUB; grind.
    rewrite interp_imp_bind. rewrite interp_imp_Ret. grind.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_GetName.
    des_ifs.
    1,5,6:(unfold triggerUB; grind).
    3:{ unfold unwrapU. grind. }
    - unfold unwrapU. grind. apply interp_imp_Call_args.
    - unfold unwrapU. grind.
  Qed.

  Lemma interp_imp_IO_args
        ge le0 x f args
    :
      interp_imp ge (
      ' eval_args : list val <- denote_exprs args;;
      (if forallb (fun v : val => match v with
                                  | Vint _ => true
                                  | _ => false
                                  end) eval_args then Ret () else triggerUB);;;
      (let eval_zs := List.map (fun v : val => match v with
                                               | Vint z => z
                                               | _ => 0%Z
                                               end) eval_args in
       (if forallb intrange_64 eval_zs then Ret () else triggerUB);;;
       v <- trigger (IO f eval_zs);; trigger (SetVar x (Vint v));;; (tau;; Ret Vundef))) le0
      =
      '(le1, vals):_ <- interp_imp ge (denote_exprs args) le0;;
      (if forallb (fun v : val => match v with
                                  | Vint _ => true
                                  | _ => false
                                  end) vals then Ret () else triggerUB);;;
      (let eval_zs := List.map (fun v : val => match v with
                                               | Vint z => z
                                               | _ => 0%Z
                                               end) vals in
      (if (forallb intrange_64 eval_zs) then Ret tt else triggerUB);;;
        v <- trigger (IO f eval_zs);; tau;; tau;;
        tau;; tau;;
        tau;; Ret (alist_add x (Vint v) le1, Vundef)).
  Proof using.
    rewrite interp_imp_bind. grind.
    des_ifs.
    2:{ grind.
        hexploit (@interp_imp_triggerUB_bind unit val ge l
          (λ u,
            v <- trigger (IO f (map (λ v, match v with | Vint z => z | _ => 0%Z end) l0));;
            trigger (SetVar x (Vint v));;;
            (tau;; Ret Vundef))).
        rewrite /triggerUB. i; ss. rewrite bind_bind in H. rewrite H. grind. }
    2:{ rewrite interp_imp_bind. rewrite interp_imp_triggerUB. unfold triggerUB; grind. }
    2:{ rewrite interp_imp_triggerUB_bind. unfold triggerUB; grind. }
    rewrite interp_imp_bind. rewrite interp_imp_Ret; grind.
    rewrite interp_imp_bind. rewrite interp_imp_IO. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    rewrite interp_imp_tau; grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_CallSys
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallSys x f args)) le0 =
      sig <- (alist_find f syscalls)? ;;
      (if (sig =? List.length args)%nat then Ret tt else triggerUB);;;
      '(le1, vals):_ <- interp_imp ge (denote_exprs args) le0;;
      (if forallb (fun v : val => match v with
                                  | Vint _ => true
                                  | _ => false
                                  end) vals then Ret () else triggerUB);;;
      (let eval_zs := List.map (fun v : val => match v with
                                               | Vint z => z
                                               | _ => 0%Z
                                               end) vals in
      (if (forallb intrange_64 eval_zs) then Ret tt else triggerUB);;;
        v <- trigger (IO f eval_zs);; tau;; tau;;
        tau;; tau;;
        tau;; Ret (alist_add x (Vint v) le1, Vundef)).
  Proof using.
    rewrite denote_stmt_CallSys.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    des_ifs.
    2:{ rewrite interp_imp_triggerUB_bind. unfold triggerUB; grind. }
    rewrite interp_imp_bind; rewrite interp_imp_Ret; grind.
    apply interp_imp_IO_args.
  Qed.

  (* eval_imp  *)
  Lemma unfold_eval_imp
        ge fparams fvars fbody args
    :
      ' vret : val <- eval_imp ge (mk_function fparams fvars fbody) args ;; Ret (vret↑)
               =
               ' vret : val <-
                        (
                          let vars := fvars ++ ["return"; "_"] in
                          let params := fparams in
                          (if ListDec.NoDup_dec string_dec (params ++ vars) then Ret tt else triggerUB);;;
                              match init_args params args (init_lenv vars) with
                              | Some iargs =>
                                ' x_ : lenv * val <-
                                       interp_imp ge (tau;; denote_stmt fbody;;; ' retv : val <- denote_expr (Var "return");; Ret retv)
                                                  iargs;; (let (_, retv) := x_ in Ret retv)
                              | None => triggerUB
                              end);; Ret (vret↑).
  Proof using.
    unfold eval_imp. ss.
  Qed.

  Lemma unfold_eval_imp_only
        ge f args
    :
      eval_imp ge f args
      =
      let vars := fn_vars f ++ ["return"; "_"] in
      let params := fn_params f in
      (if ListDec.NoDup_dec string_dec (params ++ vars) then Ret tt else triggerUB);;;
          match init_args params args (init_lenv vars) with
          | Some iargs =>
            ' x_ : lenv * val <-
                   interp_imp ge (tau;; denote_stmt (fn_body f);;; ' retv : val <- denote_expr (Var "return");; Ret retv)
                              iargs;; (let (_, retv) := x_ in Ret retv)
          | None => triggerUB
          end
  .
  Proof using. ss. Qed.

End PROOFS.
