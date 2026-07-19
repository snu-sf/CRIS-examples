Require Import CRIS.common.CRIS.

Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Loc.
Require Import Val.
Require Import Event.

Require Import Time.
Require Import View.
Require Import BoolMap.
Require Import Promises.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module Global.
  Structure t := mk {
    sc: View.t;
    promises: Promises.t;
    free_promises: FreePromises.t;
    memory: Memory.t;
  }.

  Definition init (size: list Z) := mk (View.init size) Promises.bot FreePromises.bot (Memory.init size).

  Variant wf (gl: t): Prop :=
  | wf_intro
      (SC_CLOSED: Memory.closed_view (sc gl) (memory gl))
      (MEM_CLOSED: Memory.closed (memory gl))
      (MEM_WELL_ALLOCED: Memory.well_alloced (memory gl))
  .
  #[global] Hint Constructors wf: core.

  Lemma init_wf size
    (SIZE: List.Forall (fun sz : Z => (0 <= sz)%Z) size):
    wf (init size).
  Proof.
    econs; ss.
    - apply Memory.closed_view_init.
    - apply Memory.init_closed.
    - apply Memory.init_well_alloced. eauto.
  Qed.

  (* Additional *)
  Definition promise_free (gl : t) : Prop :=
    promises gl = Promises.bot ∧ free_promises gl = FreePromises.bot.

  Lemma init_promise_free sz : promise_free (init sz). by ss. Qed.

  Variant cap (gl gl_cap: t): Prop :=
  | cap_intro
      (SC: sc gl_cap = sc gl)
      (PRM: promises gl_cap = promises gl)
      (FPRM: free_promises gl_cap = free_promises gl)
      (MEM: Memory.cap (memory gl) (memory gl_cap))
  .
  #[global] Hint Constructors cap: core.
  
  Definition cap_of (gl: t): t :=
    mk (sc gl) (promises gl) (free_promises gl) (Memory.cap_of (memory gl)).

  Lemma cap_of_cap gl:
    cap gl (cap_of gl).
  Proof.
    unfold cap_of. exploit Memory.cap_of_cap. i. des. econs; eauto.
  Qed.

  Lemma cap_wf
        gl gl_cap
        (WF: wf gl)
        (CAP: cap gl gl_cap)
        (WELL_ALLOC: Memory.well_alloced (memory gl_cap)):
    wf gl_cap.
  Proof.
    inv WF. inv CAP.
    econs; s; eauto.
    - rewrite SC. eapply Memory.cap_closed_view; eauto.
    - eapply Memory.cap_closed; eauto.
  Qed.

  Lemma cap_of_wf
        gl
        (WF: wf gl):
    wf (cap_of gl).
  Proof.
    eapply cap_wf; eauto using cap_of_cap.
    unfold cap_of. ss. eapply Memory.cap_of_well_alloced. eapply WF.
  Qed.

  Variant state_future (gl gl': Global.t): Prop :=
  | state_future_intro
      (SC: sc gl' = sc gl)
      (PRM: promises gl' = promises gl)
      (FPRM: free_promises gl' = free_promises gl)
      (MEMORY: Memory.state_future (memory gl) (memory gl'))
  .

  Variant future (gl1 gl2: t): Prop :=
  | future_intro
      (SC: View.le (sc gl1) (sc gl2))
      (MEMORY: Memory.future (memory gl1) (memory gl2))
  .
  #[global] Hint Constructors future: core.

  Lemma future_refl
        gl
        (WF: wf gl):
    future gl gl.
  Proof.
    inv WF. econs; try refl. econs; eauto.
    - econs; eauto. refl.
  Qed.

  Lemma future_trans
        gl1 gl2 gl3
        (FUTURE1: future gl1 gl2)
        (FUTURE2: future gl2 gl3):
    future gl1 gl3.
  Proof.
    econs; try by etrans; [eapply FUTURE1|eapply FUTURE2].
    eapply Memory.future_trans; [eapply FUTURE1|eapply FUTURE2].
  Qed.

  Variant prm_rel (gl1 gl2: t): Prop :=
  | prm_rel_intro
      (PRMR: forall loc,
          (<<PROMISES: implb (gl1.(promises) loc) (gl2.(promises) loc)>>) \/
          (<<LATEST: Memory.na_added_latest loc gl1.(memory) gl2.(memory)>>) \/
          (<<FREED: Memory.freed_latest loc gl1.(memory) gl2.(memory)>>))
  .

  Variant fprm_rel (gl1 gl2: t): Prop :=
  | fprm_fulfill_intro
      (FPRMR: forall loc,
          (<<FPROMISE: implb (gl1.(free_promises) (Loc.get_tbid loc)) (gl2.(free_promises) (Loc.get_tbid loc))>>) \/
          (<<FREED: Memory.freed_latest loc gl1.(memory) gl2.(memory)>>))
  .
       
  Variant strong_future (gl1 gl2: t): Prop :=
  | strong_future_intro
      (FUTURE: future gl1 gl2)
      (PRMR: prm_rel gl1 gl2)
      (FPRMR: fprm_rel gl1 gl2)
  .
  #[global] Hint Constructors strong_future: core.

  Lemma strong_future_refl
        gl
        (WF: wf gl):
    strong_future gl gl.
  Proof.
    inv WF. econs.
    - eapply future_refl; eauto.
    - econs. i. left. ss. rewrite Bool.implb_same. auto.
    - econs. i. left. ss. rewrite Bool.implb_same. auto.
  Qed.

  Lemma strong_future_trans
        gl1 gl2 gl3
        (SFUTURE1: strong_future gl1 gl2)
        (SFUTURE2: strong_future gl2 gl3):
    strong_future gl1 gl3.
  Proof.
    destruct gl1, gl2, gl3. inv SFUTURE1. inv SFUTURE2. ss. econs.
    - eapply future_trans; [eapply FUTURE|eapply FUTURE0].
    - econs. i. ss. destruct (promises0 loc) eqn:PRM0.
      { destruct (promises2 loc) eqn:PRM2.
        { left. ss. }
        destruct (promises1 loc) eqn:PRM1.
        { right. inv PRMR0. ss. hexploit PRMR1; eauto.
          erewrite PRM1. rewrite PRM2. i. des; ss.
          - left. eapply Memory.na_added_latest_le.
            { inv FUTURE. inv MEMORY. ss. eauto. }
            { eauto. }
            { reflexivity. }
          - right. r. inv FREED. econs; eauto. inv FUTURE. ss.
            inv MEMORY. inv MESSAGE_LE. specialize (STATES loc).
            unfold Memory.is_freed, Block.is_freed, Block.state_t_le, Memory.get_state in *.
            des_ifs.
        }
        { right. inv PRMR. ss. hexploit PRMR1; eauto.
          erewrite PRM0. rewrite PRM1. i. des; ss.
          - left. eapply Memory.na_added_latest_le.
            { reflexivity. }
            { eauto. }
            { inv FUTURE0. inv MEMORY. ss. }
          - right. r. inv FREED. econs; eauto.
            inv FUTURE0. inv MEMORY. inv MESSAGE_LE.
            specialize (STATES loc). ss.
            unfold Memory.is_freed, Block.is_freed, Block.state_t_le, Memory.get_state in *.
            des_ifs.
        }
      }
      econs; etrans; eauto.
    - econs. i. ss. destruct (free_promises0 (Loc.get_tbid loc)) eqn:FPRM0.
      { destruct (free_promises2 (Loc.get_tbid loc)) eqn:FPRM2.
        { left. ss. }
        destruct (free_promises1 (Loc.get_tbid loc)) eqn:FPRM1.
        { right. inv FPRMR0. ss. hexploit FPRMR1; eauto.
          erewrite FPRM1. rewrite FPRM2. i. des; ss.
          r. inv FREED. econs; eauto.  inv FUTURE. ss.
          inv MEMORY. inv MESSAGE_LE. specialize (STATES loc).
          unfold Memory.is_freed, Block.is_freed, Block.state_t_le, Memory.get_state in *.
          des_ifs.
        }
        { right. inv FPRMR. ss. hexploit FPRMR1; eauto.
          erewrite FPRM0. rewrite FPRM1. i. des; ss.
          r. inv FREED. econs; eauto.
          inv FUTURE0. inv MEMORY. inv MESSAGE_LE.
          specialize (STATES loc). ss.
          unfold Memory.is_freed, Block.is_freed, Block.state_t_le, Memory.get_state in *.
          des_ifs.
        }
      }
      eauto.
  Qed.

  Lemma cap_strong_future
    gl gl_cap
    (CAP: gl_cap = cap_of gl)
    (WF: wf gl):
    strong_future gl gl_cap.
  Proof.
    destruct gl, gl_cap. inv CAP. inv WF. econs.
    { econs; s; try refl.
      eapply Memory.cap_of_future; eauto.
    }
    { econs. i. left. ss. rewrite Bool.implb_same. auto. }
    { econs. i. left. ss. rewrite Bool.implb_same. auto. }
  Qed.

End Global.

