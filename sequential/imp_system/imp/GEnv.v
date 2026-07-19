From CRIS.lib Require Import Any AList.
From CRIS.iris_system Require Import sProp.
Import ListNotations.

Module GEnv.
  Definition t := alist string Any.t.
  Definition wf (genv : t) := List.NoDup (List.map fst genv).
  Definition unit : t := [].
  Definition add (genv1 genv2 : t) : t := genv1 ++ genv2.
  Definition equiv (genv1 genv2 : t) : Prop := genv1 ≡ₚ genv2.

  Lemma equiv_wf (genv1 genv2 : t) (EQV : equiv genv1 genv2) (WF : wf genv1) :
    wf genv2.
  Proof. eapply Permutation_NoDup, WF. eapply Permutation_map. eauto. Qed.

  Lemma equiv_incl (genv1 genv2 : t) (EQV : equiv genv1 genv2) :
    List.incl genv1 genv2.
  Proof. ii. eapply Permutation_in, H. apply EQV. Qed.

  Lemma equiv_ctx genv0 genv1 ctx (EQV : equiv genv0 genv1) :
    equiv (add genv0 ctx) (add genv1 ctx).
  Proof. eapply Permutation_app_tail. eauto. Qed.
  
End GEnv.
