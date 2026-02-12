(* Definitions of lattices partially copied from gpfsl *)
From Coq Require Export Utf8 ssreflect.
From stdpp Require Export prelude finite gmap.
From stdpp Require Import sorting.

Global Open Scope general_if_scope.
(** SqSubsetEq, Join and Meet notations **)

Infix "⊑*" := (Forall2 (⊑)) (at level 70) : stdpp_scope.
Notation "(⊑*)" := (Forall2 (⊑)) (only parsing) : stdpp_scope.
Infix "⊑**" := (Forall2 (⊑*)) (at level 70) : stdpp_scope.
Infix "⊑1*" := (Forall2 (λ p q, p.1 ⊑ q.1)) (at level 70) : stdpp_scope.
Infix "⊑2*" := (Forall2 (λ p q, p.2 ⊑ q.2)) (at level 70) : stdpp_scope.
Infix "⊑1**" := (Forall2 (λ p q, p.1 ⊑* q.1)) (at level 70) : stdpp_scope.
Infix "⊑2**" := (Forall2 (λ p q, p.2 ⊑* q.2)) (at level 70) : stdpp_scope.

Infix "⊏" := (strict sqsubseteq) (at level 70) : stdpp_scope.
Notation "(⊏)" := (strict sqsubseteq) (only parsing) : stdpp_scope.
Notation "( X ⊏)" := (sqsubseteq X) (only parsing) : stdpp_scope.
Notation "(⊏ X )" := (λ Y, Y ⊏ X) (only parsing) : stdpp_scope.
Infix "⊏*" := (Forall2 (⊏)) (at level 70) : stdpp_scope.
Notation "(⊏*)" := (Forall2 (⊏)) (only parsing) : stdpp_scope.
Infix "⊏**" := (Forall2 (⊏*)) (at level 70) : stdpp_scope.
Infix "⊏1*" := (Forall2 (λ p q, p.1 ⊏ q.1)) (at level 70) : stdpp_scope.
Infix "⊏2*" := (Forall2 (λ p q, p.2 ⊏ q.2)) (at level 70) : stdpp_scope.
Infix "⊏1**" := (Forall2 (λ p q, p.1 ⊏* q.1)) (at level 70) : stdpp_scope.
Infix "⊏2**" := (Forall2 (λ p q, p.2 ⊏* q.2)) (at level 70) : stdpp_scope.
Global Instance Strict_sqsubseteq_Rewrite `{SqSubsetEq T} : @RewriteRelation T (⊏) := {}.

Infix "⊔*" := (zip_with (⊔)) (at level 50, left associativity) : stdpp_scope.
Notation "(⊔*)" := (zip_with (⊔)) (only parsing) : stdpp_scope.
Infix "⊔**" := (zip_with (zip_with (⊔)))
  (at level 50, left associativity) : stdpp_scope.
Infix "⊔*⊔**" := (zip_with (prod_zip (⊔) (⊔*)))
  (at level 50, left associativity) : stdpp_scope.

Infix "⊓*" := (zip_with (⊓)) (at level 40, left associativity) : stdpp_scope.
Notation "(⊓*)" := (zip_with (⊓)) (only parsing) : stdpp_scope.
Infix "⊓**" := (zip_with (zip_with (⊓)))
  (at level 40, left associativity) : stdpp_scope.
Infix "⊓*⊓**" := (zip_with (prod_zip (⊓) (⊓*)))
  (at level 40, left associativity) : stdpp_scope.

(* Lattice canonical structure *)
Structure latticeT : Type := Make_Lat {
  lat_ty :> Type;
  lat_equiv : Equiv lat_ty;
  lat_sqsubseteq : SqSubsetEq lat_ty;
  #[canonical=no]
  lat_join : Join lat_ty;
  #[canonical=no]
  lat_meet : Meet lat_ty;

  #[canonical=no]
  lat_inhabited : Inhabited lat_ty;
  #[canonical=no]
  lat_sqsubseteq_proper : Proper ((≡) ==> (≡@{lat_ty}) ==> iff) (⊑);
  #[canonical=no]
  lat_join_proper : Proper ((≡) ==> (≡) ==> (≡@{lat_ty})) (⊔);
  #[canonical=no]
  lat_meet_proper : Proper ((≡) ==> (≡) ==> (≡@{lat_ty})) (⊓);
  #[canonical=no]
  lat_equiv_equivalence : Equivalence (≡@{lat_ty});
  #[canonical=no]
  lat_pre_order : PreOrder (⊑@{lat_ty});
  #[canonical=no]
  lat_sqsubseteq_antisym : AntiSymm (≡@{lat_ty}) (⊑);
  #[canonical=no]
  lat_join_sqsubseteq_l (X Y : lat_ty) : X ⊑ X ⊔ Y;
  #[canonical=no]
  lat_join_sqsubseteq_r (X Y : lat_ty) : Y ⊑ X ⊔ Y;
  #[canonical=no]
  lat_join_lub (X Y Z : lat_ty) : X ⊑ Z → Y ⊑ Z → X ⊔ Y ⊑ Z;
  #[canonical=no]
  lat_meet_sqsubseteq_l (X Y : lat_ty) : X ⊓ Y ⊑ X;
  #[canonical=no]
  lat_meet_sqsubseteq_r (X Y : lat_ty) : X ⊓ Y ⊑ Y;
  #[canonical=no]
  lat_meet_glb (X Y Z : lat_ty) : X ⊑ Y → X ⊑ Z → X ⊑ Y ⊓ Z
}.
Arguments lat_equiv : simpl never.
Arguments lat_sqsubseteq : simpl never.
Arguments lat_join : simpl never.
Arguments lat_join_sqsubseteq_l {_} _ _.
Arguments lat_join_sqsubseteq_r {_} _ _.
Arguments lat_join_lub {_} _ _ _.
Arguments lat_meet : simpl never.
Arguments lat_meet_sqsubseteq_l {_} _ _.
Arguments lat_meet_sqsubseteq_r {_} _ _.
Arguments lat_meet_glb {_} _ _ _.
Global Existing Instances lat_equiv lat_sqsubseteq lat_join lat_meet
       lat_inhabited lat_sqsubseteq_proper lat_sqsubseteq_antisym
       lat_join_proper lat_meet_proper lat_equiv_equivalence lat_pre_order.

Lemma lat_join_sqsubseteq_or (Lat : latticeT) (X Y Z : Lat) :
  Z ⊑ X ∨ Z ⊑ Y → Z ⊑ X ⊔ Y.
Proof.
  intros [H|H]; (etrans; [apply H|]);
    [apply lat_join_sqsubseteq_l|apply lat_join_sqsubseteq_r].
Qed.

Lemma lat_meet_sqsubseteq_or (Lat : latticeT) (X Y Z : Lat) :
  X ⊑ Z ∨ Y ⊑ Z → X ⊓ Y ⊑ Z.
Proof.
  intros [H|H]; (etrans; [|apply H]);
    [apply lat_meet_sqsubseteq_l|apply lat_meet_sqsubseteq_r].
Qed.

Create HintDb lat.
Ltac solve_lat := by typeclasses eauto with lat core.
Global Hint Resolve lat_join_lub lat_meet_glb : lat.
Global Hint Extern 0 (?a ⊑ ?b) =>
  (* We first check whether a and b are unifiable, in order not to
     trigger typeclass search for Reflexivity when this is not needed. *)
  unify a b with lat; reflexivity : lat.
Global Hint Extern 0 (_ = _) => apply (anti_symm (⊑)) : lat.
Global Hint Extern 0 (_ ≡ _) => apply (anti_symm (⊑)) : lat.
Global Hint Resolve lat_join_sqsubseteq_or | 10 : lat.
Global Hint Resolve lat_meet_sqsubseteq_or | 10 : lat.
Global Hint Extern 100 (?a ⊑ ?c) =>
  match goal with H : a ⊑ ?b |- _ => transitivity b; [exact H|] end
  : lat.
Global Hint Extern 200 (?a ⊑ ?c) =>
  match goal with H : ?b ⊑ c |- _ => transitivity b; [|exact H] end
  : lat.

Section Lat.

Context {Lat : latticeT}.

Global Instance lat_sqsubseteq_order_L `{!LeibnizEquiv Lat} :
  PartialOrder (A:=Lat) (⊑).
Proof.
  split; [apply lat_pre_order|] => x y ??.
  by apply leibniz_equiv, (anti_symm (⊑)).
Qed.

Global Instance lat_join_assoc : @Assoc Lat (≡) (⊔).
Proof. intros ???; solve_lat. Qed.
Global Instance lat_join_assoc_L `{!LeibnizEquiv Lat} : @Assoc Lat (=) (⊔).
Proof. intros ???. solve_lat. Qed.

Global Instance lat_join_comm : @Comm Lat Lat (≡) (⊔).
Proof. intros ??; solve_lat. Qed.
Global Instance lat_join_comm_L `{!LeibnizEquiv Lat} : @Comm Lat Lat (=) (⊔).
Proof. intros ??; solve_lat. Qed.

Global Instance lat_join_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) (@join Lat _).
Proof. intros ?????. solve_lat. Qed.
Global Instance lat_join_mono_flip :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@join Lat _).
Proof. solve_proper. Qed.

Lemma lat_le_join_l (x y : Lat) : y ⊑ x → x ⊔ y ≡ x.
Proof. solve_lat. Qed.
Lemma lat_le_join_l_L `{!LeibnizEquiv Lat} (x y : Lat) : y ⊑ x → x ⊔ y = x.
Proof. solve_lat. Qed.

Lemma lat_le_join_r (x y : Lat) : x ⊑ y → x ⊔ y ≡ y.
Proof. solve_lat. Qed.
Lemma lat_le_join_r_L `{!LeibnizEquiv Lat} (x y : Lat) : x ⊑ y → x ⊔ y = y.
Proof. solve_lat. Qed.

Lemma lat_join_idem (x : Lat) : x ⊔ x ≡ x.
Proof. solve_lat. Qed.
Lemma lat_join_idem_L `{!LeibnizEquiv Lat} (x : Lat) : x ⊔ x = x.
Proof. solve_lat. Qed.

Global Instance lat_meet_assoc : @Assoc Lat (≡) (⊓).
Proof. intros ???; solve_lat. Qed.
Global Instance lat_meet_assoc_L `{!LeibnizEquiv Lat} : @Assoc Lat (=) (⊓).
Proof. intros ???. solve_lat. Qed.

Global Instance lat_meet_comm : @Comm Lat Lat (≡) (⊓).
Proof. intros ??; solve_lat. Qed.
Global Instance lat_meet_comm_L `{!LeibnizEquiv Lat} : @Comm Lat Lat (=) (⊓).
Proof. intros ??; solve_lat. Qed.

Global Instance lat_meet_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) (@meet Lat _).
Proof. intros ?????. solve_lat. Qed.
Global Instance lat_meet_mono_flip :
  Proper (flip (⊑) ==> flip (⊑) ==> flip (⊑)) (@meet Lat _).
Proof. solve_proper. Qed.

Lemma lat_le_meet_l (x y : Lat) : x ⊑ y → x ⊓ y ≡ x.
Proof. solve_lat. Qed.
Lemma lat_le_meet_l_L `{!LeibnizEquiv Lat} (x y : Lat) : x ⊑ y → x ⊓ y = x.
Proof. solve_lat. Qed.

Lemma lat_le_meet_r (x y : Lat) : y ⊑ x → x ⊓ y ≡ y.
Proof. solve_lat. Qed.
Lemma lat_le_meet_r_L `{!LeibnizEquiv Lat} (x y : Lat) : y ⊑ x → x ⊓ y = y.
Proof. solve_lat. Qed.

Lemma lat_meet_idem (x : Lat) : x ⊓ x ≡ x.
Proof. solve_lat. Qed.
Lemma lat_meet_idem_L `{!LeibnizEquiv Lat} (x : Lat) : x ⊓ x = x.
Proof. solve_lat. Qed.

(* Lattices with a bottom element. *)
Class LatBottom (bot : Lat) :=
 lat_bottom_sqsubseteq X : bot ⊑ X.
Hint Resolve lat_bottom_sqsubseteq : lat.

Global Instance lat_join_bottom_rightid `{!LatBottom bot} : RightId (≡) bot (⊔).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_join_bottom_rightid_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  RightId (=) bot (⊔).
Proof. intros ?; solve_lat. Qed.

Global Instance lat_join_bottom_leftid `{!LatBottom bot} : LeftId (≡) bot (⊔).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_join_bottom_leftid_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  LeftId (=) bot (⊔).
Proof. intros ?; solve_lat. Qed.

Global Instance lat_meet_bottom_leftabsorb `{!LatBottom bot} (x : Lat) :
  LeftAbsorb (≡) bot (⊓).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_meet_bottom_leftabsorb_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  LeftAbsorb (=) bot (⊓).
Proof. intros ?. solve_lat. Qed.

Global Instance lat_meet_bottom_rightabsorb `{!LatBottom bot} (x : Lat) :
  RightAbsorb (≡) bot (⊓).
Proof. intros ?; solve_lat. Qed.
Global Instance lat_meet_bottom_rightabsorb_L `{!LeibnizEquiv Lat} `{!LatBottom bot} :
  RightAbsorb (=) bot (⊓).
Proof. intros ?. solve_lat. Qed.

End Lat.

Global Hint Resolve lat_bottom_sqsubseteq : lat.

(** Lattice for product **)

Section Prod.

Context (A B : latticeT).

Program Canonical Structure prod_Lat :=
  Make_Lat (A * B) prod_equiv (prod_relation (⊑) (⊑))
           (λ p1 p2, (p1.1 ⊔ p2.1, p1.2 ⊔ p2.2))
           (λ p1 p2, (p1.1 ⊓ p2.1, p1.2 ⊓ p2.2))
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  intros ??[a b]??[c d]. split=>-[??]; split;
  rewrite -?a -?b // -?c -?d // ?a ?c // ?b ?d //.
Qed.
Next Obligation.
  intros ??[a b]??[c d]. split; rewrite /= ?a ?c // ?b ?d //.
Qed.
Next Obligation.
  intros ??[a b]??[c d]. split; rewrite /= ?a ?c // ?b ?d //.
Qed.
Next Obligation.
  split; [apply: prod_relation_refl | apply: prod_relation_trans].
Qed.
Next Obligation. intros ??[??][??]; split; by apply (anti_symm (⊑)). Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??? [??] [??]. by split; solve_lat. Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??. split; solve_lat. Qed.
Next Obligation. intros ??? [??] [??]. by split; solve_lat. Qed.

Global Instance prod_sqsubseteq_dec :
  RelDecision (A:=A) (⊑) → RelDecision (A:=B) (⊑) → RelDecision (A:=A * B) (⊑).
Proof.
  move => ?? ab ab'.
  case: (decide (fst ab ⊑ fst ab'));
  case: (decide (snd ab ⊑ snd ab'));
    [left => //|right|right|right]; move => []; abstract naive_solver.
Qed.

Global Instance prod_latbottom `{!@LatBottom A botA, !@LatBottom B botB} :
  LatBottom (botA, botB).
Proof. split; solve_lat. Qed.

Global Instance fst_lat_mono : Proper ((⊑) ==> (⊑)) (@fst A B).
Proof. move => [??][??][-> _]//. Qed.

Global Instance snd_lat_mono : Proper ((⊑) ==> (⊑)) (@snd A B).
Proof. move => [??][??][_ ->]//. Qed.

Lemma lat_join_fst x y :
  fst (x ⊔ y) = fst x ⊔ fst y.
Proof. done. Qed.

Lemma lat_join_snd x y :
  snd (x ⊔ y) = snd x ⊔ snd y.
Proof. done. Qed.

End Prod.

(** Lattice for option. None is the bottom element. **)

Global Instance option_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (option A) :=
  λ o1 o2, if o1 is Some x1 return _ then
              if o2 is Some x2 return _ then x1 ⊑ x2 else False
           else True.

Global Instance option_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
  @PreOrder (option A) (⊑).
Proof.
  split.
  - move=>[x|] //. apply (@reflexivity A (⊑) _).
  - move=>[x|] [y|] [z|] //. apply (@transitivity A (⊑) _).
Qed.


Global Instance option_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
  @PartialOrder (option A) (⊑).
Proof.
  split; [apply _|].
  move => [?|] [?|] ??; [|done|done|done]. f_equal. by apply : (anti_symm (⊑)).
Qed.

Section option.

Context (Lat : latticeT).

Program Canonical Structure option_Lat :=
  Make_Lat (option Lat) option_equiv option_sqsubseteq
           (λ o1 o2, if o1 is Some x1 return _ then
                       if o2 is Some x2 return _ then Some (x1 ⊔ x2) else o1
                     else o2)
           (λ o1 o2, if o1 is Some x1 return _ then
                       if o2 is Some x2 return _ then Some (x1 ⊓ x2) else None
                     else None) _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  intros ??[???|]??[???|]; try by split. by apply lat_sqsubseteq_proper.
Qed.
Next Obligation.
  intros ??[?? EQ1|]??[?? EQ2|]=>//; constructor; by setoid_subst.
Qed.
Next Obligation.
  intros ??[?? EQ1|]??[?? EQ2|]=>//; constructor; by setoid_subst.
Qed.
Next Obligation. move=>[x|] [y|] //. constructor. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] [z|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] //. solve_lat. Qed.
Next Obligation. move=>[x|] [y|] [z|] //. solve_lat. Qed.

Global Instance option_sqsubseteq_dec :
  RelDecision (A:=Lat) (⊑) → RelDecision (A:=option Lat) (⊑).
Proof.
  move=>DEC [a|][a'|]; unfold Decision; [edestruct (DEC a a')|..]; auto with lat.
Qed.

Global Instance option_latbottom : LatBottom (@None Lat).
Proof. done. Qed.

Global Instance option_Total `{!@Total Lat (⊑)}:
  @Total (option Lat) (⊑).
Proof.
  move => [x|] [y|]; (try by right); (try by left). destruct (total (⊑) x y); auto.
Qed.

Global Instance Some_mono : Proper ((⊑) ==> (⊑)) (@Some Lat).
Proof. solve_proper. Qed.
Global Instance Some_mono_flip : Proper (flip (⊑) ==> flip (⊑)) (@Some Lat).
Proof. solve_proper. Qed.

(* Global Instance fmap_sqsubseteq_mono f : *)
(*   Proper ((⊑) ==> (⊑)) f -> *)
(*   Proper ((⊑) ==> (⊑)) (@fmap option option_fmap Lat (option Lat) f). *)
(* Proof. *)
(*   move => H. *)
(*   repeat move => ? ? S. rewrite /fmap /option_fmap /option_map. *)
(*   repeat case_match; simplify_option_eq; cbn; [by apply H|destruct S|done|done]. *)
(* Qed. *)

Lemma fmap_sqsubseteq `{Lat2 : latticeT} (f : Lat -> Lat2) (x y : option Lat) {H : Proper ((⊑) ==> (⊑)) f} :
  x ⊑ y -> fmap f x ⊑ fmap f y.
Proof.
  rewrite /fmap/option_fmap/option_map.
  repeat case_match; simplify_option_eq; cbn; [by apply H|inversion 1|done|done].
Qed.

End option.

Global Instance from_option_bot_proper {A: latticeT} `{@LatBottom B bot}
  (f: A → B) `{!Proper ((⊑) ==> (⊑)) f} :
  Proper ((⊑) ==> (⊑)) (from_option f bot).
Proof. move => [?|] [?|] ?; [solve_proper|done..]. Qed.


Section Forall2.
  Context {A} (R : relation A).

  Global Instance option_Forall2_refl : Reflexive R → Reflexive (option_Forall2 R).
  Proof. intros ? [?|]; by constructor. Qed.
  Global Instance option_Forall2_sym : Symmetric R → Symmetric (option_Forall2 R).
  Proof. destruct 2; by constructor. Qed.
  Global Instance option_Forall2_trans : Transitive R → Transitive (option_Forall2 R).
  Proof. destruct 2; inversion_clear 1; constructor; etrans; eauto. Qed.
  Global Instance option_Forall2_equiv : Equivalence R → Equivalence (option_Forall2 R).
  Proof. destruct 1; split; apply _. Qed.
End Forall2.

(** Lattice for gmap **)

Section gmap.
Context K `{Countable K}.

Global Instance gmap_sqsubseteq `{SqSubsetEq A} : SqSubsetEq (gmap K A) :=
  λ m1 m2, ∀ i, m1 !! i ⊑@{option A} m2 !! i.

Global Instance gmap_sqsubseteq_preorder `{SqSubsetEq A} `{!@PreOrder A (⊑)} :
  @PreOrder (gmap K A) (⊑).
Proof. split=>??//? LE1 LE2 ?; etrans; [apply LE1|apply LE2]. Qed.

Global Instance gmap_sqsubseteq_po `{SqSubsetEq A} `{!@PartialOrder A (⊑)} :
  @PartialOrder (gmap K A) (⊑).
Proof.
  constructor; [apply _|].
  move => ????. apply map_eq => ?. by apply : (anti_symm (⊑)).
Qed.

Global Instance gmap_key_filter {A} : Filter K (gmap K A) :=
  λ P _, filter (λ kv, P (kv.1)).


Context (A : latticeT).

Program Canonical Structure gmap_Lat :=
  Make_Lat (gmap K A) map_equiv gmap_sqsubseteq
           (union_with (λ x1 x2, Some (x1 ⊔ x2)))
           (intersection_with (λ x1 x2, Some (x1 ⊓ x2)))
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. move=> ??? ???; split=>??; setoid_subst=>//. Qed.
Next Obligation.
  move=> X1 Y1 EQ1 X2 Y2 EQ2 i. rewrite !lookup_union_with.
  by destruct (EQ1 i), (EQ2 i); setoid_subst.
Qed.
Next Obligation.
  move=> X1 Y1 EQ1 X2 Y2 EQ2 i. rewrite !lookup_intersection_with.
  by destruct (EQ1 i), (EQ2 i); setoid_subst.
Qed.
Next Obligation.
  move=>?? LE1 LE2 ?. apply (anti_symm (⊑)); [apply LE1|apply LE2].
Qed.
Next Obligation.
  move=>???. rewrite lookup_union_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>???. rewrite lookup_union_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>??? LE1 LE2 i. rewrite lookup_union_with.
  specialize (LE1 i). specialize (LE2 i).
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>???. rewrite lookup_intersection_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>???. rewrite lookup_intersection_with.
  repeat destruct lookup=>//. solve_lat.
Qed.
Next Obligation.
  move=>??? LE1 LE2 i. rewrite lookup_intersection_with.
  specialize (LE1 i). specialize (LE2 i).
  repeat destruct lookup=>//. solve_lat.
Qed.

Global Instance gmap_bottom : LatBottom (@empty (gmap K A) _).
Proof. done. Qed.

Global Instance gmap_sqsubseteq_dec :
  RelDecision (A:=A) (⊑) → RelDecision (A:=gmap K A) (⊑).
Proof.
  move => ? m m'.
  destruct (decide (set_Forall (λ k, m !! k ⊑ m' !! k) (dom m))) as [Y|N].
  - left => k.
    case: (decide (k ∈ dom m)).
    + by move/Y.
    + move/not_elem_of_dom => -> //.
  - right.
    apply not_set_Forall_Exists in N; last apply _.
    case : N => x [/elem_of_dom [a ?]] NSqsubseteq ?. by apply NSqsubseteq.
Qed.

Global Instance lookup_mono l :
  Proper ((⊑) ==> (⊑)) (@lookup K A (gmap K A) _ l).
Proof. intros ?? Le. apply Le. Qed.
Global Instance lookup_mono_flip l :
  Proper (flip (⊑) ==> flip (⊑)) (@lookup K A (gmap K A) _ l).
Proof. solve_proper. Qed.

Global Instance gmap_sqsubseteq_dom_proper :
  Proper ((@sqsubseteq (gmap K A) _) ==> (⊆)) (dom).
Proof.
  move => m1 m2 Sqsubseteq k /elem_of_dom [a Eqa].
  specialize (Sqsubseteq k). rewrite Eqa in Sqsubseteq.
  destruct (m2 !! k) as [|] eqn:Eq2; last done.
  apply elem_of_dom. by eexists.
Qed.

Lemma gmap_join_dom_union (m1 m2 : gmap K A):
  dom (m1 ⊔ m2) ≡@{gset K} dom m1 ∪ dom m2.
Proof.
  move => k. rewrite elem_of_union 3!elem_of_dom lookup_union_with /=.
  case (m1 !! k) => [v1|]; case (m2 !! k) => [v2|] /=; naive_solver.
Qed.

Lemma gmap_meet_dom_intersection (m1 m2 : gmap K A):
  dom (m1 ⊓ m2) ≡@{gset K} dom m1 ∩ dom m2.
Proof.
  move => k. rewrite elem_of_intersection 3!elem_of_dom lookup_intersection_with /=.
  case (m1 !! k) => [v1|]; case (m2 !! k) => [v2|] /=; naive_solver.
Qed.

Lemma lookup_join (m1 m2 : gmap K A) k:
  (m1 ⊔ m2) !! k = m1 !! k ⊔ m2 !! k.
Proof. rewrite lookup_union_with. by do 2!case: (_ !! k). Qed.

Lemma lookup_meet (m1 m2 : gmap K A) k:
  (m1 ⊓ m2) !! k = m1 !! k ⊓ m2 !! k.
Proof. rewrite lookup_intersection_with. by do 2!case: (_ !! k). Qed.

Global Instance gmap_leibniz_eq :
  LeibnizEquiv A → LeibnizEquiv (gmap K A).
Proof. intros. apply map_leibniz. Qed.

End gmap.

Lemma gmap_subseteq_empty `{Countable K} {A} (m : gmap K A) : ∅ ⊆ m.
Proof. intros ?. rewrite lookup_empty. by case lookup. Qed.

Lemma gset_to_gmap_sqsubseteq `{Countable K} `{SqSubsetEq A}
  (m1 m2: gset K) (a b: A) (Sub: m1 ⊆ m2) (Ext: a ⊑ b) :
  gset_to_gmap a m1 ⊑ gset_to_gmap b m2.
Proof.
  intros i.
  destruct (gset_to_gmap a m1 !! i) as [a'|] eqn:Eq; last done.
  apply lookup_gset_to_gmap_Some in Eq as [In ?]. subst a'.
  rewrite (_: gset_to_gmap b m2 !! i = Some b).
  - apply lookup_gset_to_gmap_Some. split; last done. by apply Sub.
  - by apply Ext.
Qed.

(** Lattice for positive *)
Program Canonical Structure pos_Lat :=
  Make_Lat (positive) (=) (≤)%positive
           (λ (p q : positive), if (decide (p ≤ q)%positive) then q else p)
           (λ (p q : positive), if (decide (p ≤ q)%positive) then p else q)
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. move=>x y ??. erewrite Pos.le_antisym; eauto. Qed.
Next Obligation. move=>x y. unfold join. destruct decide=>//. Qed.
Next Obligation.
  move=> x y. unfold join. destruct decide => //. apply Pos.le_nlt. lia.
Qed.
Next Obligation. move=>x y z. unfold join; destruct decide=>?? //. Qed.
Next Obligation.
  move=>x y. unfold meet. destruct decide => //. apply Pos.le_nlt. lia.
Qed.
Next Obligation. move=>x y. unfold meet. destruct decide=>//. Qed.
Next Obligation. move=>x y z. unfold meet; destruct decide=>?? //. Qed.

Global Instance pos_leibnizequiv : LeibnizEquiv positive := λ _ _ H, H.

Global Instance pos_Total : Total (@sqsubseteq positive _).
Proof.
  move => x y. case: (decide (x ≤ y)%positive); first tauto.
  move => /Pos.lt_nle /Pos.lt_le_incl. tauto.
Qed.

Global Instance pos_sqsubseteq_decision : RelDecision (@sqsubseteq positive _).
Proof. intros ??. apply _. Qed.

(** Lattice for nat *)
Program Canonical Structure nat_Lat :=
  Make_Lat (nat) (=) (≤)%nat max min
           _ _ _ _ _ _ _
           Nat.le_max_l Nat.le_max_r Nat.max_lub Nat.le_min_l Nat.le_min_r _.
Next Obligation. intros. by apply Nat.min_glb. Qed.
Global Instance nat_leibnizequiv : LeibnizEquiv nat := λ _ _ H, H.

Global Instance nat_Total : Total (@sqsubseteq nat _).
Proof. intros ??. by apply Nat.le_ge_cases. Qed.
Global Instance nat_sqsubseteq_decision : RelDecision (@sqsubseteq nat _).
Proof. intros ??. apply _. Qed.

(** Lattice for Z *)
Program Canonical Structure Z_Lat :=
  Make_Lat (Z) (=) (≤)%Z Z.max Z.min
           _ _ _ _ _ _ _
           Z.le_max_l Z.le_max_r Z.max_lub Z.le_min_l Z.le_min_r _.
Next Obligation. intros. by apply Z.min_glb. Qed.
Global Instance Z_leibnizequiv : LeibnizEquiv Z := λ _ _ H, H.

Global Instance Z_Total : Total (@sqsubseteq Z _).
Proof. intros ??. by apply Z.le_ge_cases. Qed.
Global Instance Z_sqsubseteq_decision : RelDecision (@sqsubseteq Z _).
Proof. intros ??. apply _. Qed.

(** Lattice for gset  *)
Section gset.
Context (A: Type) `{Countable A}.
(* Lattice of sets with subseteq *)
Program Canonical Structure gset_Lat  :=
  Make_Lat (gset A) (≡) subseteq union intersection
           _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. move => ???. by apply union_subseteq_l. Qed.
Next Obligation. move => ???. by apply union_subseteq_r. Qed.
Next Obligation. move => ???. by apply union_least. Qed.
Next Obligation. move => ???. by apply intersection_subseteq_l. Qed.
Next Obligation. move => ???. by apply intersection_subseteq_r. Qed.
Next Obligation. move => ??????. by apply intersection_greatest. Qed.

Global Instance gset_Lat_bot : LatBottom (∅ : gset_Lat).
Proof. done. Qed.

Global Instance gset_sqsubseteq_dec : RelDecision (A:=gset A) (⊑) := _.
End gset.

(* We restrict these to semilattices to avoid divergence. *)
Global Instance flip_total {A : latticeT} :
  @Total A (⊑) → @Total A (flip (⊑)).
Proof. move=>Ht x y. destruct (Ht y x); auto. Qed.
Global Instance flip_sqsubseteq_antisymm {A : latticeT} :
  @AntiSymm A (≡) (⊑) → @AntiSymm A (≡) (flip (⊑)).
Proof. move=>?????. by apply (anti_symm (⊑)). Qed.
Global Instance flip_sqsubseteq_antisymm_L {A : latticeT} :
  @AntiSymm A (=) (⊑) → @AntiSymm A (=) (flip (⊑)).
Proof. move=>?????. by apply (anti_symm (⊑)). Qed.
Global Instance flip_partialorder {A : latticeT} :
  @PartialOrder A (⊑) → @PartialOrder A (flip (⊑)).
Proof. move=>?. constructor; apply _. Qed.

Infix "∋" := (flip elem_of) (at level 70) : stdpp_scope.
Notation "(∋)" := (flip elem_of) (only parsing) : stdpp_scope.
Notation "( X ∋)" := ((flip elem_of) X) (only parsing) : stdpp_scope.
Notation "(∋ x )" := (λ X, X ∋ x) (only parsing) : stdpp_scope.
Notation "X ∌ x" := (¬X ∋ x) (at level 80) : stdpp_scope.
Notation "(∌)" := (λ X x, X ∌ x) (only parsing) : stdpp_scope.
Notation "( X ∌)" := (λ x, X ∌ x) (only parsing) : stdpp_scope.
Notation "(∌ x )" := (λ X, X ∌ x) (only parsing) : stdpp_scope.

(* Promise-time Lattices *)
(* TODO : Generalize to denseorders if required *)
Require Import sflib.
Require Import Time.
Section time.
  Program Canonical Structure Time_Lat :=
    Make_Lat (Time.t) (=) Time.le Time.join Time.meet
    _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation. intros ????; apply DenseOrderFacts.antisym; ss. Qed.
  Next Obligation. intros ??; apply DenseOrder.join_l. Qed.
  Next Obligation. intros ??; apply DenseOrder.join_r. Qed.
  Next Obligation. intros ??; apply DenseOrder.join_spec. Qed.
  Next Obligation. intros ??; apply DenseOrder.meet_l. Qed.
  Next Obligation. intros ??; apply DenseOrder.meet_r. Qed.
  Next Obligation. intros ???; apply DenseOrder.meet_spec. Qed.

  Global Instance Time_Lat_bot : LatBottom (Time.bot).
  Proof. intros c; eapply DenseOrder.bot_spec. Qed.
End time.

(* Promise-view Lattices *)
(* Meet operation for views are not defined - we define it here since gpfsl requires it *)
Require Import View.
Section view.
  Local Definition TimeMap_meet (M1 M2 : TimeMap.t) : TimeMap.t :=
    λ l, Time.meet (M1 l) (M2 l).
  Lemma TimeMap_meet_l (M1 M2 : TimeMap.t) : TimeMap.le (TimeMap_meet M1 M2) M1.
  Proof. by intros l; rewrite /TimeMap_meet; apply (Time.meet_l (M1 l) (M2 l)). Qed.
  Lemma TimeMap_meet_r (M1 M2 : TimeMap.t) : TimeMap.le (TimeMap_meet M1 M2) M2.
  Proof. by intros l; rewrite /TimeMap_meet; apply (Time.meet_r). Qed.
  Lemma TimeMap_meet_spec (M1 M2 M : TimeMap.t)
      (LE1 : TimeMap.le M M1) (LE2 : TimeMap.le M M2) :
    TimeMap.le M (TimeMap_meet M1 M2).
  Proof. intros l; apply Time.meet_spec; eauto. Qed.

  Local Definition AllocView_meet (M1 M2 : AllocView.t) : AllocView.t :=
    λ l, andb (M1 l) (M2 l).
  Lemma AllocView_meet_l (M1 M2 : AllocView.t) : AllocView.le (AllocView_meet M1 M2) M1.
  Proof. intros l; rewrite /AllocView_meet; intros; destruct (M1 l); destruct (M2 l); eauto. Qed.
  Lemma AllocView_meet_r (M1 M2 : AllocView.t) : AllocView.le (AllocView_meet M1 M2) M2.
  Proof. intros l; rewrite /AllocView_meet; intros; destruct (M1 l); destruct (M2 l); eauto. Qed.
  Lemma AllocView_meet_spec (M1 M2 M : AllocView.t)
      (LE1 : AllocView.le M M1) (LE2 : AllocView.le M M2) :
    AllocView.le M (AllocView_meet M1 M2).
  Proof. intros l; rewrite /AllocView_meet. move /[dup]; intros ?%LE1 ?%LE2; clarify. Qed.

  Local Definition View_meet (V1 V2 : View.t) : View.t := {|
    View.rlx := TimeMap_meet V1.(View.rlx) V2.(View.rlx);
    View.alloc_view := AllocView_meet V1.(View.alloc_view) V2.(View.alloc_view);
  |}.
  Lemma View_meet_l (M1 M2 : View.t) : View.le (View_meet M1 M2) M1.
  Proof. econs; ss; eauto using TimeMap_meet_l, AllocView_meet_l. Qed.
  Lemma View_meet_r (M1 M2 : View.t) : View.le (View_meet M1 M2) M2.
  Proof. econs; ss; eauto using TimeMap_meet_r, AllocView_meet_r. Qed.
  Lemma View_meet_spec (M1 M2 M : View.t)
      (LE1 : View.le M M1) (LE2 : View.le M M2) :
    View.le M (View_meet M1 M2).
  Proof. inv LE1; inv LE2; econs; ss; eauto using TimeMap_meet_spec, AllocView_meet_spec. Qed.

  Program Canonical Structure View_Lat :=
    Make_Lat (View.t) (=) View.le View.join View_meet
    _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation. econs; exact View.bot. Qed.
  Next Obligation. intros ????; apply View.antisym; ss. Qed.
  Next Obligation. intros ??; apply View.join_l. Qed.
  Next Obligation. intros ??; apply View.join_r. Qed.
  Next Obligation. intros ??; apply View.join_spec. Qed.
  Next Obligation. intros ??; apply View_meet_l. Qed.
  Next Obligation. intros ??; apply View_meet_r. Qed.
  Next Obligation. intros ???; apply View_meet_spec. Qed.

  Global Instance View_Lat_bot : LatBottom (View.bot).
  Proof. intros c; eapply View.bot_spec. Qed.
End view.