Require Import CRIS.common.CRIS.

From CRIS.promise_free.lib Require Import Loc.

Set Implicit Arguments.

Inductive gdef :=
  | Gfun
  | Gvar (gv : Z).

Module Val.
  Inductive t : Type :=
    | Vnum (const : Z) : t
    | Vptr (loc : Loc.t) : t
    | Vundef : t.

  Definition of_Z (n: Z): t := Vnum n.

  Definition Vnullptr := Vnum 0.
  Definition zero := Vnum 0.
  Definition one := Vnum 1.

  Definition is_zero (a: t): option bool:=
    match a with
    | Vnum a => Some (Z.eqb a 0)
    | Vptr _ => Some false
    | _ => None
    end.

  Definition add (x y : t) : t :=
    match x, y with
    | Vnum n, Vnum m => Vnum (Z.add n m)
    | Vptr (Loc.mk tid bid ofs), Vnum n =>
      Vptr (Loc.mk tid bid (Z.add ofs n))
    | Vnum n, Vptr (Loc.mk tid bid ofs) =>
      Vptr (Loc.mk tid bid (Z.add ofs n))
    | _, _ => Vundef 
    end.

  Definition sub (x y : t) : t :=
    match x, y with
    | Vnum n, Vnum m => Vnum (Z.sub n m)
    | Vptr (Loc.mk tid bid ofs), Vnum n =>
      Vptr (Loc.mk tid bid (Z.sub ofs n))
    | Vnum n, Vptr (Loc.mk tid bid ofs) =>
      Vptr (Loc.mk tid bid (Z.sub ofs n))
    | _, _ => Vundef
    end.

  Definition mul (x y : t) : t :=
    match x, y with
    | Vnum n, Vnum m => Vnum (Z.mul n m)
    | _, _ => Vundef
    end.

  Definition le (x y : t) : bool :=
    match x, y with
    | Vnum x, Vnum y => (x =? y)%Z
    | Vptr x, Vptr y => Loc.eqb x y
    | Vnum x, Vptr y => false
    | _, Vundef => true
    | _, _ => false
    end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss.
    - rewrite Z.eqb_refl. ss.
    - rewrite Loc.eqb_refl. ss.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss; inv H; inv H0.
    - rewrite Z.eqb_eq in H1, H2. subst.
      ss.
    - hexploit (Loc.eqb_eq _ _ H1). hexploit (Loc.eqb_eq _ _ H2). i. subst.
      rewrite Loc.eqb_refl. ss.
  Qed.

End Val.

Coercion Val.of_Z: Z >-> Val.t.
