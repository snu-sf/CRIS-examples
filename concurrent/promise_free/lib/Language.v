Require Import CRIS.

Set Implicit Arguments.

Module Language.
  Section Language.
    Variable E: Type.
    Structure t := mk {
      syntax: Type;
      state: Type;

      init: syntax -> state;
      (* Maybe Ensemble Loc instead of list Z?*)
      (* init : list Z -> syntax -> state; *)
      is_terminal: state -> Prop;
      step: forall (e:E) (s1:state) (s2:state), Prop;
      (* vis : forall (ptrs : Ensemble Loc.t)
      (s : state) , Prop; *)
    }.
  End Language.
End Language.
