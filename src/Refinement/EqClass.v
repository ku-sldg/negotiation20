(* Equality of Target ID for the maps *)

Require Import Maps.
Import Maps.FunctionalMaps.

Require Import Cop.Copland.
Import Copland.Term.

Import Coq.Strings.String. 

(* Target ID is just a string *)

Lemma eqb_leibniz_string : forall (x y :string), eqb x y = true -> x = y.
Proof.
    apply eqb_eq.
Qed. 

#[global]
Instance string_EqClass : EqClass string :=
  { eqb:= eqb;
    eqb_leibniz := eqb_leibniz_string }.

#[global]
Instance targID_EqClass : EqClass TARG_ID :=
    { eqb:= eqb;
    eqb_leibniz := eqb_leibniz_string }.

