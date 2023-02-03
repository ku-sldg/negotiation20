(*******
  DIFFERENT OPTIONS FOR MAPS 

  Code taken and manipulated from Software Foundations volume 1
  https://softwarefoundations.cis.upenn.edu/lf-current/toc.html

  and Petz https://github.com/ku-sldg/copland-avm/blob/master/src/Maps.v
  
  By: Anna Fritz 
  2.1.23
*)
Require Import Lists.List.
Import ListNotations.
Require Import Coq.Arith.EqNat.

(*********************************
       LIST BASED NAT MAPS 
**********************************)
Module NatListBasedMaps.

  (* First need some equality function *)
  Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
          | O => true
          | S m' => false
          end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.

  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

  (* a type for identifiers *)
  Inductive id : Type :=
    | Id (n : nat).

  (* The ids are equal if the natural number are equal *)  
  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.
    
  (* Actual lMap structure. It has two constructors. 
       *Empty* for the empty partial lMap and 
       *record* to update the lMap with some id and value *)
  Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

  Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

  Fixpoint find (x : id) (d : partial_map) : option nat :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

End NatListBasedMaps.

(*********************************
       LIST BASED MAPS 
**********************************)
Module ListBasedMaps.

  Class EqClass (A : Type) :=
    { eqb : A -> A -> bool ;
      eqb_leibniz : forall x y, eqb x y = true -> x = y }.

  Definition lMap (A:Type) (B:Type) `{H : EqClass A} := list (A * B).

  Definition lEmpty{A B:Type} `{H : EqClass A} : lMap A B := [].

  Fixpoint lGet{A B:Type} `{H : EqClass A} (m : lMap A B ) x : option B :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb x k then Some v else lGet m' x
  end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition lSet{A B:Type} `{H : EqClass A} (m:lMap A B) (x:A) (v:B) : lMap A B := (x, v) :: m.

Fixpoint lVals{A B:Type} `{H : EqClass A} (m : lMap A B ) : list B :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: lVals m'
  end.

End ListBasedMaps. 

(*********************************
       FUNCTIONAL MAPS
**********************************)

(* Maps again but this time constructed functionally. 
   Code motivated by Pierce: https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)
Module FunctionalMaps. 

  Class EqClass (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.

  Definition fMap (A B : Type)`{H:EqClass A} := A -> option B.

  Definition fEmpty {A B : Type}`{H:EqClass A} : fMap A B :=
  (fun _ => None).

  Definition fUpdate {A B : Type}`{H:EqClass A} (m : fMap A B)
                      (x : A) (v : B) :=
  fun x' => if eqb x x' then Some v else m x'.

End FunctionalMaps. 

(**********************************
  EXAMPLE OF ACTUALLY USING MAPS 
  *********************************)


(**********************************
         LIST BASED EXAMPLE
  *********************************)

Module ListBasedMapsEx. 

  Import Maps.ListBasedMaps.

  (* here is some type mynums *)
  Inductive mynums := 
  | one : mynums 
  | two : mynums 
  | three : mynums.

  (* here is decidability of that type *)
  Theorem mynums_dec : forall x y : mynums, {x =y} + {x<>y}.
    repeat decide equality.
  Defined.

  (* type of primary colors *)
  Inductive primary := 
  | red : primary 
  | yellow : primary 
  | blue : primary.

  (* now, make a lMap of it... where one maps to red. two maps to yellow. three maps to blue.  *)
  Print lMap. 
  Print EqClass. 

  Print nat. 

  #[global]
  Instance nat_EqClass : EqClass nat :=
    { eqb:= PeanoNat.Nat.eqb;
      eqb_leibniz := beq_nat_true }.

  Definition map1 : lMap nat mynums := lEmpty.

  Print map1. 

  Print lSet. 

  Definition map2 := lSet map1 1 one.

  Definition map3 : lMap nat mynums := [(1, one) ; (2 , two); (3 , three) ].
  (* Here is the issue.... the fact that we can define this feels wrong. What if you wanted 1 to lMap to three and someone else had already said 1 maps to one. *)
  Definition map3' : lMap nat mynums := [(1, one) ; (2 , two); (1 , three) ].
  
End ListBasedMapsEx.

(*********************************
       FUNCTIONAL MAPS EXAMPLE
**********************************)
Module FunctionalMapsEx. 

  Import FunctionalMaps. 

  #[global]
  Instance nat_EqClass : EqClass nat :=
  { eqb:= PeanoNat.Nat.eqb;
    eqb_leibniz := beq_nat_true }.

  (* here is some type mynums *)
  Inductive mynums := 
  | one : mynums 
  | two : mynums 
  | three : mynums.

  Print fMap. 

  Definition map1 : fMap nat mynums := fEmpty.
  Definition map2 := fUpdate map1 1 one.

  Notation "x '!->' v ';' m" := (fUpdate m x v)
                              (at level 100, v at next level, right associativity).

  Definition map3 : fMap nat mynums := ( 1 !-> one ; 2 !-> two ; 3 !-> three;  fEmpty). 

  (* AGAIN... same problem Here is the issue.... the fact that we can define this feels wrong. What if you wanted 1 to map to three and someone else had already said 1 maps to one. *)
  Definition map3' : fMap nat mynums := ( 1 !-> one ; 2 !-> two ; 1 !-> three;  fEmpty). 

  Definition map3'' : fMap nat mynums := (1 !-> three; map3).
  
End FunctionalMapsEx.