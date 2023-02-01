(*******
  DIFFERENT OPTIONS FOR MAPS 

  Code taken and manipulated from Software Foundations volume 1
  https://softwarefoundations.cis.upenn.edu/lf-current/toc.html
  
  By: Anna Fritz 
  2.1.23
*)

(* List Based Maps which operate over natural numbers. *)
Module NatListBasedMaps.

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

  Inductive id : Type :=
    | Id (n : nat).

  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => n1 =? n2
    end.
    
  (* Actual map structure. It has two constructors. 
       *Empty* for the empty partial map and 
       *record* to update the map with some id and value *)
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

(* These maps have *)
Module ListBasedMaps.

  Class EqClass (A : Type) :=
    { eqb : A -> A -> bool ;
      eqb_leibniz : forall x y, eqb x y = true -> x = y }.

    Definition eqbPair{A B:Type}`{H:EqClass A}`{H':EqClass B} (p1:A*B) (p2:A*B) : bool :=
      match (p1,p2) with
      | ((a1,b1), (a2,b2)) => andb (eqb a1 a2) (eqb b1 b2)
      end.

  Inductive partial_map {A B:Type}`{H:EqClass A} : Type :=
  | empty
  | record (i : A) (v : B) (m : partial_map).

  Definition update {A B:Type}`{H:EqClass A} (d : partial_map)
                  (x : A) (value : B)
                  : partial_map :=
  record x value d.

  Fixpoint find {A B:Type}`{H:EqClass A} (x : A) (d : partial_map) : option B :=
  match d with
  | empty => None
  | record y v d' => if eqb x y
                    then Some v
                    else find x d'
  end.

End ListBasedMaps. 


Module FunctionalMaps. 

  Class EqClass (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true -> x = y }.

  Definition total_map (A B : Type) := A -> B.

  Definition t_empty {A B : Type}`{H:EqClass A} (v : B) : total_map A B :=
  (fun _ => v).

  Definition t_update {A B : Type}`{H:EqClass A} (m : total_map A B)
                      (x : A) (v : B) :=
  fun x' => if eqb x x' then v else m x'.

End FunctionalMaps. 