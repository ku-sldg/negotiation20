(*

  Musings about data structures 

  Records
        - define type where accessor functions are created at the same time 
        - I dont think records can be recusive 

  Classes 
        - defined with parameters and methods 
        - instance is a definition of the class

  Modules 

 *)


(* Examples
   - Rectangle has a length and width 
 *)

(* Set Implicit Arguments. *)
Require Import Setoid.
Require Import Poset. 

Inductive rectangle :=
| length : nat -> rectangle
| width : nat -> rectangle 
| area : nat -> nat -> rectangle.

Check rectangle. 
Check area. 

Record rec_rectangle := {
                         rec_length : nat;
                         rec_width : nat;
     
                         (* I dont think you define function in
                            rectangle, only properties 
                          area : nat -> nat -> nat;
                          *)
                          (* Definition area : rec_length -> rec_width -> area *)      
                       }.

Definition rec_1 : rec_rectangle := {|
                                      rec_length := 1;
                                      rec_width := 2
                                      
                                   |}.


(* Class class_rectangle {
        length : nat
                   width : nat
                             area : length -> width -> nat
      }.
*)

  
  Module Type mod_rectangle.
    Parameter length : nat.
    Parameter width : nat.
    Parameter area : nat -> nat -> nat.
  End mod_rectangle.



(* Here is a record, how to put together, and reference elements *)
Record rec := mkrec {foo : nat}.
Check {t:nat | True}.
Definition term_prop : {t:nat | t = 4}.
Proof.
  econstructor. reflexivity.
Defined.
Definition daRec := mkrec (proj1_sig term_prop).
Check daRec. 
Compute (daRec.(foo)).


Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S : forall m : nat, le n m -> le n (S m).

(* the S m ordering is a relation that exists over naturals 
   It's how you move from one natural to the next *)

(* Inductive le_2 (n m : nat) : Prop :=
| le_eq : n = m -> le_2 n m
| le_neq : m > n -> le_2 n (S m). *) 


Check le_n. 
Check le_S. 

Hint Constructors le. 

Eval compute in le 2 2. 
Check le 2 2.
Check le. 
Check le 2 3. 
Eval compute in le 2 3.
Eval compute in le_S 2 2. 

Theorem le_test_1 : le 2 3.
Proof.
  auto. (* apply le_n. *)  
Qed.

Check le_test_1.
Print le_test_1.
Compute le_test_1.
Eval compute in le_test_1.

Inductive my_type :=
| A : my_type
| B : my_type
| C : my_type.


Check my_type. 
(* my_type : Set *)

(* Define a relation where A is gte B and B is gte C *)

Inductive gte : my_type -> my_type -> Prop :=
| a_b : gte A B 
| b_c : gte B C.

Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, (trc R) x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z.

Check trc gte.
Check le.

Theorem le_Sm_n : forall m z, le (S m) z -> le m z. 
Proof. 
  intros. 
  induction H.
  apply le_S. apply le_n.  
  apply le_S. apply IHle.
Qed.


Theorem le_trans_help : forall m z, le (S m) (S z) -> le m z. 
Proof.
  intros.  
  inversion H.
  apply le_n. 
  subst. apply le_Sm_n in H1. 
  apply H1.
Qed.

(* This proof works because of the way the le constructors are defined *)

Theorem le_trans : forall x y z, le x y -> le y z -> le x z. 
Proof.
  intros.
  induction H. apply H0.
  apply IHle. apply le_Sm_n in H0.  
  apply H0.
Qed. 
  
(* In order to do this proof we have to prove that the relationship is reflexive. 
   You also have to have the transitive relation defined like TrcFront. *)

Theorem trans_gte : forall x y z, gte x y -> gte y z -> gte x z.
Proof.
  intros. induction H0.  
  induction H. apply a_b. 
Abort. 
  
Theorem gte_imp_trc : forall x y, gte x y -> trc gte x y. 
Proof.
  Abort. 
  (* TRC gives you every possible relation you can define 
   TRC give you the whole relation 
   TRC gte is the partial order 
 *)

Theorem trc_trans' : forall x y z, gte x y
  -> trc gte y z
  -> trc gte x z.
Proof.
  intros. induction H. Abort.

(*
  play with proving antisymmetic 
*)

Theorem trc_trans : forall x y z, trc gte x y
  -> trc gte y z
  -> trc gte x z.
Proof.
  intros. induction H. 
  apply H0.

  eapply TrcFront. 
  eapply H.
  
  apply IHtrc. 
  apply H0. 
Qed.

Inductive empty_relation : my_type -> my_type -> Prop := .

Theorem trc_empty : forall x y z, trc empty_relation x y
                                  -> trc empty_relation y z
                                  -> trc empty_relation x z.
Proof.
  intros. induction H.
  apply H0.

  eapply TrcFront. 
  eapply H.
  
  apply IHtrc. 
  apply H0. 
Qed.

Inductive gte_2 : my_type -> my_type -> Prop :=
| a_c_2 : gte_2 A C
| a_b_2 : gte_2 A B.

Theorem trc_gte_2' : forall x y z, gte_2 x y
                                  -> trc gte_2 y z
                                  -> trc gte_2 x z.
Proof.
  intros; induction H. Abort .
  
Theorem trc_gte_2 : forall x y z, trc gte_2 x y
                                  -> trc gte_2 y z
                                  -> trc gte_2 x z.
Proof.
  intros. induction H.
  apply H0.

  eapply TrcFront. 
  eapply H.
  
  apply IHtrc. 
  apply H0. 
Qed.

Inductive eq_2 : my_type -> my_type -> Prop :=
| eq_3x : forall x, eq_2 x x.

  
Theorem trc_gte_2_asym : forall x y, trc gte_2 x y
                                  -> trc gte_2 y x
                                  -> trc eq_2 x y.
Proof.
  intros.
Abort. 



  
(* No rules to relate B and C so this proof will never work. *)
Theorem gte_C_B : gte_2 B C. 
Proof.
  intros.
  Abort. 

Inductive eq_3 : my_type -> my_type -> Prop :=
| eq_x : forall x, eq_3 x x.

Eval compute in eq_3 A A. 

(* Here I made a new data structure and tried to do the proof without trc *)

Inductive gte_3 : my_type -> my_type -> Prop :=
| refl_3 : forall x: my_type, gte_3 x x                                    
| trans_3 : forall x y z : my_type, gte_3 x y -> gte_3 y z -> gte_3 x z 
| a_b_3 : gte_3 A B
| b_c_3 : gte_3 B C.

(* Adding anti symmetic rule  
     - if we want something to be antisymmetic, then we need an understanding of equality. 
       we could make an equality data structure. However, the equality data structure is 
       the same as the reflexive tactic. 
       | antisym_3 : forall x y : my_type, gte_3 x y -> gte_3 y x -> gte_3 x y

 *)

Theorem eq_imp_gte : forall x y, eq_3 x y -> gte_3 x y.
  Proof. 
    intros.
    induction H.
    apply refl_3.
Qed. 
  
(* I'm *)
Theorem gte_antisym : forall x y, gte_3 x y -> gte_3 y x -> gte_3 x y. 
  Proof. 
    intros. 
    apply H. 
  Qed.
  
Theorem gte_antisym_eq : forall x y, gte_3 x y -> gte_3 y x -> eq_3 x y. 
Proof.
  intros.
  induction H.
  apply eq_x.
Abort.
  
Hint Constructors gte_3. 

Theorem trans_gte_3 : forall x y z, gte_3 x y -> gte_3 y z -> gte_3 x z.
Proof.
   intros. destruct x; destruct y; destruct z; try eauto. 
Qed. 


Module PosetMyType <: Poset.
  Definition t : Type := my_type.
  Definition eq : t -> t -> Prop := (fun t1 t2 => eq t1 t1).

  Hint Unfold eq. 

  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40).

  Theorem eq_refl : forall x, x == x.
  Proof. reflexivity. Qed.
