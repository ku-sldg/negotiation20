(*

This file contain various examples of data structures, and ordering relations. 
It is a bit messy but help me (Anna) understand some of what is going on in Coq. 
*)





(*

  Musings about data structures 

  Records
        - define type where accessor functions are created at the same time 
        - I dont think records can be recusive 

  Classes 
        - defined with parameters and methods 
        - instance is a definition of the class

  Modules 
        - Modules need parametes which then you implement when instantiating 
          a module 

 *)


(* Examples
   - Rectangle has a length and width 
 *)

(* Set Implicit Arguments. *)

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


(***

Here we looked at how to define orderings using Inductive Structures. 
We worked with the Coq le definition and then moved on to creating our 
own relation. 

****)

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

