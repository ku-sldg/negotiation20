(*************

Implementation of our work surrounding the concept of negotiation

Anna Fritz and Perry Alexander 


Thoughts about Policy (6/23) 
- Is the signature correct for the target's privacy policy? 
  Should work on terms or on the proposal? I am thinking the proposal 
  because then we can have a subset type but just needed to make sure. 
- I am wondering if the policies need additional information? 
- What about an environment? Do we want that to 
  better specify the system? Maybe that is how the 
  situational awareness is implemented? 

***************)

(*******************

Appraiser: goal is to verify the target is trustworthy 

Target: body that is appraised to determine trustworthiness 

Negotiation: the communication between the appraiser and target to determine the best protocol for attestation 

Privacy Policy: the policy that ensure the target or appraiser does not share sensitive information 

Selection Policy: a relation that maps concrete goals to abstract implementation


 ********************)


Require Import Poset.
Require Import Lattice.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.RelationClasses.

(* A place is the location where negotiation happens 
   Right now, a place describes who is participating 
   in the negotiation. *)

Definition place := nat.

Inductive term : Type :=
| KIM : nat -> term
| USM : nat -> term
| AT : place -> term -> term
| SEQ : term -> term -> term
| PAR : term -> term -> term
| SIG : term -> term.

(* A request is sent from appraiser to target. 
   The request is a term that describes the appraiser's
   desires for attestation. *)

Definition request := Ensemble term. 
Check request. 

(*  The proposal is sent from target to appraiser. 
    It includes the terms the target is willing 
    to share during attestation. 

    In the proposal, there will either be one 
    term, or more than one term.  

    The top includes all possible terms in 
    the proposal and the bottom is no terms.*)

Definition proposal := Ensemble term.
Definition top : Ensemble term := Full_set term. 
Definition bottom : Ensemble term := Empty_set term. 

Theorem top_includes_all : forall t:term, In term (top) t. 
 Proof. 
   intros.
   apply Full_intro.
 Qed.

Theorem bottom_includes_none : forall t:term, ~(In term (Empty_set term) t). 
Proof.
  intros.
  intros not. 
  inversion not. 
Qed.


(***** EXAMPLES WITH INTERESTION AND TERMS *****)
Module Examples.
  Check top. 
  Check (KIM 3). 
  Check (Singleton term (KIM 3)).  
  Definition USM_3_KIM_3 := (Add term (Singleton term (USM 3)) (KIM 3)). 
  Check (Add term (Singleton term (KIM 3)) (USM 3) (KIM 4)).

  Definition proposal_1 := (Singleton _ (KIM 3)).
  Definition request_1 := (Singleton _ (KIM 3)). 

  Theorem test_intersection : Included _ proposal_1 request_1. 
  Proof. 
    unfold Included.   
    unfold proposal_1. 
    unfold request_1. 
    intros. 
    apply H.
  Qed.

  (* Do I want the proof to be of type True? *)
  Check test_intersection.

End Examples.


(* 7/22 Dr. A suggested it may be easier to 
        work on ordering just terms and not Ensembles*)
Module PosetTerm <: Poset.

  Definition t : Type := term.
  Definition eq: t -> t -> Prop := (fun t1 t2 => t1 = t2).  

  Hint Unfold eq.
  
  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40).

  Theorem eq_refl : forall x, x == x.
  Proof. reflexivity. Qed.
    
  Theorem eq_sym : forall x y, x == y -> y == x.
  Proof. intros x y. intros H. auto. Qed.
    
  Theorem eq_trans : forall x y z,  x == y -> y == z -> x == z.
  Proof. intros x y z. intros H1 H2. unfold eq in *. subst. reflexivity. Qed.

  (* got stuck here, had to move on. No proofs done. *)
  Inductive order' : t -> t -> Prop := . 

  Definition order := order'. 
  
  Notation " t1 '<<=' t2 " := (order t1 t2) (at level 40).
  
  Theorem order_refl : forall x y, x == y -> x <<= y.
  Proof.
    Admitted. 
    
  Theorem order_antisym: forall x y, x <<= y -> y <<= x -> x == y.
  Proof.
    Admitted. 

  Theorem order_trans : forall x y z, x <<= y -> y <<= z ->  x <<= z.
  Proof.
    Admitted. 

  
End PosetTerm. 

  

Module PosetEnsemble <: Poset.
  (* Module inherits from Poset which must prove 
     reflexivity, antisymmetry, and transitivity *)


  (* Equality for the Ensemble is defined if the two are the same set *)
  Definition t : Type := Ensemble term.
  Definition eq (t1 t2 : t) : Prop := (Same_set _ t1 t2).

  Hint Unfold eq.
  
  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40). 

  Theorem eq_refl : forall x, x == x.
     Proof. unfold eq. intros. simpl. unfold Same_set. split.
         + unfold Included.  intros. apply H.
         + unfold Included. intros. apply H.
     Qed.
     
  Theorem eq_sym : forall x y, x == y -> y == x.
      Proof. intros x y. intros H. unfold eq. unfold Same_set. split.
         + inversion H. apply H1.
         + inversion H. apply H0.
       Qed. 
           
  Theorem eq_trans : forall x y z,  x == y -> y == z -> x == z.
     Proof. intros x y z. intros H1 H2.
         unfold eq in *. unfold Same_set in *. inversion H1.  inversion H2. split.
            + unfold Included in H. unfold Included. intros.
              apply H in H5. unfold Included in H3. apply H3 in H5. apply H5.
            + unfold Included in H4. unfold Included. intros.
              apply H4 in H5. unfold Included in H0. apply H0 in H5. apply H5.
     Qed.

  (* Order implies one set of terms is greater than another set of terms. 
     So the set  with more elements is greater *)
  Definition order := Included term. 
     
  Notation " t1 '<<=' t2 " := (order t1 t2) (at level 40).
  
  Theorem order_refl : forall x y, x == y -> x <<= y.
  Proof.
    intros. unfold order. inversion H. apply H0. 
  Qed.
  
  Theorem order_antisym: forall x y, x <<= y -> y <<= x -> x == y.
  Proof.
    intros. unfold order in *. unfold eq. unfold Same_set. split.
    apply H. apply H0.
  Qed.
  
  Theorem order_trans : forall x y z, x <<= y -> y <<= z ->  x <<= z.
  Proof.
    intros. 
    unfold order in *. 
    unfold Included in *. 
    intros. apply H0.  apply H. apply H1. 
  Qed. 

End PosetEnsemble.
  
   (* A record is defined to hold both the target's policies and 
   the appraiser's policies. 

   For the appraiser, the privacy policy takes the place (the details 
   of the appraiser) and the request to make sure the request does 
   not share confidentation information. It returns a True/False 
   to say if the request is okay. The selection policy takes a place
   and the proposal and chooses the best term from the proposal. 
   This will be the term used for attestation. 

   For the target, the privacy policy makes sure each term 
   in the proposal does not share any secret information. 
   It takes the target's description (place) and the proposal and 
   returns a subset satisfying the privacy policy. The selection policy
   for the target takes the place and the request and finds terms that
   satisfy the request and the privacy policy and places those 
   terms inside the proposal. The proposal is returned to the appraiser. *)


Record app_policy := {
                       app_privacy : place -> request -> Prop;
                       app_selection : place -> proposal -> term
                    }.

Record target_policy := {
                         tar_privacy : place -> proposal -> Prop;
                         tar_selection : place -> request -> proposal
                       }.
 



(********************* WHERE CURRENT WORK ENDS ****************)

(* Definition acceptableTerms (p:place) (pol:(privacy nat)) : Type := {t:term | (pol p t)}. *) 


Module Type Policy.

  Parameter t : Type.
  Parameter privacy : t -> t -> Prop.
  Parameter selection : t -> t -> t.

  Parameter min_priv : t -> t -> Prop. 

End Policy.  




Module term_lattice <: Lattice <: Poset.

  Definition t : Set := term.
  Definition n : Type := nat. 
  Definition eq : t -> t -> Prop := (fun t1 t2 => t1 = t2).
  Definition order : n -> n -> Prop := (fun x y => x <= y).

  Check n. 
