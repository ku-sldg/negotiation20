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


Module PosetTerm <: Poset.
  (* Module inherits from Poset which must prove 
     reflexivity, antisymmetry, and transitivity *)
  
  Definition t : Type := Ensemble term.
  Definition eq : t -> t -> Prop := (fun t1 t2 => t1 = t2).

  Hint Unfold eq.
  
  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40). 

  Theorem eq_refl : forall x, x == x.
  Proof. reflexivity. Qed.
    
  Theorem eq_sym : forall x y, x == y -> y == x.
  Proof. intros x y. intros H. auto. Qed.
    
  Theorem eq_trans : forall x y z,  x == y -> y == z -> x == z.
  Proof. intros x y z. intros H1 H2. unfold eq in *. subst. reflexivity. Qed.
  
  Check Ensemble term.
  Check top. 
 
  (* We need to define the terms in the poset  *)
  
  Definition KIME (x:nat) : Ensemble term := (Singleton _ (KIM x)).
  Definition USME (x:nat) : Ensemble term := (Singleton _ (USM x)).
  Definition KIM_and_USM (x:nat) := (Add term (Singleton term (USM x)) (KIM x)).

  Check Ensemble term.

  (* Rules 
     1. the top is always the greatest 
     2. the empty set is always the least 
     3. a USM of any number is less than a KIM of any number 
     4. a KIM of any number is less than a KIM and USM of any number *)
  
  Inductive leq : t -> t -> Prop :=
  | leq_y_top : forall (y:Ensemble term), leq y top 
  | leq_empty_y : forall (y:Ensemble term), leq bottom y
  | leq_USME_KIME : forall (x:nat), leq (USME x) (KIME x)
  | leq_KIME_KIMandUSM : forall (x:nat), leq (KIME x) (KIM_and_USM x).

  Inductive leq' (t1:t) : t -> Prop :=
  | base_case : leq' t1 t1
  | inductive_case : forall t2:t, leq' t1 t2.
  

  Definition order := leq'. 

  Notation " t1 '<<=' t2 " := (order t1 t2) (at level 40).

  Hint Unfold order.

  (* If I inductively define terms in the leq relation, do I also need 
     constructors for reflexivity, transitivity, and anti sym*)

  (* I dont really have an ordering bc I haven't defined all cases. 
     Do I need a fall through? How do I prove term = term without that
     as a constructor? It's impossible to generalize it to a forall 
     with the way I defined things *)
  
  Theorem order_refl : forall x y, x == y -> x <<= y.
  Proof.
    intros x y. intros H. unfold eq in *.
    unfold order in *. apply inductive_case.
  Qed.
  
        
  Theorem order_antisym: forall x y, x <<= y -> y <<= x -> x == y.
  Proof.
    intros x y. intros H1 H2.
    Admitted. 

  Theorem order_trans : forall x y z, x <<= y -> y <<= z ->  x <<= z.
  Proof.
    intros x y z. intros H1 H2.
    Admitted. 


(* We could use the TRC to get to any set of terms from a Proposal *) 
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | TrcRefl : forall x, (trc R) x x
  | TrcFront : forall x y z,
      R x y
      -> trc R y z
      -> trc R x z.


  Theorem trc_trans : forall x y z, trc leq x y
                                    -> trc leq y z
                                    -> trc leq x z.
  Proof.
      intros. induction H. 
      apply H0.

      eapply TrcFront. 
      eapply H.
  
      apply IHtrc. 
      apply H0. 
  Qed.

End PosetTerm.
  
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

(* We want to use a record to keep track of what policy needs to be enforced for each 
   system. The simplist and most direct way is with a record. 

   To access and create a member of a record, we have to use special syntax. 

   To create we may say 
             Definition appraiser_1 := {| app_privacy := _ ;  
                                          app_selection := _ |}.  


Definition first_app : app_policy := {|
                                    app_privacy (p:place) (r:request)  := forall p r, True;
                                    app_selection (p:place) (pro:proposal) (r:request) := forall pro r, In 
                                  |}.

Check first_app. *) 





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
