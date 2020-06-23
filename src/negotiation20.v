(*************

Implementation of our work surrounding the concept of negotiation

Anna Fritz and Perry Alexander 

CURRENT THOUGHTS (6/23) 
- Is the signature correct for the target's privacy policy? 
  Should work on terms or on the proposal? I am thinking the proposal 
  because then we can have a subset type but just needed to make sure. 
- How do you actually write the privacy policy? 
  I understand what it's supposed to say but I don't understand how 
  to correctly encode it. 
- I am wondering if the policies need additional information? 
  Maybe more terms? It feels underspecified. 
- Do we need min/max policy? Might just add to make 
  it easier to begin. 
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

Definition request := term. 

(*  The proposal is sent from target to appraiser. 
    It includes the terms the target is willing 
    to share during attestation. 

    In the proposal, there will either be one 
    term, or more than one term.  *)

Inductive proposal :=
| ONE : term -> proposal
| ADD : proposal -> proposal -> proposal.
                   

Check request.  
Check proposal.
Check ADD. 
Check (KIM 3). 
Check (ONE (KIM 3)). 
Check (ADD (ONE (KIM 3)) (ONE (USM 3))). 
Check (ADD (ONE (KIM 3)) (ADD (ONE (USM 3)) (ONE (KIM 4)))).

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
                                          app_selection := _ |}.   *) 

(* Definition acceptableTerms (p:place) (pol:(privacy nat)) : Type := {t:term | (pol p t)}. *) 

Definition first_app : app_policy := {|
                                    app_privacy (p:place) (t:term)  := forall p, True;
                                    app_selection (p:place) (pro:proposal) := proj1_sig  { KIM 0 | True }
                                  |}.

Check first_app. 

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

  Definition join : t -> t -> t := order x y -> order y z -> order x (join y z). 
