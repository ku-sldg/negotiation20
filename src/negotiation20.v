(*************

Implementation of our work surrounding the concept of negotiation

Anna Fritz and Perry Alexander 

***************)

(*******************

Appraiser: goal is to verify the target is not compromised and can perform attestation to be deemed trustworthy 

Target: body that is appraised to determine trustworthiness 

Negotiation: the communication between the appraiser and target to determine the best protocol for attestation 

Privacy Policy: the policy that ensure the target or appraiser does not share sensitive information 

Selection Policy: a relation that maps concrete goals to abstract implementation


 ********************)

(*** 

could outline the proof in section? With hypothesis? 

dont we need the TRC? Saying that if we can get to one object we can get to others? 
To help with the lattice ordering? 

do we need some inductuve structure to describe the evidence? 

 ***)

Definition place := nat.

Inductive term : Type :=
| KIM : nat -> term
| USM : nat -> term
| AT : place -> term -> term
| SEQ : term -> term -> term
| PAR : term -> term -> term
| SIG : term -> term.

Definition request := term. 

Definition proposal :Set := term.

Definition privacypolicy (ev : Type) := place -> term -> Prop. 

Check privacypolicy. 

