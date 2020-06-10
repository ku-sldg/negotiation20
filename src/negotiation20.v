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


(*******

    In the proposal, there will either be one 
    term, or more than one term. 

    We may need to touch more on ordering in the future? 
    Could just make the proposal into a list? Not sure the benefit of either. 

*******) 
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


Record policy := {
                        privacy : place -> term -> Prop; 
                        selection_target : place -> request -> proposal;
                        selection_app : place -> proposal -> term
}.

Check privacy. 

