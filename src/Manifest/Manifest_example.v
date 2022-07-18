(***************************
   EXAMPLE 

   Assumer ther are two places (attestation managers). Place 1 (P1) and place 2 (P2).  They each have an ASP "attest" which takes a measurement of the system. 

   Say that P0, the relying party, requests an attestation of P1.
   
   Request = "o1" 
****************************)
 
(* the relying party formulates the request. The request is for an attestation to measure target o1. *)
Definition request := TARG_ID.
Definition r1 : request := o1. 

(* this is the ini file for the attester. Assume the attester has two places: place 1 and place 2. Each take the "attest" measurement of the system. *)
Definition loc_man1 := mkLOCAL 1 [ASPC (asp_paramsC attest_id [] 1 o1)].
Definition loc_man2 := mkLOCAL 2 [ASPC (asp_paramsC attest_id [] 2 o2)].

Definition glob_man := mkGLOBAL [loc_man1 ; loc_man2].
Print glob_man.

(* Now, we have defined global and local manifest. We can look at what happens once request is sent. *)

(* request is sent to attester. Target needs to call "generate" function where a manifest is input and outputs some protocols. Then target needs to call thier selection function. Finally, will need to call a privacy funtion.  *)

Definition gen : list Term := generate (glob_man).
Definition sel : list Term := select_t r1 gen []. 
Compute gen. 
Compute sel.