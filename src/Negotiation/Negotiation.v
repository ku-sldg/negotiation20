(***********************************
    Overview of Negotiation 
    By: Anna Fritz 
    Date: August 2nd, 2022 
************************************)

Require Import String.
Require Import myTerm. 
Require Import Manifest. 

(* 1. ISAKMP/StrongSwan SA 

    ISAKMP creates security associations (SA) which provides encryption and authenication. Once the protocol is complete, a variety of security parameters are agreed upon including hashing and signing algorithms. 

************************************)

Record SA := {
    hashAlg : string ;
    signAlg : string
    }.
    
(* 2. Request 

    The request is a Copland phrase and a security association. 

************************************)

Definition Request: Set := (Term * SA).

(* 3. Refinement 

    The target must refine the request to realize a list of protocols that satisfy the request. 

************************************)

Definition Refinement (r: Request) (m:gMan) : list Term := 
    match r gm with 
       

(* 4. Selection 

    The relying party selects the best phrase for attestation by applying some ordering to the list of protocols sent from appraiser. 

************************************)

Definition selection (r:Request) (l: list Term) : Term. Admitted. 
