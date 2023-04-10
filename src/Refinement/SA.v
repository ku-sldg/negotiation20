(* The security association is instantiated during ISAKMP.
   It includes:  
        - identites 
        - keys 
        - domain of interpretation
        - situation
        
   For now, we only relize identities. *)
Require Import Cop.Copland.
Import Copland.Term.

(* TO DO: define situation *)

Record SA := {
    (* identity of the requestor *)
    requestor : Plc ;
    (* identity of the target... maybe this solves the "who answers the door"  *)
    target : Plc;
    (* situation field. TBD. *)
    situation : Type ; 
    (* lifetime of SA *)
    lifetime : nat ;
}. 