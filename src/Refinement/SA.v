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
    (* person who sends message *)
    src : Plc ;
    (* person who recieves message  *)
    dest : Plc;
    (* situation field. TBD. *)
    situation : Type ; 
    (* lifetime of SA *)
    lifetime : nat ;
}. 