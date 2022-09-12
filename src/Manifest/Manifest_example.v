(* EXAMPLE SYSTEM 

   an example system that has a virus checker that can be measured by the "attest" asp. 
   
   By Anna Fritz (9.12.22)*)

Require Import Lists.List.
Import ListNotations.

Require Import Cop.Copland.
Import Copland.Term.
Import Copland.Evidence. 
Require Import Manifest. 
Import Manifest.ManifestTerm. 

Require Import String. 


Module ExamplePhrases. 
(* craft two example phrases. One measures the virus checker and 
   the other measures the signature server *)
    Definition hashing := asp HSH.
    Definition signing := asp SIG.

    (* possible ASPs*)
    Definition asp_attest :ASP_ID := "attest"%string. 

    (* possible targets *)
    Definition vc : TARG_ID := "virus checker"%string.
    Definition ss : TARG_ID := "signature server"%string. 

    (* possible target IDs *)
    Definition target : Plc := "target"%string.

    (* possible Copland phrases *)
    Definition meas_vc := (ASPC ALL EXTD (asp_paramsC asp_attest [] target vc)).
    Definition meas_ss : Term := asp (ASPC ALL EXTD (asp_paramsC asp_attest [] target ss)).

    (* eval takes a term to evidence *)
    Definition eval_vc := eval (asp (meas_vc)) target mt.
    Compute eval_vc.  

End ExamplePhrases.

Module ExampleSystems. 
(* Creating a system that can measure the vc but cannot measure the ss*)
    Import ExamplePhrases.

    (* Pieces needed for manifest *)
    Definition asps' := [meas_vc].
    Definition objs' : list Obj := [].
    Definition meas' : list Plc := [].
    
    Definition man1 : Manifest := {| asps := asps' ; objs := objs' ; M := meas' |}.

    Definition e0 := e_empty.
    Definition e1 := e_update e0 target (Some man1).  

    Definition s1 := env (e1).

End ExampleSystems.