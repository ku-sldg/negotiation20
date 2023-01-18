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

Print Manifest.
(* Manifest is a list of ASPs, objects, and places that the AM can measure *)

Print Environment.
(* An Enviornement maps the place to a manifest. In other words, place where the AM is located. *)

Print System.
(* A System is a collection of environements. *)

Print e0.
(* empty enviornment *) 

Print e1.
(* The relying party has aspc1, no objects, and can measure the target. *)
Print aspc1. 
(* (ASPC ALL EXTD (asp_paramsC "asp1"%string ["x"%string;"y"%string] Target Target)).*)

Print e2. 
(* Target place has the ASP SIG and aspc2. Target can measure the appraiser. *)

Print e3.
(* The appraiser can HSH but cannot measure anyone.*) 

Module Example1. 

    Notation Rely := "Rely"%string.
    Notation Target := "Target"%string.
    Notation Appraise := "Appraise"%string.

    Notation vc := "virusChecker"%string. 
    Notation sf := "signatureFile"%string. 
    Notation ss := "signatureServer"%string. 

    Notation aspc0' :=
        (ASPC ALL EXTD (asp_paramsC "asp0"%string [] Target vc)).
    Notation aspc1' :=
        (ASPC ALL EXTD (asp_paramsC "asp1"%string ["x"%string;"y"%string] Target ss)).
    Notation aspc2' :=
        (ASPC ALL EXTD (asp_paramsC "asp2"%string ["vc"%string] Target sf)).

    Definition e0' := e_empty.
    Definition e1' :=
        e_update e0' Rely (Some {| asps := [aspc1] ; M:= [Target] |}).
    Definition e2' :=
        e_update e1' Target (Some {| asps := [SIG;  aspc2] ; M:= [Appraise] |}).
    Definition e3' :=
        e_update e2' Appraise (Some {| asps := [HSH] ; M:= [] |}).

End Example1. 

Print asp_paramsC. 
(* asp_paramsC : ASP_ID -> list Arg -> Plc -> TARG_ID -> ASP_PARAMS. *)

Module Example2. 

Notation Rely := "Rely"%string.
Notation Target := "Target"%string.
Notation Appraise := "Appraise"%string.

Notation vc := "virusChecker"%string. 
Notation os := "OS"%string. 
Notation tpm := "TrustedPlatformModule"%string. 

Notation asp_vc :=
    (ASPC ALL EXTD (asp_paramsC "measure"%string [] Target vc)).
Notation asp_os :=
    (ASPC ALL EXTD (asp_paramsC "measure"%string [] Target os)).
Notation asp_tpm :=
    (ASPC ALL EXTD (asp_paramsC "get_keys"%string [] Target tpm)).

Print aspc1. 

Definition e0' := e_empty.
(* the relying party has no ASPs *)
Definition e1' :=
    e_update e0' Rely (Some {| asps := [] ; M:= [Target] |}).
(* the target can measure vc, os, and tpm *)
Definition e2' :=
    e_update e1' Target (Some {| asps := [SIG; asp_vc ; asp_os ; asp_tpm] ; M:= [Appraise] |}).
(* the appraiser can take a hash *)
Definition e3' :=
    e_update e2' Appraise (Some {| asps := [HSH] ; M:= [] |}).

End Example2. 
