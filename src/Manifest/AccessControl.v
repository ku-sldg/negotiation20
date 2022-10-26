(* Reasoning about Access Control. Motivated by paper titled "Model Checking Distributed Mandatory Access Control Policies" 

Motivation : We need to be able to know if an AM can request measurement from another AM (measures relation). At the requested AM, we need to know if they can access a specific resource in the context of a certain appraiser. 

Goal: create a type system to describe the resource of measurement (resources) and the ASPs preforming measurement. 

By: Anna Fritz (8.25.22) *)

Require Import String.
Require Import List.
Import List.ListNotations.

Require Import Lia.
Require Import Relations.
Require Import Logic.FunctionalExtensionality.

Require Import Cop.Copland.
Import Copland.Term.
Import Copland.Evidence.

Require Import Manifest.
Import Manifest.ManifestTerm.

Require Import Manifest_example.
Import Manifest_example.Example2.

(* Start by defining a type system like the system in MCDMACP 
   https://leepike.github.io/pubs/mcdmacp12.pdf 
   
   neeeded = domain does not currently have access to an resource. 
             domain would like to aquire access in clear state.  
   notNeeded = domain does not need access to resource 
   clearr = domain has access to resource in clear 
   encrypted = info requires key but may be decrypted locally
   sealed = domain has access to resource but it needs keys/encryption 
            facilities to view information and will require use of TPM
            to gain access *)


(* In our case, lets assume clearr means you have access to decrpytion keys while sealed means you don't have access *)
Inductive status := 
| needed : status
| notNeeded : status
| clearr : status
| sealed : status.

Theorem eq_status_dec: forall (x:status) (y:status), {x = y} + {x <> y}.
Proof. 
  repeat decide equality.
Defined.  

(* Need a label to describe the return type of an ASP *)
Inductive ASPType  := 
| user : ASPType 
| kernel : ASPType
| TPM : ASPType.

(* Defining measurement resources. *)
Inductive resource  :=
| resrc :  ASP ->  ASPType -> resource.

(* This type describes the id of the requestor *)
Inductive UserType := 
| outsider : UserType 
| insider : UserType
| systemAdmin : UserType. 
  
Theorem eq_resource_dec: forall (x:resource) (y:resource), {x = y} + {x <> y}.
Proof. 
  repeat decide equality.
Defined.  

(* create some resources 
   label based on the type of data the measurement exposes *)
Definition r0 : resource := resrc asp_vc user. 
Definition r1 : resource := resrc asp_os kernel.
Definition r2 : resource := resrc asp_tpm TPM.

Compute eq_resource_dec r1 r2.
(* this returns right *)

(* In the paper, sigma is a function describing the state of the domain. 

This is essentially the privacy function. Is a resource needed or not needed? Sigma tells us its status while the red/green notation tells us if it should be shared *)

Definition sigma (r : resource) : status := 
  match r with 
  | resrc asp_vc user => needed 
  | resrc asp_os kernel => needed
  | resrc asp_tpm TPM => sealed 
  | _ => notNeeded
  end.


(* [k] = WHO the requestor is 
   [u] = TYPE of requestor for policy 
   [t] = requested resource  *)
Inductive request := 
| req : string -> UserType -> resource -> request
| many : request -> request -> request. 

Definition getPlc (a:ASP_PARAMS) : Plc := 
  match a with 
  | asp_paramsC id arg pl t => pl 
  end.
  
Definition getTarg (a:ASP_PARAMS) : TARG_ID := 
  match a with 
  | asp_paramsC id arg pl t => t 
  end.

(* Define privacy policy. This is dependent on the request and the environment.
   
   [k] is the request 
   [e] is the enviornment for which the policy exists 
   [r] is the resource in question 
   
   This policy says: 
   1. an outsider only has access to user space measurements 
   2. an insider can request use of the TPM or user space measurement 
   3. an system admin can take user space measurement, kernel measurement, and can access TPM. *)
Fixpoint privPolicy (r : request) (e: Environment) : Prop := 
  match r with 
  | req k outsider res => match res with 
                          | resrc _ user => True 
                          | _ => False 
                          end  
  | req k insider res => match res with 
                         | resrc _ user => True 
                         | resrc _ TPM => True 
                         | resrc _ kernel => False 
                         end
  | req k systemAdmin res => True 
  | many r1 r2 => privPolicy r1 e /\ privPolicy r2 e
  end. 

(* Make some example reqeusts *)
Example req1 := req Target outsider r0.

Theorem  req1': privPolicy req1 e3 = True .
Proof.
  simpl. auto.
Qed.

(* an outsider cannot request access to a kernel level object *)
Example req2 := req Target outsider r1.

Theorem  req2': privPolicy req2 e3 -> False.
Proof.
  simpl. auto.
Qed.

(* transitive reflexive closure gives us all elements we could access *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z, R x y -> trc R y z -> trc R x z.

Notation "R ^*" := (trc R) (at level 0).

(* what if we want to use the trc to reveal all resources an outsider has access to? *)


