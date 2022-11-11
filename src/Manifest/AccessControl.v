(* Reasoning about Access Control. Motivated by paper titled "Model Checking Distributed Mandatory Access Control Policies" 

Motivation : We need to be able to know if an AM can request measurement from another AM (measures relation). At the requested AM, we need to know if they can access a specific resource in the context of a certain userraiser. 

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

Definition requestor := string. 

(* Label describes the type of an ASP ie the architectural level at which the AM operates   *)
Inductive ASPType  := 
| user : ASPType 
| kernel : ASPType
| TPM : ASPType.

(* Defining measurement resources. A resource is an ASP along with its type.
   This makes it easy to get only the ASP during attestation. *)
Inductive resource  :=
| resrc :  ASP ->  ASPType -> resource.

(* create some resources 
   label based on the type of data the measurement exposes 
   
   asp_vc, asp_os, asp_tpm are simple asps defined in Manifest_example2. *)
Definition r0 : resource := resrc asp_vc user. 
Definition r1 : resource := resrc asp_os kernel.
Definition r2 : resource := resrc asp_tpm TPM.

Theorem eq_resource_dec: forall (x:resource) (y:resource), {x = y} + {x <> y}.
Proof. 
  repeat decide equality.
Defined.  

(* This type describes the id of the requestor. Either the entity requesting is  
   an outsider (don't have creditials on the network), an insider (has creditials), or the system admin. 

   There could be many more types. Using these three as a proof of concept. 
   TO DO : look at SELinux security types *)
Inductive RoleType := 
| outsider : RoleType 
| insider : RoleType
| systemAdmin : RoleType.   

Compute eq_resource_dec r1 r2.
(* this returns right *)

(* [k] = WHO the requestor is 
   [t] = requested resource  *)
Inductive request := 
| req : requestor -> resource -> request. 

(* To request multiple resources, use a list.  *)
Definition ExR0 := req Rely r0.
Definition ExR1 := req Rely r1.
Definition ExR2 := [ExR0 ; ExR1].

(* The situation describes the type of each party in the attestation scenario. Here is the situation defined relationally.  *)
Inductive situation' : requestor -> RoleType -> Set := 
| sit1' : situation' Rely insider.

(* Situation defined inductivly *)
Inductive situation := 
| sit : requestor -> RoleType -> situation. 

(* Context describes the dependency between resources as outlined in "Confining the Adversary" by Rowe. Context will likely be in the Manifest. I'm not sure if we need to reason about it yet but it's here so I don't forget about it. The latter resource here depends on the former *) 
Inductive context := 
| contxt : resource -> resource -> context. 

(* resource 0 (measure vc) depends on the measurement of the OS resource 1 (measure os) *)
Example c1 := contxt r1 r0. 

(* Define privacy policy. This is dependent on the request and the system.
   
   [k] is the request 
   [e] is the enviornment for which the policy exists 
   [r] is the resource in question 
   
   This policy says: 
   1. an outsider only has access to user space measurements 
   2. an insider can request use of the TPM or user space measurement 
   3. an system admin can take user space measurement, kernel measurement, and can access TPM. *)
Definition privPolicy' (s: situation) (r : request) : Prop := 
  match s with 
  | sit _ outsider => match r with 
                      | req _ (resrc _ user) => True 
                      | _ => False
                      end
  | sit _ insider => match r with 
                      | req _ (resrc _ user) => True 
                      | req _ (resrc _ TPM) => True 
                      | _ => False
                      end 
  | sit _ systemAdmin => True 
  end. 

(* Assuming the privacy policy will be a list *)
Fixpoint privPolicy (s : situation) (r: list request) : Prop :=
  match r with 
  | [] => True 
  | h :: t => (privPolicy' s h) /\ privPolicy s t 
  end. 

Ltac inv H := inversion H; subst. 
Ltac left_true H := left; split; simpl; try apply I; try apply H. 
Ltac not_right H0 := right; unfold not; intros; inv H0; congruence.

(* For any requested list, either the privacy policy is satisfied or its not. This proof is long and painful. It needs automation.  *)
Definition privPolicyDec : forall r s, {privPolicy s r} + {~ privPolicy s r}.
Proof.
  intros r s. generalize dependent s. induction r.
  + simpl. left. apply I.
  + simpl. intros. destruct a. destruct r4. destruct a0.
  (* proofs for user *)
  ++ destruct s. destruct r5.
  +++ simpl. specialize IHr with (sit r4 outsider). inv IHr.
  ++++ left_true H.
  ++++ not_right H0.
  +++  simpl. specialize IHr with (sit r4 insider). inv IHr.
  ++++ left_true H.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r4 systemAdmin). inv IHr.
  ++++ left_true H.
  ++++ not_right H0.
  (* proofs for kernel *)
  ++ destruct s. destruct r5.
  +++ simpl. specialize IHr with (sit r4 outsider). inv IHr.
  ++++ not_right H0. 
  ++++ not_right H0.
  +++  simpl. specialize IHr with (sit r4 insider). inv IHr.
  ++++ not_right H0.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r4 systemAdmin). inv IHr.
  ++++ left_true H.
  ++++ not_right H0.
  (* proofs for TPM *)
  ++ destruct s. destruct r5.
  +++ simpl. specialize IHr with (sit r4 outsider). inv IHr.
  ++++ not_right H0. 
  ++++ not_right H0.
  +++  simpl. specialize IHr with (sit r4 insider). inv IHr.
  ++++ left_true H. 
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r4 systemAdmin). inv IHr.
  ++++ left_true H. 
  ++++ not_right H0.
Qed. 

(* INTERESTING: 
  Because everything is types, we don't need to consider the system yet. That comes with executability. *)

(* The relying party request r1 *)
Print ExR1. 

(* Reason about example requests
   r0 = asp_vc user. 
   r1 = asp_os kernel.
   r2 = asp_tpm TPM. *)

Lemma help : True /\ True = True.
auto. Qed.  

Lemma help' : (True /\ True) -> True /\ True.
auto. Qed.  

(* in this situation, the relying party is an insider *)
Definition sit1 := sit Rely insider. 

(* this says, the relying party as an "insider" requests r1 (measurement of os at kernel level) *)
Theorem  req1': ~ privPolicy sit1 [ExR1].
Proof.
  simpl. unfold not. intros. inv H. auto.
Qed. 

(* relying party as an outsider *)
Definition sit2 := sit Rely outsider. 

(* an outsider requests access to a user level object *)
Theorem  req2': privPolicy sit2 [ExR0].
Proof.
  simpl. auto.
Qed.

(* system admin can request anything *)
Lemma req_admin : forall rely u res, u = systemAdmin -> privPolicy (sit rely u) [res].
Proof.
  intros. inv H. simpl. auto. 
Qed. 

