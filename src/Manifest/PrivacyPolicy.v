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

Module Not_Relationally. 

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
Definition r_vc_usr: resource := resrc asp_vc user. 
Definition r_os_ker : resource := resrc asp_os kernel.
Definition r_tpm_tpm : resource := resrc asp_tpm TPM.

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

Compute eq_resource_dec r_os_ker r_tpm_tpm.
(* this returns right *)

(* [k] = WHO the requestor is 
   [t] = requested resource  *)
Inductive request := 
| req : requestor -> resource -> request. 

(* To request multiple resources, use a list.  *)
Definition Req_vc_usr := req Rely r_vc_usr.
Definition Req_os_ker := req Rely r_os_ker.
Definition Req_vc_and_os := [Req_vc_usr ; Req_os_ker].

(* The situation describes the type of each party in the attestation scenario. Here is the situation defined relationally.  *)
Inductive situation' : requestor -> RoleType -> Set := 
| sit_Rely_in' : situation' Rely insider.

(* Situation defined inductivly 

TO DO: ake more general, could have ASPs, resource, target *)
Inductive situation := 
| sit : requestor -> RoleType -> situation. 

(* First, relying party is an insider. Next is a system Admin. Then is an outsider. *)
Definition sit_Rely_in := sit Rely insider. 
Definition sit_Rely_admin := sit Rely systemAdmin.
Definition sit_Rely_out := sit Rely outsider. 

(* Context describes the dependency between resources as outlined in "Confining the Adversary" by Rowe. Context will likely be in the Manifest. I'm not sure if we need to reason about it yet but it's here so I don't forget about it. The latter resource here depends on the former *) 
Inductive context := 
| contxt : resource -> resource -> context. 

(* resource 0 (measure vc) depends on the measurement of the OS resource 1 (measure os) *)
Example c1 := contxt r_os_ker r_vc_usr. 

(* Define privacy policy. This is dependent on the resource and the system.
    
   [s] is the situation for which the policy exists 
   [r] is the resource in question 
   
   This policy says: 
   1. an outsider only has access to user space measurements 
   2. an insider can request use of the TPM or user space measurement 
   3. an system admin can take user space measurement, kernel measurement, and can access TPM. *)
Definition privPolicy' (s: situation) (r : resource) : Prop := 
  match s with 
  | sit _ outsider => match r with 
                      | (resrc _ user) => True 
                      | _ => False
                      end
  | sit _ insider => match r with 
                      | (resrc _ user) => True 
                      | (resrc _ TPM) => True 
                      | _ => False
                      end 
  | sit _ systemAdmin => True 
  end. 

(* Assuming the privacy policy will be a list *)
Fixpoint privPolicy (s : situation) (r: list resource) : Prop :=
  match r with 
  | [] => True 
  | h :: t => (privPolicy' s h) /\ privPolicy s t 
  end.

Ltac inv H := inversion H; subst. 
Ltac left_true H := left; split; simpl; try apply I; try apply H. 
Ltac not_right H0 := right; unfold not; intros; inv H0; congruence.
Ltac both H H0 := try left_true H; try not_right H0.

(* For any requested list, either the privacy policy is satisfied or its not. This proof is long and painful. It needs automation.  *)
Definition privPolicyDec : forall r s, {privPolicy s r} + {~ privPolicy s r}.
Proof.
  intros r s. generalize dependent s. induction r.
  + simpl. intros. auto.
  + simpl. intros. destruct a. destruct a0.
  (* user *)
  ++ destruct s. destruct r1.
  +++ simpl. specialize IHr with (sit r0 outsider). inv IHr.
  ++++ left_true H.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r0 insider). inv IHr; simpl.
  ++++ left_true H.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r0 systemAdmin). inv IHr; simpl.
  ++++ left_true H.
  ++++ not_right H0.
  (* kernel *)
  ++  destruct s. destruct r1.
  +++ simpl. specialize IHr with (sit r0 outsider). inv IHr.
  ++++ not_right H0.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r0 insider). inv IHr; simpl.
  ++++ not_right H0.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r0 systemAdmin). inv IHr; simpl.
  ++++ left_true H.
  ++++ not_right H0.
  (* TPM *)
  ++  destruct s. destruct r1.
  +++ simpl. specialize IHr with (sit r0 outsider). inv IHr.
  ++++ not_right H0.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r0 insider). inv IHr; simpl.
  ++++ left_true H.
  ++++ not_right H0.
  +++ simpl. specialize IHr with (sit r0 systemAdmin). inv IHr; simpl.
  ++++ left_true H.
  ++++ not_right H0.
Qed. 

(* INTERESTING: 
  Because everything is types, we don't need to consider the system yet. That comes with executability. *)

(* The relying party request r_os_ker *)
Print Req_os_ker. 

(* Reason about example requests
   r_vc_usr = asp_vc user. 
   r_os_ker = asp_os kernel.
   r_tpm_tpm = asp_tpm TPM. *)

(* this says, the relying party as an "insider" requests r_os_ker (measurement of os at kernel level) *)
Theorem  req1': ~ privPolicy sit_Rely_in [r_os_ker].
Proof.
  simpl. unfold not. intros. inv H. auto.
Qed. 


(* an outsider requests access to a user level object *)
Theorem  req2': privPolicy sit_Rely_out [r_vc_usr].
Proof.
  simpl. auto.
Qed.

(* system admin can request anything *)
Lemma req_admin : forall rely u res, u = systemAdmin -> privPolicy (sit rely u) [res].
Proof.
  intros. inv H. simpl. auto. 
Qed. 

(* Selection function without proof *)
Definition reqDep (s: situation) : {r  | (privPolicy' s r)}.
Admitted. 
Print reqDep.
Check reqDep.
(*  forall s : situation, {r : request | privPolicy' s r} *)

(* subset of all requests that are true for a situation *)
Definition reqDep' (s : situation) := {r | privPolicy' s r}.
Check reqDep'.
(* situation -> Set *)

(* Anything goes for the Admin... this isn't very interesting. *)
Compute reqDep' sit_Rely_admin.

(* more interesting. How do I prove if something is in the set. *)
Example rely_dep : reqDep' sit_Rely_in.
Proof. exists r_tpm_tpm. econstructor. Qed.   

(* prove that measurement exists in the subset *)
Lemma user_exists : exists (r:resource), 
  r = proj1_sig rely_dep.
Proof. exists r_vc_usr. simpl. unfold proj1_sig. Abort.  

End Not_Relationally. 

(*****************************************
Do this all again but define relationally. 
******************************************)

Module Relationally.  

  (* base types are ASP types *)
  Inductive ASPType  := 
  | user : ASPType 
  | kernel : ASPType
  | TPM : ASPType.

  Inductive ASPs : ASP -> ASPType -> Prop  := 
  | vc : ASPs asp_vc user
  | os : ASPs asp_os kernel
  | tpm : ASPs asp_tpm TPM.

  Inductive ASPs' := 
  | tyASP (a: ASP) ( aty : ASPType).

  Lemma ASP_dec : forall a1 a2 : ASP, {a1 = a2} + {a1 <> a2}.
  Proof.
    repeat decide equality.
  Qed.

  Check ASPs.
  
  Lemma ASPs_dec : forall a1 a2 : ASPs, 

  (* Other base types are role types *)
  Inductive RoleType := 
  | outsider : RoleType 
  | insider : RoleType
  | systemAdmin : RoleType. 



  Inductive attester : requestor -> RoleType -> Prop := 
  | req_out : attester Rely outsider
  | req_in : attester Rely insider
  | req_admin : attester Rely systemAdmin.

  Inductive situaiton := 
  | att_sit : forall (a : attester), situaiton a. 

  (* TO DO : work on this definition *)
  Inductive privPolicyRel : situation -> request -> Prop := 
  | out_usr : forall k a r s, privPolicyRel (sit s k) (req r (resrc a user)).

End Relationally. 


