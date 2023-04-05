(* EXAMPLE SYSTEM 

   an example system that has a virus checker that can be measured by the "attest" asp. 
   
   By Anna Fritz (9.12.22)*)

Require Import Lists.List.
Import ListNotations.

Require Import Cop.Copland.
Import Copland.Term.
Import Copland.Evidence.

Require Import Manifest. 
Import Manifest.Manifest.
Import Manifest.ManifestProperties. 

Require Import Utils.Utilities.
Require Import String.

  (** Proof tactic for proving [executable] given the above definition
   *)
   Ltac print_goal := match goal with |- ?A => idtac A end.

   Ltac prove_exec :=
     simpl; auto; match goal with
                  | |- hasASPe _ _ _ => cbv; left; reflexivity
                  | |- knowsOfe _ _ _ => unfold knowsOfe; simpl; left; reflexivity
                  | |- _ /\ _ => split; prove_exec
                  | |- ?A => idtac A
                  end.
 
   
 
   Ltac prove_execs :=
     simpl; auto; match goal with
                  | |- hasASPe _ _ _ => cbv; left; reflexivity
                  | |- hasASPs _ _ _ => cbv; left; reflexivity
                  | |- knowsOfe _ _ _ => unfold knowsOfe; simpl; left; reflexivity
                  | |- knowsOfs _ _ _ => unfold knowsOfs,knowsOfe; simpl; left; reflexivity
                  | |- _ /\ _ => split; prove_execs
                  | |- _ \/ _ => try (left; prove_execs); try (right; prove_execs)
                  | |- ?A => idtac A
                  end.

(* Motivated by the Flexible Mechanisms for Remote Attestation, 
    we have three present parties in this attestation scheme. 
    These are used for example purposes. *)
Notation Rely := "Rely"%string.
Notation Target := "Target"%string.
Notation Appraise := "Appraise"%string.
Notation sys := "System"%string. 

(* Measurement operations (ASPs of the form ASPID p t)
   * p is place where target t is located *)
Notation request := 
  (ASPC ALL EXTD (asp_paramsC "request"%string [] Rely Rely)).
Notation attest :=
  (ASPC ALL EXTD (asp_paramsC "attest"%string [] Target sys)).
Notation app := 
  (ASPC ALL EXTD (asp_paramsC "appraise"%string [] Appraise sys)).

(** relying party can request from target  *)
Inductive rely_Policy : ASP -> Plc -> Prop := 
| rp_pol : rely_Policy request Target. 

(** target party can share attest with appraiser  *)
Inductive tar_Policy : ASP -> Plc -> Prop := 
| tar_pol : tar_Policy attest Appraise
| tar_pol_sig : forall p, tar_Policy SIG p.

(** appraiser can share result with relying party   *)
Inductive app_Policy : ASP -> Plc -> Prop := 
| app_pol : app_Policy app Rely. 


(** Definition of environments for use in examples and proofs.  Note there are 3 AM's present... Relying Party, Target, and Appraiser, each have one AM. 
*)
Definition e0 := e_empty.
Definition e_Rely :=
  e_update e_empty Rely (Some {| asps := [request]; M:= [Target] ; C := [] ; Policy := rely_Policy |}).
Definition e_Targ :=
  e_update e_empty Target (Some {| asps := [attest; SIG]; M:= [Appraise] ; C := [] ; Policy := tar_Policy|}).
Definition e_App :=
  e_update e_empty Appraise (Some {| asps := [app] ; M:= [] ; C := [Target] ; Policy := app_Policy |}).

(* In our example, the system includes the relying party, the target, and the appraiser *)
Definition example_sys_1 := [e_Rely; e_Targ; e_App]. 

(* example phrases *)
Example request_attest := lseq (asp request) (att Target (lseq (asp attest) (asp SIG))).
Example request_attest_appraise := lseq (request_attest) (att Appraise (asp app)).


(* Proofs about has ASP, depends On, and knows Of*)

(* Prove the relying party has aspc1 in the relying party's environment *)
Example ex1: hasASPe Rely e_Rely request.
Proof. unfold hasASPe. simpl. left. reflexivity. Qed.
  
Example ex2: knowsOfe Rely e_Rely Target.
Proof. unfold knowsOfe. simpl. left. reflexivity. Qed. 

(* the appriser depends on target *)
Example ex3 : dependsOne Appraise e_App Target.
Proof.
  unfold dependsOne. simpl. auto.
Qed.   

(* within the system, we see that the appraiser depends on target *)
Example ex4 : dependsOns Appraise example_sys_1 Target.
Proof. 
  unfold dependsOns. simpl. unfold dependsOne. simpl. auto.
Qed.   

(* Proofs about executability *)

(* Prove attest executable on the on target. *)
Example ex5: (executable (asp attest) Target e_Targ).
Proof. prove_exec. Qed.
  
(* copy is not executable on the target in the appraiser's environment *)
Example ex6: (executable (asp CPY) Target e_App) -> False.
Proof.
  intros Hcontra.
  simpl in *.
  cbv in *.
  destruct Hcontra.
Qed.

(* two signature operations are executable on the target*)
Example ex7: (executable (lseq (asp SIG) (asp SIG)) Target e_Targ).
Proof. prove_exec; unfold hasASPe; simpl; auto. Qed.

(* executability of the request then attest *)
Example exe_1: (executables request_attest Rely example_sys_1).
    prove_exec.
    + unfold hasASPe. simpl. auto.
    + unfold knowsOfe. simpl. intros.
      unfold hasASPe. simpl. split; auto.
Qed.

(* executability of the whole phrase *)
Example exe_all : (executables request_attest_appraise Rely example_sys_1).
Proof with simpl.
  prove_exec.
  + unfold hasASPe... auto.
  + unfold knowsOfe... intros. unfold hasASPe... split; auto.
  + unfold knowsOfe... intros. unfold hasASPe... auto.
Qed.    

(* Proofs about privacy policy . *)
Check checkASPPolicy. 


(*  The target should be able to share a measurement of attest with the apprasier. 
    Here's the issue: we pass in the target and the target's environment 
                      as well as the ASP in question... but we need to 
                      specify WHO we are sharing this measurement with.... 
                      we currently aren't doing that. *)

Example privPol1 : checkASPPolicy Target e_Targ attest.
Proof.
  unfold checkASPPolicy. simpl.  
Abort. 

(** Check environment [e] and see if place [p] has some policy 
*  where the Policy allows p to run a. *)
Definition checkASPPolicy' (rp:Plc) (p:Plc) (e:Environment) (a:ASP) :Prop :=
  match (e p) with (* Look for p in the environment *)
  | None => False
  | Some m => (Policy m a rp) (* Policy from m allows rp to have measurement of a *)
  end.

(* Now proof finishes *)
Example privPol1 : checkASPPolicy' Appraise Target e_Targ attest.
Proof.
  unfold checkASPPolicy'. simpl. apply tar_pol.  
Qed.  