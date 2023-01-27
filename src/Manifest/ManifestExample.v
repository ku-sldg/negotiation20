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

       (* Introducing three asps for reasoning purposes. *)
  Notation aspc1 :=
    (ASPC ALL EXTD (asp_paramsC "asp1"%string ["x"%string;"y"%string] Target Target)).
  Notation aspc2 :=
    (ASPC ALL EXTD (asp_paramsC "asp2"%string ["x"%string] Target Target)).

    (* Policy describes privacy constraints applied to measurement operations. 

  Below are relational definitions of Policy. Within the definition, we list each ASP on the AM and state who can recieve a measurement of said ASP (ie doesn't expose sensitive information in the context). The relying party can share the measurement of aspc1 with p. The target can share the measurement aspc2 with the appraiser and SIG with anyone. The appraiser can share a hash with anyone. 
*)

  Inductive rely_Policy : ASP -> Plc -> Prop := 
  | p_aspc1 : forall p, rely_Policy aspc1 p. 

  Inductive tar_Policy : ASP -> Plc -> Prop := 
  | p_aspc2 : tar_Policy aspc2 Appraise 
  | p_SIG : forall p, tar_Policy SIG p. 

  Inductive app_Policy : ASP -> Plc -> Prop := 
  | p_HSH : forall p, app_Policy HSH p. 


    (** Definition of environments for use in examples and proofs.  Note there are 3 AM's present... Relying Party, Target, and Appraiser, each have one AM. 
   *)
   Definition e0 := e_empty.
   Definition e_Rely :=
     e_update e_empty Rely (Some {| asps := [aspc1]; M:= [Target] ; C := [] ; Policy := rely_Policy |}).
   Definition e_Targ :=
     e_update e_empty Target (Some {| asps := [SIG;  aspc2]; M:= [Appraise] ; C := [] ; Policy := tar_Policy|}).
   Definition e_App :=
     e_update e_empty Appraise (Some {| asps := [HSH] ; M:= [] ; C := [Target] ; Policy := app_Policy |}).

       (* In our example, the system includes the relying party, the target, and the appraiser *)
  Definition example_sys_1 := [e_Rely; e_Targ; e_App]. 

  (* Prove the relying party has aspc1 in the relying party's enviornement *)
  Example ex1: hasASPe Rely e_Rely aspc1.
  Proof. unfold hasASPe. simpl. left. reflexivity. Qed.

  (* relying party does not have copy *)
  Example ex2: hasASPe Rely e_Rely CPY -> False.
  Proof. unfold hasASPe. simpl. intros. inverts H. inverts H0. auto. Qed.
  
  (* Prove the Relying party has aspc2 within the system *)
  Example ex5: hasASPs Rely (example_sys_1) aspc1.
  Proof. unfold hasASPs. unfold hasASPe. simpl. left. left. reflexivity. Qed. 

    Example ex7': knowsOfs Rely example_sys_1 Appraise -> False.
    Proof. simpl. 
      unfold knowsOfs,knowsOfe.  simpl. intros. inverts H. inverts H0;   auto. inverts H. inverts H0. apply H. inverts H; auto.    
    Qed. 

    (* the relying party knows of the target within system 1*)
  Example ex3: knowsOfs Rely example_sys_1 Target.
  Proof.
    unfold knowsOfs. simpl. left. unfold knowsOfe. simpl.  auto.
  Qed.
  
  (* the relying party does not directly know of the appraiser *)
  Example ex4: knowsOfe Rely e_App Appraise -> False.
  Proof.
    unfold knowsOfe. simpl. intros. destruct H. 
  Qed.

  (* the relying party is aware of the target in system 1*)
  Example ex7: knowsOfs Rely example_sys_1 Target.
  Proof.
    unfold knowsOfs,knowsOfe. simpl. auto.
  Qed. 

  (* if the relying party was it's own system, it would still be aware of the target *)
  Example ex8: knowsOfs Rely [e_Rely] Target.
  Proof.
    unfold knowsOfs,knowsOfe. simpl. auto.
  Qed.

  (* the appriser depends on target *)
  Example ex81 : dependsOne Appraise e_App Target.
  Proof.
    unfold dependsOne. simpl. auto.
  Qed.   

  (* within the system, we see that the appraiser depends on target *)
  Example ex82 : dependsOns Appraise example_sys_1 Target.
  Proof. 
    unfold dependsOns. simpl. unfold dependsOne. simpl. auto.
  Qed.   


  (* Is asp SIG executable on the on target place in the Targets's enviornement?*)
  Example ex9: (executable (asp SIG) Target e_Targ).
  Proof. prove_exec. Qed.
  
  (* copy is not executable on the target in the appraiser's environment *)
  Example ex10: (executable (asp CPY) Target e_App) -> False.
  Proof.
    intros Hcontra.
    simpl in *.
    cbv in *.
    destruct Hcontra.
  Qed.

  (* two signature operations are executable on the target*)
  Example ex11: (executable (lseq (asp SIG) (asp SIG)) Target e_Targ).
  Proof. prove_exec. Qed.

  Example ex12: (executable (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely e_App).
  Proof. prove_exec. intros. Abort. (* split. 
    cbv in *. left. reflexivity. 
    cbv in *. left. reflexivity.   Qed. *)

  (* the relying party can ask the target to run aspc1 and signature operations within system 1 *)
  Example ex12': (executables (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely example_sys_1).
  Proof. prove_exec. intros. simpl. unfold hasASPe. simpl.
    left. left. reflexivity.   
    cbv in *. split. right.  left. left.  reflexivity. 
    cbv in *. right. left.  left. reflexivity.   Qed.
