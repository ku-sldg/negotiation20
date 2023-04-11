(* EXAMPLE SYSTEM 

   an example system motivated by the certificate style flexible mechanisms.
   
   example protocol is: @P1[(attest P1 sys) -> @P2[(appraise P2 sys) -> SIG
   
   By Anna Fritz (9.12.22)*)

Require Import Lists.List.
Import ListNotations.

Require Import Cop.Copland.
Import Copland.Term.
Import Copland.Evidence.

Require Import Manifest. 
Import Manifest.Manifest.
Import Manifest.ManifestProperties. 

Require Import SA. 

Require Import Utils.Utilities.
Require Import String.

(** Proof tactic for proving [executable] given the above definition *)
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

Module peer_to_peer. 

  (* Start with just P0 & P1... *)
  Notation P0 := "P0"%string.
  Notation P1 := "P1"%string.
  Notation sys := "System"%string.

  Notation situation1 := Type. 

  (* Peers begin with ISAKMP to create security association *)
  Definition SA1 : SA := {| src := P0 ; 
                            dest := P1 ; 
                            situation := situation1 ; 
                            lifetime := 12 |}.

  (* Measurement operations (ASPs of the form ASPID p t)
    * p is place where P1 t is located *)
  Notation attest :=
    (ASPC ALL EXTD (asp_paramsC "attest"%string [] P1 sys)).

  (** relying party can request from P1  *)
  Inductive P0_Policy : ASP -> Plc -> Prop := . 

  (** P1 party can share attest with appraiser  *)
  Inductive P1_Policy : ASP -> Plc -> Prop := 
  | P1pol1 : P1_Policy attest P0. 

  (** Definition of environments for use in examples and proofs.  
      Note there are 3 AM's present... Relying Party, P1, and Appraiser, each have one Manifest. 
      The P1 and appriser exist within the same environment.  *)
  Definition e0 := e_empty.
  Definition e_P0 :=
    e_update e_empty P0 (Some {| asps := []; M:= [P1] ; C := [] ; Policy := P0_Policy |}).
  Definition e_P1 :=
    e_update e_empty P1 (Some {| asps := [attest]; M:= [P0] ; C := [] ; Policy := P1_Policy|}).

  (* In our example, the system includes the relying party, the P1 *)
  Definition example_sys_1 := [e_P0; e_P1]. 

  (* example phrases *)
  Example request_ := (att P1 (asp attest)).

  (* Proofs about has ASP, depends On, and knows Of*)

  (* Prove the target has the attest measurement *)
  Example ex1: hasASPe P1 e_P1 attest.
  Proof. unfold hasASPe. simpl. left. reflexivity. Qed.
    
  Example ex2: knowsOfe P0 e_P0 P1.
  Proof. unfold knowsOfe. simpl. left. reflexivity. Qed. 

  (* Proofs about executability *)

  (* Prove attest executable on the on P1. *)
  Example ex5: (executable (asp attest) P1 e_P1).
  Proof. prove_exec. Qed.
    
  (* copy is not executable on the P1 in the P2's environment *)
  Example ex6: (executable (asp CPY) P1 e_P1) -> False.
  Proof.
    intros Hcontra.
    simpl in *.
    cbv in *.
    destruct Hcontra; inversion H. 
  Qed.

  (* executability of the request then attest *)
  Example exe_1: (executables request_ P0 example_sys_1).
      prove_exec.
      + unfold hasASPe. simpl. auto.
  Qed.   

  (* Proofs about privacy policy . *)
  Check checkASPPolicy. 

  (*  The P1 should be able to share a measurement of attest with the apprasier.*)

  Example privPol1 : checkASPPolicy SA1 P1 e_P1 attest.
  Proof.
    unfold checkASPPolicy. simpl. econstructor.    
  Qed.

  Example privPol1Term : checkTermPolicy SA1 request_ P1 e_P1.
  Proof.
    simpl. apply privPol1.
  Qed.

  Example request_sound : sound  SA1 request_ P1 e_P1.
  Proof. 
    cbv. split.
    + auto.
    + econstructor.
  Qed.    

End peer_to_peer.


Module distributed. 
(* this example will align more with the flexible mech certificate example.... 
   now we have three peers (P0, P1, P2) where P1 and P2 are located in the 
   same environment  *)
 
 Notation P0 := "P0"%string.
 Notation P1 := "P1"%string.
 Notation P2 := "P2"%string.
 Notation sys := "System"%string.

 Notation situation1 := Type. 

  (* Peers begin with ISAKMP to create security association *)
  Definition SA1 : SA := {| src := P0 ; 
                            dest := P1 ; 
                            situation := situation1 ; 
                            lifetime := 12 |}.

  (* Measurement operations (ASPs of the form ASPID p t)
   * p is place where P1 t is located *)
  Notation attest :=
  (ASPC ALL EXTD (asp_paramsC "attest"%string [] P1 sys)).
  Notation appraise :=
    (ASPC ALL EXTD (asp_paramsC "app"%string [] P2 sys)).
  Notation cert :=
    (ASPC ALL EXTD (asp_paramsC "c"%string [] P2 sys)).

  (** relying party can request from P1  *)
  Inductive P0_Policy : ASP -> Plc -> Prop := . 

  (** P1 party can share attest with appraiser  *)
  Inductive P1_Policy : ASP -> Plc -> Prop := 
  | P1pol1 : P1_Policy attest P0. 

 (* assume each place has its own manifest *)

 Definition M0 := (Some {| asps := []; M:= [P1] ; C := [] ; Policy := P0_Policy |}).

 Definition e0 := e_empty.
 Definition e_P0 :=
   e_update e_empty P0 (Some {| asps := []; M:= [P1] ; C := [] ; Policy := P0_Policy |}).
 Definition e_P1 :=
   e_update e_empty P1 (Some {| asps := [attest]; M:= [P0] ; C := [] ; Policy := P1_Policy|}).

End distributed. 