(*************

File where we describe manifests using maps. Created by Anna Fritz on 7.18.22.

*)

(*  ***************
    LIST NOTATIONS 
    *****************)
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

(* Require Import Term_Defs Example_Phrases_Admits.*) 
Require Import Coq.Relations.Relation_Definitions. 
Require Import String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.Decidable.

(*********************
COPLAND GRAMMAR 
Had to redefine the Copland grammar below in order to write some examples. 
**********************)

Inductive Plc: Set := 
| relyingParty
| attester
| appraiser.

Theorem eq_plc (x y : Plc): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

Definition N_ID: Set := nat.

Definition Event_ID: Set := nat.

Inductive ASP_ID : Set := 
| request : ASP_ID
| attest_id : ASP_ID
| appraise_id : ASP_ID
| encrypt :  ASP_ID
| decrypt :  ASP_ID. 

Theorem eq_asp (x y : ASP_ID): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

Inductive TARG_ID: Set := 
| o1 : TARG_ID 
| o2 : TARG_ID.

Inductive Arg: Set := 
| a_pub_key : Arg 
| t_priv_key : Arg 
| t_pub_key : Arg. 

Theorem eq_arg (x y : Arg): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Inductive Evidence: Set :=
| mt: Evidence
| uu: (*ASP_PARAMS ->*) ASP_PARAMS ->
      (*Evidence ->*) Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP
| REQ : Plc -> ASP.

Inductive SP: Set :=
| ALL
| NONE.

Definition Split: Set := (SP * SP).

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

(* **************
DEFINING LOCAL MANIFEST
- include a list of ASPs
- measures relation 
- eventually context relation? 
**************  *)

Record lMan : Set := mkLOCAL 
{ lASP : (list ASP); 
  M : list Plc }. 

(****************
MEASURES RELATION 

what if i prove putting hte measures relation inside the lMan is the same as outside? 
*****************)

Inductive Meas : relation Plc := 
| rp_att : Meas relyingParty attester
| att_app : Meas attester appraiser.

(* could define global manifest like this... I wanted to use "pair" from the standard library but values are not the same type. 
Definition gMan := lMan -> Meas -> gMan. *)

(* map properties... taken from Pierce in Sofware Foundations
   https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)

Definition partial_map := Plc -> (option lMan).

Definition t_empty : partial_map := (fun _ => None). 

Definition t_update (m : partial_map) (x : Plc) (v: (option lMan)):=
    fun x' => if eq_plc x x' then v else m x'.

Notation "x '!->' v ';' m" := (t_update m x v)
    (at level 100, v at next level, right associativity).

Notation "x '!->' v" := (t_update t_empty x v)
    (at level 100).

(****************
GLOBAL MANIFEST 
*****************)

Definition gMan := partial_map.

(* build an example global manifest *)

Definition req_asp := REQ attester.
Definition attest_asp := ASPC (asp_paramsC attest_id [] attester o1).
Definition appraise_asp := ASPC (asp_paramsC appraise_id [] appraiser o1).

(* attester has an attest asp and can measure the appraiser. *)
Definition l_rp : lMan := mkLOCAL [req_asp] [attester].
Definition l_attester : lMan := mkLOCAL [attest_asp] [appraiser].
Definition l_appraiser : lMan := mkLOCAL [appraise_asp] [].

Example s1_gMan := (relyingParty !-> Some l_rp ; attester !-> Some l_attester ; appraiser !-> Some l_appraiser).

(***************************
  DEFINING EXECUATABLE FUNCTION 

  To check if any phrase is executable, check to see if it is in the Manifest. 
  *************************** *)

Definition hasASP (k: Plc) (gm:gMan) (a:ASP) : Prop :=
    match gm k with 
    | None => False 
    | Some v => In a v.(lASP)
    end.
    

Compute hasASP attester (s1_gMan) attest_asp.
(* ^hmmm the type of this is interesting... either they are equal or it's false. 
   Does this mean something is wrong? *)

Definition hasASP_helper : forall k gm a v, gm k = Some v -> ~ In a v.(lASP)-> ~ hasASP k gm a.
Proof.
  intros. destruct H0. induction a. destruct v. Abort. 
  
    

(* I wonder if everything is decidable? Shouldn't a target either have the ASP or not have the ASP?*)

Definition hasASP_dec : forall k gm a, {hasASP k gm a} + {~ hasASP k gm a}.
Proof.
  intros k gm a. 
  Abort. 

Example check1 : hasASP attester (s1_gMan) attest_asp.
Proof.
    constructor. reflexivity.
Qed.  

(* check to see if k can measure req_plc *)
Definition canMeas (k:Plc) (req_plc : Plc) (gm : gMan) : Prop :=
  match gm k with 
  | None => False 
  | Some v => In req_plc v.(M)
  end.

Compute canMeas attester appraiser s1_gMan.

Ltac cons_refl := constructor ; reflexivity.

Example check2 : canMeas attester appraiser s1_gMan.
Proof.
  cons_refl.
Qed.

(* could we prove that if it is executable then you will get some evidence 
- map evidence to protocol then protocol to executability 
    - if copland request is executed then it is choosen or else it gets refined *)

Inductive Executable : Term -> gMan -> Plc -> Prop :=
| asp' : forall t gm k a, t = asp a -> hasASP k gm a -> Executable t gm k
| att' : forall t gm k p t1, t = att p t1 -> canMeas k p gm -> Executable t gm k
| lseq' : forall t gm k t1 t2, t = lseq t1 t2 -> Executable t1 gm k -> Executable t2 gm k
| bseq' : forall t gm k t1 t2 sp, t = bseq sp t1 t2 -> Executable t1 gm k -> Executable t2 gm k
| bpar' : forall t gm k t1 t2 sp, t = bpar sp t1 t2 -> Executable t1 gm k -> Executable t2 gm k.

    (* Fixpoint Executable (t:Term) (gm:gMan) (k:Plc) : Prop :=
  match t with
  (* check to make sure ASP is in manifest *)
  | asp a => hasASP k gm a
  (* check that k can request a measurement from p *)
  | att p t1 => canMeas k p gm /\ Executable t1 gm p 
  (* check each sub term is executable *)
  | lseq t1 t2 => Executable t1 gm k /\ Executable t2 gm k
  | bseq sp t1 t2 => Executable t1 gm k /\ Executable t2 gm k
  | bpar sp t1 t2 => Executable t1 gm k /\ Executable t2 gm k
  end. *)

(* simple example. Checking that the attester can execute the attest asp *)
Example check_exec1 : Executable (asp attest_asp) s1_gMan attester.
Proof.
  apply asp' with (attest_asp). reflexivity. unfold hasASP. simpl. left.  reflexivity. 
  (* proof with inductive is much harder here *)
  constructor. reflexivity.
Qed.

(* check that the attester can request the appraise measurement from the appraiser *)
Example check_exec2 : Executable (att appraiser (asp appraise_asp)) s1_gMan attester.
Proof. 
  constructor.
  + constructor. reflexivity.
  + constructor. reflexivity.
Qed.

Search sumbool.

(* proof of executability *)

Theorem execute : forall t gm k, {Executable t gm k} + {~Executable t gm k}.
Proof.
  solve_decidable. 
  unfold decidable. 
repeat decide equality.
Print decide equality. 
  +     

(***************************
  DEFINING GENERATE FUNCTION 
  *************************** *)

(***************************
  DEFINING COMBINATION FUNCTION 
  ***************************)

(****************************
  TARGET'S SELECTION POLICY
*****************************)  

(*****************************
  PRIVACY POLICY
******************************)

(******************************
    THE NEGOTIATE FUNCTION 
    Here we take the request and the target's manifest to actually generate a list of protocols. 
  *****************************)
