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
Require Import Coq.Bool.Bool.

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

Inductive TARG_ID: Set := 
| o1 : TARG_ID 
| o2 : TARG_ID.

Inductive Arg: Set := 
| a_pub_key : Arg 
| t_priv_key : Arg 
| t_pub_key : Arg. 

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
| HSH: ASP.

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
DEFINING MANIFEST
- include a list of ASPs
- measures relation 
- eventually context relation? 

DEFINING SYSTEM
**************  *)

Record lMan : Set := mkLOCAL 
{ lASP : (list ASP); 
M : list Plc }. 

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

Definition gMan := partial_map.

(****************
MEASURES RELATION 
*****************)

Inductive Meas : relation Plc := 
| rp_att : Meas relyingParty attester
| att_app : Meas attester appraiser.

(***************************
PROPERTIES OF THE SYSTEM 
*************************** *)

(* make sure that place k has ASP a. Can check in the manifest for this. *)
Definition hasASP (k: Plc) (gm:gMan) (a:ASP) : Prop :=
  match gm k with 
  | None => False 
  | Some v => In a v.(lASP)
  end.
  
(* check to see if req_plc can measure meas_plc... this uses the measures relation ... may need to enrich this definition *)
Definition canMeas (req_plc: Plc) (meas_plc : Plc) (gm : gMan) : Prop :=
  match gm req_plc with 
  | None => False 
  | Some v => In meas_plc v.(M)
end.

Definition canMeas_dec :forall k meas_plc gm, {canMeas k meas_plc gm} + {~ canMeas k meas_plc gm}.
Proof.
  intros. unfold canMeas. destruct (gm k); simpl.
  + induction l. simpl.
  apply in_dec; repeat decide equality.
  + auto.
Qed.

(* Need some way to return target system from canMeas *)
Check canMeas.

Theorem in_dec {A:Type}: (forall x y:A, {x = y} + {x <> y}) -> 
  forall (a:A) (l:list A), {In a l} + {~ In a l}.
Proof. 
  intros. induction l.
  + right. auto.
  + inversion IHl.
  ++ left. simpl. right. auto.
  ++ specialize X with a a0. inversion X.
  +++ simpl. left. left. apply eq_sym. apply H0.
  +++ simpl. right. unfold not. intros. inversion H1. apply eq_sym in H2. destruct H0. apply H2. destruct H. apply H2.
Defined.


Inductive trc {A} (R: A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z, R x y -> trc R y z -> trc R x z.
  
(****************
DECIDEABILITY 
*****************)

Theorem eq_arg (x y : Arg): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

Theorem eq_asp (x y : ASP_ID): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

Definition eq_term_dec : forall t1 t2 : Term, {t1 = t2} + {t1 <> t2}.
Proof. 
  repeat decide equality.
Defined.  

Lemma eq_sym {A:Type} : forall x y : A, x = y -> y = x.
Proof. auto. Qed.   

Theorem in_dec' {A:Type}: (forall x y:A, {x = y} + {x <> y}) -> 
  forall (a:A) (l:list A), {In a l} + {~ In a l}.
Proof. 
  intros. induction l.
  + right. auto.
  + inversion IHl.
  ++ left. simpl. right. auto.
  ++ specialize X with a a0. inversion X.
  +++ simpl. left. left. apply eq_sym. apply H0.
  +++ simpl. right. unfold not. intros. inversion H1. apply eq_sym in H2. destruct H0. apply H2. destruct H. apply H2.
Defined.

Definition hasASP_helper : forall a v, {In a v.(lASP)} + {~In a v.(lASP)}. 
Proof.
  intros. induction v. simpl. induction lASP0; apply in_dec; repeat decide equality.
Defined. 

Definition hasASP_dec : forall k gm a, {hasASP k gm a} + {~ hasASP k gm a}.
Proof.
  intros k gm a. unfold hasASP. destruct (gm k). simpl. induction l. simpl. induction lASP0. apply in_dec; repeat decide equality. apply in_dec; repeat decide equality. auto. 
Defined. 


Definition canMeas_dec' :forall k meas_plc gm, {canMeas k meas_plc gm} + {~ canMeas k meas_plc gm}.
Proof.
  intros. unfold canMeas. destruct (gm k); simpl.
  + induction l. simpl.
  apply in_dec; repeat decide equality.
  + auto.
  Defined.

(****************
EXECUTABILITY 
*****************)

Fixpoint Executable (t:Term) (gm:gMan) (k:Plc) : Prop :=
match t with
(* check to make sure ASP is in manifest *)
| asp a => hasASP k gm a
(* check that k can request a measurement from p *)
| att p t1 => canMeas k p gm -> Executable t1 gm p
(* check each sub term is executable *)
| lseq t1 t2 => Executable t1 gm k /\ Executable t2 gm k
| bseq sp t1 t2 => Executable t1 gm k /\ Executable t2 gm k
| bpar sp t1 t2 => Executable t1 gm k /\ Executable t2 gm k
end.


Theorem in_a_in_a0: forall (p:Plc) (a:Plc) (l0:list Plc), In p l0 -> In p (a :: l0).
Proof. 
intros. induction l0. 
+ inversion H.
+ simpl in *. right. apply H.
Qed.  

(* this is too strong... but necessary for solving the proof *)
Theorem canMeas_neq : forall k p gm, canMeas k p gm -> k <> p.
Proof.
    intros k p gm. induction k; destruct p; intros.
    + simpl in *. unfold canMeas in H. destruct (gm relyingParty) in H.  simpl in H. 
Abort.   

Theorem execute : forall t gm k, {Executable t gm k} + {~Executable t gm k}.
Proof.
  intros.  generalize k. induction t; intros. 
  + unfold Executable. apply hasASP_dec.
  (* ok, when i get to this case I am stuck. canMeas doesn't tell me anything about the relationship between k and p that I can use in the IHt. *)
  + simpl. intros. assert (H: {canMeas k0 p gm} + {~canMeas k0 p gm}). apply canMeas_dec.
  destruct (IHt p). 
  ++ intros. left. intros. apply e.
  ++  destruct H. right. unfold not in *. intros. apply n. apply H. apply c. left. intros. congruence. 
  + simpl. specialize IHt1 with k0; specialize IHt2 with k0. inversion IHt1; inversion IHt2.  
  ++ left. split. apply H. apply H0.
  ++ right. unfold not in *. intros. inversion H1. apply H0. apply H3.
  ++ right. unfold not in *. intros. apply H. inversion H1. apply H2.
  ++ right. unfold not in *. intros. inversion H1. apply H. apply H2.
  + simpl. specialize IHt1 with k0; specialize IHt2 with k0. inversion IHt1; inversion IHt2.  
  ++ left. intros. split. apply H. apply H0.
  ++ right. unfold not in *. intros. inversion H1. apply H0. apply H3.
  ++ right. unfold not in *. intros. apply H. inversion H1. apply H2.
  ++ right. unfold not in *. intros. inversion H1. apply H. apply H2.
  + simpl. specialize IHt1 with k0; specialize IHt2 with k0. inversion IHt1; inversion IHt2.  
  ++ left. intros. split. apply H. apply H0.
  ++ right. unfold not in *. intros. inversion H1. apply H0. apply H3.
  ++ right. unfold not in *. intros. apply H. inversion H1. apply H2.
  ++ right. unfold not in *. intros. inversion H1. apply H. apply H2.
Qed.




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

(****************
EXAMPLE  
*****************)

Definition req_asp := ASPC (asp_paramsC request [] attester o1).
Definition attest_asp := ASPC (asp_paramsC attest_id [] attester o1).
Definition appraise_asp := ASPC (asp_paramsC appraise_id [] appraiser o1).

(* attester has an attest asp and can measure the appraiser. *)
Definition l_rp : lMan := mkLOCAL [req_asp] [attester].
Definition l_attester : lMan := mkLOCAL [attest_asp] [appraiser].
Definition l_appraiser : lMan := mkLOCAL [appraise_asp] [].

Example s1_gMan := (relyingParty !-> Some l_rp ; attester !-> Some l_attester ; appraiser !-> Some l_appraiser).

Example lookup : s1_gMan appraiser = Some l_appraiser.
Proof. auto. Qed.

Ltac cons_refl := constructor ; reflexivity.

Example check2 : canMeas attester appraiser s1_gMan.
Proof.
  cons_refl.
Qed.

(* simple example. Checking that the attester can execute the attest asp *)
Example check_exec1 : Executable (asp attest_asp) s1_gMan attester.
Proof. 
Abort.

(* check that the appraiser cannot execute the attest asp *)
Example check_exec2 : Executable (asp attest_asp) s1_gMan appraiser.
Proof. Abort.

(* check that the attester can request the appraise measurement from the appraiser *)
Example check_exec2 : Executable (att appraiser (asp appraise_asp)) s1_gMan attester.
Proof. Abort.

Compute hasASP attester (s1_gMan) attest_asp.
(* ^hmmm the type of this is interesting... either they are equal or it's false. 
Does this mean something is wrong? *)  

Ltac solve_left := simpl; left; auto.
Ltac solve_right H1 H2 := simpl; right; intros; destruct H1; inversion H1; destruct H2; apply H1.

Example check1 : hasASP attester (s1_gMan) attest_asp.
Proof.
constructor. reflexivity.
Qed.  

Example canMeas_ex : canMeas' attester appraiser s1_gMan.
Proof.
  unfold canMeas'. destruct canMeas_dec.
  + unfold not. intros. inversion H.
  + unfold not in n. exfalso. apply n.         