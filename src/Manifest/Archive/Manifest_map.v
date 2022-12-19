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

Require Import Cop.Copland.
Import Copland.Term.

Print Plc.

Theorem eq_plc (x y : Plc): {x = y} +  {x <> y} .
Proof.
  repeat decide equality. 
Defined.

(* **************
DEFINING MANIFEST
- include a list of ASPs
- measures relation 
- eventually context relation? 

DEFINING SYSTEM
- a collection of manifests

DEFINING ENVIORNMENT 
- a singular system or a union of systems 
**************  *)

Record Manifest : Set := mkMAN 
{ lASP : (list ASP); 
M : list Plc }. 

(* map properties... taken from Pierce in Sofware Foundations
https://softwarefoundations.cis.upenn.edu/lf-current/Maps.html *)

Definition System : Type := Plc -> (option Manifest).

Definition t_empty : System := (fun _ => None). 

Definition t_update (m : System) (x : Plc) (v: (option Manifest)):=
  fun x' => if eq_plc x x' then v else m x'.
  
Notation "x '!->' v ';' m" := (t_update m x v)
(at level 100, v at next level, right associativity).

Notation "x '!->' v" := (t_update t_empty x v)
(at level 100).

Inductive Environment : Type :=
| one : System -> Environment
| union : Environment -> Environment -> Environment.

(****************
MEASURES RELATION 
*****************)

Notation Rely := "Rely"%string.
Notation Target := "Target"%string.
Notation Appraise := "Appraise"%string.

Inductive Meas : relation Plc := 
| rp_att : Meas Rely Target
| att_app : Meas Target Appraise.

(***************************
PROPERTIES OF THE SYSTEM 
*************************** *)

(* make sure that place k has ASP a. Can check in the manifest for this. *)
Definition hasASP (k: Plc) (gm:System) (a:ASP) : Prop :=
  match gm k with 
  | None => False 
  | Some v => In a v.(lASP)
  end.
  
(* check to see if req_plc can measure meas_plc... this uses the measures relation ... may need to enrich this definition *)
Definition canMeas (req_plc: Plc) (meas_plc : Plc) (gm : System) : Prop :=
  match gm req_plc with 
  | None => False 
  | Some v => In meas_plc v.(M)
end.

Definition canMeas_dec :forall k meas_plc gm, {canMeas k meas_plc gm} + {~ canMeas k meas_plc gm}.
Proof.
  intros. unfold canMeas. destruct (gm k); simpl.
  + induction m. simpl.
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
  intros k gm a. unfold hasASP. destruct (gm k). simpl. induction m. simpl. induction lASP0. apply in_dec; repeat decide equality. apply in_dec; repeat decide equality. auto. 
Defined. 


Definition canMeas_dec' :forall k meas_plc gm, {canMeas k meas_plc gm} + {~ canMeas k meas_plc gm}.
Proof.
  intros. unfold canMeas. destruct (gm k); simpl.
  + induction m. simpl.
  apply in_dec; repeat decide equality.
  + auto.
  Defined.

(****************
EXECUTABILITY 
*****************)

Fixpoint Executable (t:Term) (gm:System) (k:Plc) : Prop :=
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
Abort.   

Theorem execute : forall t gm k, {Executable t gm k} + {~Executable t gm k}.
Proof.
  intros.  generalize k. induction t; intros. 
  + unfold Executable. apply hasASP_dec.
  (* ok, when i get to this case I am stuck. canMeas doesn't tell me anything about the relationship between k and p that I can use in the IHt. *)
  + simpl. intros. assert (H: {canMeas k0 p gm} + {~canMeas k0 p gm}). apply canMeas_dec.
  destruct (IHt p). 
  ++ intros. left. intros. apply e.
  ++ destruct H.
  +++ right. unfold not in *. intros. apply n. apply H. apply c.
  +++ left. intros. congruence. 
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
Defined.

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
****************

Definition req_asp := ASPC (asp_paramsC request [] attester o1).
Definition attest_asp := ASPC (asp_paramsC attest_id [] attester o1).
Definition appraise_asp := ASPC (asp_paramsC appraise_id [] appraiser o1).

(* attester has an attest asp and can measure the appraiser. *)
Definition l_rp : Manifest := mkMAN [req_asp] [attester].
Definition l_attester : Manifest := mkMAN [attest_asp] [appraiser].
Definition l_appraiser : Manifest := mkMAN [appraise_asp] [].

Example s1_System := (relyingParty !-> Some l_rp ; attester !-> Some l_attester ; appraiser !-> Some l_appraiser).

Example lookup : s1_System appraiser = Some l_appraiser.
Proof. auto. Qed.

Ltac cons_refl := constructor ; reflexivity.

Example check2 : canMeas attester appraiser s1_System.
Proof.
  cons_refl.
Qed.

(* simple example. Checking that the attester can execute the attest asp *)
Example check_exec1 : Executable (asp attest_asp) s1_System attester.
Proof. 
Abort.

(* check that the appraiser cannot execute the attest asp *)
Example check_exec2 : Executable (asp attest_asp) s1_System appraiser.
Proof. Abort.

(* check that the attester can request the appraise measurement from the appraiser *)
Example check_exec2 : Executable (att appraiser (asp appraise_asp)) s1_System attester.
Proof. Abort.

Compute hasASP attester (s1_System) attest_asp.
(* ^hmmm the type of this is interesting... either they are equal or it's false. 
Does this mean something is wrong? *)  

Ltac solve_left := simpl; left; auto.
Ltac solve_right H1 H2 := simpl; right; intros; destruct H1; inversion H1; destruct H2; apply H1.

Example check1 : hasASP attester (s1_System) attest_asp.
Proof.
constructor. reflexivity.
Qed.  

Example canMeas_ex : canMeas attester appraiser s1_System.
Proof.
Abort.       

*)