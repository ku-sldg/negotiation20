Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Require Import Coq.Relations.Relation_Definitions. 
Require Import String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.Logic.Decidable.
Require Import myTerm.

(****************
LOCAL MANIFEST 
*****************)

Record lMan : Set := mkLOCAL 
{ lASP : (list ASP); 
  M : list Plc }. 

Definition eq_plc : forall x x' : Plc, {x = x'} + {x <> x'}.
Proof. repeat decide equality. Defined.  


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