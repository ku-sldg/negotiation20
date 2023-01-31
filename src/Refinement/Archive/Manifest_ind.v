(********** 
Second attempt at capturing the manifest. 

Future work: Going to try to use ensembles for ASPs instead of lists. *)

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

(* Require Import Term_Defs Example_Phrases_Admits.*) 
Require Import Coq.Relations.Relation_Definitions. 
Require Import String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.

(*********************
COPLAND GRAMMAR 
Had to redefine the Copland grammar below in order to write some examples. 
**********************)

Definition Plc: Set := nat.
Definition N_ID: Set := nat.

Definition Event_ID: Set := nat.

Inductive ASP_ID : Set := 
| attest_id : ASP_ID
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

(* defining manifests *)

Inductive local := 
| l_man : Plc -> list ASP -> local.

Inductive global := 
| g_man : list local -> global.

(* define request *)

Definition request := TARG_ID. 


(* generate all possible protocols from manifest *)
Definition ASP_to_Term (p :Plc) (a : ASP) : Term := 
  match a with 
  | CPY => asp (CPY)
  | ASPC (asp_paramsC id l_arg p targ_id) => att p (asp (ASPC (asp_paramsC id l_arg p targ_id)))
  | HSH => asp (HSH)
  | SIG => asp (SIG) 
  end.
  
(* start by attempting to generate a list of ASPs *)
Definition generate (glo : global) (l1 : list Term) : list Term := 
  match glo with 
  | g_man nil => l1 
  | g_man (x::nil) => match x with 
                        | l_man p (x'::xs') => [ASP_to_Term p x'] ++ l1
                        | l_man p (nil) => l1
                        end
  | g_man (x::xs) => 
  end.
      
(* example phrases if we choose to use ensembles *)

Definition one : Ensemble ASP := (Add _ (Singleton _ SIG) HSH).
Definition two : Ensemble ASP := (Add _ (Add _ (Singleton _ SIG) HSH) (ASPC (asp_paramsC attest_id [] 1 o1))).

Definition l1 : local := l_man 1 [SIG].
Definition l2 : local := l_man 2 [HSH].

Definition g1 : global := g_man [l1; l2]. 
(* getter functions *)

Definition get_loc (g : global) : (list local) := 
match g with 
| g_man l => l 
end.

Definition get_ASP (l : local) : (list ASP) := 
match l with 
| l_man _ l' => l' 
end.

Definition get_plc (l : local) : Plc := 
match l with 
| l_man p _ => p 
end.