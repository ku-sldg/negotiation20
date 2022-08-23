(* First attempt at a transition system for modeling Term generation from Manifests 

By: Anna Fritz (8.19.22) *)

Require Import Manifest_map.
Require Import Cop.Copland. 
Import Copland.Term.

Print Environment.
Check Term. 
Print Evidence. 

(***************************
  DEFINING GENERATE FUNCTION 
  *************************** *)

(* if we want to use the modeling check stuff then we can look here: https://github.com/achlipala/frap/blob/master/ModelChecking.v... but then we need a transition system  *)

(* first, try writing "generate" as an imperative program. Start with k (the starting measurement place) gm (the global manifest) and l (an empty list of terms. this will be used as the return value )*)

Print Manifest.
(* Manifest = collection of ASPs and the measures relations *)

Print System. 
(* System = collection of manifests *)

Print Environment.
(* Environement = collection of systems. Will be useful for describing the *)

(* For any place, "generate_ASPs" returns a list of ASPs present at that place. This is a first step at a more primitive way of generated a list of terms. *)
Definition generate_ASPs (k: Plc) (s : System) : list ASP := 
match s k with 
| None => [] 
| Some t => t.(lASP)
end.  

Print hasASP_dec.
Print ASP.

(* Process for generating protocols 
    INPUT : system specifications, ideal piece of evidence 
    OUTPUT : a list of evidence that meets specified requirements 
    STEPS : 
        1. Select with first piece of evidence in evidence chain
        2. Check if corresponding ASP or measurement exists within system 
        3. Repeat until all states have been visited or the result matches the ideal evidence *)

(* QUESTIONS
   - in the current evidence structure, there is no way to represent hashing siging or any of the ASP primitives besides ASPC ??
    *)

Print Evidence. 

Fixpoint generate (s: System) (r : Evidence) (l : list Evidence): list Evidence := 
    match r with 
    | mt =>  l 
    | nn id => [nn id] ++ l
    | gg p a e => l
    | _ => []
    end. 

(* here are the states. Either a final stat or an accumulation state. Eventually I think the final state will be a lattice of terms. *)
Inductive state := 
| final_terms (term : list Term)
| accumulate (input : Term) (acc : list Term).

(* initalize with some original input added to an empty list. *)
Inductive init (original_input : Term) : state -> Prop :=
|Init : init original_input (accumulate (original_input) ([original_input] ++ [])).

Inductive final : state -> Prop := 
| Final : forall t, final (final_terms t).
