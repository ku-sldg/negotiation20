(* First attempt at a transition system for modeling Term generation from Manifests 

By: Anna Fritz (8.19.22) *)

Require Import Lists.List.
Import ListNotations.

Require Import Cop.Copland.
Import Copland.Term.
Import Copland.Evidence. 
Require Import Manifest. 
Import Manifest.ManifestTerm. 

Require Import String. 

(* TO DO check out Disclose.v & event semantics in term_defs.v *) 

(* Two states: 
    1. answer state. 
      This is the proposal. 
    2. accumlator state. 
      The input state will be the request while the accumulator 
      state will begin as an empty list. Once the request is an
      empty list, then the transition system moves into an 
      answer state.  *)
Inductive state := 
| proposal (pr : list Term)
| requesting (input accumulator : list Term) (s:System).

(* the initialization state starts with the request and an 
   empty list *)
Inductive init (req : list Term) (s: System) : state -> Prop := 
| Init : init req s (requesting req [] s).

(* the final state is the list of terms that are acceptable. AKA the proposal. *)
Inductive final : state -> Prop := 
| Final : forall prop, final (proposal (prop)).

Definition check_exe (t:Term) (k:Plc) (s:System) : list Term := 
  if executables_dec t k s then [t] else [].

(* need to get the place of measurement to check executability *)
Fixpoint get_Plc (t:Term) : Plc := 
  match t with 
  | asp (ASPC sp fwd (asp_paramsC id arg pl tar)) => pl 
  | asp _ => "p"%string
  | att p t => p 
  | lseq t1 t2 => get_Plc t1 
  | bseq sp t1 t2 => get_Plc t2 
  | bpar sp t1 t2 => get_Plc t2
  end.  

Inductive step : state -> state -> Prop := 
| Done : forall acc s, 
          step (requesting [] acc s) (proposal acc)
| Step : forall acc t s ts, 
          step (requesting (t :: ts) acc s) (requesting ts (check_exe t (get_Plc t) s ++ acc) s).

(* We need the TRC to reason about all states *)
Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z.

  Notation "R ^*" := (trc R) (at level 0).

  Definition example_sys_1 := env e3.

  Print e0.
  (* empty *)
  
  Print e1.
  (* The relying party has ASPC1 (use asp1 to measure x and y) and can measure the target *) 

  Print e2.
  (* The target can sign the virus checker and request measurement from the appraiser *) 

  Print e3. 
  (* The apprsier can hash *)

 (* Lets say the request is to hash the virus checker *)
  Definition req1 := [asp (aspc2)].
  
  Example req_vc : step^* (requesting req1 [] example_sys_1) (proposal [asp (aspc2)]).
  Proof.
    simpl.
    eapply TrcFront.
    + apply Step.
    + simpl. eapply TrcFront. simpl. apply Done. apply TrcRefl.
  Qed. 


