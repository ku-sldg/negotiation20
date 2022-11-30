(* First attempt at a transition system for modeling Term generation from Manifests 

By: Anna Fritz (8.19.22) *)

Require Import Lists.List.
Import ListNotations.
Require Import Coq.Lists.ListDec. 

Require Import Cop.Copland.
Import Copland.Term.
Import Copland.Evidence. 
Require Import Manifest. 
Import Manifest.ManifestTerm.

Require Import String.

Require Import AccessControl. 

Set Implicit Arguments.

(* TO DO check out Disclose.v & event semantics in term_defs.v *) 

Print request. 
(* | req : string -> UserType -> resource -> request
   | many : request -> request -> request. *)

(* Two states: 
    1. answer state. 
      This is the proposal. 
    2. accumlator state. 
      The input state will be the request while the accumulator 
      state will begin as an empty list. Once the request is an
      empty list, then the transition system moves into an 
      answer state.  *)
Inductive refine_state := 
| proposal (pr : list Term)
| requesting (input : request) (accumulator : list Term) (s:System) (p:Plc).

(* the initialization state starts with the request and an 
   empty list *)
Inductive init (r : request) (s: System) (p:Plc) : refine_state -> Prop := 
| Init : init r s p (requesting r [] s p).

(* the final state is the list of terms that are acceptable. AKA the proposal. *)
Inductive final : refine_state -> Prop := 
| Final : forall prop, final (proposal (prop)).

Definition check_exe (t:Term) (k:Plc) (s:System) : list Term := 
  if executables_dec t k s then [t] else [].


Inductive step : refine_state -> refine_state -> Prop := 
| Done : forall acc s p, 
          step (requesting [] acc s p) (proposal acc)
| Refine : forall acc t s ts p, 
          step (requesting (t :: ts) acc s p) (requesting ts (check_exe t p s ++ acc) s p).

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
  Definition p1 := Target.
  
  Example req_vc : step^* (requesting req1 [] example_sys_1 p1) (proposal [asp (aspc2)]).
  Proof.
    simpl.
    eapply TrcFront.
    + apply Refine.
    + simpl. eapply TrcFront.
    ++ apply Done.
    ++ apply TrcRefl.
  Qed. 

  Example req_vc' : step^* (requesting req1 [] example_sys_1 p1) (proposal [asp (aspc2)]).
  Proof.
    repeat econstructor. 
  Qed.
  
  (* Now, we can turn the state machine into a transition system using the record type *)

  Record trsys state := {
    Initial : state -> Prop;
    Step : state -> state -> Prop
  }.

  (* The type of state here is polymorphic meaning this definiton lends itself to use for any state transition system *)

  (* Here, use the transition system for refinement. *)

  Definition refinement_sys (req : list Term) (s:System) (p:Plc) : trsys refine_state := {|
    Initial := init req s p ; 
    Step := step |}.

  (* Define the reachable states *)

  Inductive reachable {state} (sys : trsys state) (st : state) : Prop :=
  | Reachable : forall st0,
    sys.(Initial) st0
    -> sys.(Step)^* st0 st
    -> reachable sys st.

  (* now, find an invariant... 
     I think our invariant is that any proposal will be a subset of the requested list. *)

     (* first, subset for lists operation 

  Fixpoint sublist {A: Type} (l1 l2 : list A) : Prop := 
    match l2 with 
    | [] => True 
    | h :: t => if In_ h l1 then sublist l1 t else False 
    end.*)

    Lemma nat_dec: forall x y : nat, {x = y}+{x <> y}.
    Proof. repeat decide equality. Qed.   

    Check nat_dec. 

    Example sublist1 : {incl [1; 2; 3] [2; 3]} + {~ incl [1; 2; 3] [2; 3]}.
    Proof. right. unfold not. unfold incl.  intros. unfold In in H. 
      destruct (H 1).
      + left. reflexivity.
      + inversion H0.
      + inversion H0. 
      ++ inversion H1. 
      ++ apply H1.
    Qed. 

    Print in_dec.
    
    Theorem in_dec {A:Type} : (forall x y: A, {x = y} + {x <> y}) -> forall (a:A) (l:list A), {In a l} + {~ In a l}.
    Proof. 
      intros. induction l.
      + right. apply in_nil.
      + simpl in *. induction IHl.
      ++ left. right. apply a1.
      ++ specialize X with a a0. inversion X.
      +++ left; left; rewrite H; reflexivity.
      +++ right. unfold not in *. intros. inversion H0. 
      ++++ apply H. rewrite H1. reflexivity.
      ++++ apply b. apply H1.
    Qed. 

    Definition Term_dec : forall x y : Term, {x = y} + {x <> y}. 
    Proof. repeat decide equality. Qed.
    
    Definition InTerm_dec : forall (a:Term) (l1: list Term), {In a l1} + {~ In a l1}.
    Proof. pose proof Term_dec. intros. induction l1.
    + right. unfold not. intros. inversion H0.
    + simpl in *. specialize H with a0 a.  destruct H; subst.
    ++ left. left.  auto.
    ++ inversion IHl1.
    +++ left. right. apply H.
    +++ right. unfold not in *. intros. inversion H0. apply n. apply H1. apply H. apply H1.
    Qed.
    
    Ltac inv H := inversion H; subst; clear H. 

    Definition InclTerm_dec : forall (l1 l2 : list Term), {incl l1 l2} + {~incl l1 l2}.
    Proof.
      pose proof Term_dec. pose proof InTerm_dec. intros.
      induction l2; destruct l1; unfold incl. 
      + left. auto.
      + right. unfold not in *. intros. specialize H1 with t. simpl in H1. destruct H1. left. reflexivity.
      + left. intros. inversion H1; clear H1. 
      + inv IHl2; unfold incl in H1.
      ++ left. intros. specialize H1 with a0. simpl. right. apply H1. apply H2.
      ++ right. intros. unfold not in *. intros. apply H1; clear H1. intros. specialize H2 with a. simpl in *.

      Restart.
      intros l1. induction l1.
      + intros. left. unfold incl. intros. inv H.
      + intros. induction l2.
      ++ specialize IHl1 with []. inv IHl1.
      +++  unfold incl in *. right. unfold not; intros. specialize H0 with a. destruct H0. simpl.  auto.
      +++ unfold incl in *. right; unfold not in *. intros. apply H. intros. specialize H0 with a0. simpl. destruct H0. simpl. right. apply H1.
      ++ inv IHl2.
      +++ unfold incl in *. right. unfold not. intros.     left. unfold incl in *. intros. specialize H with a0. simpl in *.    simpl in *.    specialize IHl1 with (a0::l2). inv IHl1.        destruct H.  inv H.   unfold incl. intros.   simpl.
      
      Restart.
      intros. generalize dependent l1. induction l2.
      + intros. unfold incl. unfold not. right.  intros. exact a in H. destruct H.      








    Definition subset_dec : forall l1 l2 : list Term, {incl l1 l2} + {~ incl l1 l2}.
    Proof.
      intros. 
      assert (H: {l1 = l2} + {l1 <> l2}).
      { induction l1; induction l2; auto.
        + right. unfold "<>". intros. inversion H.
        + inversion IHl1. 
        ++ right. rewrite H. unfold "<>". intros. inversion H0.
        ++ right. unfold not in *. intros. inversion H0. }
      induction l1; induction l2.
      + left. unfold incl. intros. apply H0.
      + 
    Abort. 
    (* not strong enough ... *)

    Definition subset_dec' : forall (t1 t2 : Term) (l1 l2 : list Term),
  Definition refine_invariant (request:list Term) (s:System) (p:Plc) (st:refine_state) : Prop := 
    match st with 
    | proposal ts => 
    | requesting 