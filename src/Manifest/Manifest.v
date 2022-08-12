Require Import Lia.
Require Import Relations.
Require Import Lists.List.
Import ListNotations.
Require Import String.
Require Import Cop.Copland.
Import Copland.Term.
Require Import Ltacs TypeClasses Maps.

(** Stuff to do:
 * - Decidability of executable.  Might not work
 * - Model finder migration from Chlipala
 * - Flesh out INI and Manifest types
 *)

Module ManifestTerm.

  Notation Rely := "Rely"%string.
  Notation Target := "Target"%string.
  Notation Appraise := "Appraise"%string.

  Notation aspc0 :=
    (ASPC ALL EXTD (asp_paramsC "asp0"%string ["x"%string;"y"%string] Target Target)).
  Notation aspc1 :=
    (ASPC ALL EXTD (asp_paramsC "asp1"%string ["x"%string;"y"%string] Target Target)).

  (** [Manifest] defines an attestation manger a list of ASPs and other
   * managers it is aware of.  [Manifest] defines a single AM and its
   * interconnections.  [add] simulates address information and [tpm]
   * simulates cruft necessary to initialize its TPM.
   *)
  Record Manifest := {
      asps : list ASP
      ; M : list Plc
(*
      ; C : list string
      ; key : string
      ; address : nat
      ; tpm : nat
*)
    }.

  Theorem asp_dec : forall (a1 a2 : ASP),
    {a1 = a2} + {a1 <> a2}.
  Proof.
    repeat decide equality.
  Qed.

  (** [Environment] is a set of AM's each defined by a [Manifest].
   * The domain of an [Environment] provides names for each [Manifest].
   * Names should be the hash of their public key, but this restriction
   * is not enforced here. 
   *)

  Import MapNotations.
  Import MapsLtac.

  Definition Environment : Type :=  Map Plc Manifest.

  Definition e_empty : Environment := {}.
  
  Definition e_update (m : Environment) (x : Plc) (v : Manifest) :=
    (x !-> v ; m).
(* 
  Lemma e_apply_empty: forall x, @e_empty x = None.
  Proof.
    intros.
    auto.
  Qed. *)

  Lemma e_update_eq : forall (m: Environment) x v,
      (e_update m x v) ![x] = Some v.
  Proof.
    intros. unfold e_update.
    smp. map_unfold. unfold decEq_string.
    destruct (plc_dec x x); eauto. 
    cong.
  Qed.

  Theorem e_update_neq : forall v x1 x2 (m:Environment),
      x1 <> x2 -> (e_update m x1 v) ![x2] = (m ![x2]).
  Proof.
    intros v x1 x2 m.
    intros H. smp.
    map_unfold. unfold decEq_string.
    destruct (plc_dec x2 x1); eauto; cong.
  Qed.

  Theorem e_update_shadow : forall (m:Environment) v1 v2 x,
    forall x',
      (e_update (e_update m x v1) x v2) ![ x'] 
      = ((e_update m x v2) ![ x']).
  Proof.
    intros m v1 v2 x x'.
    unfold e_update.
    map_unfold. unfold decEq_string.
    destruct (plc_dec x' x); eauto.
  Qed.

  Theorem e_update_same : forall x (m : Environment) v,
    m ![x] = Some v ->
      forall x', (e_update m x v) ![x'] = (m ![x']).
  Proof.
    intros x m v HV x'.
    unfold e_update.
    map_unfold. unfold decEq_string.
    destruct (plc_dec x' x); eauto.
    subst. rewrite <- HV. refl.
  Qed. 

  Theorem e_update_permute : forall v1 v2 x1 x2 (m : Environment),
      x2 <> x1 ->
      forall x', (e_update (e_update m x2 v2) x1 v1) ![x']
      = ((e_update (e_update m x1 v1) x2 v2) ![x']).
  Proof.
    intros v1 v2 x1 x2 m HX x'.
    unfold e_update.
    map_unfold. unfold decEq_string.
    destruct (plc_dec x' x2); eauto.
    destruct (plc_dec x' x1); eauto.
    cong.
  Qed.

  (** Definition of environments for use in examples and proofs.  Note they
   * build constructively through [e3] that is the map for this system
   *)
  Definition e0 := e_empty.
  Definition e1 :=
    (Rely !-> ({| asps := [aspc1]; M:= [Target] |}) ; e0).
  Definition e2 :=
    (Target !-> ({| asps := [SIG]; M:= [Appraise] |}) ; e1).
  Definition e3 :=
    (Appraise !-> ({| asps := [HSH] ; M:= [] |}) ; e2).
  
  Inductive System : Type :=
  | env : Environment -> System
  | union : System -> System -> System.


  Definition hasASPe(k:string)(e:Environment)(a:ASP): bool :=
    match (e ![k]) with
    | None => false
    | Some m => 
      match in_dec asp_dec a m.(asps) with
      | left _ => true
      | right _ => false
      end
    end.      

  Fixpoint hasASPs(k:string)(s:System)(a:ASP): bool :=
    match s with
    | env e => (hasASPe k e a)
    | union s1 s2 => orb (hasASPs k s1 a) (hasASPs k s2 a)
    end.

   Ltac prove_exec' :=
    smp; eauto; unfold hasASPe; smp; 
    destruct asp_dec; eauto; try cong.
 
  Example ex1: hasASPe Rely e3 aspc1 = true.
  Proof. prove_exec'. Qed.

  Example ex2: hasASPe Rely e3 CPY = false.
  Proof. prove_exec'. Qed.
  
  Example ex5: hasASPs Rely (env e3) aspc1 = true.
  Proof. prove_exec'. Qed.

  Example ex6: hasASPs Rely (union (env e3) (env e2)) aspc1 = true.
  Proof. prove_exec'. Qed.

  
  (** Determine if manifest [k] from [e] knows how to communicate from [k]
   * to [p]
   *)
  Definition knowsOfe(k:string)(e:Environment)(p:Plc): bool :=
    match (e ![k]) with
    | None => false
    | Some m => 
        match in_dec plc_dec p m.(M) with
        | left _ => true
        | right _ => false
        end
    end.

  Fixpoint knowsOfs(k:string)(s:System)(p:Plc): bool :=
    match s with
    | env e => (knowsOfe k e p)
    | union s1 s2 => orb (knowsOfs k s1 p) (knowsOfs k s2 p)
    end.

  Example ex3: knowsOfe Rely e3 Target = true.
  Proof.
    prove_exec'.
  Qed.
  
  Example ex4: knowsOfe Rely e3 Appraise = false.
  Proof.
    prove_exec'.
  Qed.

  Example ex7: knowsOfs Rely (env e3) Target = true.
  Proof.
    prove_exec'.
  Qed.

  Example ex8: knowsOfs Rely (union (env e3) (env e2)) Target = true.
  Proof.
    prove_exec'.
  Qed.
  
  (** Is term [t] exectuable on the attestation manager named [k] in
   * environment [e]?  Are ASPs available at the right attesation managers
   * and are necessary communications allowed?
   *)
  Fixpoint executable(t:Term)(k:string)(e:Environment): bool :=
    match t with
    | asp a  => hasASPe k e a
    | att p t => andb (knowsOfe k e p) (executable t p e)
    | lseq t1 t2 => andb (executable t1 k e) (executable t2 k e)
    | bseq _ t1 t2 => andb (executable t1 k e) (executable t2 k e)
    | bpar _ t1 t2 => andb (executable t1 k e) (executable t2 k e)
    end.

  Fixpoint executables(t:Term)(k:string)(s:System): bool :=
    match t with
    | asp a  => hasASPs k s a
    | att p t => andb (knowsOfs k s p) (executables t p s)
    | lseq t1 t2 => andb (executables t1 k s) (executables t2 k s)
    | bseq _ t1 t2 => andb (executables t1 k s) (executables t2 k s)
    | bpar _ t1 t2 => andb (executables t1 k s) (executables t2 k s)
    end.

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

  Example ex9: (executable (asp SIG) Target e3) = true.
  Proof.
    prove_exec'.
  Qed.
  
  Example ex10: (executable (asp CPY) Target e3) = false.
  Proof.
    prove_exec'.
  Qed.

  Example ex11: (executable (lseq (asp SIG) (asp SIG)) Target e3) = true.
  Proof. prove_exec'. Qed.

  Example ex12: (executable (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely e3) = true.
  Proof. 
    repeat prove_exec'. Qed.

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


  Example ex13: (executables (lseq (asp aspc1)
                                (att Target
                                   (lseq (asp SIG)
                                      (asp SIG))))
                  Rely (union (env e3) (env e2))) = true.
  Proof. repeat prove_exec'. Qed.


  (* Experiments with classes. Nothing here.  Move along...*)
  (* Class Executable T P E :=
    { exec : T -> P -> E -> bool }.

  #[local]
  Instance manExec: Executable Term Plc Environment :=
    { exec := executable
    }.

  Compute (manExec.(exec) (asp NULL) Rely e3).

  #[local]
  Instance sysExec: Executable Term string System :=
    { exec := executables
    }. *)

  (** Moving on to reasoning about system M *)
  
  Definition R(e:Environment)(k1 k2:string): bool :=
    match (e ![k1]) with
    | Some m => 
        match in_dec plc_dec k2 m.(M) with
        | left _ => true
        | right _ => false
        end
    | None => false
    end.

  Example ex14: (R e3 Rely Target) = true.
  Proof. cbv. auto. Qed.

  Example ex15: (R e3 Rely Appraise) = false.
  Proof.
    refl.
  Qed.
  
  Fixpoint Rs(s:System)(k1 k2:string): bool :=
    match s with
    | env e => R e k1 k2
    | union s1 s2 => orb (Rs s1 k1 k2) (Rs s2 k1 k2)
    end.

  Example ex16: (Rs (env e3) Rely Target) = true.
  Proof.
    unfold Rs. apply ex14.
  Qed.

  Example ex17: (Rs (union (env e3) (env e2)) Rely Target)= true.
  Proof.
    unfold Rs. refl.
  Qed.

  (** Traces through [M]
   *)
  
  Inductive trc {A} (R: A -> A -> bool) : A -> A -> Prop :=
  | TrcRefl : forall x, trc R x x
  | TrcFront : forall x y z,
    R x y = true
    -> trc R y z
    -> trc R x z.

  Lemma ex18: (trc (R e3) Rely Rely).
  Proof.
    constructor.
  Qed.

  (** [Measure] relation from [Rely] to [Appraise]
   *)
  Lemma ex19: (trc (R e3) Rely Appraise).
  Proof.
    unfold e3, e2, e1.
    eapply (TrcFront (R e3) _ Target _). prove_exec.
    eapply (TrcFront (R e3) _ Appraise _). prove_exec.
    econstructor.
  Qed.

  Inductive trcs {A} (Rs: A -> A -> bool) : A -> A -> Prop :=
  | TrcRefls : forall x, trcs Rs x x
  | TrcFronts : forall x y z,
    Rs x y = true
    -> trcs Rs y z
    -> trcs Rs x z.

  Lemma ex20: (trcs (Rs (union (env e3) (env e2))) Rely Appraise).
  Proof.
    eapply (TrcFronts (Rs (union (env e3) (env e2))) _ Target _). prove_exec.
    eapply (TrcFronts (Rs (union (env e3) (env e2))) _ Appraise _). prove_exec.
    econstructor.
  Qed.

(** 
  Module ClassExp.

  Class HasASP {A} := {hasASP:string -> A -> ASP -> Prop }.

  Instance HasASPe: HasASP Environment :=
    { hasASP(k:string)(e:Environment)(a:ASP) :=
      match (e k) with
      | None => False
      | Some m => In a m.(asps)
      end
    }.

  Instance HasASPs: HasASP System :=
    { hasASP(k:string)(s:System)(a:ASP) :=
      match s with
      | env e => hasASP k e a
      | union s1 s2 => (hasASP k s1 a) \/ (hasASP k s2 a)
      end
    }.

  End ClassExp.
   *)
  


End ManifestTerm.
