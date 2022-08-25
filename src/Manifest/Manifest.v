Require Import Lia.
Require Import Relations.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Import String.
Require Import Cop.Copland.
Import Copland.Term.

(** Stuff to do:
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

  (** [Environment] is a set of AM's each defined by a [Manifest].
   * The domain of an [Environment] provides names for each [Manifest].
   * Names should be the hash of their public key, but this restriction
   * is not enforced here. 
   *)

  Definition Environment : Type :=  Plc -> (option Manifest).

  Definition e_empty : Environment := (fun _ => None).
  
  Definition e_update (m : Environment) (x : Plc) (v : (option Manifest)) :=
    fun x' => if plc_dec x x' then v else m x'.

  Lemma e_apply_empty: forall x, @e_empty x = None.
  Proof.
    intros.
    auto.
  Qed.

  Lemma e_update_eq : forall (m: Environment) x v,
      (e_update m x v) x = v.
  Proof.
    intros. unfold e_update.
    case (plc_dec x x).
    * intro H. reflexivity.
    * intro H. contradiction.
  Qed.

  Theorem e_update_neq : forall v x1 x2 (m:Environment),
      x1 <> x2 -> (e_update m x1 v) x2 = m x2.
  Proof.
    intros v x1 x2 m.
    intros H.
    unfold e_update.
    case (plc_dec x1 x2); intros H1; [contradiction | reflexivity].
  Qed.

  Theorem e_update_shadow : forall (m:Environment) v1 v2 x,
      e_update (e_update m x v1) x v2
      = e_update m x v2.
  Proof.
    intros m v1 v2 x.
    unfold e_update.
    apply functional_extensionality.
    intros x0.
    case (plc_dec x x0).
    * intros H; reflexivity.
    * intros H; reflexivity.
  Qed.
  
  Theorem e_update_same : forall x (m : Environment),
      e_update m x (m x) = m.
  Proof.
    intros x m.
    unfold e_update.
    apply functional_extensionality.
    intros x0.
    case (plc_dec x x0).
    * intros H; subst; reflexivity.
    * intros H; reflexivity.
  Qed.

  Theorem e_update_permute : forall v1 v2 x1 x2 (m : Environment),
      x2 <> x1 ->
      (e_update (e_update m x2 v2) x1 v1)
      = (e_update (e_update m x1 v1) x2 v2).
  Proof.
    intros v1 v2 x1 x2 m.
    intros H.
    unfold e_update.
    apply functional_extensionality.
    intros x.
    case (plc_dec x1 x).
    * intros H1. subst.
      ** case (plc_dec x2 x); intros; contradiction || reflexivity.
    * intros H1. subst.
      ** case (plc_dec x2 x); intros; reflexivity.
  Qed.

  (** Definition of environments for use in examples and proofs.  Note they
   * build constructively through [e3] that is the map for this system
   *)
  Definition e0 := e_empty.
  Definition e1 :=
    e_update e0 Rely (Some {| asps := [aspc1]; M:= [Target] |}).
  Definition e2 :=
    e_update e1 Target (Some {| asps := [SIG]; M:= [Appraise] |}).
  Definition e3 :=
    e_update e2 Appraise (Some {| asps := [HSH] ; M:= [] |}).
  
  Inductive System : Type :=
  | env : Environment -> System
  | union : System -> System -> System.
  
  Definition hasASPe(k:string)(e:Environment)(a:ASP):Prop :=
    match (e k) with
    | None => False
    | Some m => In a m.(asps)
    end.      

  Fixpoint hasASPs(k:string)(s:System)(a:ASP):Prop :=
    match s with
    | env e => (hasASPe k e a)
    | union s1 s2 => (hasASPs k s1 a) \/ (hasASPs k s2 a)
    end.

  Theorem hasASP_dec: forall k e a, {hasASPe k e a}+{~hasASPe k e a}.
  Proof.
    intros k e a.
    unfold hasASPe.
    destruct (e k).
    * induction (asps m).
      right. unfold not. intros. inversion H.
      case (ASP_dec a a0).
      intros H. subst. left. simpl. auto.
      intros H. unfold not in H. destruct IHl. left. simpl. auto.
      right. unfold not. intros. unfold not in n. simpl in H0.
      destruct H0. apply H. subst. auto. apply n. assumption.
    * cbv. right. intros. assumption.
  Defined.

  Theorem hasASPs_dec: forall k e a, {hasASPs k e a}+{~hasASPs k e a}.
  Proof.
    intros k e a.
    induction e.
    + simpl in *. apply hasASP_dec.
    + simpl in *.  inversion IHe1; inversion IHe2.
    ++ left. left. apply H.
    ++ left. left. apply H.
    ++ left. right. apply H0.
    ++ right. unfold not in *. intros. inversion H1. congruence. congruence.
  Defined.
  
  Example ex1: hasASPe Rely e3 aspc1.
  Proof. unfold hasASPe. simpl. left. reflexivity. Qed.

  Example ex2: hasASPe Rely e3 CPY -> False.
  Proof. unfold hasASPe. simpl. intros. destruct H. inversion H. assumption. Qed.
  
  Example ex5: hasASPs Rely (env e3) aspc1.
  Proof. unfold hasASPs. unfold hasASPe. simpl. left. reflexivity. Qed.

  Example ex6: hasASPs Rely (union (env e3) (env e2)) aspc1.
  Proof. unfold hasASPs. left. unfold hasASPe. simpl. left. reflexivity. Qed.

  
  (** Determine if manifest [k] from [e] knows how to communicate from [k]
   * to [p]
   *)
  Definition knowsOfe(k:string)(e:Environment)(p:Plc):Prop :=
    match (e k) with
    | None => False
    | Some m => In p m.(M)
    end.

  Theorem knowsOfe_dec:forall k e p, {(knowsOfe k e p)}+{~(knowsOfe k e p)}.
  Proof.
    intros k e p.
    unfold knowsOfe.
    destruct (e k).
    induction (M m).
    right. simpl. unfold not. intros. assumption.
    case (string_dec p a).
    intros. subst. left. simpl. auto.
    intros H. unfold not in H. destruct IHl. left. simpl. auto.
    right. unfold not. intros. unfold not in n. simpl in H0.
    destruct H0. apply H. subst. auto. apply n. assumption.
    auto.
  Qed.
    
  Fixpoint knowsOfs(k:string)(s:System)(p:Plc):Prop :=
    match s with
    | env e => (knowsOfe k e p)
    | union s1 s2 => (knowsOfs k s1 p) \/ (knowsOfs k s2 p)
    end.

    Theorem knowsOfs_dec:forall k s p, {(knowsOfs k s p)}+{~(knowsOfs k s p)}.
    Proof.
      intros k s p.
      induction s; simpl in *.
      + apply knowsOfe_dec.
      + inversion IHs1; inversion IHs2.
      ++ left. left. apply H. 
      ++ left. left. apply H.
      ++ left. right. apply H0.
      ++ right. unfold not in *. intros. inversion H1; congruence.
    Qed.        

  Example ex3: knowsOfe Rely e3 Target.
  Proof.
    unfold knowsOfe. simpl. auto.
  Qed.
  
  Example ex4: knowsOfe Rely e3 Appraise -> False.
  Proof.
    unfold knowsOfe. simpl. intros. destruct H. inversion H. assumption.
  Qed.

  Example ex7: knowsOfs Rely (env e3) Target.
  Proof.
    unfold knowsOfs,knowsOfe. simpl. auto.
  Qed.

  Example ex8: knowsOfs Rely (union (env e3) (env e2)) Target.
  Proof.
    unfold knowsOfs,knowsOfe. simpl. auto.
  Qed.
  
  (** Is term [t] exectuable on the attestation manager named [k] in
   * environment [e]?  Are ASPs available at the right attesation managers
   * and are necessary communications allowed?
   *)
  Fixpoint executable(t:Term)(k:string)(e:Environment):Prop :=
    match t with
    | asp a  => hasASPe k e a
    | att p t => knowsOfe k e p -> executable t p e
    | lseq t1 t2 => executable t1 k e /\ executable t2 k e
    | bseq _ t1 t2 => executable t1 k e /\ executable t2 k e
    | bpar _ t1 t2 => executable t1 k e /\ executable t2 k e
    end.

  Theorem executable_dec:forall t k e,{(executable t k e)}+{~(executable t k e)}.
    intros.  generalize k. induction t; intros.
    + unfold executable. apply hasASP_dec.
    + simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H. destruct (IHt p).
      ++ left. intros. assumption.
      ++ right. unfold not. intros. unfold not in n. apply n. apply H. assumption.
      ++ simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H.
         +++ contradiction.
         +++ left. intros. congruence. 
    + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
      right. unfold not. intros. destruct H. contradiction.
      right. unfold not. intros H. destruct H. contradiction.
    + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
      right. unfold not. intros. destruct H. contradiction.
      right. unfold not. intros H. destruct H. contradiction.
    + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
      right. unfold not. intros. destruct H. contradiction.
      right. unfold not. intros H. destruct H. contradiction.
  Defined.

  (** Is term [t] executable on the attestation mnanager named [k] in
   * system [s]?  Are ASPs available at the right attestation managers
   * and are necessary communications allowed?
   *)
  Fixpoint executables(t:Term)(k:string)(s:System):Prop :=
    match t with
    | asp a  => hasASPs k s a
    | att p t => knowsOfs k s p -> executables t p s
    | lseq t1 t2 => executables t1 k s /\ executables t2 k s
    | bseq _ t1 t2 => executables t1 k s /\ executables t2 k s
    | bpar _ t1 t2 => executables t1 k s /\ executables t2 k s
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

  Example ex9: (executable (asp SIG) Target e3).
  Proof. prove_exec. Qed.
  
  Example ex10: (executable (asp CPY) Target e3) -> False.
  Proof.
    intros Hcontra.
    simpl in *.
    cbv in *.
    destruct Hcontra.
    discriminate. assumption.
  Qed.

  Example ex11: (executable (lseq (asp SIG) (asp SIG)) Target e3).
  Proof. prove_exec. Qed.

  Example ex12: (executable (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely e3).
  Proof. prove_exec. intros. split. 
    cbv in *. left. reflexivity. 
    cbv in *. left. reflexivity.   Qed.

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
                  Rely (union (env e3) (env e2))).
  Proof. prove_execs. simpl. intros. split.
    +  unfold hasASPe. cbv; left; left; reflexivity.
    + unfold hasASPe. cbv. left. left. reflexivity. 
  Qed.

  Check executables. 

  Theorem executables_dec : forall t gm k, {executables t gm k} + {~executables t gm k}.
Proof.
  intros.  generalize k. induction t; intros.
  + unfold executables. apply hasASPs_dec.
  + simpl. assert (H:{knowsOfs gm k0 p}+{~knowsOfs gm k0 p}). apply knowsOfs_dec. destruct H. destruct (IHt p).
    ++ left. intros. assumption.
    ++ right. unfold not. intros. unfold not in n. apply n. apply H. assumption.
    ++ simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H.
       +++ contradiction.
       +++ left. intros. congruence. 
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
    right. unfold not. intros. destruct H. contradiction.
    right. unfold not. intros H. destruct H. contradiction.
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
    right. unfold not. intros. destruct H. contradiction.
    right. unfold not. intros H. destruct H. contradiction.
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
    right. unfold not. intros. destruct H. contradiction.
    right. unfold not. intros H. destruct H. contradiction.
Defined.


  (** Moving on to reasoning about system M *)
  
  Definition R(e:Environment)(k1 k2:string):Prop :=
    match (e k1) with
    | Some m => In k2 m.(M)
    | None => False
    end.

  Example ex14: (R e3 Rely Target).
  Proof. cbv. auto. Qed.

  Example ex15: (R e3 Rely Appraise) -> False.
  Proof.
    prove_exec.
    intros HContra.
    cbv in *.
    destruct HContra.
    * inversion H.
    * assumption.
  Qed.
  
  Fixpoint Rs(s:System)(k1 k2:string):Prop :=
    match s with
    | env e => R e k1 k2
    | union s1 s2 => Rs s1 k1 k2 \/ Rs s2 k1 k2
    end.

  Example ex16: (Rs (env e3) Rely Target).
  Proof.
    unfold Rs. apply ex14.
  Qed.

  Example ex17: (Rs (union (env e3) (env e2)) Rely Target).
  Proof.
    unfold Rs. left. apply ex14.
  Qed.

  (** Traces through [M]
   *)
  
  Inductive trc {A} (R: A -> A -> Prop) : A -> A -> Prop :=
  | TrcRefl : forall x, trc R x x
  | TrcFront : forall x y z,
    R x y
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
    eapply TrcFront. constructor. reflexivity.
    eapply TrcFront. constructor. reflexivity.
    constructor.
  Qed.

  Inductive trcs {A} (Rs: A -> A -> Prop) : A -> A -> Prop :=
  | TrcRefls : forall x, trcs Rs x x
  | TrcFronts : forall x y z,
    Rs x y
    -> trcs Rs y z
    -> trcs Rs x z.

  Lemma ex20: (trcs (Rs (union (env e3) (env e2))) Rely Appraise).
  Proof.
    eapply TrcFronts. constructor. unfold Rs. constructor. reflexivity.
    eapply TrcFronts. constructor. unfold Rs. constructor. reflexivity.
    eapply TrcRefls. 
  Qed.


  (* Experiments with classes. Nothing here.  Move along...*)
  Module ManifestClass.

  Class Executable T P E :=
    { exec : T -> P -> E -> Prop }.

  #[local]
  Instance manExec: Executable Term string Environment :=
    { exec := executable
    }.

  Compute manExec.(exec) (asp NULL) Rely e3.

  #[local]
  Instance sysExec: Executable Term string System :=
    { exec := executables
    }.
  End ManifestClass.

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
