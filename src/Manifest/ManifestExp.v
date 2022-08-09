Require Import Lia.
Require Import Relations.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Export String.

(** Stuff to do:
 * - Decidability of executable.  Might not work
 * - Model finder migration from Chlipala
 * - Flesh out INI and Manifest types
 *)

Module Manifest.

  Definition Plc: Set := string.
  Definition N_ID: Set := nat.
  Definition Event_ID: Set := nat.
  Definition ASP_ID: Set := string.
  Definition TARG_ID: Set := string.
  Definition Arg: Set := string.

  (** Some places to play with *)

  Notation Rely := "Rely"%string.
  Notation Target := "Target"%string.
  Notation Appraise := "Appraise"%string.

  Notation plc_dec := string_dec.
  
  (** The structure of evidence. *)

  Inductive ASP_PARAMS: Set :=
  | asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

  Inductive Evidence: Set :=
  | mt: Evidence
  | nn: N_ID -> Evidence
  | gg: Plc -> ASP_PARAMS -> Evidence -> Evidence
  | hh: Plc -> ASP_PARAMS -> Evidence -> Evidence
  | ss: Evidence -> Evidence -> Evidence.
  Theorem Evidence_dec : forall a1 a2 : Evidence, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

  Inductive SP: Set :=
  | ALL
  | NONE.
  Theorem SP_dec : forall a1 a2 : SP, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

  Inductive FWD: Set :=
  | COMP
  | EXTD.
  Theorem FWD_dec : forall a1 a2 : FWD, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

  Inductive ASP: Set :=
  | NULL: ASP
  | CPY: ASP
  | ASPC: SP -> FWD -> ASP_PARAMS -> ASP
  | SIG: ASP
  | HSH: ASP.
  Theorem ASP_dec : forall a1 a2 : ASP, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

  (* A couple of examples for use later *)
  
  Notation aspc0 :=
    (ASPC ALL EXTD (asp_paramsC "asp0"%string ["x"%string;"y"%string] Target Target)).
  Notation aspc1 :=
    (ASPC ALL EXTD (asp_paramsC "asp1"%string ["x"%string;"y"%string] Target Target)).

  Definition Split: Set := (SP * SP).
  
  Inductive Term: Set :=
  | asp: ASP -> Term
  | att: Plc -> Term -> Term
  | lseq: Term -> Term -> Term
  | bseq: Split -> Term -> Term -> Term
  | bpar: Split -> Term -> Term -> Term.
  Theorem Term_dec : forall a1 a2 : Term, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

  Inductive ASPID := aspID : nat -> ASPID.
  Theorem aspID_dec : forall a1 a2 : ASPID, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

  Inductive EVIDENCE := evidence : nat -> EVIDENCE.
  Theorem evidence_dec : forall a1 a2 : EVIDENCE, {a1=a2}+{~a1=a2}.
  Proof. repeat decide equality. Defined.

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
      ; add : nat
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

  (** Access an [ASP] [a] from manifest [k] in manifest map [e0]
   *)
  Definition hasASP(k:string)(e0:Environment)(a:ASP):Prop :=
    match (e0 k) with
    | None => False
    | Some m => In a m.(asps)
    end.

  (** Decidability of ASP presence should be true.  Hold for later
  Theorem hasASP_dec: forall k e0 a, {hasASP k e0 a}+{~hasASP k e0 a}.
   *)
  
  Example ex1: hasASP Rely e3 aspc1.
  Proof. unfold hasASP. simpl. left. reflexivity. Qed.

  Example ex2: hasASP Rely e3 CPY -> False.
  Proof. unfold hasASP. simpl. intros. destruct H. inversion H. assumption. Qed.

  (** Determine if manifest [k] from [e0] knows how to coeunicate from [k]
   * to [p]
   *)
  Definition knowsOf(k:string)(e0:Environment)(p:Plc):Prop :=
    match (e0 k) with
    | None => False
    | Some m => In p m.(M)
    end.

  Example ex3: knowsOf Rely e3 Target.
  Proof.
    unfold knowsOf. simpl. left. reflexivity.
  Qed.
  
  Example ex4: knowsOf Rely e3 Appraise -> False.
  Proof.
    unfold knowsOf. simpl. intros. destruct H. inversion H. assumption.
  Qed.

  (** Is term [t] exectuable on the system described by manifest [k] in
   * manfiest map [e]?  Are the resources available?
   *)
  Fixpoint executable(t:Term)(k:string)(e:Environment):Prop :=
    match t with
    | asp a  => hasASP k e a
    | att p t => knowsOf k e p /\ executable t p e
    | lseq t1 t2 => executable t1 k e /\ executable t2 k e
    | bseq _ t1 t2 => executable t1 k e /\ executable t2 k e
    | bpar _ t1 t2 => executable t1 k e /\ executable t2 k e
    end.

  (** Proof tactic for proving [executable] given the above definition
   *)
  Ltac print_goal := match goal with |- ?A => idtac A end.

  Ltac prove_exec :=
    simpl; auto; match goal with
                 | |- hasASP _ _ _ => cbv; left; reflexivity
                 | |- knowsOf _ _ _ => unfold knowsOf; simpl; left; reflexivity
                 | |- _ /\ _ => split; prove_exec
                 | |- ?A => idtac A
                 end.

  Example ex5: (executable (asp SIG) Target e3).
  Proof. prove_exec. Qed.
  
  Example ex6: (executable (asp CPY) Target e3) -> False.
  Proof.
    intros Hcontra.
    simpl in *.
    cbv in *.
    destruct Hcontra.
    discriminate. assumption.
  Qed.

  Example ex7: (executable (lseq (asp SIG) (asp SIG)) Target e3).
  Proof. prove_exec. Qed.

  Example ex8: (executable (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely e3).
  Proof. prove_exec. Qed.

  (* Experiments with classes. Nothing here.  Move along...*)
  Class Executable T P E :=
    { exec : T -> P -> E -> Prop }.

  #[local]
  Instance manExec: Executable Term string Environment :=
    {| exec := executable
    |}.

  Compute manExec.(exec) (asp NULL) Rely e3.

  (** Moving on to reasoning about system M *)
  
  Definition R(e:Environment)(k1 k2:string):Prop :=
    match (e k1) with
    | Some m => In k2 m.(M)
    | None => False
    end.

  Example ex9: (R e3 Rely Target).
  Proof. cbv. auto. Qed.

  Example ex10: (R e3 Rely Appraise) -> False.
  Proof.
    prove_exec.
    intros HContra.
    cbv in *.
    destruct HContra.
    * inversion H.
    * assumption.
  Qed.

  (** Traces through [M]
   *)
  
  Inductive trc {A} (R: A -> A -> Prop) : A -> A -> Prop :=
  | TrcRefl : forall x, trc R x x
  | TrcFront : forall x y z,
    R x y
    -> trc R y z
    -> trc R x z.

  Lemma ex11: (trc (R e3) Rely Rely).
  Proof.
    constructor.
  Qed.

  (** [Measure] relation from [Rely] to [Appraise] *)
  Lemma ex12: (trc (R e3) Rely Appraise).
  Proof.
    eapply TrcFront. constructor. reflexivity.
    eapply TrcFront. constructor. reflexivity.
    constructor.
  Qed.

  Lemma zez:0=0. reflexivity. Qed.
  
  Definition eq_nat_dec : forall n m : nat, {n=m} + {n<>m}.
  refine (fix f (n m:nat) : {n=m} + {n<>m} :=
            match n,m with
              | O, O => (left _ zez)
              | S n', S m' => (if (f n' m') then (left _ _) else (right _ _))
              | i,j => (right _ _)
            end).
    lia.
    lia.
    rewrite e. reflexivity.
    injection. intros. lia.
  Defined.

  Check left.

  Theorem In_dec: forall l (a:string), {In a l}+{~In a l}.
  Proof.
    intros l a.
    induction l.
    * right. simpl. unfold not. auto.
    * inversion IHl.
      left. simpl. right. assumption.
      right.
      unfold not in *. simpl.
      intros. apply H.
      destruct H0.
      
  Abort.
  
  Theorem hasASP_dec: forall k m a, {hasASP k m a}+{~hasASP k m a}.
    intros k m a.
    induction a.
    Check In.
  Abort.

  (*
  refine (fix f (k:string)(m:Environment)(a:ASP) : {hasASP k m a}+{~hasASP k m a} :=
              match (m k) with
              | Some m0 => if (In a m0.(asps)) then True else False
              | None => (right _ _)
              end).
  
  Definition exec_dec: forall t k m, {executable t k m}+{~executable t k m}.
    refine (fix f (t:Term)(k:string)(m:Environment) : {executable t k m}+{~executable t k m} :=
              match t with
              | asp a => if (hasASP k m a) then (left _ _) else (right _ _)
              | att p t => (left _ _)
              | _ => (right _ _)
              end).
   *)
      
End Manifest.
