Require Import Relations.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Export String.

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

  (** INI is a list of ASPs and likely more later.
   *)
  Record INI :=
    { asps : list ASP }.
  
  Check {| asps := [NULL] |}.

  (** Manifest is an INI and M defining know communication.
   *)
  Record Manifest := {ini:INI; M:list string}.
  
  (** Manifest Map [mm] is a mapping from an AM keys to their manifest.
   * remember the hash of the public key is an AM's identifier.
   *)
  Definition mm : Type :=  string -> Manifest.

  (** Empty Manifest Map
   *)
  Definition mm_empty (v : Manifest) := (fun _:string => v).

  Definition mm_update (m : mm) (x : string) (v : Manifest) :=
    fun x' => if string_dec x x' then v else m x'.

  Lemma mm_apply_empty: forall x v, @mm_empty v x = v.
  Proof.
    intros.
    auto.
  Qed.

  Lemma mm_update_eq : forall (m: mm) x v,
      (mm_update m x v) x = v.
  Proof.
    intros. unfold mm_update.
    case (string_dec x x).
    * intro H. reflexivity.
    * intro H. contradiction.
  Qed.

  Theorem mm_update_neq : forall v x1 x2 (m:mm),
      x1 <> x2 -> (mm_update m x1 v) x2 = m x2.
  Proof.
    intros v x1 x2 m.
    intros H.
    unfold mm_update.
    case (string_dec x1 x2); intros H1; [contradiction | reflexivity].
  Qed.

  Theorem mm_update_shadow : forall (m:mm) v1 v2 x,
      mm_update (mm_update m x v1) x v2
      = mm_update m x v2.
  Proof.
    intros m v1 v2 x.
    unfold mm_update.
    apply functional_extensionality.
    intros x0.
    case (string_dec x x0).
    * intros H; reflexivity.
    * intros H; reflexivity.
  Qed.
  
  Theorem mm_update_same : forall x (m : mm),
      mm_update m x (m x) = m.
  Proof.
    intros x m.
    unfold mm_update.
    apply functional_extensionality.
    intros x0.
    case (string_dec x x0).
    * intros H. subst. reflexivity.
    * intros H. reflexivity.
  Qed.

  Theorem mm_update_permute : forall v1 v2 x1 x2 (m : mm),
      x2 <> x1 ->
      (mm_update (mm_update m x2 v2) x1 v1)
      = (mm_update (mm_update m x1 v1) x2 v2).
  Proof.
    intros v1 v2 x1 x2 m.
    intros H.
    unfold mm_update.
    apply functional_extensionality.
    intros x.
    case (string_dec x1 x).
    * intros H1. subst.
      ** case (string_dec x2 x); intros; contradiction || reflexivity.
    * intros H1. subst.
      ** case (string_dec x2 x); intros; reflexivity.
  Qed.

  Definition pmm : Type :=  string -> (option Manifest).

  Definition pmm_empty : pmm := (fun _ => None).

  Definition pmm_update (m : pmm) (x : string) (v : (option Manifest)) :=
    fun x' => if string_dec x x' then v else m x'.

  Lemma pmm_apply_empty: forall x, @pmm_empty x = None.
  Proof.
    intros.
    auto.
  Qed.

  Lemma pmm_update_eq : forall (m: pmm) x v,
      (pmm_update m x v) x = v.
  Proof.
    intros. unfold pmm_update.
    case (string_dec x x).
    * intro H. reflexivity.
    * intro H. contradiction.
  Qed.

  Theorem pmm_update_neq : forall v x1 x2 (m:pmm),
      x1 <> x2 -> (pmm_update m x1 v) x2 = m x2.
  Proof.
    intros v x1 x2 m.
    intros H.
    unfold pmm_update.
    case (string_dec x1 x2); intros H1; [contradiction | reflexivity].
  Qed.

  Theorem pmm_update_shadow : forall (m:pmm) v1 v2 x,
      pmm_update (pmm_update m x v1) x v2
      = pmm_update m x v2.
  Proof.
    intros m v1 v2 x.
    unfold pmm_update.
    apply functional_extensionality.
    intros x0.
    case (string_dec x x0).
    * intros H; reflexivity.
    * intros H; reflexivity.
  Qed.
  
  Theorem pmm_update_same : forall x (m : pmm),
      pmm_update m x (m x) = m.
  Proof.
    intros x m.
    unfold pmm_update.
    apply functional_extensionality.
    intros x0.
    case (string_dec x x0).
    * intros H; subst; reflexivity.
    * intros H; reflexivity.
  Qed.

  Theorem pmm_update_permute : forall v1 v2 x1 x2 (m : pmm),
      x2 <> x1 ->
      (pmm_update (pmm_update m x2 v2) x1 v1)
      = (pmm_update (pmm_update m x1 v1) x2 v2).
  Proof.
    intros v1 v2 x1 x2 m.
    intros H.
    unfold pmm_update.
    apply functional_extensionality.
    intros x.
    case (string_dec x1 x).
    * intros H1. subst.
      ** case (string_dec x2 x); intros; contradiction || reflexivity.
    * intros H1. subst.
      ** case (string_dec x2 x); intros; reflexivity.
  Qed.

  (** System is an INI, comm links, list of dependent systems.
   *
   *  THIS CONSTRUCT IS NOT CURRENTLY USED
   *)
  Record System :=
    { s_AM : pmm;             (* Who is involved *)
      s_M : relation string;     (* Who talks to who from mm *)
      s_C : list string }.       (* Who depends on who from mm *)

  (** Relations defining [M] for [Rely], [Target], and [Appraise]. 
   *)
  Definition M_Rely: list string := [Target].
  Definition M_Target: list string := [Appraise].
  Definition M_Appraise: list string := [].

  (** Relations defining [M] for the entire system.  Not currently used. 
   *)
  Inductive M_System: relation string :=
  | SRelyTarget: M_System Rely Target
  | STargetAppraise: M_System Target Appraise.
  
  (** Some example ASPs for use in proofs
   *)
  Definition asp0 := aspc0.
  Definition asp1 := aspc1.
  Definition asp2 := SIG.
  Definition asp3 := HSH.

  (** Definition of manifest maps for use in examples and proofs.  Note they
   * build constructively through [mm3] that is the map for this system
   *)
  Definition mm0 := pmm_empty.
  Definition mm1 :=
    pmm_update mm0 Rely (Some {| ini := {| asps := [asp1] |}; M:= M_Rely |}).
  Definition mm2 :=
    pmm_update mm1 Target (Some {| ini := {| asps := [asp2] |}; M:= M_Target |}).
  Definition mm3 :=
    pmm_update mm2 Appraise (Some {| ini := {| asps := [asp3] |}; M:= M_Appraise|}).

  (** Access an [ASP] [a] from manifest [k] in manifest map [mm0]
   *)
  Definition hasASP(k:string)(mm0:pmm)(a:ASP):Prop :=
    match (mm0 k) with
    | None => False
    | Some m => In a m.(ini).(asps)
    end.

  (** Decidability of ASP presence should be true.  Hold for later
  Theorem hasASP_dec: forall k mm0 a, {hasASP k mm0 a}+{~hasASP k mm0 a}.
   *)
  
  Example ex1: hasASP Rely mm3 asp1.
  Proof. unfold hasASP. simpl. left. reflexivity. Qed.

  Example ex2: hasASP Rely mm3 CPY -> False.
  Proof. unfold hasASP. simpl. intros. destruct H. inversion H. assumption. Qed.

  (** Determine if manifest [k] from [mm0] knows how to communicate from [k]
   * to [p]
   *)
  Definition knowsOf(k:string)(mm0:pmm)(p:Plc):Prop :=
    match (mm0 k) with
    | None => False
    | Some m => In p m.(M)
    end.

  Example ex3: knowsOf Rely mm3 Target.
  Proof.
    unfold knowsOf. simpl. left. reflexivity.
  Qed.
  
  Example ex4: knowsOf Rely mm3 Appraise -> False.
  Proof.
    unfold knowsOf. simpl. intros. destruct H. inversion H. assumption.
  Qed.

  (** Is term [t] exectuable on the system described by manifest [k] in
   * manfiest map [mm]?  Are the resources available?
   *)
  Fixpoint executable(t:Term)(k:string)(mm:pmm):Prop :=
    match t with
    | asp a  => hasASP k mm a
    | att p t => knowsOf k mm p /\ executable t p mm
    | lseq t1 t2 => executable t1 k mm /\ executable t2 k mm
    | bseq _ t1 t2 => executable t1 k mm /\ executable t2 k mm
    | bpar _ t1 t2 => executable t1 k mm /\ executable t2 k mm
    end.

  (** Proof tactic for proving [executable] given the above definition
   *)
  Ltac prove_exec :=
    simpl; auto; match goal with
                 | |- hasASP _ _ _ => cbv; left; reflexivity
                 | |- knowsOf _ _ _ => unfold knowsOf; simpl; left; reflexivity
                 | |- _ /\ _ => split; prove_exec
                 | |- _ => idtac
                 end.

  Definition executable_dec: forall t k mm, {executable t k mm}+{~executable t k mm}.
  Proof.
    intros t k mm.
    induction t.
    unfold executable.
  Abort.
  
  Example ex5: (executable (asp asp2) Target mm3).
  Proof. prove_exec. Qed.
  
  Example ex6: (executable (asp CPY) Target mm3) -> False.
  Proof.
    intros Hcontra.
    simpl in *.
    cbv in *.
    destruct Hcontra.
    discriminate. assumption.
  Qed.

  Example ex7: (executable (lseq (asp asp2) (asp asp2)) Target mm3).
  Proof. prove_exec. Qed.

  Example ex8: (executable (lseq (asp asp1)
                              (att Target
                                 (lseq (asp asp2)
                                    (asp asp2))))
                  Rely mm3).
  Proof. prove_exec. Qed.

  Class Executable T P E :=
    { exec : T -> P -> E -> Prop }.

  Instance manExec: Executable Term string pmm :=
    {| exec := executable
    |}.

  Compute manExec.(exec) (asp NULL) Rely mm3.

  (** Moving on to M *)
  
  Definition R(mm:pmm)(k1 k2:string):Prop :=
    match (mm k1) with
    | Some m => In k2 m.(M)
    | None => False
    end.

  Example ex9: (R mm3 Rely Target).
  Proof. cbv. left. reflexivity. Qed.

  Example ex10: (R mm3 Rely Appraise) -> False.
  Proof. intros HContra. cbv in *. destruct HContra. inversion H. assumption. Qed.
  
  Inductive trc {A} (R: A -> A -> Prop) : A -> A -> Prop :=
  | TrcRefl : forall x, trc R x x
  | TrcFront : forall x y z,
    R x y
    -> trc R y z
    -> trc R x z.

  Lemma ex11: (trc (R mm3) Rely Rely).
  Proof.
    constructor.
  Qed.

  Lemma ex12: (trc (R mm3) Rely Appraise).
  Proof.
    eapply TrcFront.
    assert ((R mm3) Rely Target). constructor. reflexivity. apply H.
    eapply TrcFront.
    assert ((R mm3) Target Appraise). constructor. reflexivity. apply H.
    eapply TrcRefl.
  Qed.
    
End Manifest.
