Require Import Lia.
Require Import Relations.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Import String.
Require Import Cop.Copland.
Import Copland.Term.
Require Import Utils.Utilities.

(** Stuff to do:
 * - Model finder migration from Chlipala
 * - Flesh out INI and Manifest types
 *)

Module ManifestTerm.

  (* Objects can be deduced from ASP *)

  Notation Rely := "Rely"%string.
  Notation Target := "Target"%string.
  Notation Appraise := "Appraise"%string.

  Notation aspc0 :=
    (ASPC ALL EXTD (asp_paramsC "asp0"%string ["x"%string;"y"%string] Target Target)).
  Notation aspc1 :=
    (ASPC ALL EXTD (asp_paramsC "asp1"%string ["x"%string;"y"%string] Target Target)).
  Notation aspc2 :=
    (ASPC ALL EXTD (asp_paramsC "asp2"%string ["vc"%string] Target Target)).

  (** [Manifest] defines an attestation manger a list of ASPs and other
   * managers it is aware of.  [Manifest] defines a single AM and its
   * interconnections.  [add] simulates address information and [tpm]
   * simulates cruft necessary to initialize its TPM.
   *)
  Record Manifest := {

      asps : list ASP ;
      M : list Plc ; 
      C : list Plc ; 
      Policy : ASP -> Plc -> Prop ;

(*
      ; key : string
      ; address : nat
      ; tpm_init : nat
*)

(* TO DO: Add privacy and selection policies to manifest *)
    }.

   Check Policy.

(* Policy describes privacy constraints applies to measurement operations. 

  Below are relational definitions of Policy. Within the definition, we list each ASP the AM has and state who can recieve a measurement of said ASP. The relying party can share the measurement of aspc1 with p. The target can share the measurement aspc2 with the appraiser and SIG with anyone. The appraiser can share a hash with anyone. 
*)

  Inductive rely_Policy : ASP -> Plc -> Prop := 
  | p_aspc1 : forall p, rely_Policy aspc1 p. 

  Inductive tar_Policy : ASP -> Plc -> Prop := 
  | p_aspc0 : tar_Policy aspc2 Appraise 
  | p_SIG : forall p, tar_Policy SIG p. 

  Inductive app_Policy : ASP -> Plc -> Prop := 
  | p_HSH : forall p, app_Policy HSH p. 

  (** [Environment] is a set of AM's each defined by a [Manifest].
   * The domain of an [Environment] provides names for each [Manifest].
   * Names should be the hash of their public key, but this restriction
   * is not enforced here. 
   *)

  Definition Environment : Type :=  Plc -> (option Manifest).

  Definition e_empty : Environment := (fun _ => None).
  
  Definition e_update (m : Environment) (x : Plc) (v : (option Manifest)) :=
    fun x' => if plc_dec x x' then v else m x'.

  (** Definition of environments for use in examples and proofs.  Note there are 3 AM's present... Relying Party, Target, and Appraiser, each have an AM. 
   *)
  Definition e0 := e_empty.
  Definition e_Rely :=
    e_update e_empty Rely (Some {| asps := [aspc1]; M:= [Target] ; C := [] ; Policy := rely_Policy |}).
  Definition e_Targ :=
    e_update e_empty Target (Some {| asps := [SIG;  aspc2]; M:= [Appraise] ; C := [] ; Policy := tar_Policy|}).
  Definition e_App :=
    e_update e_empty Appraise (Some {| asps := [HSH] ; M:= [] ; C := [Target] ; Policy := app_Policy |}).
  
  (* A System is all attestation managers in the enviornement *)
  Definition System := list Environment.

  (* Inductive System : Type :=
  | env : Environment -> System
  | union : System -> System -> System.

  Local Hint Constructors System : core. *)
  
  (* Definition of system using environements defined above. *)

  Definition example_sys_1 := [e_Rely; e_Targ; e_App]. 
  
  Definition hasASPe(k:Plc)(e:Environment)(a:ASP):Prop :=
    match (e k) with
    | None => False
    | Some m => In a m.(asps)
    end.      
    
    Fixpoint hasASPs(k:Plc)(s:System)(a:ASP):Prop :=
      match s with
      | [] => False
      | s1 :: s2 => (hasASPe k s1 a) \/ (hasASPs k s2 a)
      end.
      
    Example ex1: hasASPe Rely e_Rely aspc1.
    Proof. unfold hasASPe. simpl. left. reflexivity. Qed.
  
    Example ex2: hasASPe Rely e_App CPY -> False.
    Proof. unfold hasASPe. simpl. intros. inverts H. Qed.
    
    Example ex5: hasASPs Rely (example_sys_1) aspc1.
    Proof. unfold hasASPs. unfold hasASPe. simpl. left. left. reflexivity. Qed.
  
    (* I'm not quite sure what this is trying to say... 
     * This is currently false but I'm not sure if you want it to be true... *)
    Example ex6: hasASPs Appraise (example_sys_1) aspc1.
    Proof. unfold hasASPs. unfold hasASPe. simpl. Abort. 

  Theorem hasASPe_dec: forall k e a, {hasASPe k e a}+{~hasASPe k e a}.
  Proof.
    intros k e a.
    unfold hasASPe.
    destruct (e k).
    * induction (asps m).
      right. unfold not. intros. inverts H.
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
    + simpl in *. right. unfold not. intros. apply H.
    + simpl in *. pose proof hasASPe_dec k a0 a. inverts H. 
    ++ left. left. apply H0.
    ++ inverts IHe.
    +++ left. right. apply H.
    +++ right. unfold not. intros. inverts H1; auto.
  Qed.             

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
  
  (** Determine if manifest [k] from [e] knows how to communicate from [k]
   * to [p]
   *)
  Definition knowsOfe(k:Plc)(e:Environment)(p:Plc):Prop :=
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
  
  Fixpoint knowsOfs(k:Plc)(s:System)(p:Plc):Prop :=
    match s with
    | [] => False
    | s1 :: ss => (knowsOfe k s1 p) \/ (knowsOfs k ss p)
    end.

    Theorem knowsOfs_dec:forall k s p, {(knowsOfs k s p)}+{~(knowsOfs k s p)}.
    Proof.
      intros k s p.
      induction s; simpl in *.
      + right. unfold not. intros. inversion H.     
      + pose proof knowsOfe_dec k a p. inverts H.
      ++ left. left. apply H0.
      ++ inverts IHs.
      +++ left. right. apply H.
      +++ right. unfold not. intros. inversion H1; auto.
    Qed. 

  Example ex3: knowsOfs Rely example_sys_1 Target.
  Proof.
    unfold knowsOfs. simpl. left. unfold knowsOfe. simpl.  auto.
  Qed.
  
  Example ex4: knowsOfe Rely e_App Appraise -> False.
  Proof.
    unfold knowsOfe. simpl. intros. destruct H. 
  Qed.

  Example ex7: knowsOfs Rely example_sys_1 Target.
  Proof.
    unfold knowsOfs,knowsOfe. simpl. auto.
  Qed.

  Example ex8: knowsOfs Rely [e_Rely] Target.
  Proof.
    unfold knowsOfs,knowsOfe. simpl. auto.
  Qed.

  Definition dependsOne (k:Plc)(e:Environment)(p:Plc):Prop :=
    match (e k) with
    | None => False
    | Some m => In p m.(C)
    end.

  Fixpoint dependsOns (k:Plc)(s:System)(p:Plc):Prop :=
    match s with
    | [] => False
    | s1 :: ss => (dependsOne k s1 p) \/ (dependsOns k ss p)
    end.

  (* the appriser depends on target *)
  Example ex81 : dependsOne Appraise e_App Target.
  Proof.
    unfold dependsOne. simpl. auto.
  Qed.   

  (* within the system, we see that the appraiser depends on target *)
  Example ex82 : dependsOns Appraise example_sys_1 Target.
  Proof. 
    unfold dependsOns. simpl. unfold dependsOne. simpl. auto.
  Qed.   

  Theorem dependsOne_dec : forall k e p, {(dependsOne k e p)}+{~(dependsOne k e p)}.
  Proof.
    intros k e p.
    unfold dependsOne.
    destruct (e k).
    +  induction (C m).
    ++ auto.
    ++ simpl. inversion IHl.
    +++  auto.
    +++ assert (H': {a = p } + { a <> p}). {repeat decide equality. } inversion H'.
    ++++ left. left. apply H0.
    ++++ right. unfold not. intros. inversion H1; auto.
    + auto.
  Qed.       

  Theorem dependsOns_dec : forall k s p, {dependsOns k s p} + {~ dependsOns k s p}.
  Proof.
    intros. induction s. 
    + simpl. auto.
    + simpl. pose proof dependsOne_dec k a p. inversion IHs.
    ++ left. right. apply H0. 
    ++ inversion H.
    +++ left. left. apply H1.
    +++ right. unfold not. intros. inversion H2; auto.
  Qed.            
    
  (** Is term [t] exectuable on the attestation manager named [k] in
   * environment [e]?  Are ASPs available at the right attesation managers
   * and are necessary communications allowed?
   *)
  Fixpoint executable(t:Term)(k:Plc)(e:Environment):Prop :=
    match t with
    | asp a  => hasASPe k e a
    | att p t => knowsOfe k e p -> executable t p e
    | lseq t1 t2 => executable t1 k e /\ executable t2 k e
    | bseq _ t1 t2 => executable t1 k e /\ executable t2 k e
    | bpar _ t1 t2 => executable t1 k e /\ executable t2 k e
    end.

  Theorem executable_dec:forall t k e,{(executable t k e)}+{~(executable t k e)}.
    intros.  generalize k. induction t; intros.
    + unfold executable. apply hasASPe_dec.
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
  Fixpoint executables(t:Term)(k:Plc)(s:System):Prop :=
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

  (* Is asp SIG executable on the on target place in the Targets's enviornement?*)
  Example ex9: (executable (asp SIG) Target e_Targ).
  Proof. prove_exec. Qed.
  
  Example ex10: (executable (asp CPY) Target e_App) -> False.
  Proof.
    intros Hcontra.
    simpl in *.
    cbv in *.
    destruct Hcontra.
  Qed.

  Example ex11: (executable (lseq (asp SIG) (asp SIG)) Target e_Targ).
  Proof. prove_exec. Qed.

  Example ex12: (executable (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely e_App).
  Proof. prove_exec. intros. Abort. (* split. 
    cbv in *. left. reflexivity. 
    cbv in *. left. reflexivity.   Qed. *)

  Example ex12': (executables (lseq (asp aspc1)
                              (att Target
                                 (lseq (asp SIG)
                                    (asp SIG))))
                  Rely example_sys_1).
  Proof. prove_exec. intros. simpl. unfold hasASPe. simpl.
    left. left. reflexivity.   
    cbv in *. split. right.  left. left.  reflexivity. 
    cbv in *. right. left.  left. reflexivity.   Qed.

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


  (* Example ex13: (executables (lseq (asp aspc1)
                                (att Target
                                   (lseq (asp SIG)
                                      (asp SIG))))
                  Rely (union (env e_App) (env e_Targ))).
  Proof. prove_execs. simpl. intros. split.
    +  unfold hasASPe. cbv; left; left; reflexivity.
    + unfold hasASPe. cbv. left. left. reflexivity. 
  Qed. *)

  Check executables.

  (** Is term [t] executable on the attestation mnanager named [k] in
   * system [s]?  Are ASPs available at the right attestation managers
   * and are necessary communications allowed?
   *)

  Theorem executables_dec : forall t k s, {executables t k s} + {~executables t k s}.
    Proof.
    intros.  generalize k s. induction t; intros.
    + unfold executables. apply hasASPs_dec.
    + simpl. assert (H:{knowsOfs k0 s0 p}+{~knowsOfs k0 s0 p}). apply knowsOfs_dec. destruct (IHt p s0).
      ++ left. intros. assumption.
      ++ destruct H.
      +++ right. unfold not. intros. apply n. apply H. assumption.
      +++ left. intros. congruence. 
    + simpl. specialize IHt1 with k0 s0. specialize IHt2 with k0 s0. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
      right. unfold not. intros. destruct H. contradiction.
      right. unfold not. intros H. destruct H. contradiction.
    + simpl. specialize IHt1 with k0 s1. specialize IHt2 with k0 s1. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
      right. unfold not. intros. destruct H. contradiction.
      right. unfold not. intros H. destruct H. contradiction.
    + simpl. specialize IHt1 with k0 s1. specialize IHt2 with k0 s1. destruct IHt1,IHt2. left. split ; assumption. right. unfold not. intros H. destruct H. contradiction.
      right. unfold not. intros. destruct H. contradiction.
      right. unfold not. intros H. destruct H. contradiction.
    Defined.


  (** Moving on to reasoning about system M *)
  
  Definition R(e:Environment)(k1 k2:Plc):Prop :=
    match (e k1) with
    | Some m => In k2 m.(M)
    | None => False
    end.

  Example ex14: (R e_Rely Rely Target).
  Proof. cbv. auto. Qed.

  Example ex15: (R e_Rely Rely Appraise) -> False.
  Proof.
    prove_exec.
    intros HContra.
    cbv in *.
    destruct HContra.
    * inversion H.
    * assumption.
  Qed.
  
  Fixpoint Rs(s:System)(k1 k2:Plc):Prop :=
    match s with
    | env e => R e k1 k2
    | union s1 s2 => Rs s1 k1 k2 \/ Rs s2 k1 k2
    end.

  Example ex16: (Rs (env e_App) Rely Target).
  Proof.
    unfold Rs. apply ex14.
  Qed.

  Example ex17: (Rs (union (env e_App) (env e_Targ)) Rely Target).
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

  Local Hint Constructors trc : base.
  
  Lemma ex18: (trc (R e_App) Rely Rely).
  Proof.
    auto with base.
  Qed.

  (** [Measure] relation from [Rely] to [Appraise]
   *)
  Lemma ex19: (trc (R e_App) Rely Appraise).
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

  Local Hint Constructors trcs : base.

  Lemma ex20: (trcs (Rs (union (env e_App) (env e_Targ))) Rely Appraise).
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

  Compute manExec.(exec) (asp NULL) Rely e_App.

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
