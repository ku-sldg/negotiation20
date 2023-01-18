Require Import Lia.
Require Import Relations.
Require Import Logic.FunctionalExtensionality.
Require Import Lists.List.
Import ListNotations.
Require Import String.
Require Import Cop.Copland.
Import Copland.Term.
Require Import Utils.Utilities.

(** TO Do:
 * - Model finder migration from Chlipala
 * - Selection policy in manifest? 
 * - Properties of privacy policy? 
 *)

Module Manifest.

  (** [Manifest] defines a single attestation manger and its interconnections.  
      Information includes: 
   * asps:  a list of ASPs (measurement operations the AM can preform)
   * M : measures relation (other AMs the current AM knows of)  
   * C : context relation (other AMs the current AM depends on)
   * Policy : local policy specific to the current AM. Minimally includes privacy policy and may possibly include selection policy   
   
   * Other information not necessary for reasoning includes: 
   * [key] simulates public key 
   * [address] simulates address information and 
   * [tpm] simulates cruft necessary to initialize its TPM
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

  
  (* A System is all attestation managers in the enviornement *)
  Definition System := list Environment.

(********************
  *   HAS APS PROOFS 
  ********************)

(* Within the enviornment e, does the AM at place k have ASP a? *)
Definition hasASPe(k:Plc)(e:Environment)(a:ASP):Prop :=
  match (e k) with
  | None => False
  | Some m => In a m.(asps)
  end.      
  
(* Within the system s, does the AM located at place k have ASP a? *)
Fixpoint hasASPs(k:Plc)(s:System)(a:ASP):Prop :=
  match s with
  | [] => False
  | s1 :: s2 => (hasASPe k s1 a) \/ (hasASPs k s2 a)
  end.

(* Proof that hasASPe is decidable *)
Theorem hasASPe_dec: forall k e a, {hasASPe k e a}+{~hasASPe k e a}.
Proof.
  intros k e a.
  unfold hasASPe.
  destruct (e k); auto.
  + induction (asps m); auto.
  ++ pose proof ASP_dec a a0; inverts H; simpl.
  +++ left. auto.
  +++ destruct IHl.
  ++++ left. auto.
  ++++ right_intro_inverts; auto.
Defined.

(* prove hasASPs is decidable *)
Theorem hasASPs_dec: forall k e a, {hasASPs k e a}+{~hasASPs k e a}.
Proof.
  intros k e a.
  induction e; simpl.
  + right. unfold not; auto.
  + pose proof hasASPe_dec k a0 a; inverts H. 
  ++ left; auto.
  ++ inverts IHe.
  +++ left; auto.
  +++ right_intro_inverts; auto.
Defined.    
  
(********************
  *  KNOWS OF PROOFS 
  ********************)

(** Determine if manifest [k] from [e] knows how to communicate from [k]
  * to [p]
  *)
Definition knowsOfe(k:Plc)(e:Environment)(p:Plc):Prop :=
  match (e k) with
  | None => False
  | Some m => In p m.(M)
  end.

(* Prove knowsOfe is decidable *)
Theorem knowsOfe_dec:forall k e p, {(knowsOfe k e p)}+{~(knowsOfe k e p)}.
Proof.
  intros k e p.
  unfold knowsOfe.
  destruct (e k); auto.
  induction (M m).
  + right; auto. 
  + pose proof (string_dec p a); inverts H. 
  ++ left. simpl. auto.
  ++ inverts IHl.
  +++ simpl. left; auto.
  +++ right_intro_inverts; auto. 
Qed.
  
(** Determine if place [k] within the system [s] knows 
  * how to communicate with [p]
  *)
Fixpoint knowsOfs(k:Plc)(s:System)(p:Plc):Prop :=
  match s with
  | [] => False
  | s1 :: ss => (knowsOfe k s1 p) \/ (knowsOfs k ss p)
  end.

(* decidability of knowsOfs*)
Theorem knowsOfs_dec:forall k s p, {(knowsOfs k s p)}+{~(knowsOfs k s p)}.
Proof.
  intros k s p.
  induction s; simpl in *.
  + right_intro_inverts.     
  + pose proof knowsOfe_dec k a p. inverts H.
  ++ left. left. apply H0.
  ++ inverts IHs.
  +++ left. right. apply H.
  +++ right_intro_inverts; auto.
Qed. 

(********************
*  DEPENDS ON PROOFS 
********************)

(** Determine if place [k] within the environment [e]  
  * depends on place [p] (the context relation)
  *)
Definition dependsOne (k:Plc)(e:Environment)(p:Plc):Prop :=
  match (e k) with
  | None => False
  | Some m => In p m.(C)
  end.

(** Determine if place [k] within the system [s]  
  * depends on place [p] (the context relation)
  *)
Fixpoint dependsOns (k:Plc)(s:System)(p:Plc):Prop :=
  match s with
  | [] => False
  | s1 :: ss => (dependsOne k s1 p) \/ (dependsOns k ss p)
  end.
Check plc_dec.

(* depends on (context relation) is decidable *)
Theorem dependsOne_dec : forall k e p, {(dependsOne k e p)}+{~(dependsOne k e p)}.
Proof with auto.
  intros k e p.
  unfold dependsOne.
  destruct (e k) ...
  + induction (C m).
  ++ auto.
  ++ simpl. inversion IHl.
  +++ auto.
  +++ pose proof plc_dec a p. inversion H0.
  ++++ left ...
  ++++ right_intro_inverts ...
Defined.        

Theorem dependsOns_dec : forall k s p, {dependsOns k s p} + {~ dependsOns k s p}.
Proof with auto.
  intros. induction s. 
  + simpl...
  + simpl. pose proof dependsOne_dec k a p. inversion IHs.
  ++ left. right. apply H0. 
  ++ inversion H.
  +++ left. left. apply H1.
  +++ right_intro_inverts... 
Defined.            
    
(********************
  *   EXECUTABLE PROOFS 
  ********************)

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

(* executability of a term is decidable *)
Theorem executable_dec:forall t k e,{(executable t k e)}+{~(executable t k e)}.
  Proof with auto.
  intros.  generalize k. induction t; intros.
  + unfold executable. apply hasASPe_dec.
  + simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H. destruct (IHt p).
  ++ left. intros. assumption.
  ++ right. unfold not. intros... 
  ++ simpl. assert (H:{knowsOfe k0 e p}+{~knowsOfe k0 e p}). apply knowsOfe_dec. destruct H...
  +++ left. intros. congruence. 
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H. 
  ++ left. split ; assumption...
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H.   
  ++ left. split ; assumption...
  + simpl. specialize IHt1 with k0. specialize IHt2 with k0. destruct IHt1,IHt2; try right_dest_contr H.   
  ++ left. split ; assumption...
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

(** Is term [t] executable on the attestation mnanager named [k] in
  * system [s]?  Are ASPs available at the right attestation managers
  * and are necessary communications allowed?
  *)

Theorem executables_dec : forall t k s, {executables t k s} + {~executables t k s}.
  Proof with auto.
  intros.  generalize k s. induction t; intros.
  + unfold executables. apply hasASPs_dec.
  + simpl. assert (H:{knowsOfs k0 s0 p}+{~knowsOfs k0 s0 p}). apply knowsOfs_dec. destruct (IHt p s0).
  ++ left. intros. assumption.
  ++ destruct H.
  +++ right. unfold not...
  +++ left. intros... congruence. 
  + simpl. specialize IHt1 with k0 s0. specialize IHt2 with k0 s0. destruct IHt1,IHt2; try right_dest_contr H.
  ++  left. split ; assumption.
  + simpl. specialize IHt1 with k0 s1. specialize IHt2 with k0 s1. destruct IHt1,IHt2; try right_dest_contr H.
  ++  left. split ; assumption. 
  + simpl. specialize IHt1 with k0 s1. specialize IHt2 with k0 s1. destruct IHt1,IHt2; try right_dest_contr H.
  ++  left. split ; assumption.
  Defined.
  
End Manifest.
