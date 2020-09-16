Set Implicit Arguments.

Module DepCopland.

  Definition place : Type := nat.
  
  (* [evidence] type. Should be expanded to include others, but this is okay 
     for now. Hashes, signed things, sequential evidence. *)
  Inductive evidence : Type :=
  | EHash : evidence
  | ESig : evidence -> place -> evidence
  | ESeq : evidence -> evidence -> evidence
  | EPar : evidence -> evidence -> evidence.

  (* [term] type indexed on evidence produced. Each term type captures theorem
     type of evidence resulting from execution. [evidence -> Type] *)
  Inductive term : evidence -> Type :=
  | TMeas : term EHash
  | THash : forall e, term e -> term EHash
  | TSig : forall e p, term e -> term (ESig e p)
  | TSeq : forall e f, term e -> term f -> term (ESeq e f)
  | TPar : forall e f, term e -> term f -> term (EPar e f).

  (* Each of these types captures the kind of thing evaluting results in. 
     Note that THash obfuscates results by one-way encryption which is
     exactly what we want. *)  
  Check TMeas.
  Check (TSeq (TSig 1 TMeas) (TPar TMeas (TPar TMeas TMeas))).
  Check (TSeq (TSig 1 TMeas) (THash (TPar TMeas (TPar TMeas TMeas)))).
  Check THash TMeas.
  Check THash (TSig 2 TMeas).
  Check (TSig 2 TMeas).

  (* A function that checks signatures.  Basically, if the signed thing is
     signed by the provided place, the check is true. *)
  Definition checkSig (t:evidence)(p q:place)(e: term (ESig t p)) : Prop :=
    p = q.

  (* This will not typecheck.  Trying to check the signature of a thing
     that is not signed. Note this is caught in _typechecking_ *)
  
  (* Example e0: checkSig 1 (THash TMeas). *)
  
  Example e1: checkSig 1 (TSig 1 TMeas).
  Proof.
    unfold checkSig.
    congruence.
  Qed.
    
  Example e2: checkSig 2 (TSig 1 TMeas) -> False.
  Proof.
    unfold checkSig.
    intros.
    inversion H.
  Qed.
  
End DepCopland.
