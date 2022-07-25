(* This was our first attempt at capturing Privacy Policy. In this example, we try to prove that Hash satifies the privacy policy. I would  mostly ignore this file (6.27.22)   *)

Set Implicit Arguments.

Module PosetPrivacy.
  
  Definition place : Type := nat.

  (* [term] type. Includes hashing, signing, sequential and parallel evidence. *)
  Inductive term : Type :=
  | THash : term
  | TNonce : term
  | TSig : term -> place -> term
  | TSeq : term -> term -> term
  | TPar : term -> term -> term.

  (* The [PrivacyPolicy] is indexed on term. Each term either satisfies the 
     Privacy Policy or it doesn't. *)

  (* If we want to protect the fact that THash satisfies the privacy 
     policy, then we would use the first constructor. I'm not sure if
     we need to be able to protect THash satisfies the privacy policy.
     It's all on the target's side, and I'm not sure the target cares
     to have that information private? 

     Anyways, I can't get the PP_Hash proof with the first constructor. *)
  Inductive PrivacyPolicy : term -> Prop :=
  | PPHash : forall t, PrivacyPolicy t -> PrivacyPolicy (THash)
  | PPHash' : PrivacyPolicy THash. 

  Check PPHash. 
  Check PrivacyPolicy THash. 

  Lemma PP_Hash: forall t, t = THash -> PrivacyPolicy t.  
  Proof.
    intros. Print PPHash.
  Abort. 
  
  
  (* Try to prove that Hash satisfies the privacy policy *)
  Lemma PP_Hash': forall t, t = THash -> PrivacyPolicy t.  
  Proof.
    intros. rewrite H.  
    apply PPHash'.
  Qed. 

  Lemma PP_not_Hash : forall t, PrivacyPolicy t -> t<> THash -> False. 
  Proof. 
    intros. destruct H. destruct H0.
    - reflexivity.
    -  destruct H0. reflexivity.
  Qed.

  Lemma neqTHash : forall t, t <> THash -> False. 
  Proof. 
    intros.
  Abort.
  
  Print PrivacyPolicy. 
  (* There isn't a case for all other things in the PrivacyPolicy defintion. 
     In the pred*)
  
  (* This takes in a term and check that the privacy policy is satisfied 
     and then produces the term *)
  Definition PrivPol_strong (t: term) : t = THash -> term :=
    match t with
    | THash => fun _ => THash
    | _ => fun _ => TNonce 
    end. 
