(* Let S be an ensemble. 
   Let S be the set {1,2,3}*)

Require Import Ensembles.

Definition sing3 := Singleton _ 3.
Definition S := (Add _ (Add _ ( Singleton _ 1 ) 2) 3).

Theorem In_S_3 : In _ S 3.
Proof.
  unfold In. unfold S.
  unfold Add. apply Union_intror.
  apply In_singleton.
Qed. 
