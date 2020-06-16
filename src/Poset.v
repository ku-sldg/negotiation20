Require Import Omega.

(**
 Define a partially ordered set type.  Parameters are the set
 and the ordering relation.  Axioms define properties of a partial ordering.
 Note that Axioms are axioms only in the [Poset] module.  When we instantiate
 the [Poset] module we are responsible for proving the "axioms" over the
 specific actual parameter values.  Thus, [Axiom] in this context is really
 Assumption *)

Module Type Poset.
  Parameter t : Type.
  Parameter eq : t -> t -> Prop.

  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40). 
  
  Axiom eq_refl : forall x, x == x.
  Axiom eq_sym : forall x y, x == y -> y == x.
  Axiom eq_trans : forall x y z,  x == y -> y == z -> x == z.

  Parameter order : t -> t -> Prop.
  
  Notation " t1 '<<=' t2 " := (order t1 t2) (at level 40).
  
  Axiom order_refl : forall x y, x == y -> x <<= y.
  Axiom order_antisym: forall x y, x <<= y -> y <<= x -> x == y.
  Axiom order_trans : forall x y z, x <<= y -> y <<= z ->  x <<= z.
End Poset.

(** Show that [nat] and [<=] together define a partially ordered set.  All
  [Paramter] declarations from [Poset] have [Defintion]s in [Posetnat].
  All [Axiom] declarations from [Poset] have [Theorem]s in [Posetnat]. *)

Module PosetNat <: Poset.
  Definition t : Type := nat.
  Definition eq : t -> t -> Prop := (fun t1 t2 => t1 = t2).

  Hint Unfold eq.
  
  Notation " t1 '==' t2 " := (eq t1 t2) (at level 40).

  Theorem eq_refl : forall x, x == x.
  Proof. reflexivity. Qed.
    
  Theorem eq_sym : forall x y, x == y -> y == x.
  Proof. intros x y. intros H. auto. Qed.
    
  Theorem eq_trans : forall x y z,  x == y -> y == z -> x == z.
  Proof. intros x y z. intros H1 H2. unfold eq in *. subst. reflexivity. Qed.

  Definition order : t -> t -> Prop := (fun x y => x <= y).

  Notation " t1 '<<=' t2 " := (order t1 t2) (at level 40).

  Hint Unfold order.
  
  Theorem order_refl : forall x y, x == y -> x <<= y.
  Proof.
    intros x y.
    intros H.
    unfold eq in *.
    unfold order in *.
    omega.
  Qed.
    
  Theorem order_antisym: forall x y, x <<= y -> y <<= x -> x == y.
  Proof.
    intros x y. intros H1 H2.
    unfold eq in *. unfold order in *.
    apply Nat.le_antisymm; assumption.
  Qed.

  Theorem order_trans : forall x y z, x <<= y -> y <<= z ->  x <<= z.
  Proof.
    intros x y z. intros H1 H2.
    unfold order in *.
    eapply Nat.le_trans. apply H1. apply H2.
  Qed.

End PosetNat.
