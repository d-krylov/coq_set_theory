Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Powerset_facts.

Section Lemma_1_18.

Variable U : Type.

Variable (A B C : Ensemble U).

Theorem Union_increases_l: forall (U : Type) (a b : Ensemble U),
  Included U a (Union U a b).
Proof.
  unfold Included. intros. unfold In.
  apply Union_introl. apply H.
Qed.

Theorem Union_minimal: forall (U : Type) (a b X : Ensemble U),
  Included U a X -> Included U b X -> Included U (Union U a b) X.
Proof.
  unfold Included. intros. destruct H1.
  - apply H. apply H1.
  - apply H0. apply H1.
Qed.

(* This is the same as Union_commutative *)
Lemma i_a: Union U A B = Union U B A.
Proof.
  simple apply Extensionality_Ensembles.
  unfold Same_set. split.
  - simple apply Union_minimal.
    + simple apply Union_increases_r.
    + simple apply Union_increases_l.
  - simple apply Union_minimal.
    + simple apply Union_increases_r.
    + simple apply Union_increases_l.
Qed.

(* This is the same as Intersection_commutative *)
Lemma i_b : Intersection U A B = Intersection U B A.
Proof.
  simple apply Extensionality_Ensembles.
  unfold Same_set. split.
  - unfold Included. intros. destruct H.
    apply Intersection_intro. apply H0. apply H.
  - unfold Included. intros. destruct H.
    apply Intersection_intro. apply H0. apply H.
Qed.

(* This is the same as Union_associative *)
Lemma ii_a: Union U A (Union U B C) = Union U (Union U A B) C.
Proof.
  simple apply Extensionality_Ensembles.
  unfold Same_set. split.
  - unfold Included. intros.
    destruct H.
    + apply Union_introl. apply Union_introl. apply H.
    + destruct H. 
      * apply Union_introl. apply Union_intror. apply H.
      * apply Union_intror. apply H.
  - unfold Included. intros. destruct H.
    + destruct H.
      * apply Union_introl. apply H.
      * apply Union_intror. apply Union_introl. apply H.
    + apply Union_intror. apply Union_intror. apply H.
Qed.
 
(* This is the same as Intersection_associative *)
Lemma ii_b : Intersection U A (Intersection U B C) = Intersection U (Intersection U A B) C.
Proof.
  simple apply Extensionality_Ensembles.
  unfold Same_set.
  split.
  - unfold Included. intros.
    unfold In. unfold In in H. destruct H.
    * repeat apply Intersection_intro. destruct H0.
      apply H. destruct H0. apply H0. 
      destruct H0. apply H1.
  - unfold Included. intros.
    repeat apply Intersection_intro. destruct H.
    destruct H. apply H. destruct H. destruct H. apply H1.
    destruct H. apply H0.
Qed.
 
(* This is the same as Distributivity *)
Lemma iii_a :
    Intersection U A (Union U B C) =
    Union U (Intersection U A B) (Intersection U A C).
Proof.
  admit.
Qed.
 
(* This is the same as Distributivity' *)
Lemma iii_b :
    Union U A (Intersection U B C) =
    Intersection U (Union U A B) (Union U A C).
Proof.
  admit.
Qed.
 
(* Using intuitionistic logic, it is possible to prove that
   (A intersection B) is a subset of (A \ (A \ B)), but proving the converse
   requires classical logic. *)
Lemma iv_constructive :
    Included U (Intersection U A B) (Setminus U A (Setminus U A B)).
Proof.
  admit.
Qed.
 
(* Either add this one classical axiom only to this section *)
Hypothesis NNPP : forall p:Prop, ~ ~ p -> p.
(* or uncomment the following line to import all of Classical_Prop for this
   whole module *)
(* Require Import Coq.Logic.Classical_Prop. *)
Lemma iv : Setminus U A (Setminus U A B) = Intersection U A B.
Proof.
  admit.
Qed.
 
End Lemma_1_18.
 
Section Lemma_1_19.
 
Variable X : Type.
 
Variable (A B : Ensemble X).
 
(* This half is provable using intuitionistic logic *)
Lemma a_constructive :
    Included X (Union X (Complement X A) (Complement X B))
    (Complement X (Intersection X A B)).
Proof.
  admit.
Qed.
 
Hypothesis NNPP : forall p:Prop, ~ ~ p -> p.
 
Lemma a :
    Complement X (Intersection X A B) =
    Union X (Complement X A) (Complement X B).
Proof.
  admit.
Qed.
 
(* This half is provable using intuitionistic logic *)
Lemma b_constructive :
    Included X (Intersection X (Complement X A) (Complement X B))
    (Complement X (Union X A B)).
Proof.
  admit.
Qed. 
 
Lemma b :
    Complement X (Union X A B) = 
    Intersection X (Complement X A) (Complement X B).
Proof.
  admit.
Qed.
  
