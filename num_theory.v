Require Export ZArith.
Require Export Znumtheory.
Require Import Classical.
Require Import Arith.

Theorem euclids_first_theorem :
  forall p : Z, prime p ->
  forall a b : Z, rel_prime a b ->
  (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intros p p_prime.
  intros a b a_b_coprime.
  intros p_divs_ab.

  destruct (classic (p|a)) as [IH | IH].
  - auto.
  - right.
    specialize (Gauss p a b) as Gpab.
    apply (Gpab p_divs_ab (prime_rel_prime p p_prime a IH)).
Qed.

Fixpoint zprod_n (n : nat) (f : nat -> Z) :=
  match n with
  | O => f O
  | S i => Z.mul (zprod_n i f) (f i)
  end.

Inductive prime_images (f : nat -> Z) : Prop :=
  prime_images_intro :
    forall n : nat, prime (f n) -> prime_images f.

Lemma fta_existence :
  forall x : Z, x > 1 ->
  exists (n : nat) (f : nat -> Z), prime_images f ->
  x = zprod_n n f.
Proof.
  intros x x_gt_1.

  induction x.
  - discriminate.
  - assert nat as m. apply O.
    exists m.
    induction p.
    destruct IHp.
    exact x_gt_1.
