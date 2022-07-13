Require Import Reals.
Open Scope R_scope.

Lemma Rmult_pos_pos_pos :
  forall x y:R, x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
  intros x y x_pos y_pos.
  replace 0 with (0*y); auto with real.
  now apply Rmult_ge_compat_r.
Qed.

Lemma Rmult_neg_pos_neg :
  forall x y:R, x <= 0 -> y >= 0 -> x * y <= 0.
Proof.
  intros.
  replace 0 with (0 * y); auto with real.
Qed.

Lemma Rmult_neg_neg_pos :
  forall x y:R, x <= 0 -> y <= 0 -> x * y >= 0.
Proof.
  intros x y x_neg y_neg.
  replace 0 with (y * 0); auto with real.
  rewrite Rmult_comm.
  now apply Rmult_le_ge_compat_neg_l.
Qed.

Lemma Rsub_add_cancel :
  forall x y:R, x - y + y = x.
Proof.
  intros; lra.
Qed.
