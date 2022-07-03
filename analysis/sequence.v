Require Import Reals.
Require Import Logic.Classical.
Require Import micromega.Lra.
Require Import micromega.Lia.
Open Scope R_scope.

Theorem a_le_all_0 :
  forall a:R, (forall e:R, e > 0 -> Rabs a <= e) -> a = 0.
Proof.
  intros a H.
  destruct (classic (a = 0)) as [a_eq_0 | a_neq_0].

  - trivial.
  - apply (Rabs_pos_lt a) in a_neq_0 as Rabs_a_spos.
    pose (e := Rabs a / 2).
    cut (Rabs a <= e).

    * intro absurd_ineq.
      cbv [e] in absurd_ineq.
      apply (Rmult_le_compat_r (/(Rabs a))) in absurd_ineq; [| lra].
      unfold Rdiv in absurd_ineq.
      rewrite (Rinv_r (Rabs a) (Rabs_no_R0 a a_neq_0)) in absurd_ineq.
      rewrite (Rinv_r_simpl_m (Rabs a) (/2) (Rabs_no_R0 a a_neq_0)) in absurd_ineq.
      lra.
    * specialize (H e).
      apply Rlt_gt in Rabs_a_spos.
      apply Rgt_ge in Rabs_a_spos as Rabs_a_pos.
      cbv [e] in *.
      lra.
Qed.


