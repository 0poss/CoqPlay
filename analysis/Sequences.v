Require Import Reals.
Require Import Logic.Classical.
Require Import micromega.Lra.
Require Import micromega.Lia.
Load Abs.
Open Scope R_scope.

Theorem Rle_forall_gt_0_eq_0 :
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

Definition RSequence_converges (u:nat -> R) (l:R) : Prop :=
  forall e:R, e > 0 -> exists N:nat, forall n:nat, (n >= N)%nat ->
    Rabs (u n - l) <= e.

Theorem RSequence_lim_unicity :
  forall Un:(nat -> R), exists l:R, RSequence_converges Un l ->
  exists l':R, RSequence_converges Un l' ->
  l = l'.
Proof.
  intros.
  unfold RSequence_converges.

  pose proof 0 as l.
  pose proof 0 as l'.
  exists l.
  intro l_lim.
  exists l'.
  intro l'_lim.
  assert (exists e:R, e > 0) by (exists 1; auto with real).
  destruct H as [e e_gt_0].
  destruct l_lim with (e := e) as [N fa_n_ge_N_Rabs_Unn_l_le_e];
    [assumption|].
  destruct l'_lim with (e := e) as [N' fa_n_ge_N'_Rabs_Unn_l'_le_e];
    [assumption|].

  (* Getting e/2 > 0. *)
  (* assert (e/2 > 0) as half_e_gt_0 by lra.*)

  pose (n0 := Nat.max N N').
  assert ((n0 >= N)%nat) as n0_ge_N;
    assert ((n0 >= N')%nat) as n0_ge_N'; cbv [n0];
    auto with arith.
  pose proof (fa_n_ge_N_Rabs_Unn_l_le_e n0 n0_ge_N) as Rabs_n0_l_le_e.
  pose proof (fa_n_ge_N'_Rabs_Unn_l'_le_e n0 n0_ge_N') as Rabs_n0_l'_le_e.

  (* Getting |l-l'| <= |Un0 - l| + |Un0 - l'|. *)
  assert (Rabs (l - l') <= Rabs (Un n0 - l) + Rabs (Un n0 - l')) as ll'_triangle.
  rewrite <- Rsub_add_cancel with (x := l) (y := Un n0) at 1.
  rewrite Rabs_minus_sym with (x := Un n0).
  replace (Rabs (l - Un n0 + Un n0 - l')) with (Rabs (l - Un n0 + (Un n0 - l'))).
  exact (Rabs_triangle (l - Un n0) (Un n0 - l')).
  unfold Rminus.
  rewrite <- Rplus_assoc.
  reflexivity.

  pose proof (Rplus_le_compat (Rabs (Un n0 - l)) (e) (Rabs (Un n0 - l')) (e)).
  pose proof (H Rabs_n0_l_le_e Rabs_n0_l'_le_e).
  clear H.
  rename H0 into HRabs_Rplus_Rabs_le_2e.
  apply (Rle_trans _ _ _ ll'_triangle) in HRabs_Rplus_Rabs_le_2e as
    Rabs_ll'_le_2e.
  
  assert (e+e > 0) as e_plus_e_gt_0 by lra.
  generalize Rle_forall_gt_0_eq_0.
  intro.
Qed.

