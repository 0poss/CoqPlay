Require Import Reals.
Require Import Reals.ROrderedType.
Require Import Logic.Classical.
Require Import micromega.Lra.
Require Import micromega.Lia.
Load Base.
Open Scope R_scope.

Theorem Rabs_mult_distr :
  forall x y:R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  (* Very dirty proof. *)
  intros.
  destruct (classic (x >= 0 /\ y >= 0)).
  - destruct H as [x_pos y_pos].
    rewrite_all Rabs_right; auto.
    now apply Rmult_pos_pos_pos.
  - unfold Rge in H.
    apply not_and_or in H.
    destruct H as [neg | neg];
      apply not_or_and in neg;
      destruct neg as [neg neq_0];
      apply Rnot_gt_le in neg;
      apply (ROrder.le_neq_lt neg) in neq_0 as sneg.
    destruct (classic (y >= 0)) as [y_pos | y_sneg].
    + rewrite (Rabs_right y); auto.
      rewrite (Rabs_left1 x); auto.
      rewrite <- Ropp_mult_distr_l.
      rewrite (Rabs_left1 (x*y) (Rmult_neg_pos_neg x y neg y_pos)).
      reflexivity.
    + apply Rnot_ge_lt in y_sneg.
      apply Rlt_le in y_sneg as y_neg.
      rewrite (Rabs_left1 x neg).
      rewrite (Rabs_left1 y y_neg).
      assert (xy_pos:x * y >= 0).
      now apply Rmult_neg_neg_pos.
      rewrite (Rabs_right (x*y) xy_pos).
      rewrite Rmult_opp_opp.
      reflexivity.
    + destruct (classic (x >= 0)) as [x_pos | x_sneg].
      * rewrite (Rabs_right x); auto.
        rewrite (Rabs_left1 y); auto.
        rewrite Rmult_comm with (r2 := -y).
        rewrite Rmult_comm.
        rewrite <- Ropp_mult_distr_l.
        rewrite (Rabs_left1 (y*x) (Rmult_neg_pos_neg y x neg x_pos)).
        reflexivity.
      * apply Rnot_ge_lt in x_sneg.
        apply Rlt_le in x_sneg as x_neg.
        rewrite (Rabs_left1 x x_neg).
        rewrite (Rabs_left1 y neg).
        assert (xy_pos:x * y >= 0).
        now apply Rmult_neg_neg_pos.
        rewrite (Rabs_right (x*y) xy_pos).
        rewrite Rmult_opp_opp.
        reflexivity.
Qed.

Lemma Rabs_x_eq_0_iff_x_eq_0 :
  forall x:R, Rabs x = 0 <-> x = 0.
Proof.
  intros.
  destruct (Rcase_abs x) as [x_sneg | x_pos];
      [rewrite (Rabs_left _ x_sneg); lra |
          rewrite (Rabs_right _ x_pos); tauto ].
Qed.

Theorem Rabs_triangle :
  forall x y:R, Rabs (x + y) <= Rabs x + Rabs y.
Proof.
  intros.

  (* Getting 2xy <= 2|x||y|. *)
  pose proof (Rabs_mult_distr x y) as He.
  apply ROrder.le_eq with (x := x*y) in He;
    [| apply (Rle_abs (x*y))].
  apply (Rmult_le_compat_l 2) in He; auto with real.

  (* Getting |x+y|² <= x² + y² + 2|x||y|. *)
  pose proof (Rsqr_abs (x+y)) as He0.
  rewrite Rsqr_plus in He0.
  symmetry in He0.
  apply ROrder.eq_le with (z := x²+y²+2*Rabs x*Rabs y) in He0;
    [| lra].

  rewrite (Rsqr_abs x) in He0.
  rewrite (Rsqr_abs y) in He0.
  rewrite <- Rsqr_plus in He0.
  apply sqrt_le_1_alt in He0.
  replace (sqrt (Rabs (x + y))²) with (Rabs (x + y)) in He0;
    [| symmetry; apply sqrt_Rsqr; apply Rabs_pos].
  replace (sqrt (Rabs x + Rabs y)²) with (Rabs x + Rabs y) in He0;
    [| symmetry; apply sqrt_Rsqr; apply Rplus_le_le_0_compat; apply Rabs_pos ].

  assumption.
Qed.

Lemma Rle_opp_le_abs_le:
  forall x y:R, x <= y -> -x <= y -> Rabs x <= y.
Proof.
  intros.
  destruct (Rcase_abs x);
    [now rewrite Rabs_left | now rewrite Rabs_right].
Qed.

Theorem Rabs_triangle_opp :
  forall x y:R, Rabs (Rabs x - Rabs y) <= Rabs (x - y).
Proof.
  intros.

  (* Getting |x| - |y| <= |x - y|. *)
  pose proof (Rabs_triangle (x-y) y) as Hxy_le.
  rewrite Rsub_add_cancel in Hxy_le.
  apply (Rplus_le_compat_r (- Rabs y)) in Hxy_le.
  replace (Rabs (x - y) + Rabs y + - Rabs y) with (Rabs (x - y)) in Hxy_le;
    [| lra].
  replace (Rabs x + - Rabs y) with (Rabs x - Rabs y) in Hxy_le;
    [| lra].

  (* Getting -(|x| - |y|) <= |x - y|. *)
  pose proof (Rabs_triangle (y-x) x) as Hyx_le.
  rewrite Rsub_add_cancel in Hyx_le.
  apply (Rplus_le_compat_r (- Rabs x)) in Hyx_le.
  replace (Rabs (y - x) + Rabs x + - Rabs x) with (Rabs (y - x)) in Hyx_le;
    [| lra].
  rewrite Rabs_minus_sym in Hyx_le.
  replace (Rabs y + - Rabs x) with (Rabs y - Rabs x) in Hyx_le;
    [| lra].
  rewrite <- Ropp_minus_distr in Hyx_le.

  now apply Rle_opp_le_abs_le.
Qed.
