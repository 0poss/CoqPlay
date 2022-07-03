Require Import Reals.
Open Scope R_scope.

Definition ev (E : Set) (K : Set) :=
  exists (kop : K -> K -> K) (eop : E -> E -> E) (scal_op : K -> E -> E) (ee : E) (ek : K) (onek : K),
  (forall x y z : K,
    kop x y = kop y x /\
    kop x (kop y z) = kop (kop x y) z) /\
  (forall u : E, scal_op ek u = ee) /\
  (forall u : E, exists u' : E, eop u u' = ee) /\
  (forall x : K, forall u v : E,
    scal_op x (eop u v) = eop (scal_op x u) (scal_op x v)) /\
  (forall x y : K, forall u : E,
    scal_op (kop x y) u = eop (scal_op x u) (scal_op y u)) /\
  (forall u : E, scal_op onek u = u).

Definition R2 : Set := (R * R).
Definition R2plus (u : R2) (v : R2) : R2 :=
  (fst u + fst v, snd u + snd v).
Definition R2scal (a : R) (u : R2) : R2 :=
  (a * fst u, a * snd u).

Theorem R2_ev :
  ev R2 R.
Proof.
  unfold ev.
  exists Rplus, R2plus, R2scal, (0, 0), 0, 1.
  repeat split; unfold R2plus, R2scal; simpl.

  - apply Rplus_comm.
  - symmetry. apply Rplus_assoc.
  - intros.
    now rewrite_all Rmult_0_l.
  - intros.
    exists (-fst u, -snd u).
    now rewrite_all Rplus_opp_r.
  - intros.
    now rewrite_all Rmult_plus_distr_l.
  - intros.
    now rewrite_all Rmult_plus_distr_r.
  - intros.
    rewrite_all Rmult_1_l.
    now rewrite <- surjective_pairing.
Qed.
