(* Proofs that the structures introduced on metric spaces coincide with
the corresponding ones from the standard library. *)
From mathcomp Require Import ssreflect ssrnat ssrbool ssrfun.
From mf Require Import all_mf.
Require Import pointwise reals pseudo_metrics pseudo_metric_spaces metrics metric_spaces.
Require Import Reals Ranalysis Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope metric_scope.
Local Open Scope R_scope.

Canonical MS2M_S (M: MetricSpace): Metric_Space.
  exists M (fun x y => d(x, y)); try exact dst_sym; try exact dst0_eq.
  - by move => x y; apply Rle_ge, dst_pos.
  by move => x y z; apply dst_trngl.
Defined.

Global Instance M_S2MS (M: Metric_Space): MetricSpace.
  exists (Base M) (fun p => dist M p.1 p.2).
  split; try exact/dist_sym; try exact/dist_refl.
  - by move => x y; apply/Rge_le/dist_pos.
  by move => z x y; apply/dist_tri.
Defined.

(* This does not use the function above to remove the necessity to rewrite /R_dist everytime. *)
Global Instance R_MetricSpace: MetricSpace.
  exists R (fun p => Rabs (p.1 - p.2)).
  split; try exact/(dist_refl R_met); try exact/(dist_sym R_met).
  - by move => x y; apply/Rge_le/(dist_pos R_met).
  by move => z x y; apply/(dist_tri R_met).
Defined.

Section R_MetricSpace.
  Lemma Uncv_lim: make_mf Un_cv =~= limit.
  Proof.
    move => xn x; split => ass eps epsg0.
    have [N Nprp]:= ass eps epsg0; exists N => n ineq.
    apply/Rlt_le; rewrite /= Rabs_minus_sym.
      by rewrite /R_dist in Nprp; apply /Nprp/leP.
    have [ | N Nprp]:= ass (eps/2); try lra; exists N => n ineq.
    rewrite /R_dist Rabs_minus_sym; apply /Rle_lt_trans; first by apply /Nprp /leP.
    lra.
  Qed.

  Implicit Types (x y z: R) (xn yn: sequence_in R).
  Lemma limD xn yn x y:
    x \is_limit_of xn -> y \is_limit_of yn ->
    (x + y) \is_limit_of (ptw_op Rplus xn yn: nat -> Base R_met).
  Proof. by rewrite <-Uncv_lim => lim lim'; apply/CV_plus. Qed.

  Lemma limB xn yn x y:
    xn ~> x -> yn ~> y -> (ptw_op Rminus xn yn) ~> (x - y).
  Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_minus. Qed.

  Lemma limM xn yn x y:
    xn ~> x -> yn ~> y -> (ptw_op Rmult xn yn) ~> (x * y).
  Proof. by rewrite -Uncv_lim => lim lim'; apply/CV_mult. Qed.
  
  Lemma lim_pos xn x: x \is_limit_of xn -> (forall n, 0 <= xn n) -> 0 <= x.
  Proof.
    move => lim prp.
    suff: -x/2 <= 0 by lra.
    apply Rnot_lt_le => ineq.
    have [N /=cnd]:= lim _ ineq.
    have := cnd N (leqnn N).
    by have:= prp N; split_Rabs; lra.
  Qed.

  Lemma lim_inc xn yn x y:
    (forall i, xn i <= yn i) -> xn ~> x -> yn ~> y -> x <= y.
  Proof.
    move => prp lim lim'.
    have ineq: forall i, 0 <= yn i - xn i by move => i; have:= prp i; lra.
    suff: 0 <= y - x by lra.
    exact/lim_pos/ineq/limB.
  Qed.

  Lemma lim_dec xn yn x y:
    (forall i, xn i >= yn i) -> xn ~> x -> yn ~> y -> x >= y.
  Proof.
    move => prp lim lim'.
    have ineq: forall i, 0 <= xn i - yn i by move => i; have:= prp i; lra.
    suff: 0 <= x - y by lra.
    exact/lim_pos/ineq/limB.
  Qed.

  Definition scale (x: R) xn := (fun n => (x * (xn n))): sequence_in R.

  Lemma scale_ptw r: scale r =1 ptw_op Rmult (cnst r).
  Proof. done. Qed.

  Lemma lim_scale r x xn: xn ~> x -> (scale r xn) ~> (r * x).
  Proof.
    move => lim.
    rewrite scale_ptw.
    by apply/limM/lim; apply lim_cnst.
  Qed.

  Lemma cchy_crit: Cauchy_sequences === make_subset Cauchy_crit.
  Proof.
    move => xn; split => cchy eps epsg0.
    - have [ | N prp]:= cchy (eps/2); first by rewrite /Rdiv; lra.
      exists N => n m /leP ineq /leP ineq'.
      by apply/Rle_lt_trans; first apply/prp => //; rewrite /Rdiv; lra.
    have [N prp]:= cchy eps epsg0.
    by exists N; intros; apply/Rlt_le/prp/leP; first apply/leP.
  Qed.

  Lemma R_cmplt: R \is_complete.
  Proof.
    move => xn /cchy_crit cchy.
    have [x /Uncv_lim lim]:= R_complete xn cchy.
    by exists x.
  Qed.

  Lemma lim_dst (M: PseudoMetricSpace) (xn: sequence_in M) (x: M):
     xn ~> x <-> (fun n => pd (x,(xn n))) \converges_to 0 \wrt (@d R_MetricSpace).
  Proof.
    split => lmt eps eg0; have [n prp]:= lmt eps eg0; exists n => m ineq.
    - rewrite {1}/d/= Rminus_0_l Rabs_Ropp Rabs_pos_eq; first exact/prp.
      by apply pseudo_metrics.dst_pos.
    suff: Rabs (0 - pd(x, xn m)) <= eps by split_Rabs; lra.
    exact/prp.
  Qed.

  Lemma cntp_limin (M M': MetricSpace) (f: M2PM M -> M2PM M') (x: M):
    f \continuous_in x <-> limit_in (MS2M_S M) (MS2M_S M') f All x (f x).
  Proof.
    split => [cont eps eg0 | lmt eps eg0].
    - have e2g0: 0 < eps/2 by lra.
      have [delta [dg0 prp]]:= cont (eps/2) e2g0.
      exists delta; split => // x' [_ dst].
      apply/Rle_lt_trans.
      + rewrite /dist /= dst_sym; apply/prp/Rlt_le.
        by rewrite dst_sym; apply/dst.
      lra.
    have [delta [dg0 prp]]:= lmt eps eg0.
    exists (delta/2); split; first lra; move => y /= dst.
    rewrite dst_sym; apply/Rlt_le.
    by apply/prp; split => //; rewrite /dist /= dst_sym; lra.
  Qed.

  Lemma cont_limin (M M': MetricSpace) (A: subset M) (f: M2PM M -> M2PM M') (x: A):
    (sub_fun f: M2PM (subspace A) -> M2PM M') \continuous_in x
    <->
    limit_in (MS2M_S M) (MS2M_S M') f A (projT1 x) (f (projT1 x)).
  Proof.
    split => [cont eps eg0 | lmt eps eg0].
    - have e2g0: 0 < eps/2 by lra.
      have [delta [dg0 /= prp]]:= cont (eps/2) e2g0.
      exists delta; rewrite /dist/=.
      split => // y [Ay dst]; apply/Rle_lt_trans.
      + rewrite dst_sym; have ->: y = sval (exist _ _ Ay) by trivial.
        by apply/prp; rewrite dst_sym; apply/Rlt_le.
      lra.
    have [delta [dg0 /=prp]]:= lmt eps eg0.
    exists (delta/2); split; first lra; move => [y Ay] /= dst.
    apply/Rlt_le; rewrite dst_sym; apply/prp.
    split => //=; rewrite dst_sym.
    by apply/Rle_lt_trans; first exact/dst; lra.
  Qed.
End R_MetricSpace.
Notation metric_R:= R_MetricSpace (only parsing).
