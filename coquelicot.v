(* Interface of PseudoMetricSpace and MetricSpace types with types from the Coqeulicot Hierarchy *)
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import pointwise reals all_metrics all_metric_spaces standard infima_suprema.
Require Import Reals Psatz.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma minus_eq (G: AbelianGroup) (x y: G): minus x y = zero <-> x = y.
Proof.
  split => [eq | -> ]; last exact/minus_eq_zero.
  rewrite -(minus_zero_r x) -(minus_eq_zero y).
  move: eq; rewrite /minus opp_plus opp_opp plus_assoc => ->.
  by rewrite plus_zero_l.
Qed.

Instance AR2MS (R: AbsRing): MetricSpace.
  exists R (fun (p: R * R) => abs (minus p.1 p.2)).
  split; first by move => x y; apply /abs_ge_0.
  - by move => x y; apply/abs_minus.
  - split => [eq | ->]; last by rewrite minus_eq_zero; apply/abs_zero.
    exact/minus_eq/abs_eq_zero.
  move => z x y.
  rewrite /minus.
  apply/Rle_trans/abs_triangle.
  suff ->: plus x (opp y) = plus (plus x (opp z)) (plus z (opp y)) by apply/Rle_refl.
  by rewrite plus_assoc -(plus_assoc x) plus_opp_l plus_zero_r.
Defined.

Coercion AR2MS: AbsRing >-> MetricSpace.

Instance NM2MS (K: AbsRing) (V: NormedModule K): MetricSpace.
  exists V (fun p: V * V => norm (minus p.1 p.2)).
  split; first by move => x y; apply/norm_ge_0.
  - by move => x y; rewrite -{1}opp_minus norm_opp.
  - split => [eq | ->]; last by rewrite minus_eq_zero norm_zero.
    exact/minus_eq/norm_eq_zero.
  move => z x y.
  rewrite /minus.
  apply/Rle_trans/norm_triangle.
  suff ->: plus x (opp y) = plus (plus x (opp z)) (plus z (opp y)) by apply/Rle_refl.
  by rewrite plus_assoc -(plus_assoc x) plus_opp_l plus_zero_r.
Defined.

Coercion NM2MS: NormedModule >-> MetricSpace.

Section PseudoMetricSpaces_and_UniformSpaces.
  Definition PMS2US_mixin (M: PseudoMetricSpace): UniformSpace.mixin_of M.
    exists (fun x r y => d(x, y) < r).
    - by move => x [eps eg0]; rewrite dstxx /=.
    - by move => x y e ineq; rewrite pseudo_metrics.dst_sym.
    move => x y z e e' ineq ineq'.
    apply/Rle_lt_trans; first exact/(pseudo_metrics.dst_trngl y).
    exact/Rplus_lt_compat.
  Defined.
  
  Canonical PMS2US (M: PseudoMetricSpace):= UniformSpace.Pack M (PMS2US_mixin M) M.

  Context (M: UniformSpace).

  Definition distance_bounds (x y: M) := make_subset (fun eps => 0 <= eps /\ ball x eps y).
  
  Lemma dbnd_bbl x y: distance_bounds x y \from lower_boundeds.
  Proof. by exists 0 => r []. Qed.
  Notation "[1,oo)":= (make_subset (fun x => 1 <= x)).
  
  Lemma dom_d x y: ((distance_bounds x y) \u [1,oo)) \from dom mf_infimum.
  Proof.
    rewrite dom_inf.
    split; first by exists 0 => z [[Az] | /= l1z]; lra.
    by exists 1; right => /=; lra.
  Qed.

  Definition d_M (x y: M):= inf ((distance_bounds x y) \u [1,oo)).

  Lemma d_inf x y: mf_infimum ((distance_bounds x y) \u [1,oo)) (d_M x y).
  Proof. exact/inf_spec/dom_d. Qed.

  Lemma d_pos x y: 0 <= d_M x y.
  Proof.
    apply/inf_geq; first exact/dom_d.
    by move => z [/=[] | /= ]; lra.
  Qed.

  Lemma d_sym x y: d_M x y = d_M y x.
  Proof.
    apply/inf_eq; first exact/dom_d.
    split => [r [[pos bll] | dst] | r lb].
    - apply/inf_leq; first exact/dom_d.
      by left; split; last apply/ball_sym.
    - apply/inf_leq; first exact/dom_d.
      by right.
    apply/inf_geq; first exact/dom_d.
    move => z [[le bll] | l1z]; apply/lb; last by right.
    by left; split => //; exact/ball_sym.
  Qed.  
  
  Lemma dxx x: d_M x x = 0.
  Proof.
    suff: 0 <= d_M x x /\ d_M x x <= 0 by lra.
    - split; first apply/inf_geq; first exact/dom_d.
      move => z [ [] | /=]; lra.
    apply/cond_leq => eps eg0; rewrite Rplus_0_l /d_M.
    apply/inf_leq; first exact/dom_d.
    left; split; try lra.
    by have := ball_center x (mkposreal _ eg0).
  Qed.

  Lemma d_leq x y: d_M x y <= 1.
  Proof.
    apply/inf_leq; first exact/dom_d.
    by right => /=; lra.
  Qed.

  Lemma d_trngl x z y: d_M x z <= d_M x y + d_M y z.
  Proof.
    apply/cond_leq => eps eg0.
    suff: d_M x z <= (d_M x y + eps/2) + (d_M y z + eps/2) by lra.
    apply/inf_leq; first exact/dom_d.
    case: (total_order_T (d_M x y + eps/2) 1); last by right => /=; have:= d_pos y z; lra.
    case => [lt | ->]; last by right => /=; have := d_pos y z; lra.
    case: (total_order_T (d_M y z + eps/2) 1); last by right => /=; have := d_pos x y; lra.
    case => [lt' | ->]; last by right => /=; have := d_pos x y; lra.
    left; split; first by have := d_pos x y; have := d_pos y z; lra.
    have eps2: 0 < eps/2 by lra.
    apply/(ball_triangle x y z).
    - have [eps' [[[pos bll] | /= ineq] ineq']]:= (inf_approx (d_inf x y) eps2).
      + exact/ball_le/bll/ineq'.
      by have := d_pos x y; lra.
    have [eps' [[[pos bll] | /= ineq] ineq']]:= (inf_approx (d_inf y z) eps2).
    - exact/ball_le/bll/ineq'.
    by have := d_pos y z; lra.
  Qed.

  Lemma dst_bll x y eps: 0 < eps -> d_M x y <= Rmin (eps/2) (1/4) -> ball x eps y.
  Proof.
    rewrite/d_M /= => eg0 dst.
    pose A:= make_subset (fun eps => 0 <= eps /\ ball x eps y) \u [eta Rle 1].
    have e4: 0 < Rmin (eps/2) (1/4) by apply/Rmin_pos; lra.
    have [x' [[[_ bll] ineq | ]]]:= @inf_approx A _ (inf_spec (dom_d x y)) _ e4.
    + apply (ball_le x x') => //; first apply/Rle_trans; first exact/ineq.
      apply/Rle_trans; first by apply/Rplus_le_compat_r/dst.
      by have := Rmin_l (eps/2) (1/4); lra.
    have := Rmin_r (eps/2) (1/4) => ineq ineq' ineq''.
    have : x' <= Rmin (eps/2) (1/4) + Rmin (eps/2) (1/4); try lra.
    by apply/Rle_trans/Rplus_le_compat_r/dst.
  Qed.

  Lemma bll_dst:
    (forall (x y: M), (forall eps, 0 < eps -> ball x eps y) -> x = y)
      -> (forall x y, d_M x y = 0 -> x = y).
  Proof.
    move => prp x y dst.
    apply/prp => eps eg0.
    apply/(dst_bll eg0).
    rewrite dst.
    by apply/Rlt_le/Rmin_pos; lra.
  Qed.
  
  Instance US2PMS: PseudoMetricSpace.
    exists M (fun p => d_M p.1 p.2); split; [exact/d_pos | exact/d_sym | exact/dxx | ].
    by move => z x y; apply/d_trngl.
  Defined.
End PseudoMetricSpaces_and_UniformSpaces.

Section Continuity.
  Local Open Scope metric_scope.
  Lemma cntp_cntp_pmtrc (M N: PseudoMetricSpace) (f: M -> N) x:
    f \continuous_in x <-> continuous (f: PMS2US M -> PMS2US N) x.
  Proof.
    split => [cont P [[eps eg0] prp]| cont eps eg0].
    - have [ | delta [dg0 aprx]]:= cont (eps/2); first by lra.
      exists (mkposreal delta dg0) => /= y bll'.
      apply/prp/Rle_lt_trans; first apply/aprx/Rlt_le/bll'.
      by rewrite /=; lra.
    have [ | [delta dg0] prp]:= cont (fun y => d (f x, y) < eps); first by exists (mkposreal eps eg0).
    exists (delta/2); split => [ | y dst]; first by lra.
    apply/Rlt_le/prp/Rle_lt_trans; first exact/dst.
    rewrite /=; lra.
  Qed.
  
  Lemma cntp_cntp_us (N M: UniformSpace) (f: N -> M) x:
    continuous f x <-> (f: US2PMS N -> US2PMS M) \continuous_in x.
  Proof.
    split => [cont eps eg0 | cont P [[eps eg0] prp]].
    - have [ | [delta dg0] dprp]:= cont (fun y => d (f x: US2PMS M, y: US2PMS M) <= eps).
      + have eg2: 0 < eps/2 by lra.
        exists (mkposreal _ eg2) => y bll.
        suff : d (f x: US2PMS M, y) <= eps/2 by simpl; lra.
        rewrite /d/=/d_M/=; apply/bnds_inf_leq.
        * by exists 0; rewrite /= => z [[] | ]; lra.
        by left; split; [lra | apply/bll].
      exists (Rmin (delta/2) (1/4)).
      split => [ | y dst]; first by apply/Rmin_pos; lra.
      by apply/dprp/dst_bll/dst => /=; lra.
    have e2: 0 < Rmin (eps/2) (1/4) by apply/Rmin_pos; lra.
    have [delta [dg0 cnd]]:= cont (Rmin (eps/2) (1/4)) e2.
    exists (mkposreal _ dg0) => y bll.    
    have : d (f x: US2PMS M, f y) <= Rmin (eps/2) (1/4).
    - apply/cnd; rewrite /d/=/d_M/=.
      apply/inf_leq; first exact/dom_d.
      by left; split; first lra.
    rewrite /d/=/d_M/= => dst.
    by apply/prp/dst_bll/dst => /=; lra.
  Qed.
End Continuity.