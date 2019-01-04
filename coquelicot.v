(* Interface of MetricSpace type with types from the Coqeulicot Hierarchy *)
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import pointwise reals metric.
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

Definition AR2MS_class (R: AbsRing): MetricSpace.mixin_of (AbsRing.sort R).
  exists (fun x y => abs (minus x y)).
  by move => x y; apply /abs_ge_0.
  by move => x y; apply/abs_minus.
  by move => x; rewrite minus_eq_zero; apply/abs_zero.
  by move => x y eq; apply/minus_eq/abs_eq_zero.
  move => x y z.
  rewrite /minus.
  apply/Rle_trans/abs_triangle.
  suff ->: plus x (opp y) = plus (plus x (opp z)) (plus z (opp y)) by apply/Rle_refl.
  by rewrite plus_assoc -(plus_assoc x) plus_opp_l plus_zero_r.
Defined.

Canonical AR2MS (R: AbsRing): MetricSpace := MetricSpace.Pack (AR2MS_class R) (AbsRing.sort R).

Definition NM2MS_class (K: AbsRing) (V: NormedModule K):
  MetricSpace.mixin_of (NormedModule.sort K V).
  exists (fun x y => norm (minus x y)).
  by move => x y; apply/norm_ge_0.
  by move => x y; rewrite -{1}opp_minus norm_opp.
  by move => x; rewrite minus_eq_zero norm_zero.
  by move => x y eq; apply/minus_eq/norm_eq_zero.
  move => x y z.
  rewrite /minus.
  apply/Rle_trans/norm_triangle.
  suff ->: plus x (opp y) = plus (plus x (opp z)) (plus z (opp y)) by apply/Rle_refl.
  by rewrite plus_assoc -(plus_assoc x) plus_opp_l plus_zero_r.
Defined.

Canonical NM2MS K V := MetricSpace.Pack (@NM2MS_class K V) V.
Coercion NM2MS: NormedModule >-> MetricSpace.

Definition MS2US_mixin (M: MetricSpace): UniformSpace.mixin_of M.
  exists (fun x r y => d x y < r).
  by move => x [eps eg0]; rewrite dstxx /=.
  by move => x y e ineq; rewrite dst_sym.
  move => x y z e e' ineq ineq'.
  apply/Rle_lt_trans; first exact/(dst_trngl y).
  exact/Rplus_lt_compat.
Defined.

Canonical MS2US (M: MetricSpace):= UniformSpace.Pack M (MS2US_mixin M) M.

Section lemmas.
  Context (M N: MetricSpace).
  Local Open Scope metric_scope.
  Lemma cntp_cont (f: M -> N) x:
    f \is_continuous_in x <-> continuous f x.
  Proof.
    split => [cont P [[eps eg0] prp]| cont eps eg0].
    - have [ | delta [dg0 aprx]]:= cont (eps/2); first by lra.
      exists (mkposreal delta dg0) => /= y bll'.
      apply/prp/Rle_lt_trans; first apply/aprx/Rlt_le/bll'.
      by rewrite /=; lra.
    have [ | [delta dg0] prp]:= cont (fun y => d (f x) y < eps); first by exists (mkposreal eps eg0).
    exists (delta/2); split => [ | y dst]; first by lra.
    apply/Rlt_le/prp/Rle_lt_trans; first exact/dst.
    rewrite /=; lra.
  Qed.
End lemmas.