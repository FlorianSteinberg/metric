From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From mf Require Import all_mf.
Require Import pointwise reals pseudo_metrics.
Require Import Reals Psatz Classical ChoiceFacts Morphisms ProofIrrelevance ProofIrrelevanceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope metric_scope.
Local Open Scope R_scope.

Section PseudoMetricSpaces.
  Class PseudoMetricSpace :=
    {carrier:> Type;
     distance: carrier * carrier -> R;
     pseudo_metric: distance \is_pseudo_metric_on carrier}.

  Coercion carrier: PseudoMetricSpace >-> Sortclass.

  Global Instance pm (M: PseudoMetricSpace): distance \is_pseudo_metric.
  Proof. exact/pseudo_metric. Qed.
  Notation d := distance.

  Context (M: PseudoMetricSpace).
  Implicit Types (x y z: M).
    
  Lemma dst_le x y z r r' q: d(x,z) <= r -> d(z,y) <= r' -> r + r' <= q -> d(x,y) <= q.
  Proof. exact/dst_le. Qed.

  Lemma le_dst x y z r r' q: r + r' <= q -> d(x,z) <= r -> d(z,y) <= r' -> d(x,y) <= q.
  Proof. exact/le_dst. Qed.

  Lemma dst_lt x y z r r' q: d(x,z) <= r -> d(z,y) <= r' -> r + r' < q -> d(x,y) < q.
  Proof. exact/dst_lt. Qed.
End PseudoMetricSpaces.
Notation d := distance.

Section limits.
  Context (M: PseudoMetricSpace).
  Implicit Types (x y z: M).
  Local Notation "xn ~> x" := (limit d xn x) (at level 4).
  Local Notation "x \limit_of xn":= (xn ~> x) (at level 4).
  Local Notation "x \is_limit_of xn" := (xn ~> x) (at level 4).
  
  Lemma lim_dst xn x y: x \limit_of xn -> y \limit_of xn  -> d(x,y) = 0.
  Proof. exact/lim_dst. Qed.

  Lemma lim_cnst x: x \limit_of (cnst x).
  Proof. exact/lim_cnst. Qed.
  
  Lemma lim_tpmn xn x: x \limit_of xn <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof. exact/lim_tpmn. Qed.
  
  Lemma dst0_tpmn x y: (forall n, d(x,y) <= / 2 ^ n) <-> d(x,y) = 0.
  Proof. exact/dst0_tpmn. Qed.
End limits.
Notation limit := (limit d).
Notation "xn ~> x" := (limit xn x) (at level 23): metric_scope.
Notation "x \limit_of xn" := (xn ~> x) (at level 23): metric_scope.
Notation "x \is_limit_of xn" := (xn ~> x) (at level 23): metric_scope.

Section density.
  Context (M: PseudoMetricSpace).
  Local Notation "A \is_dense_subset" := (A \dense_subset_wrt d) (at level 35).
  Local Notation "xn \is_dense" := (xn \dense_sequence_wrt d) (at level 35).
  Local Notation closure A := (closure d A).

  Lemma dns_tpmn (A: subset M):
    A \is_dense_subset <-> forall x n, exists y, y \from A /\ d(x,y) <= /2^n.
  Proof. exact/dns_tpmn. Qed.  
  
  Lemma dseq_dns (xn: sequence):
    xn \is_dense <-> (codom (F2MF xn)) \is_dense_subset. 
  Proof. exact/dseq_dns. Qed.

  Lemma dseq_tpmn (xn: sequence):
    xn \is_dense <-> forall x n, exists k, d(x,xn k) <= /2^n.
  Proof. exact/dseq_tpmn. Qed.
  
  Lemma subs_clos A: A \is_subset_of closure A.
  Proof. exact/subs_clos. Qed.

  Lemma dns_clos A: A \is_dense_subset <-> closure A === All.
  Proof. exact/dns_clos. Qed.
End density.
Notation "A \dense_subset" := (A \dense_subset_wrt d) (at level 35): metric_scope.
Notation "A \is_dense_subset":= (A \dense_subset) (at level 35): metric_scope.
Notation "xn \dense" := (xn \dense_wrt d) (at level 35): metric_scope.
Notation "xn \is_dense" := (xn \dense) (at level 35): metric_scope.
Notation "xn \dense_sequence" := (xn \dense) (at level 35): metric_scope.
Notation "xn \is_dense_sequence" := (xn \dense) (at level 35): metric_scope.
Notation closure A := (closure d A).

Section Cauchy_sequences.
  Context (M: PseudoMetricSpace).
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  Local Notation Cauchy_sequences := (Cauchy_sequences d).
  Local Notation "xn \Cauchy" := (xn \is_Cauchy_sequence_wrt d) (at level 4).
  Local Notation complete := (complete d).
  
  Lemma lim_cchy: dom limit \is_subset_of Cauchy_sequences.
  Proof. exact/lim_cchy. Qed.  
      
  Lemma cchy_tpmn xn: xn \Cauchy <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d (xn n, xn m) <= /2^k).
  Proof. exact/cchy_tpmn. Qed.

  Lemma lim_evb xn mu (x: M): x \limit_of xn -> eventually_big mu -> limit (xn \o_f mu) x.
  Proof. exact/lim_evb. Qed.
  
  Lemma cchy_evb xn mu: xn \Cauchy -> eventually_big mu -> (xn \o_f mu) \Cauchy.
  Proof. exact/cchy_evb. Qed.
End Cauchy_sequences.
Notation Cauchy_sequences:= (Cauchy_sequences d).  
Notation "xn \Cauchy" := (xn \Cauchy_wrt d) (at level 45): metric_scope.
Notation "xn \Cauchy_sequence" := (xn \Cauchy) (at level 45): metric_scope.
Notation "xn \is_Cauchy" := (xn \Cauchy) (at level 45): metric_scope.
Notation "xn \is_Cauchy_sequence" := (xn \Cauchy) (at level 45): metric_scope.
Notation complete M := (@complete M d).
Notation "M \is_complete" := (complete M) (at level 45): metric_scope.

Section efficient_convergence.
  Context (M: PseudoMetricSpace).
  Local Notation fast_Cauchy_sequences := (fast_Cauchy_sequences d).
  Local Notation "xn \fast_Cauchy" := (xn \is_fast_Cauchy_sequence_wrt d) (at level 35).
  Local Notation efficient_limit := (efficient_limit d).
  
  Lemma fchy_cchy: fast_Cauchy_sequences \is_subset_of Cauchy_sequences.
  Proof. exact/fchy_cchy. Qed.
  
  Lemma lim_eff_spec: efficient_limit =~= limit|_(fast_Cauchy_sequences).
  Proof. exact/lim_eff_spec. Qed.
    
  Lemma lim_eff_lim : limit \extends efficient_limit.
  Proof. exact/lim_eff_lim. Qed.

  Lemma fchy_lim_eff: complete M ->
    fast_Cauchy_sequences === dom efficient_limit.
  Proof. exact/fchy_lim_eff. Qed.

  Lemma lim_eff_dst xn x y: efficient_limit xn x -> efficient_limit xn y -> d(x, y) = 0.
  Proof. exact/lim_eff_dst. Qed.

  Lemma lim_tight_lim_eff: limit \tightens efficient_limit.
  Proof. exact/lim_tight_lim_eff. Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n, xn m) <= /2^n + /2^m) -> xn \fast_Cauchy.
  Proof. exact/cchy_eff_suff. Qed.
End efficient_convergence.
Notation fast_Cauchy_sequences := (fast_Cauchy_sequences d).  
Notation "xn \fast_Cauchy" := (xn \fast_Cauchy_wrt d) (at level 45): metric_scope.
Notation "xn \fast_Cauchy_sequence" := (xn \fast_Cauchy) (at level 45): metric_scope.
Notation "xn \is_fast_Cauchy_sequence" := (xn \fast_Cauchy) (at level 45): metric_scope.
Notation efficient_limit:= (efficient_limit d).
Notation "x \efficient_limit_of xn" := (efficient_limit xn x) (at level 45): metric_scope.

Section continuity.
  Context (M M': PseudoMetricSpace).
  Context (f: M -> M').
  Implicit Types (x y: M) (xn yn: sequence_in M).
  Local Notation continuous_in x := (continuity_point d d f x).
  Local Notation continuous := (f \continuous_wrt d \and d).
  Local Notation continuity_points := (continuity_points d d f).
  Local Notation sequential_continuity_points := (sequential_continuity_points d d f).
  Local Notation sequentially_continuous := (f \sequentially_continuous_wrt d \and d).

  Lemma cntp_tpmn x:
    continuous_in x <-> forall n, exists m, forall x', d (x, x') <= /2^m -> d (f x, f x') <= /2^n.
  Proof. exact/cntp_tpmn. Qed.
  
  Lemma cont_tpmn:
    continuous <-> forall x n, exists m, forall x', d (x, x') <= /2^m -> d (f x, f x') <= /2^n.
  Proof. exact/cont_tpmn. Qed.
  
  Lemma cntp_all: continuous <-> continuity_points === All.
  Proof. exact/cntp_all. Qed.

  Lemma scntp_all: sequentially_continuous <-> sequential_continuity_points === All.
  Proof. exact/scntp_all. Qed.

  Lemma cntp_scntp: continuity_points \is_subset_of sequential_continuity_points.
  Proof. exact/cntp_scntp. Qed.
  
  Lemma cont_scnt: continuous -> sequentially_continuous.
  Proof. exact/cont_scnt. Qed.
End continuity.
Notation "f \continuous_in x" :=
  (continuity_point d d  f x) (at level 35): pseudo_metric_scope.
Notation continuity_points:= (continuity_points d d).
Notation "f \continuous" := (continuous d d f) (at level 2): pseudo_metric_scope.
Notation "f \is_continuous" := (f \continuous_wrt d \and d) (at level 2): pseudo_metric_scope.
Notation sequential_continuity_points := (sequential_continuity_points d d).
Notation "f \sequentially_continuous_in x" :=
  (sequential_continuity_point d d f x) (at level 40): pseudo_metric_scope.
Notation "f \sequentially_continuous" :=
  (f \sequentially_continuous_wrt d \and d) (at level 40): pseudo_metric_scope.
Notation "f \is_sequentially_continuous" :=
  (f \sequentially_continuous_wrt d \and d) (at level 40): pseudo_metric_scope.

Delimit Scope pseudo_metric_scope with pmetric.
Section subspaces.
  Context (M: PseudoMetricSpace).

  Global Instance subspace (A: subset M): PseudoMetricSpace.
    exists {x | x \from A} (fun xy => d (sval xy.1, sval xy.2)).
    split; first by move => x y; apply/dst_pos.
    - by move => x y; apply/dst_sym.
    - by move => x; apply/dstxx.
    by move => x y z; apply/dst_trngl.
  Defined.
End subspaces.
