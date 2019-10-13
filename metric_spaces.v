From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From mf Require Import all_mf.
Require Import pointwise reals pseudo_metrics pseudo_metric_spaces metrics.
Require Import Reals Psatz Classical ChoiceFacts Morphisms ProofIrrelevance ProofIrrelevanceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Local Open Scope metric_scope.
Section MetricSpaces.
  Class MetricSpace :=
    {
      carrier: Type;
      distance: carrier * carrier -> R;
      metric: distance \is_metric;
    }.

  Coercion carrier: MetricSpace >-> Sortclass.
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: sequence_in M).

  Global Instance distant_metric: distance \is_metric.
  Proof. exact metric. Qed.

  Global Instance M2PM: PseudoMetricSpace.
    by exists carrier distance; apply m2pm.
  Defined.

  Lemma dst_le x y z r r' q:
    d (x, z) <= r -> d (z, y) <= r' -> r + r' <= q -> d (x, y) <= q.
  Proof. by apply dst_le. Qed.

  Lemma le_dst x y z r r' q: r + r' <= q -> d(x,z) <= r -> d(z,y) <= r' -> d(x,y) <= q.
  Proof. by apply le_dst. Qed.

  Lemma dst_lt x y z r r' q: d(x,z) <= r -> d(z,y) <= r' -> r + r' < q -> d(x,y) < q.
  Proof. by apply dst_lt. Qed.

End MetricSpaces.  
Coercion M2PM: MetricSpace >-> PseudoMetricSpace.

Notation "xn ~> x" := (limit xn x) (at level 23): metric_scope.
Notation "x \limit_of xn" := (xn ~> x) (at level 23): metric_scope.
Notation "x \is_limit_of xn" := (xn ~> x) (at level 23): metric_scope.
Section limits.
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: sequence_in M).

  Lemma lim_sing: limit \is_singlevalued.
  Proof. exact lim_sing. Qed.

  Definition lim_cnst := @lim_cnst M.

  Lemma lim_tpmn xn x: limit xn x <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof. exact/lim_tpmn. Qed.

  Lemma cond_eq_tpmn x y:
    (forall n, d(x,y) <= / 2 ^ n) -> x = y.
  Proof. by apply cond_eq_tpmn. Qed.

  Lemma lim_lim xnk xn x: FunctionalCountableChoice ->
    (forall n, (xn n) \is_limit_of (xnk n)) -> x \is_limit_of xn ->
    exists mu, x \is_limit_of (fun n => xnk n (mu n)).
  Proof. by move => choice; apply lim_lim. Qed.
End limits.

Notation "A \dense_subset" := (A \dense_subset_wrt d) (at level 35): metric_scope.
Notation "A \is_dense_subset":= (A \dense_subset) (at level 35): metric_scope.
Notation "xn \dense" := (xn \dense_wrt d) (at level 35): metric_scope.
Notation "xn \is_dense" := (xn \dense) (at level 35): metric_scope.
Notation "xn \dense_sequence" := (xn \dense) (at level 35): metric_scope.
Notation "xn \is_dense_sequence" := (xn \dense) (at level 35): metric_scope.
Section sets.
  Context (M: MetricSpace).

  Lemma dns_tpmn (A: subset M):
    A \dense_subset <-> forall x n, exists y, y \from A /\ d(x, y) <= /2^n.
  Proof. exact/dns_tpmn. Qed.

  Lemma dseq_dns (xn: sequence_in M): xn \dense <-> (codom (F2MF xn)) \dense_subset. 
  Proof. exact/dseq_dns. Qed.

  Lemma dseq_tpmn (xn: sequence_in M):
    xn \dense <-> forall x n, exists k, d(x, xn k) <= /2^n.
  Proof. exact/dseq_tpmn. Qed.

  Lemma subs_clos A: A \is_subset_of closure A.
  Proof. by apply subs_clos. Qed.

  Lemma clos_spec A x: FunctionalCountableChoice -> x \from closure A <->
                       exists (xn: sequence_in A), x \is_limit_of (ptw sval xn).
  Proof. by move => choice; apply clos_spec. Qed.

  Lemma dns_clos A: A \dense_subset_wrt d <-> closure A === All.
  Proof. exact/dns_clos. Qed.
End sets.

Notation "xn \Cauchy" := (xn \Cauchy_wrt d) (at level 45): metric_scope.
Notation "xn \Cauchy_sequence" := (xn \Cauchy) (at level 45): metric_scope.
Notation "xn \is_Cauchy" := (xn \Cauchy) (at level 45): metric_scope.
Notation "xn \is_Cauchy_sequence" := (xn \Cauchy) (at level 45): metric_scope.
Notation "xn \fast_Cauchy" := (xn \fast_Cauchy_wrt d) (at level 45): metric_scope.
Notation "xn \fast_Cauchy_sequence" := (xn \fast_Cauchy) (at level 45): metric_scope.
Notation "xn \is_fast_Cauchy_sequence" := (xn \fast_Cauchy) (at level 45): metric_scope.
Notation "x \efficient_limit_of xn" := (efficient_limit xn x) (at level 45): metric_scope.
Notation "M \is_complete" := (complete M) (at level 45): metric_scope.
Section Cauchy_sequences.
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  
  Lemma lim_cchy: dom limit \is_subset_of Cauchy_sequences.
  Proof. exact lim_cchy. Qed.
    
  Lemma fchy_cchy: fast_Cauchy_sequences \is_subset_of Cauchy_sequences.
  Proof. exact/fchy_cchy. Qed.
    
  Lemma cchy_tpmn xn: xn \Cauchy <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d(xn n, xn m) <= /2^k).
  Proof. by apply cchy_tpmn. Qed.

  Lemma lim_evb xn mu (x: M):
    x \is_limit_of xn -> eventually_big mu -> x \is_limit_of (xn \o_f mu).
  Proof. exact/lim_evb. Qed.
  
  Lemma cchy_evb xn mu: xn \Cauchy -> eventually_big mu -> (xn \o_f mu) \Cauchy.
  Proof. exact/cchy_evb. Qed.

  Lemma cchy_fchy xn: FunctionalCountableChoice_on nat -> xn \Cauchy -> exists mu, (xn \o_f mu) \fast_Cauchy_sequence.
  Proof. by move => choice; apply cchy_fchy. Qed.
  
  Lemma lim_eff_spec: efficient_limit =~= limit|_fast_Cauchy_sequences.
  Proof. exact lim_eff_spec. Qed.
    
  Lemma lim_eff_lim : limit \extends efficient_limit.
  Proof. exact lim_eff_lim. Qed.

  Lemma fchy_lim_eff: d \is_complete_metric ->
    fast_Cauchy_sequences === dom efficient_limit.
  Proof. exact fchy_lim_eff. Qed.  

  Lemma lim_tight_lim_eff: limit \tightens efficient_limit.
  Proof. exact lim_tight_lim_eff. Qed.

  Lemma lim_eff_sing: efficient_limit \is_singlevalued.
  Proof. exact lim_eff_sing. Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n, xn m) <= /2^n + /2^m) ->
    xn \fast_Cauchy_sequence_wrt d.
  Proof. by apply cchy_eff_suff. Qed.
End Cauchy_sequences.  
Notation "f \continuous_in x" :=
  (continuity_point d d (f: M2PM _ -> M2PM _) x) (at level 35): metric_scope.
Notation d := distance.
Notation continuity_points:= (pseudo_metrics.continuity_points d d).
Notation "f \continuous" := (continuous d d f) (at level 2): metric_scope.
Local Open Scope pseudometric_scope.
Notation "f \is_continuous" := (f \continuous_wrt d \and d) (at level 2): metric_scope.
Notation sequential_continuity_points := (pseudo_metrics.sequential_continuity_points d d).
Notation "f \sequentially_continuous_in x" :=
  (sequential_continuity_point d d f x) (at level 40): metric_scope.
Notation "f \sequentially_continuous" :=
  (f \sequentially_continuous_wrt d \and d) (at level 40): metric_scope.
Notation "f \is_sequentially_continuous" :=
  (f \sequentially_continuous) (at level 40): metric_scope.
Local Close Scope pseudometric_scope.

Section continuity.
  Context (M M': MetricSpace) (f: M -> M').

  Lemma cntp_tpmn x:
    f \continuous_in x <-> forall n, exists m, forall x', d (x, x') <= /2^m -> d (f x, f x') <= /2^n.
  Proof. by apply cntp_tpmn. Qed.
  
  Lemma cont_tpmn:
    f \is_continuous <-> forall x n, exists m, forall x', d (x, x') <= /2^m -> d (f x, f x') <= /2^n.
  Proof. exact/cont_tpmn. Qed.
    
  Lemma cntp_scntp: continuity_points f \is_subset_of sequential_continuity_points f.
  Proof. exact/cntp_scntp. Qed.

  Lemma cont_scnt: f \is_continuous -> f \sequentially_continuous.
  Proof. exact/cont_scnt. Qed.
  
  Lemma scnt_cont: FunctionalCountableChoice_on M -> f \sequentially_continuous -> f \is_continuous.
  Proof. by apply scnt_cont. Qed.
End continuity.

Section subspaces.
  Context (M: MetricSpace).

  Global Instance subspace (A: subset M): MetricSpace.
    exists {x | x \from A} (fun p => d(sval p.1, sval p.2)).
    by apply sub_metric.
  Defined.
  
  Definition sub_fun S T (A: subset S) (f: S -> T) (a: A) := f (sval a).
  Arguments sub_fun {S} {T} (A).
  
  Definition sub_mf S T (A: subset S) (f: S ->> T) :=
    make_mf (fun (a: A) t => f (sval a) t).

  Lemma sub_F2MF S T (A: subset S) (f: S -> T):
    F2MF (sub_fun A f) =~= sub_mf A (F2MF f).
  Proof. done. Qed.
End subspaces.
Notation pd:= pseudo_metric_spaces.distance.
