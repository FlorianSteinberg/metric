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
  Proof. exact/metric. Qed.

  Global Instance M2PM: PseudoMetricSpace.
  Proof. exists carrier distance; exact/m2pm. Defined.
End MetricSpaces.  
Coercion M2PM: MetricSpace >-> PseudoMetricSpace.

Section limits.
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  
  Lemma lim_sing: limit \is_singlevalued.
  Proof. exact/lim_sing. Qed.

  Definition lim_cnst := @lim_cnst M.

  Lemma lim_tpmn xn x: limit xn x <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof. exact/lim_tpmn. Qed.

  Lemma cond_eq_tpmn x y:
    (forall n, d(x,y) <= / 2 ^ n) -> x = y.
  Proof. exact/cond_eq_tpmn. Qed.

  Lemma lim_lim xnk xn x:
    (forall n, (xn n) \is_limit_of (xnk n)) -> x \is_limit_of xn ->
    exists mu, x \is_limit_of (fun n => xnk n (mu n)).
  Proof. exact/lim_lim. Qed.    
End limits.

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
  Proof. exact/subs_clos. Qed.

  Lemma clos_spec A x: x \from closure A <->
                       exists xn, x \is_limit_of xn /\ forall n, xn n \from A.
  Proof. exact/clos_spec. Qed.

  Lemma dns_clos A: A \dense_subset_wrt d <-> A \closed_wrt d === All.
  Proof. exact/dns_clos. Qed.
End sets.

Section Cauchy_sequences.
  Context (M: MetricSpace).
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  
  Lemma lim_cchy: dom limit \is_subset_of Cauchy_sequences.
  Proof. exact/lim_cchy. Qed.
    
  Lemma fchy_cchy: fast_Cauchy_sequences \is_subset_of Cauchy_sequences.
  Proof. exact/fchy_cchy. Qed.
    
  Lemma cchy_tpmn xn: xn \Cauchy <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d(xn n, xn m) <= /2^k).
  Proof. exact/cchy_tpmn. Qed.

  Lemma lim_evb xn mu (x: M):
    x \is_limit_of xn -> eventually_big mu -> x \is_limit_of (xn \o_f mu).
  Proof. exact/lim_evb. Qed.
  
  Lemma cchy_evb xn mu: xn \Cauchy -> eventually_big mu -> (xn \o_f mu) \Cauchy.
  Proof. exact/cchy_evb. Qed.

  Lemma cchy_fchy xn: xn \Cauchy -> exists mu, (xn \o_f mu) \fast_Cauchy_sequence.
  Proof. exact/cchy_fchy. Qed.
  
  Lemma lim_eff_spec: efficient_limit =~= limit|_fast_Cauchy_sequences.
  Proof. exact/lim_eff_spec. Qed.
    
  Lemma lim_eff_lim : limit \extends efficient_limit.
  Proof. exact/lim_eff_lim. Qed.

  Lemma fchy_lim_eff: d \is_complete_metric ->
    fast_Cauchy_sequences === dom efficient_limit.
  Proof. exact/fchy_lim_eff. Qed.  

  Lemma lim_tight_lim_eff: limit \tightens efficient_limit.
  Proof. exact/lim_tight_lim_eff. Qed.

  Lemma lim_eff_sing: efficient_limit \is_singlevalued.
  Proof. exact/lim_eff_sing. Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n, xn m) <= /2^n + /2^m) ->
    xn \fast_Cauchy_sequence_wrt d.
  Proof. exact/cchy_eff_suff. Qed.
End Cauchy_sequences.  

Definition metric_function (M M': MetricSpace) := M -> M'.
Definition pseudo_metric_function (M M': PseudoMetricSpace):= M -> M'.

Section continuity.
  Context (M M': MetricSpace) (f: carrier -> carrier).
  
  Lemma cntp_scntp: continuity_points f \is_subset_of sequential_continuity_points f.
  Proof. exact/cntp_scntp. Qed.

  Lemma cont_scnt: f \is_continuous -> f \sequentially_continuous.
  Proof. exact/cont_scnt. Qed.
  
  Lemma scnt_cont: f \sequentially_continuous -> f \is_continuous.
  Proof. exact/scnt_cont. Qed.
End continuity.

Section sub_metrics.
  Context (M: MetricSpace).

  Global Instance subspace (A: subset M): MetricSpace.
    exists {x | x \from A} (fun p => d(sval p.1, sval p.2)).
    exact/sub_metric.
  Defined.
  
  Definition sub_fun S T (A: subset S) (f: S -> T) (a: A) := f (sval a).
  Arguments sub_fun {S} {T} (A).
  
  Definition sub_mf S T (A: subset S) (f: S ->> T) :=
    make_mf (fun (a: A) t => f (sval a) t).

  Lemma sub_F2MF S T (A: subset S) (f: S -> T):
    F2MF (sub_fun A f) =~= sub_mf A (F2MF f).
  Proof. done. Qed.
End sub_metrics.