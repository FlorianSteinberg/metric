From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From mf Require Import all_mf.
Require Import pointwise reals pseudo_metrics.
Require Import Reals Psatz Classical ChoiceFacts Morphisms ProofIrrelevance ProofIrrelevanceFacts.

Fact eq_sub T P (a b : {x : T | P x}) : a = b <-> projT1 a = projT1 b.
Proof.
  split=> [->//|]; move: a b => [a Pa] [b Pb] /= eqab.
  case: _ / eqab in Pb *; congr (exist _ _ _).
  exact/proof_irrelevance.
Qed.

Set Implicit Arguments. 
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Local Open Scope metric_scope.
Section metrics.
  Class is_metric (M: Type) (d: M * M -> R) :=
    {
      positive: forall x y, 0 <= d(x, y);
      symmetric: forall x y, d(x, y) = d(y, x);
      reflects_equality: forall x y, d(x, y) = 0 <-> x = y;
      triangle_inequality: forall x y z, d(x, y) <= d(x, z) + d(z, y);
    }.
  Local Notation "d \is_metric" := (is_metric d) (at level 36).
  Local Notation "d \is_metric_on M" := (@is_metric M d) (at level 36).

  Context `{is_metric}.

  Lemma dst0_eq x y: d(x, y) = 0 <-> x = y.
  Proof. by apply reflects_equality. Qed.

  Global Instance m2pm: (d \is_pseudometric)%pmetric.
    split; first by apply positive.
    - exact symmetric.
    by move => x; apply/dst0_eq.
    exact triangle_inequality.
  Defined.

  Lemma dst_pos x y: 0 <= d (x,y).
  Proof. by apply dst_pos. Qed.

  Lemma dst_sym x y: d(x,y) = d(y,x).
  Proof. by apply dst_sym. Qed.

  Lemma dst_trngl z x y: d(x,y) <= d(x,z) + d(z,y).
  Proof. by apply dst_trngl. Qed.
    
  Implicit Types (x y z: M) (xn yn: sequence_in M).

  Notation limit := (limit d).
  
  Lemma lim_sing: limit \is_singlevalued.
  Proof.
    move => xn x y lim lim'.
    by apply dst0_eq, (lim_dst lim lim').
  Qed.

  Lemma lim_tpmn xn x: limit xn x <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof. exact/lim_tpmn. Qed.

  Lemma cond_eq_tpmn x y:
    (forall n, d(x,y) <= / 2 ^ n) -> x = y.
  Proof. by move => /dst0_tpmn/dst0_eq. Qed.
End metrics.
Notation "d \is_metric_on M" := (@is_metric M d) (at level 26): metric_scope.
Notation "d \is_metric" := (is_metric d) (at level 36): metric_scope.

Notation "xn \converges_to x \wrt d" := (limit d xn x) (at level 23): metric_scope.
Section limits.
  Context `{is_metric}.
  Lemma lim_lim xnk xn x: FunctionalCountableChoice_on nat ->
    (forall n, (xnk n) \converges_to (xn n) \wrt d) -> xn \converges_to x \wrt d ->
    exists mu, (fun n => xnk n (mu n)) \converges_to x \wrt d.
  Proof. by apply lim_lim_choice. Qed.    
End limits.

Notation "A \dense_subset_wrt d" := (dense_subset d A) (at level 35): metric_scope.
Notation "xn \dense_wrt d":= (dense_sequence d xn) (at level 35): metric_scope.
Notation "xn \dense_sequence_wrt d":= (dense_sequence d xn) (at level 35): metric_scope.
Notation "A \closed_wrt d":= (closure d A) (at level 35): metric_scope.
Section sets.
  Context `{m: is_metric}.  

  Lemma dns_tpmn (A: subset M):
    A \dense_subset_wrt d <-> forall x n, exists y, y \from A /\ d(x, y) <= /2^n.
  Proof. exact/dns_tpmn. Qed.

  Lemma dseq_dns (r: nat -> M):
    r \dense_wrt d <-> (codom (F2MF r)) \dense_subset_wrt d. 
  Proof. exact/dseq_dns. Qed.

  Lemma dseq_tpmn (r: nat -> M):
    r \dense_wrt d <-> forall x n, exists m, d(x, r m) <= /2^n.
  Proof. exact/dseq_tpmn. Qed.

  Lemma subs_clos A: A \is_subset_of A \closed_wrt d.
  Proof. by apply subs_clos. Qed.

  Hypothesis (M_choice: FunctionalCountableChoice_on M).

  Lemma clos_spec A x:
    x \from A \closed_wrt d <-> exists (xn: sequence_in A), (ptw sval xn) \converges_to x \wrt d.
  Proof.
    rewrite ->clos_spec_choice; last exact/M_choice.
    split => [[xn [Axn prp]] | [xn prp]]; first by exists (fun n => exist _ _ (Axn n)).
    by exists (ptw sval xn); split => // n; apply/(svalP (xn n)).
  Qed.

  Lemma dns_clos A: A \dense_subset_wrt d <-> A \closed_wrt d === All.
  Proof. exact/dns_clos. Qed.
End sets.

Notation "xn \Cauchy_wrt d" := (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \Cauchy_sequence_wrt d" := (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \is_Cauchy_wrt d" := (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \is_Cauchy_sequence_wrt d" :=
  (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "d \is_complete" := (complete d) (at level 45): metric_scope.
Notation "d \is_complete_metric" := (complete d) (at level 45): metric_scope.
Notation "xn \fast_Cauchy_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \fast_Cauchy_sequence_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \is_fast_Cauchy_sequence_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): metric_scope.
Notation "x \efficient_limit_of xn \wrt d" := (efficient_limit d xn x) (at level 45): metric_scope.
Section Cauchy_sequences.
  Local Open Scope pseudometric_scope.
  Context `{m: is_metric}.
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  
  Lemma lim_cchy: dom (limit d) \is_subset_of (Cauchy_sequences d).
  Proof. by apply lim_cchy. Qed.
    
  Lemma fchy_cchy: fast_Cauchy_sequences d \is_subset_of Cauchy_sequences d.
  Proof. exact/fchy_cchy. Qed.
    
  Lemma cchy_tpmn xn: xn \Cauchy_sequence_wrt d <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d(xn n, xn m) <= /2^k).
  Proof. by apply cchy_tpmn. Qed.

  Lemma lim_evb xn mu (x: M):
    xn \converges_to x \wrt d -> eventually_big mu -> (xn \o_f mu) \converges_to x \wrt d.
  Proof. exact/lim_evb. Qed.
  
  Lemma cchy_evb xn mu: xn \Cauchy_wrt d -> eventually_big mu -> (xn \o_f mu) \Cauchy_wrt d.
  Proof. exact/cchy_evb. Qed.
  
  Lemma lim_eff_spec: efficient_limit d =~= (limit d)|_(fast_Cauchy_sequences d).
  Proof. by apply lim_eff_spec. Qed.
    
  Lemma lim_eff_lim : (limit d) \extends efficient_limit d.
  Proof. by apply lim_eff_lim. Qed.

  Lemma fchy_lim_eff: d \is_complete_metric ->
    fast_Cauchy_sequences d === dom (efficient_limit d).
  Proof. by apply fchy_lim_eff. Qed.  

  Lemma lim_tight_lim_eff: (limit d) \tightens (efficient_limit d).
  Proof. by apply sing_exte_tight; [apply lim_sing | apply/lim_eff_lim]. Qed.

  Lemma lim_eff_sing: (efficient_limit d) \is_singlevalued.
  Proof.
    by apply/exte_sing; first apply lim_eff_lim; last apply lim_sing.
  Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n, xn m) <= /2^n + /2^m) ->
    xn \fast_Cauchy_sequence_wrt d.
  Proof. by apply cchy_eff_suff. Qed.

  Hypothesis (nat_choice: FunctionalCountableChoice_on nat).
  Lemma cchy_fchy xn: xn \Cauchy_wrt d -> exists mu, (xn \o_f mu) \fast_Cauchy_sequence_wrt d.
  Proof. by apply cchy_fchy_choice, nat_choice. Qed.
End Cauchy_sequences.  

Section continuity.
  Local Open Scope pseudometric_scope.
  Context `{m: is_metric}.
  Context `{m0: is_metric}.
  Context (f: M -> M0).
  
  Lemma cont_tpmn:
    f \continuous_wrt d \and d0 <-> forall x n, exists m, forall x', d (x, x') <= /2^m -> d0 (f x, f x') <= /2^n.
  Proof. exact/cont_tpmn. Qed.
  
  Lemma cntp_scntp: continuity_points d d0 f \is_subset_of sequential_continuity_points d d0 f.
  Proof. exact/cntp_scntp. Qed.

  Lemma cont_scnt: f \continuous_wrt d \and d0 -> f \sequentially_continuous_wrt d \and d0.
  Proof. exact/cont_scnt. Qed.

  Hypothesis (M_choice: FunctionalCountableChoice_on M).
  Lemma scnt_cont: f \sequentially_continuous_wrt d \and d0 -> f \continuous_wrt d \and d0.
  Proof. exact/scnt_cont_choice/M_choice. Qed.
End continuity.

Section sub_metrics.
  Context `{is_metric}.

  Definition sub_met (A: subset M) (p: {x | x \from A} * {x | x \from A}) := d(sval p.1, sval p.2).
  Arguments sub_met: clear implicits.
  
  Global Instance sub_metric (A: subset M):
    (sub_met A) \is_metric_on {x | x \from A}.
    rewrite /sub_met.
    destruct (sub_pseudo_metric A); intros.
    split => // x y; split => [dst | -> ] //.
    by apply eq_sub, dst0_eq.
  Defined.
End sub_metrics.
