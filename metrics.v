From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From mf Require Import all_mf.
Require Import pointwise reals pseudo_metrics.
Require Import Reals Psatz Classical ChoiceFacts Morphisms ProofIrrelevance ProofIrrelevanceFacts.

Axiom countable_choice: FunctionalCountableChoice.
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
  Class metric `{M: Type} (d: M * M -> R) :=
    {
      dst_pos: forall x y, 0 <= d(x, y);
      dst_sym: forall x y, d(x, y) = d(y, x);
      dst0_eq: forall x y, d(x, y) = 0 <-> x = y;
      dst_trngl: forall z x y, d(x, y) <= d(x, z) + d(z, y);
    }.
  Local Notation "d \is_metric" := (metric d) (at level 36).
  Local Notation "d \is_metric_on M" := (@metric M d) (at level 36).
  
  Global Instance m2pm M d: d \is_metric_on M -> d \is_pseudo_metric.
    split; first exact/dst_pos.
    exact/dst_sym.
    by move => x; apply/dst0_eq.
    exact/dst_trngl.
  Defined.

  Context `{m: metric}.
  Implicit Types (x y z: M) (xn yn: sequence_in M).

  Notation limit := (limit d).
  
  Lemma lim_sing: limit \is_singlevalued.
  Proof.
    move => xn x y lim lim'.
    exact/dst0_eq/lim_dst/lim'/lim.
  Qed.

  Definition lim_cnst := @lim_cnst M.

  Lemma lim_tpmn xn x: limit xn x <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof. exact/lim_tpmn. Qed.

  Lemma cond_eq_tpmn x y:
    (forall n, d(x,y) <= / 2 ^ n) -> x = y.
  Proof. by move => /dst0_tpmn/dst0_eq. Qed.

  Lemma lim_lim xnk xn x:
    (forall n, (xnk n) \converges_to (xn n) \wrt d) -> xn \converges_to x \wrt d ->
    exists mu, (fun n => xnk n (mu n)) \converges_to x \wrt d.
  Proof.
    move => lmtlmt /lim_tpmn lmt.
    have /countable_choice [mu muprp]:
      forall n, exists m, forall k, (m <= k)%nat -> d (xn n, xnk n k) <= /2 ^ n.
    - by move => n; apply/(lmtlmt n (/2^n))/Rinv_0_lt_compat/pow_lt; lra.
    exists mu.
    apply/lim_tpmn => n.
    have [N prp]:= lmt (n.+1).
    exists (maxn n.+1 N) => k ineq.
    apply/le_dst/muprp => //; last first.
    apply/prp/leq_trans/ineq/leq_maxr.
    rewrite [X in _ <= X]tpmn_half.
    apply/Rplus_le_compat/Rinv_le_contravar/Rle_pow/leP/leq_trans/ineq/leq_maxl; try lra.
    by apply/pow_lt; lra.
  Qed.    
End metrics.
Notation "d \is_metric_on M" := (@metric M d) (at level 26): metric_scope.
Notation "d \is_metric" := (metric d) (at level 36): metric_scope.

Section sets.
  Context `{m: metric}.  

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
  Proof. exact/subs_clos. Qed.

  Lemma clos_spec A x: x \from A \closed_wrt d <->
                     exists (xn: nat -> M), xn \converges_to x \wrt d /\ forall n, xn n \from A.
  Proof.
    split => [clos | [xn [lmt prp]] eps eg0].
    - have /countable_choice [xn prp]: forall n, exists y, d(y, x) <= /2^n /\ A y.
      + move => n.
        have [ | y []]:= clos (/2^n); first by apply/Rinv_0_lt_compat/pow_lt; lra.
        by exists y; rewrite dst_sym.
      exists xn; split => [ | n]; last by have []:= prp n.
      apply/lim_tpmn => n; exists n => k ineq.
      rewrite dst_sym; apply/Rle_trans; first exact/(prp k).1.
      apply/Rinv_le_contravar/Rle_pow/leP => //; try lra.
      by apply/pow_lt; lra.
    have [n cnd]:= lmt eps eg0.
    by exists (xn n); split; [apply/prp | apply/(cnd n)].
  Qed.

  Lemma dns_clos A: A \dense_subset_wrt d <-> A \closed_wrt d === All.
  Proof. exact/dns_clos. Qed.
End sets.

Section Cauchy_sequences.
  Context `{m: metric}.
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  
  Lemma lim_cchy: dom (limit d) \is_subset_of (Cauchy_sequences d).
  Proof. exact/lim_cchy. Qed.
    
  Lemma fchy_cchy: fast_Cauchy_sequences d \is_subset_of Cauchy_sequences d.
  Proof. exact/fchy_cchy. Qed.
    
  Lemma cchy_tpmn xn: xn \Cauchy_sequence_wrt d <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d(xn n, xn m) <= /2^k).
  Proof. exact/cchy_tpmn. Qed.

  Lemma lim_evb xn mu (x: M):
    xn \converges_to x \wrt d -> eventually_big mu -> (xn \o_f mu) \converges_to x \wrt d.
  Proof. exact/lim_evb. Qed.
  
  Lemma cchy_evb xn mu: xn \Cauchy_wrt d -> eventually_big mu -> (xn \o_f mu) \Cauchy_wrt d.
  Proof. exact/cchy_evb. Qed.

  Lemma cchy_fchy xn: xn \Cauchy_wrt d -> exists mu, (xn \o_f mu) \fast_Cauchy_sequence_wrt d.
  Proof.
    move => /cchy_tpmn cchy.    
    have /countable_choice[mu prp]:= cchy.
    exists mu => n k /=.
    case/orP: (leq_total (mu n) (mu k)) => ineq.
    - apply/Rle_trans; first by apply/prp/andP.
      rewrite -[X in X <= _]Rplus_0_r; apply/Rplus_le_compat_l.
      by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    rewrite dst_sym; apply/Rle_trans; first by apply/prp/andP.
    rewrite -[X in X <= _]Rplus_0_l; apply/Rplus_le_compat_r.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.
  
  Lemma lim_eff_spec: efficient_limit d =~= (limit d)|_(fast_Cauchy_sequences d).
  Proof. exact/lim_eff_spec. Qed.
    
  Lemma lim_eff_lim : (limit d) \extends efficient_limit d.
  Proof. exact/lim_eff_lim. Qed.

  Lemma fchy_lim_eff: d \is_complete_metric ->
    fast_Cauchy_sequences d === dom (efficient_limit d).
  Proof. exact/fchy_lim_eff. Qed.  

  Lemma lim_tight_lim_eff: (limit d) \tightens (efficient_limit d).
  Proof.
    apply sing_exte_tight; [exact/lim_sing | exact/lim_eff_lim].
  Qed.

  Lemma lim_eff_sing: (efficient_limit d) \is_singlevalued.
  Proof.
    by apply/exte_sing; first apply/ lim_eff_lim; last apply/lim_sing.
  Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n, xn m) <= /2^n + /2^m) ->
    xn \fast_Cauchy_sequence_wrt d.
  Proof. exact/cchy_eff_suff. Qed.
End Cauchy_sequences.  

Section continuity.
  Context `{m: metric}.
  Context `{m0: metric}.
  Context (f: M -> M0).
  
  Lemma cntp_scntp: continuity_points d d0 f \is_subset_of sequential_continuity_points d d0 f.
  Proof. exact/cntp_scntp. Qed.

  Lemma cont_scnt: f \continuous_wrt d \and d0 -> f \sequentially_continuous_wrt d \and d0.
  Proof. exact/cont_scnt. Qed.
  
  Lemma scnt_cont: f \sequentially_continuous_wrt d \and d0 -> f \continuous_wrt d \and d0.
  Proof.    
    move => scnt x eps eg0.
    apply/not_all_not_ex => prp.
    have /countable_choice [xn xnprp]: forall n, exists y, d(x, y) <= /2^n /\ eps < d0(f x, f y).
    - move => n; have /not_and_or [ | cnd]:= (prp (/2 ^ n)).
      + by have : 0 < /2^n by apply/Rinv_0_lt_compat/pow_lt; lra.
      apply/not_all_not_ex => asd.
      apply/cnd => y dst.
      have /not_and_or [ineq | ineq]:= asd y; last exact/Rnot_lt_le.
      lra.
    have lmt: xn \converges_to x \wrt d.
    - rewrite lim_tpmn => n.
      exists n => k ineq; have [le _]:= xnprp k.
      apply/Rle_trans; first exact/le.
      apply/Rinv_le_contravar/Rle_pow; try lra; first by apply/pow_lt; lra.
      exact/leP.
    have [K cnd]:= scnt x xn lmt eps eg0.
    have []:= xnprp K.
    suff: d0 (f x, f (xn K)) <= eps by lra.
    exact/cnd.
  Qed.
End continuity.

Section sub_metrics.
  Context `{m: metric}.

  Definition sub_met (A: subset M) (p: {x | x \from A} * {x | x \from A}) := d(sval p.1, sval p.2).
  Arguments sub_met: clear implicits.
  
  Global Instance sub_metric (A: subset M):
    (sub_met A) \is_metric_on {x | x \from A}.
    rewrite /sub_met.
    have []:= sub_pseudo_metric A; intros.
    split => // x y; split => [dst | -> ] //.
    exact/eq_sub/dst0_eq.
  Defined.
End sub_metrics.