From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From mf Require Import all_mf.
Require Import pointwise reals.
Require Import Reals Psatz Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope R_scope.
Section pseudometrics.
  Class pseudometric `{M: Type} (d: M * M -> R) :=
    {
      dst_pos: forall x y, 0 <= d(x,y);
      dst_sym: forall x y, d(x,y) = d(y,x);
      dstxx: forall x, d(x,x) = 0;
      dst_trngl: forall z x y, d(x,y) <= d(x,z) + d(z,y);
    }.

  Context M (d: M * M -> R).
  Hypothesis (pm: pseudometric d).
  Implicit Types (x y z: M).
    
  Lemma dst_le x y z r r' q: d(x,z) <= r -> d(z,y) <= r' -> r + r' <= q -> d(x,y) <= q.
  Proof.
    move => ineq ienq' add.
    by apply/Rle_trans/add/Rle_trans/Rplus_le_compat; first exact/dst_trngl.
  Qed.

  Lemma le_dst x y z r r' q: r + r' <= q -> d(x,z) <= r -> d(z,y) <= r' -> d(x,y) <= q.
  Proof. by move => ineq dst dst'; apply/dst_le/ineq/dst'/dst. Qed.

  Lemma dst_lt x y z r r' q: d(x,z) <= r -> d(z,y) <= r' -> r + r' < q -> d(x,y) < q.
  Proof.
    move => ineq ienq' add.
    by apply/Rle_lt_trans/add/Rle_trans/Rplus_le_compat; first exact/dst_trngl.
  Qed.
End pseudometrics.
Notation "d \is_pseudo_metric_on M" := (@pseudometric M d) (at level 36): metric_scope.
Notation "d \is_pseudo_metric" := (pseudometric d) (at level 36): metric_scope.

Local Open Scope metric_scope.
Section limits.
  Context M (d: M * M -> R).
  Hypothesis (pm: d \is_pseudo_metric).
  Definition limit M (d: M * M -> R) := make_mf (fun xn x =>
    forall eps, 0 < eps -> exists N, forall m,
          (N <= m)%nat -> d (x,xn m) <= eps).
  Local Notation "x \limits xn \wrt d" := (limit d xn x) (at level 4).
  
  Global Instance lim_prpr M d:
    Proper (@eqfun M nat ==> @set_equiv M) (limit d).
  Proof.
    move => xn yn eq x.
    split => lim eps eg0; have [N prp]:= lim eps eg0; exists N => m.
    - by rewrite -(eq m); apply/prp.
    by rewrite (eq m); apply/prp.
  Qed.

  Implicit Types (x y z: M).

  Lemma lim_dst xn x y: x \limits xn \wrt d -> y \limits xn \wrt d -> d(x,y) = 0.
  Proof.
    move => limxnx limxnx'.
    apply/cond_eq => eps epsg0.
    rewrite Rminus_0_r Rabs_pos_eq; last exact/dst_pos.
    have [ | N Nprp]:= limxnx (eps/3); try lra.
    have [ | N' N'prp]:= limxnx' (eps/3); try lra.
    pose k:= maxn N N'.
    apply/dst_lt; first exact/Nprp/leq_maxl/N'.
    - rewrite dst_sym; apply/N'prp/leq_maxr.
    lra.
  Qed.

  Lemma lim_cnst x: x \limits (cnst x) \wrt d.
  Proof.
    exists 0%nat; rewrite/cnst dstxx; intros.
    lra.
  Qed.
  
  Lemma lim_tpmn xn x: x \limits xn \wrt d <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof.
  split => [lim n | lim eps eg0].
  - have [ | N prp]:= lim (/2 ^ n); first by apply/Rinv_0_lt_compat/pow_lt; lra.
    by exists N.
  have [n ineq]:= accf_tpmn eg0.
  have [N prp]:= lim n.
  exists N => m Nlm.
  exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
  Qed.
  
  Lemma dst0_tpmn x y:
    (forall n, d(x,y) <= / 2 ^ n) <-> d(x,y) = 0.
  Proof.
    split => [prp | ->]; last exact/tpmn_pos.
    apply/cond_eq_f => [ | n ineq]; first exact/accf_tpmn.
    rewrite /R_dist Rminus_0_r Rabs_pos_eq; first exact/prp.
    exact/dst_pos.
  Qed.
End limits.
Notation "xn \converges_to x \wrt d" := (limit d xn x) (at level 23): metric_scope.

Section density.
  Context `{pm: pseudometric}.

  Definition dense_subset (A: subset M):=
    forall x eps, eps > 0 -> exists y, y \from A /\ d(x,y) <= eps.

  Global Instance dns_prpr: Proper (@set_equiv M ==> iff) dense_subset.
  Proof.
    move => A B eq; split => dns x eps eg0; have [y []]:= dns x eps eg0; exists y.
    - by rewrite -eq.
    by rewrite eq.
  Qed.
    
  Lemma dns_tpmn (A: subset M):
    dense_subset A <-> forall x n, exists y, y \from A /\ d(x,y) <= /2^n.
  Proof.
    split => [dns x n | dns x eps eg0]; first by apply/dns/Rlt_gt/Rinv_0_lt_compat/pow_lt; lra.
    have [n ineq]:= accf_tpmn eg0.
    have [y []]:= dns x n.
    exists y; split => //.
    exact/Rlt_le/Rle_lt_trans/ineq.2.
  Qed.

  Definition sequence := nat -> M.
  
  Definition dense_sequence (r: sequence) :=
    forall x eps, 0 < eps -> exists n, d(x,r n) <= eps.

  Lemma dseq_dns (r: sequence):
    dense_sequence r <-> dense_subset (codom (F2MF r)). 
  Proof.
    split => dns x eps eg0; have []:= dns x eps eg0.
    - by move => n ineq; exists (r n); split => //; exists n.
    by move => y [[n <-] ineq]; exists n.
  Qed.

  Lemma dseq_tpmn (r: sequence):
    dense_sequence r <-> forall x n, exists m, d(x,r m) <= /2^n.
  Proof.
    split => [dns x n| dns x eps eg0]; first apply/dns.
    - by apply/Rinv_0_lt_compat/pow_lt; lra.
    have [n ineq]:= accf_tpmn eg0.
    have [m prp]:= dns x n.
    exists m.
    exact/Rlt_le/Rle_lt_trans/ineq.2/prp.
  Qed.

  Definition closure A := make_subset (fun (x: M) =>
    forall eps, 0 < eps -> exists y, y \from A /\ d(x,y) <= eps).

  Lemma subs_clos A: A \is_subset_of closure A.
  Proof. by move => x Ax eps epsg0; exists x; split; last rewrite dstxx; try lra. Qed.

  Lemma dns_clos A: dense_subset A <-> closure A === All.
  Proof.
    split => [dns x | eq x]; first by split => // _; apply/dns.
    by have [_ prp]:= eq x; apply/prp.
  Qed.
End density.
Notation sequence_in M := (@sequence M).
Arguments dense_subset: clear implicits.
Arguments dense_subset {M} (d).
Notation "A \dense_subset_wrt d" := (dense_subset d A) (at level 35): metric_scope.
Arguments dense_sequence: clear implicits.
Arguments dense_sequence {M} (d).
Notation "xn \dense_wrt d":= (dense_sequence d xn) (at level 35): metric_scope.
Notation "xn \dense_sequence_wrt d":= (dense_sequence d xn) (at level 35): metric_scope.
Arguments closure: clear implicits.
Arguments closure {M} (d).
Notation "A \closed_wrt d":= (closure d A) (at level 35): metric_scope.

Section Cauchy_sequences.
  Context `{pm: pseudometric}.
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  Notation limit := (limit d).

  Definition Cauchy_sequence xn :=
    forall eps, 0 < eps -> exists N, forall n m,
          (N <= n)%nat -> (N <= m)%nat -> d(xn n, xn m) <= eps.

  Definition Cauchy_sequences := make_subset Cauchy_sequence.
  
  Lemma lim_cchy: dom limit \is_subset_of Cauchy_sequences.
  Proof.
    move => xn [x lim] eps eg0.
    have [ | N prp]:= lim (eps/2); first by lra.
    exists N => n m ineq ineq'.
    apply/dst_le;first by rewrite dst_sym; apply/prp.
    - exact/prp.
    lra.
  Qed.
  
  Definition complete := Cauchy_sequences \is_subset_of dom limit.
      
  Lemma cchy_tpmn xn: Cauchy_sequence xn <->
    (forall k, exists N, forall n m,
            (N <= n <= m)%nat -> d (xn n, xn m) <= /2^k).
  Proof.
    split => [cchy k | ass eps epsg0].
    - have [ | N prp]:= cchy (/2 ^ k).
      + by apply/Rinv_0_lt_compat/pow_lt; lra.
      exists N => n m /andP [ineq ineq'].
      exact/prp/leq_trans/ineq'.
    have [N [g0 /Rlt_le ineq]]:= accf_tpmn epsg0.
    have [N' N'prp]:= ass N.
    exists N' => n m nineq mineq.
    case/orP: (leq_total n m) => ineq'.
    - by apply/Rle_trans; first exact/N'prp/andP.
    by rewrite dst_sym; apply/Rle_trans; first apply/N'prp/andP.
  Qed.

  Definition eventually_big mu:= forall (n: nat), exists N, forall m,
          (N <= m)%nat -> (n <= mu m)%nat.

  Lemma lim_evb xn mu (x: M): limit xn x -> eventually_big mu -> limit (xn \o_f mu) x.
  Proof.
    move => lim evb eps eg0.
    have [N prp]:= lim eps eg0.
    have [N' ineq]:= evb N.
    exists N' => m ineq'.
    exact/prp/ineq/ineq'. 
  Qed.
  
  Lemma cchy_evb xn mu: Cauchy_sequence xn -> eventually_big mu -> Cauchy_sequence (xn \o_f mu).
  Proof.
    move => cchy evb eps eg0.
    have [N prp]:= cchy eps eg0.
    have [N' le]:= evb N.
    exists N' => n m ineq ineq'; apply/prp/le; last exact/ineq'.
    exact/le/ineq.
  Qed.
End Cauchy_sequences.
Arguments Cauchy_sequence: clear implicits.
Arguments Cauchy_sequence {M} (d).
Arguments Cauchy_sequences: clear implicits.
Arguments Cauchy_sequences {M} (d).
Notation "xn \Cauchy_wrt d" := (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \Cauchy_sequence_wrt d" := (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \is_Cauchy_wrt d" := (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \is_Cauchy_sequence_wrt d" :=
  (xn \from Cauchy_sequences d) (at level 45): metric_scope.
Arguments complete: clear implicits.
Arguments complete {M} (d).
Notation "d \is_complete" := (complete d) (at level 45): metric_scope.
Notation "d \is_complete_metric" := (complete d) (at level 45): metric_scope.

Section efficient_convergence.
  Context `{pm: pseudometric}.
  Local Notation limit := (limit d).
  Local Notation Cauchy_sequence := (Cauchy_sequence d).
  Local Notation Cauchy_sequences:= (Cauchy_sequences d).
  Local Notation complete := (complete d).

  Definition fast_Cauchy_sequence xn :=
    forall n m, d (xn n,xn m) <= /2^n + /2^m.

  Definition fast_Cauchy_sequences := make_subset fast_Cauchy_sequence.
  
  Lemma fchy_cchy: fast_Cauchy_sequences \is_subset_of Cauchy_sequences.
  Proof.
    move => xn cchy eps epsg0.
    have [N [_ ineq]]:= accf_tpmn epsg0.
    exists N.+1 => n m nineq mineq.
    apply/Rlt_le/Rle_lt_trans; last exact/ineq.
    apply /Rle_trans; [exact/cchy | rewrite (tpmn_half N)].
    by apply/Rplus_le_compat; apply/Rinv_le_contravar;
      try apply/pow_lt; try apply/Rle_pow/leP => //; try lra.
  Qed.

  Definition efficient_limit := make_mf (fun xn (x: M) =>
    forall n, d(x, xn n) <= /2^n).
  
  Lemma lim_eff_spec: efficient_limit =~= limit|_(fast_Cauchy_sequences).
  Proof.
    move => xn x; split => [lim | [fchy lim] n].
    - split => [n m | eps epsg0].
      apply/dst_le/Rle_refl/lim; first by rewrite dst_sym; apply/lim.
      have [n ineq]:= accf_tpmn epsg0.
      exists n => m nlm.
      apply/Rlt_le/Rle_lt_trans/ineq.2/Rle_trans; first exact/lim.
      apply/Rinv_le_contravar; first by apply/pow_lt; lra.
      by apply/Rle_pow/leP => //; lra.
    suff all: forall m, d(x, xn n) <= / 2 ^ n + / 2 ^ m.
    - suff: d(x, xn n) - / 2 ^ n <= 0 by lra.
      apply/Rnot_lt_le => ineq.
      have [m ineq']:= accf_tpmn ineq.
      by have := all m; lra.
    move => m.  
    have [ | N prp]:= lim (/2 ^ m.+1); first by apply/Rinv_0_lt_compat/pow_lt; lra.
    rewrite (tpmn_half m) -Rplus_assoc Rplus_comm.
    apply/Rle_trans/Rplus_le_compat.
    - + exact/(dst_trngl (xn (maxn m.+1 N))).
    - exact/prp/leq_maxr.
    rewrite dst_sym; apply/Rle_trans; first exact/fchy.
    apply/Rplus_le_compat_l/Rinv_le_contravar/Rle_pow/leP/leq_maxl; try lra.
    by apply/pow_lt; lra.
  Qed.
    
  Lemma lim_eff_lim : limit \extends efficient_limit.
  Proof.
    rewrite lim_eff_spec {2}[limit]restr_all.
    exact/exte_restr/subs_all.
  Qed.

  Lemma fchy_lim_eff: complete ->
    fast_Cauchy_sequences === dom efficient_limit.
  Proof.
    move => cmplt xn; split => [cchy | [x /lim_eff_spec []]]//.
    rewrite lim_eff_spec dom_restr_spec; split => //.
    exact/cmplt/fchy_cchy.
  Qed.  

  Lemma lim_eff_dst xn x y: efficient_limit xn x -> efficient_limit xn y -> d(x, y) = 0.
  Proof. by move => lim lim'; apply/lim_dst/lim_eff_lim/lim'/lim_eff_lim/lim. Qed.

  Lemma lim_tight_lim_eff: limit \tightens efficient_limit.
  Proof.
    move => xn [x lim]; split => [ | y lim' n]; first by exists x; apply/lim_eff_lim.
    apply/Rle_trans; first exact/(dst_trngl x).
    have ->: d(y, x) = 0 by apply/lim_dst/lim_eff_lim/lim.
    by rewrite Rplus_0_l; apply/lim.
  Qed.

  Lemma cchy_eff_suff xn:
    (forall n m, (n <= m)%nat -> d (xn n, xn m) <= /2^n + /2^m) ->
    fast_Cauchy_sequence xn.
  Proof.
    move => ass n m.
    case /orP: (leq_total n m) => ineq; first by apply ass.
    by rewrite dst_sym Rplus_comm; apply ass.
  Qed.
End efficient_convergence.
Arguments fast_Cauchy_sequence: clear implicits.
Arguments fast_Cauchy_sequence {M} (d).
Arguments fast_Cauchy_sequences: clear implicits.
Arguments fast_Cauchy_sequences {M} (d).
Notation "xn \fast_Cauchy_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \fast_Cauchy_sequence_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): metric_scope.
Notation "xn \is_fast_Cauchy_sequence_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): metric_scope.
Arguments efficient_limit: clear implicits.
Arguments efficient_limit {M} (d).
Notation "x \efficient_limit_of xn \wrt d" := (efficient_limit d xn x) (at level 45): metric_scope.

Section continuity.
  Context `{pm: pseudometric}.
  Context `{pm0: pseudometric}.
  Context (f: M -> M0).
  Implicit Types (x y: M) (xn yn: sequence_in M).
  
  Definition continuity_point x :=
    forall eps, 0 < eps -> exists delta, 0 < delta /\ forall y, d(x,y) <= delta -> d0(f x, f y) <= eps.

  Definition continuity_points := make_subset continuity_point.

  Definition continuous:= forall x, continuity_point x.

  Lemma cntp_all: continuous <-> continuity_points === All.
  Proof.
    split => [cont x | eq x]; last exact/eq.
    by split => // _; apply/cont.
  Qed.
  
  Definition sequential_continuity_point x:=
    forall xn, xn \converges_to x \wrt d -> (ptw f xn) \converges_to (f x) \wrt d0.

  Definition sequential_continuity_points := make_subset sequential_continuity_point.

  Definition sequentially_continuous:=
    forall x, sequential_continuity_point x.

  Lemma scntp_all: sequentially_continuous <-> sequential_continuity_points === All.
  Proof.
    split => [cont x | eq x]; last exact/eq.
    by split => // _; apply/cont.
  Qed.
  Lemma cntp_scntp x: continuity_point x -> sequential_continuity_point x.
  Proof.
    move => cont xn lmt eps eg0.
    have [delta [dg0 prp]]:= cont eps eg0.
    have [N' cnd]:= lmt delta dg0.
    exists N' => m ineq.
    exact/prp/cnd.
  Qed.

  Lemma cont_scnt: continuous -> sequentially_continuous.
  Proof. by move => cont x; apply/cntp_scntp. Qed.
End continuity.
Arguments continuity_point: clear implicits.
Arguments continuity_point {M} (d) {M0} (d0).
Arguments continuity_points: clear implicits.
Arguments continuity_points {M} (d) {M0} (d0).
Notation "f \continuous_wrt d \and d0 \in x" :=
  (continuity_point d d0 f x) (at level 35): metric_scope.
Notation continuous_wrt d d0 := (@continuous _ d _ d0).
Notation "f \continuous_wrt d \and d0" :=
  (continuous_wrt d d0 f) (at level 2): metric_scope.
Notation "f \is_continuous_wrt d \and d0" :=
  (continuous_wrt d d0 f) (at level 2): metric_scope.
Arguments sequential_continuity_points: clear implicits.
Arguments sequential_continuity_points {M} (d) {M0} (d0).
Arguments sequential_continuity_point: clear implicits.
Arguments sequential_continuity_point {M} (d) {M0} (d0).
Arguments sequentially_continuous: clear implicits.
Arguments sequentially_continuous {M} (d) {M0} (d0).
Notation "f \sequentially_continuous_wrt d \and d0 \in x" :=
  (sequential_continuity_point d d0 f x) (at level 40): metric_scope.
Notation "f \sequentially_continuous_wrt d \and d0" :=
  (sequentially_continuous d d0 f) (at level 40): metric_scope.
Notation "f \is_sequentially_continuous_wrt d \and d0" :=
  (sequentially_continuous d d0 f) (at level 40): metric_scope.

Section subpseudometric.
  Context `{pm: pseudometric}.
  Global Instance sub_pseudo_metric (A: subset M):
    (fun xy => d (sval xy.1, sval xy.2)) \is_pseudo_metric_on {x | x \from A}.
    split; first by move => x y; apply/dst_pos.
    - by move => x y; apply/dst_sym.
    - by move => x; apply/dstxx.
    by move => x y z; apply/dst_trngl.
  Defined.
End subpseudometric.