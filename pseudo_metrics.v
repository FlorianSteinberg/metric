From mathcomp Require Import ssreflect seq ssrfun ssrbool ssrnat.
From mf Require Import all_mf.
Require Import pointwise reals.
Require Import Reals Psatz Morphisms ChoiceFacts Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Delimit Scope pseudometric_scope with pmetric.
Local Open Scope pseudometric_scope.
Local Open Scope R_scope.
Section pseudometrics.
  Class is_pseudometric `{M: Type} (d: M * M -> R) :=
    {
      positive: forall x y, 0 <= d(x,y);
      symmetric: forall x y, d(x,y) = d(y,x);
      reflexive: forall x, d(x,x) = 0;
      triangle_inequality: forall x y z, d(x,y) <= d(x,z) + d(z,y);
    }.
  Local Notation "p /is_pseudometric":= (is_pseudometric p) (at level 30).
  
  Context `{is_pseudometric}.
  Implicit Types (x y z: M).

  Lemma dst_pos x y: 0 <= d(x,y).
  Proof. by apply positive. Qed.

  Lemma dst_sym x y: d(x,y) = d(y,x).
  Proof. by apply symmetric. Qed.

  Lemma dstxx x: d(x,x) = 0.
  Proof. by apply reflexive. Qed.

  Lemma dst_trngl z x y: d(x,y) <= d(x,z) + d(z,y).
  Proof. by apply triangle_inequality. Qed.
  
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
Notation "d \is_pseudometric_on M" := (@is_pseudometric M d) (at level 36): pseudometric_scope.
Notation "d \is_pseudometric" := (is_pseudometric d) (at level 36): pseudometric_scope.

Delimit Scope metric_scope with metric.
Local Open Scope metric_scope.
Section limits.
  Context `{is_pseudometric}.
  Definition limit M (d: M * M -> R) := make_mf (fun xn x =>
    forall eps, 0 < eps -> exists N, forall m,
          (N <= m)%nat -> d (x,xn m) <= eps).

  Local Notation "x \limits xn \wrt d" := (limit d xn x) (at level 4).
  Local Notation "x \is_limit_of xn \wrt d" := (limit d xn x) (at level 4).
  
  Global Instance lim_prpr M' d': Proper (@eqfun M' nat ==> @set_equiv M') (limit d').
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
    rewrite Rminus_0_r Rabs_pos_eq; last by apply dst_pos.
    have [ | N Nprp]:= limxnx (eps/3); try lra.
    have [ | N' N'prp]:= limxnx' (eps/3); try lra.
    pose k:= maxn N N'.
    apply/(@dst_lt _ _ H); first by apply/Nprp/leq_maxl/N'.
    - rewrite dst_sym; apply/N'prp/leq_maxr.
    lra.
  Qed.

  Lemma lim_cnst x: x \limits (cnst x) \wrt d.
  Proof. by exists 0%nat; rewrite/cnst dstxx; intros; lra. Qed.
  
  Lemma lim_tpmn xn x: x \limits xn \wrt d <->
    (forall n, exists N, forall m, (N <= m)%nat -> d(x,xn m) <= /2 ^ n).
  Proof.
    split => [lim n | lim eps eg0].
    - case: (lim (/2 ^ n)) => [ | N]; last by exists N.
      by apply/Rinv_0_lt_compat/pow_lt; lra.
    have [n [? ineq]]:= accf_tpmn eg0.
    have [N prp]:= lim n; exists N => ? ?.
    exact/Rlt_le/Rle_lt_trans/ineq/prp.
  Qed.
  
  Lemma dst0_tpmn x y: d(x,y) = 0 <-> forall n, d(x,y) <= / 2 ^ n.
  Proof.
    split => [-> | ?]; first exact/tpmn_pos.
    apply/cond_eq_f; first exact/accf_tpmn.
    rewrite /R_dist Rminus_0_r Rabs_pos_eq //.
    by apply dst_pos.
  Qed.

  Lemma lim_lim_choice xnk xn x:
    FunctionalCountableChoice_on nat ->
    (forall n, (xn n) \limits (xnk n) \wrt d) -> x \limits xn \wrt d ->
    exists mu, x \limits (fun n => xnk n (mu n)) \wrt d.
  Proof.
    move => choice lmtlmt /lim_tpmn lmt.
    have /choice [mu muprp]:
      forall n, exists m, forall k, (m <= k)%nat -> d (xn n, xnk n k) <= /2 ^ n.
    - by move => n; apply/(lmtlmt n (/2^n))/Rinv_0_lt_compat/pow_lt; lra.
    exists mu.
    apply/lim_tpmn => n.
    have [N prp]:= lmt (n.+1).
    exists (maxn n.+1 N) => k ineq.
    apply/(le_dst _)/muprp => //; last exact/prp/leq_trans/ineq/leq_maxr.
    rewrite [X in _ <= X]tpmn_half.
    apply/Rplus_le_compat/Rinv_le_contravar/Rle_pow/leP/leq_trans/ineq/leq_maxl; try lra.
    by apply/pow_lt; lra.
  Qed.    
End limits.
Notation "xn \converges_to x \wrt d" := (limit d xn x) (at level 23): pseudometric_scope.

Section density.
  Context `{pm: is_pseudometric}.

  Definition dense_subset (A: subset M):=
    forall x eps, eps > 0 -> exists y, y \from A /\ d(x,y) <= eps.

  Global Instance dns_prpr: Proper (@set_equiv M ==> iff) dense_subset.
  Proof.
    move => A B eq; split => dns x eps eg0; have [y []]:= dns x eps eg0; exists y.
    - by rewrite <-eq.
    by rewrite ->eq.
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

  Local Notation sequence := (nat -> M).
  
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
    have [n [_ ineq]]:= accf_tpmn eg0.
    have [m prp]:= dns x n.
    exists m.
    exact/Rlt_le/Rle_lt_trans/ineq/prp.
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

  Lemma clos_spec_choice A x:
    FunctionalCountableChoice_on M ->
    x \from closure A <->
                     exists (xn: sequence), (forall n, xn n \from A) /\ xn \converges_to x \wrt d.
  Proof.
    move => choice; split => [clos | [xn [prp lmt]] eps eg0].
    - have /choice [xn prp]: forall n, exists y, d(y, x) <= /2^n /\ A y.
      + move => n.
        have [ | y []]:= clos (/2^n); first by apply/Rinv_0_lt_compat/pow_lt; lra.
        by exists y; rewrite dst_sym.
      exists xn; split => [n | ]; first by have []:= prp n.
      apply/lim_tpmn => n; exists n => k ineq.
      rewrite dst_sym; apply/Rle_trans; first exact/(prp k).1.
      apply/Rinv_le_contravar/Rle_pow/leP => //; try lra.
      by apply/pow_lt; lra.
    have [n cnd]:= lmt eps eg0.
    by exists (xn n); split; [apply/prp | apply/(cnd n)].
  Qed.
End density.
Notation sequence_in M := (nat -> M).
Arguments dense_subset: clear implicits.
Arguments dense_subset {M} (d).
Notation "A \dense_subset_wrt d" := (dense_subset d A) (at level 35): pseudometric_scope.
Arguments dense_sequence: clear implicits.
Arguments dense_sequence {M} (d).
Notation "xn \dense_wrt d":= (dense_sequence d xn) (at level 35): pseudometric_scope.
Notation "xn \dense_sequence_wrt d":= (dense_sequence d xn) (at level 35): pseudometric_scope.
Arguments closure: clear implicits.
Arguments closure {M} (d).
Notation "A \closed_wrt d":= (closure d A) (at level 35): pseudometric_scope.

Section Cauchy_sequences.
  Context `{is_pseudometric}.
  Implicit Types (x y z: M) (xn yn: sequence_in M).
  Notation limit := (limit d).

  Definition Cauchy_sequences := make_subset (fun xn =>
    forall eps, 0 < eps -> exists N, forall n m, (N <= n)%nat -> (N <= m)%nat -> d(xn n, xn m) <= eps).
  
  Lemma lim_cchy: dom limit \is_subset_of Cauchy_sequences.
  Proof.
    move => xn [x lim] eps eg0.
    have [ | N prp]:= lim (eps/2); first by lra.
    exists N => n m ineq ineq'.
    apply/(@dst_le _ _ H); try exact/prp; first by rewrite dst_sym; apply/prp.
    lra.
  Qed.
  
  Definition complete := Cauchy_sequences \is_subset_of dom limit.
      
  Lemma cchy_tpmn xn: xn \from Cauchy_sequences <->
    forall k, exists N, forall n m, (N <= n <= m)%nat -> d (xn n, xn m) <= /2^k.
  Proof.
    split => [cchy k | ass eps /dns0_tpmn [N /Rlt_le ineq]].
    - have [ | N prp]:= cchy (/2 ^ k); first exact/tpmn_lt.
      by exists N => n m /andP [? ineq]; apply/prp/leq_trans/ineq.
    have [N' N'prp]:= ass N; exists N' => n m ? ?.
    case/orP: (leq_total n m) => ineq'.
    - by apply/Rle_trans; first exact/N'prp/andP.
    by rewrite dst_sym; apply/Rle_trans; first apply/N'prp/andP.
  Qed.

  Definition Cauchy_sequences_with_modulus mu := make_subset (fun xn =>
    forall k n m, (mu k <= n <= m)%nat -> d (xn n, xn m) <= /2^k).

  Lemma chym_subs mu: Cauchy_sequences_with_modulus mu \is_subset_of Cauchy_sequences.
  Proof. by move => xn chy; apply/cchy_tpmn => k; exists (mu k); apply/chy. Qed.
    
  Lemma cchy_mod_exists_choice xn:
    FunctionalCountableChoice_on nat ->
    xn \from Cauchy_sequences <-> exists mu, xn \from Cauchy_sequences_with_modulus mu.
  Proof. by move => choice; split => [/cchy_tpmn /choice | [mu]]//; apply/chym_subs. Qed.

  Definition eventually_big mu:= forall (n: nat), exists N, forall m, (N <= m)%nat -> (n <= mu m)%nat.

  Lemma lim_evb xn mu (x: M): limit xn x -> eventually_big mu -> limit (xn \o_f mu) x.
  Proof.
    move => lim evb eps eg0.
    have [N prp]:= lim eps eg0.
    have [N' ineq]:= evb N.
    exists N' => m ineq'.
    exact/prp/ineq/ineq'. 
  Qed.
  
  Lemma cchy_evb xn mu:
    xn \from Cauchy_sequences -> eventually_big mu -> (xn \o_f mu) \from Cauchy_sequences.
  Proof.
    move => cchy evb eps /cchy [N prp].
    have [N' le]:= evb N.
    exists N' => n m ineq ineq'; apply/prp/le/ineq'.
    exact/le/ineq.
  Qed.
End Cauchy_sequences.
Arguments Cauchy_sequences: clear implicits.
Arguments Cauchy_sequences {M} (d).
Notation "xn \Cauchy_wrt d" := (xn \from Cauchy_sequences d) (at level 45): pseudometric_scope.
Notation "xn \Cauchy_sequence_wrt d" := (xn \from Cauchy_sequences d) (at level 45): pseudometric_scope.
Notation "xn \is_Cauchy_wrt d" := (xn \from Cauchy_sequences d) (at level 45): pseudometric_scope.
Notation "xn \is_Cauchy_sequence_wrt d" :=
  (xn \from Cauchy_sequences d) (at level 45): pseudometric_scope.
Arguments complete: clear implicits.
Arguments complete {M} (d).
Notation "d \is_complete" := (complete d) (at level 45): pseudometric_scope.
Notation "d \is_complete_metric" := (complete d) (at level 45): pseudometric_scope.

Section efficient_convergence.
  Context `{pm: is_pseudometric}.
  Local Notation limit := (limit d).
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
      apply/(@dst_le _ _ pm)/Rle_refl/lim; first by rewrite dst_sym; apply/lim.
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
    - by apply (dst_trngl (xn (maxn m.+1 N))).
    - exact/prp/leq_maxr.
    rewrite dst_sym; apply/Rle_trans; first exact/fchy.
    apply/Rplus_le_compat_l/Rinv_le_contravar/Rle_pow/leP/leq_maxl; try lra.
    by apply/pow_lt; lra.
  Qed.
    
  Lemma lim_eff_lim : limit \extends efficient_limit.
  Proof.
    rewrite ->lim_eff_spec.
    rewrite {2}[limit]restr_all.
    exact/exte_restr/subs_all.
  Qed.

  Lemma fchy_lim_eff: complete -> fast_Cauchy_sequences === dom efficient_limit.
  Proof.
    move => cmplt xn; split => [cchy | [x /lim_eff_spec []]]//.
    rewrite ->lim_eff_spec; rewrite ->dom_restr_spec; split => //.
    exact/cmplt/fchy_cchy.
  Qed.  

  Lemma cchy_fchy_choice xn: FunctionalCountableChoice_on nat ->
    xn \Cauchy_wrt d -> exists mu, (xn \o_f mu) \from fast_Cauchy_sequences.
  Proof.
    move => choice /cchy_tpmn /choice [mu prp].    
    exists mu => n k /=.
    case/orP: (leq_total (mu n) (mu k)) => ineq.
    - apply/Rle_trans; first by apply/prp/andP.
      rewrite -[X in X <= _]Rplus_0_r; apply/Rplus_le_compat_l.
      by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    rewrite dst_sym; apply/Rle_trans; first by apply/prp/andP.
    rewrite -[X in X <= _]Rplus_0_l; apply/Rplus_le_compat_r.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  Qed.

  Lemma lim_eff_dst xn x y: efficient_limit xn x -> efficient_limit xn y -> d(x, y) = 0.
  Proof. by move => lim lim'; apply/(@lim_dst _ _ pm)/lim_eff_lim/lim'/lim_eff_lim/lim. Qed.

  Lemma lim_tight_lim_eff: limit \tightens efficient_limit.
  Proof.
    move => xn [x lim]; split => [ | y lim' n]; first by exists x; apply/lim_eff_lim.
    apply/Rle_trans; first by apply (dst_trngl x).
    have ->: d(y, x) = 0 by apply/(@lim_dst _ _ pm)/lim_eff_lim/lim.
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
  (xn \from fast_Cauchy_sequences d) (at level 45): pseudometric_scope.
Notation "xn \fast_Cauchy_sequence_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): pseudometric_scope.
Notation "xn \is_fast_Cauchy_sequence_wrt d" :=
  (xn \from fast_Cauchy_sequences d) (at level 45): pseudometric_scope.
Arguments efficient_limit: clear implicits.
Arguments efficient_limit {M} (d).
Notation "x \efficient_limit_of xn \wrt d" := (efficient_limit d xn x) (at level 45): pseudometric_scope.

Section continuity.
  Context `{pm: is_pseudometric}.
  Context `{pm0: is_pseudometric}.
  Context (f: M -> M0).
  Implicit Types (x y: M) (xn yn: sequence_in M).
  
  Definition continuity_point x :=
    forall eps, 0 < eps -> exists delta, 0 < delta /\ forall y, d(x,y) <= delta -> d0(f x, f y) <= eps.

  Lemma cntp_tpmn x:
    continuity_point x <-> forall n, exists m, forall x', d (x, x') <= /2^m -> d0 (f x, f x') <= /2^n.
  Proof.
    split => [cont n | cont eps /dns0_tpmn [n ineq]].
    - have [delta [/dns0_tpmn [m ineq] prp]]:= cont (/2^n) (tpmn_lt n).
      by exists m => x' dst; apply/prp/Rlt_le/Rle_lt_trans/ineq.
    have [m prp]:= cont n.
    exists (/2^m); split => [ | y dst]; first exact/tpmn_lt.
    exact/Rlt_le/Rle_lt_trans/ineq/prp.
  Qed.

  Definition continuity_points := make_subset continuity_point.

  Definition continuous:= forall x, continuity_point x.

  Lemma cont_tpmn:
    continuous <-> forall x n, exists m, forall x', d (x, x') <= /2^m -> d0 (f x, f x') <= /2^n.
  Proof. by split => cont x; apply/cntp_tpmn. Qed.

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

  Lemma scnt_cont_choice:
    FunctionalCountableChoice_on M -> sequentially_continuous -> continuous.
  Proof.    
    move => choice scnt x eps eg0.
    apply/not_all_not_ex => prp.
    have /choice [xn xnprp]: forall n, exists y, d(x, y) <= /2^n /\ eps < d0(f x, f y).
    - move => n; have /not_and_or [ | cnd]:= (prp (/2 ^ n)).
      + by have : 0 < /2^n by apply/Rinv_0_lt_compat/pow_lt; lra.
      apply/not_all_not_ex => asd.
      apply/cnd => y dst.
      have /not_and_or [ineq | ineq]:= asd y; last exact/Rnot_lt_le.
      lra.
    have lmt: xn \converges_to x \wrt d.
    - rewrite ->lim_tpmn => n.
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
Arguments continuity_point: clear implicits.
Arguments continuity_point {M} (d) {M0} (d0).
Arguments continuity_points: clear implicits.
Arguments continuity_points {M} (d) {M0} (d0).
Notation "f \continuous_wrt d \and d0 \in x" :=
  (continuity_point d d0 f x) (at level 35): pseudometric_scope.
Notation continuous_wrt d d0 := (@continuous _ d _ d0).
Notation "f \continuous_wrt d \and d0" :=
  (continuous_wrt d d0 f) (at level 30): pseudometric_scope.
Notation "f \is_continuous_wrt d \and d0" :=
  (continuous_wrt d d0 f) (at level 30): pseudometric_scope.
Arguments sequential_continuity_points: clear implicits.
Arguments sequential_continuity_points {M} (d) {M0} (d0).
Arguments sequential_continuity_point: clear implicits.
Arguments sequential_continuity_point {M} (d) {M0} (d0).
Arguments sequentially_continuous: clear implicits.
Arguments sequentially_continuous {M} (d) {M0} (d0).
Notation "f \sequentially_continuous_wrt d \and d0 \in x" :=
  (sequential_continuity_point d d0 f x) (at level 40): pseudometric_scope.
Notation "f \sequentially_continuous_wrt d \and d0" :=
  (sequentially_continuous d d0 f) (at level 40): pseudometric_scope.
Notation "f \is_sequentially_continuous_wrt d \and d0" :=
  (sequentially_continuous d d0 f) (at level 40): pseudometric_scope.

Section subpseudometric.
  Context `{pm: is_pseudometric}.
  Global Instance sub_pseudo_metric (A: subset M):
    (fun xy => d (sval xy.1, sval xy.2)) \is_pseudometric_on {x | x \from A}.
    split; first by move => x y; apply dst_pos.
    - by move => x y; apply dst_sym.
    - by move => x; apply dstxx.
    by move => x y z; apply dst_trngl.
  Defined.
End subpseudometric.
