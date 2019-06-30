(* Interface of MetricSpace type with types from the Coqeulicot Hierarchy *)
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
Require Import pointwise reals pseudo_metrics pseudo_metric_spaces metrics metric_spaces standard.
Require Import Reals Psatz Classical ChoiceFacts.
From Coquelicot Require Import Coquelicot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section infima.
  Local Open Scope metric_scope.
  Implicit Types (A: subset R).  

  Definition is_lower_bound A x:= forall a, a \from A -> x <= a.
  
  Definition lower_bounds A:= make_subset (fun x => is_lower_bound A x).

  Definition is_infimum A x := is_lower_bound A x /\ is_upper_bound (lower_bounds A) x.
  
  Lemma is_infimum_glb_Rbar A x:
    is_infimum A x <-> is_glb_Rbar A (Finite x).
  Proof.
    rewrite is_glb_Rbar_correct.
    split => [[lb inf] | [lb inf]].
    - split.
      + case; try by case.
        by move => y [_ Ay]; apply/lb.
      case => //[ y ass | ass].
      + apply/inf => z Az.
        have /=ass' := ass z.
        by apply/ass'.
      suff: (x + 1 <= x) by lra.
      apply/inf => y Ay; have /= ass' := ass (Finite y).
      by exfalso; apply/ass'.
    split => y Ay; first exact/(lb y).
    apply/(inf y); case => // [z [_ ] | []]//.
    exact/Ay.
  Qed.
  
  Definition mf_infimum:= make_mf is_infimum.

  Lemma inf_sing: mf_infimum \is_singlevalued.
  Proof.
    move => A inf inf' [bnd sup] [bnd' sup'].
    suff: inf <= inf' /\ inf' <= inf by lra.
    by split; [apply/sup' | apply/sup].
  Qed.
      
  Definition p_infimum A := match Glb_Rbar A with
                        | Finite r => Some r
                        | _ => None
                        end.

  Lemma p_inf_spec: PF2MF p_infimum =~= mf_infimum.
  Proof.
    move => A infA; rewrite /p_infimum /=.
    split => [/= | /is_infimum_glb_Rbar spec]; last by have -> := is_glb_Rbar_unique _ _ spec.
    case spec: (Glb_Rbar A) => [x | | ] // <-.
    apply/is_infimum_glb_Rbar; rewrite -spec.
    exact/Glb_Rbar_correct.
  Qed.
    
  Definition infimum A := match Glb_Rbar A with
                      | Finite r => r
                      | _ => 0
                      end.
  Notation inf := infimum.
  
  Lemma inf_icf: infimum \is_choice_for mf_infimum.
  Proof.
    rewrite /infimum => A [infA val].
    rewrite (is_glb_Rbar_unique A infA) //.
    exact/is_infimum_glb_Rbar.
  Qed.
  
  Definition nonempty A:= exists a, a \from A.

  Definition nonempties := make_subset nonempty.
  
  Definition bounded_from_below A := exists a, a \from lower_bounds A.

  Definition lower_boundeds:= make_subset bounded_from_below.
 
  Lemma dom_inf: dom mf_infimum === lower_boundeds \n nonempties.
  Proof.
    move => A; split => [[x [lb inf]] | [[y lb] [x Ax]]].
    - split; first by exists x.
      apply/not_all_not_ex => mty.
      suff: x + 1 <= x by lra.
      by apply/inf => y Ay; exfalso; apply/mty/Ay.
    have := lb x Ax.
    case => [ineq | eq]; last by exists x; split => [ | z lbz]; [rewrite -eq | exact/lbz].
    suff /countable_choice [xn xnprp]:
      forall n, exists (xn: M2PM metric_R), lower_bounds A xn
                           /\
                           exists z, A z /\ d (xn, z) <= /2^n.
    - have xnbnd: forall n, is_lower_bound A (xn n) by move => n; have []:= xnprp n.
      have /(@fchy_lim_eff R_MetricSpace R_cmplt) [infA lmt]:
        (xn: sequence_in (M2PM R_MetricSpace)) \fast_Cauchy.
      + apply cchy_eff_suff => n m nlm.
        have [_ [z [Az dst]]]:= xnprp m.
        have [_ [z' [Az' dst']]]:= xnprp n.
        have := xnbnd n z Az; have := xnbnd m z' Az'.
        by move : dst dst' => /=; split_Rabs; lra.
      exists infA.
      split => [z Az | x' lbx'].
      * apply/lim_inc/lim_cnst/lim_eff_lim/lmt.
        by move => n; rewrite/cnst; apply/xnbnd.
      apply/cond_leq => eps eg0.
      have /accf_tpmn [N [pos Nle]] : 0 < eps/2 by lra.
      have [_ [z [Az dst]]]:= xnprp N.
      have := lbx' z Az; have := lmt N.
      by move: dst => /=; split_Rabs; lra.
    suff prp: forall n, exists (xn: M2PM metric_R), lower_bounds A xn
                                   /\
                                   exists z, A z /\ d(xn, z) <= (x - y)/2^n.
    - move => n.
      have /accf_tpmn [N [pos Nlxy]]: 0 < /(x - y) by apply/Rinv_0_lt_compat; lra.
      have [xn [xnlb [z [Az dst]]]]:= prp (N + n)%nat.
      exists xn; split => //.
      exists z; split => //.
      have lt: 0 < 2^n by apply pow_lt; lra.
      have lt': 0< 2^N by apply/pow_lt; lra.
      apply/Rle_trans; first exact/dst.
      rewrite pow_add /Rdiv Rinv_mult_distr; try lra.
      rewrite -Rmult_assoc -{2}(Rmult_1_l (/2^n)).
      apply/Rmult_le_compat_r; first by apply/Rlt_le/Rinv_0_lt_compat.
      rewrite -(Rinv_r (2^N)); try lra.
      apply/Rmult_le_compat_r; first by apply/Rlt_le/Rinv_0_lt_compat.
      rewrite -(Rinv_involutive (2^N)); try lra.
      rewrite -(Rinv_involutive (x - y)); try lra.
      by apply/Rinv_le_contravar; lra.
    elim => [ | n [xn [xnlb [z [Az dst]]]]].
    - by exists y; split; last by exists x; split; last by simpl; split_Rabs; lra.
    case: (classic (exists z', A z' /\ d(xn, z') <= (x - y)/2^n.+1)) => [ex | /not_ex_all_not nex].
    - by exists xn.
    exists (xn + (x-y)/2^n.+1).
    split => [z' Az' |].
    - have /not_and_or [nAz' | /Rnot_le_lt dst']:= nex z'; first by exfalso; apply/nAz'.
      by have := xnlb z' Az'; move: dst' => /=; split_Rabs; lra.
    have /not_and_or [nAz | /Rnot_le_lt dst']:= nex z; first by exfalso; apply/nAz.
    exists z; split => //; have xnlz:= xnlb z Az.
    have xn'lz: xn + (x - y) /2^n.+1 <= z.    
    - have : 0 < (x - y) /2^n.+1 by apply/Rdiv_lt_0_compat/pow_lt; lra.
      by simpl in dst; move : dst' dst; rewrite [X in _ < X]/=; split_Rabs; lra.
    rewrite /Rdiv (tpmn_half n) in dst.
    by move: xn'lz dst' dst => /=; split_Rabs; lra.
  Qed.
  
  Lemma inf_spec A: A \from dom mf_infimum -> mf_infimum A (inf A).
  Proof. exact/inf_icf. Qed.

  Lemma inf_eq A r: A \from dom mf_infimum -> mf_infimum A r -> inf A = r.
  Proof.
    move => fd val.
    exact/inf_sing/val/inf_icf.
  Qed.

  Lemma inf_leq A x: A \from dom mf_infimum -> x \from A -> inf A <= x.
  Proof.
    move => Afd xfa.
    have [lb _]:= inf_icf Afd.
    exact/lb.
  Qed.

  Lemma bnds_inf_leq A x: A \from lower_boundeds -> x \from A -> inf A <= x.
  Proof.
    move => bnd elt; apply/inf_leq => //.
    by rewrite dom_inf; split; last exists x.
  Qed.
  
  Lemma inf_geq A x: A \from dom mf_infimum -> x \from lower_bounds A -> x <= inf A.
  Proof.
    move => Afd lb.
    have [lbs nf]:= inf_icf Afd.
    exact/nf.
  Qed.

  Lemma ne_inf_geq A x: A \from nonempties -> x \from lower_bounds A -> x <= inf A.
  Proof. by move => ne lb; apply/inf_geq; first by rewrite dom_inf; split => //; exists x. Qed.

  Lemma inf_approx A infA: mf_infimum A infA -> 
                      forall eps, 0 < eps -> exists x, x \from A /\ x <= infA + eps.
  Proof.
    move => [lb nf] eps eg0.
    apply/not_all_not_ex => all.
    have := nf (infA + eps).
    suff: infA + eps <= infA by lra.
    apply/nf => z Az.
    have /not_and_or [nAz | /Rnot_le_lt]:= all z; try lra.
    by exfalso; apply/nAz.
  Qed.
End infima.  
Notation inf:= infimum.

Section suprema.
  Definition mf_supremum:= make_mf (fun (A: subset R) => is_lub A).

  Definition supremum A:= iota (mf_supremum A).
  Notation sup := supremum.
End suprema.