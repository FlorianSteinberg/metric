From mathcomp Require Import ssreflect ssrfun seq ssrnat ssrbool.
From mf Require Import all_mf.
Require Import FunctionalExtensionality ClassicalChoice ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section pointwise.
  Context (I: Type).
  Definition mf_ptw R T (f: R ->> T):= make_mf (fun rs ts =>
    forall (i: I), f (rs i) (ts i)).

  Lemma ptw_sur R T (f: R ->> T): f \is_cototal -> (mf_ptw f) \is_cototal.
  Proof.
    move => cotot ts.
    have /choice [rs prp] := cotot.
    exists (rs \o_f ts) => i; exact/prp.
  Qed.

  Lemma ptw_sing R T (f: R ->> T):
    f \is_singlevalued -> (mf_ptw f) \is_singlevalued.
  Proof.
    move => sing rs ts t's val val'.
    apply/functional_extensionality => i.
    exact/sing/val'/val.
  Qed.

  Definition ptw R T (f: R -> T) (rs: I -> R) i := f (rs i).
  
  Lemma ptw_comp R T (f: R -> T) rs: (ptw f rs) =1 f \o_f rs.
  Proof. done. Qed.

  Lemma F2MF_ptw R T (f: R -> T):
    mf_ptw (F2MF f) =~= F2MF (ptw f).
  Proof.
    move => rs ts /=; split => [prp | <-]//.
    exact/functional_extensionality.
  Qed.
  
  Definition ptw_op R S T (op: R -> S -> T) (rs: I -> R) (ss: I -> S) i:=
    op (rs i) (ss i).

  Lemma ptwA R (op: R -> R -> R): associative op -> associative (ptw_op op).
  Proof.
    by move => ass x y z; apply/functional_extensionality => n; apply/ass.
  Qed.

  Lemma ptwC R (op: R -> R -> R): commutative op -> commutative (ptw_op op).
  Proof.
    by move => ass x y; apply/functional_extensionality => n; apply/ass.
  Qed.

  Lemma ptwDl R (op op': R -> R -> R):
    left_distributive op op' -> left_distributive (ptw_op op) (ptw_op op').
  Proof.
    by move => ass x y z; apply/functional_extensionality => n; apply/ass.
  Qed.

  Lemma ptwDr R (op op': R -> R -> R):
    right_distributive op op' -> right_distributive (ptw_op op) (ptw_op op').
  Proof.
    by move => ass x y z; apply/functional_extensionality => n; apply/ass.
  Qed.  
  
  Definition curry R S T (f: R -> S -> T) rs := f rs.1 rs.2.
End pointwise.
Notation ptwn_op := (@ptw_op nat).
Notation ptwn := (@ptw nat).