Require Import Lists.List.
Require Import Bool.Bool.

Require Import SymbComp.Remove.

(*
  Facts about lists with no repeated elements
*)
Section distinct.
  Variable A : Type.

  Fixpoint distinct (l : list A) :=
    match l with
    | nil => True
    | (a :: l') => (~ In a l') /\ distinct l'
    end.

  Hypothesis decA : forall a a' : A, {a = a'} + {a <> a'}.

  Lemma distinct_remove a l
    : distinct l -> distinct (remove decA a l).
  Proof.
    induction l as [ | a' l IH ]; try tauto.
    destruct 1 as [ norepH distH ].
    unfold remove; fold (remove decA).
    destruct (decA a a') as [ <- | neH ]; auto.
    split; eauto using (in_remove_means_in_original decA).
  Qed.

End distinct.

(* How to make a distinct list *)
Section rem_dups.
  Variable A : Type.
  Hypothesis decA : forall a a' : A, {a = a'} + {a <> a'}.

  Fixpoint search (a : A) l : bool :=
    match l with
    | nil => false
    | cons a' l' => if decA a a' then true else search a l'
    end.

  Lemma search_imp_in a l : Is_true (search a l) -> In a l.
  Proof.
    induction l as [ | a' ]; auto.
    simpl; destruct (decA a a'); auto.
  Qed.

  Lemma in_imp_search a l : In a l -> Is_true (search a l).
  Proof.
    induction l as [ | a' ]; auto.
    simpl; destruct (decA a a') as [ <- | neH ].
    - simpl; auto.
    - destruct 1; auto.
      contradiction neH; auto.
  Qed.

  Lemma search_iff_in a l : Is_true (search a l) <-> In a l.
  Proof.
    constructor; auto using search_imp_in, in_imp_search.
  Qed.

  Lemma if_search_true {B : Type} {a l} (b b' : B)
    : In a l -> (if search a l then b else b') = b.
  Proof.
    case_eq (search a l); auto.
    intros nsearchH inH.
    pose proof (Is_true_eq_true _ (in_imp_search a l inH)) as searchH.
    contradiction diff_false_true; congruence.
  Qed.

  Lemma if_search_false {B : Type} {a l} (b b' : B)
    : ~ In a l -> (if search a l then b else b') = b'.
  Proof.
    case_eq (search a l); auto.
    intros searchH notinH.
    contradiction notinH; clear notinH.
    auto using Is_true_eq_left, search_imp_in.
  Qed.

  Fixpoint rem_dups (seen l : list A) : list A :=
    match l with
    | nil => nil
    | cons a l' => if search a seen
                   then rem_dups seen l'
                   else cons a (rem_dups (cons a seen) l')
    end.

  Lemma search_false_imp_not_in a l
    : search a l = false -> ~ In a l.
  Proof.
    intros search inH.
    rewrite <- search_iff_in in inH.
    rewrite search in inH.
    auto.
  Qed.

  Lemma seen_not_in_rem_dups a seen l
    : In a seen -> ~ In a (rem_dups seen l).
  Proof.
    revert seen; induction l as [ | a' l IH ]; intro seen; auto.
    unfold rem_dups; fold rem_dups.
    case_eq (search a' seen); auto.
    destruct (decA a a') as [ <- | neH ]; intros unseenH inH.
    - contradiction (search_false_imp_not_in _ _ unseenH).
    - specialize (IH (a' :: seen) (in_cons _ _ _ inH)).
      simpl; intuition.
  Qed.

  Lemma distinct_rem_dups seen l
    : distinct A (rem_dups seen l).
  Proof.
    revert seen; induction l as [ | a l IH ]; intro seen.
    - simpl; auto.
    - unfold rem_dups; fold rem_dups.
      case (search a seen); auto.
      unfold distinct; fold (distinct A).
      split; auto using seen_not_in_rem_dups with datatypes.
  Qed.

  Lemma in_rem_dups_if a l seen
    : In a l -> ~ In a seen -> In a (rem_dups seen l).
  Proof.
    revert seen.
    induction l as [ | a' l IH ]; try contradiction.
    intros seen inH notseenH; unfold rem_dups; fold rem_dups.
    destruct (decA a a') as [ <- | neH ].
    - rewrite (if_search_false _ _ notseenH); apply in_eq.
    - destruct inH as [ -> | inH ]; try contradiction.
      case_eq (search a' seen); auto; intros.
      apply in_cons.
      apply (IH (a' :: seen) inH).
      destruct 1 as [ -> |  ]; contradiction.
  Qed.

End rem_dups.
