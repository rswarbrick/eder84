Require Import Lists.List.
Require Import Bool.Bool.

Require Import SymbComp.Remove.

(*
  Facts about lists with no repeated elements
*)
Section decA.
  Variable A : Type.

  Fixpoint distinct (l : list A) :=
    match l with
    | nil => True
    | (a :: l') => (~ In a l') /\ distinct l'
    end.

  Lemma distinct_cons_intro a l
    : ~ In a l -> distinct l -> distinct (a :: l).
  Proof. simpl; auto. Qed.

  Lemma distinct_uncons a l
    : distinct (a :: l) -> distinct l.
  Proof.
    simpl; tauto.
  Qed.

  Hint Resolve distinct_cons_intro : distinct.

  Hypothesis decA : forall a a' : A, {a = a'} + {a <> a'}.

  Ltac if_dec :=
    match goal with
    | [ |- context [ if decA ?a ?a' then _ else _ ] ] =>
      destruct (decA a a') as [ <- | ]
    | [ |- context [ In ?a (?a' :: ?l) ] ] =>
      destruct (decA a a') as [ <- | ]
    end.

  Lemma distinct_remove a l
    : distinct l -> distinct (remove decA a l).
  Proof.
    induction l; try tauto.
    destruct 1; autorewrite with remove; if_dec; auto.
    eauto 6 using (in_remove_means_in_original decA) with distinct.
  Qed.

  Fixpoint search (a : A) l : bool :=
    match l with
    | nil => false
    | cons a' l' => if decA a a' then true else search a l'
    end.

  Lemma search_imp_in a l : Is_true (search a l) -> In a l.
  Proof.
    induction l; auto; simpl; if_dec; auto.
  Qed.

  Lemma in_imp_search a l : In a l -> Is_true (search a l).
  Proof.
    induction l as [ | a' ]; simpl; auto.
    if_dec; simpl; auto; destruct 1; auto; congruence.
  Qed.

  Lemma search_iff_in a l : Is_true (search a l) <-> In a l.
  Proof.
    constructor; auto using search_imp_in, in_imp_search.
  Qed.

  Lemma search_induct a l {P : Prop}
    : (search a l = true -> In a l -> P) ->
      (search a l = false -> ~ In a l -> P) ->
      P.
  Proof.
    case_eq (search a l).
    - intro stH. pose (search_imp_in _ _ (Is_true_eq_left _ stH)); auto.
    - intros sfH; rewrite <- search_iff_in, sfH. auto.
  Qed.

  Ltac search_discr :=
    match goal with
    | [ |- context [ search ?a ?l ] ] =>
      intros; apply (search_induct a l);
      let H := fresh "H" in
      intro H; rewrite H
    end.

  Lemma if_search_false {B : Type} {a l} (b b' : B)
    : ~ In a l -> (if search a l then b else b') = b'.
  Proof.
    search_discr; auto; try contradiction.
  Qed.

  Fixpoint rem_dups (seen l : list A) : list A :=
    match l with
    | nil => nil
    | cons a l' => if search a seen
                   then rem_dups seen l'
                   else cons a (rem_dups (cons a seen) l')
    end.

  Lemma rem_dups_cons seen a l
    : rem_dups seen (a :: l) =
      (if search a seen then rem_dups seen l else a :: rem_dups (a :: seen) l).
  Proof. simpl; auto. Qed.

  Hint Rewrite rem_dups_cons : rem_dups.

  Lemma search_false_imp_not_in a l
    : search a l = false -> ~ In a l.
  Proof.
    intros searchH; rewrite <- search_iff_in, searchH. auto.
  Qed.

  Lemma seen_not_in_rem_dups a seen l
    : In a seen -> ~ In a (rem_dups seen l).
  Proof.
    revert seen; induction l as [ | a' l IH ]; intro seen; auto.
    autorewrite with rem_dups.
    intros; search_discr; auto; if_dec; auto.
    specialize (IH (a' :: seen)); simpl; intuition.
  Qed.

  Lemma distinct_rem_dups seen l
    : distinct (rem_dups seen l).
  Proof.
    revert seen; induction l as [ | a l IH ]; intro seen;
      simpl; auto; search_discr; auto.
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

  Lemma remove_notin a l
    : ~ In a l -> remove decA a l = l.
  Proof.
    induction l as [ | a' l IH ]; try tauto.
    unfold remove; fold (remove decA).
    destruct (decA a a') as [ <- | neH ].
    - intros H; contradiction H; apply in_eq.
    - intros; apply f_equal; intuition.
  Qed.

  Lemma length_distinct_remove_in a l
    : distinct l -> In a l ->
      length l = S (length (remove decA a l)).
  Proof.
    induction l as [ | a' l IH ]; try contradiction.
    destruct 1 as [ notL distH ].
    unfold remove; fold (remove decA).
    destruct (decA a a') as [ <- | neH ].
    - rewrite (remove_notin _ _ notL); auto.
    - destruct 1 as [ -> | inH ]; try contradiction.
      simpl; rewrite (IH distH inH); auto.
  Qed.

End decA.

Arguments distinct {A}.
Arguments distinct_uncons {A a l}.
Arguments distinct_remove {A} decA a {l}.
Arguments remove_notin {A} decA {a l}.
Arguments length_distinct_remove_in {A} decA {a l}.
