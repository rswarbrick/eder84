Require Import Lists.List.
Require Import Bool.Bool.

Require Import Top.FinSet.Remove.
Require Import Top.FinSet.ListFacts.

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

  Lemma search_imp_in a l : is_true (search a l) -> In a l.
  Proof.
    induction l; unfold is_true; simpl; auto using diff_false_true.
    destruct (decA _ _); auto.
  Qed.

  Lemma in_imp_search a l : In a l -> is_true (search a l).
  Proof.
    induction l as [ | a' ]; simpl; auto.
    if_dec; simpl; auto; destruct 1; auto; congruence.
  Qed.

  Lemma search_iff_in a l : is_true (search a l) <-> In a l.
  Proof.
    constructor; auto using search_imp_in, in_imp_search.
  Qed.

  Lemma search_induct a l {P : Prop}
    : (search a l = true -> In a l -> P) ->
      (search a l = false -> ~ In a l -> P) ->
      P.
  Proof.
    case_eq (search a l).
    - auto using search_imp_in.
    - intros sfH; rewrite <- search_iff_in, sfH; unfold is_true; auto.
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
    intros searchH; rewrite <- search_iff_in, searchH; unfold is_true; auto.
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

Lemma distinct_take (A : Type) n (xs : list A)
  : distinct xs -> distinct (take n xs).
Proof.
  revert n; induction xs as [ | x xs IH ]; intro n; [ rewrite take_nil; auto | ].
  destruct 1 as [ notinH distH ].
  destruct n; simpl; auto.
  split; eauto using in_take.
Qed.

(**

  As above, but "under" a map. For example, set [f] to [fst] to get a
  nice way to work with lists of pairs defining a function.

*)

Section decB.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint distinct_under (l : list A) :=
    match l with
    | nil => True
    | a :: tl => (~ in_under f (f a) tl) /\ distinct_under tl
    end.

  Lemma distinct_under_cons_intro a l
    : ~ in_under f (f a) l -> distinct_under l -> distinct_under (a :: l).
  Proof. simpl; auto. Qed.

  Lemma distinct_under_uncons a l
    : distinct_under (a :: l) -> distinct_under l.
  Proof.
    simpl; tauto.
  Qed.

  Hint Resolve distinct_under_cons_intro : distinct.

  Hypothesis decB : forall b b' : B, {b = b'} + {b <> b'}.

  Lemma distinct_under_remove a l
    : distinct_under l -> distinct_under (remove_under decB f a l).
  Proof.
    induction l as [ | x l IH ]; try tauto.
    destruct 1; simpl; destruct (decB a (f x));
      eauto 6 using distinct_under_cons_intro, in_under_remove_means_in_original.
  Qed.

  Fixpoint rem_dups_under (seen : list B) (l : list A) : list A :=
    match l with
    | nil => nil
    | a :: tl => if search _ decB (f a) seen
                 then rem_dups_under seen tl
                 else a :: (rem_dups_under (f a :: seen) tl)
    end.

  Lemma rem_dups_under_cons seen a l
    : rem_dups_under seen (a :: l) =
      (if search _ decB (f a) seen
       then rem_dups_under seen l
       else a :: rem_dups_under (f a :: seen) l).
  Proof. simpl; auto. Qed.

  Hint Rewrite rem_dups_under_cons : rem_dups.

  Lemma seen_not_in_rem_dups_under b seen l
    : In b seen -> ~ in_under f b (rem_dups_under seen l).
  Proof.
    revert seen; induction l as [ | a l IH ]; intro seen; auto.
    autorewrite with rem_dups.
    apply (search_induct _ decB (f a) seen); intros ->; auto.
    intros fanewH bseenH; simpl.
    specialize (IH (f a :: seen) (in_cons _ _ _ bseenH)).
    intro H; destruct H as [ -> | ]; auto.
  Qed.

  Lemma distinct_under_rem_dups seen l
    : distinct_under (rem_dups_under seen l).
  Proof.
    revert seen; induction l as [ | a l IH ]; intro seen; simpl; auto.
    apply (search_induct _ decB (f a) seen); intros ->; auto.
    intro notseen; simpl; auto using seen_not_in_rem_dups_under with datatypes.
  Qed.

  Lemma in_under_rem_dups_if b l seen
    : in_under f b l -> ~ In b seen -> in_under f b (rem_dups_under seen l).
  Proof.
    revert seen.
    induction l as [ | a l IH ]; try contradiction.
    intros seen inH notseenH; simpl.
    destruct (decB b (f a)) as [ eqH | neH ].
    - rewrite <- eqH; case_eq (search B decB b seen); simpl; auto.
      revert notseenH; rewrite <- (search_iff_in _ decB); tauto.
    - destruct inH as [ | consH ]; [ contradiction | ].
      case_eq (search B decB (f a) seen); simpl; auto.
      intros notsearchH; right.
      apply IH; auto.
      destruct 1; auto.
  Qed.

  Lemma remove_not_in_under b l
    : ~ in_under f b l -> remove_under decB f b l = l.
  Proof.
    induction l as [ | a l IH ]; try tauto.
    simpl.
    intro H; destruct (Decidable.not_or _ _ H) as [ neH nunderH ]; clear H.
    destruct (decB b (f a)); [ tauto | apply f_equal; auto ].
  Qed.

  Lemma length_remove_under_le b l
    : length (remove_under decB f b l) <= length l.
  Proof.
    induction l as [ | a l IH ]; auto.
    simpl; destruct (decB b (f a)) as [ | neH ]; auto using le_S.
    simpl; auto using le_n_S.
  Qed.

  Lemma length_remove_under_in b l
    : in_under f b l -> length (remove_under decB f b l) < length l.
  Proof.
    induction l as [ | a l IH ]; [ contradiction | ].
    simpl; destruct (decB b (f a)) as [ -> | neH ].
    - auto using Lt.le_lt_n_Sm, length_remove_under_le.
    - destruct 1 as [ | inH ]; [ contradiction | ].
      simpl; auto using Lt.lt_n_S.
  Qed.

  Lemma length_distinct_under_remove_in b l
    : distinct_under l -> in_under f b l ->
      length l = S (length (remove_under decB f b l)).
  Proof.
    induction l as [ | a l IH ]; [ contradiction | ].
    cbn [length in_under remove_under].
    destruct 1 as [ nodupaH distinctH ].
    intro inconsH; apply f_equal.
    destruct (decB b (f a)) as [ -> | neH ].
    - rewrite remove_not_in_under; auto.
    - destruct inconsH; [ contradiction | auto ].
  Qed.

End decB.

Arguments distinct_under {A B} f l.
Arguments distinct_under_cons_intro {A B f a l} notinH dH.
Arguments distinct_under_uncons {A B f a l} dH.
Arguments distinct_under_remove {A B f} decB a {l} dH.
Arguments rem_dups_under {A B} f decB seen l.
Arguments rem_dups_under_cons {A B} f decB seen a l.
Arguments seen_not_in_rem_dups_under {A B} f decB {b seen} l inH.
Arguments distinct_under_rem_dups {A B} f decB seen l.
Arguments in_under_rem_dups_if {A B f} decB {b l seen} inH unseenH.
Arguments remove_not_in_under {A B f} decB {b l} notinH.
Arguments length_remove_under_le {A B} f decB b l.
Arguments length_remove_under_in {A B f} decB {b l} inH.
Arguments length_distinct_under_remove_in {A B f} decB {b l} distH inH.
