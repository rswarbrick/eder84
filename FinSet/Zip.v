Require Import Lists.List.

Require Import Top.FinSet.Distinct.

Set Implicit Arguments.

(** A simple development of the zip function *)
Section zip.
  Variables A B : Type.

  Fixpoint zip (xs : list A) (ys : list B) :=
    match xs with
    | nil => nil
    | cons x xs' =>
      match ys with
      | nil => nil
      | cons y ys' => cons (x, y) (zip xs' ys')
      end
    end.

  Ltac auto_zip_unfold :=
    match goal with
    | [ |- context [ zip ?xs ?ys ] ] =>
      revert ys; induction xs as [ | x xs IH ]; auto;
        intro ys; destruct ys as [ | y ys ]; auto
    end.

  Lemma len_zip (xs : list A) (ys : list B)
    : length (zip xs ys) = min (length xs) (length ys).
  Proof.
    auto_zip_unfold; simpl; apply f_equal; auto.
  Qed.

  Lemma in_zip_elim (xs : list A) (ys : list B) (x : A) (y : B)
    : In (x, y) (zip xs ys) -> In x xs /\ In y ys.
  Proof.
    revert ys; induction xs as [ | u xs IH ]; try contradiction.
    intro ys; destruct ys as [ | v ys ]; try contradiction.
    simpl; destruct 1 as [ prH | consH ].
    - split; left.
      + exact (f_equal fst prH).
      + exact (f_equal snd prH).
    - specialize (IH ys consH).
      destruct IH as [ xH yH ].
      auto.
  Qed.

  Lemma distinct_zip_introl
        (xs : list A) (ys : list B)
    : distinct xs -> distinct (zip xs ys).
  Proof.
    auto_zip_unfold; simpl; auto.
    destruct 1 as [ notinH distH ]; split; auto.
    intro inprH; apply notinH.
    destruct (in_zip_elim xs ys x y inprH); auto.
  Qed.

  Lemma distinct_zip_intror
        (xs : list A) (ys : list B)
    : distinct ys -> distinct (zip xs ys).
  Proof.
    auto_zip_unfold; simpl; auto.
    destruct 1 as [ notinH distH ]; split; auto.
    intro inprH; apply notinH.
    destruct (in_zip_elim xs ys x y inprH); auto.
  Qed.
End zip.
