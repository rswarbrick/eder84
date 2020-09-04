(**

   Some handy facts and definitions for lists.

*)

Require Import Lists.List.

Set Implicit Arguments.

Fixpoint take (A : Type) (n : nat) (xs : list A) : list A :=
  match n with
  | O => nil
  | S k =>
    match xs with
    | nil => nil
    | cons x xs' => cons x (take k xs')
    end
  end.

Lemma take_nil (A : Type) n
  : take n (nil (A := A)) = nil.
Proof.
  induction n; auto.
Qed.

Lemma in_take (A : Type) n x (xs : list A)
  : In x (take n xs) -> In x xs.
Proof.
  revert xs; induction n as [ | n IH ]; [ contradiction | ]; intro xs.
  destruct xs as [ | a xs ]; auto.
  simpl. destruct 1; auto.
Qed.

Lemma map_take (A B : Type) (f : A -> B) n xs
  : map f (take n xs) = take n (map f xs).
Proof.
  revert n; induction xs as [ | x xs IH ];
    intro n; [ rewrite !take_nil; auto | ].
  destruct n; auto.
  simpl; apply f_equal; auto.
Qed.

Lemma take_take (A : Type) n m (xs : list A)
  : take n (take m xs) = take (min n m) xs.
Proof.
  revert xs m; induction n as [ | n IH ]; auto; intros xs m.
  destruct m; auto.
  destruct xs; auto.
  simpl; apply f_equal; auto.
Qed.

Lemma take_length (A : Type) (xs : list A)
  : take (length xs) xs = xs.
Proof.
  induction xs; simpl; auto using f_equal.
Qed.

Lemma map_fst_combine (A B : Type) (xs : list A) (ys : list B)
  : map fst (combine xs ys) = take (min (length xs) (length ys)) xs.
Proof.
  revert ys; induction xs as [ | x xs IH ]; auto; intro ys.
  destruct ys as [ | y ys ]; auto.
  simpl; apply f_equal; auto.
Qed.

Lemma map_snd_combine (A B : Type) (xs : list A) (ys : list B)
  : map snd (combine xs ys) = take (min (length xs) (length ys)) ys.
Proof.
  revert ys; induction xs as [ | x xs IH ]; auto; intro ys.
  destruct ys as [ | y ys ]; auto.
  simpl; apply f_equal; auto.
Qed.
