Require Import Lists.List.

(**

  Some more facts about removing an item from a list.

  *)

Section remove.
  Variable A : Type.
  Hypothesis decA : forall a a' : A, {a = a'} + {a <> a'}.

  Lemma remove_eq (a : A) (l : list A)
    : remove decA a (a :: l) = remove decA a l.
  Proof.
    unfold remove; fold (remove decA a).
    case (decA a a); auto. contradiction.
  Qed.

  Lemma remove_neq {a a' : A} {l : list A}
    : a <> a' -> remove decA a (a' :: l) = a' :: remove decA a l.
  Proof.
    unfold remove; fold (remove decA a).
    case (decA a a'); tauto.
  Qed.

  Lemma remove_cons {a a' : A} {l : list A}
    : remove decA a (a' :: l) =
      if decA a a' then remove decA a l else a' :: remove decA a l.
  Proof.
    unfold remove; fold (remove decA); auto.
  Qed.

  Lemma in_remove a a' l
    : In a l -> a <> a' -> In a (remove decA a' l).
  Proof.
    intros inH neH.
    induction l as [ | a'' l IH ]; try contradiction.
    destruct (decA a' a'') as [ <- | neH' ].
    - rewrite remove_eq.
      destruct (in_inv inH) as [ <- | ]; tauto.
    - rewrite (remove_neq neH').
      destruct (in_inv inH) as [ <- | ];
        auto with datatypes.
  Qed.

  Lemma in_remove_means_in_original a a' l
    : In a (remove decA a' l) -> In a l.
  Proof.
    induction l as [ | a'' l IH ]; auto.
    destruct (decA a' a'') as [ <- | neH' ].
    - rewrite remove_eq; auto using in_cons.
    - rewrite (remove_neq neH').
      destruct 1 as [ -> | neH ]; auto with datatypes.
  Qed.

End remove.

Arguments remove_eq {A} decA a l.
Arguments remove_neq {A} decA {a a'} l.
Arguments in_remove {A} decA {a a' l}.
Arguments in_remove_means_in_original {A} decA {a a' l}.

Hint Rewrite @remove_eq : remove.
Hint Rewrite @remove_neq : remove.
Hint Rewrite @remove_cons : remove.

Section remove_under.
  Variables A B : Type.
  Hypothesis decB : forall b b' : B, {b = b'} + {b <> b'}.
  Variable f : A -> B.

  Fixpoint remove_under (b : B) (l : list A) :=
    match l with
    | nil => nil
    | a :: tl => if decB b (f a)
                 then remove_under b tl
                 else a :: remove_under b tl
    end.

  Lemma remove_under_eq a l
    : remove_under (f a) (a :: l) = remove_under (f a) l.
  Proof.
    simpl; destruct (decB (f a) (f a)); [ auto | contradiction ].
  Qed.

  Lemma remove_under_neq a b l
    : b <> f a -> remove_under b (a :: l) = a :: remove_under b l.
  Proof.
    simpl; destruct (decB b (f a)); [ contradiction | auto ].
  Qed.

  Lemma remove_under_cons a b l
    : remove_under b (a :: l) =
      if decB b (f a) then remove_under b l else a :: remove_under b l.
  Proof.
    auto.
  Qed.

  Fixpoint in_under (b : B) (l : list A) :=
    match l with
    | nil => False
    | a :: tl => b = f a \/ in_under b tl
    end.

  Lemma in_under_remove b b' l
    : in_under b l -> b <> b' -> in_under b (remove_under b' l).
  Proof.
    intros inH neH.
    induction l as [ | a l IH ]; [ contradiction | ].
    simpl; destruct (decB b' (f a)) as [ -> | neH' ];
      simpl; destruct inH; tauto.
  Qed.

  Lemma in_under_remove_means_in_original b b' l
    : in_under b (remove_under b' l) -> in_under b l.
  Proof.
    induction l as [ | a l IH ]; auto.
    simpl; destruct (decB b' (f a)); [ | destruct 1 ]; auto.
  Qed.

End remove_under.

Arguments remove_under {A B} decB f b l.
Arguments remove_under_eq {A B} decB f a l.
Arguments remove_under_neq {A B} decB {f a b} l neH.
Arguments remove_under_cons {A B} decB f a b l.
Arguments in_under {A B} f b l.
Arguments in_under_remove {A B} decB f {b b' l} inH neH.
Arguments in_under_remove_means_in_original {A B} decB f {b b' l} inH.

Hint Rewrite @remove_under_eq : remove.
Hint Rewrite @remove_under_neq : remove.
Hint Rewrite @remove_under_cons : remove.
