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
