(**

  This library is all about the cardinality of sets under projection.
  Specifically, if we have a map [p : A -> B] and know that
  [FiniteProj p], which says that the image of [p] as a subset of [B]
  is finite), then we can define a cardinality for that image. As with
  defining [FiniteProj], we don't talk about the cardinality of the
  whole set, rather we always talk about the image of the projection.

*)

Require Import Lists.List.
Require Import PeanoNat.

Require Import SymbComp.FinSet.
Require Import SymbComp.NatMap.
Require Import SymbComp.Distinct.
Require Import SymbComp.InjList.

(** * Cardinality definition

    We are going to define cardinality in a way that isn't necessarily
    computable (but that doesn't require decidability for the
    image). When [B] is decidable, we'll find that there's a unique
    cardinality.
 *)
Definition fp_card {A B : Type} (p : A -> B) (n : nat) : Prop :=
  exists l, distinct (map p l) /\ FullProj p l /\ length l = n.

(**
  If we have an injective map from one projection to the next, then a
  cardinality for the source must be at most any cardinality for the
  target.
*)
Section inj_map.
  Variables A B C D : Type.
  Variable p : A -> B.
  Variable q : C -> D.
  Variable f : nat_map p q.

  Lemma nat_map_gives_list_map l1 l2
    : FullProj q l2 ->
      is_list_map (nm_bot f) (map p l1) (map q l2).
  Proof.
    intro fullH.
    intros b.
    rewrite in_map_iff.
    destruct 1 as [ a aH ]; destruct aH as [ <- inH ].
    rewrite <- nat_map_nat.
    apply fullH.
  Qed.

  Hypothesis injH :
    forall a a',
      nm_bot f (p a) = nm_bot f (p a') ->
      p a = p a'.

  Lemma nm_bot_inj_on_list l1
    : inj_on_list (nm_bot f) (map p l1).
  Proof.
    unfold inj_on_list.
    intros b0 b1 inb0H inb1H.
    rewrite in_map_iff in inb0H;
      destruct inb0H as [ a0 aH ]; destruct aH as [ <- ina0H ].
    rewrite in_map_iff in inb1H;
      destruct inb1H as [ a1 aH ]; destruct aH as [ <- ina1H ].
    auto.
  Qed.

  Hypothesis decD : forall x y : D, {x = y} + {x <> y}.

  Lemma fp_card_inj_le n m
    : fp_card p n -> fp_card q m -> n <= m.
  Proof.
    unfold fp_card.
    destruct 1 as [ l1 H1 ].
    destruct H1 as [ dist1H H1 ].
    destruct H1 as [ full1H <- ].
    destruct 1 as [ l2 H2 ].
    destruct H2 as [ dist2H H2 ].
    destruct H2 as [ full2H <- ].
    enough (maplenH : length (map p l1) <= length (map q l2));
      try (rewrite map_length, map_length in maplenH; auto).
    apply (inj_on_list_length
             (map p l1) (map q l2) decD dist1H dist2H
             (nat_map_gives_list_map l1 l2 full2H)
             (nm_bot_inj_on_list l1)).
  Qed.
End inj_map.

Section fp_card_unique.
  Variables A B : Type.
  Variable p : A -> B.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Local Lemma fp_card_le n m
    : fp_card p n -> fp_card p m -> n <= m.
  Proof.
    apply (fp_card_inj_le A B A B p p (nat_map_v p)); auto.
  Qed.

  Lemma fp_card_unique n m
    : fp_card p n -> fp_card p m -> n = m.
  Proof.
    auto using fp_card_le, Nat.le_antisymm.
  Qed.

End fp_card_unique.

Arguments fp_card_unique {A B} p decB.
