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
Require Import Bool.

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
   A finite projection always has a cardinality, providing that we
   have decidability downstairs. The proof is that you pick a listing
   that implies finiteness and remove elements that give duplicates
   under the projection. That second part needs a function.
 *)
Section rem_dups_below.
  Variables A B : Type.
  Variable p : A -> B.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Fixpoint rem_dups_below (s : list B) (l : list A) : list A :=
    match l with
    | nil => nil
    | a :: l' => if search _ decB (p a) s
                 then rem_dups_below s l'
                 else a :: rem_dups_below (p a :: s) l'
    end.

  Lemma seen_not_in_rem_dups_below b s l
    : In b s -> ~ In b (map p (rem_dups_below s l)).
  Proof.
    revert s; induction l as [ | a l IH ]; auto.
    intro s; unfold rem_dups_below; fold rem_dups_below.
    case_eq (search B decB (p a) s); auto.
    intros nsearchH inbH.
    rewrite map_cons.
    destruct 1 as [ <- | x ].
    - auto using
           (eq_true_false_abs (search B decB (p a) s)),
           (Is_true_eq_true _ (in_imp_search _ decB _ _ inbH)).
    - contradiction (IH (p a :: s) (in_cons (p a) b s inbH)).
  Qed.

  Lemma distinct_map_rem_dups_below s l
    : distinct (map p (rem_dups_below s l)).
  Proof.
    revert s; induction l as [ | a l IH ]; simpl; auto; intro s.
    case (search B decB (p a) s); auto.
    rewrite map_cons.
    apply distinct_cons_intro; auto.
    apply seen_not_in_rem_dups_below.
    apply in_eq.
  Qed.

  Lemma in_map_rem_dups_below b s l
    : In b (map p l) -> ~ In b s -> In b (map p (rem_dups_below s l)).
  Proof.
    revert s; induction l as [ | a l IH ]; auto.
    intro s.
    unfold rem_dups_below; fold rem_dups_below.
    case_eq (search B decB (p a) s);
      intros searchH inconsH.
    - destruct inconsH as [ <- | ]; auto; intro notinH.
      contradiction notinH.
      apply (search_imp_in _ decB).
      apply (Is_true_eq_left _ searchH).
    - rewrite map_cons.
      destruct (decB b (p a)) as [ <- | neH ]; intros notinH.
      + apply in_eq.
      + apply in_cons.
        destruct inconsH as [ <- | inH ]; try tauto.
        apply IH; auto.
        destruct 1; auto.
  Qed.
End rem_dups_below.

Arguments rem_dups_below {A B} p decB s l.
Arguments distinct_map_rem_dups_below {A B} p decB s l.
Arguments in_map_rem_dups_below {A B} p decB b s l.

Lemma fp_card_exists
      {A B : Type} (p : A -> B)
      (decB : forall x y : B, {x = y} + {x <> y})
  : FiniteProj p -> exists n, fp_card p n.
Proof.
  destruct 1 as [ l fullH ].
  unfold fp_card.
  set (l' := rem_dups_below p decB nil l).
  exists (length l'), l'; intuition.
  - apply (distinct_map_rem_dups_below p decB nil l).
  - unfold FullProj in *.
    intro a; specialize (fullH a).
    unfold InProj in *.
    apply in_map_rem_dups_below; auto.
Qed.

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

Arguments nat_map_gives_list_map {A B C D p q} f l1 {l2}.
Arguments nm_bot_inj_on_list {A B C D p q} f injH l1.

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

(*

  We want to show that an injective endomorphism on a finite set is in
  fact a bijection.

  How do we do this? Well, the first thing is to notice that this
  injection must also be surjective. We'll show a slightly stronger
  result: if two sets have the same cardinality, an injection from one
  to the other is a surjection. We have proved the "list form" of this
  in the InjList theory.

*)
Section inj_same_size.
  Variables A B C D : Type.
  Variable p : A -> B.
  Variable q : C -> D.
  Variable f : nat_map p q.

  Variable n : nat.
  Hypothesis cardpH : fp_card p n.
  Hypothesis cardqH : fp_card q n.

  Hypothesis injH :
    forall a a',
      nm_bot f (p a) = nm_bot f (p a') ->
      p a = p a'.

  Hypothesis decD : forall x y : D, {x = y} + {x <> y}.

  Lemma fp_inj_same_card_is_surj
    : SurjectiveProj f.
  Proof.
    destruct cardpH as [ lp H ];
      destruct H as [ distpH H ];
      destruct H as [ fullpH lenpH ].
    destruct cardqH as [ lq H ];
      destruct H as [ distqH H ];
      destruct H as [ fullqH lenqH ].
    assert (surjH : surj_on_list (nm_bot f) (map p lp) (map q lq));
      try (apply (inj_on_eql_list_is_surj
                    (map p lp) (map q lq) decD distpH distqH
                    (nat_map_gives_list_map f lp fullqH)
                    (nm_bot_inj_on_list f injH lp));
           rewrite !map_length; congruence).
    intros c.
    specialize (fullqH c).
    specialize (surjH (q c) fullqH).
    rewrite in_map_iff in surjH.
    destruct surjH as [ b bH ]; destruct bH as [ <- bH ].
    rewrite in_map_iff in bH.
    destruct bH as [ a aH ]; destruct aH as [ <- aH ].
    exists a; reflexivity.
  Qed.
End inj_same_size.

Arguments fp_inj_same_card_is_surj {A B C D p q} f {n} cardpH cardqH injH decD.

Section inj_endo_is_surj.
  Variables A B : Type.
  Variable p : A -> B.
  Variable f : nat_map p p.

  Hypothesis injH :
    forall a a',
      nm_bot f (p a) = nm_bot f (p a') ->
      p a = p a'.

  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis finH : FiniteProj p.

  Lemma inj_endo_is_surj
    : SurjectiveProj f.
  Proof.
    destruct (fp_card_exists p decB finH) as [ n cardH ].
    apply (fp_inj_same_card_is_surj f cardH cardH injH decB).
  Qed.
End inj_endo_is_surj.

Arguments inj_endo_is_surj {A B p} f injH decB finH.
