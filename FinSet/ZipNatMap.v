(**

  This library is about defining a natural map between two
  projections, based on a finite list of pairs. The top types are
  called [A1], [A2] and the bottom types are called [B1], [B2].

  You can do this whenever the first coordinates of the list of pairs
  form a full list for the first projection. Clearly, that's necessary
  (otherwise, where should some other element of [A1] end up?). It
  turns out to be sufficient too.

  The only slight wrinkle is that we also need to supply a function
  [B1 -> B2]. The point is that we don't require the projection [A1 ->
  B1] to be surjective, so we're going to have extra elements that we
  need to send somewhere. We could have asked for an element of [B2],
  but the expected use case for all of this has [B1] equal to [B2], so
  it's easier to provide the identity map than to pick out a special
  element of the bottom set.

*)

Require Import Lists.List.

Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.Distinct.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.ProjSet.

Set Implicit Arguments.

(** The technical work for defining this natural map is simplified by
    the idea of a staged projection (one composed of two projections
    chained together). In our application, this will be from [A1 * A2]
    to [B1], chaining [fst] with [p1]. Lifting this projection gives
    the pair in the zipped list that will define our mapping. *)

Section staged_proj.
  Variables A A' B : Type.
  Variable p : A -> A'.
  Variable q : A' -> B.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Fixpoint lift_staged_proj (b : B) (l : list A) : option A :=
    match l with
    | nil => None
    | cons a l' =>
      if decB (q (p a)) b then Some a else lift_staged_proj b l'
    end.

  Fixpoint lift_staged_proj' (b : B) (l : list A) : InProj q b (map p l) -> A :=
    match l as l0 return InProj q b (map p l0) -> A with
    | nil => fun inH => False_rect A inH
    | cons a l' =>
      fun inH =>
        match dec_in_inv decB inH with
        | left eqH => a
        | right inH' => lift_staged_proj' b l' inH'
        end
    end.

  Lemma lift_staged_proj_some b l inH
    : lift_staged_proj b l = Some (lift_staged_proj' b l inH).
  Proof.
    induction l as [ | a l IH ]; [ contradiction inH | ].
    simpl; unfold dec_in_inv.
    destruct (decB (q (p a)) b) as [ | neH ]; auto.
    fold (map p l); fold (map q (map p l)).
    destruct (in_dec decB b (map q (map p l))) as [ | notinH ]; auto.
    contradiction notinH; destruct (in_proj_inv inH); tauto.
  Qed.

  Lemma lift_staged_proj_in b l a
    : lift_staged_proj b l = Some a -> In a l.
  Proof.
    induction l as [ | a' l IH ]; [ discriminate | simpl ].
    destruct (decB (q (p a')) b) as [ eqH | neH ]; auto.
    intro someH; injection someH; auto.
  Qed.

  Lemma lift_staged_proj'_in b l inH
    : In (lift_staged_proj' b l inH) l.
  Proof.
    eauto using lift_staged_proj_in, lift_staged_proj_some.
  Qed.

  Lemma proj_lift_staged_proj b l a
    : lift_staged_proj b l = Some a -> q (p a) = b.
  Proof.
    induction l as [ | a' l IH ]; [ discriminate | simpl ].
    destruct (decB (q (p a')) b) as [ eqH | neH ]; auto.
    intro someH; injection someH; intro aH; rewrite <- aH; auto.
  Qed.

  Lemma proj_lift_staged_proj' b l inH
    : q (p (lift_staged_proj' b l inH)) = b.
  Proof.
    eauto using proj_lift_staged_proj, lift_staged_proj_some.
  Qed.

  Lemma in_staged_proj_map_elim b l
    : InProj q b (map p l) ->
      exists a : A, q (p a) = b /\ In a l.
  Proof.
    intro inH.
    induction l as [ | a l IH ]; [ contradiction inH | ].
    destruct inH as [ eqH | consH ].
    - exists a; auto with datatypes.
    - destruct (IH consH) as [ a' [ eqH inH ] ].
      exists a'; auto with datatypes.
  Qed.

End staged_proj.

Section distinct.
  Variables A B : Type.
  Variable f : A -> B.

  Lemma distinct_match_at a0 a1 l
    : f a1 = f a0 ->
      distinct (map f (a1 :: l)) ->
      In a0 (a1 :: l) ->
      a1 = a0.
  Proof.
    intros eqfH distinctH inH.
    destruct distinctH as [ notinH _ ]; rewrite eqfH in notinH.
    destruct inH as [ | inH ]; auto.
    contradiction notinH; apply in_map; auto.
  Qed.

  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Lemma distinct_under_map_implies_inj l a a'
    : distinct (map f l) ->
      In a l ->
      In a' l ->
      f a = f a' ->
      a = a'.
  Proof.
    intros distinctH in1H in2H eqH.
    induction l as [ | a'' l IH ]; [ contradiction in1H | ].
    destruct (decB (f a'') (f a)) as [ feqH | fneH ].
    - rewrite <- (distinct_match_at feqH distinctH in1H).
      exact (distinct_match_at (eq_trans feqH eqH) distinctH in2H).
    - destruct in1H as [ | in1H ];
        [ contradiction fneH; apply f_equal; auto | ].
      destruct in2H as [ eqH' | in2H ];
        [ contradiction fneH; rewrite (f_equal f eqH'); auto | ].
      apply IH; eauto using distinct_uncons.
  Qed.

End distinct.


(** Now we can define our natural map. We start by specialising the
    definitions and lemmas above to the case with pairs as
    described. With this done, the definitions are reasonably obvious:
    the only difficulty is keeping track of what hypotheses are needed
    where! *)

Section znm.
  Variables A1 A2 B1 B2 : Type.
  Variable p1 : A1 -> B1.
  Variable p2 : A2 -> B2.
  Hypothesis decB1 : forall x y : B1, {x = y} + {x <> y}.

  Definition lift_pr_proj'
             (a1 : A1) (l : list (A1 * A2)) (fullH : FullProj p1 (map fst l))
    : A1 * A2 :=
    lift_staged_proj' fst p1 decB1 (p1 a1) l (fullH a1).

  Definition lift_pr_proj (b1 : B1) (l : list (A1 * A2)) : option (A1 * A2) :=
    lift_staged_proj fst p1 decB1 b1 l.

  Lemma lift_pr_proj_some a1 l fullH
    : lift_pr_proj (p1 a1) l = Some (lift_pr_proj' a1 l fullH).
  Proof.
    apply lift_staged_proj_some.
  Qed.

  Local Definition top_map
        (l : list (A1 * A2)) (fullH : FullProj p1 (map fst l)) (a1 : A1) : A2 :=
    snd (lift_pr_proj' a1 l fullH).

  Local Definition bot_map
        (fb : B1 -> B2) (l : list (A1 * A2)) (b1 : B1) : B2 :=
    match lift_pr_proj b1 l with
    | Some pr => p2 (snd pr)
    | None => fb b1
    end.

  Local Lemma is_nat
        (fb : B1 -> B2) (l : list (A1 * A2)) (fullH : FullProj p1 (map fst l))
    : is_nat_map p1 p2 (top_map l fullH, bot_map fb l).
  Proof.
    intro a1; simpl.
    unfold top_map, bot_map.
    rewrite (lift_pr_proj_some a1 l fullH).
    auto.
  Qed.

  Definition zip_nat_map
             (fb : B1 -> B2)
             (l : list (A1 * A2))
             (fullH : FullProj p1 (map fst l))
    : nat_map p1 p2 :=
    exist _ (top_map l fullH, bot_map fb l) (is_nat fb l fullH).

  Definition pr_proj1 : A1 * A2 -> B1 := fun pr => p1 (fst pr).
  Definition pr_proj2 : A1 * A2 -> B2 := fun pr => p2 (snd pr).

  Lemma zip_nat_map_in fb l fullH a1 a2
    : nm_top (zip_nat_map fb l fullH) a1 = a2 ->
      exists a1', p1 a1' = p1 a1 /\ In (a1', a2) l.
  Proof.
    unfold zip_nat_map; simpl.
    unfold top_map, lift_pr_proj'.
    set (pr := (lift_staged_proj' fst p1 decB1 (p1 a1) l (fullH a1))).
    intro prH.
    exists (fst pr); split.
    - apply proj_lift_staged_proj'.
    - rewrite <- prH.
      rewrite <- surjective_pairing.
      apply lift_staged_proj'_in.
  Qed.

  (** How can we tell that we defined the "right" map? One obvious
      thing to expect is that if the list contains a pair [(a1, a2)]
      then [a1] is mapped to [a2]. Of course, that is only true if
      there isn't some other pair that comes before and also maps to
      [p1 a1]. This is guaranteed, however, if the first elements of
      the pairs map to distinct elements. In our use case for
      constructing maps between sets based on their cardinalities,
      this will definitely hold. *)

  Lemma distinct_zip_nat_map_at fb l fullH a1 a2
    : distinct (map pr_proj1 l) ->
      In (a1, a2) l ->
      nm_top (zip_nat_map fb l fullH) a1 = a2.
  Proof.
    intros distinctH prInH.
    destruct (zip_nat_map_in fb l fullH a1 eq_refl)
      as [ a1' [ p1H inH ] ].
    exact (eq_sym (f_equal snd (distinct_under_map_implies_inj
                                  pr_proj1 decB1 l _ _
                                  distinctH prInH inH (eq_sym p1H)))).
  Qed.

  (** When is the map injective (in the sense of [inj_nat_map])? If
      the list is distinct under projection with [pr_proj2]. Note that
      this needs decidable equality in [B2]. This is because otherwise
      there's no way to unpack the fact that things are distinct in
      [B2].

      The converse isn't quite true. The point is that the list could
      contain a pair (a1, a2) twice. This doesn't stop the induced map
      being injective (the second occurrence is ignored in the induced
      map) but obviously [map pr_proj2 l] will not be distinct. This
      can be fixed if you require [map pr_proj1 l] to be distinct, but
      I don't think I need that at the moment. *)

  Lemma zip_nat_map_inj_intro
        (decB2 : forall x y : B2, {x = y} + {x <> y})
        fb l fullH
    : distinct (map pr_proj2 l) ->
      inj_nat_map (zip_nat_map fb l fullH).
  Proof.
    intros distinctH a10 a11.
    rewrite <- !(nat_map_nat (zip_nat_map fb l fullH)).
    destruct (zip_nat_map_in fb l fullH a10 eq_refl)
      as [ a10' [ p10H in10H ] ].
    destruct (zip_nat_map_in fb l fullH a11 eq_refl)
      as [ a11' [ p11H in11H ] ].
    intro p2H; rewrite <- p10H, <- p11H.
    exact (f_equal pr_proj1 (distinct_under_map_implies_inj
                               pr_proj2 decB2 l _ _
                               distinctH in10H in11H p2H)).
  Qed.

  (** Similarly, you can show when the map is surjective. Here, you
      just need the list of second coordinates to be full for [p2]. Of
      course, you also need the first elements to be distinct, because
      a pair with a repeated first coordinate won't contribute to the
      map. *)

  Lemma zip_nat_map_surj_intro fb l fullH
    : distinct (map pr_proj1 l) ->
      FullProj p2 (map snd l) ->
      SurjectiveProj (zip_nat_map fb l fullH).
  Proof.
    intros distinctH full2H.
    intro a2.
    destruct (in_staged_proj_map_elim snd p2 (p2 a2) l (full2H a2))
      as [ [ a1' a2' ] [ eq2H inH ] ].
    exists a1'.
    rewrite <- !(nat_map_nat (zip_nat_map fb l fullH)), <- eq2H.
    auto using f_equal, distinct_zip_nat_map_at.
  Qed.

End znm.
