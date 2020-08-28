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

End staged_proj.

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

End znm.
