(**

  In this library, we talk about projections. A projection is some map
  [p: A -> B], which we assume to be surjective (but probably nowhere
  near injective).

  In particular, we're interested in projections with finite
  image. Maybe [A] is a sigma type for some predicate and [p] is
  projection onto the first coordinate. Then finiteness of the image
  means that there are finitely many elements [B] that satisfy the
  predicate.

*)

Require Import Lists.List.

Require Import Top.FinSet.NatMap.

Set Implicit Arguments.

(**

  * A projected notion of being in a list

  Firstly, we define a "projected" version of [In]. The statement
  [InProj p b lst] means that there is some [a] in [lst] such that [p
  a = b].

*)

Section InProj.
  Variables (A B : Type).
  Variable (p : A -> B).

  Definition InProj (b : B) (l : list A) := In b (map p l).

  Lemma in_proj_cons a b l : InProj b l -> InProj b (a :: l).
  Proof.
    unfold InProj; rewrite map_cons; auto with datatypes.
  Qed.

  Lemma in_proj_eq a b l : p a = b -> InProj b (a :: l).
  Proof.
    unfold InProj; rewrite map_cons; intros ->; apply in_eq.
  Qed.

  Lemma in_proj_nil b : ~ InProj b nil.
  Proof.
    unfold InProj, map; auto with datatypes.
  Qed.

  Lemma in_proj_inv a b l : InProj b (a :: l) -> p a = b \/ InProj b l.
  Proof.
    unfold InProj; rewrite map_cons; apply in_inv.
  Qed.

  Lemma in_proj_or_app (l m : list A) (b : B)
    : InProj b l \/ InProj b m -> InProj b (l ++ m).
  Proof.
    unfold InProj; rewrite map_app; apply in_or_app.
  Qed.

  Lemma in_proj_lift b l
    : InProj b l ->
      exists a : A, In a l /\ p a = b.
  Proof.
    induction l as [ | a l IH ]; [ inversion 1 | ].
    intros inH; destruct (in_proj_inv inH) as [ eqH | consH ].
    - exists a; auto with datatypes.
    - destruct (IH consH) as [ a' [ inH' pa'H ] ].
      exists a'. auto with datatypes.
  Qed.

End InProj.

(** As you might expect, [InProj] generalises the standard library's
   [In]. This lemma shows that [In] is a degenerate case of InProj,
   where [A=B] and the "projection" is the identity. *)
Lemma in_proj_in (A : Type) (a : A) l : In a l <-> InProj id a l.
Proof.
  constructor.
  - intro inH.
    induction l as [ | a' l IH ].
    + contradiction (in_nil inH).
    + destruct (in_inv inH).
      * apply in_proj_eq. unfold id. exact H.
      * apply in_proj_cons. apply IH. exact H.
  - intro ipH.
    induction l as [ | a' l IH ].
    + contradiction (in_proj_nil ipH).
    + destruct (in_proj_inv ipH).
      * unfold id in H.
        rewrite H.
        apply in_eq.
      * apply in_cons. apply IH. exact H.
Qed.

(** ** The relation between [InProj] and mapping over lists

   The Coq standard library defines a lemma [in_map], which says that
   if [a] is in [lst] then [f a] is in [map f lst]. The corresponding
   lemma for [InProj] is slightly more complicated to state. The
   point is that the right notion of a "map" between two projections
   [p : A -> B] and [p' : A' -> B'] is a pair of maps between the tops
   and bottoms, making the naturality square commute.
   % \begin{equation}
     \label{eq:natsq}
     \begin{tikzcd}
       A \arrow[d, "p"] \arrow[r, "f"] &
       A' \arrow[d, "p'"]
       \\
       B \arrow[r, "g"] &
       B'
     \end{tikzcd}
   \end{equation} %
   This naturality condition is passed as a hypothesis to [in_proj_map].

 *)
Lemma in_proj_map
      (A A' B B' : Type)
      (p : A -> B) (p' : A' -> B') (m : nat_map p p') b l
  : InProj p b l -> InProj p' (nm_bot m b) (map (nm_top m) l).
Proof.
  induction l as [ | a l IH ].
  - intro H. contradiction (in_proj_nil H).
  - intro H.
    destruct (in_proj_inv H); clear H.
    + apply in_proj_eq.
      rewrite <- H0.
      apply nat_map_nat.
    + rewrite map_cons.
      apply in_proj_cons.
      apply IH. exact H0.
Qed.

(** * Fullness of lists and finiteness

   Now that we have a projective notion of [In], we can define
   [FullProj] using it. We want to say that "the image of [p : A -> B]
   is covered by the image of the given list".

*)

Definition FullProj (A B : Type) (p : A -> B) (l : list A) : Prop :=
  forall a : A, InProj p (p a) l.

Definition FiniteProj (A B : Type) (p : A -> B) : Type :=
  { l : list A | FullProj p l }.

(** * Decidability

    [InProj] is decidable if [B] has decidable equality. We prove that
    here.

    [FullProj] isn't decidable (because there's no way to check "all"
    of a type). However, we can define a function to lift pre-images
    of a list. If you know that the projection is full, you can use
    the tight version ([lift_proj'], defined below) of this lift to
    define a sort of right inverse to the projection.

 *)

Definition dec_proc_to_sumbool
           {A : Type}
           {P : A -> Prop}
           {f : A -> bool}
           (H: forall a, P a <-> is_true (f a))
           (a : A)
  : {P a} + {~ P a} :=
  Bool.reflect_dec _ _ (Bool.iff_reflect (P a) (f a) (H a)).

Section dec.
  Variables A B : Type.
  Variable p : A -> B.
  Hypothesis decB : forall b1 b2 : B, {b1 = b2} + {b1 <> b2}.

  Lemma in_cons_but_not_tail (a b : B) (l : list B)
    : In b (cons a l) -> ~ In b l -> a = b.
  Proof.
    destruct 1; tauto.
  Qed.

  (** A decidable version of [in_inv]. Note that the sumbool terms
      aren't disjoint (because [b] can equal the head and also appear in
      the tail. We return the left value in this case. *)
  Definition dec_in_inv (a b : B) (l : list B) (inH0 : In b (cons a l))
    : {a = b} + {In b l} :=
    match decB a b with
    | left eqH => left eqH
    | right neH =>
      match in_dec decB b l with
      | left inH => right inH
      | right notinH => False_rec _ (neH (in_cons_but_not_tail inH0 notinH))
      end
    end.

End dec.
