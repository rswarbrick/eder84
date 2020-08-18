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

Definition FiniteProj (A B : Type) (p : A -> B) : Prop :=
  exists l : list A, FullProj p l.
