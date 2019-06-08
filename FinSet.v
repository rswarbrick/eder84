(**
  This library is concerned with finiteness of a set under some
  projection operation. The motivation is to deal with types that
  contain some sort of propositional part. That is, you might have a
  set that would be represented in normal maths as $A = \{ x \,|\, P\,
  x \}$.

  This set is represented by a Coq sigma types of the form [sig
  P]. However finiteness of [sig P] isn't really very interesting: You
  care about the number of the elements, x, but don't care about how
  many proofs of P x there are.

  We will work by talking about finiteness of the image of some
  projection operation [p : A -> B]. Maybe [A] is a sigma type like
  above and [p] is projection onto the first coordinate. We carefully
  _don't_ construct the type that is the image of [p]: that would have
  exactly the same problems as the original type (two apparently
  identical elements are different because we don't have proof
  irrelevance).

 *)

Require Import Lists.List.
Require Import Program.Basics.
Require Import Logic.FinFun.

Require Import SymbComp.NatMap.

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

(** * The disjoint sum of two finite sets is finite

   With projections, this might mean an internal or external sum (is
   the target [B + B'] or just [B]?). We'll prove the external version
   here and then use a surjectivity result to prove the internal
   version as a corollary later% (see section
   \ref{sec:int-sum-finite})%.

   To prove this, you take a list for each projection, map the
   elements into an option type and then join the two resulting lists
   together. The new projection we need is a map [A + A' -> B + B']
   which is constructed with [sumf], defined below (it's just the
   external sum of two maps).

 *)
Lemma finite_sum {A A' B B': Type} (p : A -> B) (p' : A' -> B')
      : FiniteProj p -> FiniteProj p' -> FiniteProj (sumf p p').
Proof.
  (* Unfold finiteness and then unpack the assumptions *)
  unfold FiniteProj.
  intros exP exP'.
  destruct exP as [ la fpA ].
  destruct exP' as [ la' fpA' ].
  (* The full element will be map inl la + map inr la' *)
  exists ((map inl la) ++ (map inr la')).
  unfold FullProj. intro aa.
  (* Proceed by case analysis: is aa in A or A'? *)
  destruct aa as [ a | a' ].
  - clear fpA'.
    apply in_proj_or_app; left.
    apply (in_proj_map (nat_map_inl p p')).
    unfold FullProj in fpA. apply fpA.
  - clear fpA.
    apply in_proj_or_app; right.
    apply (in_proj_map (nat_map_inr p' p)).
    unfold FullProj in fpA'. apply fpA'.
Qed.

(** * The surjective image of a finite set is finite.

   Here, we have to be a little careful with what we mean by
   "surjective". Remember that our projection [p: A -> B] needn't
   itself be surjective: we're only interested in the image of [p] as
   a subset of [B] (onto which p is obviously surjective).

   So we define a [SurjectiveProj] predicate. For the usual natural
   square% (see equation \ref{eq:natsq})%, saying that it is
   [SurjectiveProj] means that [g] restricted to the image of [p]
   surjects onto the image of [p']. We define this explicitly, rather
   than with Coq's builtin [Surjective] predicate (because we don't
   want to talk about the image of [p] as a type in itself).

   Note that this surjectivity definition doesn't imply that the upper
   map, f, is surjective. That's a good thing, because in the
   motivating sigma type example, we definitely don't want to claim
   that we can map to every proof "upstairs".

*)

Definition SurjectiveProj
           {A B A' B' : Type} (p : A -> B) (p' : A' -> B') (m : nat_map p p') :=
  forall a' : A', exists a : A, nm_bot m (p a) = p' a'.

Lemma finite_surj
      {A A' B B' : Type} (p : A -> B) (p' : A' -> B') (m : nat_map p p')
  : FiniteProj p -> SurjectiveProj m -> FiniteProj p'.
Proof.
  unfold FiniteProj.
  intros fullP surjH.
  destruct fullP as [l fullH].
  exists (map (nm_top m) l).
  unfold FullProj; intro a'.
  unfold SurjectiveProj in surjH.
  destruct (surjH a') as [ a aH ]; clear surjH.
  rewrite <- aH.
  apply in_proj_map.
  unfold FullProj in fullH.
  apply fullH.
Qed.

(** There's a degenerate case of [finite_surj], where we actually just
   have a second (surjective) projection to apply after [p]. Note that
   this asks for a genuine surjection from [B] to [B']. You could
   weaken this slightly, but at that point you may as well just use
   [finite_surj] explicitly.  *)

Lemma finite_surj_vert {A B B' : Type} (p : A -> B) (q : B -> B')
  : FiniteProj p -> Surjective q -> FiniteProj (compose q p).
Proof.
  intros fpH surjH.
  set (m0 := nat_map_v p).
  set (m1 := nat_map_diag id q).
  assert (midH : forall b : B, nm_top m1 b = nm_bot m0 b); auto.
  apply (finite_surj (m := nat_map_comp_v m0 m1 midH)); auto.
  unfold SurjectiveProj, compose; simpl.
  intro a. exists a. auto.
Qed.

(** ** Finiteness of an internal sum %\label{sec:int-sum-finite}%

  Now for the promised internal sum version of [finite_sum]. The proof
  of this just goes by composing the external sum with a folding
  operation, [codiag: A + A -> A], defined in the obvious way.

 *)
Definition codiag {A : Type} (a : A + A) : A :=
  match a with
  | inl a => a
  | inr a => a
  end.

Lemma surj_codiag A : Surjective (@codiag A).
Proof.
  unfold Surjective.
  intro a.
  exists (inl a).
  unfold codiag.
  exact eq_refl.
Qed.

Definition internal_sumf {A A' B} (f : A -> B) (g : A' -> B) : A + A' -> B :=
  compose codiag (sumf f g).

Lemma finite_sum_internal {A A' B} (p : A -> B) (p' : A' -> B)
  : FiniteProj p -> FiniteProj p' -> FiniteProj (internal_sumf p p').
Proof.
  unfold internal_sumf.
  intros fpH fpH'.
  apply finite_surj_vert.
  - exact (finite_sum fpH fpH').
  - exact (@surj_codiag B).
Qed.

(** * Finiteness with injections

   Now we want to prove something related to the basic result from
   maths that if I have an injection [f : X -> Y] and know that [Y] is
   finite, then [X] must be finite too.

   To prove finiteness in Coq, you need to build some form of a
   listing of [X]. Merely knowing that [f] is injective isn't going to
   be enough to construct this from a listing of [Y]: we'd need some
   non-constructive choice axiom to pick elements of [X] in the
   inverse image. In classical maths, a map [f] is injective if and
   only if it has a left inverse [g] (so $g \circ f =
   \mathrm{id}$). We'll ask to be given this map, which does the "find
   something in the inverse image" operation for us.

   In practice, that's a pain to produce, so we'll actually ask for a
   map [g : Y -> option X], satisfying [g (f a) = Some a]. Note that
   this implies that no element in the image of [f] gets mapped to
   [None], so in a non-constructive setting we could extend [g] to a
   map [Y -> X] by mapping [None] to some arbitrary element of [X].

   ** Mapping and filtering

   If we start with a listing of the image of [p'], we can apply our
   partial inverse to each element to get a list of [option
   A]'s. Filtering out the [None]'s gives a list of elements of [A],
   which generate our listing of the image of [p].
*)

Section map_filter.
  Variables (A A' : Type).
  Variable (h : A' -> option A).

  Fixpoint map_filter (l : list A') : list A :=
    match l with
    | nil => nil
    | cons a' l' => match h a' with
                    | Some a => a :: map_filter l'
                    | None => map_filter l'
                    end
    end.

  Lemma map_filter_inv a' l
    : map_filter (a' :: l) = match h a' with
                                | Some a => a :: map_filter l
                                | None => map_filter l
                                end.
  Proof. reflexivity. Qed.

  (**

     We want to precisely characterise when an element is in the image
     of [map_filter]. To make sense of this, we need to do a little
     more setup. The commutative diagram we're interested in is:
     % \begin{equation}
       \begin{tikzcd}
         A' \arrow[r, "h"] \arrow[d, "p'"] &
         \mathrm{option}\,A \arrow[d] &
         A \arrow[l, "\mathrm{Some}"'] \arrow[d, "p"]
         \\
         B' \arrow[r, "k"] &
         \mathrm{option}\,B &
         B
         \arrow[l, "\mathrm{Some}"']
       \end{tikzcd}
     \end{equation} %
     where the vertical map in the middle is [option_map p]. The right hand
     square commutes for free by the definition of [option_map]. Commutativity
     of the left hand square is the [natH] hypothesis below.

   *)

  Variables (B B' : Type).
  Variable (k : B' -> option B).
  Variable (p : A -> B).
  Variable (p' : A' -> B').
  Hypothesis (natH: forall a', option_map p (h a') = k (p' a')).

  Lemma in_proj_map_filter l a
    : (exists a', k (p' a') = Some (p a) /\ InProj p' (p' a') l) ->
      InProj p (p a) (map_filter l).
  Proof.
    intros H; destruct H as [ a' H ]; destruct H as [ mapH inH ].
    induction l as [ | x' l IH ].
    - contradiction inH.
    - destruct (in_proj_inv inH); clear inH.
      + clear IH.
        (* This is the case where we're supposed to get a hit at the
           start of the list. We have some x' where p' x' = p' a' (both
           elements of B'). *)
        rewrite <- H in mapH; clear H.
        rewrite <- (natH x') in mapH; clear natH.
        (* Now mapH says that option_map p (h x') = Some (p a).
           That must mean h x is Some something (by looking at the
           definition of option_map) *)
        case_eq (h x');
          try (intro U; rewrite U in mapH; discriminate mapH).
        intros x hx'H.
        (* Now we can do a little unpacking to conclude that p x
           equals p a. *)
        assert (p_eq_H: p x = p a);
          try (rewrite hx'H in mapH; inversion mapH; exact eq_refl).
        rewrite map_filter_inv, hx'H.
        apply in_proj_eq.
        exact p_eq_H.
      + (* This is the easier case, where we just pass stuff through
           induction. *)
        enough (InProj p (p a) (map_filter l)) as Hrst.
        * rewrite map_filter_inv.
          destruct (h x'); try (apply in_proj_cons); exact Hrst.
        * apply IH. exact H.
  Qed.

  Lemma full_proj_map_filter l
    : (forall a, exists a' : A', k (p' a') = Some (p a) /\ InProj p' (p' a') l) ->
      FullProj p (map_filter l).
  Proof.
    intro H; unfold FullProj; intro a.
    apply in_proj_map_filter, H.
  Qed.

  Variable f : A -> A'.
  Variable g : B -> B'.
  Hypothesis natfgH: forall a, p' (f a) = g (p a).
  Hypothesis kleftH: forall a, k (g (p a)) = Some (p a).

  (** We finally get to the full lemma. The big commutative diagram
     can be drawn as:
     % \begin{equation}
       \begin{tikzcd}
         A \arrow[rr, "f"] \arrow[dr, hookrightarrow] \arrow[ddd, "p"'] &
         &
         A' \arrow[ld, "h"] \arrow[ddd, "p'"]
         \\
           & \mathrm{option}\,A \arrow[d, "\mathrm{option\_map}(p)"'] &
         \\
           & \mathrm{option}\,B &
         \\
         B \arrow[ur, hookrightarrow] \arrow[rr, "g"]& & B' \arrow[ul, "k"']
       \end{tikzcd}
     \end{equation} %


     The left hand square commutes by definition of [option_map]. The outer
     square commutes, by the hypothesis [natfgH]. The bottom left half of the
     diagram commutes by the hypothesis [kleftH] (because
     [option_map p (Some a) = Some (p a)]).

     The point is that the existence of [k], which acts as (almost) the left
     inverse of the restriction of [g] to the image of [p] is equivalent to
     injectivity of [g] on the image of [p] in a non-constructive setting.
   *)

  Lemma finite_left_inverse : FiniteProj p' -> FiniteProj p.
  Proof.
    unfold FiniteProj.
    destruct 1 as [ l' l'H ].
    exists (map_filter l').
    apply full_proj_map_filter.
    intro a.
    unfold FullProj in l'H.
    exists (f a).
    rewrite (natfgH a).
    rewrite kleftH; clear kleftH.
    constructor; try exact eq_refl.
    enough (H: g (p a) = p' (f a)).
    - rewrite H. apply l'H.
    - rewrite natfgH; exact eq_refl.
  Qed.
End map_filter.

(** * Finiteness of option types

     This section shows that a type is finite if and only if the
     corresponding option type is. Use [finite_option_intro] to infer
     that an option type is finite. More usefully,
     [finite_option_elim] allows you to prove finiteness of an option
     type in order to conclude finiteness of the underlying type.

*)

Section finite_option.
  Variables (A B : Type).
  Variable (p : A -> B).

  Lemma finite_option_intro : FiniteProj p -> FiniteProj (option_map p).
  Proof.
    unfold FiniteProj.
    intro finP.
    destruct finP as [ l fullL ].
    exists (cons None (map Some l)).
    unfold FullProj.
    intro x; destruct x as [ a | ].
    - apply in_proj_cons.
      apply (in_proj_map (nat_map_some p)).
      unfold FullProj in fullL. apply fullL.
    - apply in_proj_eq; reflexivity.
  Qed.

  Lemma finite_option_elim : FiniteProj (option_map p) -> FiniteProj p.
  Proof.
    assert (H0: (forall a' : option A,
                    option_map p (id a') = id (option_map p a')));
      try reflexivity.
    assert (H1: forall a : A, option_map p (Some a) = Some (p a));
      try reflexivity.
    assert (H2: forall a : A, id (Some (p a)) = Some (p a));
      try reflexivity.
    apply (finite_left_inverse id id p H0 Some Some H1 H2).
  Qed.
End finite_option.

(** * An easier way to prove finiteness with surjectivity

    The [finite_surj] lemma is all very well, but it's sometimes a bit
    difficult to construct exactly the map you want. When trying to
    define a surjection from [p : A -> B] to [p' : A' -> B'], there
    might be some elements, [a], that we don't care about and just
    want to map to [None]. In this section, we do the leg-work to make
    this approach work properly.

*)
Module surj_finite_option.
  Definition lift_opt {A B : Type} (f : A -> option B) (oa : option A)
  : option B :=
    match oa with
    | Some a => f a
    | None => None
    end.

  Section surj_finite_option.
    Variables A A' B B' : Type.
    Variable p: A -> B.
    Variable p': A' -> B'.
    Variable f: A -> option A'.
    Variable g: B -> option B'.

    Hypothesis finP : FiniteProj p.
    Hypothesis natH : forall a, option_map p' (f a) = g (p a).
    Hypothesis surjH : forall a' : A', exists a : A, g (p a) = Some (p' a').

    Local Definition xp := option_map p.
    Local Definition xp' := option_map p'.
    Local Definition xf := lift_opt f.
    Local Definition xg := lift_opt g.

    Local Lemma OfinP : FiniteProj xp.
    Proof.
      exact (finite_option_intro finP).
    Qed.

    Local Lemma OnatH: is_nat_map xp xp' (xf, xg).
    Proof.
      unfold is_nat_map. intro a; destruct a; simpl; auto.
    Qed.

    Local Lemma OsurjH : SurjectiveProj (exist _ (xf, xg) OnatH).
    Proof.
      unfold SurjectiveProj; intro x'; destruct x' as [ a' | ].
      - specialize (surjH a').
        destruct surjH as [ a H ]; clear surjH.
        exists (Some a).
        auto.
      - exists None.
        auto.
    Qed.

    Lemma finite_surj_option : FiniteProj p'.
    Proof.
      apply finite_option_elim.
      apply (finite_surj OfinP OsurjH).
    Qed.
  End surj_finite_option.
End surj_finite_option.

Import surj_finite_option.
Export surj_finite_option.

Local Lemma decompose_pair_eq {A B : Type} (a a' : A) (b b' : B)
  : (a, b) = (a', b') -> a = a' /\ b = b'.
Proof.
  intro H; constructor.
  - pose proof (f_equal fst H) as Ha; simpl in Ha. assumption.
  - pose proof (f_equal snd H) as Hb; simpl in Hb. assumption.
Qed.

Lemma in_proj_neq {A B : Type} (p : A -> B) b a l
  : p a <> b -> InProj p b (a :: l) -> InProj p b l.
Proof.
  intros neq consH.
  destruct (in_proj_inv consH); tauto.
Qed.

(** * Sections of projections

    It isn't the case that we can always make a section for a
    projection (as defined in this theory) - the whole point is that
    [p : A -> B] probably isn't surjective. However, if we are given
    some element of A then we can map elements of B that we don't care
    about to that point. If [l] is nonempty, we could just use the
    first element of the list, but I think it's cleaner to pass in
    this element explicitly (which punts on the problems you get
    otherwise when [A] is empty).
 *)
Section proj_section.
  Variables A B : Type.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Variable p : A -> B.
  Variable a0 : A.

  Fixpoint proj_section (b : B) (l : list A) : A :=
    match l with
    | nil => a0
    | a :: l' => match decB (p a) b with
                 | left eqH => a
                 | right neH => proj_section b l'
                 end
    end.

  Lemma proj_section_if_in b l
    : In b (map p l) -> p (proj_section b l) = b.
  Proof.
    induction l as [ | a l IH ]; try contradiction.
    unfold proj_section; fold proj_section.
    destruct (decB (p a) b) as [ | neH ]; auto.
    destruct 1 as [ | inH ]; tauto.
  Qed.

  Lemma full_proj_section_is_section l
    : FullProj p l ->
      forall a : A, p (proj_section (p a) l) = p a.
  Proof.
    intros.
    apply proj_section_if_in.
    unfold FullProj, InProj in *; auto.
  Qed.
End proj_section.

(** * Inverses of surjective natural maps

  *)
Lemma map_compose
      {A B C : Type}
      (f : A -> B) (g : B -> C) (l : list A)
  : map (compose g f) l = map g (map f l).
Proof.
  induction l as [ | a l IH ]; auto.
  rewrite map_cons, map_cons, map_cons.
  unfold compose at 1.
  apply f_equal; auto.
Qed.

Section surj_map_is_invertible.
  Variables A B C D : Type.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis decD : forall x y : D, {x = y} + {x <> y}.
  Variable p : A -> B.
  Variable q : C -> D.
  Variable f : nat_map p q.

  Variable a0 : A.

  Local Fixpoint bot_map (l : list A) (d : D) : B :=
    match l with
    | nil => p a0
    | a :: l' => match decD (nm_bot f (p a)) d with
                 | left _ => p a
                 | right _ => bot_map l' d
                 end
    end.

  Local Lemma bot_map_if_in d l
    : In d (map (compose (nm_bot f) p) l) ->
      nm_bot f (bot_map l d) = d.
  Proof.
    induction l as [ | a l IH ]; try contradiction.
    unfold bot_map; fold bot_map.
    destruct (decD (nm_bot f (p a)) d); auto.
    rewrite map_cons.
    destruct 1; tauto.
  Qed.

  Local Lemma in_map_compose_if c l
    : SurjectiveProj f -> FullProj p l ->
      In (q c) (map (compose (nm_bot f) p) l).
  Proof.
    intros surjH fullH.
    specialize (surjH c).
    destruct surjH as [ a natH ]; rewrite <- natH; clear natH c.
    (* So we need to use fullness of l wrt p. This gives us some
       element of l that maps down to the same element as [a] does.
     *)
    specialize (fullH a); unfold InProj in fullH.
    rewrite in_map_iff in fullH.
    destruct fullH as [ a' H ]; destruct H as [ peqH inH ].
    rewrite map_compose.
    apply in_map.
    rewrite <- peqH.
    apply in_map; assumption.
  Qed.

  Local Definition top_map (l : list A) (c : C) : A :=
    proj_section decB p a0 (bot_map l (q c)) l.

  Local Lemma bot_map_in_proj (l : list A) d
    : In d (map (compose (nm_bot f) p) l) ->
      InProj p (bot_map l d) l.
  Proof.
    induction l as [ | a l IH ]; auto.
    unfold bot_map; fold bot_map.
    intro inH.
    unfold InProj in *; rewrite map_cons.
    destruct (decD (nm_bot f (p a)) d) as [ <- | neH ].
    - apply in_eq.
    - destruct inH as [ | inH ]; try tauto.
      apply in_cons; auto.
  Qed.

  Variable l : list A.
  Hypothesis surjH : SurjectiveProj f.
  Hypothesis fullH : FullProj p l.

  Local Lemma bot_map_exists_lift c
    : exists a, p a = bot_map l (q c) /\ In a l.
  Proof.
    rewrite <- in_map_iff.
    apply bot_map_in_proj.
    apply in_map_compose_if; auto.
  Qed.

  Local Lemma inv_is_nat_map : is_nat_map q p (top_map l, bot_map l).
  Proof.
    intros c; simpl.
    unfold top_map.
    destruct (bot_map_exists_lift c) as [ a H ].
    destruct H as [ <- inH ].
    apply full_proj_section_is_section; auto.
  Qed.

  Local Definition inv_map : nat_map q p :=
    exist _ (top_map l, bot_map l) inv_is_nat_map.

  Local Lemma inv_map_is_section c
    : nm_bot (nat_map_comp_h inv_map f) (q c) = q c.
  Proof.
    simpl; unfold compose.
    apply bot_map_if_in.
    apply in_map_compose_if; auto.
  Qed.

  Lemma surj_map_is_invertible
    : exists g : nat_map q p,
      forall c, nm_bot (nat_map_comp_h g f) (q c) = q c.
  Proof.
    eauto using inv_map_is_section.
  Qed.
End surj_map_is_invertible.
