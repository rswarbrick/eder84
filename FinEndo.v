(** This library is concerned with what it calls _finite
    endomorphisms_. That is, maps on a set that fix all but finitely
    many elements.

    We start by defining these maps and then prove basic properties,
    like the fact that the set of these maps is closed under
    composition.
 *)

Require Import Lists.List.
Require Import Logic.FinFun.
Require Import Logic.Decidable.
Require Import Program.Basics.
Require Import Bool.

Require Import SymbComp.FinSet.

Set Implicit Arguments.

(** * Basic definitions

    We start by fixing an underlying set, [A], and a map [f : A -> A].
    A finite endomorphism is a map from a set to itself such that
    only finitely many elements are not equal to their image. We
    define this with the help of the [SymbComp.FinSet] library's
    [FiniteProj] predicate.
*)

Section FinEndo.
  Variable A : Type.
  Variable f : A -> A.

  (** The [dom] type describes variables that are not fixed by [f].
      The universe of this type is the _domain_ of f (in the the
      terminology of Eder's paper). We can encode this as a sigma
      type, but we name the projection map (partly because it helps
      the type system when we want to define [fin_endo]).
   *)

  Definition in_dom (a : A) := f a <> a.
  Definition dom := sig in_dom.
  Definition dom_elt : dom -> A := @proj1_sig A in_dom.
  Definition fin_endo : Prop := FiniteProj dom_elt.
End FinEndo.

(* The identity map is a FinEndo. In fact, it has an empty domain
   (so the empty list is full for it) even before projection. *)

Lemma fin_endo_id A : fin_endo (@id A).
Proof.
  unfold fin_endo, FiniteProj.
  exists nil.
  unfold FullProj.
  intro a.
  unfold dom, in_dom, id in a.
  destruct a as [x H].
  contradiction (H (eq_refl)).
Qed.

(** * Composition

    We'd like to show that the composition of two [fin_endo] maps is
    itself [fin_endo]. In classical maths, this is pretty easy. The
    point is that if [compose g f] doesn't fix [a] then we know that
    either [f a <> a] or [g (f a) <> a] (and we only care about the
    case when [f a = a], so we're really asserting that [g a <> a]).

    Frankly, we'd probably say "well, obviously" at that point. Being
    a bit more careful, we might note that this gives us a surjection
    [dom g + dom f -> dom (compose g f)]. Well, sort of. What we
    really have is a map [A + A -> A] such that the image of [dom g +
    dom f] covers [dom (compose g f)]. The pesky problem is that it
    might be that [g] reverses [f] on some [a].

    The core of the proof ends up with the square
    % \begin{equation}
      \begin{tikzcd}
        \mathrm{option}(\mathrm{dom}\, g + \mathrm{dom}\, f)
        \arrow[r] \arrow[d] &
        \mathrm{option}(\mathrm{dom}\, (\mathrm{compose}\, g f)
        \arrow[d]
        \\
        \mathrm{option}(A + A) \arrow[r] &
        \mathrm{option}(A)
      \end{tikzcd}
    \end{equation} %
    where the map along the top tries to map [a] to itself, corralling
    the proofs along the way, and maps to [None] if [g (f a) <> a].
    The left hand surjection is a [FiniteProj] because it's a sum of
    them and the map is surjective in the right way. Note that we'll
    need equality in [A] to be decidable in order to actually define
    the map (otherwise we don't know when elements are in the domain).
 *)

Module FinEndoComp.
  Section FinEndoComp.
    Variable A : Type.
    Hypothesis decA : forall x y : A, {x = y} + { ~ x = y }.

    Variables f g : A -> A.
    Hypothesis finF : fin_endo f.
    Hypothesis finG : fin_endo g.

    (** Firstly, we define the four maps in the square and show that it
      commutes. *)

    Local Definition map_a (a : A) : option (dom (compose g f)) :=
      match decA (g (f a)) a with
      | left _ => None
      | right neH => Some (exist _ a (fun eqH => neH eqH))
      end.

    Local Definition proj0 : (dom g + dom f) -> (A + A) :=
      sumf (dom_elt (f := g)) (dom_elt (f := f)).

    Local Definition proj1 : (dom (compose g f)) -> A :=
      dom_elt (f := compose g f).

    Local Definition top_map (dd : (dom g + dom f))
      : option (dom (compose g f)) :=
      map_a (match dd with
             | inl dg => dom_elt dg
             | inr df => dom_elt df
             end).

    Local Definition bot_map (aa : (A + A)) : option A :=
      option_map proj1 (map_a (match aa with
                               | inl a => a
                               | inr a => a
                               end)).

    Local Lemma natH
      : forall dd, option_map proj1 (top_map dd) = bot_map (proj0 dd).
    Proof.
      intro dd; destruct dd; reflexivity.
    Qed.

    (** Now, let's prove that [proj0] is indeed [FiniteProj]. It turns
      out that we can do this with a bare proof term: all the work was
      done in the [SymbComp.FinSet] script. *)

    Local Definition fin_proj0 : FiniteProj proj0 := finite_sum finG finF.

    (** To apply the [finite_surj] lemma, we'll need to prove that the
      bottom map has the required surjectivity. This is just a finicky
      case analysis. *)

    Local Lemma surjH
      : forall d' : dom (compose g f),
        exists dd : dom g + dom f,
          bot_map (proj0 dd) = Some (proj1 d').
    Proof.
      intro d'. destruct d' as [ a in_dom_a ].
      case (decA (f a) a) as [ feqH | fneH ].
      - case (decA (g (f a)) (f a)) as [ gfeqH | gfneH ].
        + contradiction in_dom_a; clear in_dom_a.
          rewrite <- feqH at 2; clear feqH.
          unfold compose. exact gfeqH.
        + rewrite feqH in gfneH; rename gfneH into gneH.
          exists (inl (exist _ a gneH)).
          simpl. unfold bot_map, map_a.
          destruct (decA (g (f a)) a) as [ gfeqH | gfneH ].
          * rewrite feqH in gfeqH. contradiction.
          * reflexivity.
      - exists (inr (exist _ a fneH)).
        simpl. unfold bot_map, map_a.
        destruct (decA (g (f a)) a) as [ gfeqH | gfneH ].
        + contradiction.
        + reflexivity.
    Qed.

    (** We finally have all the bits we need to prove the theorem we
      wanted: that composition preserves the [fin_endo] property.
     *)

    Lemma compose_fin_endo : fin_endo (compose g f).
    Proof.
      unfold fin_endo.
      apply (finite_surj_option proj1 top_map bot_map fin_proj0 natH surjH).
    Qed.
  End FinEndoComp.
End FinEndoComp.
Import FinEndoComp.
Export FinEndoComp.
(** * Restriction

   The domain of a finite endomorphism can be restricted, which means
   that it's forced to be the identity except a certain elements. In a
   classical setting, you talk about restricting to a subset of [A],
   but this doesn't really work here (since subsets aren't really a
   thing). Instead, we'll talk about restricting an endomorphism to
   points where some decidable predicate is true.

 *)
Module Restrictions.
  Section Restrictions.
    Variable A : Type.
    Variable in_spt : A -> Prop.
    Hypothesis dec_in_spt : forall a, {in_spt a} + {~ in_spt a}.

    Definition restrict_map (f : A -> A) (a : A) : A :=
      if dec_in_spt a then f a else a.

    (** We now have to show that the restriction of a [fin_endo] map is
      itself [fin_endo]. A stronger result that we might wish to prove
      later is that if [in_support] has some finiteness properties
      then restricting _any_ map by it yields a [fin_endo] map. But
      that's not what we're doing here.

      The actual definition of the top map is rather unpleasant, and
      we have to prove an auxiliary lemma to build it, but ignoring
      the proof stuff, the map is just [Some].

     *)
    Variable f : A -> A.

    Local Definition proj0 : dom (restrict_map f) -> A :=
      @dom_elt _ (restrict_map f).

    Local Definition proj1 : (dom f) -> A := @dom_elt _ f.

    Local Definition dom_proof a
      : in_dom f a -> in_spt a -> in_dom (restrict_map f) a.
    Proof.
      intros domH sptH.
      unfold in_dom, restrict_map.
      case (dec_in_spt a).
      - intro. unfold in_dom in domH. exact domH.
      - intro H. contradiction (H sptH).
    Qed.

    Local Definition h (x : dom f) : option (dom (restrict_map f)) :=
      let (a, domH) := x in
      match dec_in_spt a with
      | left sptH => Some (exist _ a (dom_proof domH sptH))
      | right _ => None
      end.

    Local Definition k (a : A) : option A :=
      if dec_in_spt a then Some a else None.

    Local Lemma hk_in_spt a H
      : in_spt a -> option_map proj0 (h (exist _ a H)) = k a.
    Proof.
      intros; unfold h, k; destruct (dec_in_spt a).
      - reflexivity.
      - contradiction.
    Qed.

    Local Lemma hk_no_spt a H
      : ~ in_spt a -> option_map proj0 (h (exist _ a H)) = k a.
    Proof.
      intros; unfold h, k; destruct (dec_in_spt a).
      - contradiction.
      - reflexivity.
    Qed.

    Local Lemma natH0 : forall x : dom f, option_map proj0 (h x) = k (proj1 x).
    Proof.
      intro x.
      case x as [ a H ].
      destruct (dec_in_spt a) as [ sptH | nsptH ];
        unfold proj1, dom_elt, proj1_sig.
      - apply (hk_in_spt H sptH).
      - apply (hk_no_spt H nsptH).
    Qed.

    Lemma in_dom_from_restrict a : in_dom (restrict_map f) a -> in_dom f a.
    Proof.
      unfold in_dom, restrict_map in *.
      destruct (dec_in_spt a); auto.
    Qed.

    Definition restrict_dom_inject (x : dom (restrict_map f)) : dom f :=
      let (a, domH) := x in exist _ a (in_dom_from_restrict domH).

    Lemma restrict_preserves_fin_endo
      : fin_endo f -> fin_endo (restrict_map f).
    Proof.
      unfold fin_endo.
      apply (@finite_left_inverse
               (dom (restrict_map f)) (dom f)
               h A A k proj0 proj1 natH0
               restrict_dom_inject id).
      - intro x. destruct x as [ a H ].
        reflexivity.
      - intro x. destruct x as [ a H ].
        simpl; unfold k, id.
        unfold in_dom, restrict_map in H.
        revert H.
        case (dec_in_spt a).
        + reflexivity.
        + contradiction.
    Qed.
  End Restrictions.
End Restrictions.
Import Restrictions.
Export Restrictions.
