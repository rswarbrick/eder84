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

Section DecFinEndo.
  Variable A : Set.
  Hypothesis decA : forall x y : A, {x = y} + { ~ x = y }.

  Variables f g : A -> A.
  Hypothesis finF : fin_endo f.
  Hypothesis finG : fin_endo g.

  (** Firstly, we define the four maps in the square and show that it
      commutes. *)

  Definition map_a (a : A) : option (dom (compose g f)) :=
    match decA (g (f a)) a with
    | left _ => None
    | right neH => Some (exist _ a (fun eqH => neH eqH))
    end.

  Definition proj0 : option (dom g + dom f) -> option (A + A) :=
    option_map (sumf (dom_elt (f := g)) (dom_elt (f := f))).

  Definition proj1 : option (dom (compose g f)) -> option A :=
    option_map (dom_elt (f := compose g f)).

  Definition top_map (x : option (dom g + dom f))
    : option (dom (compose g f)) :=
    match x with
    | None => None
    | Some dd => match dd with
                 | inl dg => map_a (dom_elt dg)
                 | inr df => map_a (dom_elt df)
                 end
    end.

  Definition bot_map (x : option (A + A)) : option A :=
    match x with
      | None => None
      | Some aa => match aa with
                   | inl a => proj1 (map_a a)
                   | inr a => proj1 (map_a a)
                   end
    end.

  Lemma natH : forall x, proj1 (top_map x) = bot_map (proj0 x).
  Proof.
    intro x. destruct x as [ dd | ].
    - destruct dd; reflexivity.
    - reflexivity.
  Qed.

  (** Now, let's prove that [proj0] is indeed [FiniteProj]. It turns
      out that we can do this with a bare proof term: all the work was
      done in the [SymbComp.FinSet] script. *)

  Definition fin_proj0 : FiniteProj proj0 :=
    finite_option_intro (finite_sum finG finF).

  (** To apply the [finite_surj] lemma, we'll need to prove that the
      bottom map has the required surjectivity. This is just a finicky
      case analysis. *)

  Lemma surjH : SurjectiveProj bot_map proj0 proj1.
  Proof.
    unfold SurjectiveProj.
    intro x; destruct x as [ dgf | ].
    - destruct dgf as [ a in_dom_a ].
      case (decA (f a) a) as [ feqH | fneH ].
      + case (decA (g (f a)) (f a)) as [ gfeqH | gfneH ].
        * contradiction in_dom_a; clear in_dom_a.
          rewrite <- feqH at 2; clear feqH.
          unfold compose. exact gfeqH.
        * rewrite feqH in gfneH; rename gfneH into gneH.
          exists (Some (inl (exist _ a gneH))).
          simpl. unfold map_a.
          destruct (decA (g (f a)) a) as [ gfeqH | gfneH ].
          -- rewrite feqH in gfeqH. contradiction.
          -- reflexivity.
      + exists (Some (inr (exist _ a fneH))).
        simpl. unfold map_a.
        destruct (decA (g (f a)) a) as [ gfeqH | gfneH ].
        * contradiction.
        * reflexivity.
    - exists None.
      reflexivity.
  Qed.

  (** We finally have all the bits we need to prove the theorem we
      wanted: that composition preserves the [fin_endo] property.
   *)

  Lemma compose_fin_endo : fin_endo (compose g f).
  Proof.
    unfold fin_endo.
    apply finite_option_elim.
    apply (finite_surj top_map fin_proj0 natH surjH).
  Qed.
End DecFinEndo.
