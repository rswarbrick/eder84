(** This library is concerned with what it calls _finite
    endomorphisms_. That is, maps on a set that fix all but finitely
    many elements.

    We actually start by defining a more general type of map, called a
    [fin_mod] ("finite modification"). This is based on some map [f :
    A -> B] but differs at finitely many points. When [f] is the
    identity on [A], we get the [fin_endo] case.

    One use case for [fin_mod] is when you have a smaller type
    injecting into a bigger type. In classical maths, you might say
    that [f : A -> B] is an endomorphism because it happens to take
    values in the image of [A]. Here, we can talk about it being a
    modification of the injection [A -> B].

*)

Require Import Lists.List.
Require Import Logic.FinFun.
Require Import Logic.Decidable.
Require Import Program.Basics.
Require Import Bool.

Require Import SymbComp.NatMap.
Require Import SymbComp.FinSet.

Set Implicit Arguments.

(** * Basic definitions

    We start by fixing a underlying sets, [A] and [B], and a base map
    [i : A -> B]. This is the map that is to be modified. Then we
    define a finite modification ([fin_mod]) to be a map [f : A -> B]
    where only finitely many elements are mapped differently by [f]
    and [i]. We define this with the help of the [SymbComp.FinSet]
    library's [FiniteProj] predicate.

*)

Section FinMod.
  Variable A B : Type.
  Variable i : A -> B.

  Definition mod_elt f (a : A) := f a <> i a.
  Definition mod_dom f := sig (mod_elt f).
  Definition md_elt f : mod_dom f -> A := @proj1_sig A (mod_elt f).
  Definition fin_mod f : Prop := FiniteProj (@md_elt f).

  (** As you would expect, [i] is a [fin_mod]. Indeed, its
      modification domain is empty. *)
  Lemma fin_mod_i : fin_mod i.
  Proof.
    unfold fin_mod, FiniteProj.
    exists nil.
    unfold FullProj.
    intro a. destruct a as [ a H ].
    unfold mod_elt in H.
    contradiction.
  Qed.

  Definition mod_dom_cast {f g} (H : forall a, f a = g a) (d : mod_dom f)
    : mod_dom g := match d with
                   | exist _ a H' =>
                     exist _ a (eq_ind (f a) (fun b => b <> i a) H' _ (H a))
                   end.

  Lemma fin_mod_ex f g
    : (forall a : A, f a = g a) -> fin_mod f -> fin_mod g.
  Proof.
    unfold fin_mod.
    intros eqH finF.
    assert (natH : is_nat_map (md_elt (f := f)) (md_elt (f := g))
                              (mod_dom_cast eqH, id));
      try (unfold is_nat_map; intro a; destruct a; auto).
    apply (finite_surj (m := exist _ _ natH) finF).
    unfold SurjectiveProj.
    intro d'; destruct d' as [ a gaH ]; simpl; unfold id.
    clear natH.
    specialize (eqH a).
    assert (faH : mod_elt f a);
      try (unfold mod_elt in *; rewrite eqH; tauto).
    exists (exist _ a faH).
    tauto.
  Qed.
End FinMod.

(** * Finite endomorphisms

    A special case of a [fin_mod] is when [B = A]. Then we call a
    [fin_mod] of the identity map [fin_endo].
*)

Definition fin_endo {A : Type} (f : A -> A) : Prop := fin_mod id f.

(** The identity map is a FinEndo (since it's [i]) *)

Lemma fin_endo_id {A : Type} : @fin_endo A id.
Proof.
  unfold fin_endo.
  apply fin_mod_i.
Qed.

(** ** Composition

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

    Local Definition map_a (a : A) : option (mod_dom id (compose g f)) :=
      match decA (g (f a)) (id a) with
      | left _ => None
      | right neH => Some (exist _ a (fun eqH => neH eqH))
      end.

    Local Definition proj0 : (mod_dom id g + mod_dom id f) -> (A + A) :=
      sumf (md_elt (f := g)) (md_elt (f := f)).

    Local Definition proj1 : (mod_dom id (compose g f)) -> A :=
      md_elt (f := compose g f).

    Local Definition top_map (dd : (mod_dom id g + mod_dom id f))
      : option (mod_dom id (compose g f)) :=
      map_a (match dd with
             | inl dg => md_elt dg
             | inr df => md_elt df
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

    Ltac use_decA :=
      simpl; unfold bot_map, map_a;
      match goal with
      | [ |- context [decA ?a ?a'] ] => case (decA a a')
      | _ => contradiction
      | _ => reflexivity
      | _ => simpl
      end.

    Local Lemma surjH
      : forall d' : mod_dom id (compose g f),
        exists dd : mod_dom id g + mod_dom id f,
          bot_map (proj0 dd) = Some (proj1 d').
    Proof.
      intro d'. destruct d' as [ a in_dom_a ].
      case (decA (f a) a) as [ feqH | fneH ].
      - case (decA (g (f a)) (f a)) as [ gfeqH | gfneH ].
        + contradiction in_dom_a; clear in_dom_a.
          rewrite <- feqH at 2; apply gfeqH.
        + rewrite feqH in gfneH; rename gfneH into gneH.
          exists (inl (exist _ a gneH)).
          repeat use_decA.
      - exists (inr (exist _ a fneH)).
        repeat use_decA.
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
    Variable A B : Type.
    Variable i : A -> B.
    Variable in_spt : A -> Prop.
    Hypothesis dec_in_spt : forall a, {in_spt a} + {~ in_spt a}.

    Definition restrict_map (f : A -> B) (a : A) : B :=
      if dec_in_spt a then f a else i a.

    (** We now have to show that the restriction of a [fin_mod] map is
      itself [fin_mod]. A stronger result that we might wish to prove
      later is that if [in_support] has some finiteness properties
      then restricting _any_ map by it yields a [fin_endo] map. But
      that's not what we're doing here.

      The actual definition of the top map is rather unpleasant, and
      we have to prove an auxiliary lemma to build it, but ignoring
      the proof stuff, the map is just [Some].

     *)
    Variable f : A -> B.

    Local Definition proj0 : mod_dom i (restrict_map f) -> A :=
      @md_elt A B i (restrict_map f).

    Local Definition proj1 : mod_dom i f -> A := @md_elt A B i f.

    Ltac dec_in_spt a :=
      destruct (dec_in_spt a); try tauto.

    Local Definition dom_proof a
      : mod_elt i f a -> in_spt a -> mod_elt i (restrict_map f) a.
    Proof.
      unfold mod_elt, restrict_map in *; dec_in_spt a.
    Qed.

    Local Definition h (x : mod_dom i f)
      : option (mod_dom i (restrict_map f)) :=
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
      unfold h, k; dec_in_spt a.
    Qed.

    Local Lemma hk_no_spt a H
      : ~ in_spt a -> option_map proj0 (h (exist _ a H)) = k a.
    Proof.
      unfold h, k; dec_in_spt a.
    Qed.

    Local Lemma natH0
      : forall x : mod_dom i f, option_map proj0 (h x) = k (proj1 x).
    Proof.
      intro x. destruct x as [ a H ].
      dec_in_spt a; unfold proj1, md_elt, proj1_sig.
      - apply (hk_in_spt H); tauto.
      - apply (hk_no_spt H); tauto.
    Qed.

    Lemma in_dom_from_restrict a : mod_elt i (restrict_map f) a -> mod_elt i f a.
    Proof.
      unfold mod_elt, restrict_map in *; dec_in_spt a.
    Qed.

    Definition restrict_dom_inject (x : mod_dom i (restrict_map f))
      : mod_dom i f :=
      let (a, domH) := x in exist _ a (in_dom_from_restrict domH).

    Lemma restrict_preserves_fin_mod
      : fin_mod i f -> fin_mod i (restrict_map f).
    Proof.
      apply (finite_left_inverse _ _ _ natH0 restrict_dom_inject id);
        intro x; destruct x as [ a H ]; try tauto.
      simpl; unfold k, id; unfold mod_elt, restrict_map in H; dec_in_spt a.
    Qed.
  End Restrictions.
End Restrictions.
Import Restrictions.
Export Restrictions.
