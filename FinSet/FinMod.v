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

Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.ProjSet.
Require Import Top.FinSet.FinSet.

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
  Definition fin_mod f : Type := FiniteProj (@md_elt f).

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
End FinMod.

Arguments mod_elt {A B} i f.
Arguments mod_dom {A B} i f.
Arguments md_elt {A B i f} d.
Arguments fin_mod {A B} i f.
Arguments fin_mod_i {A B} i.

Definition mod_dom_cast {A B} {i j f g : A -> B} (d : mod_dom i f)
  : i (md_elt d) = j (md_elt d) ->
    f (md_elt d) = g (md_elt d) -> mod_dom j g.
  refine (match d with
          | exist _ a H' =>
            fun ijH fgH => exist _ a _
          end).
  unfold mod_elt in H'.
  simpl in ijH, fgH.
  unfold mod_elt.
  rewrite <- fgH, <- ijH.
  exact H'.
Defined.

Lemma md_elt_mod_dom_cast {A B} {i j f g : A -> B} {d}
      (ijH : i (md_elt d) = j (md_elt d))
      (fgH : f (md_elt d) = g (md_elt d))
  : md_elt (mod_dom_cast d ijH fgH) = md_elt d.
Proof.
  destruct d. auto.
Qed.

Lemma fin_mod_ex {A B : Type} (i j f g : A -> B)
  : (forall a : A, i a = j a) ->
    (forall a : A, f a = g a) ->
    fin_mod i f -> fin_mod j g.
Proof.
  intros ijH fgH fmH.
  destruct fmH as [ fl fullH ].
  exists (map (fun df =>
                 mod_dom_cast df (ijH (md_elt df)) (fgH (md_elt df))) fl).
  intro dg.
  specialize (fullH (mod_dom_cast dg
                                  (sym_eq (ijH (md_elt dg)))
                                  (sym_eq (fgH (md_elt dg))))).
  rewrite md_elt_mod_dom_cast in fullH.
  unfold InProj in *.
  rewrite in_map_iff in fullH.
  destruct fullH as [ df dfH ].
  rewrite map_map, in_map_iff.
  exists df.
  rewrite md_elt_mod_dom_cast.
  auto.
Qed.

Lemma empty_mod_elim
      {A B : Type} (decB : forall b b' : B, {b = b'} + {b <> b'})
      (i f : A -> B)
  : FullProj (@md_elt A B i f) nil -> forall a, f a = i a.
Proof.
  intros fullH a.
  destruct (decB (f a) (i a)) as [ | neH ]; auto.
  contradiction (fullH (exist _ a neH)).
Qed.

Fixpoint map_if {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons a l' => match f a with
                 | Some b => cons b (map_if f l')
                 | None => map_if f l'
                 end
  end.

Lemma map_map_if {A B C : Type} (f : A -> option B) (g : B -> C) l
  : map g (map_if f l) = map_if (fun a => option_map g (f a)) l.
Proof.
  induction l as [ | a l IH ]; auto.
  unfold map_if at 1; fold (map_if f).
  unfold map_if at 3; fold (map_if (fun a => (option_map g (f a)))).
  case (f a); intros; simpl; auto using f_equal.
Qed.

Lemma in_map_if {A B : Type} {f : A -> option B} a b l
  : In a l -> f a = Some b -> In b (map_if f l).
Proof.
  intros inH faH.
  induction l as [ | a' l IH ]; auto.
  unfold map_if; fold (map_if f).
  destruct inH as [ -> | neH ].
  - rewrite faH; auto with datatypes.
  - destruct (f a'); auto with datatypes.
Qed.

Lemma fin_domain_implies_fin_mod {A B : Type} (i f : A -> B) {l : list A}
  : (forall x y : B, {x = y} + { ~ x = y }) ->
    Full l ->
    fin_mod i f.
Proof.
  intros decB fullH.
  exists (map_if (fun a => match decB (f a) (i a) with
                           | left _ => None
                           | right neH => Some (exist _ a neH)
                           end) l).
  intro d.
  unfold InProj.
  rewrite map_map_if.
  destruct d as [ a aH ].
  apply (in_map_if a); auto.
  destruct (decB (f a) (i a)); auto; contradiction.
Qed.

(** * Finite endomorphisms

    A special case of a [fin_mod] is when [B = A]. Then we call a
    [fin_mod] of the identity map [fin_endo].
*)

Definition fin_endo {A : Type} (f : A -> A) : Type := fin_mod id f.

(** The identity map is a FinEndo (since it's [i]) *)

Lemma fin_endo_id {A : Type} : @fin_endo A id.
Proof.
  unfold fin_endo.
  apply fin_mod_i.
Qed.

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

    Local Definition dom_proof {a}
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

    Local Lemma hk_in_spt {a} H
      : in_spt a -> option_map proj0 (h (exist _ a H)) = k a.
    Proof.
      unfold h, k; dec_in_spt a.
    Qed.

    Local Lemma hk_no_spt {a} H
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

    Lemma in_dom_from_restrict {a}
      : mod_elt i (restrict_map f) a -> mod_elt i f a.
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

Arguments restrict_map {A B} i in_spt dec_in_spt f a.
