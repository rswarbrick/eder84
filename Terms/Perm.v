Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinModComp.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.FPCard.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.ProjSet.
Require Import Top.Terms.Term.
Require Import Top.Terms.Subst.

Set Implicit Arguments.

(** To represent a substitution that maps variables to variables, we
    define a [var_subst] to be a finite endomorphism on V. Composing
    on the left with [varTerm] gives the substitution itself. *)

Section var_subst.
  Definition var_subst {V} (s : V -> V) := fin_endo s.

  Variable L : lType.
  Notation V := (Term.V L).

  Definition var_subst_subst (s : V -> V) : V -> Term L :=
    compose (varTerm L) s.

  Hypothesis decV : forall x y : V, {x = y} + { ~ x = y }.
  Hypothesis decF : forall x y : Lmodule.F L, {x = y} + { ~ x = y }.

  (** Since we're generally interested in finite substitutions, we
      would hope that a [var_subst] induces one, and it does. *)

  Lemma fin_subst_var_subst s
    : var_subst s -> fin_subst L (var_subst_subst s).
  Proof.
    intro finH; unfold var_subst_subst; simpl.
    eapply (compose_fin_mod decV decV (decTerm decV decF) _ _
                            finH
                            (fin_mod_i (varTerm L))).
    Unshelve.
    - destruct 1 as [ x eltH ]; contradiction eltH; auto.
    - intro d; destruct d as [ x eltH ]; contradiction eltH; auto.
  Qed.

  Lemma var_subst_compose (t s : V -> V)
    : var_subst s -> var_subst t -> var_subst (compose t s).
  Proof.
    apply (compose_fin_endo decV).
  Qed.
End var_subst.

(** We're particularly interested in permutations, defined to be
    bijective variable substitutions. Since "bijective" is a little
    bit difficult to pin down in Coq, we'll ask that there is an
    "extensionally inverse" map. That is, the maps should compose to a
    map that equals the identity on every input. *)

Definition ext_inverse {A B : Type} (f : A -> B) (g : B -> A) :=
  (forall a, g (f a) = a) /\ (forall b, f (g b) = b).

(** In a minute, we're going to construct an inverse to a finite
    endomorphism, using [inj_endo_is_invertible]. That takes a little
    bit of tidying up, though, because we'll only get the inverse on
    the domain of the original endomorphism.

    Here, we show that we can extend the inverse map in a finitary
    way, provided that [a <> f a] implies that [f a <> f (f a)] (a
    fact which is implied by injectivity of [f]). *)

Section extend_inverse.
  Variables A : Type.
  Variable f g : A -> A.

  Hypothesis fH : fin_mod id f.
  Hypothesis decA : forall a a' : A, {a = a'} + {a <> a'}.

  Hypothesis gfH :
    forall d : mod_dom id f, g (f (proj1_sig d)) = proj1_sig d.
  Hypothesis fgH :
    forall d : mod_dom id f, f (g (proj1_sig d)) = proj1_sig d.

  Hypothesis f_preserves_dom :
    forall a : A, f a <> a -> f (f a) <> f a.

  Local Definition clamp_g (a : A) : A := if decA (f a) a then a else g a.

  Local Lemma mod_f_imp_mod_clamp_g a (H : mod_elt id f a)
    : mod_elt id clamp_g a.
  Proof.
    specialize (fgH (exist _ a H)). simpl in fgH.
    unfold mod_elt, id, clamp_g in *.
    destruct (decA (f a) a); congruence.
  Qed.

  Local Definition cast_clamp_g (d : mod_dom id f) : mod_dom id clamp_g :=
    let (a, H) := d in exist _ a (mod_f_imp_mod_clamp_g H).

  Local Lemma fin_clamp_g : fin_mod id clamp_g.
  Proof.
    destruct fH as [ l fullH ].
    exists (map cast_clamp_g l).
    intro d; destruct d as [ a aH ]; simpl.
    unfold mod_elt in aH.
    assert (fneH : f a <> id a).
    - unfold clamp_g in aH; destruct (decA (f a) a); auto.
    - apply in_map_iff.
      specialize (fullH (exist _ a fneH));
        unfold InProj in fullH; simpl in fullH.
      rewrite in_map_iff in fullH.
      destruct fullH as [ d dH ]; destruct dH as [ adH inH ].
      exists (cast_clamp_g d).
      constructor.
      + destruct d; tauto.
      + apply in_map; auto.
  Qed.

  Local Lemma gf_id_eq a
    : a = f a -> clamp_g (f a) = a.
  Proof.
    unfold clamp_g.
    intro eqH; rewrite <- !eqH; destruct (decA a a); tauto.
  Qed.

  Local Lemma gf_id_ne a
    : a <> f a -> clamp_g (f a) = a.
  Proof.
    intro neH; unfold clamp_g.
    specialize (gfH (exist _ a (not_eq_sym neH))); simpl in gfH.
    specialize (f_preserves_dom (not_eq_sym neH)).
    case (decA (f (f a)) (f a)); congruence.
  Qed.

  Local Lemma fg_id_eq a
    : a = f a -> f (clamp_g a) = a.
  Proof.
    unfold clamp_g; intro eqH; rewrite <- eqH; destruct (decA a a); congruence.
  Qed.

  Local Lemma fg_id_ne a
    : a <> f a -> f (clamp_g a) = a.
  Proof.
    intro neH; unfold clamp_g.
    destruct (decA (f a) a); auto.
    specialize (fgH (exist _ a (not_eq_sym neH))); simpl in fgH.
    auto.
  Qed.

  Lemma ext_inverse_clamp_g : ext_inverse f clamp_g.
  Proof.
    constructor; intro a;
      destruct (decA (f a) a);
      auto using gf_id_eq, gf_id_ne, fg_id_eq, fg_id_ne.
  Qed.

End extend_inverse.

(** Now we try to prove Eder's Lemma 2.5, which says that every
    injective var substitution is a permutation.

    To do so, we follow his proof and lift the substitution to a map
    from its domain to itself. Most of the logic should be
    unsurprising. The work to extend the inverse from the domain [D]
    to [V] was basically done in the [extended_inverse] section above.

    The one not-so-obvious thing is the [maybe_id] hypothesis. The
    problem is that [inj_endo_is_invertible] needs some element of [D]
    to map uninteresting elements to. Of course, if [s] is the
    identity substitution then [D] is empty and this won't work! *)

Section inj_subst.
  Variable V : Type.
  Variable s : V -> V.
  Variable substH : var_subst s.
  Hypothesis injH : forall v w : V, s v = s w -> v = w.

  (** We'll define [D] to be the domain of [s] *)
  Local Definition D : Type := mod_dom id s.

  (** The first part of the argument in the paper explains why a
      variable [v] in the domain must be mapped to another element of
      the domain. The point is that otherwise [f (f v) = f v] and
      injectivity would then imply that [f v = v], contradicting the
      fact that [v] was in the domain. *)

  Local Lemma f_maps_into_dom v : s v <> v -> s (s v) <> s v.
  Proof.
    intuition.
  Qed.

  Local Lemma maps_into_dom {v}
    : mod_elt id s v -> mod_elt id s (s v).
  Proof.
    unfold mod_elt, id; apply f_maps_into_dom.
  Qed.

  (** Knowing this we can construct a natural map, where the top map
      is [D -> D] and the bottom map is [f : V -> V]. We'll name the
      vertical maps at either side as [proj] *)

  Local Definition proj : D -> V := md_elt.

  Local Definition finite_proj : FiniteProj proj := substH.

  Local Definition top_map : D -> D :=
    fun d => let (v, eltH) := d in exist _ (s v) (maps_into_dom eltH).

  Local Lemma top_map_natural
    : is_nat_map proj proj (top_map, s).
  Proof.
    intro d; destruct d as [ v H ]; auto.
  Qed.

  Local Definition nmap : nat_map proj proj :=
    exist _ (top_map, s) top_map_natural.

  (** The injectivity lemma, [injH], then implies that [nmap] is an
      [inj_nat_map]. *)

  Local Lemma inj_nmap : inj_nat_map nmap.
  Proof.
    intros d0 d1; unfold nmap, proj; auto.
  Qed.

  (** With decidability on [V], we can strengthen [maps_into_dom]
      significantly. *)

  Hypothesis decV : forall x y : V, {x = y} + { ~ x = y }.

  Local Lemma idem_iff_ident {v}
    : s (s v) = s v <-> s v = v.
  Proof.
    split; try congruence.
    destruct (decV (s v) v); auto.
  Qed.

  Local Definition lift_non_idem (v : V) (neH : s (s v) <> s v) : D.
  refine (exist _ v _).
  unfold id.
  intro eqH.
  rewrite <- idem_iff_ident in eqH.
  auto.
  Defined.

  (* If s happens to be the identity, this was all a bit pointless: we
     can't use [inj_endo_is_invertible] to produce the inverse map,
     because we have no element of [D]. But, of course, if [s] is the
     identity, it's pretty easy to find an inverse! *)
  Lemma ext_inverse_id
    : (forall v, s v = v) -> ext_inverse s s.
  Proof.
    intro svH; split; intros; rewrite !svH; auto.
  Qed.

  Variable v0 : V.
  Hypothesis v0H : s v0 <> v0.

  (* If [s] isn't the identity, there's at least one [v] where [s v <>
     v], giving us an element of [D]. Give a name to the [nat_map]
     from whose base we can extract the inverse. *)
  Local Definition inv_nmap : nat_map proj proj :=
    inj_endo_inv inj_nmap decV substH (exist _ v0 v0H) (proj2_sig substH).

  Local Definition inj_subst_inv : V -> V :=
    clamp_g s (nm_bot (inv_nmap)) decV.

  Lemma ext_inverse_inj_subst : ext_inverse s inj_subst_inv.
  Proof.
    apply ext_inverse_clamp_g; auto;
      apply (inj_endo_is_invertible inj_nmap _ _ (exist _ v0 v0H)).
  Qed.
End inj_subst.
