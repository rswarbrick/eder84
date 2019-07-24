Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.Terms.Term.
Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinModComp.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.FPCard.

(** A [var_subst] is like a substitution, but induced by a map [V ->
    V]. Composing on the left with [varTerm] gives the substitution
    itself. *)

Section var_subst.
  Definition var_subst (V : Type) := sig (@fin_endo V).

  Variable L : lType.

  Definition var_subst_subst (s : var_subst (Lmodule.V L))
    : Lmodule.V L -> Term L :=
    compose (varTerm L) (proj1_sig s).

  Hypothesis decV : forall x y : Lmodule.V L, {x = y} + { ~ x = y }.
  Hypothesis decF : forall x y : Lmodule.F L, {x = y} + { ~ x = y }.

  (** Since we're generally interested in finite substitutions, we
      would hope that a [var_subst] induces one, and it does. *)

  Lemma fin_subst_var_subst s
    : fin_subst L (var_subst_subst s).
  Proof.
    destruct s as [ f finH ]; simpl.
    apply (compose_fin_mod decV decV (decTerm L decV decF));
      first [ apply finH | apply fin_mod_i | contradiction ].
  Qed.

  Definition compose_var_subst (t s : var_subst (Lmodule.V L)) :=
    match t, s with
      exist _ g gH, exist _ f fH =>
      exist _ (compose g f) (compose_fin_endo decV fH gH)
    end.

  Lemma proj1_sig_compose_var_subst t s
    : proj1_sig (compose_var_subst t s) = compose (proj1_sig t) (proj1_sig s).
  Proof.
    destruct t as [ g gH ]; destruct s as [ f fH ]; auto.
  Qed.
End var_subst.

Arguments var_subst V : assert.
Arguments var_subst_subst {L} s v.
Arguments fin_subst_var_subst {L} decV decF.
Arguments compose_var_subst {L} decV t s.
Arguments proj1_sig_compose_var_subst {L} decV t s.

(** We're particularly interested in permutations, defined to be
    bijective variable substitutions. Since "bijective" is a little
    bit difficult to pin down in Coq, we'll ask that there is an
    "extensionally inverse" map. That is, the maps should compose to a
    map that equals the identity on every input. *)

Definition ext_inverse {A B : Type} (f : A -> B) (g : B -> A) :=
  (forall a, g (f a) = a) /\ (forall b, f (g b) = b).

Definition is_var_perm {V} (s : var_subst V) : Prop :=
  exists t : var_subst V, ext_inverse (proj1_sig s) (proj1_sig t).

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
    let (a, H) := d in exist _ a (mod_f_imp_mod_clamp_g a H).

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
    specialize (f_preserves_dom a (not_eq_sym neH)).
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

  Local Lemma inverses : ext_inverse f clamp_g.
  Proof.
    constructor; intro a;
      destruct (decA (f a) a);
      auto using gf_id_eq, gf_id_ne, fg_id_eq, fg_id_ne.
  Qed.

  Lemma exists_extended_inverse
    : exists g', fin_mod id g' /\ ext_inverse f g'.
  Proof.
    exists clamp_g.
    auto using inverses, fin_clamp_g.
  Qed.
End extend_inverse.

Arguments exists_extended_inverse {A f g} fH decA gfH fgH f_preserves_dom.

(** Now we try to prove Eder's Lemma 2.5, which says that every
    injective var substitution is a permutation.

    To do so, we follow his proof and lift the substitution to a map
    from its domain to itself. Most of the logic should be
    unsurprising. The work to extend the inverse from the domain [D]
    to [V] was basically done in [exists_extended_inverse] above.

    The one not-so-obvious thing is the [maybe_id] hypothesis. The
    problem is that [inj_endo_is_invertible] needs some element of [D]
    to map uninteresting elements to. Of course, if [s] is the
    identity substitution then [D] is empty and this won't work! *)

Section inj_subst.
  Variable V : Type.
  Variable s : var_subst V.
  Hypothesis injH :
    forall v w : V, proj1_sig s v = proj1_sig s w -> v = w.

  (** Firstly, we define some local variables to tidy up the names a
      little. We'll define [f] to be the underlying map of [s] and [D]
      to be the domain. *)

  Local Definition f : V -> V := proj1_sig s.
  Local Definition D : Type := mod_dom id f.

  (** The first part of the argument in the paper explains why a
      variable [v] in the domain must be mapped to another element of
      the domain. The point is that otherwise [f (f v) = f v] and
      injectivity would then imply that [f v = v], contradicting the
      fact that [v] was in the domain. *)

  Local Lemma f_maps_into_dom v : f v <> v -> f (f v) <> f v.
  Proof.
    intuition.
  Qed.

  Local Lemma maps_into_dom {v}
    : mod_elt id f v -> mod_elt id f (f v).
  Proof.
    fold f in injH; unfold mod_elt, id; apply f_maps_into_dom.
  Qed.

  (** Knowing this we can construct a natural map, where the top map
      is [D -> D] and the bottom map is [f : V -> V]. We'll name the
      vertical maps at either side as [proj] *)

  Local Definition proj : D -> V := md_elt.

  Local Lemma finite_proj : FiniteProj proj.
  Proof.
    unfold proj, D, f.
    destruct s as [ f' H ].
    unfold fin_endo, fin_mod in H.
    apply H.
  Qed.

  Local Definition top_map : D -> D :=
    fun d => let (v, eltH) := d in exist _ (f v) (maps_into_dom eltH).

  Local Lemma top_map_natural
    : is_nat_map proj proj (top_map, f).
  Proof.
    intro d; destruct d as [ v H ]; auto.
  Qed.

  Local Definition nmap : nat_map proj proj :=
    exist _ (top_map, f) top_map_natural.

  (** The injectivity lemma, [injH], then implies that [nmap] is an
      [inj_nat_map]. *)

  Local Lemma inj_nmap : inj_nat_map nmap.
  Proof.
    intros d0 d1; unfold nmap, proj, f; auto.
  Qed.

  (** With decidability on [V], we can strengthen [maps_into_dom]
      significantly. *)

  Hypothesis decV : forall x y : V, {x = y} + { ~ x = y }.

  Local Lemma idem_iff_ident {v}
    : f (f v) = f v <-> f v = v.
  Proof.
    fold f in injH; constructor; try congruence.
    destruct (decV (f v) v); auto.
  Qed.

  Local Definition lift_non_idem (v : V) (neH : f (f v) <> f v) : D.
  refine (exist _ v _).
  unfold id.
  intro eqH.
  rewrite <- idem_iff_ident in eqH.
  auto.
  Defined.

  Hypothesis maybe_id :
    (forall v, proj1_sig s v = v) \/ (exists v, proj1_sig s v <> v).

  Lemma inj_subst_is_perm : is_var_perm s.
  Proof.
    destruct maybe_id.
    - exists s. constructor; intro v; rewrite (H v), (H v); auto.
    - destruct H as [ v vH ].
      destruct (inj_endo_is_invertible nmap inj_nmap decV finite_proj
                                       (exist _ v vH)) as [ t tH ].
      unfold inv_bottom, nmap, nat_map_comp_h, compose in tH; simpl in tH.
      destruct (exists_extended_inverse
                  (proj2_sig s) decV (proj1 tH) (proj2 tH) f_maps_into_dom)
        as [ g gH ].
      destruct gH as [ fmH invH ].
      exists (exist _ g fmH); simpl.
      exact invH.
  Qed.
End inj_subst.

Arguments inj_subst_is_perm {V s} injH decV maybe_id.
