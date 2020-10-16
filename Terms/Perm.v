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
  Definition is_var_subst {V} (s : V -> V) := fin_endo s.
  Definition var_subst V := sigT (is_var_subst (V := V)).

  Variable L : lType.
  Notation V := (Term.V L).

  Definition var_subst_subst (s : var_subst V) : V -> Term L :=
    let (s', _) := s in compose (varTerm L) s'.

  Hypothesis decV : forall x y : V, {x = y} + { ~ x = y }.
  Hypothesis decF : forall x y : Lmodule.F L, {x = y} + { ~ x = y }.

  (** Since we're generally interested in finite substitutions, we
      would hope that a [var_subst] induces one, and it does. *)

  Lemma var_subst_is_fin_subst (s : var_subst V)
    : is_fin_subst L (var_subst_subst s).
  Proof.
    destruct s as [ s finH ].
    unfold var_subst_subst; simpl.
    eapply (compose_fin_mod decV decV (decTerm decV decF) _ _
                            finH
                            (fin_mod_i (varTerm L))).
    Unshelve.
    - destruct 1 as [ x eltH ]; contradiction eltH; auto.
    - intro d; destruct d as [ x eltH ]; contradiction eltH; auto.
  Qed.

  Definition var_subst_to_fin_subst : var_subst V -> fin_subst L :=
    fun s => existT _ (var_subst_subst s) (var_subst_is_fin_subst s).

  Lemma var_subst_subst_fin_subst s
    : fin_subst_subst L (var_subst_to_fin_subst s) =
      var_subst_subst s.
  Proof.
    auto.
  Qed.

  Lemma is_var_subst_compose (t s : V -> V)
    : is_var_subst t -> is_var_subst s -> is_var_subst (compose t s).
  Proof.
    apply (compose_fin_endo decV).
  Qed.

  Definition compose_var_subst (t s : var_subst V) : var_subst V :=
    let (ft, tH) := t in
    let (fs, sH) := s in
    existT _ (compose ft fs) (is_var_subst_compose tH sH).

End var_subst.

(** We're particularly interested in permutations, defined to be
    bijective variable substitutions. Since "bijective" is a little
    bit difficult to pin down in Coq, we'll ask that there is an
    "extensionally inverse" map. That is, the maps should compose to a
    map that equals the identity on every input. *)

Definition ext_inverse {A B : Type} (f : A -> B) (g : B -> A) :=
  (forall a, g (f a) = a) /\ (forall b, f (g b) = b).

Lemma ext_inverse_sym (A B : Type) (f : A -> B) (g : B -> A)
  : ext_inverse f g -> ext_inverse g f.
Proof.
  unfold ext_inverse; destruct 1; auto.
Qed.

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

(** Now we try to prove Eder's Lemma 2.6, which says that every
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
  Variable s : var_subst V.

  Definition var_subst_inj : Prop :=
    let (fs, _) := s in
    forall v w : V, fs v = fs w -> v = w.

  Hypothesis injH : var_subst_inj.

  Local Definition fs : V -> V := let (s', _) := s in s'.

  Local Lemma substH : is_var_subst fs.
  Proof.
    unfold fs; destruct s; auto.
  Qed.

  Local Lemma fs_inj : forall v w : V, fs v = fs w -> v = w.
  Proof.
    unfold var_subst_inj, fs in *; destruct s; auto.
  Qed.

  (** We'll define [D] to be the domain of [s] *)
  Local Definition D : Type := mod_dom id fs.

  (** The first part of the argument in the paper explains why a
      variable [v] in the domain must be mapped to another element of
      the domain. The point is that otherwise [f (f v) = f v] and
      injectivity would then imply that [f v = v], contradicting the
      fact that [v] was in the domain. *)

  Local Lemma f_maps_into_dom v : fs v <> v -> fs (fs v) <> fs v.
  Proof.
    unfold var_subst_inj, fs in *.
    destruct s as [ fs H ].
    intuition.
  Qed.

  Local Lemma maps_into_dom {v}
    : mod_elt id fs v -> mod_elt id fs (fs v).
  Proof.
    unfold mod_elt, id; apply f_maps_into_dom.
  Qed.

  (** Knowing this we can construct a natural map, where the top map
      is [D -> D] and the bottom map is [f : V -> V]. We'll name the
      vertical maps at either side as [proj] *)

  Local Definition proj : D -> V := md_elt.

  Local Definition finite_proj : FiniteProj proj := substH.

  Local Definition top_map : D -> D :=
    fun d => let (v, eltH) := d in exist _ (fs v) (maps_into_dom eltH).

  Local Lemma top_map_natural
    : is_nat_map proj proj (top_map, fs).
  Proof.
    intro d; destruct d as [ v H ]; auto.
  Qed.

  Local Definition nmap : nat_map proj proj :=
    exist _ (top_map, fs) top_map_natural.

  (** The injectivity lemma, [injH], then implies that [nmap] is an
      [inj_nat_map]. *)

  Local Lemma inj_nmap : inj_nat_map nmap.
  Proof.
    intros d0 d1; unfold nmap, proj; auto using fs_inj.
  Qed.

  (** With decidability on [V], we can strengthen [maps_into_dom]
      significantly. *)

  Hypothesis decV : forall x y : V, {x = y} + { ~ x = y }.

  Local Lemma idem_iff_ident {v}
    : fs (fs v) = fs v <-> fs v = v.
  Proof.
    split; try congruence.
    destruct (decV (fs v) v); auto using fs_inj.
  Qed.

  Local Definition lift_non_idem (v : V) (neH : fs (fs v) <> fs v) : D.
  refine (exist _ v _).
  unfold id.
  intro eqH.
  rewrite <- idem_iff_ident in eqH.
  auto.
  Defined.

  (** Because [s] is a [var_subst], in particular it is finite
      modification of the identity. But that means that we can use
      [decV] to find a value on which [s] isn't the identity. *)
  Definition dec_id : D + (forall v, fs v = v).
    destruct substH as [ ds fullH ].
    destruct ds as [ | d ds' ].
    - right; apply (empty_mod_elim decV id fs fullH).
    - left; exact d.
  Defined.

  (** If s happens to be the identity, this was all a bit pointless:
      we can't use [inj_endo_is_invertible] to produce the inverse
      map, because we have no element of [D]. But, of course, if [s]
      is the identity, it's pretty easy to find an inverse! *)
  Lemma ext_inverse_id
    : (forall v, fs v = v) -> ext_inverse fs fs.
  Proof.
    intro svH; split; intros; rewrite !svH; auto.
  Qed.

  (* If [s] isn't the identity, there's at least one [v] where [s v <>
     v], giving us an element of [D]. Give a name to the [nat_map]
     from whose base we can extract the inverse. *)
  Local Definition inv_nmap (d : D) : nat_map proj proj :=
    inj_endo_inv inj_nmap decV substH d (proj2_sig substH).

  Definition inj_subst_inv_fun : V -> V :=
    match dec_id with
    | inl d => clamp_g fs (nm_bot (inv_nmap d)) decV
    | inr idH => fs
    end.

  Lemma ext_inverse_inj_subst : ext_inverse fs inj_subst_inv_fun.
  Proof.
    unfold inj_subst_inv_fun; destruct dec_id as [ d | idH ].
    - apply ext_inverse_clamp_g.
      + apply (inj_endo_is_invertible inj_nmap _ _ d).
      + apply (inj_endo_is_invertible inj_nmap _ _ d).
      + intros v neH eqH. rewrite idem_iff_ident in eqH; auto.
    - apply (ext_inverse_id idH).
  Qed.

  Lemma is_var_subst_inj_subst_inv : is_var_subst inj_subst_inv_fun.
  Proof.
    unfold inj_subst_inv_fun; destruct dec_id as [ d | ]; auto.
    apply fin_clamp_g; auto.
    - unfold fs; destruct s; auto.
    - intro d'; apply (inj_endo_is_invertible inj_nmap _ _ d).
    - unfold fs; destruct s; auto.
  Qed.

  Definition inj_subst_inv : var_subst V :=
    existT _ inj_subst_inv_fun is_var_subst_inj_subst_inv.

End inj_subst.

Hint Rewrite var_subst_subst_fin_subst : var_subst.
