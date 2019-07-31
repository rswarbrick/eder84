Require Import Top.Terms.Term.
Require Import Top.Terms.Generality.
Require Import Top.Terms.Perm.
Require Import Top.Terms.VecUtils.
Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinSet.

Require Vectors.VectorDef.
Require Import Logic.FinFun.
Require Import Program.Basics.
Require Import Lists.List.

(** * Initial Setup

    This theory develops Example 2.7 from Eder's paper, showing an
    example of a set of substitutions that is bounded above but has no
    supremum.

    To start us off, we need to choose our set of variables and set of
    functions. We pick three variables ([x, y, z]) and one function,
    [f]. Eder's paper is very slightly more general since he only
    requires that these variables exist. But dealing with the possibly
    infinite set of other variables seems like hard work, so we'll
    start with a minimal example.
 *)

Inductive V := Vx | Vy | Vz.
Inductive F := Ff.
Definition a (f : F) : nat := 2.

(* Our set of variables is finite (with cardinality 3) and
   decidable. *)

Lemma fullV : Full (Vx :: Vy :: Vz :: nil).
Proof.
  intro v; destruct v; auto with datatypes.
Qed.

Lemma decV : forall v v' : V, {v = v'} + {v <> v'}.
Proof.
  intros v v'; destruct v, v'; (auto || (right; discriminate)).
Qed.

Definition L := LType V F (Lmodule.Mixin _ _ a).

(** Constructing terms with vectors is a little cumbersome. [mkF] is a
    helper for applying the binary operation [Ff]. As you'd hope,
    [mkF] is injective. *)

Definition mkF (t0 t1 : Term L) : Term L :=
  funTerm L Ff (VectorDef.cons _ t0 1 (VectorDef.cons _ t1 O (VectorDef.nil _))).

Lemma mkF_inj {s0 t0 s1 t1} : mkF s0 s1 = mkF t0 t1 -> s0 = t0 /\ s1 = t1.
Proof.
  intro eqH; injection eqH; auto.
Qed.

(* Similarly, we have a constructor for making terms from
   variables. Of course, this is just [varTerm]. This is also
   injective. *)

Definition mkV : V -> Term L := varTerm L.

Lemma mkV_inj {v v'} : mkV v = mkV v' -> v = v'.
Proof.
  intro eqH; injection eqH; auto.
Qed.

(** We have rewrites for the action of subst_endo on mkF and mkV. It
    acts as a homomorphism as you'd hope. *)

Lemma subst_endo_mkF s t0 t1
  : subst_endo L s (mkF t0 t1) = mkF (subst_endo L s t0) (subst_endo L s t1).
Proof.
  exact eq_refl.
Qed.

Lemma subst_endo_mkV s v : subst_endo L s (mkV v) = s v.
Proof.
  exact eq_refl.
Qed.

(** * The special substitutions

    Eder considers two specially chosen substitutions: [sigma] and
    [tau]. *)

Definition sigma : Subst L := fun v => mkF (mkV Vx) (mkF (mkV Vy) (mkV Vz)).

Definition tau : Subst L := fun v => mkF (mkF (mkV Vx) (mkV Vy)) (mkV Vz).

(** In Eder's paper, he talks about the set containing [sigma] and
    [tau]. We define sets of substitutions implicitly using predicates
    [P : Subst -> Prop]. We want to show that this set is bounded
    above but has no supremum.

    We also define elimination and introduction rules for being an
    upper bound over [in_st]. (There are two elements in the set, so
    it's pretty easy to see what you have to do!) *)

Definition in_st (s : Subst L) : Prop := s = sigma \/ s = tau.

Lemma ub_st_elim {rho}
  : subst_ub L in_st rho ->
    smg L sigma rho /\ smg L tau rho.
Proof.
  unfold subst_ub, in_st, smg; auto.
Qed.

Lemma ub_st_intro {rho}
  : smg L sigma rho ->
    smg L tau rho ->
    subst_ub L in_st rho.
Proof.
  intros.
  unfold subst_ub, in_st; fold smg.
  intro t; destruct 1; congruence.
Qed.

(** * The [smg] relation

    To get started, we look at what it means for some [rho] to be more
    general than [sigma]. If [smg sigma rho] then there is a [sigma']
    such that [comp_subst sigma' sigma] and [rho] agree on all [v].

    In that case, we show that [rho] factors in a specific way.
 *)

Section sigma_decomp.
  Variable v : V.
  Variable sigma' rho : Subst L.
  Hypothesis decompH : comp_subst sigma' sigma v = rho v.

  Local Definition s12 := sigma' Vx.
  Local Definition s3 := sigma' Vy.
  Local Definition s4 := sigma' Vz.

  Local Lemma rho_in_s_1 : rho v = mkF s12 (mkF s3 s4).
  Proof.
    rewrite <- decompH; tauto.
  Qed.
End sigma_decomp.

(** The same argument goes for [tau], with a slightly different
    factorisation. *)

Section tau_decomp.
  Variable v : V.
  Variable tau' rho : Subst L.
  Hypothesis decompH : comp_subst tau' tau v = rho v.

  Local Definition s1 := tau' Vx.
  Local Definition s2 := tau' Vy.
  Local Definition s34 := tau' Vz.

  Local Lemma rho_in_s_2 : rho v = mkF (mkF s1 s2) s34.
  Proof.
    rewrite <- decompH; tauto.
  Qed.
End tau_decomp.

(** * Upper bounds for [in_st]

    In what follows, we often want to say "there exist four terms such
    that...". This is a bit unwieldy with four layers of existential
    quantifier, so we define a [Quad] type to hold them.

    We're going to need a variation on the quad type in a minute, so
    we include an map from the entries to terms. A quad containing
    terms is a [Quad id].

 *)

Inductive Quad {A : Type} (f : A -> Term L) :=
  mkQuad { q_t0 : A ; q_t1 : A ; q_t2 : A ; q_t3 : A }.

(** The quad composes to make the term [F (F a b) (F c d)], where [a,
    b, c, d] are the coordinates of the quad. *)

Definition quad_term {A : Type} {f : A -> Term L} (q : Quad f) : Term L :=
  match q with
    mkQuad _ _ a0 a1 a2 a3 => mkF (mkF (f a0) (f a1)) (mkF (f a2) (f a3))
  end.

(** If a substitution decomposes with [sigma] and [tau], we can
    actually write down its form explicitly. *)

Lemma subst_is_quad_term {v sigma' tau' rho}
  : comp_subst sigma' sigma v = rho v ->
    comp_subst tau' tau v = rho v ->
    rho v = mkF (mkF (s1 tau') (s2 tau')) (mkF (s3 sigma') (s4 sigma')).
Proof.
  intros sigmaH tauH.
  assert (sH : rho v = mkF (s12 sigma') (mkF (s3 sigma') (s4 sigma')));
    try (apply (rho_in_s_1 v sigma' rho sigmaH)).
  assert (tH : rho v = mkF (mkF (s1 tau') (s2 tau')) (s34 tau'));
    try (apply (rho_in_s_2 v tau' rho tauH)).
  destruct (mkF_inj (eq_stepl sH tH)) as [ eq12H eq34H ].
  congruence.
Qed.

(** Now we can pack [subst_is_quad_term] up into a nicer lemma, which
    shows that every upper bound for [in_st] is a [quad_term]. *)

Lemma form_if_ub {rho}
  : subst_ub L in_st rho ->
    exists q : Quad id, forall v, rho v = quad_term q.
Proof.
  intro ubH.
  destruct (ub_st_elim ubH) as [ smgsH smgtH ].
  destruct smgsH as [ sigma' sigmaH ].
  destruct smgtH as [ tau' tauH ].
  exists (mkQuad _ _ (s1 tau') (s2 tau') (s3 sigma') (s4 sigma')).
  intro v; unfold quad_term.
  apply subst_is_quad_term; auto.
Qed.

(** The converse is also true: every [quad_term] is an upper bound for
    [in_st]. To make the definition slick, we define [vfun], a helper
    method for defining functions on [V] by cases. *)

Definition vfun {A : Type} (ax ay az : A) (v : V) : A :=
  match v with Vx => ax | Vy => ay | Vz => az end.

Lemma ub_if_form {q : Quad id} rho
  : (forall v, rho v = quad_term q) -> Generality.subst_ub L in_st rho.
Proof.
  destruct q as [ t0 t1 t2 t3 ].
  intros formH; apply ub_st_intro;
    [ exists (vfun (mkF t0 t1) t2 t3) | exists (vfun t0 t1 (mkF t2 t3)) ];
    intro v; destruct v; auto.
Qed.

(** * Supremums for [in_st]

    We have shown that a substitution is an upper bound if and only if
    it maps every v to some [quad_term]. If the substitution is to be
    a supremum as well, the entries in the quad term must themselves
    be variables. This can be written as [Quad mkV].

    This holds because any substitution that maps to a quad of
    variables (for example, [cvquad Vx]) is of the correct form to be
    an upper bound.

    This is surprisingly difficult to prove. The problem is that we
    don't immediately get variables in our equations, where we can
    destruct the terms to see what's going on. To avoid a horrible
    mess, we use the [term_height] function. The point is that
    [term_height (quad_term q)] is zero iff [q] only contains
    variables.
 *)

Definition cvquad (v : V) : Quad mkV := mkQuad _ _ v v v v.
Definition cvquad_subst (v : V) : Subst L := fun v' => quad_term (cvquad v).

Lemma cvquad_is_ub (v : V)
  : Generality.subst_ub L in_st (cvquad_subst v).
Proof.
  set (q := mkQuad _ id (mkV v) (mkV v) (mkV v) (mkV v)).
  apply (@ub_if_form q).
  intro v'; auto.
Qed.

Lemma height_cvquad_subst_v {v v' : V}
  : term_height (cvquad_subst v v') = 2.
Proof.
  apply eq_refl.
Qed.

Lemma arity_value (f : Term.F L) : Term.a L f = 2.
Proof.
  apply eq_refl.
Qed.

Lemma height_cvquad_subst_endo {v : V} {t : Term L}
  : term_height (subst_endo L (cvquad_subst v) t) = 2 + term_height t.
Proof.
  revert t; apply Term_ind'; auto using height_cvquad_subst_v.
  intros f ts IH.
  unfold cvquad_subst, subst_endo;
    fold (subst_endo L); fold (cvquad_subst v).
  unfold term_height; fold (@term_height L).
  rewrite PeanoNat.Nat.add_succ_r; apply f_equal.
  rewrite (vec_max_at_map_equal (g := fun n => 2 + n)); auto; clear IH.
  revert ts; rewrite arity_value.
  intros; apply vec_max_at_map_incr.
  intros; repeat (apply le_n_S); assumption.
Qed.

Lemma height_mkF {t t'}
  : term_height (mkF t t') = S (max (term_height t) (term_height t')).
Proof.
  unfold mkF.
  unfold term_height at 1; fold (@term_height L).
  apply f_equal.
  rewrite (vec_max_at_cons (n := 1)).
  rewrite (vec_max_at_cons_nil).
  exact eq_refl.
Qed.

Lemma max_0_elim {a b}
  : max a b = 0 -> a = 0 /\ b = 0.
Proof.
  destruct a, b; auto.
  intro sH; rewrite <- PeanoNat.Nat.succ_max_distr in sH.
  contradiction (PeanoNat.Nat.neq_succ_0 _ sH).
Qed.

Lemma height_0_term {t}
  : term_height t = 0 -> exists v, t = mkV v.
Proof.
  destruct t.
  - exists v; auto.
  - simpl; intro eqH; contradiction (PeanoNat.Nat.neq_succ_0 _ eqH).
Qed.

Lemma height_2_quad_term {tq : Quad id}
  : term_height (quad_term tq) = 2 ->
    exists vq : Quad mkV, quad_term tq = quad_term vq.
Proof.
  intro htH.
  destruct tq as [ t0 t1 t2 t3 ]; unfold quad_term, id in htH.
  assert ((max (max (term_height t0) (term_height t1))
               (max (term_height t2) (term_height t3))) = 0) as maxH;
    [ apply eq_add_S, eq_add_S; revert htH; rewrite !height_mkF; auto | ].
  destruct (max_0_elim maxH) as [ max01H max23H ]; clear htH maxH.
  destruct (max_0_elim max01H) as [ max0H max1H ]; clear max01H.
  destruct (max_0_elim max23H) as [ max2H max3H ]; clear max23H.
  destruct (height_0_term max0H) as [ v0 H0 ]; clear max0H.
  destruct (height_0_term max1H) as [ v1 H1 ]; clear max1H.
  destruct (height_0_term max2H) as [ v2 H2 ]; clear max2H.
  destruct (height_0_term max3H) as [ v3 H3 ]; clear max3H.
  exists (mkQuad _ mkV v0 v1 v2 v3).
  unfold quad_term, id; rewrite H0, H1, H2, H3.
  exact eq_refl.
Qed.

Lemma height_quad_term {A} {f : A -> Term L} {q : Quad f}
  : 2 <= term_height (quad_term q).
Proof.
  destruct q; unfold quad_term.
  rewrite !height_mkF; simpl.
  auto using le_n_S, le_0_n.
Qed.

Lemma comp_subst_quad_to_var {s0 s1 : Subst L} {v v' : V} {tq : Quad id}
  : s0 v' = quad_term tq ->
    comp_subst s1 s0 v' = cvquad_subst v v' ->
    exists vq : Quad mkV, s0 v' = quad_term vq.
Proof.
  intros tqH eqH.
  rewrite tqH; apply height_2_quad_term.
  apply PeanoNat.Nat.le_antisymm; [ | exact height_quad_term ].
  rewrite <- tqH.
  assert (term_height (comp_subst s1 s0 v') = 2) as heightH;
    [ exact (f_equal term_height eqH) | ].
  rewrite <- heightH; exact term_height_comp_subst.
Qed.

Lemma form_if_sup {rho}
  : Generality.subst_sup L in_st rho ->
    exists q : Quad mkV, forall v, rho v = quad_term q.
Proof.
  destruct 1 as [ ubH lbH ].
  destruct (form_if_ub ubH) as [ tq tqH ]; clear ubH.
  destruct (lbH _ (cvquad_is_ub Vx)) as [ rho' rho'H ]; clear lbH.
  destruct (comp_subst_quad_to_var (tqH Vx) (rho'H Vx)) as [ q qH ].
  exists q; congruence.
Qed.
