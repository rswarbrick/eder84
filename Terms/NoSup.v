Require Top.Terms.Term.
Require Top.Terms.Generality.
Require Import Top.Terms.Perm.
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

(** Rather than suffixing everything with [V F a], we import
    [Term.Term] qualified and then define local things with the right
    names, specialised to our setup. *)

Definition L := Term.LType V F (Term.Lmodule.Mixin _ _ a).

Definition T := Term.Term L.
Definition funTerm := Term.funTerm L.
Definition varTerm := Term.varTerm L.
Definition subst_endo := Term.subst_endo L.
Definition Subst := Generality.Subst L.
Definition smg := Generality.smg L.

(** Constructing terms with vectors is a little cumbersome. [mkF] is a
    helper for applying the binary operation [Ff]. As you'd hope,
    [mkF] is injective. *)

Definition mkF (t0 t1 : T) : T :=
  funTerm Ff (VectorDef.cons _ t0 1 (VectorDef.cons _ t1 O (VectorDef.nil _))).

Lemma mkF_inj {s0 t0 s1 t1} : mkF s0 s1 = mkF t0 t1 -> s0 = t0 /\ s1 = t1.
Proof.
  intro eqH; injection eqH; auto.
Qed.

(* Similarly, we have a constructor for making terms from
   variables. Of course, this is just [varTerm]. This is also
   injective. *)

Definition mkV : V -> T := varTerm.

Lemma mkV_inj {v v'} : mkV v = mkV v' -> v = v'.
Proof.
  intro eqH; injection eqH; auto.
Qed.

(** We have rewrites for the action of subst_endo on mkF and mkV. It
    acts as a homomorphism as you'd hope. *)

Lemma subst_endo_mkF s t0 t1
  : subst_endo s (mkF t0 t1) = mkF (subst_endo s t0) (subst_endo s t1).
Proof.
  exact eq_refl.
Qed.

Lemma subst_endo_mkV s v : subst_endo s (mkV v) = s v.
Proof.
  exact eq_refl.
Qed.

(** * The special substitutions

    Eder considers two specially chosen substitutions: [sigma] and
    [tau]. *)

Definition sigma : Subst := fun v => mkF (mkV Vx) (mkF (mkV Vy) (mkV Vz)).

Definition tau : Subst := fun v => mkF (mkF (mkV Vx) (mkV Vy)) (mkV Vz).

(** In Eder's paper, he talks about the set containing [sigma] and
    [tau]. We define sets of substitutions implicitly using predicates
    [P : Subst -> Prop]. We want to show that this set is bounded
    above but has no supremum.

    We also define elimination and introduction rules for being an
    upper bound over [in_st]. (There are two elements in the set, so
    it's pretty easy to see what you have to do!) *)

Definition in_st (s : Subst) : Prop := s = sigma \/ s = tau.

Lemma ub_st_elim {rho}
  : Generality.subst_ub L in_st rho ->
    smg sigma rho /\ smg tau rho.
Proof.
  unfold Generality.subst_ub, in_st, smg; auto.
Qed.

Lemma ub_st_intro {rho}
  : smg sigma rho ->
    smg tau rho ->
    Generality.subst_ub L in_st rho.
Proof.
  intros.
  unfold Generality.subst_ub, in_st; fold smg.
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
  Variable sigma' rho : Subst.
  Hypothesis decompH : Term.comp_subst sigma' sigma v = rho v.

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
  Variable tau' rho : Subst.
  Hypothesis decompH : Term.comp_subst tau' tau v = rho v.

  Local Definition s1 := tau' Vx.
  Local Definition s2 := tau' Vy.
  Local Definition s34 := tau' Vz.

  Local Lemma rho_in_s_2 : rho v = mkF (mkF s1 s2) s34.
  Proof.
    rewrite <- decompH; tauto.
  Qed.
End tau_decomp.

(** * Quads

    In what follows, we often want to say "there exist four terms such
    that...". This is a bit unwieldy with four layers of existential
    quantifier, so we define a [Quad] type to hold them.

 *)

Inductive Quad := mkQuad { q_t0 : T ; q_t1 : T ; q_t2 : T ; q_t3 : T }.

(** The quad composes to make the term [F (F a b) (F c d)], where [a,
    b, c, d] are the coordinates of the quad. *)

Definition quad_term (q : Quad) : T :=
  match q with mkQuad t0 t1 t2 t3 => mkF (mkF t0 t1) (mkF t2 t3) end.

(** This is just a helper method for defining functions on [V] by
    cases. *)

Definition vfun {A : Type} (ax ay az : A) (v : V) : A :=
  match v with Vx => ax | Vy => ay | Vz => az end.

(** If a substitution decomposes with [sigma] and [tau], we can
    actually write down its form explicitly. *)

Lemma subst_is_quad_term {v sigma' tau' rho}
  : Term.comp_subst sigma' sigma v = rho v ->
    Term.comp_subst tau' tau v = rho v ->
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

(** Now we pack [subst_is_quad_term] up into a nicer lemma *)

Lemma form_if_ub {rho}
  : Generality.subst_ub L in_st rho ->
    exists q : Quad, forall v, rho v = quad_term q.
Proof.
  intro ubH.
  destruct (ub_st_elim ubH) as [ smgsH smgtH ].
  destruct smgsH as [ sigma' sigmaH ].
  destruct smgtH as [ tau' tauH ].
  exists (mkQuad (s1 tau') (s2 tau') (s3 sigma') (s4 sigma')).
  intro v; unfold quad_term.
  apply subst_is_quad_term; auto.
Qed.

(*

Lemma ub_if_form {q} rho : (forall v, rho v = quad_term q) -> subst_ub
  V F a in_st rho.  Proof.  intro formH.  destruct q as [ t0 t1 t2 t3
  ].  intro t; destruct 1 as [ -> | -> ].  - exists (vfun (mkF t0 t1)
  t2 t3); intro v; destruct v; unfold vfun, comp_subst, compose;
  simpl; fold (mkF t2 t3); fold (mkF (mkF t0 t1) (mkF t2 t3)); auto.
  - exists (vfun t0 t1 (mkF t2 t3)); intro v; destruct v; unfold vfun,
  comp_subst, compose; simpl; fold (mkF t0 t1); fold (mkF (mkF t0 t1)
  (mkF t2 t3)); auto.  Qed.

(** We want to show that if [rho] is a supremum for [in_st] then in
    any quad form for [rho], each [t0] through [t3] is of the form
    [mkV v0] through [mkV v3].  *) Inductive VQuad := mkVQuad { v_t0 :
    V ; v_t1 : V ; v_t2 : V ; v_t3 : V }.

Definition vquad_to_quad (vq : VQuad) : Quad := mkQuad (mkV (v_t0 vq))
  (mkV (v_t1 vq)) (mkV (v_t2 vq)) (mkV (v_t3 vq)).

Lemma factor_var_map {v q sigma rho vq} : (rho v = quad_term q) ->
  (comp_subst sigma rho v = quad_term (vquad_to_quad vq)) -> exists
  vq', rho v = quad_term (vquad_to_quad vq').  Proof.  intros rhoH H.
  unfold comp_subst, compose in H.  unfold subst_endo at 2 in H.
  destruct q as [ t0 t1 t2 t3 ].  rewrite rhoH in *; clear rhoH.
  simpl in H; simpl.  injection H; clear H; intros H3 H2 H1 H0.
  destruct vq as [ v0 v1 v2 v3 ]; simpl in *.  (* Each Hi implies ti
  is a variable *) repeat match goal with | [ H : subst_endo V F a
  sigma ?t = mkV ?v |- _ ] => let H' := fresh in rename H into H';
  assert (exists w, t = varTerm V F a w) as H; try solve [(destruct t
  as [ w | ]; (exists w; auto) || inversion H')]; clear H' end.
  destruct H0 as [ w0 H0 ].  destruct H1 as [ w1 H1 ].  destruct H2 as
  [ w2 H2 ].  destruct H3 as [ w3 H3 ].  exists (mkVQuad w0 w1 w2 w3);
  simpl.  rewrite H0, H1, H2, H3.  tauto.  Qed.

(*


Lemma quad_rho_is_vquad {rho q} : subst_sup V F a in_st rho -> (forall
  v, rho v = quad_term q) -> exists vq, q = vquad_to_quad vq.  Proof.
  destruct 1 as [ ubH lbH ].  intros qH.  (** The proof starts by
  picking another upper bound whose terms are simple variables. *) set
  (x := mkV Vx).  set (qx := vquad_to_quad (mkVQuad Vx Vx Vx Vx)).
  set (f := (fun v : V => mkF (mkF x x) (mkF x x))).  specialize (lbH
  f).  assert (ubfH : subst_ub V F a in_st f).  try (apply
  (@ub_if_form qx f); intro v; destruct v; auto).  specialize (lbH
  ubfH) as smgH; clear ubfH.  (** The smgH hypothesis says that we can
  factor [f] through [rho] *) destruct smgH as [ sigma sigmaH ].



  unfold smg in smgH.



Lemma UNUSED_subst_to_var_is_var_subst {rho} : (forall v, exists v',
  rho v = mkV v') -> (exists rho', forall v, rho v = var_subst_subst a
  rho' v).  Proof.  intro H.  destruct (H Vx) as [ vx Hx ].  destruct
  (H Vy) as [ vy Hy ].  destruct (H Vz) as [ vz Hz ].  set (f := (fun
  v => match v with | Vx => vx | Vy => vy | Vz => vz end)).  exists
  (exist _ f (fin_domain_implies_fin_mod id f decV fullV)).  intro
  v. unfold var_subst_subst; simpl; unfold f, compose.  destruct v;
  tauto.  Qed.

(* This is nonsense. We must show that

     rho v = F (F a b) (F c d)

  where a, b, c, d are disjoint variables. *)

Lemma sup_is_var_subst {rho} : subst_sup V F a in_st rho -> exists
  rho' : var_subst V, forall v, rho v = var_subst_subst a rho' v.
  Proof.  destruct 1 as [ ubH lbH ].  apply subst_to_var_is_var_subst.
  (* Unpack form_if_ub to get the general shape of rho *) destruct
  (form_if_ub ubH) as [ t0 ubH' ]; clear ubH.  destruct ubH' as [ t1
  ubH ]; destruct ubH as [ t2 ubH ]; destruct ubH as [ t3 ubH ].  (*
  Now we need to use the fact that rho is a minimal upper bound. *)
  intro v.  specialize (ubH v).

  specialize (ubH Vx).  set (x := mkV Vx).  set (f := (fun v : V =>
  mkF (mkF x x) (mkF x x))).  specialize (lbH f).  assert (ubfH :
  subst_ub V F a in_st f); try (apply (@ub_if_form x x x x f); intro
  v; destruct v; auto).  specialize (lbH ubfH).  destruct lbH as [ f'
  f'H ].  specialize (f'H Vx).  unfold comp_subst, compose, f in f'H.
  simpl in f'H.  rewrite ubH in f'H; unfold x in f'H.  injection f'H.

    Check ub_if_form f.  unfold subst_lb in lbH.
      
*)
*)
