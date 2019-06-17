Require Import Top.Terms.Term.
Require Import Top.Terms.Generality.

Require Coq.Vectors.VectorDef.
Require Import Program.Basics.

(** This theory develops Example 2.7 from Eder's paper, showing an
    example of a set of substitutions that is bounded above but has no
    supremum. *)

Inductive V := Vx | Vy | Vz.
Inductive F := Ff.
Definition a (f : F) : nat := 2.

Definition mkF (t0 t1 : Term V F a) : Term V F a :=
  funTerm V F a Ff
          (VectorDef.cons _ t0 1
                          (VectorDef.cons _ t1 O (VectorDef.nil _))).

Definition mkV (v : V) : Term V F a := varTerm V F a v.

Lemma subst_endo_mkF s t0 t1
  : subst_endo V F a s (mkF t0 t1) =
    mkF (subst_endo V F a s t0) (subst_endo V F a s t1).
Proof.
  tauto.
Qed.

Lemma subst_endo_mkV s v : subst_endo V F a s (mkV v) = s v.
Proof.
  tauto.
Qed.

Lemma mkF_inj {t0 t1 t0' t1'}
  : mkF t0 t1 = mkF t0' t1' -> t0 = t0' /\ t1 = t1'.
Proof.
  unfold mkF; intro eqH.
  injection eqH.
  auto.
Qed.

Definition sigma : Subst V F a :=
  fun v => mkF (mkV Vx) (mkF (mkV Vy) (mkV Vz)).

Definition tau : Subst V F a :=
  fun v => mkF (mkF (mkV Vx) (mkV Vy)) (mkV Vz).

(** In Eder's paper, he talks about the set containing [sigma] and
    [tau]. We define sets of substitutions implicitly using predicates
    [P : Subst -> Prop]. *)

Definition in_st (s : Subst V F a) : Prop := s = sigma \/ s = tau.

(** We want to show that this set is bounded above but has no
    supremum. To get started, we look at what it means for some [rho]
    to be more general than [sigma].

    If [smg sigma rho] then there is a [sigma'] such that [comp_subst
    sigma' sigma] and [rho] agree on all [v].

 *)
Section sigma_decomp.
  Variable sigma' rho : Subst V F a.
  Hypothesis decompH : forall v, comp_subst sigma' sigma v = rho v.

  Local Definition s12 := sigma' Vx.
  Local Definition s3 := sigma' Vy.
  Local Definition s4 := sigma' Vz.

  Local Lemma rho_in_s_1 v : rho v = mkF s12 (mkF s3 s4).
  Proof.
    rewrite <- (decompH v); tauto.
  Qed.
End sigma_decomp.

Section tau_decomp.
  Variable tau' rho : Subst V F a.
  Hypothesis decompH : forall v, comp_subst tau' tau v = rho v.

  Local Definition s1 := tau' Vx.
  Local Definition s2 := tau' Vy.
  Local Definition s34 := tau' Vz.

  Local Lemma rho_in_s_2 v : rho v = mkF (mkF s1 s2) s34.
  Proof.
    rewrite <- (decompH v); tauto.
  Qed.
End tau_decomp.

Lemma form_if_ub {rho}
  : smg V F a sigma rho -> smg V F a tau rho ->
    exists t0 t1 t2 t3,
      forall v, rho v = mkF (mkF t0 t1) (mkF t2 t3).
Proof.
  destruct 1 as [ sigma' sigmaH ].
  destruct 1 as [ tau' tauH ].
  exists (s1 tau'), (s2 tau'), (s3 sigma'), (s4 sigma').
  intro v.
  assert (sH : rho v = mkF (s12 sigma') (mkF (s3 sigma') (s4 sigma')));
    try (apply (rho_in_s_1 sigma' rho sigmaH v)).
  assert (tH : rho v = mkF (mkF (s1 tau') (s2 tau')) (s34 tau'));
    try (apply (rho_in_s_2 tau' rho tauH v)).
  destruct (mkF_inj (eq_stepl sH tH)) as [ eq12H eq34H ].
  congruence.
Qed.

Lemma ub_if_form {rho t0 t1 t2 t3}
  : (forall v, rho v = mkF (mkF t0 t1) (mkF t2 t3)) ->
    smg V F a sigma rho /\ smg V F a tau rho.
Proof.
  intro formH.
  constructor.
  - exists (fun v => match v with
                     | Vx => mkF t0 t1
                     | Vy => t2
                     | Vz => t3
                     end).
    intro v; destruct v;
      unfold comp_subst, compose; simpl;
        fold (mkF t2 t3); fold (mkF (mkF t0 t1) (mkF t2 t3)); auto.
  - exists (fun v => match v with
                     | Vx => t0
                     | Vy => t1
                     | Vz => mkF t2 t3
                     end).
    intro v; destruct v;
      unfold comp_subst, compose; simpl;
        fold (mkF t0 t1); fold (mkF (mkF t0 t1) (mkF t2 t3)); auto.
Qed.

Lemma ub_iff {rho}
  : subst_ub V F a in_st rho <->
    exists t0 t1 t2 t3, forall v, rho v = mkF (mkF t0 t1) (mkF t2 t3).
Proof.
  unfold subst_ub.
  constructor.
  - unfold subst_ub; intro ubH.
    apply form_if_ub; apply ubH; unfold in_st; auto.
  - destruct 1 as [ t0 H ]; destruct H as [ t1 H ];
      destruct H as [ t2 H ]; destruct H as [ t3 H ].
    pose (ubH := ub_if_form H).
    intro t; destruct 1 as [ -> | -> ]; tauto.
Qed.
