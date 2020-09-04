Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.Terms.Term.
Require Import Top.Terms.VecUtils.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.FinMod.

(* First, we have to define the "more general than" relation on
   substitutions, abbreviated to smg.
 *)
Section smg.
  Variable L : lType.

  Definition Subst := (Lmodule.V L -> Term L).

  Definition smg (sigma tau : Subst) : Prop :=
    exists rho, forall v, comp_subst rho sigma v = tau v.

  Lemma smg_refl {sigma : Subst} : smg sigma sigma.
  Proof.
    unfold smg; exists (varTerm L); intro v.
    apply comp_subst_idl.
  Qed.

  Lemma smg_trans {r s t : Subst} :
    smg r s -> smg s t -> smg r t.
  Proof.
    unfold smg.
    destruct 1 as [ rho_rs rsH ].
    destruct 1 as [ rho_st stH ].
    exists (comp_subst rho_st rho_rs).
    intro v.
    rewrite <- comp_subst_assoc.
    assert (eqH : forall v, rho_st v = rho_st v); auto.
    rewrite (comp_subst_ex v eqH rsH).
    rewrite stH.
    exact eq_refl.
  Qed.

  Definition sequiv (sigma tau : Subst) : Prop :=
    smg sigma tau /\ smg tau sigma.

  Definition subst_ub (P : Subst -> Prop) (s : Subst) :=
    forall t : Subst, P t -> smg t s.

  Definition subst_lb (P : Subst -> Prop) (s : Subst) :=
    forall t : Subst, P t -> smg s t.

  Definition subst_sup (P : Subst -> Prop) (s : Subst) :=
    subst_ub P s /\ subst_lb (subst_ub P) s.

  Definition subst_inf (P : Subst -> Prop) (s : Subst) :=
    subst_lb P s /\ subst_ub (subst_lb P) s.

End smg.

(** * Elements that are [sequiv] are related by a permutation

    This section is devoted to proving Lemma 2.10 from Eder's paper. This says
    that if two substitutions are equivalent under the [smg] relation then
    there are permutations that relabel them into each other.

    The first big statement is that if you have a finite substitution, sigma,
    then there are only finitely many variables that are not free variables in
    the image of sigma. Why? Well, sigma leaves all but finitely many variables
    untouched and these untouched variables will still be free in the image of
    sigma.

    We start by setting up a sigma type for the bound variables. We want to
    show that [proj1_sig] on that sigma type is a finite projection.

    TODO: Currently working on this in the BoundInImage module.

*)
