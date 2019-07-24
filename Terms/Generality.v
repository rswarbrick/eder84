Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.Terms.Term.

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
    apply (comp_subst_idl L).
  Qed.

  Lemma smg_trans {r s t : Subst} :
    smg r s -> smg s t -> smg r t.
  Proof.
    unfold smg.
    destruct 1 as [ rho_rs rsH ].
    destruct 1 as [ rho_st stH ].
    exists (comp_subst rho_st rho_rs).
    intro v.
    rewrite <- (comp_subst_assoc L).
    assert (eqH : forall v, rho_st v = rho_st v); auto.
    rewrite (comp_subst_ex L v eqH rsH).
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
