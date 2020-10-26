Require Import Top.Terms.Subst.
Require Import Top.Terms.Term.

(* First, we have to define the "more general than" relation on
   substitutions, abbreviated to smg.
 *)
Section smg.
  Variable L : lType.
  Notation V := (Term.V L).
  Notation F := (Term.F L).
  Hypothesis decV : forall v v' : V, {v = v'} + {v <> v'}.

  Definition is_left_factoring (rho sigma tau : fin_subst L) : Prop :=
    forall v, comp_subst L (fin_subst_subst L rho)
                         (fin_subst_subst L sigma) v =
              fin_subst_subst L tau v.

  Definition smg (sigma tau : fin_subst L) :=
    exists rho, is_left_factoring rho sigma tau.

  Lemma smg_refl {sigma} : smg sigma sigma.
  Proof.
    exists (existT _ (varTerm L) (fin_subst_varTerm L));
      intro v; apply comp_subst_idl.
  Qed.

  Lemma smg_trans
        (decF : forall f f' : F, {f = f'} + {f <> f'})
        {r s t} :
    smg r s -> smg s t -> smg r t.
  Proof.
    unfold smg.
    destruct 1 as [ rho_rs rsH ].
    destruct 1 as [ rho_st stH ].
    exists (fin_subst_comp L decV decF rho_st rho_rs).
    destruct rho_st as [ urho_st rstH ].
    destruct rho_rs as [ urho_rs rrsH ].
    revert rsH stH; unfold is_left_factoring; simpl; intros rsH stH.
    intro v; unfold fin_subst_comp; simpl.
    rewrite <- comp_subst_assoc.
    assert (eqH : forall v, urho_st v = urho_st v); auto.
    rewrite (comp_subst_ex L v eqH rsH).
    auto using stH.
  Qed.

  Definition is_subst_equiv sigma tau pr : Prop :=
    is_left_factoring (fst pr) sigma tau /\
    is_left_factoring (snd pr) tau sigma.

  Definition sequiv sigma tau := sig (is_subst_equiv sigma tau).

  Definition subst_ub (P : fin_subst L -> Prop) (s : fin_subst L) :=
    forall t : fin_subst L, P t -> exists r, is_left_factoring r t s.

  Definition subst_lb (P : fin_subst L -> Prop) (s : fin_subst L) :=
    forall t : fin_subst L, P t -> exists r, is_left_factoring r s t.

  Definition subst_sup (P : fin_subst L -> Prop) (s : fin_subst L) :=
    subst_ub P s /\ subst_lb (subst_ub P) s.

  Definition subst_inf (P : fin_subst L -> Prop) (s : fin_subst L) :=
    subst_lb P s /\ subst_ub (subst_lb P) s.

End smg.
