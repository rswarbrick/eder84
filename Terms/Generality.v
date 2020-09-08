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

*)
Section sequiv_means_perm.
  Variable L : lType.
  Variables sigma sigma' : Subst L.
  Variables rho rho' : Subst L.
  Hypothesis sigma'H : forall v, sigma' v = comp_subst rho sigma v.
  Hypothesis sigmaH : forall v, sigma v = comp_subst rho' sigma' v.

  Lemma sigma_is_rho2_sigma v
    : sigma v = comp_subst (comp_subst rho' rho) sigma v.
  Proof.
    rewrite <- comp_subst_assoc.
    unfold comp_subst at 1, compose; simpl.
    rewrite <- sigma'H, sigmaH; auto.
  Qed.

  Lemma rho2_fixes_im_sigma v
    : termset_fv v (subst_im sigma) ->
      comp_subst rho' rho v = varTerm L v.
  Proof.
    apply (@comp_subst_determines_fvs
             L sigma (comp_subst rho' rho) (varTerm L)); clear v.
    intro v; rewrite <- sigma_is_rho2_sigma, comp_subst_idl; auto.
  Qed.

  Lemma rho_im_sigma_has_height_0 v
    : termset_fv v (subst_im sigma) -> term_height (rho v) = 0.
  Proof.
    intro fvH.
    apply PeanoNat.Nat.le_0_r.
    apply (PeanoNat.Nat.le_trans _ _ _ (@term_height_comp_subst L rho' rho v)).
    rewrite (rho2_fixes_im_sigma v fvH); auto.
  Qed.

  Definition unpack_height_0_term (t : Term L)
    : term_height t = 0 -> Term.V L :=
    match t with
    | varTerm _ v => fun _ => v
    | funTerm f ts =>
      fun htH =>
        False_rect (Term.V L)
                   (PeanoNat.Nat.neq_succ_0
                      (vec_max_at (term_height (L:=L)) ts) htH)
    end.

  Lemma varTerm_unpack_height_0_term t H
    : varTerm L (unpack_height_0_term t H) = t.
  Proof.
    destruct t; auto.
    contradiction (PeanoNat.Nat.neq_succ_0 _ H).
  Qed.

  Definition rho_v_var_on_im_sigma
             (v : Term.V L) (fvH : termset_fv v (subst_im sigma)) : Term.V L :=
    unpack_height_0_term (rho v) (rho_im_sigma_has_height_0 v fvH).

  Lemma rvvois_correct
        v (fvH : termset_fv v (subst_im sigma))
    : varTerm L (rho_v_var_on_im_sigma v fvH) = rho v.
  Proof.
    apply varTerm_unpack_height_0_term.
  Qed.

  Lemma rvvois_is_fv_for_sigma'
        v (fvH : termset_fv v (subst_im sigma))
    : termset_fv (rho_v_var_on_im_sigma v fvH) (subst_im sigma').
  Proof.
    destruct fvH as [ t [ imH fvH' ] ].
    generalize (ex_intro (fun t0 => _ /\ term_fv v t0) _
                         (conj imH fvH')); intro fvH.
    destruct imH as [ w tH ].
    rewrite tH in fvH'; clear t tH.
    rewrite termset_fv_subst_im; exists w.
    rewrite sigma'H.
    apply (term_fv_in_subst_endo rho v
                                 (rho_v_var_on_im_sigma v fvH)
                                 (sigma w)
                                 fvH').
    rewrite <- (rvvois_correct v fvH).
    simpl; auto.
  Qed.

End sequiv_means_perm.
