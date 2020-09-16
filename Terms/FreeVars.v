Require Import Lists.List.
Require Import Bool.

Require Import Top.FinSet.FinMod.

Require Import Top.Terms.Term.
Require Import Top.Terms.VecUtils.

Set Implicit Arguments.

  (** * Free variables

      A term may have free variables. This is a set, so we encode it
      as a predicate: [term_fv t v] means "v is a free variable in
      t". This is extended by union in the obvious way to sets of
      terms and sets of sets of terms.

      This matches the notation in 2.8 in Eder's paper.

   *)
Section fv.
  Variable L : lType.

  Fixpoint term_fv (v : Term.V L) (t : Term L) : Prop :=
    match t with
    | varTerm _ v' => v = v'
    | funTerm f ts => vec_some (term_fv v) ts
    end.

  Definition termset_fv (v : Term.V L) (M : Term L -> Prop) : Prop :=
    exists t : Term L, M t /\ term_fv v t.

  Definition termsetset_fv (v : Term.V L) (P : (Term L -> Prop) -> Prop) : Prop :=
    exists M : Term L -> Prop, P M /\ termset_fv v M.

  (**

    If we have decidable equality on terms, there's a decision procedure to
    check whether a variable is free in a given term. Sadly, we can't use
    [check_vec_someb] for checking through the vector of a [funTerm] (because
    we'd be passing [check_term_fv decV v] as the function to map, which isn't
    a structural recursion).

   *)
  Fixpoint check_term_fv
           (decV : forall v w : Term.V L, {v = w} + {v <> w})
           (v : Term.V L) (t : Term L) : bool :=
    match t with
    | varTerm _ w => if decV v w then true else false
    | funTerm f ts =>
      let fix ff n ts' :=
          match ts' with
          | vnil _ => false
          | vcons _ t _ ts'' => orb (check_term_fv decV v t) (ff _ ts'')
          end
      in
      ff _ ts
    end.

  (**

    We couldn't use [check_vec_someb] in [check_term_fv] because of the
    termination checker, but we can use it now. Check that we wrote down the
    formula we intended to.

   *)
  Lemma check_term_fv_funTerm decV v f ts
    : check_term_fv decV v (funTerm f ts) =
      check_vec_someb (check_term_fv decV v) ts.
  Proof.
    simpl.
    revert ts; generalize (Term.a L f).
    induction ts as [ | t n ts IH ]; auto.
    rewrite check_vec_someb_cons.
    apply orb_intro_left; auto.
  Qed.

  Lemma check_term_fv_correct
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (v : Term.V L) (t : Term L)
    : term_fv v t <-> is_true (check_term_fv decV v t).
  Proof.
    apply (Term_ind' (fun t' => _ t' <-> is_true (_ t'))).
    - intro w.
      simpl; destruct (decV v w); unfold is_true; try tauto.
      split.
      + contradiction.
      + intro ftH; contradiction (Bool.diff_false_true ftH).
    - intros f ts allH.
      rewrite check_term_fv_funTerm.
      unfold term_fv; fold term_fv.
      revert ts allH; generalize (Term.a L f); clear f t.
      intros n ts.
      induction ts as [ | a n ts IH ].
      + simpl; rewrite check_vec_someb_nil; unfold is_true.
        split; auto using diff_false_true.
      + simpl.
        rewrite check_vec_someb_cons.
        intros [ termH restH ].
        specialize (IH restH); clear restH.
        split.
        * destruct 1 as [ H0 | H1 ].
          -- rewrite termH in H0; rewrite H0; auto.
          -- rewrite IH in H1; rewrite H1.
             auto using orb_true_r.
        * unfold is_true.
          intro H.
          destruct (orb_prop _ _ H) as [ H0 | H1 ].
          -- rewrite <- termH in H0; auto.
          -- rewrite <- IH in H1; auto.
  Qed.

  Definition dec_term_fv
             (decV : forall v w : Term.V L, {v = w} + {v <> w})
             (v : Term.V L) (t : Term L)
    : {term_fv v t} + {~ term_fv v t} :=
    dec_proc_to_sumbool (check_term_fv_correct decV v) t.

  (**

    Eder makes some remarks in part 2.9. The first is "the
    intersection of V and M is a subset of V(M)". This takes a bit of
    decoding if V isn't considered a subset of the set of terms. The
    point is that if you have a set of terms, M, then each of the
    variables in that set (the intersection between V and M) appear as
    a free variable of the set.

    We can formalise this, but need some injections into the set of
    terms and the statement ends up looking a little different.

  *)

  Lemma var_in_M_is_free_var (v : Term.V L) (M : Term L -> Prop)
    : M (varTerm L v) -> termset_fv v M.
  Proof.
    exists (varTerm L v); simpl; auto.
  Qed.

  (**

    The second remark of 2.9 is "If sigma is a substitution, then V is
    equal to D(sigma) union V(sigma V) and is a subset of D(sigma)
    union sigma V."

    To make sense of this in our development, recall that D(sigma) is
    the domain of sigma: the set of variables that aren't mapped to
    themselves. The predicate for this is [mod_elt varTerm sigma].

    Then the first part of the statement says that every variable is
    either mapped non-trivially by sigma or is a free variable of the
    set of terms that you get by applying sigma to each variable. The
    point is that if sigma fixes a variable, v, then v will be an
    element of sigma V and thus it will (trivially) be a free variable
    of that set of terms.

    Note that this needs the law of excluded middle (a variable is in
    the domain or isn't). If equality is decidable on V, we can use
    [dec_mod_elt_varTerm] for this. The proof is a little ugly because
    you end up with a double negation (if [mod_elt] is false then
    you're saying that something is "not not equal"). If we need this
    logic lots, we could factor out a negated version of
    [dec_mod_elt_varTerm].

    The second part of the statement is essentially the same point,
    except that we're considering V as a set of terms and noticing
    that every term that's a variable either appears in the domain of
    sigma or in its image. We don't prove that separately: it's
    basically the same statement, and is ugly to state because of all
    the bouncing between [V] and [Term]. *)

  Lemma mod_elt_or_free_in_image_as_var
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (sigma : Term.V L -> Term L)
        (v : Term.V L)
    : mod_elt (varTerm L) sigma v \/ termset_fv v (subst_im sigma).
  Proof.
    destruct (dec_mod_elt_varTerm decV sigma v) as [ | not_mod_eltH ]; auto.
    right; exists (sigma v); split.
    - exists v; auto.
    - revert not_mod_eltH.
      unfold mod_elt.
      case_eq (sigma v); try discriminate.
      intros w sigmavH vtH.
      destruct (decV v w) as [ | neH ]; auto.
      assert (varTerm _ w <> varTerm _ v) as vtneH.
      + injection; exact (not_eq_sym neH).
      + contradiction vtneH.
  Qed.

  (**

    The third remark in 2.9 supposes that you have a substitution,
    tau. Then two substitutions, sigma and sigma' have the same
    compositions with tau (i.e. sigma tau = sigma' tau) if sigma and
    sigma' agree on all free variables of tau V.

    This is obvious of [tau v] is itself a variable. Less obvious if
    it's some general term: in that case, you actually have to do
    induction over the resulting term. The proof ends up being
    repeated applications of generalize to simplify the types enough
    to allow us to induct over the term first and then a function
    term's children.

   *)

  Lemma comp_subst_determined_by_fvs (tau sigma sigma' : Term.V L -> Term L)
    : (forall v, termset_fv v (subst_im tau) -> sigma v = sigma' v) ->
      forall v, comp_subst sigma tau v = comp_subst sigma' tau v.
  Proof.
    intros eqH v.
    unfold comp_subst.
    assert (forall w, term_fv w (tau v) -> sigma w = sigma' w) as H.
    - intros w fvH.
      apply eqH.
      unfold termset_fv.
      exists (tau v).
      split; auto.
      exists v; auto.
    - clear eqH; revert H; generalize (tau v); clear tau v.
      apply (Term_ind' (fun t => _ -> _ t = _ t)).
      + intros v H; apply H; unfold term_fv; auto.
      + intros f ts allH H; simpl.
        apply f_equal, vec_map_ext.
        apply (vec_all_modus_ponens ts allH); clear allH.
        revert H; simpl.
        generalize ts; clear ts; generalize (Term.a L f); clear f.
        intros n ts.
        induction ts; simpl; auto.
  Qed.

  Definition term_children (t : Term L) : list (Term L) :=
    match t with
    | varTerm _ v => nil
    | funTerm f ts => VectorDef.to_list ts
    end.

  Lemma funTerm_inj f (v v' : Term.vec (Term L) (Term.a L f))
    : funTerm f v = funTerm f v' -> v = v'.
  Proof.
    intro eqH.
    apply vec_to_list_inj.
    exact (f_equal term_children eqH).
  Qed.

  Lemma subst_endo_determines_fvs
        (sigma sigma' : Term.V L -> Term L) v t
    : term_fv v t ->
      subst_endo sigma t = subst_endo sigma' t ->
      sigma v = sigma' v.
  Proof.
    revert t.
    apply (Term_ind' (fun t => _ -> _ -> sigma v = sigma' v)).
    - intro v''; simpl; intro v''H; rewrite <- v''H; auto.
    - simpl.
      intros f ts allH someH eqH.
      assert (VectorDef.map (subst_endo sigma) ts =
              VectorDef.map (subst_endo sigma') ts) as eqH';
        [ apply (funTerm_inj eqH) | ]; clear eqH.
      assert (VectorDef.to_list (VectorDef.map (subst_endo sigma) ts) =
              VectorDef.to_list (VectorDef.map (subst_endo sigma') ts)) as eqH;
        [ apply f_equal; auto | ]; clear eqH'.
      rewrite !vec_map_to_list in eqH.
      destruct (vec_some_to_list _ _ someH) as [ t [ inH fvH ] ]; clear someH.
      apply (vec_all_to_list _ _ allH t inH fvH); clear allH.
      revert eqH inH;
        generalize (VectorDef.to_list ts); clear f ts; intro lst.
      induction lst as [ | t' lst IH ]; [ intros eqH inH; contradiction inH | ].
      simpl; intros eqH [ ttH | inH ].
      + rewrite ttH in eqH; apply (f_equal (hd t) eqH).
      + exact (IH (f_equal (@tl (Term L)) eqH) inH).
  Qed.

  Lemma comp_subst_determines_fvs
        (tau sigma sigma' : Term.V L -> Term L)
    : (forall v, comp_subst sigma tau v = comp_subst sigma' tau v) ->
      (forall v, termset_fv v (subst_im tau) -> sigma v = sigma' v).
  Proof.
    intros eqH v fvH.
    destruct fvH as [ t [ imH fvH ] ].
    destruct imH as [ v' tH ].
    specialize (eqH v'); revert eqH.
    unfold comp_subst; simpl; rewrite <- tH; clear v' tH.
    eauto using subst_endo_determines_fvs.
  Qed.

  (** A fact about free variables in substitutions. *)
  Lemma term_fv_in_subst_endo sigma v w t
    : term_fv v t ->
      term_fv w (sigma v) ->
      term_fv w (subst_endo sigma t).
  Proof.
    revert t.
    apply (Term_ind' (fun t => term_fv v t ->
                               term_fv w (sigma v) ->
                               term_fv w (subst_endo sigma t))); simpl.
    - intros v0 eqH; rewrite eqH; auto.
    - intros f ts IH someH fvH.
      destruct (vec_some_to_list _ _ someH) as [ t [ inH fvH' ] ]; clear someH.
      apply vec_some_map_intro.
      apply (vec_some_to_list_intro _ ts t inH).
      apply (vec_all_to_list _ _ IH t inH fvH' fvH).
  Qed.

  (** What does it mean for v to be to be free in the image of a
      substitution? One take is that there is some term, t, in the
      image of the substitution where v is a free variable of t
      (that's the definition). But, equivalently, there could exist
      some variable, w, such that v is free in sigma w. *)
  Lemma termset_fv_subst_im v sigma
    : termset_fv v (subst_im sigma) <->
      exists w, term_fv v (sigma w).
  Proof.
    split.
    - destruct 1 as [ t [ substH fvH ] ].
      destruct substH as [ w tH ].
      exists w; rewrite <- tH; auto.
    - destruct 1 as [ w fvH ].
      exists (sigma w); split; auto.
      exists w; auto.
  Qed.
End fv.
