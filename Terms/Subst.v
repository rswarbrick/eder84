(** This library describes a [fin_subst] (called a substitution in
    Eder's paper), which is a rule for substituting terms for
    variables in a term. *)

Require Import Lists.List.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.

Require Import Top.Terms.Term.
Require Import Top.Terms.VecUtils.

(** * Substitutions

    Eder's paper talks about substitutions as if they are
    endomorphisms on Term, but he is only interested in the
    endomorphisms that come about from actual substitutions: maps
    from variables to terms which may or may not themselves be
    variables.

    Let's start by defining the induced endomorphism on Term that
    comes from a substitution. *)
Section subst.
  Variable L : lType.

  Definition Subst := Term.V L -> Term L.

  Fixpoint subst_endo (s : Subst) (t : Term L) : Term L :=
    match t with
    | varTerm _ v => s v
    | funTerm f ts => funTerm f (VectorDef.map (subst_endo s) ts)
    end.

  (** One map from [V] to [Term] is [varTerm] (the [Term] constructor
      for variable names). This should induce the identity. The point
      is that the induced endomorphism is exactly filling in each "v"
      with "v" again.  *)

  Lemma subst_endo_varTerm {t}
    : subst_endo (varTerm L) t = t.
  Proof.
    revert t; apply Term_ind'; try reflexivity.
    intros f ts allH.
    unfold subst_endo; fold subst_endo.
    apply f_equal.
    induction ts as [ | t n ts IH ]; try reflexivity.
    destruct allH as [ tH tsH ].
    specialize (IH tsH); clear tsH.
    unfold VectorDef.map;
      fold (@VectorDef.map (Term L) _ (subst_endo (varTerm L))).
    rewrite IH, tH.
    exact eq_refl.
  Qed.

  (** Another fact we might want to know about these induced
      endomorphisms is extensionality. That is, if two substitutions
      have the same values on all of [V] then their induced
      endomorphisms have the same values on all of [Term]. (This sort
      of messing around is needed because functions aren't extensional
      in Coq). *)

  Lemma subst_endo_ex {s s' t}
    : (forall v, s v = s' v) -> subst_endo s t = subst_endo s' t.
  Proof.
    intro eqH.
    revert t; apply Term_ind'.
    - intro v; specialize (eqH v). tauto.
    - intros f ts allH.
      unfold subst_endo; fold subst_endo.
      apply f_equal.
      apply vec_map_ext.
      exact allH.
  Qed.

  (** Obviously, we can't compose substitutions directly (because they
      are maps [V -> Term]). However, we can compose their induced
      endomorphisms and then restrict back to variables by composing
      with [varTerm]. *)

  Definition comp_subst (sigma tau : Subst) : Subst :=
    fun v => subst_endo sigma (tau v).

  (** Fortunately, given the name, [comp_subst] is indeed the right
      notion of composition of substitutions. In fact, if you compose
      the induced endomorphisms from two substitutions, you get the
      same thing as if you use [comp_subst] to compose the
      substitutions and then induce the endomorphism. *)

  Lemma compose_subst_endo (sigma tau : Subst) (t : Term L)
    : subst_endo sigma (subst_endo tau t) =
      subst_endo (comp_subst sigma tau) t.
  Proof.
    revert t; apply Term_ind'; try tauto.
    intros f ts IH.
    unfold subst_endo; fold subst_endo; apply f_equal.
    rewrite vec_map_map.
    auto using vec_map_ext.
  Qed.

  (** As you would hope, [varTerm] is a left and right identity for
      [comp_subst]. *)

  Lemma comp_subst_idl {sigma v} : comp_subst (varTerm L) sigma v = sigma v.
  Proof.
    unfold comp_subst; auto using subst_endo_varTerm.
  Qed.

  Lemma comp_subst_idr {sigma v} : comp_subst sigma (varTerm L) v = sigma v.
  Proof.
    unfold comp_subst; auto using subst_endo_varTerm.
  Qed.

  (** Also, unsurprisingly, [comp_subst] is associative. *)

  Lemma comp_subst_assoc {s1 s2 s3 v}
    : comp_subst s1 (comp_subst s2 s3) v = comp_subst (comp_subst s1 s2) s3 v.
  Proof.
    unfold comp_subst; simpl.
    generalize (s3 v); clear s3 v.
    apply Term_ind'; try reflexivity.
    intros f ts IH.
    unfold subst_endo at 2; fold subst_endo.
    unfold subst_endo at 1; fold subst_endo.
    unfold subst_endo at 3; fold subst_endo.
    apply f_equal.
    rewrite vec_map_map.
    apply vec_map_ext.
    exact IH.
  Qed.

  (** A technical lemma about extensionality. If we have two
      factorisations where the factors are extensionally equal, then the
      composite maps must be too. *)

  Lemma comp_subst_ex {r r' s s'} (v : Term.V L)
    : (forall v, r v = r' v) ->
      (forall v, s v = s' v) ->
      comp_subst r s v = comp_subst r' s' v.
  Proof.
    intros rH sH.
    unfold comp_subst; rewrite sH, (subst_endo_ex rH); auto.
  Qed.

  (** Define the image of a substitution: the terms that you get when
      applying the substitution to each variable in [V]. The set is
      encoded as a predicate. *)
  Definition subst_im (s : Subst) (t : Term L) : Prop :=
    exists v, t = s v.

  (** * Finite substitutions

      Now we get to an important definition: [fin_subst]. Eder is only
      interested in substitutions that map only finitely many
      variables differently from [varTerm]. In our development, this
      means that it should be a finite modification of [varTerm]. *)

  Definition fin_subst := fin_mod (varTerm L).

  (** We can construct our first [fin_subst] from varTerm. Since this
      is a trivial modification of [varTerm], it definitely satisfies
      the definition. *)

  Lemma fin_subst_varTerm : fin_subst (varTerm L).
  Proof.
    apply fin_mod_i.
  Qed.

  (** It's a bit more difficult to show that [fin_subst] maps are
      closed under composition (using [comp_subst]). I think that the
      substitution that induces the composition of two induced
      endomorphisms is actually easiest to define by concatenating
      lists, so we start in terms of list maps. *)

  Section fin_comp_subst.
    Variables sigma tau : Subst.
    Variable sl tl : list (Term.V L * Term L).

    Hypothesis decV : forall x y : Term.V L, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : Term.F L, {x = y} + {x <> y}.

    Hypothesis sH : forall v, sigma v = list_map decV (varTerm L) sl v.
    Hypothesis tH : forall v, tau v = list_map decV (varTerm L) tl v.

    (** A list inducing the correct correct composed map ([compose
        sigma tau]) is given by first mapping all the variables to
        where [tau] would send them and then applying the induced map
        from [sigma] to the resulting term.

        Variables that weren't moved by [tau] get mapped by [sigma],
        which we can express by shoving them to the end of the
        list. *)

    Local Definition stl : list (Term.V L * Term L) :=
      app (map (fun p => (fst p, subst_endo sigma (snd p))) tl)
          sl.

    Lemma stl_map_v v
      : list_map decV (varTerm L) stl v = comp_subst sigma tau v.
    Proof.
      specialize (tH v).
      unfold comp_subst, subst_endo, stl.
      set (pmap := (fun p => (fst p, subst_endo sigma (snd p)))).
      revert tau tH.
      induction tl as [ | p tl' IH ].
      - intros; rewrite tH; simpl; auto.
      - intros tau tH.
        clear tl; rename tl' into tl.
        rewrite (map_cons pmap p tl), <- app_comm_cons.
        destruct p as [ v' sv' ].
        destruct (decV v' v) as [ veqH | vneH ].
        + rewrite veqH in *; clear v' veqH.
          simpl in tH; rewrite upd_map_at in tH.
          unfold pmap; simpl; rewrite upd_map_at.
          rewrite tH. tauto.
        + unfold pmap at 1; simpl.
          rewrite (upd_map_not_at decV _ _ (not_eq_sym vneH)).
          simpl in tH.
          rewrite (upd_map_not_at decV _ _ (not_eq_sym vneH)) in tH.
          apply IH.
          apply tH.
    Qed.
  End fin_comp_subst.

  (** Since we worked in terms of list maps, we now must use the
      correspondence between those and finite mods to conclude that
      the composition of two finite substitutions is itself finite
      (assuming that equality of terms is decidable) *)

  Lemma fin_subst_comp sigma tau
    : (forall x y : Term.V L, {x = y} + {x <> y}) ->
      (forall x y : Term.F L, {x = y} + {x <> y}) ->
      fin_subst sigma -> fin_subst tau -> fin_subst (comp_subst sigma tau).
  Proof.
    unfold fin_subst at 1 2.
    intros decV decF fmS fmT.
    set (decT := (decTerm decV decF)).
    destruct (fin_mod_is_list_map decV decT fmS) as [ sl slH ].
    destruct (fin_mod_is_list_map decV decT fmT) as [ tl tlH ].
    destruct slH as [ slH _ ].
    destruct tlH as [ tlH _ ].
    apply (fin_mod_ex _ _ _ _
                      (fun x => eq_refl (varTerm L x))
                      (stl_map_v sigma tau sl tl decV slH tlH)).
    apply (fin_mod_list_map decV _ decT).
  Qed.

  (** Finally, we show that restricting a finite substitution to
      variables satisfying some predicate doesn't stop it being
      finite. *)

  Lemma fin_subst_restrict
        {s P} (decP : forall v : Term.V L, {P v} + {~ P v})
    : fin_subst s -> fin_subst (restrict_map (varTerm L) P decP s).
  Proof.
    unfold fin_subst.
    apply restrict_preserves_fin_mod.
  Qed.

  Lemma term_height_subst {s}
    : forall t, term_height t <= term_height (subst_endo s t).
  Proof.
    apply Term_ind'; auto using le_0_n.
    intros.
    apply le_n_S; fold (subst_endo s); fold term_height.
    auto using vec_max_at_map_le.
  Qed.

  Lemma term_height_comp_subst {s' s v}
    : term_height (s v) <= term_height (comp_subst s' s v).
  Proof.
    apply term_height_subst.
  Qed.
End subst.
