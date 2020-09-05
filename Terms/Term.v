(** This library describes a [Term], which is the general form of an
    expression considered in Eder's paper. This is essentially a tree
    of function applications and variable instances. It also describes
    a [fin_subst] (called a substitution in Eder's paper), which is a
    rule for substituting terms for variables in a term. *)

Require Import Lists.List.
Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.Fin.
Require Vectors.VectorDef.
Require Import Program.Basics.
Require Import Bool.

Require Import Top.Terms.VecUtils.
Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.

Set Implicit Arguments.

Definition vec := VectorDef.t.

Lemma orb_elim_left a b c
  : orb a b = orb a c -> orb a (eqb b c) = true.
Proof.
  destruct a, b, c; auto.
Qed.

Lemma orb_intro_left a b c
  : is_true a \/ b = c -> orb a b = orb a c.
Proof.
  destruct a; unfold is_true; simpl; auto.
  intro H; destruct H as [ eqFT | ]; auto.
  contradiction (diff_false_true eqFT).
Qed.

(** * Terms

    When talking about terms, we fix types [V] and [F]. Elements of
    [V] are variable names and elements of [F] should be thought of as
    functions or operators. There is also an arity function, [a],
    which gives the arity of each function.

    Rather than pass these types around separately, we pack them into
    a module (in a similar style to that used in mathcomp). *)

Module Lmodule.
  Structure type : Type := Pack { V : Type; F : Type; a : F -> nat }.
End Lmodule.

Notation lType := Lmodule.type.
Notation LType := Lmodule.Pack.

Section Term.
  Variable L : lType.

  Local Definition V := Lmodule.V L.
  Local Definition F := Lmodule.F L.
  Local Definition a := Lmodule.a L.

  Inductive Term : Type :=
  | varTerm : V -> Term
  | funTerm (f : F) (ts : vec Term (a f)) : Term.

  (** When defining a function on terms, you need an induction
      rule. We use vectors to represent the rose tree structure of a
      term and Coq's automatic induction rule isn't strong enough, so
      we define a better one here. *)

  Section Term_ind'.
    Variable P : Term -> Prop.
    Hypothesis vH : forall v, P (varTerm v).
    Hypothesis fH : forall f, forall ts, vec_all P ts -> P (funTerm f ts).

    Fixpoint Term_ind' (t : Term) : P t :=
      match t with
      | varTerm v => vH v
      | funTerm f ts =>
        fH f ts
           (VectorDef.t_rect Term (fun _ v => vec_all P v)
                             (vec_all_nil P)
                             (fun t n v => vec_all_cons _ _ (Term_ind' t))
                             (a f) ts)
      end.
  End Term_ind'.

  (** We also define a structural recursion rule for [Term]
      objects. This is a little more finicky because it lets us
      recurse over the structure of the function vectors as well as
      the term itself.

      The [varH] hypothesis says that [P] holds for all terms that are
      just a variable. The [funH] hypothesis says that if we know [Q]
      holds for a vector of terms (of the correct length), then [P]
      will hold when we use them to make arguments for a function
      term. To show that [Q] ever holds, we then need to know that it
      holds for the empty vector ([qnilH]) and that it holds for a
      cons if [P] holds for the item we're adding. *)

  Section Term_rect'.
    Variable P : Term -> Type.
    Variable Q : forall n, vec Term n -> Type.

    Variable varH : forall v, P (varTerm v).
    Variable funH : forall f, forall ts, Q ts -> P (funTerm f ts).
    Variable qnilH : Q (VectorDef.nil _).
    Variable qconsH : forall t n (ts : vec Term n),
        P t -> Q ts -> Q (VectorDef.cons _ t _ ts).

    Fixpoint Term_rect' (t : Term) : P t :=
      match t with
      | varTerm v => varH v
      | funTerm f ts =>
        funH f
             (VectorDef.t_rect Term Q qnilH
                               (fun t' n ts' => qconsH (Term_rect' t'))
                               (a f) ts)
      end.
  End Term_rect'.

  Lemma varTerm_ne_funTerm v f ts : varTerm v <> funTerm f ts.
  Proof.
    intros eqH. inversion eqH.
  Qed.

  (** The [decTerm] fixpoint shows that equality in [Term] is
      decidable if it is decidable for the functions and variable
      names. *)

  Section DecTerm.
    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    Fixpoint decTerm (x y : Term) : {x = y} + {x <> y}.
      refine (match x, y with
              | varTerm v, varTerm v' => _
              | varTerm v, funTerm f ts => _
              | funTerm f ts, varTerm v => _
              | funTerm f ts, funTerm f' ts' => _
              end
             ).
      - destruct (decV v v') as [ eqH | neH ].
        + exact (left (f_equal varTerm eqH)).
        + enough (H: varTerm v <> varTerm v');
            try (exact (right H)).
          injection; tauto.
      - exact (right (@varTerm_ne_funTerm v f ts)).
      - exact (right (not_eq_sym (@varTerm_ne_funTerm v f ts))).
      - destruct (decF f f') as [ feqH | fneH ].
        + revert ts'. rewrite <- feqH. clear feqH; intro ts'.
          destruct (dec_vec decTerm ts ts') as [ tseqH | tsneH ].
          * apply left. apply f_equal. exact tseqH.
          * apply right. intro funH. inversion funH.
            exact (tsneH (inj_pair2_eq_dec
                            F decF (fun f => vec Term (a f)) f ts ts' H0)).
        + enough (H: funTerm f ts <> funTerm f' ts');
            try (exact (right H)).
          injection; tauto.
    Qed.
  End DecTerm.

  (** * Substitutions

      Eder's paper talks about substitutions as if they are
      endomorphisms on Term, but he is only interested in the
      endomorphisms that come about from actual substitutions: maps
      from variables to terms which may or may not themselves be
      variables.

      Let's start by defining the induced endomorphism on Term that
      comes from a substitution. *)

  Fixpoint subst_endo (s : V -> Term) (t : Term) : Term :=
    match t with
    | varTerm v => s v
    | funTerm f ts => funTerm f (VectorDef.map (subst_endo s) ts)
    end.

  (** One map from [V] to [Term] is [varTerm] (the [Term] constructor
      for variable names). This should induce the identity. The point
      is that the induced endomorphism is exactly filling in each "v"
      with "v" again.  *)

  Lemma subst_endo_varTerm {t}
    : subst_endo varTerm t = t.
  Proof.
    revert t; apply Term_ind'; try reflexivity.
    intros f ts allH.
    unfold subst_endo; fold subst_endo.
    apply f_equal.
    induction ts as [ | t n ts IH ]; try reflexivity.
    destruct allH as [ tH tsH ].
    specialize (IH tsH); clear tsH.
    unfold VectorDef.map; fold (@VectorDef.map Term _ (subst_endo varTerm)).
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

  Definition comp_subst (sigma tau : V -> Term) :=
    compose (compose (subst_endo sigma) (subst_endo tau)) varTerm.

  (** Fortunately, given the name, [comp_subst] is indeed the right
      notion of composition of substitutions. In fact, if you compose
      the induced endomorphisms from two substitutions, you get the
      same thing as if you use [comp_subst] to compose the
      substitutions and then induce the endomorphism. *)

  Lemma compose_subst_endo (sigma tau : V -> Term) (t : Term)
    : compose (subst_endo sigma) (subst_endo tau) t =
      subst_endo (comp_subst sigma tau) t.
  Proof.
    revert t; apply Term_ind'; try tauto.
    intros f ts IH.
    unfold compose, subst_endo; fold subst_endo; apply f_equal.
    rewrite vec_map_map.
    auto using vec_map_ext.
  Qed.

  (** As you would hope, [varTerm] is a left and right identity for
      [comp_subst]. *)

  Lemma comp_subst_idl {sigma v} : comp_subst varTerm sigma v = sigma v.
  Proof.
    unfold comp_subst, compose.
    unfold subst_endo at 2.
    rewrite subst_endo_varTerm.
    exact eq_refl.
  Qed.

  Lemma comp_subst_idr {sigma v} : comp_subst sigma varTerm v = sigma v.
  Proof.
    unfold comp_subst, compose, subst_endo.
    exact eq_refl.
  Qed.

  (** Also, unsurprisingly, [comp_subst] is associative. *)

  Lemma comp_subst_assoc {s1 s2 s3 v}
    : comp_subst s1 (comp_subst s2 s3) v = comp_subst (comp_subst s1 s2) s3 v.
  Proof.
    unfold comp_subst, compose; simpl.
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

  Lemma comp_subst_ex {r r' s s'} (v : V)
    : (forall v, r v = r' v) ->
      (forall v, s v = s' v) ->
      comp_subst r s v = comp_subst r' s' v.
  Proof.
    intros rH sH.
    unfold comp_subst, compose.
    rewrite (subst_endo_ex sH).
    rewrite (subst_endo_ex rH).
    exact eq_refl.
  Qed.

  (** Define the image of a substitution: the terms that you get when
      applying the substitution to each variable in [V]. The set is
      encoded as a predicate. *)
  Definition subst_im (s : V -> Term) (t : Term) : Prop :=
    exists v, t = s v.

  (** * Finite substitutions

      Now we get to an important definition: [fin_subst]. Eder is only
      interested in substitutions that map only finitely many
      variables differently from [varTerm]. In our development, this
      means that it should be a finite modification of [varTerm]. *)

  Definition fin_subst := fin_mod varTerm.

  (** We can construct our first [fin_subst] from varTerm. Since this
      is a trivial modification of [varTerm], it definitely satisfies
      the definition. *)

  Lemma fin_subst_varTerm : fin_subst varTerm.
  Proof.
    apply fin_mod_i.
  Qed.

  (** It's a bit more difficult to show that [fin_subst] maps are
      closed under composition (using [comp_subst]). I think that the
      substitution that induces the composition of two induced
      endomorphisms is actually easiest to define by concatenating
      lists, so we start in terms of list maps. *)

  Section fin_comp_subst.
    Variables sigma tau : V -> Term.
    Variable sl tl : list (V * Term).

    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    Hypothesis sH : forall v : V, sigma v = list_map decV varTerm sl v.
    Hypothesis tH : forall v : V, tau v = list_map decV varTerm tl v.

    (** A list inducing the correct correct composed map ([compose
        sigma tau]) is given by first mapping all the variables to
        where [tau] would send them and then applying the induced map
        from [sigma] to the resulting term.

        Variables that weren't moved by [tau] get mapped by [sigma],
        which we can express by shoving them to the end of the
        list. *)

    Local Definition stl : list (V * Term) :=
      app (map (fun p => (fst p, subst_endo sigma (snd p))) tl)
          sl.

    Lemma stl_map_v (v : V)
      : list_map decV varTerm stl v = comp_subst sigma tau v.
    Proof.
      specialize (tH v).
      unfold comp_subst, compose, subst_endo at 2, stl.
      set (pmap := (fun p : V * Term => (fst p, subst_endo sigma (snd p)))).
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
    : (forall x y : V, {x = y} + {x <> y}) ->
      (forall x y : F, {x = y} + {x <> y}) ->
      fin_subst sigma -> fin_subst tau -> fin_subst (comp_subst sigma tau).
  Proof.
    unfold fin_subst at 1 2.
    intros decV decF fmS fmT.
    set (decT := (decTerm decV decF)).
    destruct (fin_mod_is_list_map decV decT fmS) as [ sl slH ].
    destruct (fin_mod_is_list_map decV decT fmT) as [ tl tlH ].
    destruct slH as [ slH _ ].
    destruct tlH as [ tlH _ ].
    apply (fin_mod_ex varTerm varTerm _ _
                      (fun x => eq_refl (varTerm x))
                      (stl_map_v sigma tau sl tl decV slH tlH)).
    apply (fin_mod_list_map decV varTerm decT).
  Qed.

  (** Finally, we show that restricting a finite substitution to
      variables satisfying some predicate doesn't stop it being
      finite. *)

  Lemma fin_subst_restrict {s P} (decP : forall v : V, {P v} + {~ P v})
    : fin_subst s -> fin_subst (restrict_map varTerm P decP s).
  Proof.
    unfold fin_subst.
    apply restrict_preserves_fin_mod.
  Qed.

  (** If variables have decidable equality then [mod_elt varTerm] is
      decidable. However, [mod_elt varTerm] asks that two things are not equal
      (the substitution should map an element to something different from
      [varTerm]). This isn't great, because if it's false you have a double
      negation, which you can't get rid of without the law of excluded middle.
      Thus we unfold the double negation in the second part of the sumbool. *)

  Lemma dec_mod_elt_varTerm
        (decV : forall v w : V, {v = w} + {v <> w})
        (sigma : V -> Term)
        (v : V)
    : {mod_elt varTerm sigma v} + {sigma v = varTerm v}.
  Proof.
    unfold mod_elt.
    destruct (sigma v) as [ w | ]; clear sigma.
    - destruct (decV v w) as [ eqH | neH ].
      + right; rewrite eqH; auto.
      + left; injection; auto.
    - left; discriminate.
  Qed.

  (** * Heights

      When trying to show things about terms, it's sometimes useful to
      know their heights. This is the maximum nesting depth of
      function terms. In particular, a substitution can never decrease
      the height of a term.
   *)

  Fixpoint term_height (t : Term) : nat :=
    match t with
    | varTerm v => O
    | funTerm f ts => S (vec_max_at term_height ts)
    end.

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

  (** * Free variables

      A term may have free variables. This is a set, so we encode it
      as a predicate: [term_fv t v] means "v is a free variable in
      t". This is extended by union in the obvious way to sets of
      terms and sets of sets of terms.

      This matches the notation in 2.8 in Eder's paper.

   *)

  Fixpoint term_fv (v : V) (t : Term) : Prop :=
    match t with
    | varTerm v' => v = v'
    | funTerm f ts => vec_some (term_fv v) ts
    end.

  Definition termset_fv (v : V) (M : Term -> Prop) : Prop :=
    exists t : Term, M t /\ term_fv v t.

  Definition termsetset_fv (v : V) (P : (Term -> Prop) -> Prop) : Prop :=
    exists M : Term -> Prop, P M /\ termset_fv v M.

  (**

    If we have decidable equality on terms, there's a decision procedure to
    check whether a variable is free in a given term. Sadly, we can't use
    [check_vec_someb] for checking through the vector of a [funTerm] (because
    we'd be passing [check_term_fv decV v] as the function to map, which isn't
    a structural recursion).

   *)
  Fixpoint check_term_fv
           (decV : forall v w : V, {v = w} + {v <> w})
           (v : V) (t : Term) : bool :=
    match t with
    | varTerm w => if decV v w then true else false
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
    revert ts; generalize (a f).
    induction ts as [ | t n ts IH ]; auto.
    rewrite check_vec_someb_cons.
    apply orb_intro_left; auto.
  Qed.

  Lemma check_term_fv_correct
        (decV : forall v w : V, {v = w} + {v <> w})
        (v : V) (t : Term)
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
      revert ts allH; generalize (a f); clear f t.
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
             (decV : forall v w : V, {v = w} + {v <> w})
             (v : V) (t : Term)
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

  Lemma var_in_M_is_free_var (v : V) (M : Term -> Prop)
    : M (varTerm v) -> termset_fv v M.
  Proof.
    exists (varTerm v); simpl; auto.
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
        (decV : forall v w : V, {v = w} + {v <> w})
        (sigma : V -> Term)
        (v : V)
    : mod_elt varTerm sigma v \/ termset_fv v (subst_im sigma).
  Proof.
    destruct (dec_mod_elt_varTerm decV sigma v) as [ | not_mod_eltH ]; auto.
    right; exists (sigma v); split.
    - exists v; auto.
    - revert not_mod_eltH.
      unfold mod_elt.
      case_eq (sigma v); try discriminate.
      intros w sigmavH vtH.
      destruct (decV v w) as [ | neH ]; auto.
      assert (varTerm w <> varTerm v) as vtneH.
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

  Lemma comp_subst_determined_by_fvs (tau sigma sigma' : V -> Term)
    : (forall v, termset_fv v (subst_im tau) -> sigma v = sigma' v) ->
      forall v, comp_subst sigma tau v = comp_subst sigma' tau v.
  Proof.
    intros eqH v.
    unfold comp_subst, compose.
    unfold subst_endo at 2 4.

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
        generalize ts; clear ts; generalize (a f); clear f.
        intros n ts.
        induction ts; simpl; auto.
  Qed.

  Lemma funTerm_inj
        (decF : forall x y : F, {x = y} + {x <> y}) f v v'
    : funTerm f v = funTerm f v' -> v = v'.
  Proof.
    injection 1 as H.
    exact (inj_pair2_eq_dec F decF (fun f => vec Term (a f)) f v v' H).
  Qed.

  Lemma subst_endo_determines_fvs
        (decF : forall x y : F, {x = y} + {x <> y})
        (sigma sigma' : V -> Term) v t
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
        [ apply (funTerm_inj decF eqH) | ]; clear eqH.
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
      + exact (IH (f_equal (@tl Term) eqH) inH).
  Qed.

  Lemma comp_subst_determines_fvs
        (decF : forall x y : F, {x = y} + {x <> y})
        (tau sigma sigma' : V -> Term)
    : (forall v, comp_subst sigma tau v = comp_subst sigma' tau v) ->
      (forall v, termset_fv v (subst_im tau) -> sigma v = sigma' v).
  Proof.
    intros eqH v fvH.
    destruct fvH as [ t [ imH fvH ] ].
    destruct imH as [ v' tH ].
    specialize (eqH v'); revert eqH.
    unfold comp_subst, compose; simpl; rewrite <- tH; clear v' tH.
    eauto using subst_endo_determines_fvs.
  Qed.

End Term.
