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

Require Import Top.Terms.VecUtils.
Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.

Definition vec := VectorDef.t.

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
                             (fun t n v => vec_all_cons (Term_ind' t))
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
    Variable funH : forall f, forall ts, Q _ ts -> P (funTerm f ts).
    Variable qnilH : Q _ (VectorDef.nil _).
    Variable qconsH : forall t n ts,
        P t -> Q n ts -> Q _ (VectorDef.cons _ t _ ts).

    Fixpoint Term_rect' (t : Term) : P t :=
      match t with
      | varTerm v => varH v
      | funTerm f ts =>
        funH f ts
             (VectorDef.t_rect Term Q qnilH
                               (fun t' n ts' =>
                                  qconsH t' n ts' (Term_rect' t'))
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
      - exact (right (varTerm_ne_funTerm v f ts)).
      - exact (right (not_eq_sym (varTerm_ne_funTerm v f ts))).
      - destruct (decF f f') as [ feqH | fneH ].
        + revert ts'. rewrite <- feqH. clear feqH; intro ts'.
          destruct (dec_vec Term decTerm ts ts') as [ tseqH | tsneH ].
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
  Fixpoint term_fv (t : Term) (v : V) : Prop :=
    match t with
    | varTerm v' => v = v'
    | funTerm f ts => vec_some (fun t => term_fv t v) ts
    end.

  Definition termset_fv (P : Term -> Prop) (v : V) : Prop :=
    exists t : Term, P t /\ term_fv t v.

  Definition termsetset_fv (P : (Term -> Prop) -> Prop) (v : V) : Prop :=
    exists M : Term -> Prop, P M /\ termset_fv M v.

End Term.

Arguments comp_subst {L} sigma tau.
Arguments term_height {L} t.
Arguments term_height_subst {L s}.
Arguments term_height_comp_subst {L s' s v}.

Arguments term_fv {L} t v.
Arguments termset_fv {L} P v.
Arguments termsetset_fv {L} P v.
