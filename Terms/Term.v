(** This library describes a [Term], which is the general form of an
    expression considered in Eder's paper. This is essentially a tree
    of function applications and variable instances. *)

Require Import Bool.
Require Import Lists.List.
Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.Fin.
Require Vectors.VectorDef.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.

Require Import Top.Terms.VecUtils.

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

End Term.
