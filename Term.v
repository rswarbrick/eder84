Require Import Lists.List.
Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.Fin.
Require Vectors.VectorDef.

Require Import SymbComp.VecUtils.
Require Import SymbComp.FinMod.
Require Import SymbComp.ListMod.

Definition vec := VectorDef.t.

Section Term.
  Variable V : Set.
  Variable F : Set.
  Variable a : F -> nat.

  Inductive Term : Type :=
  | varTerm : V -> Term
  | funTerm (f : F) (ts : vec Term (a f)) : Term.

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

  Section DecTerm.
    (* Equality in Term is decidable if it is in V and F *)
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

  (* Eder's paper talks about substitutions as if they are
     endomorphisms on Term, but he is only interested in the
     endomorphisms that come about from actual substitutions: maps
     from variables to terms which may or may not themselves be
     variables.

     Let's start by defining the induced endomorphism on Term that
     comes from a substitution.  *)
  Fixpoint subst_endo (s : V -> Term) (t : Term) : Term :=
    match t with
    | varTerm v => s v
    | funTerm f ts => funTerm f (VectorDef.map (subst_endo s) ts)
    end.

  (* The induced endomorphism from varTerm is the identity *)
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

  (* Eder is only interested in substitutions that map only finitely
     many variables differently from [varTerm] *)
  Definition fin_subst := fin_mod varTerm.

  (* The induced endomorphism from varTerm (the identity) is obviously
     a finite substitution *)
  Lemma fin_subst_varTerm : fin_subst varTerm.
  Proof.
    unfold fin_subst.
    apply fin_mod_i.
  Qed.

  (* Composition is more of a faff. The substitution that induces the
     composition of two induced endomorphisms is actually easiest to
     define by concatenating lists *)

  Section comp_subst.
    Variables sigma tau : V -> Term.
    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    (* TODO! *)

    (*Check (@fin_mod_is_list_map V decV Term varTerm
                                (decTerm decV decF)).*)
  End comp_subst.
End Term.
