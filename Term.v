Require Import Lists.List.
Require Vectors.Fin.
Require Vectors.VectorDef.

Require Import SymbComp.FinMod.

Definition fin := Fin.t.
Definition vec := VectorDef.t.

Section vec_all.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint vec_all {n} (v : vec A n) :=
    match v with
    | VectorDef.nil _ => True
    | VectorDef.cons _ a _ v' => P a /\ vec_all v'
    end.

  Definition vec_all_nil : vec_all (VectorDef.nil _) := I.

  Lemma vec_all_singleton a
    : P a -> vec_all (VectorDef.cons _ a _ (VectorDef.nil _)).
  Proof.
    unfold vec_all. auto.
  Qed.

  Lemma vec_all_cons a {n} (v : vec A n)
    : P a -> vec_all v -> vec_all (VectorDef.cons _ a _ v).
  Proof.
    intros aH vH.
    unfold vec_all; fold (@vec_all n).
    exact (conj aH vH).
  Qed.
End vec_all.

Arguments vec_all {A} P {n}.
Arguments vec_all_nil {A} P.
Arguments vec_all_singleton {A P a} aH.
Arguments vec_all_cons {A P a n v} aH vH.

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
     define by concatenating lists. TODO! *)
End Term.
