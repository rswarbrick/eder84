Require Import Compare_dec.
Require Import PeanoNat.

Require Import Top.Terms.Term.
Require Import Top.Terms.VecUtils.

Set Implicit Arguments.

Section term_at.
  Variable L : lType.

  (** The [term_at] function is an analogue of [nth_error] on lists. *)
  Fixpoint term_at (pos : list nat) (t : Term L) : option (Term L) :=
    match pos with
    | nil => Some t
    | cons i pos' =>
      match t with
      | varTerm _ _ => None
      | funTerm f ts =>
        match lt_dec i (Term.a L f) with
        | left ltH => term_at pos' (VectorDef.nth_order ts ltH)
        | right _ => None
        end
      end
    end.

  Lemma term_at_cons_fun i pos f ts (ltH : i < Term.a L f)
    : term_at (cons i pos) (funTerm f ts) =
      term_at pos (VectorDef.nth_order ts ltH).
  Proof.
    simpl; destruct (lt_dec i (Term.a L f)) as [ ltH' | ]; try contradiction.
    unfold VectorDef.nth_order.
    rewrite (Fin.of_nat_ext ltH ltH'); auto.
  Qed.

  Lemma term_height_term_at t t' pos
    : term_at pos t = Some t' ->
      term_height t >= length pos + term_height t'.
  Proof.
    revert t; induction pos as [ | i pos IH ]; intro t; simpl.
    - injection 1; intro tH; rewrite tH; auto.
    - destruct t as [ | f ts ]; try discriminate.
      destruct (lt_dec i (Term.a L f)) as [ ltH | ]; try discriminate.
      intro someH; simpl.
      unfold ge. apply le_n_S.
      apply (Nat.le_trans _ (term_height (VectorDef.nth_order ts ltH))).
      + exact (IH _ someH).
      + exact (vec_max_at_ge_nth_order (term_height (L := L)) ts ltH).
  Qed.
End term_at.
