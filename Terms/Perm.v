Require Import Program.Basics.

Require Import Top.Terms.Term.
Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinModComp.

(** A var_subst is like a substitution, but induced by a map [V ->
    V]. Composing on the left with [varTerm] gives the substitution
    itself. *)

Section Perm.
  Variable V : Type.
  Variable F : Type.
  Variable a : F -> nat.

  Definition var_subst := sig (@fin_endo V).

  Definition var_subst_subst (s : var_subst) : V -> Term V F a :=
    compose (varTerm V F a) (proj1_sig s).

  Hypothesis decV : forall x y : V, {x = y} + { ~ x = y }.
  Hypothesis decF : forall x y : F, {x = y} + { ~ x = y }.

  (** Since we're generally interested in finite substitutions, we
      would hope that a [var_subst] induces one, and it does. *)

  Lemma fin_subst_var_subst s
    : fin_subst V F a (var_subst_subst s).
  Proof.
    destruct s as [ f finH ]; simpl.
    apply (compose_fin_mod decV decV (decTerm V F a decV decF));
      first [ apply finH | apply fin_mod_i | contradiction ].
  Qed.
End Perm.
