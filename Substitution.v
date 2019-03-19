Require Import Lists.List.
Require Import SymbComp.FinMod.
Require Import Program.Basics.

Set Implicit Arguments.

Section Substitution.
  Variable A : Type.
  Hypothesis decA : forall x y : A, {x = y} + { ~ x = y }.

  Definition sub := sig (@fin_endo A).
  Definition sub_map (x : sub) : A -> A := proj1_sig x.

  Lemma fin_endo_sub_map x : fin_endo (sub_map x).
  Proof.
    destruct x. auto.
  Qed.

  (* The identity is always a substitution *)
  Definition id_sub : sub := (exist _ id fin_endo_id).

  (* Substitutions are closed under composition *)
  Definition comp_sub (g f : sub) : sub :=
    exist _ (compose (sub_map g) (sub_map f))
          (compose_fin_endo decA (fin_endo_sub_map f) (fin_endo_sub_map g)).

End Substitution.

(* Restrictions

   A substitution can be restricted by giving a (decidable) predicate
   for whether the substitution is allowed not to be the identity.
*)
Section Restrictions.
  Variable A : Type.
  Variable in_spt : A -> Prop.
  Hypothesis dec_in_spt : forall a, {in_spt a} + {~ in_spt a}.

  Definition restrict (s : sub A) : sub A :=
    let f' := restrict_map in_spt dec_in_spt (sub_map s) in
    exist _ f' (restrict_preserves_fin_endo _ _ (fin_endo_sub_map s)).

  Lemma sub_map_restrict s
    : sub_map (restrict s) = restrict_map in_spt dec_in_spt (sub_map s).
  Proof.
    reflexivity.
  Qed.
End Restrictions.
