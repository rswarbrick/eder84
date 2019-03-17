(** * Describing endomorphisms by a list of pairs

    A finite endomorphism, as defined in the [SymbComp.FinEndo]
    library, is exactly the same thing as an endomorphism that can be
    described by a list of successive updates ("send [a] to [b]")
    applied to the identity map. In this theory, we prove this fact.
*)

Require Import Lists.List.
Require Import SymbComp.FinEndo.
Require Import SymbComp.FinSet.
Require Import Program.Basics.

Set Implicit Arguments.

(** ** Updating a map

    The first thing to describe is the process of updating an existing
    map at a single point. This needs the domain of the map to be
    decidable (since the updated map works by checking whether it's
    argument is equal to the place it was updated).
*)

Section UpdMap.
  Variable A : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.

  Definition upd_map {B : Type} (p : A * B) (f : A -> B) (a : A) : B :=
    match decA a (fst p) with
    | left _ => snd p
    | right _ => f a
    end.

  (**

       At this point, we fix some endomorphism [f : A -> A] and want
       to prove that updating it with a pair doesn't stop it being
       finite. To prove this, we try to define a map from [dom f +
       unit] to [dom (upd_map p f)] which will induce the surjection
       in the underlying sets. The idea is that the image of [tt] in
       [unit] is [fst p], together with a proof that it's in the
       domain. Of course, it might be that [fst p = snd p], in which
       case it's not in the domain. To deal with this, we actually map
       to [option (dom (upd_map p f))] and allow ourselves to map to
       [None] in that case.

   *)

  Variable f : A -> A.
  Variable p : A * A.

  Local Definition map_a (a : A) : option (dom (upd_map p f)) :=
    match decA (upd_map p f a) a with
    | left eqH => None
    | right neqH => Some (exist _ a neqH)
    end.

  Local Definition proj0 (x : dom f + unit) : A :=
    match x with
    | inl x => dom_elt x
    | inr tt => fst p
    end.

  Local Definition proj1 : dom (upd_map p f) -> A :=
    dom_elt (f := upd_map p f).

  Local Definition top_map (x : dom f + unit) : option (dom (upd_map p f)) :=
    match x with
    | inl (exist _ a H) => map_a a
    | inr tt => map_a (fst p)
    end.

  Local Definition bot_map (a : A) : option A := option_map proj1 (map_a a).

  Local Lemma finite_proj0 : fin_endo f -> FiniteProj proj0.
  Proof.
    unfold FiniteProj.
    destruct 1 as [ l H ].
    exists (cons (inr tt) (map inl l)).
    unfold FullProj. intro x.
    destruct x.
    - apply in_proj_cons.
      unfold proj0 at 2.
      unfold FullProj in H. specialize (H d).
      revert H.
      apply (in_proj_map_id_g inl (dom_elt (f:=f)) proj0
                              (dom_elt d) l); reflexivity.
    - apply in_proj_eq.
      destruct u.
      reflexivity.
  Qed.

  Local Lemma natH x : option_map proj1 (top_map x) = bot_map (proj0 x).
  Proof.
    unfold bot_map; apply f_equal.
    destruct x as [ d | u ].
    - destruct d; auto.
    - destruct u; auto.
  Qed.

  Local Ltac dec_a_equal :=
    unfold map_a;
    repeat (match goal with
            | [ |- context [decA ?X ?Y]] =>
              case (decA X Y)
            | _ => reflexivity
            | _ => contradiction
            end).

  Local Lemma surjH (d' : dom (upd_map p f))
    : exists a : dom f + unit, bot_map (proj0 a) = Some (proj1 d').
  Proof.
    destruct d' as [ a H ]; unfold in_dom in H. simpl.
    case (decA (fst p) a).
    - intro fstH.
      exists (inr tt).
      simpl. unfold bot_map, map_a.
      case (decA (upd_map p f (fst p)) (fst p)).
      + rewrite <- fstH in H. contradiction.
      + simpl. rewrite fstH. tauto.
    - intro rstH.
      assert (not_H_a: a <> fst p); auto.
      assert (IH: upd_map p f a = f a);
        unfold upd_map; dec_a_equal.
      assert (aH: in_dom f a);
        unfold in_dom in H; unfold in_dom. rewrite <- IH; auto.
      exists (inl (exist _ a aH)).
      unfold bot_map; dec_a_equal.
  Qed.

  (**

        We can finally prove the lemma that we wanted. Note that we
        use the [finite_surj_option] lemma from the FinEndo library.
        This avoids some of the faffing around with option types that
        we'd need otherwise.

   *)

  Lemma fin_endo_upd_map
    : fin_endo f -> fin_endo (upd_map p f).
  Proof.
    intro feH.
    unfold fin_endo.
    apply (finite_surj_option proj1 top_map bot_map (finite_proj0 feH)).
    - exact natH.
    - exact surjH.
  Qed.
End UpdMap.

Fixpoint list_endo {A : Type} decA (l : list (A * A)) : A -> A :=
  match l with
  | nil => id
  | cons p l => upd_map decA p (list_endo decA l)
  end.

Lemma list_endo_nil {A : Type} (decA : forall x y : A, {x = y} + {x <> y}) :
  list_endo decA nil = id.
Proof. reflexivity. Qed.

Lemma list_endo_cons {A : Type} (decA : forall x y : A, {x = y} + {x <> y}) p l
  : list_endo decA (cons p l) = upd_map decA p (list_endo decA l).
Proof. reflexivity. Qed.

Lemma fin_endo_list_endo {A : Type} decA (l : list (A * A))
  : fin_endo (list_endo decA l).
Proof.
  induction l as [ | pr l IH ].
  - simpl. apply fin_endo_id.
  - unfold list_endo. fold (list_endo decA).
    apply fin_endo_upd_map.
    exact IH.
Qed.
