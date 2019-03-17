(** A finite endomorphism, as defined in the [SymbComp.FinEndo]
    library, is exactly the same thing as an endomorphism that can be
    described by a list of successive updates ("send [a] to [b]")
    applied to the identity map. In this theory, we prove this fact.
*)

Require Import Lists.List.
Require Import SymbComp.FinEndo.
Require Import SymbComp.FinSet.
Require Import Program.Basics.

Set Implicit Arguments.

Section decA.
  Variable A : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.


  (** * Updating a map

      The first thing to describe is the process of updating an
      existing map at a single point. This needs the domain of the map
      to be decidable (since the updated map works by checking whether
      it's argument is equal to the place it was updated).

   *)

  Section UpdMap.
    Definition upd_map {B : Type} (p : A * B) (f : A -> B) (a : A) : B :=
      match decA a (fst p) with
      | left _ => snd p
      | right _ => f a
      end.

    Lemma upd_map_elim {B : Type} a a' b (f : A -> B) P
      : (a' = a -> P b) ->
        (a' <> a -> P (f a')) ->
        P (upd_map (a, b) f a').
    Proof.
      intros H0 H1.
      unfold upd_map. simpl.
      destruct (decA a' a); auto.
    Qed.

    Lemma upd_map_at {B : Type} a b (f : A -> B)
      : upd_map (a, b) f a = b.
    Proof.
      apply upd_map_elim; first [ reflexivity | contradiction ].
    Qed.

    Lemma upd_map_not_at {B : Type} a a' b (f : A -> B)
      : a' <> a -> upd_map (a, b) f a' = f a'.
    Proof.
      apply upd_map_elim; first [ reflexivity | contradiction ].
    Qed.

    (**

        At this point, we fix some endomorphism [f : A -> A] and want
        to prove that updating it with a pair doesn't stop it being
        finite. To prove this, we try to define a map from [dom f +
        unit] to [dom (upd_map p f)] which will induce the surjection
        in the underlying sets. The idea is that the image of [tt] in
        [unit] is [fst p], together with a proof that it's in the
        domain. Of course, it might be that [fst p = snd p], in which
        case it's not in the domain. To deal with this, we actually
        map to [option (dom (upd_map p f))] and allow ourselves to map
        to [None] in that case.

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

    Ltac dec_a_equal :=
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

  (** * List endomorphisms

      With the results of the previous section, it now just takes a
      quick induction to define the endomorphism described by a list
      of pairs and to see that it has finite domain.
   *)

  Fixpoint list_endo (l : list (A * A)) : A -> A :=
    match l with
    | nil => id
    | cons p l => upd_map p (list_endo l)
    end.

  Lemma list_endo_nil : list_endo nil = id.
  Proof. reflexivity. Qed.

  Lemma list_endo_cons p l : list_endo (cons p l) = upd_map p (list_endo l).
  Proof. reflexivity. Qed.

  Lemma fin_endo_list_endo l : fin_endo (list_endo l).
  Proof.
    induction l as [ | pr l IH ].
    - simpl. apply fin_endo_id.
    - unfold list_endo. fold list_endo.
      apply fin_endo_upd_map.
      exact IH.
  Qed.

  Section FinIsList.
    Variable f : A -> A.
    Hypothesis finH : fin_endo f.

    Local Definition list_graph (l : list A) : list (A * A) :=
      map (fun a => (a, f a)) l.

    Local Lemma list_endo_list_graph_cons a l a'
      : list_endo (list_graph (a :: l)) a' = upd_map (a, f a) (list_endo (list_graph l)) a'.
    Proof.
      reflexivity.
    Qed.

    Local Lemma ev_list_graph_off_dom l a
      : f a = a -> list_endo (list_graph l) a = a.
    Proof.
      intro eqH.
      induction l as [ | a' l IH ]; auto.
      rewrite list_endo_list_graph_cons.
      apply upd_map_elim.
      - intro aH; rewrite <- aH, eqH. exact eq_refl.
      - intro. exact IH.
    Qed.

    Lemma fin_endo_is_list_endo
      : exists l, forall a, f a = list_endo l a.
    Proof.
      unfold fin_endo in finH.
      unfold FiniteProj in finH.
      destruct finH as [ l fullH ]; clear finH.
      set (ul := map (dom_elt (f := f)) l).
      exists (list_graph ul).
      intro a.
      unfold FullProj in fullH.
      - case (decA (f a) a).
        + intro eqA; rewrite (ev_list_graph_off_dom ul eqA); tauto.
        + intro neH.
          specialize (fullH (exist _ a neH)).
          rename fullH into inProjH.
          induction l as [ | d l IH ]; try contradiction.
          simpl in inProjH.
          unfold ul. rewrite map_cons.
          rewrite list_endo_list_graph_cons.
          destruct (decA (dom_elt d) a) as [ deqH | dneH ].
          * rewrite deqH, upd_map_at; exact eq_refl.
          * simpl in IH.
            destruct inProjH; try contradiction.
            specialize (IH H); clear H.
            rewrite (upd_map_not_at _ _ (not_eq_sym dneH)).
            apply IH.
    Qed.
  End FinIsList.
End decA.
