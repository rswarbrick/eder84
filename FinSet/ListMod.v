(** A finite endomorphism, as defined in the [SymbComp.FinMod]
    library, is exactly the same thing as an endomorphism that can be
    described by a list of successive updates ("send [a] to [b]")
    applied to the identity map. In this theory, we prove this fact.
*)

Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.FinMod.


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

        At this point, we fix some map [f : A -> B] which is a finite
        modification of some other map [i : A -> B]. We want to prove
        that updating it with a pair doesn't stop it being a finite
        mo. To do so, we try to define a map from [mod_dom i f + unit] to
        [mod_dom i (upd_map p f)] which will induce the surjection in the
        underlying sets. The idea is that the image of [tt] in [unit]
        is [fst p], together with a proof that it's in the domain. Of
        course, it might be that [fst p = snd p], in which case it's
        not in the domain. To deal with this, we actually map to
        [option (mod_dom i (upd_map p f))] and allow ourselves to map to
        [None] in that case.

     *)

    Variable B : Type.
    Variable f : A -> B.
    Variable i : A -> B.
    Variable p : A * B.

    Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

    Local Definition map_a (a : A) : option (mod_dom i (upd_map p f)) :=
      match decB (upd_map p f a) (i a) with
      | left eqH => None
      | right neqH => Some (exist _ a neqH)
      end.

    Local Definition proj0 (x : mod_dom i f + unit) : A :=
      match x with
      | inl x => md_elt x
      | inr tt => fst p
      end.

    Local Definition proj1 : mod_dom i (upd_map p f) -> A :=
      md_elt (f := upd_map p f).

    Local Definition top_map (x : mod_dom i f + unit)
      : option (mod_dom i (upd_map p f)) :=
      match x with
      | inl (exist _ a H) => map_a a
      | inr tt => map_a (fst p)
      end.

    Local Definition bot_map (a : A) : option A := option_map proj1 (map_a a).

    Local Lemma nat_left : is_nat_map (md_elt (f:=f)) proj0 (inl, id).
    Proof.
      unfold is_nat_map; intro a; auto.
    Qed.

    Local Lemma finite_proj0 : fin_mod i f -> FiniteProj proj0.
    Proof.
      unfold FiniteProj.
      destruct 1 as [ l H ].
      exists (cons (inr tt) (map inl l)).
      unfold FullProj. intro x.
      destruct x as [ d | ].
      - apply in_proj_cons.
        unfold proj0 at 2.
        unfold FullProj in H. specialize (H d).
        apply (in_proj_map (exist (is_nat_map (md_elt (f := f)) proj0)
                                  (inl, id) nat_left)).
        apply H.
      - apply in_proj_eq; destruct u; reflexivity.
    Qed.

    Local Lemma natH x : option_map proj1 (top_map x) = bot_map (proj0 x).
    Proof.
      unfold bot_map; apply f_equal.
      destruct x as [ d | u ].
      - destruct d; auto.
      - destruct u; auto.
    Qed.

    Ltac dec_equal :=
      unfold map_a;
      repeat (match goal with
              | [ |- context [decA ?X ?Y]] =>
                case (decA X Y)
              | [ |- context [decB ?X ?Y]] =>
                case (decB X Y)
              | _ => reflexivity
              | _ => contradiction
              end).

    Local Lemma surjH (d' : mod_dom i (upd_map p f))
      : exists a : mod_dom i f + unit,
        bot_map (proj0 a) = Some (proj1 d').
    Proof.
      destruct d' as [ a H ]; unfold mod_elt in H; simpl.
      case (decA (fst p) a).
      - intro fstH.
        exists (inr tt).
        simpl. unfold bot_map, map_a.
        case (decB (upd_map p f (fst p)) (i (fst p))).
        + rewrite <- fstH in H. contradiction.
        + simpl. rewrite fstH. tauto.
      - intro rstH.
        assert (not_H_a: a <> fst p); auto.
        assert (IH: upd_map p f a = f a);
          unfold upd_map; dec_equal.
        assert (aH: mod_elt i f a);
          unfold mod_elt in H; unfold mod_elt. rewrite <- IH; auto.
        exists (inl (exist _ a aH)).
        unfold bot_map; dec_equal.
    Qed.

    (**

        We can finally prove the lemma that we wanted. Note that we
        use the [finite_surj_option] lemma from the FinMod library.
        This avoids some of the faffing around with option types that
        we'd need otherwise.

     *)
    Lemma fin_mod_upd_map
      : fin_mod i f -> fin_mod i (upd_map p f).
    Proof.
      intro feH.
      unfold fin_endo.
      apply (finite_surj_option proj1 top_map bot_map (finite_proj0 feH)).
      - exact natH.
      - exact surjH.
    Qed.
  End UpdMap.

  (** * List maps

      With the results of the previous section, it now just takes a
      quick induction to define the function described by a list of
      pairs and to see that it is a finite modification of the
      underlying map.
   *)
  Section ListMap.
    Variable B : Type.
    Variable i : A -> B.
    Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

    Fixpoint list_map (l : list (A * B)) : A -> B :=
      match l with
      | nil => i
      | cons p l => upd_map p (list_map l)
      end.

    Lemma list_map_nil : list_map nil = i.
    Proof. reflexivity. Qed.

    Lemma list_map_cons p l : list_map (cons p l) = upd_map p (list_map l).
    Proof. reflexivity. Qed.

    Lemma fin_mod_list_map l : fin_mod i (list_map l).
    Proof.
      induction l as [ | pr l IH ].
      - simpl. apply fin_mod_i.
      - unfold list_map. fold list_map.
        apply (fin_mod_upd_map); tauto.
    Qed.

    Lemma list_map_app_in l1 l2 a
      : In a (map fst l1) -> list_map (l1 ++ l2) a = list_map l1 a.
    Proof.
      induction l1 as [ | p l1 IH ]; try contradiction.
      destruct p as [ pa pb ]; simpl.
      destruct (decA pa a) as [ -> | neH ].
      - rewrite ! upd_map_at; auto.
      - destruct 1 as [ | inH ]; try contradiction.
        specialize (IH inH); clear inH.
        rewrite ! upd_map_not_at; auto.
    Qed.

    Lemma list_map_app_not_in l1 l2 a
      : ~ In a (map fst l1) -> list_map (l1 ++ l2) a = list_map l2 a.
    Proof.
      induction l1 as [ | p l1 IH ]; auto.
      destruct p as [ pa pb ]; simpl.
      destruct (decA pa a) as [ -> | neH ]; try tauto.
      rewrite ! upd_map_not_at; auto.
    Qed.

    Section FinIsList.
      Variable f : A -> B.
      Hypothesis finH : fin_mod i f.

      Local Definition list_graph (l : list A) : list (A * B) :=
        map (fun a => (a, f a)) l.

      Local Lemma list_map_list_graph_cons a l a'
        : list_map (list_graph (a :: l)) a' =
          upd_map (a, f a) (list_map (list_graph l)) a'.
      Proof.
        reflexivity.
      Qed.

      Local Lemma ev_list_graph_off_dom l a
        : f a = i a -> list_map (list_graph l) a = i a.
      Proof.
        intro eqH.
        induction l as [ | a' l IH ]; auto.
        rewrite list_map_list_graph_cons.
        apply upd_map_elim.
        - intro aH; rewrite <- aH, eqH. exact eq_refl.
        - intro. exact IH.
      Qed.

      Local Lemma fm_graph_is_list_map (l : list (mod_dom i f))
        : FullProj (md_elt (f := f)) l ->
          forall a,
            f a = list_map (list_graph (map (md_elt (f := f)) l)) a.
      Proof.
        unfold FullProj; intros fullH a.
        set (ul := map (md_elt (f := f)) l).
        case (decB (f a) (i a)).
        + intro eqA; rewrite (ev_list_graph_off_dom ul eqA); tauto.
        + intro neH.
          specialize (fullH (exist _ a neH)).
          rename fullH into inProjH.
          induction l as [ | d l IH ]; try contradiction.
          simpl in inProjH.
          unfold ul. rewrite map_cons.
          rewrite list_map_list_graph_cons.
          destruct (decA (md_elt d) a) as [ deqH | dneH ].
          * rewrite deqH, upd_map_at; exact eq_refl.
          * simpl in IH.
            destruct inProjH; try contradiction.
            specialize (IH H); clear H.
            rewrite (upd_map_not_at _ _ (not_eq_sym dneH)).
            apply IH.
      Qed.

      Local Lemma in_md_elt_graph_imp_neq p (l : list (mod_dom i f))
        : In p (list_graph (map (md_elt (f := f)) l)) ->
          f (fst p) <> i (fst p).
      Proof.
        induction l as [ | md l IH ]; try contradiction.
        revert IH.
        unfold list_graph.
        rewrite !map_map, map_cons.
        intro IH.
        destruct 1 as [ <- | inH ]; auto.
        unfold md_elt; apply proj2_sig.
      Qed.

      Lemma fin_mod_is_list_map
        : exists l,
          (forall a, f a = list_map l a) /\
          (forall p, In p l -> f (fst p) <> i (fst p)).
      Proof.
        unfold fin_endo in finH.
        unfold FiniteProj in finH.
        destruct finH as [ l fullH ]; clear finH.
        exists (list_graph (map (md_elt (f := f)) l)).
        eauto using fm_graph_is_list_map, in_md_elt_graph_imp_neq.
      Qed.
    End FinIsList.
  End ListMap.
End decA.
