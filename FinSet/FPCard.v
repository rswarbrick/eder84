(**

  This library is all about the cardinality of sets under projection.
  Specifically, if we have a map [p : A -> B] and know that
  [FiniteProj p], which says that the image of [p] as a subset of [B]
  is finite), then we can define a cardinality for that image. As with
  defining [FiniteProj], we don't talk about the cardinality of the
  whole set, rather we always talk about the image of the projection.

*)

Require Import Lists.List.
Require Import PeanoNat.
Require Import Bool.

Require Import Top.FinSet.ProjSet.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.Distinct.
Require Import Top.FinSet.InjList.
Require Import Top.FinSet.ZipNatMap.
Require Import Top.FinSet.ListFacts.

Set Implicit Arguments.

(** * Cardinality definition

    We are going to define cardinality in a way that isn't necessarily
    computable (but that doesn't require decidability for the
    image). When [B] is decidable, we'll find that there's a unique
    cardinality.
 *)
Definition fp_card {A B : Type} (p : A -> B) (n : nat) : Prop :=
  exists l, distinct (map p l) /\ FullProj p l /\ length l = n.

(**
   A finite projection always has a cardinality, providing that we
   have decidability downstairs. The proof is that you pick a listing
   that implies finiteness and remove elements that give duplicates
   under the projection. That second part needs a function.
 *)
Section rem_dups_below.
  Variables A B : Type.
  Variable p : A -> B.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Fixpoint rem_dups_below (s : list B) (l : list A) : list A :=
    match l with
    | nil => nil
    | a :: l' => if search _ decB (p a) s
                 then rem_dups_below s l'
                 else a :: rem_dups_below (p a :: s) l'
    end.

  Lemma seen_not_in_rem_dups_below b s l
    : In b s -> ~ In b (map p (rem_dups_below s l)).
  Proof.
    revert s; induction l as [ | a l IH ]; auto.
    intro s; unfold rem_dups_below; fold rem_dups_below.
    case_eq (search B decB (p a) s); auto.
    intros nsearchH inbH.
    rewrite map_cons.
    destruct 1 as [ <- | x ].
    - auto using
           (eq_true_false_abs (search B decB (p a) s)),
           (Is_true_eq_true _ (in_imp_search _ decB _ _ inbH)).
    - contradiction (IH (p a :: s) (in_cons (p a) b s inbH)).
  Qed.

  Lemma distinct_map_rem_dups_below s l
    : distinct (map p (rem_dups_below s l)).
  Proof.
    revert s; induction l as [ | a l IH ]; simpl; auto; intro s.
    case (search B decB (p a) s); auto.
    rewrite map_cons.
    apply distinct_cons_intro; auto.
    apply seen_not_in_rem_dups_below.
    apply in_eq.
  Qed.

  Lemma in_map_rem_dups_below b s l
    : In b (map p l) -> ~ In b s -> In b (map p (rem_dups_below s l)).
  Proof.
    revert s; induction l as [ | a l IH ]; auto.
    intro s.
    unfold rem_dups_below; fold rem_dups_below.
    case_eq (search B decB (p a) s);
      intros searchH inconsH.
    - destruct inconsH as [ <- | ]; auto; intro notinH.
      contradiction notinH.
      apply (search_imp_in _ decB).
      apply (Is_true_eq_left _ searchH).
    - rewrite map_cons.
      destruct (decB b (p a)) as [ <- | neH ]; intros notinH.
      + apply in_eq.
      + apply in_cons.
        destruct inconsH as [ <- | inH ]; try tauto.
        apply IH; auto.
        destruct 1; auto.
  Qed.
End rem_dups_below.

Lemma fp_card_exists
      {A B : Type} (p : A -> B)
      (decB : forall x y : B, {x = y} + {x <> y})
  : FiniteProj p -> exists n, fp_card p n.
Proof.
  destruct 1 as [ l fullH ].
  unfold fp_card.
  set (l' := rem_dups_below p decB nil l).
  exists (length l'), l'; intuition.
  - apply (distinct_map_rem_dups_below p decB nil l).
  - unfold FullProj in *.
    intro a; specialize (fullH a).
    unfold InProj in *.
    apply in_map_rem_dups_below; auto.
Qed.

(**
  If we have an injective map from one projection to the next, then a
  cardinality for the source must be at most any cardinality for the
  target.
*)
Section inj_map.
  Variables A B C D : Type.
  Variable p : A -> B.
  Variable q : C -> D.
  Variable f : nat_map p q.

  Lemma nat_map_gives_list_map l1 l2
    : FullProj q l2 ->
      is_list_map (nm_bot f) (map p l1) (map q l2).
  Proof.
    intro fullH.
    intros b.
    rewrite in_map_iff.
    destruct 1 as [ a aH ]; destruct aH as [ <- inH ].
    rewrite <- nat_map_nat.
    apply fullH.
  Qed.

  Hypothesis injH : inj_nat_map f.

  Lemma nm_bot_inj_on_list l1
    : inj_on_list (nm_bot f) (map p l1).
  Proof.
    unfold inj_on_list.
    intros b0 b1 inb0H inb1H.
    rewrite in_map_iff in inb0H;
      destruct inb0H as [ a0 aH ]; destruct aH as [ <- ina0H ].
    rewrite in_map_iff in inb1H;
      destruct inb1H as [ a1 aH ]; destruct aH as [ <- ina1H ].
    auto.
  Qed.

  Hypothesis decD : forall x y : D, {x = y} + {x <> y}.

  Lemma fp_card_inj_le n m
    : fp_card p n -> fp_card q m -> n <= m.
  Proof.
    unfold fp_card.
    destruct 1 as [ l1 H1 ].
    destruct H1 as [ dist1H H1 ].
    destruct H1 as [ full1H <- ].
    destruct 1 as [ l2 H2 ].
    destruct H2 as [ dist2H H2 ].
    destruct H2 as [ full2H <- ].
    enough (maplenH : length (map p l1) <= length (map q l2));
      try (rewrite map_length, map_length in maplenH; auto).
    apply (inj_on_list_length
             (map p l1) (map q l2) decD dist1H dist2H
             (nat_map_gives_list_map l1 full2H)
             (nm_bot_inj_on_list l1)).
  Qed.
End inj_map.

Section fp_card_unique.
  Variables A B : Type.
  Variable p : A -> B.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Local Lemma fp_card_le n m
    : fp_card p n -> fp_card p m -> n <= m.
  Proof.
    apply (fp_card_inj_le (f:=nat_map_v p));
      unfold inj_nat_map; auto.
  Qed.

  Lemma fp_card_unique n m
    : fp_card p n -> fp_card p m -> n = m.
  Proof.
    auto using fp_card_le, Nat.le_antisymm.
  Qed.

End fp_card_unique.

(*

  We want to show that an injective endomorphism on a finite set is in
  fact a bijection.

  How do we do this? Well, the first thing is to notice that this
  injection must also be surjective. We'll show a slightly stronger
  result: if two sets have the same cardinality, an injection from one
  to the other is a surjection. We have proved the "list form" of this
  in the InjList theory.

*)
Section inj_same_size.
  Variables A B C D : Type.
  Variable p : A -> B.
  Variable q : C -> D.
  Variable f : nat_map p q.

  Variable n : nat.
  Hypothesis cardpH : fp_card p n.
  Hypothesis cardqH : fp_card q n.

  Hypothesis injH : inj_nat_map f.

  Hypothesis decD : forall x y : D, {x = y} + {x <> y}.

  Lemma fp_inj_same_card_is_surj
    : SurjectiveProj f.
  Proof.
    destruct cardpH as [ lp H ];
      destruct H as [ distpH H ];
      destruct H as [ fullpH lenpH ].
    destruct cardqH as [ lq H ];
      destruct H as [ distqH H ];
      destruct H as [ fullqH lenqH ].
    assert (surjH : surj_on_list (nm_bot f) (map p lp) (map q lq)).
      try (apply (inj_on_eql_list_is_surj
                    (map p lp) (map q lq) decD distpH distqH
                    (nat_map_gives_list_map f lp fullqH)
                    (nm_bot_inj_on_list injH lp));
           rewrite !map_length; congruence).
    intros c.
    specialize (fullqH c).
    specialize (surjH (q c) fullqH).
    rewrite in_map_iff in surjH.
    destruct surjH as [ b bH ]; destruct bH as [ <- bH ].
    rewrite in_map_iff in bH.
    destruct bH as [ a aH ]; destruct aH as [ <- aH ].
    exists a; reflexivity.
  Qed.
End inj_same_size.

Section inj_endo.
  Variables A B : Type.
  Variable p : A -> B.
  Variable f : nat_map p p.
  Hypothesis injH : inj_nat_map f.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis finH : FiniteProj p.

  Lemma inj_endo_is_surj
    : SurjectiveProj f.
  Proof.
    destruct (fp_card_exists decB finH) as [ n cardH ].
    apply (fp_inj_same_card_is_surj cardH cardH injH decB).
  Qed.

  Variable a0 : A.

  Local Definition g {l} (fullH : FullProj p l) : nat_map p p :=
    surj_nat_map_right_inverse decB decB a0 inj_endo_is_surj fullH.

  Local Lemma g_is_right_inv
        {l} (fullH : FullProj p l)
    : forall a, nm_bot (nat_map_comp_h (g fullH) f) (p a) = p a.
  Proof.
    apply (surj_map_is_invertible decB decB a0 inj_endo_is_surj fullH).
  Qed.

  Local Lemma g_is_left_inv
        {l} (fullH : FullProj p l)
    : forall a, nm_bot (nat_map_comp_h f (g fullH)) (p a) = p a.
  Proof.
    intro a.
    unfold inj_nat_map in injH.
    pose proof (g_is_right_inv fullH (nm_top f a)) as gfH.
    rewrite nat_map_nat in gfH.
    rewrite <- nm_bot_comp_h in gfH.
    rewrite nm_comp_h_assoc_bot in gfH.
    rewrite nm_bot_comp_h in gfH.
    rewrite <- nat_map_nat in gfH.
    rewrite <- nat_map_nat.
    exact (injH _ _ gfH).
  Qed.

  Lemma inj_endo_is_invertible : exists h : nat_map p p, inv_bottom f h.
  Proof.
    destruct finH as [ l fullH ].
    exists (g fullH).
    constructor; auto using g_is_right_inv, g_is_left_inv.
  Qed.
End inj_endo.

Lemma proj1_combine_shorter (X Y : Type) (xs : list X) (ys : list Y)
  : length xs <= length ys -> map fst (combine xs ys) = xs.
Proof.
  revert ys; induction xs as [ | x xs IHx ]; auto; intro ys.
  destruct ys; simpl; intro lenH.
  - apply Le.le_n_0_eq in lenH; discriminate lenH.
  - rewrite (IHx ys (le_S_n _ _ lenH)); auto.
Qed.

(* Like combine, but repeats y as necessary to make up to the length of xs *)
Fixpoint combine_with_tail2
         (X Y : Type) (y' : Y) (xs : list X) (ys : list Y) {struct ys} :=
  match ys with
  | nil => map (fun x => (x, y')) xs
  | cons y ys =>
    match xs with
    | nil => nil
    | cons x xs => cons (x, y) (combine_with_tail2 y' xs ys)
    end
  end.

Lemma map_fst_combine_with_tail2
      (X Y : Type) (y' : Y) (xs : list X) (ys : list Y)
  : map fst (combine_with_tail2 y' xs ys) = xs.
Proof.
  revert xs; induction ys as [ | y ys IHy ]; intro xs.
  - simpl; rewrite map_map; induction xs; simpl; eauto using f_equal.
  - destruct xs; simpl; eauto using f_equal.
Qed.

Lemma initial_part_combine_with_tail2
      (X Y : Type) (y' : Y) (xs : list X) (ys : list Y)
  : take (min (length xs) (length ys)) (combine_with_tail2 y' xs ys) =
    take (min (length xs) (length ys)) (combine xs ys).
Proof.
  revert xs; induction ys as [ | y ys IHy ]; intro xs.
  - rewrite Nat.min_0_r; auto.
  - destruct xs; simpl; eauto using f_equal.
Qed.

Lemma take_initial_combine_with_tail2
      (X Y : Type) (y' : Y) n (xs : list X) (ys : list Y)
  : n <= min (length xs) (length ys) ->
    take n (combine_with_tail2 y' xs ys) = take n (combine xs ys).
Proof.
  revert n xs; induction ys as [ | y ys IH ]; intros n xs.
  - simpl; rewrite Nat.min_0_r, Nat.le_0_r.
    intro nH; rewrite nH; auto.
  - destruct xs; auto.
    destruct n; auto; simpl.
    rewrite <- Nat.succ_le_mono; intro nH.
    apply f_equal; auto.
Qed.

Lemma in_proj_take (A B : Type) (p : A -> B) n x xs
  : InProj p (p x) (take n xs) -> InProj p (p x) xs.
Proof.
  revert xs; induction n as [ | n IH ]; [ contradiction | ]; intro xs.
  destruct xs as [ | a xs ]; auto.
  simpl; destruct 1; unfold InProj; simpl; auto.
  right; apply IH; auto.
Qed.

Lemma take_full_proj (A B : Type) (p : A -> B) n xs
  : FullProj p (take n xs) -> FullProj p xs.
Proof.
  intros fullH x; apply (in_proj_take p n), fullH.
Qed.

Section inj_surj.
  (** * Injections and surjections between sets with cardinality

    Normal maths defines the cardinality of a set by talking about
    equivalence classes of surjections. We've done it slightly
    differently, restricting to finite sets and asking for a
    surjection from a list.

    This section will recover a little of the ordinary theory, showing
    that if you have set [B1] smaller than set [B2] then there is a
    surjection [B2 -> B1] and an injection [B1 -> B2].

   *)
  Variables A1 A2 B1 B2 : Type.
  Variable p1 : A1 -> B1.
  Variable p2 : A2 -> B2.

  Hypothesis decB1 : forall u v : B1, {u = v} + {u <> v}.
  Hypothesis decB2 : forall u v : B2, {u = v} + {u <> v}.

  Variables n1 n2 : nat.
  Hypothesis card1H : fp_card p1 n1.
  Hypothesis card2H : fp_card p2 n2.
  Hypothesis card_leH : n1 <= n2.

  Lemma inj_from_smaller_card (fb : B1 -> B2)
    : exists h : nat_map p1 p2, inj_nat_map h.
  Proof.
    destruct card1H as [ as1 [ dist1H [ full1H len1H ] ] ].
    destruct card2H as [ as2 [ dist2H [ full2H len2H ] ] ].
    clear card1H card2H.
    set (prs := combine as1 as2).
    assert (map fst prs = as1) as mapfstH;
      [ unfold prs; apply proj1_combine_shorter;
        rewrite len1H, len2H; auto | ].
    assert (FullProj p1 (map fst prs)) as fullmap1H;
      [ rewrite mapfstH; auto | ].
    exists (zip_nat_map p2 decB1 fb prs fullmap1H).
    apply zip_nat_map_inj_intro; auto.
    unfold pr_proj2; rewrite <- map_map.
    unfold prs; rewrite map_snd_combine, map_take.
    auto using distinct_take.
  Qed.

  Lemma surj_from_larger_card (fb : B2 -> B1) (a1 : A1)
    : exists h : nat_map p2 p1, SurjectiveProj h.
  Proof.
    destruct card1H as [ as1 [ dist1H [ full1H len1H ] ] ].
    destruct card2H as [ as2 [ dist2H [ full2H len2H ] ] ].
    clear card1H card2H.
    set (prs := combine_with_tail2 a1 as2 as1).
    assert (map fst prs = as2) as mapfstH;
      [ unfold prs; rewrite map_fst_combine_with_tail2; auto | ].
    assert (FullProj p2 (map fst prs)) as fullmap2H;
      [ rewrite mapfstH; auto | ].
    exists (zip_nat_map p1 decB2 fb prs fullmap2H).
    apply zip_nat_map_surj_intro.
    - unfold pr_proj1; rewrite <- map_map, mapfstH; auto.
    - apply (take_full_proj n1).
      assert (n1 <= min (length as2) (length as1)) as n1minH;
        [ rewrite len1H, len2H;
          apply (Nat.min_glb n2 n1 n1 card_leH (le_n n1)) | ].
      unfold prs.
      rewrite <- map_take.
      rewrite (take_initial_combine_with_tail2 a1 as2 as1 n1minH).
      rewrite map_take, map_snd_combine, take_take.
      rewrite len1H, len2H, (min_r _ _ card_leH), Nat.min_id, <- len1H.
      rewrite take_length.
      apply full1H.
  Qed.

End inj_surj.
