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
Section proj.
  Variables A B : Type.
  Variable p : A -> B.

  Definition is_card_list (l : list A) : Prop :=
    distinct (map p l) /\ FullProj p l.

  Definition fp_card_list : Type := sig is_card_list.

  Definition fp_card (cl : fp_card_list) : nat := length (proj1_sig cl).

  Lemma card_list_is_distinct (cl : fp_card_list)
    : distinct (map p (proj1_sig cl)).
  Proof.
    destruct cl as [ l [ distH fullH ] ]; auto.
  Qed.

  Lemma card_list_is_full (cl : fp_card_list)
    : FullProj p (proj1_sig cl).
  Proof.
    destruct cl as [ l [ distH fullH ] ]; auto.
  Qed.
End proj.

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
    - rewrite (in_imp_search _ decB _ _ inbH) in nsearchH.
      contradiction diff_true_false.
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
      eauto using search_imp_in.
    - rewrite map_cons.
      destruct (decB b (p a)) as [ <- | neH ]; intros notinH.
      + apply in_eq.
      + apply in_cons.
        destruct inconsH as [ <- | inH ]; try tauto.
        apply IH; auto.
        destruct 1; auto.
  Qed.
End rem_dups_below.

Section dec_fp_card_list.
  Variables A B : Type.
  Variable p : A -> B.
  Variable finH : FiniteProj p.

  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Local Definition dec_fp_card_list' : list A :=
    rem_dups_below p decB nil (proj1_sig finH).

  Local Lemma is_card_list_dec : is_card_list p dec_fp_card_list'.
  Proof.
    split.
    - apply distinct_map_rem_dups_below.
    - intro.
      apply in_map_rem_dups_below; auto.
      apply (proj2_sig finH).
  Qed.

  Definition dec_fp_card_list : fp_card_list p :=
    exist _ _ is_card_list_dec.
End dec_fp_card_list.

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

  Lemma fp_card_inj_le (clp : fp_card_list p) (clq : fp_card_list q)
    : fp_card clp <= fp_card clq.
  Proof.
    unfold fp_card.
    rewrite <- (map_length p), <- (map_length q).
    destruct (proj2_sig clp), (proj2_sig clq).
    eauto using inj_on_list_length, nat_map_gives_list_map, nm_bot_inj_on_list.
  Qed.
End inj_map.

Section fp_card_unique.
  Variables A B : Type.
  Variable p : A -> B.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.

  Local Lemma fp_card_le (cl cl' : fp_card_list p)
    : fp_card cl <= fp_card cl'.
  Proof.
    apply (fp_card_inj_le (f:=nat_map_v p));
      unfold inj_nat_map; auto.
  Qed.

  Lemma fp_card_unique (cl cl' : fp_card_list p)
    : fp_card cl = fp_card cl'.
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

  Variable cardp : fp_card_list p.
  Variable cardq : fp_card_list q.
  Hypothesis cardeqH : fp_card cardp = fp_card cardq.

  Hypothesis injH : inj_nat_map f.

  Hypothesis decD : forall x y : D, {x = y} + {x <> y}.

  Lemma fp_inj_same_card_is_surj
    : SurjectiveProj f.
  Proof.
    destruct cardp as [ lp H ];
      destruct H as [ distpH fullpH ].
    destruct cardq as [ lq H ];
      destruct H as [ distqH fullqH ].
    assert (surjH : surj_on_list (nm_bot f) (map p lp) (map q lq));
      [ apply (inj_on_eql_list_is_surj _ _ decD
                                       distpH distqH
                                       (nat_map_gives_list_map f lp fullqH)
                                       (nm_bot_inj_on_list injH lp));
        revert cardeqH; unfold fp_card; rewrite !map_length; auto | ].
    clear cardeqH; intros c.
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
    apply (fp_inj_same_card_is_surj (dec_fp_card_list finH decB)
                                    (dec_fp_card_list finH decB)
                                    eq_refl injH decB).
  Qed.

  Variable a0 : A.

  Definition inj_endo_inv {l} (fullH : FullProj p l) : nat_map p p :=
    surj_nat_map_right_inverse decB decB a0 inj_endo_is_surj fullH.

  Local Lemma inj_endo_inv_right
        {l} (fullH : FullProj p l)
    : forall a, nm_bot (nat_map_comp_h (inj_endo_inv fullH) f) (p a) = p a.
  Proof.
    apply (surj_map_is_invertible decB decB a0 inj_endo_is_surj fullH).
  Qed.

  Local Lemma inj_endo_inv_left
        {l} (fullH : FullProj p l)
    : forall a, nm_bot (nat_map_comp_h f (inj_endo_inv fullH)) (p a) = p a.
  Proof.
    intro a.
    unfold inj_nat_map in injH.
    pose proof (inj_endo_inv_right fullH (nm_top f a)) as gfH; revert gfH.
    rewrite nat_map_nat,
            <- nm_bot_comp_h, nm_comp_h_assoc_bot, nm_bot_comp_h,
            <- nat_map_nat.
    apply injH.
  Qed.

  Lemma inj_endo_is_invertible : inv_bottom f (inj_endo_inv (proj2_sig finH)).
  Proof.
    split; auto using inj_endo_inv_right, inj_endo_inv_left.
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

  Variable card1 : fp_card_list p1.
  Variable card2 : fp_card_list p2.
  Hypothesis card_leH : fp_card card1 <= fp_card card2.

  Local Definition zipped_list_12 : list (A1 * A2) :=
    combine (proj1_sig card1) (proj1_sig card2).

  Local Lemma zipped_list_12_fst_is_full
    : FullProj p1 (map fst zipped_list_12).
  Proof.
    unfold zipped_list_12; rewrite (proj1_combine_shorter _ _ card_leH).
    apply card_list_is_full.
  Qed.

  Definition inj_from_smaller (fb : B1 -> B2) : nat_map p1 p2 :=
    zip_nat_map p2 decB1 fb zipped_list_12 zipped_list_12_fst_is_full.

  Lemma inj_from_smaller_is_inj (fb : B1 -> B2)
    : inj_nat_map (inj_from_smaller fb).
  Proof.
    apply zip_nat_map_inj_intro; auto.
    unfold pr_proj2, zipped_list_12;
      rewrite <- map_map, map_snd_combine, map_take.
    auto using distinct_take, card_list_is_distinct.
  Qed.

  Local Definition zipped_list_21 a1 : list (A2 * A1) :=
    combine_with_tail2 a1 (proj1_sig card2) (proj1_sig card1).

  Local Lemma zipped_list_21_fst_is_full a1
    : FullProj p2 (map fst (zipped_list_21 a1)).
  Proof.
    unfold zipped_list_21; rewrite map_fst_combine_with_tail2.
    apply card_list_is_full.
  Qed.

  Definition surj_from_larger fb a1 : nat_map p2 p1 :=
    zip_nat_map p1 decB2 fb
                (zipped_list_21 a1) (zipped_list_21_fst_is_full a1).

  Lemma surj_from_larger_is_surj (fb : B2 -> B1) (a1 : A1)
    : SurjectiveProj (surj_from_larger fb a1).
  Proof.
    apply zip_nat_map_surj_intro.
    - unfold zipped_list_21, pr_proj1;
        rewrite <- map_map, map_fst_combine_with_tail2.
      auto using card_list_is_distinct.
    - apply (take_full_proj (fp_card card1)).
      assert (fp_card card1 <= min (fp_card card2) (fp_card card1)) as n1minH;
        [ apply (Nat.min_glb _ _ _ card_leH (le_n _)) | ].
      rewrite <- map_take.
      unfold zipped_list_21;
        rewrite (take_initial_combine_with_tail2 a1 _ _ n1minH).
      rewrite map_take, map_snd_combine, take_take.
      unfold fp_card in card_leH.
      rewrite (min_r _ _ card_leH), Nat.min_id, take_length.
      auto using card_list_is_full.
  Qed.

End inj_surj.
