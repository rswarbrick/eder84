Require Import List.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.ProjSet.

Section split_map.
  Variables A B : Type.
  Variable P : A -> Prop.
  Variable decP : forall a, {P a} + {~ P a}.
  Variable f1 : { a : A | P a } -> B.
  Variable f2 : { a : A | ~ P a } -> B.

  Definition split_map a :=
    match decP a with
    | left pH => f1 (exist _ a pH)
    | right qH => f2 (exist _ a qH)
    end.

  Lemma inj_split
        (inj1H : forall x x', f1 x = f1 x' -> proj1_sig x = proj1_sig x')
        (inj2H : forall y y', f2 y = f2 y' -> proj1_sig y = proj1_sig y')
        (disjH : forall x y, f1 x <> f2 y)
    : forall a a', split_map a = split_map a' -> a = a'.
  Proof.
    intros a a'; unfold split_map.
    destruct (decP a);
      destruct (decP a'); intro H;
        [ apply (inj1H _ _ H)
        | contradiction (disjH _ _ H)
        | contradiction (disjH _ _ (sym_eq H))
        | apply (inj2H _ _ H)
        ].
  Qed.

  (** If [f1] and [f2] are both "finite" modifications of some [f], we
      want to show that the split map is too. This is a little fiddly,
      because neither is exactly a [fin_mod] of some map (the problem
      is that the sigma type that's the domain of each map could have
      infinitely many proofs of [P a] or [~ P a] for some [a]).

      So we "unfold" [fin_mod] a bit and ask for a finite projection
      from the domain of the maps down to [A].
   *)
  Section fin_split.
    Variable f : A -> B.

    Definition fP : { a : A | P a } -> B := fun x => f (proj1_sig x).
    Definition fQ : { a : A | ~ P a } -> B := fun x => f (proj1_sig x).

    Hypothesis irrel1H : forall a pH pH', f1 (exist _ a pH) = f1 (exist _ a pH').
    Hypothesis irrel2H : forall a qH qH', f2 (exist _ a qH) = f2 (exist _ a qH').

    Variable fin1H : FiniteProj (fun (x : mod_dom fP f1) =>
                                   (proj1_sig (md_elt x))).
    Variable fin2H : FiniteProj (fun (x : mod_dom fQ f2) =>
                                   (proj1_sig (md_elt x))).

    Local Lemma mod_elt_split_map_intro_P x
      : mod_elt fP f1 x -> mod_elt f split_map (proj1_sig x).
    Proof.
      intro neH.
      destruct x as [ a pH ]; simpl.
      unfold mod_elt, split_map.
      destruct (decP a) as [ pH' | ]; auto.
      rewrite (irrel1H a pH' pH); auto.
    Qed.

    Local Lemma mod_elt_split_map_intro_Q x
      : mod_elt fQ f2 x -> mod_elt f split_map (proj1_sig x).
    Proof.
      intro neH.
      destruct x as [ a qH ]; simpl.
      unfold mod_elt, split_map.
      destruct (decP a) as [ | qH' ]; auto.
      rewrite (irrel2H a qH' qH); auto.
    Qed.

    Local Lemma mod_elt_split_map_elim_P x
      : mod_elt f split_map (proj1_sig x) -> mod_elt fP f1 x.
    Proof.
      unfold mod_elt, split_map, fP.
      destruct x as [ a pH ]; simpl.
      destruct (decP a) as [ pH' | ]; auto.
      rewrite (irrel1H a pH' pH).
      auto.
    Qed.

    Local Lemma mod_elt_split_map_elim_Q x
      : mod_elt f split_map (proj1_sig x) -> mod_elt fQ f2 x.
    Proof.
      unfold mod_elt, split_map, fQ.
      destruct x as [ a qH ]; simpl.
      destruct (decP a) as [ | qH' ]; auto.
      rewrite (irrel2H a qH' qH).
      auto.
    Qed.

    Local Definition mod_dom_map_1 : mod_dom fP f1 -> mod_dom f split_map :=
      fun d =>
        match d with
        | exist _ x neH => exist _ _ (mod_elt_split_map_intro_P x neH)
        end.

    Local Definition mod_dom_map_2 : mod_dom fQ f2 -> mod_dom f split_map :=
      fun d =>
        match d with
        | exist _ x neH => exist _ _ (mod_elt_split_map_intro_Q x neH)
        end.

    Local Definition fin_split_list : list (mod_dom f split_map) :=
      app (map mod_dom_map_1 (proj1_sig fin1H))
          (map mod_dom_map_2 (proj1_sig fin2H)).

    Local Lemma mdm_nat_1 d
      : proj1_sig (mod_dom_map_1 d) = proj1_sig (md_elt d).
    Proof.
      destruct d; auto.
    Qed.

    Local Lemma mdm_nat_2 d
      : proj1_sig (mod_dom_map_2 d) = proj1_sig (md_elt d).
    Proof.
      destruct d; auto.
    Qed.

    Local Definition mdm_nm_1
      : nat_map (fun d : mod_dom fP f1 => proj1_sig (md_elt d))
                (fun d : mod_dom f split_map => proj1_sig d) :=
      exist _ (mod_dom_map_1, id) mdm_nat_1.

    Local Definition mdm_nm_2
      : nat_map (fun d : mod_dom fQ f2 => proj1_sig (md_elt d))
                (fun d : mod_dom f split_map => proj1_sig d) :=
      exist _ (mod_dom_map_2, id) mdm_nat_2.

    Local Lemma fin_split_list_full : FullProj md_elt fin_split_list.
    Proof.
      intros [ a neH ]; simpl.
      apply in_proj_or_app.
      destruct (decP a) as [ pH | qH ].
      - left.
        destruct fin1H as [ l1 full1H ]; simpl.
        apply (in_proj_map mdm_nm_1 a l1).
        apply (full1H (exist _ _ (mod_elt_split_map_elim_P
                                    (exist _ a pH) neH))).
      - right.
        destruct fin2H as [ l2 full2H ]; simpl.
        apply (in_proj_map mdm_nm_2 a l2).
        apply (full2H (exist _ _ (mod_elt_split_map_elim_Q
                                    (exist _ a qH) neH))).
    Qed.

    Definition fin_split : fin_mod f split_map :=
      exist _ fin_split_list fin_split_list_full.
  End fin_split.
End split_map.
