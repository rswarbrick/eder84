Require Import Lists.List.
Require Import Coq.Arith.PeanoNat.

Require Import SymbComp.Distinct.
Require Import SymbComp.Remove.

(**

  * Injections between lists

 *)
Section lists.
  Variables A B : Type.
  Variable f : A -> B.
  Variable aa : list A.

  Definition inj_on_list : Prop :=
    forall a a', In a aa -> In a' aa -> f a = f a' -> a = a'.

  Variable bb : list B.

  Definition is_list_map : Prop :=
    forall a, In a aa -> In (f a) bb.

  Definition surj_on_list : Prop :=
    forall b, In b bb -> In b (map f aa).

End lists.

Arguments inj_on_list {A B} f aa.
Arguments is_list_map {A B} f aa bb.
Arguments surj_on_list {A B} f aa bb.

Lemma inj_on_list_uncons {A B : Type} {f : A -> B} {a aa}
  : inj_on_list f (a :: aa) -> inj_on_list f aa.
Proof.
  unfold inj_on_list; auto with datatypes.
Qed.

Lemma is_list_map_uncons {A B : Type} {f : A -> B} {a aa bb}
      (decB : forall x y : B, {x = y} + {x <> y})
  : is_list_map f (a :: aa) bb ->
    ~ In a aa ->
    inj_on_list f (a :: aa) ->
    is_list_map f aa (remove decB (f a) bb).
Proof.
  unfold is_list_map.
  intros lmH notH injH a' inH.
  apply in_remove; auto with datatypes.
  unfold inj_on_list in injH.
  intro feqH.
  rewrite (injH a' a (in_cons a a' aa inH) (in_eq a aa) feqH) in inH.
  contradiction.
Qed.

Lemma list_map_cons_first_in_tgt {A B : Type} {f : A -> B} {a aa bb}
  : is_list_map f (a :: aa) bb -> In (f a) bb.
Proof.
  auto using (in_eq  a aa).
Qed.

Lemma distinct_inj_induct
      {A B : Type} {f : A -> B} {aa bb}
      (decB : forall x y : B, {x = y} + {x <> y})
      P
  : (forall bb, P nil bb) ->
    (forall a aa bb, distinct aa ->
                     distinct bb ->
                     ~ In a aa ->
                     is_list_map f (a :: aa) bb ->
                     P aa (remove decB (f a) bb) ->
                     P (a :: aa) bb) ->
    distinct aa ->
    distinct bb ->
    is_list_map f aa bb ->
    inj_on_list f aa ->
    P aa bb.
Proof.
  intros nilH stepH; revert bb.
  induction aa as [ | a aa IH ]; auto.
  intros bb distaH distbH lmH injH.
  destruct distaH as [ norepaH distaH ].
  specialize (IH (remove decB (f a) bb) distaH
                 (distinct_remove decB (f a) distbH)
                 (is_list_map_uncons decB lmH norepaH injH)
                 (inj_on_list_uncons injH)).
  auto.
Qed.

Lemma inj_on_list_length
      {A B : Type} {f : A -> B} (aa : list A) (bb : list B)
      (decB : forall x y : B, {x = y} + {x <> y})
  : distinct aa ->
    distinct bb ->
    is_list_map f aa bb ->
    inj_on_list f aa ->
    length aa <= length bb.
Proof.
  apply (distinct_inj_induct decB (fun aa bb => length aa <= length bb));
    auto using le_0_n.
  clear aa bb; intros a aa bb distaH distbH norepaH lmH lenH.
  rewrite (length_distinct_remove_in
             decB distbH (list_map_cons_first_in_tgt lmH)).
  simpl; auto using le_n_S.
Qed.

Lemma surj_on_list_nil {A B : Type} (f : A -> B) (l : list A)
  : surj_on_list f l nil.
Proof.
  unfold surj_on_list; intros; contradiction.
Qed.

(*

  Now we want to show how to get a surjection from an injection. If I
  have an injective map between two equal length lists (with no
  duplicates) then it follows that the map is actually surjective.

*)
Lemma inj_on_eql_list_is_surj
      {A B : Type} {f : A -> B}
      (aa : list A) (bb : list B)
      (decB : forall x y : B, {x = y} + {x <> y})
  : distinct aa -> distinct bb ->
    is_list_map f aa bb ->
    inj_on_list f aa ->
    length aa = length bb ->
    surj_on_list f aa bb.
Proof.
  apply (distinct_inj_induct
           decB
           (fun aa bb => length aa = length bb -> surj_on_list f aa bb));
    clear aa bb.
  - intros bb lenH.
    enough (bbH : bb = nil); try (rewrite bbH; auto using surj_on_list_nil).
    apply length_zero_iff_nil; auto.
  - intros a aa bb distaH distbH norepaH lmH stepH lenH.
    rewrite (length_distinct_remove_in
               decB distbH (list_map_cons_first_in_tgt lmH)) in lenH.
    simpl in lenH.
    specialize (stepH (eq_add_S _ _ lenH)); clear lenH.
    intros b inH; unfold surj_on_list in stepH; specialize (stepH b).
    rewrite map_cons.
    destruct (decB b (f a)) as [ -> | neH ].
    + apply in_eq.
    + apply in_cons; apply stepH.
      apply (in_remove decB inH neH).
Qed.
