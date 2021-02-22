Require Import Compare_dec.
Require Import FinFun.
Require Import Lists.List.
Require Import Lt.
Require Import PeanoNat.
Require Import Wf_nat.

Require Import Top.FinSet.Distinct.
Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.
Require Import Top.FinSet.Remove.
Require Import Top.FinSet.ListFacts.

Ltac split_conj :=
  repeat match goal with
         | [ |- ?H /\ ?H' ] => split
         end.

Fixpoint ne_tail {X : Type} (x : X) (xs : list X) : X :=
  match xs with
  | nil => x
  | x' :: xs' => ne_tail x' xs'
  end.

Lemma nth_error_ne_tail {X} (x : X) (xs : list X)
  : nth_error (x :: xs) (length xs) = Some (ne_tail x xs).
Proof.
  revert x; induction xs as [ | x' xs IH ]; simpl; auto.
Qed.

Lemma in_ne_tail {X} (x : X) (xs : list X)
  : In (ne_tail x xs) (x :: xs).
Proof.
  revert x; induction xs as [ | x' xs IH ]; [ simpl; auto | ].
  intro x; apply in_cons; cbn [ne_tail]; auto.
Qed.

Lemma ne_tail_irrel {X : Type} (x x' : X) (xs : list X)
  : xs <> nil ->
    ne_tail x xs = ne_tail x' xs.
Proof.
  induction xs; tauto.
Qed.

Definition ne_cons {X : Type} (x : X) (xs : X * list X) : X * list X :=
  (x, fst xs :: snd xs).

Lemma list_map_cons_dec
      {A B : Type} (decA : forall a a' : A, {a = a'} + {a <> a'})
      (i : A -> B) {a a'} b l
  : list_map decA i ((a, b) :: l) a' =
    if decA a' a then b else list_map decA i l a'.
Proof.
  simpl; unfold upd_map; auto.
Qed.

Ltac lmc_simpl := rewrite !list_map_cons_dec; simpl.

Lemma distinct_in_under
      {A B : Type} (decB : forall b b' : B, {b = b'} + {b <> b'})
      {f : A -> B} {la : list A} {lb : list B}
  : distinct lb ->
    (forall b, In b lb -> in_under f b la) ->
    length lb <= length la.
Proof.
  intros distH inH.
  revert la inH; induction lb as [ | b lb IH ];
    intros la inH;
    [ simpl; auto using le_0_n | ].
  destruct distH as [ ninH distH ].
  simpl; apply lt_le_S.
  set (la' := remove_under decB f b la).
  apply (Nat.le_lt_trans (length lb) (length la')).
  - apply (IH distH la').
    intros b' in'H.
    apply (in_under_remove decB f (inH b' (in_cons b b' lb in'H))).
    intros eqH; rewrite eqH in in'H; contradiction ninH.
  - apply (length_remove_under_in decB).
    apply (inH b (in_eq b lb)).
Qed.

(**

  This theory is all about finite injections. That is, finite modifications of
  an injection that are still injections. We prove a sort of induction
  principle, showing that any such an injection can be thought of as a one- or
  two-element update from another smaller one.

  Let [f] be a finite modification of [i], with both of them injections where
  some proposition [P] holds. Suppose that I want to "reset" some [a0] which is
  currently mapped by [f] to something other than [i a0]. Maybe I can just
  start sending it to [i a0]? Unfortunately, the resulting map won't
  necessarily be injective. We know that no [a1 != a0] has [i a1 = i a0]
  (because [i] is injective), but maybe there's some [a1] in the list with [f
  a1 = i a0]. If so, this element is unique by injectivity of [f].

  However, if there is such an element, we can repeat the search. (Is there an
  [a2] with [f a2 = i a1]?). Suppose we keep doing this and eventually find
  some [aN] where [f] maps nothing to [i aN]. If that happens, we can update
  [f] to send [aN] to [i aN] and we've found a smaller injection.

  What else can happen? Well, we can get a cycle where eventually the pre-image
  of [aN] is something we've seen before. In fact, this pre-image will actually
  be [a0]. But then we can modify the map by sending [a1] to [i aN] (instead of
  [i a0]) and sending [a0] to [i a0]. This "snips" [a0] out of the cycle.

  Since we know that the preimages we find are distinct and all in the (finite)
  [mod_dom] of [f], we must eventually find a no preimage or find a cycle, as
  described above.

*)
Section find_under.
  Variables A B : Type.
  Hypothesis decB : forall b b' : B, {b = b'} + {b <> b'}.
  Variable f : A -> B.

  Fixpoint find_under (b : B) (l : list A) : option A :=
    match l with
    | nil => None
    | a :: tl => if decB b (f a) then Some a else find_under b tl
    end.

  Lemma find_under_some a b l
    : find_under b l = Some a -> in_under f b l /\ f a = b.
  Proof.
    induction l as [ | a' l IH ]; [ inversion 1 | ].
    simpl; destruct (decB b (f a')) as [ -> | neH ].
    - injection 1; intros ->; auto.
    - intro findH; destruct (IH findH); auto.
  Qed.

  Lemma find_under_some' a b l
    : find_under b l = Some a -> In a l.
  Proof.
    induction l as [ | a' l IH ]; [ inversion 1 | ].
    simpl; destruct (decB b (f a')) as [ -> | neH ]; auto.
    injection 1; auto.
  Qed.

  Lemma find_under_none b l
    : find_under b l = None -> forall a, In a l -> f a <> b.
  Proof.
    induction l as [ | a l IH ]; auto.
    cbn [find_under]; destruct (decB b (f a)); [ inversion 1 | ].
    intros noneH x; specialize (IH noneH x); clear noneH.
    destruct 1 as [ <- | ]; auto.
  Qed.

  Lemma find_under_rem_dups'
        (C : Type) (decC : forall c c' : C, {c = c'} + {c <> c'})
        (g : A -> C) b seen l
    : (forall a a', g a = g a' -> f a = f a') ->
      (forall a, f a = b -> ~ In (g a) seen) ->
      find_under b l =
      find_under b (rem_dups_under g decC seen l).
  Proof.
    intros gfH.
    revert seen; induction l as [ | a l IH ]; auto.
    intros seen unseenH; simpl.
    destruct (decB b (f a)) as [ -> | neH ].
    - rewrite (if_search_false C decC _ _ (unseenH a (eq_refl _))).
      simpl; destruct (decB _ _); tauto.
    - case_eq (search C decC (g a) seen); auto.
      intro searchFalseH.
      simpl; destruct (decB _ _) as [ | _ ]; try tauto.
      apply IH.
      intros x fxH inH.
      destruct inH as [ geqH | ]; [ | contradiction (unseenH x fxH) ].
      contradiction neH; rewrite <- fxH; apply (gfH x a); auto.
  Qed.

  Lemma find_under_rem_dups
        (C : Type) (decC : forall c c' : C, {c = c'} + {c <> c'})
        (g : A -> C) b l
    : (forall a a', g a = g a' -> f a = f a') ->
      find_under b l =
      find_under b (rem_dups_under g decC nil l).
  Proof.
    intro gfH.
    apply (find_under_rem_dups' C decC g b nil l gfH).
    intros a faH innilH; inversion innilH.
  Qed.

End find_under.

Arguments find_under {A B} decB f b l.
Arguments find_under_some {A B decB f a b l} someH.
Arguments find_under_some' {A B decB f a b l} someH.
Arguments find_under_none {A B decB f b l} noneH.
Arguments find_under_rem_dups' {A B decB f C} decC {g b seen} l gfH.
Arguments find_under_rem_dups {A B decB f C} decC {g b} l gfH.

Definition inj_on {A B : Type} (P : A -> Prop) (f : A -> B) :=
  forall a1 a2, P a1 -> P a2 -> f a1 = f a2 -> a1 = a2.

Section maps.
  Variables A B : Type.
  Hypothesis decA : forall a a' : A, {a = a'} + {a <> a'}.
  Hypothesis decB : forall b b' : B, {b = b'} + {b <> b'}.
  Variable P : A -> Prop.
  Variable i : A -> B.

  Section lmp.
    Variable l : list (A * B).

    Local Definition f := list_map decA i l.

    (** If not None, [list_map_preimage b] is a value, [a] which is mapped to [b]
      by [f] because of a pair [(a, b)] in the list (not just because [b = i
      a]).

      Note that we start with a call to [rem_dups_under] to avoid problems with
      lists like [(a, b0) :: (a, b1) :: l]. *)

    Definition list_map_preimage (b : B) : option A :=
      option_map fst (find_under decB snd b (rem_dups_under fst decA nil l)).

    Lemma in_under_find_under_some {b a b'} {dl : list (A * B)}
      : find_under decB snd b dl = Some (a, b') ->
        in_under fst a dl.
    Proof.
      eauto using in_under_preimage, find_under_some'.
    Qed.

    Lemma lmp_some_elim {a b}
      : list_map_preimage b = Some a -> f a = b.
    Proof.
      unfold list_map_preimage, f.
      rewrite list_map_rem_dups.
      pose proof (distinct_under_rem_dups fst decA nil l) as H; revert H.
      generalize (rem_dups_under fst decA nil l) as dl; intro dl.
      induction dl as [ | [ u v ] dl IH ]; [ inversion 2 | ].
      destruct 1 as [ uuniqH distinctH ].
      lmc_simpl.
      destruct (decB b v) as [ <- | bvneH ]; simpl.
      - injection 1; destruct (decA a u) as [ | neH ]; auto.
        intros; contradiction neH; auto.
      - intro findH.
        destruct (decA a u) as [ <- | ]; auto.
        contradiction uuniqH; simpl; clear uuniqH IH.
        case_eq (find_under decB snd b dl);
          [ | intro fuH; revert findH; rewrite fuH; inversion 1 ].
        intros [ aa bb ] fuH.
        revert findH; rewrite fuH; simpl; injection 1 as ->.
        eauto using in_under_find_under_some.
    Qed.

    Lemma lmp_some_in {a b}
      : list_map_preimage b = Some a -> in_under fst a l.
    Proof.
      unfold list_map_preimage.
      case_eq (find_under decB snd b (rem_dups_under fst decA nil l));
        [ | inversion 2 ].
      intros [ a' b' ] someH; injection 1 as ->.
      pose proof (in_under_find_under_some someH) as inH.
      rewrite <- (in_under_rem_dups_iff fst decA a l nil) in inH.
      destruct inH; auto.
    Qed.

    Lemma lmp_none_elim a {b}
      : list_map_preimage b = None ->
        f a = b ->
        f a = i a.
    Proof.
      unfold list_map_preimage, f.
      rewrite list_map_rem_dups.
      pose proof (distinct_under_rem_dups fst decA nil l) as H; revert H.
      generalize (rem_dups_under fst decA nil l) as dl; intro dl.
      induction dl as [ | [ u v ] dl IH ]; auto.
      destruct 1 as [ uuniqH distinctH ].
      lmc_simpl; destruct (decB b v) as [ | bvneH ]; [ inversion 1 | ].
      intros noneH.
      specialize (IH distinctH noneH); clear distinctH noneH.
      destruct (decA a u); auto.
      intros; contradiction bvneH; auto.
    Qed.
  End lmp.

  Ltac f_cons_simpl := unfold f; lmc_simpl.

  Lemma list_map_remove_under l a u
    : list_map decA i (remove_under decA fst a l) u =
      if decA u a then i a else list_map decA i l u.
  Proof.
    induction l as [ | [ x y ] l IH ].
    - destruct (decA u a) as [ -> | ]; auto.
    - lmc_simpl.
      destruct (decA a x) as [ <- | axneH ].
      + rewrite IH; destruct (decA u a); auto.
      + lmc_simpl.
        destruct (decA u x) as [ <- | ]; auto.
        destruct (decA u a) as [ -> | ]; tauto.
  Qed.

  Hypothesis injiH : inj_on P i.

  (** First we deal with the simple case. If [list_map_preimage l (i a)] is
      None, we know that there are no pairs [(a', i a)] in [l]. So we can
      remove any pair starting with [a] from [l] and the result will still be
      injective. *)
  Lemma lmp_none_simpl {l} (injfH : inj_on P (f l)) {a}
    : list_map_preimage l (i a) = None ->
      inj_on P (f (remove_under decA fst a l)).
  Proof.
    intros noneH u v Pu Pv.
    unfold f; rewrite !list_map_remove_under; fold (f l).
    destruct (decA u a) as [ -> | uaneH ];
      destruct (decA v a) as [ -> | vaneH ]; auto.
    - intro iaH.
      rewrite (lmp_none_elim l v noneH (sym_eq iaH)) in iaH; auto.
    - intro iaH.
      rewrite (lmp_none_elim l u noneH iaH) in iaH; auto.
  Qed.

  Definition extends1 l0 l1 :=
    length l0 < length l1 /\
    inj_on P (list_map decA i l0) /\
    inj_on P (list_map decA i l1) /\
    exists a, forall u, list_map decA i l1 u =
              list_map decA i ((a, f l1 a) :: l0) u.

  (** What's more, we can recover the existing map by consing on our pair
      (which gives us a sort of induction step). *)
  Lemma lmp_none_ind_step {l} (injfH : inj_on P (f l)) {a}
    : in_under fst a l ->
      list_map_preimage l (i a) = None ->
      extends1 (remove_under decA fst a l) l.
  Proof.
    intros inH noneH; unfold extends1.
    split_conj; auto using lmp_none_simpl, length_remove_under_in.
    exists a; intro u; f_cons_simpl; rewrite list_map_remove_under.
    destruct (decA u a) as [ -> | ]; auto.
  Qed.

  (** There's another simple case: if [list_map_preimage l (i a)] is
      [a], removing any pairs starting with [a] from [l] will yield an
      injective map (in fact, it's the same map!). *)
  Lemma lmp_same_eval {l} {a}
    : list_map_preimage l (i a) = Some a ->
      forall aa, f (remove_under decA fst a l) aa = f l aa.
  Proof.
    intros lmpH aa.
    unfold f; rewrite list_map_remove_under.
    destruct (decA aa a) as [ -> | neH ]; auto.
    fold (f l); rewrite (lmp_some_elim _ lmpH); auto.
  Qed.

  Lemma lmp_same_simpl {l} (injfH : inj_on P (f l)) {a}
    : list_map_preimage l (i a) = Some a ->
      inj_on P (f (remove_under decA fst a l)).
  Proof.
    intros lmpH a0 a1.
    rewrite !(lmp_same_eval lmpH).
    apply injfH.
  Qed.

  (** We want to look at the list of elements that you get from
      repeated successful calls to [list_map_preimage]. These are a
      chain of pre-images. If this was a permutation (if [i] was the
      identity), we would be building a cycle in the disjoint cycle
      representation of the permutation. The [is_preimage_chain]
      proposition encodes the fact that we have the chain we
      expect. *)

  Fixpoint is_preimage_chain l a1 ll : Prop :=
    match ll with
    | nil => True
    | a :: ll' => f l a1 = i a /\ is_preimage_chain l a ll'
    end.

  Definition is_P_list ll : Prop :=
    forall a, In a ll -> P a.

  Lemma is_P_list_cons {a ll}
    : P a -> is_P_list ll -> is_P_list (a :: ll).
  Proof.
    intros paH plH aa inH.
    destruct inH as [ <- | ]; auto.
  Qed.

  Lemma is_P_list_singleton {a}
    : P a -> is_P_list (a :: nil).
  Proof.
    intros paH aa inH.
    destruct inH as [ <- | H ]; [ auto | inversion H ].
  Qed.

  Lemma is_P_list_tail {a ll}
    : is_P_list (a :: ll) -> is_P_list ll.
  Proof.
    intros plH aa inH; auto with datatypes.
  Qed.

  Definition is_P_list2 (l : list (A * B)) : Prop :=
    forall a, in_under fst a l -> P a.

  Lemma plist2_remove_under a l
    : is_P_list2 l ->
      is_P_list2 (remove_under decA fst a l).
  Proof.
    intros pl2H aa inH.
    exact (pl2H _ (in_under_remove_means_in_original _ _ inH)).
  Qed.

  (** In a minute, we're going to rely on the fact that some arbitrary pair in
      the chain are successors in the way we want. We prove it here, using
      [nth_error] to encode the fact that we have actually got successive
      elements from the middle of the chain. *)

  Lemma preimage_chain_nth_successors {l a1 ll n a a'}
    : is_preimage_chain l a1 ll ->
      nth_error (a1 :: ll) n = Some a ->
      nth_error (a1 :: ll) (S n) = Some a' ->
      f l a = i a'.
  Proof.
    revert a1 n; induction ll as [ | x ll IH ]; intros a1 n;
      [ destruct n; inversion 3 | ].
    destruct 1 as [ fla1H pcH ].
    destruct n.
    - repeat (injection 1 as ->); auto.
    - revert pcH; apply IH.
  Qed.

  (** Now we prove the lemma that's at the core of the usual "disjoint cycle"
      representation. If we're building up such a cycle and find a repeat, it
      must be a repeat of the last element. That is, we can't "jump back into
      the middle". *)

  Lemma lmp_loop_at_end {l a1 ll a}
    : is_preimage_chain l a1 ll ->
      is_P_list (a1 :: ll) ->
      distinct (a1 :: ll) ->
      list_map_preimage l (i a1) = Some a ->
      In a (a1 :: ll) ->
      a = ne_tail a1 ll.
  Proof.
    intros pcH plH distH lmpH inH.
    destruct (In_nth_error _ _ inH) as [ n aH ]; clear inH.
    assert (n < length (a1 :: ll)) as nleH;
      [ apply nth_error_Some; rewrite aH; inversion 1 | ].
    simpl in nleH.
    destruct (le_lt_eq_dec _ _ (lt_n_Sm_le _ _ nleH)) as [ nltH | -> ].
    - assert (exists a', nth_error (a1 :: ll) (S n) = Some a') as a'H;
        [ exists (nth (S n) (a1 :: ll) a);
          apply (nth_error_nth' (a1 :: ll) a (lt_n_S _ _ nltH)) | ].
      destruct a'H as [ a' a'H ].
      pose proof (lmp_some_elim l lmpH) as flaH.
      rewrite (preimage_chain_nth_successors pcH aH a'H) in flaH.
      destruct distH as [ notinH _ ].
      contradiction notinH.
      assert (P a') as Pa';
        [ exact (plH _ (nth_error_In (a1 :: ll) (S n) a'H)) | ].
      assert (P a1) as Pa1;
        [ exact (plH _ (in_eq a1 ll)) | ].
      rewrite <- (injiH a' a1 Pa' Pa1 flaH).
      apply (nth_error_In ll n a'H).
    - rewrite nth_error_ne_tail in aH; injection aH; auto.
  Qed.

  (** Suppose we've got a chain [a1 :: a2 :: ll] and have found a cycle. That
      is, [a1 = ne_tail a2 ll] (the extra cons avoids having to think about
      what happens if [ll] is null). Then we can make a simpler injection by
      mapping [a1] to [i a1] and then redirecting [ne_tail a2 ll], which was
      pointing at [i a1], to [i a2] (which [a1] no longer points at).

      Note that we remove [ne_tail a2 ll] from the list and then put it
      back. This makes no difference to the resulting function, but it's
      important for the induction because we're now removing two things and
      adding one back, so the list actually gets shorter. *)

  Definition trim_cycle l (tuple : A * A * list A)
    : list (A * B) :=
    let (head, ll) := tuple in
    let (a1, a2) := head in
    cons (ne_tail a2 ll, i a2)
         (remove_under decA fst (ne_tail a2 ll)
                       (remove_under decA fst a1 l)).

  Lemma trim_cycle_shorter l a1 a2 ll
    : distinct (a1 :: a2 :: ll) ->
      in_under fst a1 l ->
      in_under fst (ne_tail a2 ll) l ->
      length (trim_cycle l (a1, a2, ll)) < length l.
  Proof.
    intros distH in1H innH; simpl.
    apply (Nat.le_trans _ (S (length (remove_under decA fst a1 l)))).
    - apply le_n_S, length_remove_under_in.
      apply in_under_remove; auto.
      destruct distH as [ notinH _ ];
        intros <-; contradiction notinH;
        auto using in_ne_tail.
    - apply length_remove_under_in; auto.
  Qed.

  (** This next lemma is a little technical lemma that's used in
      [trim_cycle_inj] (it comes up twice, so seemed worth factoring
      out). *)

  Lemma lm_remove_under_a1 l a1 a2 ll v
    : inj_on P (f l) ->
      is_P_list (a1 :: a2 :: ll) ->
      P v ->
      distinct (a1 :: a2 :: ll) ->
      is_preimage_chain l a1 (a2 :: ll) ->
      i a2 <> list_map decA i (remove_under decA fst a1 l) v.
  Proof.
    intros injfH plH pvH distH pcH.
    assert (P a1) as Pa1;
      [ exact (plH a1 (in_eq a1 (a2 :: ll))) | ].
    assert (P a2) as Pa2;
      [ exact (plH a2 (in_cons a1 a2 (a2 :: ll) (in_eq a2 ll))) | ].
    rewrite list_map_remove_under.
    destruct (decA v a1) as [ -> | ne1H ].
    - intro H; specialize (injiH a2 a1 Pa2 Pa1 H); clear H.
      destruct distH as [ notinH _ ]; contradiction notinH.
      rewrite injiH; auto with datatypes.
    - fold (f l); intro flvH.
      contradiction ne1H.
      destruct pcH as [ fla1H _ ]; rewrite <- fla1H in flvH; auto.
  Qed.

  (** One reasonably painful job is to check that the [trim_cycle]
      yields a list that still gives an injective function. This boils
      down to a long case analysis. *)

  Lemma trim_cycle_inj {l a1 a2 ll}
    : inj_on P (f l) ->
      is_preimage_chain l a1 (a2 :: ll) ->
      is_P_list (a1 :: a2 :: ll) ->
      is_P_list2 l ->
      distinct (a1 :: a2 :: ll) ->
      list_map_preimage l (i a1) = Some (ne_tail a2 ll) ->
      inj_on P (f (trim_cycle l (a1, a2, ll))).
  Proof.
    unfold trim_cycle.
    set (an := ne_tail a2 ll).
    intros injfH pcH plH pl2H distH lmpH.
    pose proof (lmp_some_elim l lmpH) as flanH.
    intros u v Pu Pv; f_cons_simpl; rewrite list_map_remove_under.
    destruct (decA u an) as [ -> | neuH ].
    + rewrite list_map_remove_under.
      destruct (decA v an) as [ -> | nevH ]; auto.
      intros; contradiction (lm_remove_under_a1 l a1 a2 ll v).
    + rewrite (list_map_remove_under _ _ v).
      destruct (decA v an) as [ -> | nevH ];
        [ intros;
          contradiction (lm_remove_under_a1 l a1 a2 ll u);
          auto | ].
      rewrite !list_map_remove_under.
      assert (P an) as Pan; [ exact (pl2H _ (lmp_some_in l lmpH)) | ].
      destruct (decA u a1) as [ -> | neu1H ].
      * destruct (decA v a1) as [ -> | nev1H ]; auto.
        fold (f l); rewrite <- flanH; intros; contradiction nevH; auto.
      * destruct (decA v a1) as [ -> | nev1H ]; auto.
        fold (f l); rewrite <- flanH; intros; contradiction neuH; auto.
  Qed.

  (** Once we've trimmed the cycle, we want to be able to extend it
      back to give the function we started with. This job is done by
      [extend_cycle], which we define and then show has the properties
      we want. *)

  Definition extend_cycle a1 a2 a3 l' :=
    (a1, i a2) :: (a3, i a1) :: l'.

  Lemma extend_trimmed {l a1 a2 ll} u
    : is_preimage_chain l a1 (a2 :: ll) ->
      list_map_preimage l (i a1) = Some (ne_tail a2 ll) ->
      f l u = f (extend_cycle a1 a2 (ne_tail a2 ll)
                              (trim_cycle l (a1, a2, ll))) u.
  Proof.
    intros pcH lmpH.
    pose proof (lmp_some_elim l lmpH) as flanH.
    unfold extend_cycle, trim_cycle.
    f_cons_simpl; fold (f l).
    destruct pcH as [ fla1H pcH ].
    rewrite !list_map_remove_under.
    destruct (decA u a1) as [ -> | ]; auto.
    destruct (decA u (ne_tail a2 ll)) as [ -> | ]; auto.
  Qed.

  Definition extends2 l0 l1 :=
    length l0 < length l1 /\
    inj_on P (list_map decA i l0) /\
    inj_on P (list_map decA i l1) /\
    exists a1 a2 a3,
      list_map decA i l0 a3 = i a2 /\
      forall u,
        list_map decA i l1 u =
        list_map decA i (extend_cycle a1 a2 a3 l0) u.

  (** This lemma shows how to simplify an injection if we've managed
      to find a cycle. We ask that we've got a pre-image chain of the
      form [a1 :: a2 :: ll] where the pre-image of [a1] is the tail of
      [a2 :: ll]. *)

  Lemma lmp_some_tail_ind_stop l a1 a2 ll
    : inj_on P (f l) ->
      is_preimage_chain l a1 (a2 :: ll) ->
      is_P_list (a1 :: a2 :: ll) ->
      is_P_list2 l ->
      distinct (a1 :: a2 :: ll) ->
      list_map_preimage l (i a1) = Some (ne_tail a2 ll) ->
      in_under fst a1 l ->
      in_under fst (ne_tail a2 ll) l ->
      extends2 (trim_cycle l (a1, a2, ll)) l.
  Proof.
    intros injfH pcH plH pl2H distH lmpH in1H innH.
    unfold extends2; split_conj; auto.
    - auto using trim_cycle_shorter.
    - eauto using trim_cycle_inj.
    - exists a1. exists a2; exists (ne_tail a2 ll).
      split.
      + simpl; unfold upd_map; simpl.
        destruct (decA _ _); tauto.
      + auto using extend_trimmed.
  Qed.

  (** We know how to cons terms one by one onto a pre-image chain. Now
      we define a function that does this [n] times, if possible. If
      not, it returns some element with no pre-image. In the latter
      case, we can use [lmp_none_ind_step]. In the former case, we
      make sure to choose a large enough [n] that we know we'll get a
      loop. The trick is that if there's no loop then each element is
      distinct. But each element also appears as the first coordinate
      in [l], so we must have some sort of repeat if [n] is [S (length
      l)]. *)

  Inductive cycle_result : Type :=
  | DeadEnd  : A -> cycle_result
  | Repeat   : A -> cycle_result
  | Cycle    : A -> list A -> cycle_result
  | Straight : A -> list A -> cycle_result.

  Fixpoint build_cycle'
           (l : list (A * B))
           (n : nat) (a0 : A) (ll : list A) (a : A) {struct n}
    : cycle_result :=
    match n with
    | 0 => Straight a0 ll
    | S n' =>
      match list_map_preimage l (i a0) with
      | None => DeadEnd a0
      | Some a1 =>
        if decA a1 a0
        then Repeat a0
        else if decA a1 a
             then Cycle a1 (a0 :: ll)
             else build_cycle' l n' a1 (a0 :: ll) a
      end
    end.

  Definition build_cycle l n a := build_cycle' l n a nil a.

  Lemma dead_end_elim' {l n a0 ll a a'}
    : inj_on P (f l) ->
      in_under fst a0 l ->
      build_cycle' l n a0 ll a = DeadEnd a' ->
      extends1 (remove_under decA fst a' l) l.
  Proof.
    intros injH inH.
    revert a0 ll inH; induction n as [ | n IH ]; intros a0 ll inH;
      [ inversion 1 | ].
    cbn [build_cycle' fst].
    case_eq (list_map_preimage l (i a0)).
    - intros a1 lmpH bcH.
      destruct (decA a1 a0) as [ | ne10H ]; [ inversion bcH | ].
      destruct (decA a1 a) as [ | ne1H ]; [ inversion bcH | ].
      exact (IH a1 (a0 :: ll) (lmp_some_in l lmpH) bcH).
    - intros lmpH; injection 1 as <-.
      auto using lmp_none_ind_step.
  Qed.

  Lemma dead_end_elim {l n a a'}
    : inj_on P (f l) ->
      in_under fst a l ->
      build_cycle l n a = DeadEnd a' ->
      extends1 (remove_under decA fst a' l) l.
  Proof.
    apply dead_end_elim'.
  Qed.

  Lemma repeat_elim' {l n a0 ll a a'}
    : inj_on P (f l) ->
      in_under fst a0 l ->
      build_cycle' l n a0 ll a = Repeat a' ->
      extends1 (remove_under decA fst a' l) l.
  Proof.
    intros injH; unfold extends1.
    revert a0 ll; induction n as [ | n IH ]; intros a0 ll;
      [ inversion 2 | ].
    intros inH.
    simpl.
    case_eq (list_map_preimage l (i a0));
      [ | inversion 2 ].
    intros a1 lmpH.
    destruct (decA a1 a0) as [ -> | ne01H ].
    - injection 1 as <-; split_conj; auto.
      + auto using (length_remove_under_in decA inH).
      + auto using lmp_same_simpl.
      + exists a0.
        fold (f (remove_under decA fst a0 l)).
        intro u; unfold upd_map; simpl.
        rewrite (lmp_same_eval lmpH u).
        destruct (decA u a0) as [ <- | ]; auto.
    - destruct (decA a1 a) as [ | ne1H ]; [ inversion 1 | ].
      intros bcH.
      apply (IH a1 (a0 :: ll) (lmp_some_in l lmpH) bcH).
  Qed.

  Lemma repeat_elim {l n a a'}
    : inj_on P (f l) ->
      in_under fst a l ->
      build_cycle l n a = Repeat a' ->
      extends1 (remove_under decA fst a' l) l.
  Proof.
    apply repeat_elim'.
  Qed.

  Lemma cycle_ind' {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Cycle a0' ll' ->
      forall PP : A -> list A -> Prop,
      forall Q : A -> list A -> Prop,
        PP a0 ll ->
        (forall a0 ll,
            PP a0 ll ->
            a <> a0 ->
            list_map_preimage l (i a0) = Some a ->
            Q a (a0 :: ll)) ->
        (forall a1 a0 ll,
            PP a0 ll ->
            a1 <> a0 ->
            a1 <> a ->
            list_map_preimage l (i a0) = Some a1 ->
            PP a1 (a0 :: ll)) ->
        Q a0' ll'.
  Proof.
    intros bcH PP Q baseH step0H step1H.
    revert a0 ll bcH baseH; induction n as [ | n IH ]; intros a0 ll;
      [ inversion 1 | ].
    cbn [build_cycle' fst].
    case_eq (list_map_preimage l (i a0)); [ | inversion 2 ].
    intros a1 lmpH.
    destruct (decA a1 a0) as [ -> | neH ]; [ inversion 1 | ].
    destruct (decA a1 a) as [ -> | neH' ].
    - injection 1 as <- <-; auto.
    - auto using (IH a1 (a0 :: ll)).
  Qed.

  Lemma cycle_ind_pp' {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Cycle a0' ll' ->
      forall P : A -> list A -> Prop,
        P a0 ll ->
        (forall a1 a0 ll,
            P a0 ll ->
            a1 <> a0 ->
            list_map_preimage l (i a0) = Some a1 ->
            P a1 (a0 :: ll)) ->
        P a0' ll'.
  Proof.
    intros bcH PP P0 stepH.
    apply (cycle_ind' bcH PP PP); auto.
  Qed.

  Lemma cycle_head {l n a a' ll'}
    : build_cycle l n a = Cycle a' ll' ->
      a' = a.
  Proof.
    intros bcH.
    apply (cycle_ind' bcH (fun a0 ll => True) (fun a0 ll => a0 = a)); auto.
  Qed.

  Lemma cycle_tail' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      ne_tail a0 ll = a ->
      ne_tail a ll' = a.
  Proof.
    eauto using (cycle_ind_pp' _ (fun a0 ll => ne_tail a0 ll = a)).
  Qed.

  Lemma cycle_tail {l n a ll'}
    : build_cycle l n a = Cycle a ll' ->
      ne_tail a ll' = a.
  Proof.
    eauto using cycle_tail'.
  Qed.

  Lemma cycle_pc' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      is_preimage_chain l a0 ll ->
      is_preimage_chain l a ll'.
  Proof.
    intros bcH pcH.
    apply (cycle_ind_pp' bcH (is_preimage_chain l)); auto.
    split; auto using lmp_some_elim.
  Qed.

  Lemma cycle_pc {l n a ll'}
    : build_cycle l n a = Cycle a ll' ->
      is_preimage_chain l a ll'.
  Proof.
    intros bcH.
    apply (cycle_pc' bcH); simpl; auto.
  Qed.

  Lemma cycle_plist' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      is_P_list (a0 :: ll) ->
      is_P_list2 l ->
      is_P_list (a :: ll').
  Proof.
    intros bcH plH pl2H.
    apply (cycle_ind_pp' bcH);
      eauto using is_P_list_cons, lmp_some_in.
  Qed.

  Lemma cycle_plist {l n a ll'}
    : build_cycle l n a = Cycle a ll' ->
      P a ->
      is_P_list2 l ->
      is_P_list (a :: ll').
  Proof.
    intros bcH paH pl2H.
    apply (cycle_plist' bcH); auto using is_P_list_singleton.
  Qed.

  Lemma cycle_distinct' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      is_preimage_chain l a0 ll ->
      is_P_list (a0 :: ll) ->
      is_P_list2 l ->
      ne_tail a0 ll = a ->
      distinct (a0 :: ll) ->
      distinct ll'.
  Proof.
    intros bcH pcH plH pl2H tailH distH.
    apply (cycle_ind' bcH
                      (fun a0 ll =>
                         is_preimage_chain l a0 ll /\
                         is_P_list (a0 :: ll) /\
                         ne_tail a0 ll = a /\
                         distinct (a0 :: ll))
                      (fun a0 ll => distinct ll));
      auto; clear a0 ll bcH pcH plH tailH distH.
    - intros a0 ll [ pcH [ plH [ tailH distH ] ] ] ne10H lmpH; auto.
    - intros a1 a0 ll [ pcH [ plH [ tailH distH ] ] ] ne10H neH lmpH.
      split_conj; auto.
      + split; auto using (lmp_some_elim _ lmpH).
      + eauto using is_P_list_cons, lmp_some_in.
      + split; auto.
        intros inH.
        contradiction neH.
        rewrite (lmp_loop_at_end pcH plH distH lmpH inH); auto.
  Qed.

  Lemma cycle_distinct {l n a ll'}
    : build_cycle l n a = Cycle a ll' ->
      P a ->
      is_P_list2 l ->
      distinct ll'.
  Proof.
    unfold build_cycle; intros bcH paH pl2H;
      apply (cycle_distinct' bcH);
      simpl;
      auto using is_P_list_singleton.
  Qed.

  Lemma cycle_length' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      length ll' > length ll.
  Proof.
    intros bcH.
    destruct n; [ inversion bcH | ].
    simpl in bcH.
    destruct (list_map_preimage l (i a0)) as [ a1 | ]; [ | inversion bcH ].
    destruct (decA a1 a0) as [ | ne10H ]; [ inversion bcH | ].
    destruct (decA a1 a) as [ -> | neH ]; [ injection bcH as <-; auto | ].
    set (longer := (fun (a0' : A) (ll' : list A) => length ll' > length ll)).
    apply (cycle_ind' bcH longer longer); unfold longer; simpl; auto.
  Qed.

  Lemma cycle_structure' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      ne_tail a0 ll = a ->
      length ll' >= 2.
  Proof.
    (* We know that a' = a and that ne_tail a' ll' = a. We also know
       that ll' = a0 :: ll. If ll was nil then a = ne_tail a0 ll = a0.
       But then we'd have seen a Repeat, not a Cycle. Thus ll is
       non-nil and of the form ll = a1 :: ll'' for some ll''. But then
       ll' = a0 :: a1 :: ll'' and we are done. *)
    intros bcH tailH.
    pose proof (cycle_tail' bcH tailH) as tailH'.
    destruct n; [ inversion bcH | ]; simpl in bcH.
    destruct (list_map_preimage l (i a0)); [ | inversion bcH ].
    destruct (decA a1 a0) as [ | ne01H ]; [ inversion bcH | ].
    destruct (decA a1 a) as [ -> | ne1H ].
    - injection bcH as <-.
      destruct ll as [ | a1 ll'' ].
      + contradiction ne01H; simpl in tailH'; auto.
      + simpl; unfold ge; repeat (apply le_n_S).
        apply le_0_n.
    - apply (Nat.le_trans 2 (S (S (length ll))) (length ll'));
        auto using le_n_S, le_0_n.
      apply lt_le_S.
      apply (cycle_length' bcH).
  Qed.

  Definition uncons2 (ll : list A) (default : A) : A * A * list A :=
    match ll with
    | a0 :: a1 :: ll' => (a0, a1, ll')
    | _ => (default, default, nil)
    end.

  Definition cons2 (tuple : A * A * list A) : list A :=
    let (head, ll) := tuple in
    let (a0, a1) := head in
    a0 :: a1 :: ll.

  Lemma cycle_structure {l n a ll'}
    : build_cycle l n a = Cycle a ll' ->
      ll' = cons2 (uncons2 ll' a).
  Proof.
    intros bcH.
    destruct ll' as [ | a0 ll' ];
      [ contradiction (Nat.nle_succ_0 1);
        apply (cycle_structure' bcH eq_refl) | ].
    destruct ll' as [ | a1 ll' ];
      [ contradiction (Nat.nle_succ_0 0);
        apply le_S_n, (cycle_structure' bcH eq_refl) | ].
    auto.
  Qed.

  Lemma plist2_trim_cycle l a0 a1 ll
    : is_P_list (a0 :: a1 :: ll) ->
      is_P_list2 l ->
      is_P_list2 (trim_cycle l (a0, a1, ll)).
  Proof.
    intros plH pl2H; simpl.
    intros a inH.
    destruct inH as [ -> | inH ].
    - simpl; auto using in_ne_tail with datatypes.
    - apply pl2H.
      pose proof (in_under_remove_means_in_original _ _ inH) as inH'.
      apply (in_under_remove_means_in_original _ _ inH').
  Qed.

  Lemma cycle_lmp' {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Cycle a (a0' :: ll') ->
      list_map_preimage l (i a0') = Some a.
  Proof.
    revert a0 ll; induction n as [ | n IH ]; [ inversion 1 | ]; intros a0 ll.
    simpl.
    case_eq (list_map_preimage l (i a0)); [ | inversion 2 ].
    intros a1 lmpH.
    destruct (decA a1 a0) as [ | ne01H ]; [ inversion 1 | ].
    destruct (decA a1 a) as [ -> | neH ].
    - injection 1 as <- <-; auto.
    - intros bcH; specialize (IH a1 (a0 :: ll) bcH); auto.
  Qed.

  Lemma cycle_lmp {l n a a0 ll}
    : build_cycle l n a = Cycle a (a0 :: ll) ->
      list_map_preimage l (i a0) = Some a.
  Proof.
    eauto using cycle_lmp'.
  Qed.

  Lemma cycle_in_under' {l n a0 ll a ll'}
    : build_cycle' l n a0 ll a = Cycle a ll' ->
      (forall aa, In aa (a0 :: ll) -> in_under fst aa l) ->
      forall aa, In aa (a :: ll') -> in_under fst aa l.
  Proof.
    intros bcH preH.
    apply (cycle_ind_pp' bcH (fun a0 ll => (forall aa, In aa (a0 :: ll) ->
                                               in_under fst aa l)));
      auto; clear a0 ll ll' bcH preH.
    intros a0 ll inH neH lmpH aa.
    destruct 1 as [ -> | ]; eauto using lmp_some_in.
  Qed.

  Lemma cycle_in_under {l n a ll'}
    : build_cycle l n a = Cycle a ll' ->
      in_under fst a l ->
      forall aa, In aa (a :: ll') ->
            in_under fst aa l.
  Proof.
    intros bcH inH; apply (cycle_in_under' bcH).
    intros aa inH'; destruct inH' as [ <- | nilH ];
      [ auto | inversion nilH ].
  Qed.

  Lemma cycle_elim {l n a a' ll'}
    : inj_on P (f l) ->
      build_cycle l n a = Cycle a' ll' ->
      P a ->
      is_P_list2 l ->
      in_under fst a l ->
      extends2 (trim_cycle l (uncons2 ll' a)) l.
  Proof.
    intros injH bcH paH pl2H inH.
    rewrite (cycle_head bcH) in bcH; clear a'.
    rewrite (cycle_structure bcH) in bcH.
    destruct (uncons2 ll' a) as [ [ a0 a1 ] ll ]; simpl in bcH.
    assert (ne_tail a1 ll = a) as tailH;
      [ pose proof (cycle_tail bcH) as tailH';
        simpl in tailH'; rewrite tailH'; auto | ].
    apply (lmp_some_tail_ind_stop l a0 a1 ll);
      try (rewrite tailH); auto.
    - destruct (cycle_pc bcH); auto.
    - intros aa inH'.
      apply (cycle_plist bcH paH pl2H);
        auto with datatypes.
    - apply (cycle_distinct bcH paH pl2H).
    - apply (cycle_lmp bcH).
    - apply (cycle_in_under bcH inH); simpl; auto.
  Qed.

  Lemma straight_ind'  {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Straight a0' ll' ->
      forall P : A -> list A -> Prop,
        P a0 ll ->
        (forall a1 a0 ll,
            P a0 ll ->
            list_map_preimage l (i a0) = Some a1 ->
            a1 <> a0 ->
            a1 <> a ->
            P a1 (a0 :: ll)) ->
        P a0' ll'.
  Proof.
    intros bcH PP P0 stepH; revert bcH.
    revert a0 ll P0; induction n as [ | n IH ]; intros a0 ll P0;
      [ injection 1 as <- <-; auto | ].
    cbn [build_cycle' fst].
    case_eq (list_map_preimage l (i a0)); [ | inversion 2 ].
    intros a1 lmpH.
    destruct (decA a1 a0) as [ | ne0H ]; [ inversion 1 | ].
    destruct (decA a1 a) as [ | neH ]; [ inversion 1 | ].
    eauto.
  Qed.

  Lemma straight_length' {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Straight a0' ll' ->
      length (a0' :: ll') = n + length (a0 :: ll).
  Proof.
    revert a0 ll; induction n as [ | n IH ]; intros a0 ll;
      [ injection 1 as <- <-; auto | ].
    simpl; simpl in IH.
    destruct (list_map_preimage l (i a0)) as [ a1 | ]; [ | inversion 1 ].
    destruct (decA a1 a0) as [ | ne10H ]; [ inversion 1 | ].
    destruct (decA a1 a) as [ | ne1H ]; [ inversion 1 | ].
    intros bcH.
    rewrite (IH a1 (a0 :: ll) bcH); auto.
  Qed.

  Lemma straight_length {l n a a0 ll}
    : build_cycle l n a = Straight a0 ll ->
      length (a0 :: ll) = S n.
  Proof.
    intros bcH.
    rewrite (straight_length' bcH); auto using Nat.add_1_r.
  Qed.

  Lemma straight_distinct' {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Straight a0' ll' ->
      is_P_list2 l ->
      (is_preimage_chain l a0 ll /\
       is_P_list (a0 :: ll) /\
       ne_tail a0 ll = a /\
       distinct (a0 :: ll)) ->
      (is_preimage_chain l a0' ll' /\
       is_P_list (a0' :: ll') /\
       ne_tail a0' ll' = a /\
       distinct (a0' :: ll')).
  Proof.
    intros bcH pl2H H0; apply (straight_ind' bcH); auto.
    clear a0' ll' bcH H0 a0 ll.
    intros a1 a0 ll [ pcH [ plH [ tailH distH ] ] ] lmpH ne10H neH.
    split_conj; auto.
    - split; auto using (lmp_some_elim _ lmpH).
    - eauto using is_P_list_cons, lmp_some_in.
    - split; auto.
      intros inH; contradiction neH.
      rewrite (lmp_loop_at_end pcH plH distH lmpH inH); auto.
  Qed.

  Lemma straight_distinct {l n a a0 ll}
    : build_cycle l n a = Straight a0 ll ->
      P a ->
      is_P_list2 l ->
      distinct (a0 :: ll).
  Proof.
    intros bcH paH pl2H.
    apply (straight_distinct' bcH pl2H).
    split_conj; simpl; auto using is_P_list_singleton.
  Qed.

  Lemma straight_in_l' {l n a0 ll a a0' ll'}
    : build_cycle' l n a0 ll a = Straight a0' ll' ->
      (forall x, In x (a0 :: ll) -> in_under fst x l) ->
      (forall x, In x (a0' :: ll') -> in_under fst x l).
  Proof.
    intros bcH H0; apply (straight_ind' bcH); auto.
    clear a0' ll' bcH H0 a0 ll.
    intros a1 a0 ll inH lmpH ne10H neH x.
    destruct 1 as [ <- | ]; eauto using lmp_some_in.
  Qed.

  Lemma straight_in_l {l n a a0 ll}
    : build_cycle l n a = Straight a0 ll ->
      in_under fst a l ->
      (forall x, In x (a0 :: ll) -> in_under fst x l).
  Proof.
    intros bcH inH.
    apply (straight_in_l' bcH).
    intros x.
    destruct 1 as [ <- | consH ]; [ auto | inversion consH ].
  Qed.

  Lemma straight_len_l {l n a a0 ll}
    : build_cycle l n a = Straight a0 ll ->
      P a ->
      is_P_list2 l ->
      in_under fst a l ->
      length l >= S n.
  Proof.
    intros bcH paH pl2H inH.
    rewrite <- (straight_length bcH).
    apply (distinct_in_under decA (f := fst));
      auto using (straight_distinct bcH paH pl2H), (straight_in_l bcH).
  Qed.

  Definition hunt_cycle l a := build_cycle l (length l) a.

  Lemma hunt_cycle_not_straight {l a}
    : in_under fst a l ->
      P a ->
      is_P_list2 l ->
      forall a0 ll, hunt_cycle l a <> Straight a0 ll.
  Proof.
    unfold hunt_cycle.
    intros inH paH pl2H a0 ll bcH.
    contradiction (Nat.nle_succ_diag_l (length l)).
    apply (straight_len_l bcH paH pl2H inH).
  Qed.

  Lemma hunt_cycle_cases {l a}
    : in_under fst a l ->
      P a ->
      is_P_list2 l ->
      forall P : Prop,
        (forall a', hunt_cycle l a = DeadEnd a' -> P) ->
        (forall a', hunt_cycle l a = Repeat a' -> P) ->
        (forall ll, hunt_cycle l a = Cycle a ll -> P) ->
        P.
  Proof.
    unfold hunt_cycle; intros inH paH pl2H PP deH reH ceH.
    case_eq (build_cycle l (length l) a); auto.
    - intros a0 ll bcH; rewrite (cycle_head bcH) in bcH; eauto.
    - intros a0 ll bcH;
        contradiction (hunt_cycle_not_straight inH paH pl2H a0 ll).
  Qed.

  Definition shorten_cycle l a
    : list (A * B) :=
    match hunt_cycle l a with
    | DeadEnd a' => remove_under decA fst a' l
    | Repeat a' => remove_under decA fst a' l
    | Cycle a0 ll => trim_cycle l (uncons2 ll a)
    | Straight a0 ll => (* bogus *) nil
    end.

  Definition extends (l' l : list (A * B)) : Prop :=
    extends1 l' l \/ extends2 l' l.

  Lemma extends_shorter {l' l}
    : extends l' l -> length l' < length l.
  Proof.
    unfold extends, extends1, extends2; tauto.
  Qed.

  Lemma extends_inj {l' l}
    : extends l' l -> inj_on P (list_map decA i l').
  Proof.
    unfold extends, extends1, extends2; tauto.
  Qed.

  Lemma hunt_cycle_elim {l a}
        (injH : inj_on P (f l))
        (inH : in_under fst a l)
        (paH : P a)
        (pl2H : is_P_list2 l)
    : extends (shorten_cycle l a) l.
  Proof.
    unfold shorten_cycle.
    apply (hunt_cycle_cases inH paH pl2H).
    - intros a' hcH; rewrite hcH.
      left; eauto using (dead_end_elim injH inH hcH).
    - intros a' hcH; rewrite hcH.
      left; eauto using (repeat_elim injH inH hcH).
    - intros ll hcH; rewrite hcH.
      right; eauto using (cycle_elim injH hcH paH pl2H inH).
  Qed.

  Lemma plist2_shorten a l
        (inH : in_under fst a l)
        (paH : P a)
        (pl2H : is_P_list2 l)
    : is_P_list2 (shorten_cycle l a).
  Proof.
    unfold shorten_cycle.
    apply (hunt_cycle_cases inH paH pl2H).
    - intros a' hcH; rewrite hcH.
      auto using plist2_remove_under.
    - intros a' hcH; rewrite hcH.
      auto using plist2_remove_under.
    - intros ll hcH; rewrite hcH.
      assert (is_P_list (a :: ll)) as plH;
        [ exact (cycle_plist hcH paH pl2H) | ].
      revert plH; rewrite (cycle_structure hcH).
      destruct (uncons2 ll a) as [ [ a0 a1 ] ll' ].
      cbn [cons2 uncons2].
      eauto using plist2_trim_cycle, is_P_list_tail.
  Qed.

  Lemma extends_wf : well_founded extends.
  Proof.
    intro l.
    (* Juggle terms to allow induction in length l *)
    set (n := length l).
    assert (length l = n) as lenH; auto.
    revert lenH; generalize n; clear n.
    intros n; revert l.

    (* Strong induction principle *)
    induction (lt_wf n) as [ n _ IH ].
    intros l lenH.

    rewrite <- lenH in IH; clear n lenH.
    apply Acc_intro.
    intros l' exH.
    apply (IH (length l') (extends_shorter exH) l' eq_refl).
  Qed.

  Lemma in_under_fst_cons {X Y} (p : X * Y) l
    : in_under fst (fst p) (p :: l).
  Proof.
    simpl; auto.
  Qed.

  Lemma inj_map_ind (PP : (A -> B) -> Prop)
    : PP i ->
      (forall l0 l1,
          extends l0 l1 ->
          PP (list_map decA i l0) ->
          PP (list_map decA i l1)) ->
      forall l,
        inj_on P (list_map decA i l) ->
        is_P_list2 l ->
        PP (list_map decA i l).
  Proof.
    intros PiH stepH l injH.
    induction (extends_wf l) as [ l _ IH ].
    intros pl2H.
    destruct l as [ | [ a b ] l ]; auto.
    assert (in_under fst a ((a, b) :: l)) as inH;
      [ exact (in_under_fst_cons (a, b) l) | ].
    assert (P a) as paH; [ exact (pl2H a inH) | ].
    pose proof (hunt_cycle_elim injH inH paH pl2H) as exH.
    eauto using plist2_shorten, extends_inj.
  Qed.

  Lemma inj_map_rect (PP : list (A * B) -> Type)
    : PP nil ->
      (forall l0 l1, extends l0 l1 -> PP l0 -> PP l1) ->
      forall l,
        inj_on P (list_map decA i l) ->
        is_P_list2 l ->
        PP l.
  Proof.
    intros nilH stepH l injH pl2H.
    eapply (well_founded_induction_type
              extends_wf
              (fun l' => inj_on P (list_map decA i l') -> is_P_list2 l' -> PP l')
              _ l); auto. Unshelve.
    clear l injH pl2H; simpl; intros l allH injH pl2H.
    destruct l as [ | [ a b ] l ]; auto.
    assert (in_under fst a ((a, b) :: l)) as inH;
      [ exact (in_under_fst_cons (a, b) l) | ].
    assert (P a) as paH; [ exact (pl2H a inH) | ].
    pose proof (hunt_cycle_elim injH inH paH pl2H) as exH.
    eauto using plist2_shorten, extends_inj.
  Defined.

End maps.
