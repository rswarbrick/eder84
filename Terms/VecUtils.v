(** This library contains various handy definitions and lemmas for
    working with vectors, which don't come with that many batteries
    included straight from the Coq library. *)

Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.VectorDef.
Require Import Lists.List.
Require Import Program.Basics.

Notation vec := VectorDef.t.
Notation vnil := VectorDef.nil.
Notation vcons := VectorDef.cons.
Notation vsing := (fun a => vcons _ a _ (vnil _)).

Set Implicit Arguments.

Definition dec_proc_to_sumbool
           {A : Type}
           {P : A -> Prop}
           {f : A -> bool}
           (H: forall a, P a <-> is_true (f a))
           (a : A)
  : {P a} + {~ P a} :=
  Bool.reflect_dec _ _ (Bool.iff_reflect (P a) (f a) (H a)).

Definition dec_is_true_or_not (b : bool)
  : {is_true b} + {~ is_true b} :=
  match b with
  | true => left eq_refl
  | false => right Bool.diff_false_true
  end.

(** * [vec_all]

    We define [vec_all] to hold for a vector when the associated
    proposition holds for every element in it. This is vacuously true
    for the empty vector. *)

Section vec_all.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint vec_all {n} (v : vec A n) :=
    match v with
    | vnil _ => True
    | vcons _ a _ v' => P a /\ vec_all v'
    end.

  (** Here are the introduction rules. For convenience, we have an
      introduction rule for singletons as well. We don't prove an
      elimination rule for [vec_all] of a cons because just
      destructing the hypothesis does the right thing. *)

  Definition vec_all_nil : vec_all (vnil A) := I.

  Lemma vec_all_cons a {n} (v : vec A n)
    : P a -> vec_all v -> vec_all (vcons A a n v).
  Proof.
    apply conj.
  Qed.

  Definition vec_all_singleton a (aH : P a) : vec_all (vsing a) := conj aH I.

  (** The two introduction rules for [~ vec_all]. *)

  Lemma not_vec_all_cons0 a {n} (v : vec A n)
    : ~ P a -> ~ vec_all (vcons A a n v).
  Proof.
    unfold vec_all; tauto.
  Qed.

  Lemma not_vec_all_cons1 a {n} (v : vec A n)
    : ~ vec_all v -> ~ vec_all (vcons _ a _ v).
  Proof.
    intros; unfold vec_all; tauto.
  Qed.
End vec_all.

Hint Resolve vec_all_nil : vec.
Hint Resolve vec_all_cons : vec.
Hint Resolve vec_all_singleton : vec.

(** As you might expect from the executable definition, [vec_all P] is
    decidable if [P] is decidable. We prove that here by defining a
    decision procedure and then proving its correctness. *)

Section dec_vec_all.
  Variable A : Type.
  Variable P : A -> Prop.
  Hypothesis decP : forall x : A, {P x} + {~ (P x)}.

  Fixpoint check_vec_all {n} (v : vec A n) : bool :=
    match v with
    | vnil _ => true
    | vcons _ a _ v' =>
      match decP a with
      | left paH => check_vec_all v'
      | right nH => false
      end
    end.

  Lemma check_vec_all_correct {n} (v : vec A n)
    : vec_all P v <-> is_true (check_vec_all v).
  Proof.
    induction v as [ | a n v IH ]; simpl; unfold is_true, iff; auto.
    destruct (decP a) as [ pH | npH ];
      destruct IH as [ IHl IHr ]; try tauto.
    split.
    + intros [ H _ ]; auto.
    + intros ftH; contradiction Bool.diff_false_true.
  Qed.

  Definition dec_vec_all {n} (v : vec A n)
    : {vec_all P v} + {~ (vec_all P v)} :=
    dec_proc_to_sumbool check_vec_all_correct v.

End dec_vec_all.

Arguments check_vec_all {A P} decP {n} v.
Arguments dec_vec_all {A P} decP {n} v.

(** A version of modus ponens for vec_all *)

Lemma vec_all_modus_ponens
      {A : Type} {P Q : A -> Prop} {n} (v : vec A n)
  : vec_all (fun a => P a -> Q a) v ->
    vec_all P v -> vec_all Q v.
Proof.
  induction v as [ | a n v IH ]; auto.
  simpl; intros [ pqH allpqH ] [ paH allpH ]; split; auto.
Qed.

(** Unpacking [vec_all] when converting to a list *)

Lemma vec_all_to_list (A : Type) (P : A -> Prop) n (v : vec A n)
  : vec_all P v ->
    forall a,
      In a (VectorDef.to_list v) -> P a.
Proof.
  induction v as [ | a0 n v IH ]; [ simpl; tauto | ].
  destruct 1 as [ H0 allH ].
  intro a.
  specialize (IH allH a); clear allH.
  unfold VectorDef.to_list; fold (VectorDef.to_list v).
  destruct 1 as [ eqH | ]; [ rewrite <- eqH | ]; auto.
Qed.

(** * [vec_some]

  This is the existential version of [vec_all]. If everything is
  decidable, this can be expressed in terms of [vec_all] but, of
  course, you have to be a bit more careful if not. So we define it
  separately and then prove the relationship between the two versions
  afterwards.

*)

Section vec_some.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint vec_some {n} (v : vec A n) :=
    match v with
    | vnil _ => False
    | vcons _ a _ v' => P a \/ vec_some v'
    end.

  (**

    The introduction rules for [vec_some]. Unlike [vec_all], there
    isn't a rule for the nil case (since this is always false!) As
    with [vec_all], we prove an explicit introduction rule for the
    singleton case.

   *)

  Lemma vec_some_cons0 a {n} (v : vec A n)
    : P a -> vec_some (vcons A a n v).
  Proof.
    simpl; auto.
  Qed.

  Lemma vec_some_cons1 a {n} (v : vec A n)
    : vec_some v -> vec_some (vcons A a n v).
  Proof.
    simpl; auto.
  Qed.

  Definition vec_some_singleton a (aH : P a) : vec_some (vsing a) :=
    vec_some_cons0 (vnil _) aH.

  (**

    Now the introduction rules for [~vec_some].

   *)

  Lemma not_vec_some_nil : ~ vec_some (vnil A).
  Proof.
    auto.
  Qed.

  Lemma not_vec_some_cons a {n} (v : vec A n)
    : ~ P a -> ~ vec_some v -> ~ vec_some (vcons A a n v).
  Proof.
    simpl; tauto.
  Qed.

End vec_some.

Arguments vec_some {A} P {n}.
Arguments vec_some_cons0 {A P a n v} naH.
Arguments vec_some_cons1 {A P} a {n v} nvH.
Arguments vec_some_singleton {A P a} aH.
Arguments not_vec_some_nil {A} P.
Arguments not_vec_some_cons {A P a n v} aH vH.

Hint Resolve vec_some_cons0 : vec.
Hint Resolve vec_some_cons1 : vec.
Hint Resolve vec_some_singleton : vec.

(** Before we do the equivalent of [dec_vec_all] for [vec_some], we
    show the relationship between [vec_some] and [vec_all]. This
    lets us "cheat" and avoid having to define a decidable
    version of [vec_some] from scratch. *)

Section dec_vec_some.
  Variable A : Type.
  Variable P : A -> Prop.
  Hypothesis decP : forall x : A, {P x} + {~ (P x)}.

  Lemma vec_some_as_vec_all {n} (v : vec A n)
    : vec_some P v <-> ~ vec_all (fun a => ~ P a) v.
  Proof.
    induction v as [ | a n v IH ].
    - simpl; tauto.
    - simpl; split; try tauto.
      destruct (decP a); tauto.
  Qed.

  Lemma decP_inv : forall x, {~ P x} + {~ (~ P x)}.
  Proof.
    intro x.
    destruct (decP x); auto.
  Qed.

  Definition check_vec_some {n} (v : vec A n) : bool :=
    negb (check_vec_all decP_inv v).

  Lemma check_vec_some_correct {n} (v : vec A n)
    : vec_some P v <-> is_true (check_vec_some v).
  Proof.
    rewrite vec_some_as_vec_all.
    rewrite (check_vec_all_correct _ decP_inv).
    unfold check_vec_some.
    unfold is_true; rewrite Bool.negb_true_iff.
    rewrite Bool.not_true_iff_false.
    tauto.
  Qed.

  Definition dec_vec_some {n} (v : vec A n)
    : {vec_some P v} + {~ (vec_some P v)} :=
    dec_proc_to_sumbool check_vec_some_correct v.

End dec_vec_some.

Arguments vec_some_as_vec_all {A P} decP {n} v.
Arguments check_vec_some {A P} decP {n} v.
Arguments dec_vec_some {A P} decP {n} v.

(** Unpacking [vec_some] when converting to a list *)

Lemma vec_some_to_list (A : Type) (P : A -> Prop) n (v : vec A n)
  : vec_some P v ->
    exists a,
      In a (VectorDef.to_list v) /\ P a.
Proof.
  induction v as [ | a0 n v IH ]; [ contradiction | ].
  destruct 1 as [ pa0H | someH ].
  - exists a0; split; simpl; auto.
  - destruct (IH someH) as [ a [ inH paH ] ].
    exists a; split; simpl; auto.
Qed.

(** Specialized forms of [vec_all] and [vec_some] for boolean functions *)

Section dec_vecb.
  Variable A : Type.
  Variable f : A -> bool.

  Definition vec_allb {n} (v : vec A n) : Prop :=
    vec_all (fun a => is_true (f a)) v.

  Definition check_vec_allb {n} (v : vec A n)  : bool :=
    check_vec_all (fun a => dec_is_true_or_not (f a)) v.

  Lemma check_vec_allb_correct {n} (v : vec A n)
    : vec_allb v <-> is_true (check_vec_allb v).
  Proof.
    apply check_vec_all_correct.
  Qed.

  Definition dec_vec_allb {n} (v : vec A n)
    : {vec_allb v} + {~ vec_allb v} :=
    dec_proc_to_sumbool check_vec_allb_correct v.

  Definition vec_someb {n} (v : vec A n) : Prop :=
    vec_some (fun a => is_true (f a)) v.

  Definition check_vec_someb {n} (v : vec A n)  : bool :=
    check_vec_some (fun a => dec_is_true_or_not (f a)) v.

  Lemma check_vec_someb_correct {n} (v : vec A n)
    : vec_someb v <-> is_true (check_vec_someb v).
  Proof.
    apply check_vec_some_correct.
  Qed.

  Definition dec_vec_someb {n} (v : vec A n)
    : {vec_someb v} + {~ vec_someb v} :=
    dec_proc_to_sumbool check_vec_someb_correct v.

  Lemma check_vec_someb_nil
    : check_vec_someb (vnil A) = false.
  Proof.
    unfold check_vec_someb, check_vec_some; auto.
  Qed.

  Lemma check_vec_someb_cons {n} (a : A) (v : vec A n)
    : check_vec_someb (vcons A a n v) = orb (f a) (check_vec_someb v).
  Proof.
    unfold check_vec_someb at 1.
    unfold check_vec_some.
    simpl.
    destruct (decP_inv _ _ a) as [ noH | yesH ].
    - unfold is_true in noH.
      rewrite (Bool.not_true_is_false (f a) noH); simpl; clear noH.
      reflexivity.
    - revert yesH; unfold is_true.
      case (f a); auto.
      intro H; contradiction H.
      apply Bool.diff_false_true.
  Qed.

End dec_vecb.


Lemma vec_cons_eq_intro {A a a'} {n} {v v' : vec A n}
  : a = a' -> v = v' -> vcons A a n v = vcons A a' n v'.
Proof.
  intros; subst a; subst v; exact eq_refl.
Qed.

(** Here, we show that if [f] and [g] agree on all elements of [v]
    then mapping either over the vector gives the same result. This is
    the equivalent of [map_ext_in] for lists. *)

Lemma vec_map_ext {A B : Type} (f g : A -> B) {n} (v : vec A n)
  : vec_all (fun t => f t = g t) v ->
    VectorDef.map f v = VectorDef.map g v.
Proof.
  induction v; auto.
  destruct 1; eauto using vec_cons_eq_intro.
Qed.

(** * Other vector helpers

    Firstly, we prove a version of [VectorEq.eq_dec]. Our version
    doesn't need an equality function, though, which makes it a bit
    easier to use when you've just got a decidability lemma.

    Doing this from scratch seems to be necessary to be able to define
    functions using this with Fixpoint. In particular, defining this
    via [VectorEq.eq_dec] seems not to work. *)

Section dec_vec.
  Variable A : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.

  Definition dec_vec {n} (v v' : vec A n) : {v = v'} + {v <> v'}.
    refine (VectorDef.rect2 (fun _ x y => {x = y} + {x <> y})
                            (left (eq_refl))
                            (fun n v v' veq a a' => _)
                            v v').
    - destruct (decA a a') as [ <- | ].
      + destruct veq as [ <- | ].
        * left. auto.
        * right; inversion 1; auto using (inj_pair2_eq_dec _ Nat.eq_dec).
      + right; inversion 1; contradiction.
  Defined.
End dec_vec.

(** Now we have an equivalent of the [map_map] lemma that fuses
    successive mappings over lists. Unlike the list version, we
    express the composition with [compose], mainly because it's a bit
    shorter looking. *)

Lemma vec_map_map {A B C : Type} (f : A -> B) (g : B -> C) {n} (v : vec A n)
  : VectorDef.map g (VectorDef.map f v) = VectorDef.map (compose g f) v.
Proof.
  induction v; simpl; auto using f_equal.
Qed.

(** Show that [VectorDef.map] is the same as [map] once we've
    converted to a list *)

Lemma vec_map_to_list (A B : Type) (f : A -> B) n (v : vec A n)
  : VectorDef.to_list (VectorDef.map f v) = map f (VectorDef.to_list v).
Proof.
  induction v as [ | a n v IH ]; auto.
  simpl; unfold VectorDef.to_list at 1.
  auto using f_equal.
Qed.

(** * Calculating a maximum over a vector

    Note that [vec_max_at h] is basically the same thing as mapping
    [h] over the vector and then applying some sort of [vec_max]
    function (which we haven't defined). *)

Definition vec_max_at {A : Type} (h : A -> nat) {n} (v : vec A n) : nat :=
  VectorDef.fold_right (fun a n => max (h a) n) v 0.

(** While [vec_max_at h (vnil A)] is defined, it's probably not what
    you want, so it generally makes more sense to call this on
    non-empty vectors. Here, we show that it does the right thing on a
    singleton and we give a rewrite rule for applying it to a cons. *)

Lemma vec_max_at_cons {A h a n v}
  : vec_max_at h (vcons A a n v) = max (h a) (vec_max_at h v).
Proof.
  apply eq_refl.
Qed.

Lemma vec_max_at_singleton {A h a}
  : vec_max_at h (vcons A a 0 (vnil A)) = h a.
Proof.
  unfold vec_max_at; simpl.
  auto using Nat.max_0_r.
Qed.

Hint Rewrite @vec_max_at_cons : vec.
Hint Rewrite @vec_max_at_singleton : vec.

(** Let's prove some facts about the maximum over a vector. Firstly, a
    monotonicity theorem: we have a function [A -> A] which doesn't
    decrease the value of anything under [h]. Then the maximum value
    under [f] is at least as big as without. *)

Lemma vec_max_at_map_le {A} {f h n} {v : vec A n}
  : vec_all (fun x => h x <= h (f x)) v ->
    vec_max_at h v <= vec_max_at h (VectorDef.map f v).
Proof.
  induction v; auto.
  destruct 1; simpl; autorewrite with vec; auto using Nat.max_le_compat.
Qed.

Lemma vec_max_at_map_equal {A f g h n} {v : vec A n}
  : vec_all (fun x => h (f x) = g (h x)) v ->
    vec_max_at h (VectorDef.map f v) = vec_max_at (compose g h) v.
Proof.
  induction v; auto.
  destruct 1; simpl; autorewrite with vec; auto.
Qed.

Lemma vec_max_at_map_incr {A g h n} {v : vec A (S n)}
  : (forall n n', n <= n' -> g n <= g n') ->
    vec_max_at (compose g h) v = g (vec_max_at h v).
Proof.
  intros incH.
  revert n v; apply VectorDef.rectS; unfold compose.
  - intros; autorewrite with vec using auto.
  - intros a n v IH; autorewrite with vec; rewrite IH.
    auto using Nat.max_monotone.
Qed.
