Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.VectorDef.
Require Import Lists.List.
Require Import Program.Basics.

Definition vec := VectorDef.t.

Section vec_all.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint vec_all {n} (v : vec A n) :=
    match v with
    | VectorDef.nil _ => True
    | VectorDef.cons _ a _ v' => P a /\ vec_all v'
    end.

  Definition vec_all_nil : vec_all (VectorDef.nil _) := I.

  Lemma vec_all_singleton a
    : P a -> vec_all (VectorDef.cons _ a _ (VectorDef.nil _)).
  Proof.
    unfold vec_all. auto.
  Qed.

  Lemma vec_all_cons a {n} (v : vec A n)
    : P a -> vec_all v -> vec_all (VectorDef.cons _ a _ v).
  Proof.
    intros aH vH.
    unfold vec_all; fold (@vec_all n).
    exact (conj aH vH).
  Qed.

  Lemma vec_all_cons_elim {a n} {v : vec A n}
    : vec_all (VectorDef.cons _ a _ v) -> P a /\ vec_all v.
  Proof.
    auto.
  Qed.

  Lemma not_vec_all_cons0 a {n} (v : vec A n)
    : ~ P a -> ~ vec_all (VectorDef.cons _ a _ v).
  Proof.
    intro naH; unfold vec_all; fold (@vec_all n); tauto.
  Qed.

  Lemma not_vec_all_cons1 a {n} (v : vec A n)
    : ~ vec_all v -> ~ vec_all (VectorDef.cons _ a _ v).
  Proof.
    unfold vec_all at 2; fold (@vec_all n); tauto.
  Qed.
End vec_all.

Arguments vec_all {A} P {n}.
Arguments vec_all_nil {A} P.
Arguments vec_all_singleton {A P a} aH.
Arguments vec_all_cons {A P a n v} aH vH.
Arguments not_vec_all_cons0 {A P a n v} naH.
Arguments not_vec_all_cons1 {A P} a {n v} nvH.

Section dec_vec_all.
  Variable A : Type.
  Variable P : A -> Prop.
  Hypothesis decP : forall x : A, {P x} + {~ (P x)}.

  Fixpoint dec_vec_all {n} (v : vec A n) : {vec_all P v} + {~ (vec_all P v)} :=
    match v with
    | VectorDef.nil _ => left (vec_all_nil P)
    | VectorDef.cons _ a _ v' =>
      match decP a with
      | left paH => match dec_vec_all v' with
                    | left restH => left (vec_all_cons paH restH)
                    | right nrestH => right (not_vec_all_cons1 a nrestH)
                    end
      | right nH => right (not_vec_all_cons0 nH)
      end
    end.
End dec_vec_all.

Arguments dec_vec_all {A P} decP {n} v.

Section dec_vec.
  Variable A : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.

  Definition dec_vec {n} (v v' : vec A n) : {v = v'} + {v <> v'}.
    refine (VectorDef.rect2 (fun _ x y => {x = y} + {x <> y})
                            (left (eq_refl))
                            (fun n v v' veq a a' => _)
                            v v').
    - destruct (decA a a') as [ eqaH | neaH ].
      + rewrite <- eqaH; clear eqaH a'.
        destruct veq as [ eqvH | nevH ].
        * rewrite <- eqvH. apply left. exact eq_refl.
        * apply right. intro consH. inversion consH.
          exact (nevH (inj_pair2_eq_dec nat Nat.eq_dec (vec A) n v v' H0)).
      + apply right.
        intro consH. inversion consH. contradiction.
  Defined.
End dec_vec.

Lemma vec_map_map {A B C : Type} (f : A -> B) (g : B -> C) {n} (v : vec A n)
  : VectorDef.map g (VectorDef.map f v) = VectorDef.map (compose g f) v.
Proof.
  induction v as [ | a n v IH ]; try tauto.
  simpl.
  apply f_equal.
  apply IH.
Qed.

Lemma vec_map_equal {A B : Type} (f g : A -> B) {n} (v : vec A n)
  : vec_all (fun t => f t = g t) v ->
    VectorDef.map f v = VectorDef.map g v.
Proof.
  induction v as [ | a n v IH ]; try tauto.
  unfold vec_all. fold (vec_all (fun t : A => f t = g t) v).
  destruct 1 as [ eq1H eqnH ].
  specialize (IH eqnH); clear eqnH.
  simpl. rewrite eq1H, IH; exact eq_refl.
Qed.

Definition vec_max_at {A : Type} (h : A -> nat) {n} (v : vec A n) : nat :=
  VectorDef.fold_right (fun a n => max (h a) n) v 0.

Lemma vec_max_at_cons_nil {A h a}
  : vec_max_at h (VectorDef.cons A a 0 (VectorDef.nil A)) = h a.
Proof.
  unfold vec_max_at; simpl.
  auto using Nat.max_0_r.
Qed.

Lemma vec_max_at_cons {A h a n v}
  : vec_max_at h (VectorDef.cons A a n v) = max (h a) (vec_max_at h v).
Proof.
  apply eq_refl.
Qed.

Lemma vec_max_at_map_le {A} {f h n} {v : vec A n}
  : vec_all (fun x => h x <= h (f x)) v ->
    vec_max_at h v <= vec_max_at h (VectorDef.map f v).
Proof.
  induction v as [ | a n v IH ]; auto.
  intros allHC.
  destruct (vec_all_cons_elim _ _ allHC) as [ hH allH ]; clear allHC.
  specialize (IH allH); clear allH.
  simpl; rewrite !vec_max_at_cons.
  auto using Nat.max_le_compat.
Qed.

Lemma vec_max_at_map_equal {A f g h n} {v : vec A n}
  : vec_all (fun x => h (f x) = g (h x)) v ->
    vec_max_at h (VectorDef.map f v) = vec_max_at (compose g h) v.
Proof.
  induction v as [ | a n v IH ]; auto.
  intros allHC.
  destruct (vec_all_cons_elim _ _ allHC) as [ hH allH ]; clear allHC.
  specialize (IH allH); clear allH.
  simpl; rewrite !vec_max_at_cons.
  auto.
Qed.

Lemma vec_max_at_map_incr {A g h n} {v : vec A (S n)}
  : (forall n n', n <= n' -> g n <= g n') ->
    vec_max_at (compose g h) v = g (vec_max_at h v).
Proof.
  intros incH.
  revert n v; apply VectorDef.rectS.
  - intros; rewrite !vec_max_at_cons_nil; auto.
  - intros a n v IH; rewrite !vec_max_at_cons.
    rewrite IH; clear IH; unfold compose.
    apply Nat.max_monotone.
    unfold Morphisms.Proper, Morphisms.respectful; auto.
Qed.
