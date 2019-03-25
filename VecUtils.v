Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.VectorDef.

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
