Require Import Lists.List.
Require Import Program.Basics.
Require Import Logic.FinFun.
Require Import Logic.Decidable.

(* The disjoint sum of two finite sets is finite *)
Lemma finite_sum {A B : Set}
      : Finite A -> Finite B -> Finite (A + B).
Proof.
  (* Expand finiteness of A, B to get the lists *)
  intros FA FB.
  unfold Finite in FA; destruct FA as [ la la_full ].
  unfold Finite in FB; destruct FB as [ lb lb_full ].
  (* Expand finiteness of A+B and then full to get an elt of A+B to hit *)
  unfold Finite.
  exists ((map inl la) ++ (map inr lb)).
  unfold Full. intro ab.
  (* Proceed by case analysis: is ab in A or B? *)
  destruct ab as [ a | b ].
  - clear lb_full.
    apply in_or_app; left.
    apply in_map.
    unfold Full in la_full; apply la_full.
  - clear la_full.
    apply in_or_app; right.
    apply in_map.
    unfold Full in lb_full; apply lb_full.
Qed.

(* If A is finite and surjects onto B then B is finite. *)
Lemma finite_surj {A B : Set} (f : A -> B)
  : Finite A -> Surjective f -> Finite B.
Proof.
  intros finA surjF.
  unfold Finite in finA. destruct finA as [ lst fullH ].
  unfold Finite. exists (map f lst).
  unfold Full. intro b.
  unfold Surjective in surjF.
  case (surjF b). intro a; clear surjF.
  intro fa. rewrite <- fa; clear fa.
  apply in_map; clear b f B.
  unfold Full in fullH. apply fullH.
Qed.

(* We'd like to prove that if A injects into B and B is finite then A
   is itself finite. This is slightly difficult, because we have to
   construct the list.

   First we define a way to construct this list of elements if we have
   a decidability proof that says an element b is either in the image
   of f or not. In fact, we ask for a pseudo-inverse, and then use a
   Haskell-style cat_maybes function.

 *)
Fixpoint cat_maybes {A B : Set} (f : A -> option B) (lst : list A) : list B :=
  match lst with
  | nil => nil
  | cons a lst' => match f a with
                  | Some b => b :: cat_maybes f lst'
                  | None => cat_maybes f lst'
                  end
  end.

Lemma cat_maybes_inv (A B : Set) (f : A -> option B) (a : A) (lst : list A)
  : cat_maybes f (a :: lst) = match f a with
                              | Some b => b :: cat_maybes f lst
                              | None => cat_maybes f lst
                              end.
Proof.
  unfold cat_maybes at 1.
  fold (@cat_maybes A B).
  apply eq_refl.
Qed.

(* full_inv deals with the case where I have maps f, inv such that inv
   is a left-inverse for f, but mapping to option A so that we don't
   need choice when we don't have a pre-image.

   The first proposition is asking that inv really is a left inverse
   for (f o Some). Then we say that if lst lists the elements of B, we
   can create a full list of the elements of A by discarding the Nones
   from the list you get by mapping inv over lst.
 *)
Lemma full_inv (A B : Set) (f : A -> B) (inv : B -> option A) (lst : list B)
  : (forall a, inv (f a) = Some a) -> Full lst -> Full (cat_maybes inv lst).
Proof.
  intros invH fullH.
  unfold Full. intro a.
  unfold Full in fullH; pose proof (fullH (f a)) as in_fa_H; clear fullH.
  induction lst as [ | a0 lst IH ].
  - unfold In in in_fa_H. contradiction in_fa_H.
  - (* in_fa_H is now In (f a) (a0 :: lst) *)
    rewrite cat_maybes_inv.
    apply in_inv in in_fa_H.
    destruct in_fa_H as [ eqH | ].
    + (* f a = a0 *)
      rewrite eqH.
      rewrite invH.
      apply in_eq.
    + (* In (f a) lst *)
      apply IH in H; clear IH.
      case (inv a0).
      * intro aa. apply in_cons. exact H.
      * exact H.
Qed.

Lemma finite_inj {A B : Set} (f : A -> B) (g : B -> option A)
  : Finite B -> (forall a, g (f a) = Some a) -> Finite A.
Proof.
  intros finB invG.
  unfold Finite in finB; destruct finB as [ bs fullB ].
  unfold Finite.
  exists (cat_maybes g bs).
  apply (full_inv _ _ _ _ _ invG).
  exact fullB.
Qed.

Lemma finite_option {A : Set}
  : Finite (option A) -> Finite A.
Proof.
  intro finOp.
  apply (finite_inj Some id finOp).
  intro a.
  unfold id.
  exact eq_refl.
Qed.
