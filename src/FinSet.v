Require Import Lists.List.
Require Import Program.Basics.
Require Import Logic.FinFun.
Require Import Logic.Decidable.

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

Fixpoint filter_option {A : Set} (lst : list (option A)) : list A :=
  match lst with
  | nil => nil
  | cons ma lst' => match ma with
                    | Some a => a :: filter_option lst'
                    | None => filter_option lst'
                    end
  end.

Lemma full_filter_option (A : Set) (lst : list (option A))
  : Full lst -> Full (filter_option lst).
Proof.
  intro fullH.
  unfold Full. intro a.
  unfold Full in fullH; pose proof (fullH (Some a)) as aH; clear fullH.
  induction lst as [ | a0 lst IH ].
  - unfold In in aH. contradiction aH.
  - unfold In in aH; fold (@In (option A)) in aH.
    destruct aH.
    + rewrite H; clear H a0.
      unfold filter_option. fold (@filter_option A).
      unfold In. left. exact eq_refl.
    + unfold filter_option. fold (@filter_option A).
      destruct a0.
      * unfold In. fold (@In A).
        right. exact (IH H).
      * exact (IH H).
Qed.

Lemma finite_option {A : Set}
  : Finite (option A) -> Finite A.
Proof.
  intro H.
  unfold Finite in H; destruct H as [ lst fullH ].
  unfold Finite. exists (filter_option lst).
  apply full_filter_option. exact fullH.
Qed.
