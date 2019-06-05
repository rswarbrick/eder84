(**

  This library deals with "natural maps", a slight shorthand for the
  situation where you have a commuting square of maps and regard (say)
  the horizontal maps as being some sort of natural transformation
  between the vertical ones.

 *)

Require Import Program.Basics.

Set Implicit Arguments.

Section nat_map.
  Variables A B C D: Type.
  Variable p : A -> B.
  Variable q : C -> D.

  Definition is_nat_map (fg : (A -> C) * (B -> D)) : Prop :=
    forall a : A, q (fst fg a) = snd fg (p a).

  Definition nat_map := sig is_nat_map.

  Definition nm_top (fg : nat_map) :=
    match fg with
      exist _ (f, _) _ => f
    end.

  Definition nm_bot (fg : nat_map) :=
    match fg with
      exist _ (_, g) _ => g
    end.

  Lemma nat_map_nat (fg : nat_map) (a : A)
    : q (nm_top fg a) = nm_bot fg (p a).
  Proof.
    destruct fg as [ pr H ].
    destruct pr as [ f g ].
    unfold is_nat_map in H.
    unfold nm_top, nm_bot.
    specialize (H a). auto.
  Qed.
End nat_map.

Definition sumf {A A' B B'} (f : A -> B) (g : A' -> B') (aa : A + A')
  : B + B' :=
  match aa with
  | inl a => inl (f a)
  | inr a' => inr (g a')
  end.

Definition nat_map_inl (A B C D : Type) (p : A -> B) (q : C -> D)
  : nat_map p (sumf p q) := exist (is_nat_map p (sumf p q))
                                  (inl, inl) (fun _ => eq_refl).

Definition nat_map_inr (A B C D : Type) (p : A -> B) (q : C -> D)
  : nat_map p (sumf q p) := exist (is_nat_map p (sumf q p))
                                  (inr, inr) (fun _ => eq_refl).

Definition nat_map_v (A B : Type) (p : A -> B)
  : nat_map p p := exist (is_nat_map p p) (id, id) (fun _ => eq_refl).

Definition nat_map_h (A B : Type) (f : A -> B)
  : nat_map id id := exist (is_nat_map id id) (f, f) (fun _ => eq_refl).

Lemma is_nat_map_comp_h (A B C D E F : Type)
      (p : A -> B) (q : C -> D) (r : E -> F)
      (m0 : nat_map p q) (m1 : nat_map q r)
  : is_nat_map p r (compose (nm_top m1) (nm_top m0),
                    compose (nm_bot m1) (nm_bot m0)).
Proof.
  destruct m0 as [ pr0 H0 ]; destruct pr0 as [ f0 g0 ].
  destruct m1 as [ pr1 H1 ]; destruct pr1 as [ f1 g1 ].
  unfold compose, is_nat_map in *. intro a. simpl.
  specialize (H0 a); simpl in H0.
  specialize (H1 (f0 a)); simpl in H1.
  rewrite H1, H0.
  exact eq_refl.
Qed.

Definition nat_map_comp_h (A B C D E F : Type)
           (p : A -> B) (q : C -> D) (r : E -> F)
           (m0 : nat_map p q) (m1 : nat_map q r)
  : nat_map p r := exist _ (compose (nm_top m1) (nm_top m0),
                            compose (nm_bot m1) (nm_bot m0))
                         (is_nat_map_comp_h m0 m1).

Lemma is_nat_map_comp_v (A B C D E F : Type)
      (p : A -> B) (q : C -> D) (p' : B -> E) (q' : D -> F)
      (m0 : nat_map p q) (m1 : nat_map p' q')
  : (forall b, nm_top m1 b = nm_bot m0 b) ->
    is_nat_map (compose p' p) (compose q' q) (nm_top m0, nm_bot m1).
Proof.
  intro eqH.
  destruct m0 as [ pr0 H0 ]; destruct pr0 as [ f0 g0 ].
  destruct m1 as [ pr1 H1 ]; destruct pr1 as [ f1 g1 ].
  unfold compose, is_nat_map in *. intro a. simpl.
  simpl in *.
  specialize (H0 a).
  specialize (H1 (p a)).
  specialize (eqH (p a)).
  rewrite H0, <- eqH, H1.
  exact eq_refl.
Qed.

Definition nat_map_comp_v (A B C D E F : Type)
           (p : A -> B) (q : C -> D) (p' : B -> E) (q' : D -> F)
           (m0 : nat_map p q) (m1 : nat_map p' q')
           (eqH : forall b, nm_top m1 b = nm_bot m0 b)
  : nat_map (compose p' p) (compose q' q) :=
  exist _ (nm_top m0, nm_bot m1) (is_nat_map_comp_v m0 m1 eqH).

Definition nat_map_diag (A B C : Type) (f : A -> B) (g : B -> C)
  : nat_map f g := exist (is_nat_map f g) (f, g) (fun _ => eq_refl).

Definition nat_map_some (A B : Type) (p : A -> B)
  : nat_map p (option_map p) := exist (is_nat_map p (option_map p))
                                      (Some, Some) (fun _ => eq_refl).

(*

  The notion of injectivity that we want is injectivity on the lower
  map. If [p] is surjective (which is usually the case in settings we
  care about), this is exactly asking that [nm_bot f] is injective. In
  general, we just ask that it's injective on the image of [p].

*)
Definition inj_nat_map
           (A B C D : Type) (p : A -> B) (q : C -> D)
           (f : nat_map p q) :=
  forall a a',
    nm_bot f (p a) = nm_bot f (p a') -> p a = p a'.
