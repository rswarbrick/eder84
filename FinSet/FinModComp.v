(* Compositions of FinMod maps *)
Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.

Section list_mod_cons.
  Variables A B : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.
  Variable f : A -> B.

  Local Definition const_mod (b : B) : list A -> list (A * B) :=
    map (fun a => (a, b)).

  Local Lemma in_map_fst_const_mod a b l
    : In a l -> In a (map fst (const_mod b l)).
  Proof.
    unfold const_mod; rewrite map_map, map_id; auto.
  Qed.

  Local Lemma not_in_map_fst_const_mod a b l
    : ~ In a l -> ~ In a (map fst (const_mod b l)).
  Proof.
    unfold const_mod; rewrite map_map, map_id; auto.
  Qed.

  Local Lemma list_map_in_const_mod a b l
    : In a l -> list_map decA f (const_mod b l) a = b.
  Proof.
    induction l as [ | a' l IH ]; try contradiction.
    unfold const_mod; rewrite map_cons.
    unfold list_map; fold (list_map decA f).
    destruct (decA a' a) as [ -> | neH ].
    - rewrite upd_map_at; auto.
    - destruct 1 as [ -> | inH ]; try contradiction.
      rewrite upd_map_not_at; auto.
  Qed.

  Local Lemma list_map_not_in_const_mod a b l
    : ~ In a l -> list_map decA f (const_mod b l) a = f a.
  Proof.
    induction l as [ | a' l IH ]; auto.
    unfold const_mod; rewrite map_cons.
    unfold list_map; fold (list_map decA f).
    simpl. intuition.
    rewrite upd_map_not_at; auto.
  Qed.
End list_mod_cons.

Arguments const_mod {A B} b.
Arguments in_map_fst_const_mod {A B a} b {l}.
Arguments not_in_map_fst_const_mod {A B a} b {l}.
Arguments list_map_in_const_mod {A B} decA f {a} b {l}.
Arguments list_map_not_in_const_mod {A B} decA f {a} b {l}.

Section fm_precomp.
  Variables A B C : Type.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis decC : forall x y : C, {x = y} + {x <> y}.

  Variable f : A -> B.
  Variable g : B -> C.

  Hypothesis finH :
    forall b : B, exists l : list A, forall a : A, f a = b <-> In a l.

  Local Lemma exists_pre_list (lbc : list (B * C))
    : exists lac : list (A * C),
      forall a : A,
        list_map decA (compose g f) lac a =
        compose (list_map decB g lbc) f a.
  Proof.
    induction lbc as [ | bc lbc IH ].
    - exists nil; auto.
    - unfold compose at 2.
      unfold list_map at 2; fold (list_map decB g lbc).
      destruct IH as [ lac IH ].
      destruct bc as [ b c ].
      destruct (finH b) as [ la laH ].
      exists (const_mod c la ++ lac).
      intro a; specialize (IH a).
      destruct (laH a) as [ laH0 laH1 ]; clear laH.
      destruct (decB (f a) b) as [ eqH | neH ].
      + specialize (laH0 eqH); rewrite eqH; clear eqH laH1.
        rewrite upd_map_at.
        rewrite (list_map_app_in decA); auto using in_map_fst_const_mod.
        apply list_map_in_const_mod; auto.
      + assert (H : ~ In a la); auto.
        clear laH0 laH1.
        rewrite upd_map_not_at; auto.
        rewrite (list_map_app_not_in decA);
          auto using not_in_map_fst_const_mod.
  Qed.

  Lemma fin_mod_precomp g'
    : fin_mod g g' -> fin_mod (compose g f) (compose g' f).
  Proof.
    intro fmH.
    destruct (fin_mod_is_list_map decB decC fmH) as [ lbc bcH ].
    destruct (exists_pre_list lbc) as [ lac acH ].
    enough (H: forall a : A,
               list_map decA (compose g f) lac a = compose g' f a).
    - apply (fin_mod_ex (compose g' f) H), fin_mod_list_map; auto.
    - intro a; specialize (acH a); specialize (bcH (f a)).
      rewrite acH; unfold compose; auto.
  Qed.
End fm_precomp.

Arguments fin_mod_precomp {A B C} decA decB decC f {g} finH {g'}.
