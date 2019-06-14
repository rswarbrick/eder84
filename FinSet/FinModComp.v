(* Compositions of FinMod maps *)
Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.ListMod.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.FinSet.

Section list_mod_cons.
  Variables A B : Type.
  Variable f : A -> B.
  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.

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
Arguments list_map_in_const_mod {A B} f decA {a} b {l}.
Arguments list_map_not_in_const_mod {A B} f decA {a} b {l}.

Section fm_precomp.
  Variables A B C : Type.
  Variable f : A -> B.
  Variable g g' : B -> C.

  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis decC : forall x y : C, {x = y} + {x <> y}.

  Local Lemma exists_pre_list
        (lbc : list (B * C)) (P : B -> Prop)
        (finH : forall b : B, P b ->
                              exists l : list A,
                                forall a : A, f a = b <-> In a l)
    : (forall p, In p lbc -> P (fst p)) ->
      exists lac : list (A * C),
      forall a : A,
        list_map decA (compose g f) lac a =
        compose (list_map decB g lbc) f a.
  Proof.
    induction lbc as [ | bc lbc IH ].
    - exists nil; auto.
    - unfold compose at 2.
      unfold list_map at 2; fold (list_map decB g lbc).
      destruct bc as [ b c ].
      intro pH.
      assert (pIH : forall p, In p lbc -> P (fst p));
        auto with datatypes.
      destruct (finH b (pH (b, c) (in_eq _ _))) as [ la laH ]; clear pH.
      specialize (IH pIH); clear pIH; destruct IH as [ lac IH ].
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

  Hypothesis finH :
    forall b : B, g' b <> g b ->
                  exists l : list A, forall a : A, f a = b <-> In a l.

  Lemma fin_mod_precomp : fin_mod g g' -> fin_mod (compose g f) (compose g' f).
  Proof.
    intro fmH.
    destruct (fin_mod_is_list_map decB decC fmH) as [ lbc bcH ].
    destruct bcH as [ bcH neqH ].
    set (P b := g' b <> g b).
    destruct (exists_pre_list lbc P finH neqH) as [ lac acH ].
    apply (fin_mod_ex _ _ (list_map decA (compose g f) lac) _
                      (fun x => eq_refl (compose g f x))).
    - intro a; specialize (acH a); specialize (bcH (f a)).
      rewrite acH; unfold compose; auto.
    - apply fin_mod_list_map; auto.
  Qed.
End fm_precomp.

Arguments fin_mod_precomp {A B C f g g'} decA decB decC finH.

Section fm_comp.
  Variables A B C : Type.
  Variable f f' : A -> B.
  Variable g g' : B -> C.

  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis decC : forall x y : C, {x = y} + {x <> y}.

  Hypothesis finpreH :
    forall b : B, g' b <> g b ->
                  exists l : list A, forall a : A, f a = b <-> In a l.

  Hypothesis finfH : fin_mod f f'.
  Hypothesis fingH : fin_mod g g'.

  Local Definition gf := compose g f.
  Local Definition g'f' := compose g' f'.
  Local Definition g'f := compose g' f.

  Local Definition map_a (a : A) : option (mod_dom gf g'f') :=
    match decC (g'f' a) (gf a) with
    | left _ => None
    | right neH => Some (exist _ a (fun eqH => neH eqH))
    end.

  Local Definition proj0 : (mod_dom f f' + mod_dom gf g'f) -> (A + A) :=
    sumf (md_elt (f := f')) (md_elt (f := g'f)).

  Local Definition proj1 : (mod_dom gf g'f') -> A :=
    md_elt (f := g'f').

  Local Definition top_map (dd : mod_dom f f' + mod_dom gf g'f)
    : option (mod_dom gf g'f') :=
    map_a (match dd with
           | inl dg => md_elt dg
           | inr df => md_elt df
           end).

  Local Definition bot_map (aa : (A + A)) : option A :=
    option_map proj1 (map_a (match aa with
                             | inl a => a
                             | inr a => a
                             end)).

  Local Lemma natH
    : forall dd, option_map proj1 (top_map dd) = bot_map (proj0 dd).
  Proof.
    intro dd; destruct dd; reflexivity.
  Qed.

  (** Now, let's prove that [proj0] is indeed [FiniteProj]. It turns
      out that we can do this with a bare proof term: all the work was
      done in the [SymbComp.FinSet] script and above. *)

  Local Definition fin_proj0 : FiniteProj proj0 :=
    finite_sum finfH (fin_mod_precomp decA decB decC finpreH fingH).

  (** To apply the [finite_surj] lemma, we'll need to prove that the
      bottom map has the required surjectivity. This is just a finicky
      case analysis. *)

  Local Lemma surjH
    : forall d' : mod_dom gf g'f',
      exists dd : mod_dom f f' + mod_dom gf g'f,
        bot_map (proj0 dd) = Some (proj1 d').
  Proof.
    intro d'. destruct d' as [ a in_dom_a ].
    case (decB (f' a) (f a)) as [ feqH | fneH ].
    - case (decC (g'f a) (gf a)) as [ gfeqH | gfneH ];
        unfold g'f, gf, g'f', compose in *.
      + contradiction in_dom_a; clear in_dom_a.
        rewrite feqH; auto.
      + unfold mod_dom, mod_elt.
        exists (inr (exist _ a gfneH)); simpl.
        unfold bot_map, map_a.
        destruct (decC (g'f' a) (gf a)); try contradiction.
        tauto.
    - exists (inl (exist _ a fneH)); simpl.
      unfold bot_map, map_a.
      destruct (decC (g'f' a) (gf a)); try contradiction.
      tauto.
  Qed.

  (** We finally have all the bits we need to prove the theorem we
      wanted: that composition preserves the [fin_endo] property.
   *)

  Lemma compose_fin_mod : fin_mod (compose g f) (compose g' f').
  Proof.
    apply (finite_surj_option proj1 top_map bot_map fin_proj0 natH surjH).
  Qed.
End fm_comp.

Arguments compose_fin_mod {A B C f f' g g'} decA decB decC finpreH.

Section fe_comp.
  Variable A : Type.
  Variables f g : A -> A.

  Hypothesis decA : forall x y : A, {x = y} + { ~ x = y }.
  Hypothesis finF : fin_endo f.
  Hypothesis finG : fin_endo g.

  Lemma compose_fin_endo : fin_endo (compose g f).
  Proof.
    unfold fin_endo in *.
    apply (fin_mod_ex (compose id id) id
                      (compose g f) (compose g f)); auto.
    enough (forall a, g a <> id a ->
                      exists l, forall a' : A, id a' = a <-> In a' l);
      try apply (compose_fin_mod decA decA decA); auto.
    unfold id; intros a gH; exists (a :: nil).
    constructor.
    - intro eqH; rewrite eqH; auto with datatypes.
    - destruct 1; auto; try contradiction.
  Qed.
End fe_comp.

Arguments compose_fin_endo {A f g} decA finF finG.
