(* Compositions of FinMod maps *)
Require Import Lists.List.
Require Import Program.Basics.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.ListMod.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.ProjSet.

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

(* Convert a mod_dom element to a graph pair (x, f x) *)
Local Definition mod_dom_to_pr {A B : Type} {i f : A -> B}
  : mod_dom i f -> A * B :=
  fun d => (proj1_sig d, f (proj1_sig d)).

Lemma list_graph_from_doms {A B : Type} {i f : A -> B} (finH : fin_mod i f)
  : map mod_dom_to_pr (proj1_sig finH) = fin_mod_list_graph finH.
Proof.
  unfold fin_mod_list_graph; simpl.
  destruct finH as [ ds fullH ]; simpl.
  unfold ListMod.list_graph; rewrite map_map; auto.
Qed.

Local Definition is_pre_list
      {A B : Type} (f : A -> B) (l : list A) (b : B) : Prop :=
  forall a : A, f a = b <-> In a l.

Section fm_precomp.
  Variables A B C : Type.
  Variable f : A -> B.
  Variable g g' : B -> C.

  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis decC : forall x y : C, {x = y} + {x <> y}.

  Variable get_pre : mod_dom g g' -> list A.
  Variable get_preH : forall d, is_pre_list f (get_pre d) (proj1_sig d).

  (* Create a list of pairs for [compose g' f] given a (full) list of
     dom_elts of g' *)
  Local Fixpoint pre_compose (ds : list (mod_dom g g')) : list (A * C) :=
    match ds with
    | nil => nil
    | cons d ds' => app (map (fun a => (a, (g' (proj1_sig d)))) (get_pre d))
                        (pre_compose ds')
    end.

  (* Show that the pre_compose function actually computes the right thing *)
  Local Lemma list_map_pre_compose (ds : list (mod_dom g g'))
    : forall a : A,
        list_map decA (compose g f) (pre_compose ds) a =
        compose (list_map decB g (map mod_dom_to_pr ds)) f a.
  Proof.
    intro a.
    unfold compose at 2.
    induction ds as [ | d ds IH ]; auto.
    simpl.
    destruct (decB (f a) (proj1_sig d)) as [ eqH | neqH ].
    - assert (In a (get_pre d)) as inH;
        [ rewrite <- (get_preH d a); auto | ].
      rewrite (list_map_app_in decA (compose g f) _ _ a);
        [ | rewrite map_map, map_id; auto ].
      fold (const_mod (g' (proj1_sig d)) (get_pre d)).
      rewrite list_map_in_const_mod; auto.
      unfold mod_dom_to_pr. rewrite <- eqH, upd_map_at; auto.
    - assert (~ In a (get_pre d)) as notinH;
        [ destruct (get_preH d a); auto | ].
      rewrite (list_map_app_not_in decA (compose g f) _ _ a);
        [ | rewrite map_map, map_id; auto ].
      unfold mod_dom_to_pr at 1; rewrite upd_map_not_at; auto.
  Qed.

  Lemma fin_mod_precomp : fin_mod g g' -> fin_mod (compose g f) (compose g' f).
  Proof.
    intro finH.
    apply (fin_mod_ex _ _ (list_map decA (compose g f)
                                    (pre_compose (proj1_sig finH)))
                      _ (fun a => eq_refl)).
    - intro a.
      rewrite list_map_pre_compose; unfold compose.
      generalize (f a); intro b; clear a.
      rewrite (list_graph_from_doms finH).
      fold (fin_mod_list_map decB finH).
      rewrite <- fin_mod_is_list_map; auto.
    - apply (list_map_is_fin_mod decA (compose g f) decC).
  Qed.
End fm_precomp.

Arguments fin_mod_precomp {A B C f g g'} decA decB decC get_pre get_preH finH.

Section fm_comp.
  Variables A B C : Type.
  Variable f f' : A -> B.
  Variable g g' : B -> C.

  Hypothesis decA : forall x y : A, {x = y} + {x <> y}.
  Hypothesis decB : forall x y : B, {x = y} + {x <> y}.
  Hypothesis decC : forall x y : C, {x = y} + {x <> y}.

  Variable get_pre : mod_dom g g' -> list A.
  Variable get_preH : forall d, is_pre_list f (get_pre d) (proj1_sig d).

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
    finite_sum finfH (fin_mod_precomp decA decB decC get_pre get_preH fingH).

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

Arguments compose_fin_mod {A B C f f' g g'} decA decB decC get_pre get_preH.

Section fe_comp.
  Variable A : Type.
  Variables g f : A -> A.

  Hypothesis decA : forall x y : A, {x = y} + { ~ x = y }.
  Hypothesis finG : fin_endo g.
  Hypothesis finF : fin_endo f.

  Local Definition get_pre_id (d : mod_dom id g) : list A :=
    cons (proj1_sig d) nil.

  Local Lemma get_pre_idH (d : mod_dom id g)
    : is_pre_list id (get_pre_id d) (proj1_sig d).
  Proof.
    destruct d as [ a modH ]; unfold get_pre_id; simpl.
    intro b; split; unfold id.
    - intro baH; rewrite baH; auto with datatypes.
    - destruct 1 as [ | innilH ]; auto.
      contradiction innilH.
  Qed.

  Lemma compose_fin_endo : fin_endo (compose g f).
  Proof.
    unfold fin_endo in *.
    apply (fin_mod_ex (compose id id) id
                      (compose g f) (compose g f)); auto.
    apply (compose_fin_mod decA decA decA
                           get_pre_id get_pre_idH); auto.
  Qed.
End fe_comp.

Arguments compose_fin_endo {A g f} decA finG finF.
