Require Import Lists.List.
Require Import Logic.Eqdep_dec.
Require Import PeanoNat.
Require Vectors.Fin.
Require Vectors.VectorDef.
Require Import Program.Basics.

Require Import SymbComp.VecUtils.
Require Import SymbComp.FinMod.
Require Import SymbComp.ListMod.

Definition vec := VectorDef.t.

Section Term.
  Variable V : Type.
  Variable F : Type.
  Variable a : F -> nat.

  Inductive Term : Type :=
  | varTerm : V -> Term
  | funTerm (f : F) (ts : vec Term (a f)) : Term.

  Section Term_ind'.
    Variable P : Term -> Prop.
    Hypothesis vH : forall v, P (varTerm v).
    Hypothesis fH : forall f, forall ts, vec_all P ts -> P (funTerm f ts).

    Fixpoint Term_ind' (t : Term) : P t :=
      match t with
      | varTerm v => vH v
      | funTerm f ts =>
        fH f ts
           (VectorDef.t_rect Term (fun _ v => vec_all P v)
                             (vec_all_nil P)
                             (fun t n v => vec_all_cons (Term_ind' t))
                             (a f) ts)
      end.
  End Term_ind'.

  Section Term_rect'.
    Variable P : Term -> Type.
    Variable Q : forall n, vec Term n -> Type.

    Variable varH : forall v, P (varTerm v).
    Variable funH : forall f, forall ts, Q _ ts -> P (funTerm f ts).
    Variable qnilH : Q _ (VectorDef.nil _).
    Variable qconsH : forall t n ts,
        P t -> Q n ts -> Q _ (VectorDef.cons _ t _ ts).

    Fixpoint Term_rect' (t : Term) : P t :=
      match t with
      | varTerm v => varH v
      | funTerm f ts =>
        funH f ts
             (VectorDef.t_rect Term Q qnilH
                               (fun t' n ts' =>
                                  qconsH t' n ts' (Term_rect' t'))
                               (a f) ts)
      end.
  End Term_rect'.

  Lemma varTerm_ne_funTerm v f ts : varTerm v <> funTerm f ts.
  Proof.
    intros eqH. inversion eqH.
  Qed.

  Section DecTerm.
    (* Equality in Term is decidable if it is in V and F *)
    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    Fixpoint decTerm (x y : Term) : {x = y} + {x <> y}.
      refine (match x, y with
              | varTerm v, varTerm v' => _
              | varTerm v, funTerm f ts => _
              | funTerm f ts, varTerm v => _
              | funTerm f ts, funTerm f' ts' => _
              end
             ).
      - destruct (decV v v') as [ eqH | neH ].
        + exact (left (f_equal varTerm eqH)).
        + enough (H: varTerm v <> varTerm v');
            try (exact (right H)).
          injection; tauto.
      - exact (right (varTerm_ne_funTerm v f ts)).
      - exact (right (not_eq_sym (varTerm_ne_funTerm v f ts))).
      - destruct (decF f f') as [ feqH | fneH ].
        + revert ts'. rewrite <- feqH. clear feqH; intro ts'.
          destruct (dec_vec Term decTerm ts ts') as [ tseqH | tsneH ].
          * apply left. apply f_equal. exact tseqH.
          * apply right. intro funH. inversion funH.
            exact (tsneH (inj_pair2_eq_dec
                            F decF (fun f => vec Term (a f)) f ts ts' H0)).
        + enough (H: funTerm f ts <> funTerm f' ts');
            try (exact (right H)).
          injection; tauto.
    Qed.
  End DecTerm.

  (* Eder's paper talks about substitutions as if they are
     endomorphisms on Term, but he is only interested in the
     endomorphisms that come about from actual substitutions: maps
     from variables to terms which may or may not themselves be
     variables.

     Let's start by defining the induced endomorphism on Term that
     comes from a substitution.  *)
  Fixpoint subst_endo (s : V -> Term) (t : Term) : Term :=
    match t with
    | varTerm v => s v
    | funTerm f ts => funTerm f (VectorDef.map (subst_endo s) ts)
    end.

  (* The induced endomorphism from varTerm is the identity *)
  Lemma subst_endo_varTerm {t}
    : subst_endo varTerm t = t.
  Proof.
    revert t; apply Term_ind'; try reflexivity.
    intros f ts allH.
    unfold subst_endo; fold subst_endo.
    apply f_equal.
    induction ts as [ | t n ts IH ]; try reflexivity.
    destruct allH as [ tH tsH ].
    specialize (IH tsH); clear tsH.
    unfold VectorDef.map; fold (@VectorDef.map Term _ (subst_endo varTerm)).
    rewrite IH, tH.
    exact eq_refl.
  Qed.

  Lemma subst_endo_ex {s s' t}
    : (forall v, s v = s' v) -> subst_endo s t = subst_endo s' t.
  Proof.
    intro eqH.
    revert t; apply Term_ind'.
    - intro v; specialize (eqH v). tauto.
    - intros f ts allH.
      unfold subst_endo; fold subst_endo.
      apply f_equal.
      apply vec_map_equal.
      exact allH.
  Qed.

  (* Eder is only interested in substitutions that map only finitely
     many variables differently from [varTerm] *)
  Definition fin_subst := fin_mod varTerm.

  (* The induced endomorphism from varTerm (the identity) is obviously
     a finite substitution *)
  Lemma fin_subst_varTerm : fin_subst varTerm.
  Proof.
    unfold fin_subst.
    apply fin_mod_i.
  Qed.

  (* Let's prove that the composition of two induced endomorphisms is
     itself induced. *)
  Definition var_restriction (f : Term -> Term) (v : V) : Term :=
    f (varTerm v).

  Lemma comp_subst_is_subst (sigma tau : V -> Term) (t : Term)
    : compose (subst_endo sigma) (subst_endo tau) t =
      subst_endo (var_restriction
                    (compose (subst_endo sigma) (subst_endo tau))) t.
  Proof.
    revert t; apply Term_ind'.
    - intros; unfold compose, var_restriction; simpl; exact eq_refl.
    - intros f ts IH.
      unfold compose, subst_endo; fold subst_endo.
      apply f_equal.
      rewrite vec_map_map.
      fold (compose (subst_endo sigma) (subst_endo tau)).
      apply vec_map_equal.
      exact IH.
  Qed.

  (* Composition is more of a faff. The substitution that induces the
     composition of two induced endomorphisms is actually easiest to
     define by concatenating lists *)

  Definition comp_subst (sigma tau : V -> Term) :=
    compose (compose (subst_endo sigma) (subst_endo tau)) varTerm.

  Section fin_comp_subst.
    Variables sigma tau : V -> Term.
    Variable sl tl : list (V * Term).

    Hypothesis decV : forall x y : V, {x = y} + {x <> y}.
    Hypothesis decF : forall x y : F, {x = y} + {x <> y}.

    Hypothesis sH : forall v : V, sigma v = list_map decV varTerm sl v.
    Hypothesis tH : forall v : V, tau v = list_map decV varTerm tl v.

    (* A list inducing the correct correct composed map ([compose
       sigma tau]) is given by first mapping all the variables to
       where tau would send them and then applying the induced map
       from sigma to the resulting term.

       Variables that weren't moved by tau get mapped by sigma, which
       we can express by shoving them to the end of the list.
     *)
    Local Definition stl : list (V * Term) :=
      app (map (fun p => (fst p, subst_endo sigma (snd p))) tl)
          sl.

    Lemma stl_map_v (v : V)
      : list_map decV varTerm stl v = comp_subst sigma tau v.
    Proof.
      specialize (tH v).
      unfold comp_subst, compose, subst_endo at 2, stl.
      set (pmap := (fun p : V * Term => (fst p, subst_endo sigma (snd p)))).
      revert tau tH.
      induction tl as [ | p tl' IH ].
      - intros; rewrite tH; clear tH; simpl; auto.
      - intros tau tH.
        clear tl; rename tl' into tl.
        rewrite (map_cons pmap p tl), <- app_comm_cons.
        destruct p as [ v' sv' ].
        destruct (decV v' v) as [ veqH | vneH ].
        + rewrite veqH in *; clear v' veqH.
          simpl in tH; rewrite upd_map_at in tH.
          unfold pmap; simpl; rewrite upd_map_at.
          rewrite tH. tauto.
        + unfold pmap at 1; simpl.
          rewrite (upd_map_not_at decV _ _ (not_eq_sym vneH)).
          simpl in tH.
          rewrite (upd_map_not_at decV _ _ (not_eq_sym vneH)) in tH.
          apply IH.
          apply tH.
    Qed.
  End fin_comp_subst.

  Lemma fin_subst_comp sigma tau
    : (forall x y : V, {x = y} + {x <> y}) ->
      (forall x y : F, {x = y} + {x <> y}) ->
      fin_subst sigma -> fin_subst tau -> fin_subst (comp_subst sigma tau).
  Proof.
    unfold fin_subst at 1 2.
    intros decV decF fmS fmT.
    set (decT := (decTerm decV decF)).
    destruct (fin_mod_is_list_map decV decT fmS) as [ sl slH ].
    destruct (fin_mod_is_list_map decV decT fmT) as [ tl tlH ].
    unfold comp_subst, compose.
    apply (fin_mod_ex _ (stl_map_v sigma tau sl tl decV slH tlH)).
    apply (fin_mod_list_map decV varTerm decT).
  Qed.

  Lemma comp_subst_idl {sigma v} : comp_subst varTerm sigma v = sigma v.
  Proof.
    unfold comp_subst, compose.
    unfold subst_endo at 2.
    rewrite subst_endo_varTerm.
    exact eq_refl.
  Qed.

  Lemma comp_subst_idr {sigma v} : comp_subst sigma varTerm v = sigma v.
  Proof.
    unfold comp_subst, compose, subst_endo.
    exact eq_refl.
  Qed.

  Lemma comp_subst_assoc {s1 s2 s3 v}
    : comp_subst s1 (comp_subst s2 s3) v = comp_subst (comp_subst s1 s2) s3 v.
  Proof.
    unfold comp_subst, compose; simpl.
    generalize (s3 v); clear s3 v.
    apply Term_ind'; try reflexivity.
    intros f ts IH.
    unfold subst_endo at 2; fold subst_endo.
    unfold subst_endo at 1; fold subst_endo.
    unfold subst_endo at 3; fold subst_endo.
    apply f_equal.
    rewrite vec_map_map.
    apply vec_map_equal.
    exact IH.
  Qed.

  Lemma fin_subst_restrict {s P} (decP : forall v : V, {P v} + {~ P v})
    : fin_subst s -> fin_subst (restrict_map varTerm P decP s).
  Proof.
    unfold fin_subst.
    apply restrict_preserves_fin_mod.
  Qed.

  Lemma comp_subst_ex1 {r r' s} (v : V)
    : (forall v, r v = r' v) -> comp_subst r s v = comp_subst r' s v.
  Proof.
    intro eqH.
    unfold comp_subst, compose.
    rewrite (subst_endo_ex eqH).
    tauto.
  Qed.

  Lemma comp_subst_ex2 {r s s'} (v : V)
    : (forall v, s v = s' v) -> comp_subst r s v = comp_subst r s' v.
  Proof.
    intro eqH.
    unfold comp_subst, compose.
    rewrite (subst_endo_ex eqH).
    tauto.
  Qed.

End Term.

Arguments comp_subst {V F a} sigma tau.
