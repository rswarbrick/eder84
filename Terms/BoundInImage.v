Require Import Lists.List.
Require Import Decidable.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.ProjSet.

Require Import Top.Terms.Term.
Require Import Top.Terms.Subst.
Require Import Top.Terms.FreeVars.

(* for dec_proc_to_sumbool: probably refactor this! *)
Require Import Top.Terms.VecUtils.

(**

    At the start of Lemma 2.10, Eder investigates which variables are
    bound in the image of some substitution. That is, he looks at the
    set of terms that are the image of some variable and then asks
    which variables don't appear as free variables in any of them.

    If the substitution is finite, it fixes most variables and these
    ones are definitely not bound in the image: the image will contain
    a term for the original variable, which definitely contains itself
    as a free variable! However a variable that isn't fixed isn't
    necessarily bound: it, or some other variable might be mapped to a
    term that contains it.

    In this module, we define a type for the variables that are bound
    in the image of a substitution. We then define a decision
    procedure for checking whether a variable is so bound and check
    it's correctness (this turns out to be quite hard!).

    Finally, we show that the variables bound in the image of a finite
    substitution are a finite set.

*)

Section fin_subst_bound_vars.
  Variable L : lType.
  Variable sigma : Subst L.
  Hypothesis sigma_finiteH : fin_subst L sigma.

  Definition is_bound_in_image (v : Term.V L) : Prop :=
    ~ termset_fv v (subst_im L sigma).

  Definition bound_in_image : Type := sig is_bound_in_image.

  Definition bound_image_var : bound_in_image -> Term.V L := @proj1_sig _ _.

  (**

    To prove that the projection is finite, we'd need a list of bound
    variables. We've almost got that, by looking at the variables that are in
    the domain of sigma: this is a finite list by [sigma_finiteH]. But some of
    those might still end up free (suppose sigma is actually a variable
    permutation).

    Fortunately, we have a finite list of ways in which a variable in the
    domain of sigma can turn out to be free, so we can write a decidable
    function to check that it isn't. Use [check_bound_in_image] with a full
    list of elements for the domain of sigma (which exists because it's a
    [fin_subst]).

   *)

  Fixpoint check_bound_in_image_lst
           (decV : forall v w : Term.V L, {v = w} + {v <> w})
           (v : Term.V L) (vs : list (Term.V L))
    : bool :=
    match vs with
    | nil => true
    | cons w vs' => andb (negb (check_term_fv decV v (sigma w)))
                         (check_bound_in_image_lst decV v vs')
    end.

  Definition check_bound_in_image
             (decV : forall v w : Term.V L, {v = w} + {v <> w})
             (vs : list (Term.V L)) (v : Term.V L)
    : bool :=
    andb (if dec_mod_elt_varTerm decV sigma v then true else false)
         (check_bound_in_image_lst decV v vs).

  (**

    What does [check_bound_in_image] actually check? This first lemma turns
    (not) bound in image into something that looks a bit more like the shape of
    [check_bound_in_image]. The point is that we know any variable that is
    fixed by sigma is free in the image of sigma (because it appears as
    itself). A variable that isn't fixed by sigma might be free, so long as
    neither it or any other variable is mapped to something containing it.

   *)
  Lemma free_in_image_iff_dom_elt_hits_it
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        v
    : termset_fv v (subst_im L sigma) <->
      (sigma v = varTerm L v \/
       (exists w, mod_elt (varTerm L) sigma w /\
                  term_fv v (sigma w))).
  Proof.
    split.
    - destruct 1 as [ t [ imH fvH ] ].
      destruct imH as [ w twH ].
      rewrite twH in fvH; clear twH t.
      destruct (dec_mod_elt_varTerm decV sigma v) as [ eltH | ].
      + right; exists w; split; auto.
        destruct (dec_mod_elt_varTerm decV sigma w) as [ | eqwH ]; auto.
        rewrite eqwH in fvH.
        simpl in fvH; rewrite <- fvH; auto.
      + left; auto.
    - destruct 1 as [ fixedH | [ w [ eltH fvH ] ] ].
      + exists (sigma v).
        split.
        * exists v; auto.
        * rewrite fixedH; simpl; auto.
      + exists (sigma w); split; auto.
        exists w; auto.
  Qed.

  (** The lemma above will be enough to show that [check_bound_in_image] is
      correct if [check_bound_in_image_lst] is. For that, we prove each
      direction separately by induction over the list. *)

  Lemma check_bound_in_image_lst_false_intro
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (v w : Term.V L)
        (freeH : term_fv v (sigma w))
        (vs : list (Term.V L))
    : In w vs -> check_bound_in_image_lst decV v vs = false.
  Proof.
    induction vs as [ | u vs IH ]; try contradiction.
    destruct 1 as [ uwH | inH ].
    - rewrite <- uwH in freeH.
      apply Bool.andb_false_intro1.
      rewrite Bool.negb_false_iff.
      rewrite <- (check_term_fv_correct decV v (sigma u)).
      auto.
    - specialize (IH inH); clear inH.
      simpl; apply Bool.andb_false_intro2; auto.
  Qed.

  Lemma check_bound_in_image_lst_false_elim
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (v : Term.V L)
        (vs : list (Term.V L))
    : check_bound_in_image_lst decV v vs = false ->
      exists w, In w vs /\ term_fv v (sigma w).
  Proof.
    induction vs as [ | u vs IH ].
    - intro H; contradiction (Bool.diff_true_false H).
    - intro bd_falseH; simpl in bd_falseH.
      case (Bool.andb_false_elim _ _ bd_falseH); clear bd_falseH.
      + rewrite Bool.negb_false_iff.
        rewrite <- (check_term_fv_correct decV v (sigma u)).
        eauto with datatypes.
      + intro H; destruct (IH H) as [ w [ inH fvH ] ].
        eauto with datatypes.
  Qed.

  (** We can finally show that [check_bound_in_image] does what we want. After
      a bit of rewriting, the proof starts by applying
      [free_in_image_iff_dom_elt_hits_it] to split up the proposition
      part. Then there's a certain amount of unpacking on each side of the iff
      until we can finally apply the intro/elim rules we just proved. *)

  Lemma check_bound_in_image_correct
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (dom_elts : list (mod_dom (varTerm L) sigma))
        (fullH : FullProj md_elt dom_elts)
        (v : Term.V L)
    : is_bound_in_image v <->
      is_true (check_bound_in_image decV (map md_elt dom_elts) v).
  Proof.
    unfold is_bound_in_image.
    unfold is_true.
    rewrite <- Bool.not_false_iff_true.
    apply not_iff_compat.
    rewrite (free_in_image_iff_dom_elt_hits_it decV v).
    split.
    - destruct 1 as [ fixedH | exH ]; unfold check_bound_in_image.
      + case (dec_mod_elt_varTerm decV sigma v); [ contradiction | auto ].
      + apply Bool.andb_false_intro2.
        destruct exH as [ w [ eltwH fvH ] ].
        assert (In w (map md_elt dom_elts)) as inH;
          [ exact (fullH (exist _ w eltwH)) | ]; clear fullH eltwH.
        apply (check_bound_in_image_lst_false_intro decV v w fvH _ inH).
    - intro check_falseH.
      case (Bool.andb_false_elim _ _ check_falseH); simpl; clear check_falseH.
      + destruct (dec_mod_elt_varTerm decV sigma v); auto.
        intro tfH; contradiction Bool.diff_true_false.
      + intro check_lstH.
        destruct (check_bound_in_image_lst_false_elim _ _ _ check_lstH)
          as [ w [ inH fvH ] ].
        right; exists w; split; auto.
        rewrite (in_map_iff md_elt dom_elts w) in inH.
        destruct inH as [ md [ md_eltH inH ] ].
        rewrite <- md_eltH.
        unfold md_elt; apply proj2_sig.
  Qed.

  (** With this, we can finally prove that [is_bound_in_image] is
      decidable. We have to pack this into a sumbool as shown so that
      we can use it to define the maps in the finiteness proof
      below. *)
  Definition dec_bound_in_image
             (decV : forall v w : Term.V L, {v = w} + {v <> w})
             (dom_elts : list (mod_dom (varTerm L) sigma))
             (fullH : FullProj md_elt dom_elts)
             (v : Term.V L)
    : {is_bound_in_image v} + {~ is_bound_in_image v} :=
    dec_proc_to_sumbool (check_bound_in_image_correct decV dom_elts fullH) v.

  (** We have a finite list of variables in the domain of sigma. We
      know that every variable that is bound in the image is one of
      these variables, so we have a surjection from the domain of
      sigma to the option type for variables that are bound in the
      image (mapping those that turn out not to be to None).

      The "downstairs" map (on variables) is the identity on those
      that are bound in the image and maps others to None.

   *)
  Local Definition lo_map
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (elts : list (Term.V L))
        (v : Term.V L)
    : option (Term.V L) :=
    if check_bound_in_image decV elts v then Some v else None.

  (** For the "upstairs" map, we need the full decision check (because
      we need to know the object we make is indeed bound). *)
  Local Definition hi_map
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        (dom_elts : list (mod_dom (varTerm L) sigma))
        (fullH : FullProj md_elt dom_elts)
        (dom_elt : mod_dom (varTerm L) sigma)
    : option bound_in_image :=
    match dec_bound_in_image decV dom_elts fullH (md_elt dom_elt) with
    | left bdH => Some (exist _ (proj1_sig dom_elt) bdH)
    | right _ => None
    end.

  Lemma not_fixed_if_bound_in_image
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
        v
    : is_bound_in_image v -> mod_elt (varTerm L) sigma v.
  Proof.
    intros boundH fixedH.
    destruct (free_in_image_iff_dom_elt_hits_it decV v) as [ _ H ].
    specialize (H (or_introl fixedH)).
    exact (boundH H).
  Qed.

  Lemma finite_bound_in_image
        (decV : forall v w : Term.V L, {v = w} + {v <> w})
    : FiniteProj bound_image_var.
  Proof.
    destruct sigma_finiteH as [ dom_elts fullH ].
    apply (finite_surj_option bound_image_var
                              (hi_map decV dom_elts fullH)
                              (lo_map decV (map md_elt dom_elts))
                              sigma_finiteH).
    - intro d.
      destruct (check_bound_in_image_correct decV dom_elts fullH (md_elt d))
        as [ bd2chk chk2bd ].
      unfold hi_map, lo_map.
      set (chk := (check_bound_in_image decV (map md_elt dom_elts) (md_elt d))).
      fold chk in bd2chk, chk2bd.
      destruct (dec_bound_in_image decV dom_elts fullH (md_elt d))
        as [ bdH | notbdH ];
        simpl.
      + rewrite (bd2chk bdH); reflexivity.
      + case_eq chk; auto.
        intro chkH; contradiction (notbdH (chk2bd chkH)).
    - intro bd.
      destruct bd as [ v bdH ].
      exists (exist _ _ (not_fixed_if_bound_in_image decV v bdH)); simpl.
      unfold lo_map.
      case_eq (check_bound_in_image decV (map md_elt dom_elts) v); auto.
      rewrite <- Bool.not_true_iff_false.
      rewrite <- (check_bound_in_image_correct decV dom_elts fullH v); tauto.
  Qed.

End fin_subst_bound_vars.
