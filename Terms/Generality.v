Require Import Lists.List.
Require Import Compare_dec.

Require Import Top.FinSet.FinMod.
Require Import Top.FinSet.FinSet.
Require Import Top.FinSet.FPCard.
Require Import Top.FinSet.NatMap.
Require Import Top.FinSet.ProjSet.

Require Import Top.Terms.BoundInImage.
Require Import Top.Terms.FreeVars.
Require Import Top.Terms.Perm.
Require Import Top.Terms.SplitMap.
Require Import Top.Terms.Subst.
Require Import Top.Terms.Term.
Require Import Top.Terms.VecUtils.

(* First, we have to define the "more general than" relation on
   substitutions, abbreviated to smg.
 *)
Section smg.
  Variable L : lType.
  Notation V := (Term.V L).
  Notation F := (Term.F L).
  Hypothesis decV : forall v v' : V, {v = v'} + {v <> v'}.

  Definition is_left_factoring (rho sigma tau : fin_subst L) : Prop :=
    forall v, comp_subst L (fin_subst_subst L rho)
                         (fin_subst_subst L sigma) v =
              fin_subst_subst L tau v.

  Definition smg (sigma tau : fin_subst L) :=
    exists rho, is_left_factoring rho sigma tau.

  Lemma smg_refl {sigma} : smg sigma sigma.
  Proof.
    exists (existT _ (varTerm L) (fin_subst_varTerm L));
      intro v; apply comp_subst_idl.
  Qed.

  Lemma smg_trans
        (decF : forall f f' : F, {f = f'} + {f <> f'})
        {r s t} :
    smg r s -> smg s t -> smg r t.
  Proof.
    unfold smg.
    destruct 1 as [ rho_rs rsH ].
    destruct 1 as [ rho_st stH ].
    exists (fin_subst_comp L decV decF rho_st rho_rs).
    destruct rho_st as [ urho_st rstH ].
    destruct rho_rs as [ urho_rs rrsH ].
    revert rsH stH; unfold is_left_factoring; simpl; intros rsH stH.
    intro v; unfold fin_subst_comp; simpl.
    rewrite <- comp_subst_assoc.
    assert (eqH : forall v, urho_st v = urho_st v); auto.
    rewrite (comp_subst_ex L v eqH rsH).
    auto using stH.
  Qed.

  Definition is_subst_equiv sigma tau pr : Prop :=
    is_left_factoring (fst pr) sigma tau /\
    is_left_factoring (snd pr) tau sigma.

  Definition sequiv sigma tau := sig (is_subst_equiv sigma tau).

  Definition subst_ub (P : fin_subst L -> Prop) (s : fin_subst L) :=
    forall t : fin_subst L, P t -> exists r, is_left_factoring r t s.

  Definition subst_lb (P : fin_subst L -> Prop) (s : fin_subst L) :=
    forall t : fin_subst L, P t -> exists r, is_left_factoring r s t.

  Definition subst_sup (P : fin_subst L -> Prop) (s : fin_subst L) :=
    subst_ub P s /\ subst_lb (subst_ub P) s.

  Definition subst_inf (P : fin_subst L -> Prop) (s : fin_subst L) :=
    subst_lb P s /\ subst_ub (subst_lb P) s.

End smg.


(** * Elements that are [sequiv] are related by a permutation

    This section is devoted to proving Lemma 2.10 from Eder's paper. This says
    that if two substitutions are equivalent under the [smg] relation then
    there are permutations that relabel them into each other.

*)
Section sequiv_means_perm_lt.
  Variable L : lType.
  Notation V := (Term.V L).

  (** Firstly, we a helper function and facts about it. This function
      takes a term of height zero (which must actually be a variable)
      and extracts that variable. *)

  Definition unpack_height_0_term (t : Term L)
    : term_height t = 0 -> V :=
    match t with
    | varTerm _ v => fun _ => v
    | funTerm f ts =>
      fun htH =>
        False_rect _ (PeanoNat.Nat.neq_succ_0
                        (vec_max_at (term_height (L:=L)) ts) htH)
    end.

  Lemma unpack_height_0_term_irrel
        (t : Term L) (htH0 htH1 : term_height t = 0)
    : unpack_height_0_term t htH0 = unpack_height_0_term t htH1.
  Proof.
    destruct t; auto.
    contradiction (PeanoNat.Nat.neq_succ_0
                     (vec_max_at (term_height (L:=L)) ts)).
  Qed.

  Lemma varTerm_unpack_height_0_term t H
    : varTerm L (unpack_height_0_term t H) = t.
  Proof.
    destruct t; auto.
    contradiction (PeanoNat.Nat.neq_succ_0 _ H).
  Qed.

  (** Now we throw in the assumptions used in lemma 2.10. Here, we
      arbitrarily decide that there will be more bound variables in the
      image of [sigma'] than in the image of [sigma]. We'll argue by
      symmetry at the very end. *)

  Hypothesis decV : forall v v' : V, {v = v'} + {v <> v'}.
  Variables sigma sigma' rho rho' : fin_subst L.

  Hypothesis sigma'H :
    forall v, fin_subst_subst L sigma' v =
              comp_subst L (fin_subst_subst L rho)
                         (fin_subst_subst L sigma) v.

  Hypothesis sigmaH :
    forall v, fin_subst_subst L sigma v =
              comp_subst L (fin_subst_subst L rho')
                         (fin_subst_subst L sigma') v.

  Definition biv_card_list (s : fin_subst L)
    : fp_card_list (bound_image_var L (fin_subst_subst L s)) :=
    dec_fp_card_list (finite_bound_in_image decV s) decV.

  Definition biv_card (s : fin_subst L) : nat := fp_card (biv_card_list s).

  Hypothesis cardleH : biv_card sigma <= biv_card sigma'.

  (** Define local versions of the underlying substitutions from
      sigma, sigma', rho, rho' to avoid all the fin_subst_subst
      noise. *)
  Local Definition s : Subst L := fin_subst_subst L sigma.
  Local Definition s' : Subst L := fin_subst_subst L sigma'.
  Local Definition r : Subst L := fin_subst_subst L rho.
  Local Definition r' : Subst L := fin_subst_subst L rho'.

  (** We are going to define the permutation by splitting [V] into
      those variables that are free in the image of [sigma] and those
      that are bound in the image of [sigma].

      On the "free part", we will show that [rho] sends variables to
      variables and we define [vrho] to get at these variables. *)

  Lemma sigma_is_rho2_sigma v
    : s v = comp_subst L (comp_subst L r' r) s v.
  Proof.
    rewrite <- comp_subst_assoc.
    unfold comp_subst at 1; simpl.
    rewrite <- sigma'H, sigmaH; auto.
  Qed.

  Definition is_sigma_fv (v : V) := termset_fv v (subst_im L s).
  Definition is_sigma_bv (v : V) := is_bound_in_image L s v.

  Definition fv_proj (x : sig is_sigma_fv) : V := proj1_sig x.
  Definition bv_proj (x : sig is_sigma_bv) : V := proj1_sig x.

  Lemma rho2_fixes_im_sigma v
    : is_sigma_fv v -> comp_subst L r' r v = varTerm L v.
  Proof.
    apply (@comp_subst_determines_fvs
             L s (comp_subst L r' r) (varTerm L)); clear v.
    intro v; rewrite <- sigma_is_rho2_sigma, comp_subst_idl; auto.
  Qed.

  Lemma rho_im_sigma_has_height_0 v
    : is_sigma_fv v -> term_height (r v) = 0.
  Proof.
    intro fvH.
    apply PeanoNat.Nat.le_0_r.
    apply (PeanoNat.Nat.le_trans _ _ _ (@term_height_comp_subst L r' r v)).
    rewrite (rho2_fixes_im_sigma v fvH); auto.
  Qed.

  Local Definition vrho (x : sig is_sigma_fv) : V :=
    match x with
    | exist _ v H =>
      unpack_height_0_term (r v) (rho_im_sigma_has_height_0 v H)
    end.

  Lemma vrho_correct v H
    : varTerm L (vrho (exist _ v H)) = r v.
  Proof.
    apply varTerm_unpack_height_0_term.
  Qed.

  Lemma vrho_is_fv_for_sigma' x
    : termset_fv (vrho x) (subst_im L s').
  Proof.
    destruct x as [ v fvH ]; destruct fvH as [ t [ imH fvH' ] ].
    generalize (ex_intro (fun t0 => _ /\ term_fv v t0) _
                         (conj imH fvH')); intro fvH.
    destruct imH as [ w tH ].
    rewrite tH in fvH'; clear t tH.
    rewrite termset_fv_subst_im; exists w.
    rewrite sigma'H.
    apply (term_fv_in_subst_endo r v _ (s w) fvH').
    rewrite <- (vrho_correct v fvH).
    simpl; auto.
  Qed.

  Lemma vrho_irrel v (fvH0 fvH1 : is_sigma_fv v)
    : vrho (exist _ v fvH0) = vrho (exist _ v fvH1).
  Proof.
    unfold vrho; auto using unpack_height_0_term_irrel.
  Qed.

  (** We need to show some sort of finiteness property for [vrho]. The
      obvious statement, [fin_mod fv_proj vrho] isn't true. The
      problem is that the domain of [vrho] is itself a sigma type, so
      you run into problems with how many proofs there are that a
      given variable is free.

      Instead of proving that, we "unpack" [fin_mod] slightly, and
      construct a list of [mod_dom fv_proj vrho] elements (variables
      free in the image of [sigma] for which [vrho] is not the
      identity) where projecting all the way down to [V] does give a
      [FullProj].

      To do this, note that forgetting a variable is free gives an
      injection from [mod_dom fv_proj vrho] into [mod_dom varTerm rho]
      (variables for which [rho] is not [varTerm]). This forms a
      commutative square with [id: V -> V] along the bottom and the
      projection on the right is finite by finiteness of [rho].

       All we need in order to use [finite_left_inverse] is to
       construct a partial right inverse to this inclusion. *)

  Lemma dec_sigma_fv (v : V) : {is_sigma_fv v} + {is_sigma_bv v}.
  Proof.
    unfold is_sigma_fv, is_sigma_bv, s.
    destruct sigma as [ us finH ]; simpl.
    apply (dec_free_in_image L us decV _ (proj2_sig finH) v).
  Qed.

  Lemma mod_elt_rho_to_vrho v
        (neH : mod_elt (varTerm L) r v)
        (fvH : termset_fv v (subst_im L s))
    : mod_elt fv_proj vrho (exist _ v fvH).
  Proof.
    unfold mod_elt, fv_proj, proj1_sig.
    intro eqH; contradiction neH.
    rewrite <- (f_equal (varTerm L) eqH).
    rewrite vrho_correct; auto.
  Qed.

  Lemma varTerm_injective v w
    : varTerm L v = varTerm L w -> v = w.
  Proof.
    injection 1; auto.
  Qed.

  Lemma mod_elt_vrho_to_rho v
        (fvH : termset_fv v (subst_im L s))
        (neH : mod_elt fv_proj vrho (exist _ v fvH))
    : mod_elt (varTerm L) r v.
  Proof.
    unfold mod_elt, fv_proj, proj1_sig.
    intro eqH; contradiction neH.
    apply varTerm_injective.
    rewrite vrho_correct; auto.
  Qed.

  Local Definition vrho_inj_top
    : mod_dom fv_proj vrho -> mod_dom (varTerm L) r :=
    fun x =>
      match x with
      | exist _ (exist _ v fvH) neH => exist _ v (mod_elt_vrho_to_rho v fvH neH)
      end.

  Local Definition vrho_uninj_top
    : mod_dom (varTerm L) r -> option (mod_dom fv_proj vrho) :=
    fun x =>
      match x with
      | exist _ v neH =>
        match dec_sigma_fv v with
        | left fvH => Some (exist _ (exist _ v fvH)
                                  (mod_elt_rho_to_vrho v neH fvH))
        | right bdH => None
        end
      end.

  Local Definition vrho_uninj_bot : V -> option V :=
    fun v =>
      match dec_sigma_fv v with
      | left fvH => Some v
      | right bdH => None
      end.

  Lemma vrho_finite : FiniteProj (fun (x : mod_dom fv_proj vrho) =>
                                    (fv_proj (md_elt x))).
  Proof.
    eapply (@finite_left_inverse (mod_dom fv_proj vrho)
                                 (mod_dom (varTerm L) r)
                                 vrho_uninj_top
                                 V V vrho_uninj_bot
                                 (fun x => proj1_sig (md_elt x)) md_elt
                                 _ vrho_inj_top id _ _ _).
    Unshelve.
    - intro x; destruct x as [ v neH ].
      unfold vrho_uninj_top, vrho_uninj_bot; simpl.
      destruct (dec_sigma_fv v); auto.
    - intro x; destruct x as [ x neH ]; destruct x as [ v fvH ]; auto.
    - intro x; destruct x as [ x neH ]; destruct x as [ v fvH ]; simpl.
      unfold vrho_uninj_bot, id.
      destruct (dec_sigma_fv v) as [ | bdH ]; [ auto | contradiction bdH ].
    - unfold md_elt, r; destruct rho; auto.
  Qed.

  Lemma vrho_injective x x'
    : vrho x = vrho x' -> proj1_sig x = proj1_sig x'.
  Proof.
    intro vrhoH.
    destruct x as [ v0 fv0H ], x' as [ v1 fv1H ]; simpl.
    apply varTerm_injective.
    rewrite <- (rho2_fixes_im_sigma v0 fv0H), <- (rho2_fixes_im_sigma v1 fv1H).
    unfold comp_subst; apply f_equal.
    rewrite <- (vrho_correct v0 fv0H), <- (vrho_correct v1 fv1H).
    apply f_equal, vrhoH.
  Qed.

  Local Definition bound_inj
    : nat_map (bound_image_var L s) (bound_image_var L s') :=
    inj_from_smaller decV
                     (biv_card_list sigma) (biv_card_list sigma')
                     cardleH id.

  Local Lemma bound_inj_is_inj : inj_nat_map bound_inj.
  Proof.
    eauto using inj_from_smaller_is_inj.
  Qed.

  Definition usplit_rho : V -> V :=
    split_map _ _ _ dec_sigma_fv vrho (fun x => nm_bot bound_inj (proj1_sig x)).

  Definition bound_inj_bot (x : sig is_sigma_bv) : V :=
    nm_bot bound_inj (proj1_sig x).

  Lemma bound_inj_bot_irrel v bvH bvH'
    : bound_inj_bot (exist _ v bvH) = bound_inj_bot (exist _ v bvH').
  Proof.
    auto.
  Qed.

  Definition bound_inj_nm_top (x : bound_in_image L s)
    : option (mod_dom bv_proj bound_inj_bot) :=
    match decV (bound_inj_bot x) (proj1_sig x) with
    | left eqH => None
    | right neH => Some (exist _ x neH)
    end.

  Definition bound_inj_nm_bot (v : V) : option V :=
    match dec_sigma_fv v with
    | left fvH => None
    | right bdH =>
      match decV (bound_inj_bot (exist _ v bdH)) v with
      | left eqH => None
      | right neH => Some v
      end
    end.

  Lemma bound_inj_finite
    : FiniteProj (fun (x : mod_dom bv_proj bound_inj_bot) =>
                    (bv_proj (md_elt x))).
  Proof.
    destruct (proj2_sig (biv_card_list sigma)) as [ _ fullH ].
    apply (finite_surj_option (fun x => bv_proj (md_elt x))
                              bound_inj_nm_top bound_inj_nm_bot
                              (exist _ (proj1_sig (biv_card_list sigma))
                                     fullH)).
    - unfold bound_inj_nm_top, bound_inj_nm_bot.
      intro x; destruct x as [ v bdH ]; simpl.
      destruct (dec_sigma_fv v) as [ | bdH' ]; [ contradiction | ].
      rewrite (bound_inj_bot_irrel v bdH' bdH); clear bdH'.
      destruct (decV (bound_inj_bot (exist _ v bdH)) v) as [ eqH | neH ];
        simpl;
        destruct (decV (bound_inj_bot (exist is_sigma_bv v bdH)) v);
        tauto.
    - intro d; destruct d as [ x neH ]; exists x.
      destruct x as [ v bdH ]; simpl.
      unfold bound_inj_nm_bot.
      destruct (dec_sigma_fv v) as [ | bdH' ]; [ contradiction | ].
      rewrite (bound_inj_bot_irrel v bdH' bdH); clear bdH'.
      destruct (decV (bound_inj_bot (exist is_sigma_bv v bdH)) v);
        [ contradiction | auto ].
  Qed.

  Lemma is_var_subst_usplit_rho
    : is_var_subst usplit_rho.
  Proof.
    apply (fin_split V V is_sigma_fv);
      auto using vrho_irrel, vrho_finite, bound_inj_finite.
  Qed.

  Definition split_rho : var_subst V :=
    existT _ usplit_rho is_var_subst_usplit_rho.

  Lemma split_rho_inj : var_subst_inj split_rho.
  Proof.
    unfold split_rho, var_subst_inj; apply inj_split.
    - eauto using vrho_injective.
    - intros x x'.
      assert (bound_image_var _ _ x = proj1_sig x) as projH; auto.
      assert (bound_image_var _ _ x' = proj1_sig x') as projH'; auto.
      rewrite <- projH, <- projH'.
      apply bound_inj_is_inj.
    - intros x x'.
      assert (bound_image_var _ _ x' = proj1_sig x') as projH'; auto.
      rewrite <- projH', <- nat_map_nat; clear projH'.
      unfold bound_image_var.
      intro eqH.
      apply (proj2_sig (nm_top bound_inj x')).
      unfold bound_image_var; rewrite <- eqH.
      apply vrho_is_fv_for_sigma'.
  Qed.

  Lemma usplit_rho_on_free v (freeH : is_sigma_fv v)
    : usplit_rho v = vrho (exist _ v freeH).
  Proof.
    unfold usplit_rho, split_map.
    destruct dec_sigma_fv; [ apply vrho_irrel | contradiction ].
  Qed.

  Lemma split_rho_sigma v
    : comp_subst L
                 (var_subst_subst L split_rho)
                 (fin_subst_subst L sigma) v =
      fin_subst_subst L sigma' v.
  Proof.
    fold s; fold s'.
    rewrite sigma'H.
    revert v; apply comp_subst_determined_by_fvs; intro v.
    unfold var_subst_subst, Basics.compose, split_rho, usplit_rho, split_map.
    destruct dec_sigma_fv; [ auto using vrho_correct | contradiction ].
  Qed.

  Definition split_rho_inv : var_subst V :=
    inj_subst_inv split_rho split_rho_inj decV.

  Lemma split_rho_inv_sigma' v
    : comp_subst L
                 (var_subst_subst L split_rho_inv)
                 (fin_subst_subst L sigma') v =
      fin_subst_subst L sigma v.
  Proof.
    fold s; fold s'.
    unfold comp_subst;
      rewrite sigma'H;
      fold r s;
      fold (comp_subst L (var_subst_subst L split_rho_inv)
                       (comp_subst L r s) v).
    rewrite comp_subst_assoc.
    rewrite <- (comp_subst_idl _ (sigma := s)).
    apply (comp_subst_determined_by_fvs); clear v; intros v fvH.
    unfold comp_subst.
    assert (r v = varTerm L (usplit_rho v)) as rhoH.
    - rewrite (usplit_rho_on_free _ fvH), vrho_correct; auto.
    - rewrite rhoH; simpl; unfold var_subst_subst, Basics.compose; apply f_equal.
      destruct (ext_inverse_inj_subst split_rho split_rho_inj decV).
      auto.
  Qed.
End sequiv_means_perm_lt.

Section sequiv_means_perm.
  Variable L : lType.
  Notation V := (Term.V L).
  Notation F := (Term.F L).

  Hypothesis decV : forall v v' : V, {v = v'} + {v <> v'}.
  Hypothesis decF : forall f f' : F, {f = f'} + {f <> f'}.

  Variables sigma sigma' : fin_subst L.
  Hypothesis equivH : sequiv L sigma sigma'.

  Local Definition rho : fin_subst L := fst (proj1_sig equivH).
  Local Definition rho' : fin_subst L := snd (proj1_sig equivH).

  Lemma sigma'H
    : forall v, fin_subst_subst L sigma' v =
                comp_subst L (fin_subst_subst L rho)
                           (fin_subst_subst L sigma) v.
  Proof.
    destruct (proj2_sig equivH); auto.
  Qed.

  Lemma sigmaH
    : forall v, fin_subst_subst L sigma v =
                comp_subst L (fin_subst_subst L rho')
                           (fin_subst_subst L sigma') v.
  Proof.
    destruct (proj2_sig equivH); auto.
  Qed.

  Local Definition tau : var_subst V :=
    match le_ge_dec (biv_card L decV sigma) (biv_card L decV sigma') with
    | left leH => split_rho L decV sigma sigma' rho rho'
                            sigma'H sigmaH leH
    | right geH => split_rho_inv L decV sigma' sigma rho' rho
                                 sigmaH sigma'H geH
    end.

  Lemma tau_sigma v
    : fin_subst_subst L
                      (fin_subst_comp L decV decF
                                      (var_subst_to_fin_subst L decV decF tau)
                                      sigma)
                      v =
      fin_subst_subst L sigma' v.
  Proof.
    autorewrite with fin_subst var_subst.
    unfold tau; destruct (le_ge_dec _ _);
      auto using split_rho_sigma, split_rho_inv_sigma'.
  Qed.

  Local Definition tau' : var_subst V :=
    match le_ge_dec (biv_card L decV sigma) (biv_card L decV sigma') with
    | left leH => split_rho_inv L decV sigma sigma' rho rho' sigma'H sigmaH leH
    | right geH => split_rho L decV sigma' sigma rho' rho sigmaH sigma'H geH
    end.

  Lemma tau'_sigma' v
    : fin_subst_subst L
                      (fin_subst_comp L decV decF
                                      (var_subst_to_fin_subst L decV decF tau')
                                      sigma')
                      v =
      fin_subst_subst L sigma v.
  Proof.
    autorewrite with fin_subst var_subst.
    unfold tau'; destruct (le_ge_dec _ _);
      auto using split_rho_sigma, split_rho_inv_sigma'.
  Qed.

  Lemma ext_inverse_tau : ext_inverse (projT1 tau) (projT1 tau').
  Proof.
    unfold tau, tau'; destruct (le_ge_dec _ _);
      [ | apply ext_inverse_sym ];
      apply ext_inverse_inj_subst.
  Qed.

End sequiv_means_perm.
