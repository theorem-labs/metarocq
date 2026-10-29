(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICInductivesEta]

  Each lemma of [PCUICInductivesEta] that has a premise is applied here to a concrete instance
  with every premise proved. The environment is [iv_Σ] of [PCUICInversionEtaInstances]
  ([CoInductive R (A : Prop) : Prop := mkR { f : A }], a record with one projection, well formed
  for the η typing by [iv_wfE]). The context is
  [Γk := [y : k g; k : (Prop → Prop) → Prop; g : Prop → Prop]], in which [y : k g] is retyped at
  [k (λx:Prop. g x)] by one η step ([c16_y_eta]); [Γr := Γk ,, r : R (k g)], in which [r] is
  retyped at [R (k (λx:Prop. g x))] by the same step under [R] ([c16_r_eta]);
  [Γz := Γk ,, z := y : k (λx:Prop. g x)], whose let-in body is typed through the η step; and
  [Γh := Γk ,, h : Π x : k (λx:Prop. g x). Prop], in which [h y : Prop] applies [h] to [y] at
  [k (λx:Prop. g x)], so that its derivation contains the η step ([c16_hy_typed]).
  The instances whose hypotheses carry a typing judgement, a substitution, a spine or a context
  over these retypings go through the η step: [on_inductive_instE],
  [declared_inductive_valid_typeE], [declared_inductive_type_closed_redE],
  [declared_inductive_type_ws_cumulE], [isType_ind_arity_instE], [type_Ind_arity_formE] and
  [wf_ind_predicateE] (their context premise is [Γz]); [isType_introE], [typing_spine_ind_typeE],
  [typing_spine_ind_type_invE], [isType_mkApps_IndE], [wf_subsletE], [wf_subslet_domE],
  [isType_it_mkProd_or_LetIn_invE], [isType_it_mkProd_or_LetIn_substE],
  [subslet_extended_substE], [context_subst_to_extended_list_kE], [spine_subst_smash_invE],
  [type_local_ctx_cumE], [type_local_ctx_wfE], [isType_it_mkProd_or_LetInE],
  [isType_it_mkProd_or_LetIn_smashE], [typing_spine_to_extended_listE],
  [invert_type_mkApps_indE], [isType_mkApps_Ind_invE], [isType_mkApps_Ind_inv'E],
  [projection_subsletE], [wf_local_expand_letsE], [typing_expand_lets_genE],
  [map_subst_let_expand_k_to_extended_list_liftE], [map_subst_let_expand_to_extended_listE],
  [subslet_smash_contextE], [spine_subst_expand_letsE], [isType_case_predicateE] and
  [arity_spine_case_predicateE].
  A mark NOT BUILT names a part of an instance that a cheap witness does not reach, the missing
  witness and its cost. [R] is monomorphic, so its only universe instance is [[]] and
  [subst_instance []] is the identity: a nonempty instance needs a universe-polymorphic
  inductive (a new inductive, a new environment and its [wfE] proof). Every instance at [[]] of
  a lemma with a [consistent_instance_ext] premise is marked NOT BUILT for that part; the
  instances so marked without an η step have only declarations and that premise. A mark
  IMPOSSIBLE names a part that cannot contain an η step by the head and the rule set: the
  comparison of [type_local_ctx_cumE] is between two sorts ([Prop ≤ Type]), and the premises of
  [red_it_mkProd_or_LetIn_to_smashE] are booleans. [conv_ctx_reflE] has no premise; it is
  applied to [Γk]. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICCases PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICReduction
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICContextSubst PCUICSigmaCalculus PCUICClosedBodies
     PCUICWellScopedCumulativity PCUICConversion PCUICInductives PCUICWsCumulEtaCtxTyp
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta
     PCUICTypingEtaNotions PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances
     PCUICSpineEta PCUICInductivesEta.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

(** ** The η kit in [iv_Σ] *)

Lemma c16_K_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E iv_K : tSort (Sort.sort_of_product iv_sPP (Sort.super sProp)).
Proof.
  intros h. unfold iv_K. apply typeE_Prod.
  - exact (iv_vass_s iv_Σ Γ si_na iv_PP _ (iv_PP_typed iv_Σ Γ h) Logic.eq_refl).
  - exact (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ Γ si_na iv_PP _ h (iv_PP_typed iv_Σ Γ h) Logic.eq_refl)).
Qed.

Lemma c16_wf_Γg : wf_localE iv_Σ iv_Γg.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_PP _ localenv_nil (iv_PP_typed iv_Σ [] localenv_nil) Logic.eq_refl). Qed.

Lemma c16_wf_Γkg : wf_localE iv_Σ iv_Γkg.
Proof. exact (iv_wf_vass iv_Σ iv_Γg si_na iv_K _ c16_wf_Γg (c16_K_typed iv_Γg c16_wf_Γg) Logic.eq_refl). Qed.

Lemma c16_kg0_typed : iv_Σ ;;; iv_Γkg |-E tApp (tRel 0) (tRel 1) : si_P.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na iv_PP si_P _ (tRel 1) (c16_K_typed iv_Γkg c16_wf_Γkg)
           (typeE_Rel _ _ 0 (vass si_na iv_K) c16_wf_Γkg Logic.eq_refl)
           (typeE_Rel _ _ 1 (vass si_na iv_PP) c16_wf_Γkg Logic.eq_refl)).
Qed.

Lemma c16_wf_Γk : wf_localE iv_Σ iv_Γk.
Proof. exact (iv_wf_vass iv_Σ iv_Γkg si_na (tApp (tRel 0) (tRel 1)) sProp c16_wf_Γkg c16_kg0_typed Logic.eq_refl). Qed.

Lemma c16_closed_Γk : is_closed_context iv_Γk.
Proof. exact (wf_local_closed_contextE (Σ := iv_Σ) (wfΣ := iv_wfE) c16_wf_Γk). Qed.

Lemma c16_y_typed : iv_Σ ;;; iv_Γk |-E tRel 0 : iv_kg.
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tApp (tRel 0) (tRel 1))) c16_wf_Γk Logic.eq_refl). Qed.

(** [k g : Prop]. *)
Lemma c16_kg_typed : iv_Σ ;;; iv_Γk |-E iv_kg : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ (tRel 2) (c16_K_typed iv_Γk c16_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) c16_wf_Γk Logic.eq_refl)
           (typeE_Rel _ _ 2 (vass si_na iv_PP) c16_wf_Γk Logic.eq_refl)).
Qed.

Lemma c16_eta_g_typed : iv_Σ ;;; iv_Γk |-E iv_eta_g : iv_PP.
Proof.
  have w : wf_localE iv_Σ (iv_Γk ,, vass si_na si_P) := iv_wf_P iv_Σ iv_Γk c16_wf_Γk.
  unfold iv_eta_g, iv_PP. apply typeE_Lambda.
  - exact (iv_vass iv_Σ iv_Γk si_na si_P _ (iv_P_typed iv_Σ iv_Γk c16_wf_Γk) Logic.eq_refl).
  - exact (typeE_App _ _ (tRel 3) si_na si_P si_P _ (tRel 0) (iv_PP_typed iv_Σ _ w)
             (typeE_Rel _ _ 3 (vass si_na iv_PP) w Logic.eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) w Logic.eq_refl)).
Qed.

(** [k (λx:Prop. g x) : Prop]. *)
Lemma c16_keta_typed : iv_Σ ;;; iv_Γk |-E iv_keta : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ iv_eta_g (c16_K_typed iv_Γk c16_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) c16_wf_Γk Logic.eq_refl) c16_eta_g_typed).
Qed.

(** [k g ≤ k (λx:Prop. g x)]: congruence, and the symmetric of one [cumul_eta_l] step. *)
Lemma c16_spec_eta : cumulSpecE iv_Σ iv_Γk iv_kg iv_keta.
Proof.
  unfold cumulSpecE, iv_kg, iv_keta, iv_eta_g.
  apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
Qed.

(** [y : k g] retyped at [k (λx:Prop. g x)] through the η step only. *)
Lemma c16_y_eta : iv_Σ ;;; iv_Γk |-E tRel 0 : iv_keta.
Proof. exact (typeE_Cumul _ _ (tRel 0) iv_kg iv_keta sProp c16_y_typed c16_keta_typed c16_spec_eta). Qed.

Lemma c16_isT_keta : isTypeE iv_Σ iv_Γk iv_keta.
Proof. exact (has_sort_isTypeE _ c16_keta_typed). Qed.

Lemma c16_cu : consistent_instance_ext iv_Σ (ind_universes iv_mdecl) [].
Proof. reflexivity. Qed.

(** The projections fact of [R], from its declaration. *)
Lemma c16_onps : on_projections iv_mdecl (inductive_mind iv_ind) (inductive_ind iv_ind) iv_idecl
  (ind_indices iv_idecl) iv_cdecl.
Proof.
  destruct (on_declared_projectionE (wfΣ := iv_wfE) iv_declared_projection) as [[_ _] [[[_ onps] _] _]].
  exact onps.
Qed.

(** *** [r : R (k g)] retyped at [R (k (λx:Prop. g x))] *)

Definition c16_Γr : context := iv_Γk ,, vass si_na (iv_R iv_kg).
Definition c16_kg1 : term := lift0 1 iv_kg.
Definition c16_keta1 : term := lift0 1 iv_keta.

Lemma c16_Rkg_typed : iv_Σ ;;; iv_Γk |-E iv_R iv_kg : si_P.
Proof. exact (iv_RX_typed iv_Γk iv_kg c16_wf_Γk c16_kg_typed). Qed.

Lemma c16_wf_Γr : wf_localE iv_Σ c16_Γr.
Proof. exact (iv_wf_vass iv_Σ iv_Γk si_na (iv_R iv_kg) sProp c16_wf_Γk c16_Rkg_typed Logic.eq_refl). Qed.

Lemma c16_keta1_typed : iv_Σ ;;; c16_Γr |-E c16_keta1 : si_P.
Proof. exact (weakeningE iv_Σ iv_Γk [vass si_na (iv_R iv_kg)] iv_keta si_P iv_wfE c16_wf_Γr c16_keta_typed). Qed.

Lemma c16_Rketa1_typed : iv_Σ ;;; c16_Γr |-E iv_R c16_keta1 : si_P.
Proof. exact (iv_RX_typed c16_Γr c16_keta1 c16_wf_Γr c16_keta1_typed). Qed.

Lemma c16_r_typed : iv_Σ ;;; c16_Γr |-E tRel 0 : iv_R c16_kg1.
Proof. exact (typeE_Rel _ _ 0 (vass si_na (iv_R iv_kg)) c16_wf_Γr Logic.eq_refl). Qed.

Lemma c16_spec_R : cumulSpecE iv_Σ c16_Γr (iv_R c16_kg1) (iv_R c16_keta1).
Proof.
  unfold cumulSpecE, iv_R, c16_kg1, c16_keta1, iv_kg, iv_keta, iv_eta_g. cbn.
  apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
Qed.

(** [r : R (k (λx:Prop. g x))], through the η step under [R]. *)
Lemma c16_r_eta : iv_Σ ;;; c16_Γr |-E tRel 0 : mkApps (tInd iv_ind []) [c16_keta1].
Proof. exact (typeE_Cumul _ _ (tRel 0) (iv_R c16_kg1) (iv_R c16_keta1) sProp c16_r_typed c16_Rketa1_typed c16_spec_R). Qed.

Lemma c16_isT_Rketa1 : isTypeE iv_Σ c16_Γr (mkApps (tInd iv_ind []) [c16_keta1]).
Proof. exact (has_sort_isTypeE _ c16_Rketa1_typed). Qed.

(** *** [z := y : k (λx:Prop. g x)], its body typed through the η step *)

Definition c16_Δz : context := [vdef si_na (tRel 0) iv_keta].
Definition c16_Γz : context := iv_Γk ,,, c16_Δz.

Lemma c16_wf_Γz : wf_localE iv_Σ c16_Γz.
Proof.
  apply localenv_cons_def; [exact c16_wf_Γk|].
  exact (iv_vdef iv_Σ iv_Γk si_na (tRel 0) iv_keta sProp c16_y_eta c16_keta_typed Logic.eq_refl).
Qed.

Lemma c16_keta_z_typed : iv_Σ ;;; c16_Γz |-E lift0 1 iv_keta : si_P.
Proof. exact (weakeningE iv_Σ iv_Γk c16_Δz iv_keta si_P iv_wfE c16_wf_Γz c16_keta_typed). Qed.

(** [y], at [tRel 1] under [z], typed at [k (λx:Prop. g x)] through the η step. *)
Lemma c16_y_eta_z : iv_Σ ;;; c16_Γz |-E tRel 1 : lift0 1 iv_keta.
Proof. exact (weakeningE iv_Σ iv_Γk c16_Δz (tRel 0) iv_keta iv_wfE c16_wf_Γz c16_y_eta). Qed.

(** The one-variable telescope [x : k (λx:Prop. g x)], and [y] for it. *)
Definition c16_Δx : context := [vass si_na iv_keta].

Lemma c16_wf_Γx : wf_localE iv_Σ (iv_Γk ,,, c16_Δx).
Proof. exact (iv_wf_vass iv_Σ iv_Γk si_na iv_keta sProp c16_wf_Γk c16_keta_typed Logic.eq_refl). Qed.

Lemma c16_cs_x : context_subst c16_Δx [tRel 0] [tRel 0].
Proof. exact (context_subst_ass [] [] [] si_na iv_keta (tRel 0) context_subst_nil). Qed.

(** [x := y] for [x : k (λx:Prop. g x)]: the substitution types [y : k g] through η. *)
Definition c16_sp_x : spine_substE iv_Σ iv_Γk [tRel 0] [tRel 0] c16_Δx :=
  {| spine_dom_wfE := c16_wf_Γk; spine_codom_wfE := c16_wf_Γx; inst_ctx_substE := c16_cs_x;
     inst_subsletE := subslet_ass_tipE c16_y_eta |}.

(** [Π x : k (λx:Prop. g x). Prop]. *)
Definition c16_Px : term := it_mkProd_or_LetIn c16_Δx (tSort sProp).

Lemma c16_Px_typed : iv_Σ ;;; iv_Γk |-E c16_Px : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof.
  change (iv_Σ ;;; iv_Γk |-E tProd si_na iv_keta (tSort sProp) : tSort (Sort.sort_of_product sProp (Sort.super sProp))).
  apply typeE_Prod; [exact (iv_vass_s iv_Σ iv_Γk si_na iv_keta sProp c16_keta_typed Logic.eq_refl)|].
  exact (iv_P_typed iv_Σ _ c16_wf_Γx).
Qed.

Lemma c16_isT_Px : isTypeE iv_Σ iv_Γk c16_Px.
Proof. exact (has_sort_isTypeE _ c16_Px_typed). Qed.

(** *** [Γh := Γk ,, h : Π x : k (λx:Prop. g x). Prop] and [h y : Prop] *)

Definition c16_Γh : context := iv_Γk ,, vass si_na c16_Px.

Lemma c16_wf_Γh : wf_localE iv_Σ c16_Γh.
Proof. exact (iv_wf_vass iv_Σ iv_Γk si_na c16_Px _ c16_wf_Γk c16_Px_typed Logic.eq_refl). Qed.

(** [h y]: [y : k g] is used at [k (λx:Prop. g x)]. *)
Definition c16_hy : term := tApp (tRel 0) (tRel 1).

Lemma c16_y_eta_h : iv_Σ ;;; c16_Γh |-E tRel 1 : lift0 1 iv_keta.
Proof. exact (weakeningE iv_Σ iv_Γk [vass si_na c16_Px] (tRel 0) iv_keta iv_wfE c16_wf_Γh c16_y_eta). Qed.

Lemma c16_Px_h : iv_Σ ;;; c16_Γh |-E tProd si_na (lift0 1 iv_keta) (tSort sProp) :
  tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof. exact (weakeningE iv_Σ iv_Γk [vass si_na c16_Px] c16_Px _ iv_wfE c16_wf_Γh c16_Px_typed). Qed.

Lemma c16_h_typed : iv_Σ ;;; c16_Γh |-E tRel 0 : tProd si_na (lift0 1 iv_keta) (tSort sProp).
Proof. exact (typeE_Rel _ _ 0 (vass si_na c16_Px) c16_wf_Γh Logic.eq_refl). Qed.

(** [h y : Prop]; the η step is inside this derivation (through [c16_y_eta]). *)
Lemma c16_hy_typed : iv_Σ ;;; c16_Γh |-E c16_hy : tSort sProp.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na (lift0 1 iv_keta) (tSort sProp) _ (tRel 1) c16_Px_h c16_h_typed c16_y_eta_h).
Qed.

(** [w : h y] as a telescope of sort [Prop] over [Γh]. *)
Definition c16_Δhy : context := [vass si_na c16_hy].

Lemma c16_tlc_hy : type_local_ctx (PCUICTyping.lift_typing typingE) iv_Σ c16_Γh c16_Δhy sProp.
Proof.
  cbn. split; [cbn; trivial|]. exact (iv_vass_s iv_Σ c16_Γh si_na c16_hy sProp c16_hy_typed Logic.eq_refl).
Qed.

(** [Π w : h y. Prop] over [Γh]. *)
Lemma c16_isT_Phy : isTypeE iv_Σ c16_Γh (it_mkProd_or_LetIn c16_Δhy (tSort sProp)).
Proof.
  exact (has_sort_isTypeE _ (typeE_Prod _ _ si_na c16_hy (tSort sProp) sProp (Sort.super sProp)
           (iv_vass_s iv_Σ c16_Γh si_na c16_hy sProp c16_hy_typed Logic.eq_refl)
           (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ c16_Γh si_na c16_hy sProp c16_wf_Γh c16_hy_typed Logic.eq_refl)))).
Qed.

(** [let z := y : k (λx:Prop. g x) in Prop]. *)
Definition c16_Pz : term := it_mkProd_or_LetIn c16_Δz (tSort sProp).

Lemma c16_Pz_typed : iv_Σ ;;; iv_Γk |-E c16_Pz : tLetIn si_na (tRel 0) iv_keta (tSort (Sort.super sProp)).
Proof.
  change (iv_Σ ;;; iv_Γk |-E tLetIn si_na (tRel 0) iv_keta (tSort sProp) : tLetIn si_na (tRel 0) iv_keta (tSort (Sort.super sProp))).
  apply typeE_LetIn; [exact (iv_vdef iv_Σ iv_Γk si_na (tRel 0) iv_keta sProp c16_y_eta c16_keta_typed Logic.eq_refl)|].
  exact (iv_P_typed iv_Σ _ c16_wf_Γz).
Qed.

Lemma c16_Type_typed : iv_Σ ;;; iv_Γk |-E tSort (Sort.super sProp) : tSort (Sort.super (Sort.super sProp)).
Proof. apply typeE_Sort; [exact c16_wf_Γk|apply PCUICUnivSubstitutionConv.wf_sort_super; cbn; trivial]. Qed.

(** [let z := y : k (λx:Prop. g x) in Prop : Type], by the ζ-step of its type. *)
Lemma c16_Pz_sort : iv_Σ ;;; iv_Γk |-E c16_Pz : tSort (Sort.super sProp).
Proof.
  refine (typeE_Cumul _ _ c16_Pz _ _ _ c16_Pz_typed c16_Type_typed _).
  exact (cumulE_zeta _ _ _ _ _ _ _).
Qed.

(** ** Instances of [PCUICInductivesEta] *)

(** [conv_ctx_reflE] has no premise; applied to [Γk]. *)
Definition conv_ctx_reflE_inst := conv_ctx_reflE iv_Σ iv_Γk.

(* NOT BUILT (the universe part): the premises are a declaration and [consistent_instance_ext];
   [R] is monomorphic, so the only instance is [[]] and [subst_instance []] is the identity. A
   nonempty instance needs a universe-polymorphic inductive (a new inductive, a new environment
   and its [wfE] proof). *)
Definition wf_arities_context_instE_inst :=
  @wf_arities_context_instE _ iv_Σ iv_wfE iv_kn iv_mdecl [] (MRProd.proj1 iv_declared_inductive) c16_cu.
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition instantiate_indsE_inst :=
  @instantiate_indsE _ iv_Σ iv_wfE [] iv_kn iv_mdecl (MRProd.proj1 iv_declared_inductive) c16_cu.

Definition declared_inductive_arity_isTypeRelE_inst :=
  @declared_inductive_arity_isTypeRelE _ iv_env iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive.
Definition on_minductive_wf_params_indicesE_inst :=
  @on_minductive_wf_params_indicesE _ iv_env iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive.
(* NOT BUILT (the reduction step): the declared type of [R] is its arity, so the reduction has
   no step. A step needs an inductive whose declared arity is a redex, since the declaration asks
   only that its declared arity reduce to the built one (a new inductive, a new environment and
   its [wfE] proof). *)
Definition declared_inductive_typeE_inst :=
  @declared_inductive_typeE _ iv_env iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive.

(** The β-step [(λP:Prop. P) (∀P:Prop. P) ⇝ ∀P:Prop. P], closed, lifted into [Γk]. *)
Lemma c16_red_beta : red iv_Σ [] (tApp iv_id iv_False) iv_False.
Proof. apply red1_red. unfold iv_id. apply red_beta. Qed.
Definition closed_red_from_emptyE_inst :=
  @closed_red_from_emptyE _ iv_Σ iv_wfE iv_Γk (tApp iv_id iv_False) iv_False c16_closed_Γk Logic.eq_refl c16_red_beta.

(** [h y : Prop], typed through the η step. *)
Definition isType_introE_inst := @isType_introE _ iv_Σ c16_Γh c16_hy sProp c16_hy_typed.

(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition on_minductive_wf_params_indices_instE_inst :=
  @on_minductive_wf_params_indices_instE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive [] c16_cu.

(** The six lemmas below and [wf_ind_predicateE] take the context [Γz], whose let-in body is
    typed through the η step. *)
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition on_inductive_instE_inst :=
  @on_inductive_instE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γz [] c16_wf_Γz c16_cu.
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition declared_inductive_valid_typeE_inst :=
  @declared_inductive_valid_typeE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γz [] c16_wf_Γz c16_cu.
(* NOT BUILT (the reduction step and the universe part): as [declared_inductive_typeE_inst]
   (an inductive whose declared arity is a redex) and as [wf_arities_context_instE_inst] (a
   universe-polymorphic inductive). *)
Definition declared_inductive_type_closed_redE_inst :=
  @declared_inductive_type_closed_redE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γz [] c16_wf_Γz.
(* NOT BUILT (the reduction step and the universe part): as
   [declared_inductive_type_closed_redE_inst] (here the conversion is reflexive). *)
Definition declared_inductive_type_ws_cumulE_inst :=
  @declared_inductive_type_ws_cumulE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γz [] c16_wf_Γz.
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition isType_ind_arity_instE_inst :=
  @isType_ind_arity_instE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γz [] c16_wf_Γz c16_cu.
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition type_Ind_arity_formE_inst :=
  @type_Ind_arity_formE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γz [] c16_wf_Γz c16_cu.

(** The spine [Π A:Prop. Prop] applied to [h y]: its argument is typed through the η step. *)
Lemma c16_isT_arity : isTypeE iv_Σ c16_Γh si_arity.
Proof. exact (has_sort_isTypeE _ (iv_PP_typed iv_Σ c16_Γh c16_wf_Γh)). Qed.
Lemma c16_isT_Prop : isTypeE iv_Σ c16_Γh (tSort sProp).
Proof. exact (has_sort_isTypeE _ (iv_P_typed iv_Σ c16_Γh c16_wf_Γh)). Qed.
Lemma c16_sp_arity : PCUICAritiesEta.typing_spineE iv_Σ c16_Γh si_arity [c16_hy] (tSort sProp).
Proof.
  eapply PCUICAritiesEta.type_spine_consE; [exact c16_isT_arity|exact c16_isT_arity| |exact c16_hy_typed|].
  - exact (isType_ws_cumul_pbE_refl (Σ := iv_Σ) (wfΣ := iv_wfE) _ _ c16_isT_arity).
  - apply PCUICAritiesEta.type_spine_nilE; [exact c16_isT_Prop|exact c16_isT_Prop|].
    exact (isType_ws_cumul_pbE_refl (Σ := iv_Σ) (wfΣ := iv_wfE) _ _ c16_isT_Prop).
Qed.

(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition typing_spine_ind_typeE_inst :=
  @typing_spine_ind_typeE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γh [] [c16_hy] (tSort sProp)
    c16_wf_Γh c16_cu c16_sp_arity.
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition typing_spine_ind_type_invE_inst :=
  @typing_spine_ind_type_invE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γh [] [c16_hy] (tSort sProp)
    c16_wf_Γh c16_cu c16_sp_arity.

Definition oiE_inst := @PCUICInductivesEta.oiE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive.
Definition oibE_inst := @PCUICInductivesEta.oibE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive.
Definition on_inductive_sortE_inst :=
  @on_inductive_sortE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive.
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition on_inductive_sort_instE_inst :=
  @on_inductive_sort_instE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive [] c16_cu.

(** [A := h y] for the parameters of [R]: the substitution types [h y] through the η step. *)
Lemma c16_wf_Γhpar : wf_localE iv_Σ (c16_Γh ,,, si_params).
Proof. exact (iv_wf_P iv_Σ c16_Γh c16_wf_Γh). Qed.
Lemma c16_cs_hy : context_subst si_params [c16_hy] [c16_hy].
Proof. exact (context_subst_ass [] [] [] si_na si_P c16_hy context_subst_nil). Qed.
Definition c16_sp_hy : spine_substE iv_Σ c16_Γh [c16_hy] [c16_hy] si_params :=
  {| spine_dom_wfE := c16_wf_Γh; spine_codom_wfE := c16_wf_Γhpar; inst_ctx_substE := c16_cs_hy;
     inst_subsletE := subslet_ass_tipE c16_hy_typed |}.

(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition isType_mkApps_IndE_inst :=
  @isType_mkApps_IndE _ iv_Σ iv_wfE iv_mdecl iv_ind iv_idecl iv_declared_inductive c16_Γh [] [c16_hy] [c16_hy]
    c16_cu c16_sp_hy.

Definition untyped_subslet_projsE_inst :=
  untyped_subslet_projsE iv_Σ iv_ind iv_mdecl iv_idecl iv_wfE iv_declared_inductive c16_onps.

(** [x := y] with [x : k (λx:Prop. g x)], its substitution typed through η. *)
Definition wf_subsletE_inst : wf_subsletE iv_Σ iv_Γk [tRel 0] c16_Δx :=
  {| wf_subslet_ctxE := c16_wf_Γx; wf_subslet_subsletE := subslet_ass_tipE c16_y_eta |}.
Definition wf_subslet_domE_inst := wf_subslet_domE wf_subsletE_inst.

(** [Π w : h y. Prop], typed through the η step. *)
Definition isType_it_mkProd_or_LetIn_invE_inst :=
  @isType_it_mkProd_or_LetIn_invE _ iv_Σ iv_wfE c16_Γh c16_Δhy (tSort sProp) c16_isT_Phy.
Definition isType_it_mkProd_or_LetIn_substE_inst :=
  @isType_it_mkProd_or_LetIn_substE _ iv_Σ iv_wfE iv_Γk c16_Δx [tRel 0] [tRel 0] (tSort sProp) c16_isT_Px c16_sp_x.

Definition c16_subslet_extended_substE_inst :=
  PCUICInductivesEta.subslet_extended_substE iv_Σ c16_Γz iv_wfE c16_wf_Γz.
Definition context_subst_to_extended_list_kE_inst := context_subst_to_extended_list_kE iv_Σ c16_Γz iv_wfE c16_wf_Γz.
Definition spine_subst_smash_invE_inst := @spine_subst_smash_invE _ iv_Σ c16_Γz iv_wfE c16_wf_Γz.

Definition wf_projection_context_genE_inst :=
  @wf_projection_context_genE _ iv_Σ iv_mdecl iv_ind iv_idecl iv_cdecl iv_wfE iv_declared_inductive c16_onps.
Definition declared_constructor_wf_pars_argsE_inst :=
  @declared_constructor_wf_pars_argsE _ iv_Σ iv_ind 0 iv_mdecl iv_idecl iv_cdecl iv_wfE iv_declared_constructor.
Definition wf_projection_arg_ctxE_inst k :=
  @wf_projection_arg_ctxE _ iv_Σ iv_mdecl iv_ind iv_idecl iv_cdecl iv_wfE iv_declared_constructor c16_onps k.

Definition declared_projectionsE_inst :=
  declared_projectionsE (Σ := iv_Σ) iv_wfE iv_declared_inductive c16_onps.

(** The projection facts of [f], at index 0, from [declared_projectionsE]: the induction
    hypothesis of [declared_projections_subslet_indE] at [i = 1]. *)
Lemma c16_IH : forall i0 : nat, i0 < 1 -> forall x, nth_error (ind_projs iv_idecl) i0 = Some x ->
  isTypeE (iv_Σ.1, ind_universes iv_mdecl)
    (smash_context [] (ind_params iv_mdecl),,
     vass {| binder_name := nNamed (ind_name iv_idecl); binder_relevance := ind_relevance iv_idecl |}
       (mkApps (tInd iv_ind (abstract_instance (ind_universes iv_mdecl)))
          (to_extended_list (smash_context [] (ind_params iv_mdecl))))) x.(proj_type)
  × (∑ decl : PCUICEnvironment.context_decl,
       [× nth_error (smash_context [] (cstr_args iv_cdecl))
           (context_assumptions (cstr_args iv_cdecl) - Datatypes.S i0) = Some decl,
         isTypeE (iv_Σ.1, ind_universes iv_mdecl)
           (arities_context (ind_bodies iv_mdecl),,, ind_params iv_mdecl,,,
            skipn (context_assumptions (cstr_args iv_cdecl) - i0)
              (smash_context [] (cstr_args iv_cdecl))) (decl_type decl),
         wf_localE (iv_Σ.1, ind_universes iv_mdecl)
           (arities_context (ind_bodies iv_mdecl),,, ind_params iv_mdecl,,,
            smash_context [] (cstr_args iv_cdecl)),
         projection_type iv_mdecl iv_ind i0 (decl_type decl) = x.(proj_type) &
         projection_type iv_mdecl iv_ind i0 (decl_type decl) =
         projection_type' iv_mdecl iv_ind i0 (decl_type decl)]).
Proof.
  intros i0 hi x hx.
  have IH := declared_projectionsE_inst.
  eapply nth_error_alli in IH; tea. exact IH.
Qed.

Definition declared_projections_subslet_indE_inst :=
  declared_projections_subslet_indE (Σ := iv_Σ) iv_wfE iv_declared_inductive iv_cdecl Logic.eq_refl
    (on_projections_decl c16_onps) 1 c16_IH c16_onps (le_n 1) Logic.eq_refl Logic.eq_refl.
Definition declared_projections_subsletE_inst :=
  declared_projections_subsletE (Σ := iv_Σ) iv_wfE iv_declared_inductive iv_cdecl Logic.eq_refl c16_onps 1 (le_n 1).
Definition declared_projection_typeE_inst :=
  @declared_projection_typeE _ iv_Σ iv_mdecl iv_idecl iv_proj iv_cdecl iv_pdecl iv_wfE iv_declared_projection.
Definition declared_projection_type_and_eqE_inst :=
  @declared_projection_type_and_eqE _ iv_Σ iv_mdecl iv_idecl iv_proj iv_cdecl iv_pdecl iv_wfE iv_declared_projection.

Lemma c16_wf_sort_Prop : wf_sort iv_Σ sProp.
Proof. cbn; trivial. Qed.
Lemma c16_wf_sort_Type : wf_sort iv_Σ (Sort.super sProp).
Proof. apply PCUICUnivSubstitutionConv.wf_sort_super; cbn; trivial. Qed.
(** [Prop ≤ Type]: the cumulativity of the two sorts. *)
Lemma c16_leq_Prop_Type : leq_sort (global_ext_constraints iv_Σ) sProp (Sort.super sProp).
Proof. cbn; trivial. Qed.

(* IMPOSSIBLE (the comparison): it is between two sorts ([Prop ≤ Type]), where no η step can
   occur. The telescope [w : h y] of the [type_local_ctx] premise is typed through the η step. *)
Definition type_local_ctx_cumE_inst :=
  @type_local_ctx_cumE _ iv_Σ c16_Γh c16_Δhy sProp (Sort.super sProp) iv_wfE c16_wf_sort_Type c16_leq_Prop_Type
    c16_tlc_hy.
Definition type_local_ctx_wfE_inst := @type_local_ctx_wfE _ iv_Σ c16_Γh c16_Δhy sProp iv_wfE c16_tlc_hy.
Definition c16_isType_it_mkProd_or_LetInE_inst :=
  PCUICInductivesEta.isType_it_mkProd_or_LetInE iv_Σ c16_Γh c16_Δhy sProp sProp iv_wfE c16_wf_Γh c16_tlc_hy
    c16_wf_sort_Prop.
Definition isType_it_mkProd_or_LetIn_smashE_inst :=
  isType_it_mkProd_or_LetIn_smashE iv_Σ iv_Γk c16_Δz sProp iv_wfE (has_sort_isTypeE _ c16_Pz_sort).

(** The telescope [w : P'] with the closed proposition
    [P' := Π g:Prop→Prop. Π k:(Prop→Prop)→Prop. Π y:k g. Π h:(k (λx:Prop. g x) → Prop). h y],
    whose typing contains the η step (at [h y]). *)
Definition c16_P4 : term := tProd si_na c16_Px c16_hy.
Definition c16_P3 : term := tProd si_na (tApp (tRel 0) (tRel 1)) c16_P4.
Definition c16_P2 : term := tProd si_na iv_K c16_P3.
Definition c16_P' : term := tProd si_na iv_PP c16_P2.

Lemma c16_P4_typed : iv_Σ ;;; iv_Γk |-E c16_P4 : tSort sProp.
Proof.
  exact (typeE_Prod _ _ si_na c16_Px c16_hy (Sort.sort_of_product sProp (Sort.super sProp)) sProp
           (iv_vass_s iv_Σ iv_Γk si_na c16_Px _ c16_Px_typed Logic.eq_refl) c16_hy_typed).
Qed.
Lemma c16_P3_typed : iv_Σ ;;; iv_Γkg |-E c16_P3 : tSort sProp.
Proof.
  exact (typeE_Prod _ _ si_na (tApp (tRel 0) (tRel 1)) c16_P4 sProp sProp
           (iv_vass_s iv_Σ iv_Γkg si_na _ sProp c16_kg0_typed Logic.eq_refl) c16_P4_typed).
Qed.
Lemma c16_P2_typed : iv_Σ ;;; iv_Γg |-E c16_P2 : tSort sProp.
Proof.
  exact (typeE_Prod _ _ si_na iv_K c16_P3 (Sort.sort_of_product iv_sPP (Sort.super sProp)) sProp
           (iv_vass_s iv_Σ iv_Γg si_na iv_K _ (c16_K_typed iv_Γg c16_wf_Γg) Logic.eq_refl) c16_P3_typed).
Qed.
Lemma c16_P'_typed : iv_Σ ;;; [] |-E c16_P' : tSort sProp.
Proof.
  exact (typeE_Prod _ _ si_na iv_PP c16_P2 iv_sPP sProp
           (iv_vass_s iv_Σ [] si_na iv_PP _ (iv_PP_typed iv_Σ [] localenv_nil) Logic.eq_refl) c16_P2_typed).
Qed.

Definition c16_ΔP' : context := [vass si_na c16_P'].
Lemma c16_isT_ΔP' : isTypeE iv_Σ [] (it_mkProd_or_LetIn c16_ΔP' (tSort sProp)).
Proof.
  exact (has_sort_isTypeE _ (typeE_Prod _ _ si_na c16_P' (tSort sProp) sProp (Sort.super sProp)
           (iv_vass_s iv_Σ [] si_na c16_P' sProp c16_P'_typed Logic.eq_refl)
           (iv_P_typed iv_Σ _ (iv_wf_vass iv_Σ [] si_na c16_P' sProp localenv_nil c16_P'_typed Logic.eq_refl)))).
Qed.
Definition typing_spine_to_extended_listE_inst :=
  typing_spine_to_extended_listE iv_Σ c16_ΔP' [] sProp iv_wfE c16_isT_ΔP'.

(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition wf_projection_contextE_inst :=
  @wf_projection_contextE _ iv_Σ iv_mdecl iv_idecl iv_proj iv_cdecl iv_pdecl [] iv_wfE iv_declared_projection c16_cu.

(** [R (h y)], typed through the η step. *)
Lemma c16_Rhy_typed : iv_Σ ;;; c16_Γh |-E iv_R c16_hy : si_P.
Proof. exact (iv_RX_typed c16_Γh c16_hy c16_wf_Γh c16_hy_typed). Qed.

Definition invert_type_mkApps_indE_inst :=
  invert_type_mkApps_indE iv_Σ c16_Γh iv_ind [] [c16_hy] (tSort sProp) iv_mdecl iv_idecl iv_wfE iv_declared_inductive
    c16_Rhy_typed.
Definition isType_mkApps_Ind_invE_inst :=
  @isType_mkApps_Ind_invE _ iv_Σ c16_Γh iv_ind [] [c16_hy] iv_wfE iv_mdecl iv_idecl iv_declared_inductive c16_wf_Γh
    (has_sort_isTypeE _ c16_Rhy_typed).
Definition isType_mkApps_Ind_inv'E_inst :=
  @isType_mkApps_Ind_inv'E _ iv_Σ c16_Γh iv_ind [] [c16_hy] iv_wfE iv_mdecl iv_idecl iv_declared_inductive c16_wf_Γh
    (has_sort_isTypeE _ c16_Rhy_typed).

(** [r : R (k (λx:Prop. g x))], typed through the η step, projected. *)
Definition projection_subsletE_inst :=
  projection_subsletE iv_Σ c16_Γr iv_mdecl iv_idecl [] (tRel 0) iv_proj iv_cdecl iv_pdecl [c16_keta1]
    iv_declared_projection iv_wfE c16_r_eta c16_isT_Rketa1.

(** The β-step [(λP:Prop. P) (k g) ⇝ k g] in the domain of a product. *)
Definition c16_bkg : term := tApp iv_id iv_kg.
Lemma c16_red_bkg : red iv_Σ iv_Γk c16_bkg iv_kg.
Proof. apply red1_red. unfold c16_bkg, iv_id. apply red_beta. Qed.
Lemma c16_open_bkg_prod T : is_open_term iv_Γk T -> is_open_term iv_Γk (tProd si_na c16_bkg T) ->
  iv_Σ ;;; iv_Γk ⊢ tProd si_na c16_bkg T ⇝ tProd si_na iv_kg T.
Proof.
  intros _ op. apply into_closed_red; [|exact c16_closed_Γk|exact op].
  now eapply red_prod_l, c16_red_bkg.
Qed.
Lemma c16_red_prod_Prop : iv_Σ ;;; iv_Γk ⊢ it_mkProd_or_LetIn [vass si_na c16_bkg] (tSort sProp) ⇝
  tProd si_na iv_kg (tSort sProp).
Proof. apply c16_open_bkg_prod; reflexivity. Qed.

Definition red_it_mkProd_or_LetIn_smashE_inst :=
  @red_it_mkProd_or_LetIn_smashE _ iv_Σ iv_wfE iv_Γk [vass si_na c16_bkg] (tSort sProp)
    (tProd si_na iv_kg (tSort sProp)) 0 (vass si_na c16_bkg) c16_red_prod_Prop Logic.eq_refl.

Lemma c16_red_prod_R : iv_Σ ;;; iv_Γk ⊢ it_mkProd_or_LetIn [vass si_na c16_bkg] (mkApps (tInd iv_ind []) [iv_keta]) ⇝
  tProd si_na iv_kg (mkApps (tInd iv_ind []) [iv_keta]).
Proof. apply c16_open_bkg_prod; reflexivity. Qed.
Definition red_it_mkProd_or_LetIn_mkApps_IndE_inst :=
  @red_it_mkProd_or_LetIn_mkApps_IndE _ iv_Σ iv_wfE iv_Γk [vass si_na c16_bkg] iv_ind [] [iv_keta]
    (tProd si_na iv_kg (mkApps (tInd iv_ind []) [iv_keta])) c16_red_prod_R.

Lemma c16_cred_bkg : iv_Σ ;;; iv_Γk ⊢ c16_bkg ⇝ iv_kg.
Proof. apply into_closed_red; [exact c16_red_bkg|exact c16_closed_Γk|reflexivity]. Qed.
Definition closed_red_it_mkProd_or_LetIn_assum_nthE_inst :=
  @closed_red_it_mkProd_or_LetIn_assum_nthE _ iv_Σ iv_wfE iv_Γk [vass si_na c16_bkg] (tSort sProp) 0
    (vass si_na c16_bkg) iv_kg ltac:(repeat constructor) Logic.eq_refl Logic.eq_refl c16_cred_bkg.

(** [let z := y : k (λx:Prop. g x) in Prop] reduces to its smashed form (a ζ-step). *)
(* IMPOSSIBLE (η): the premises are the booleans [is_closed_context] and [is_open_term], so no
   η derivation can be part of them (the [is_open_term] proof here goes through the typing of
   the let-in, whose body is typed through η). *)
Definition red_it_mkProd_or_LetIn_to_smashE_inst :=
  @red_it_mkProd_or_LetIn_to_smashE _ iv_Σ iv_wfE iv_Γk c16_Δz (tSort sProp) c16_closed_Γk
    (subject_is_open_termE (Σ := iv_Σ) (wfΣ := iv_wfE) c16_Pz_typed).

(** A fixpoint body declaration whose recursive argument has type [(λP:Prop. P) (R (k g))]. *)
Definition c16_bR : term := tApp iv_id (iv_R iv_kg).
Definition c16_fixd : def term :=
  {| dname := si_na; dtype := tProd si_na c16_bR (tSort sProp); dbody := tRel 0; rarg := 0 |}.
Lemma c16_cred_bR : iv_Σ ;;; iv_Γk ⊢ c16_bR ⇝ mkApps (tInd iv_ind []) [iv_kg].
Proof.
  apply into_closed_red; [|exact c16_closed_Γk|reflexivity].
  apply red1_red. unfold c16_bR, iv_id. apply red_beta.
Qed.
Definition red_rec_arg_check_one_fixE_inst :=
  @red_rec_arg_check_one_fixE _ iv_Σ iv_wfE iv_Γk c16_fixd [vass si_na c16_bR] (tSort sProp) (vass si_na c16_bR)
    iv_ind [] [iv_kg] Logic.eq_refl Logic.eq_refl Logic.eq_refl c16_cred_bR.

(** The context [Γk ,,, [z := y] ,,, [w : k (λx:Prop. g x)]]. *)
Definition c16_Δw : context := [vass si_na (lift0 1 iv_keta)].
Lemma c16_wf_Γzw : wf_localE iv_Σ (iv_Γk ,,, c16_Δz ,,, c16_Δw).
Proof. exact (iv_wf_vass iv_Σ c16_Γz si_na (lift0 1 iv_keta) sProp c16_wf_Γz c16_keta_z_typed Logic.eq_refl). Qed.

Definition wf_local_expand_letsE_inst :=
  @wf_local_expand_letsE _ iv_Σ iv_wfE iv_Γk c16_Δz c16_Δw c16_wf_Γzw.
Definition typing_expand_lets_genE_inst :=
  @typing_expand_lets_genE _ iv_Σ iv_wfE iv_Γk c16_Δz [] (tRel 1) (lift0 1 iv_keta) c16_y_eta_z.

Definition map_subst_let_expand_k_to_extended_list_liftE_inst :=
  @map_subst_let_expand_k_to_extended_list_liftE _ iv_Σ [tRel 0] iv_Γk c16_Δx 1 c16_sp_x.
Definition map_subst_let_expand_to_extended_listE_inst :=
  @map_subst_let_expand_to_extended_listE _ iv_Σ [tRel 0] iv_Γk c16_Δx c16_sp_x.

(** [x := y] under [z], for [x : k (λx:Prop. g x)]: typed through η. *)
Definition c16_Δx1 : context := [vass si_na (lift0 1 iv_keta)].
Lemma c16_wf_Γzx : wf_localE iv_Σ (iv_Γk ,,, c16_Δz ,,, [] ,,, c16_Δx1).
Proof. exact c16_wf_Γzw. Qed.
Lemma c16_cs_x1 : context_subst c16_Δx1 [tRel 1] [tRel 1].
Proof. exact (context_subst_ass [] [] [] si_na (lift0 1 iv_keta) (tRel 1) context_subst_nil). Qed.
Definition c16_sub_z : subsletE iv_Σ (iv_Γk ,,, c16_Δz ,,, []) [tRel 1] c16_Δx1 := subslet_ass_tipE c16_y_eta_z.
Definition c16_sp_z : spine_substE iv_Σ (iv_Γk ,,, c16_Δz ,,, []) [tRel 1] [tRel 1] c16_Δx1 :=
  {| spine_dom_wfE := c16_wf_Γz; spine_codom_wfE := c16_wf_Γzx; inst_ctx_substE := c16_cs_x1;
     inst_subsletE := c16_sub_z |}.

Definition subslet_smash_contextE_inst :=
  @subslet_smash_contextE _ iv_Σ iv_wfE iv_Γk c16_Δz [] c16_Δx1 [tRel 1] c16_sub_z.
Definition spine_subst_expand_letsE_inst :=
  @spine_subst_expand_letsE _ iv_Σ iv_wfE iv_Γk c16_Δz [] [tRel 1] [tRel 1] c16_Δx1 c16_sp_z.

(** Case predicates on [R]. *)
Definition c16_ci : case_info := {| ci_ind := iv_ind; ci_npar := 1; ci_relevance := Relevant |}.

(* The context is [Γz], whose let-in body is typed through the η step; the predicate context is
   that of [R]. NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition wf_ind_predicateE_inst :=
  @wf_ind_predicateE _ iv_Σ iv_wfE c16_Γz c16_ci iv_mdecl iv_idecl [] c16_wf_Γz iv_declared_inductive c16_cu.
(* The parameter [h y] is typed through the η step. NOT BUILT (the universe part): as
   [wf_arities_context_instE_inst]. *)
Definition isType_case_predicateE_inst :=
  @isType_case_predicateE _ iv_Σ iv_wfE c16_Γh c16_ci iv_mdecl iv_idecl [] [c16_hy] sProp
    c16_wf_Γh iv_declared_inductive c16_cu c16_wf_sort_Prop c16_sp_hy.

(** The parameters [A := k (λx:Prop. g x)] in [Γr], and no index. *)
Lemma c16_wf_Γrpar : wf_localE iv_Σ (c16_Γr ,,, si_params).
Proof. exact (iv_wf_P iv_Σ c16_Γr c16_wf_Γr). Qed.
Lemma c16_cs_par1 : context_subst si_params [c16_keta1] [c16_keta1].
Proof. exact (context_subst_ass [] [] [] si_na si_P c16_keta1 context_subst_nil). Qed.
Definition c16_sp_par1 : spine_substE iv_Σ c16_Γr [c16_keta1] [c16_keta1] si_params :=
  {| spine_dom_wfE := c16_wf_Γr; spine_codom_wfE := c16_wf_Γrpar; inst_ctx_substE := c16_cs_par1;
     inst_subsletE := subslet_ass_tipE c16_keta1_typed |}.
Definition c16_sp_nil : spine_substE iv_Σ c16_Γr [] [] [] :=
  {| spine_dom_wfE := c16_wf_Γr; spine_codom_wfE := (c16_wf_Γr : wf_localE iv_Σ (c16_Γr ,,, []));
     inst_ctx_substE := context_subst_nil;
     inst_subsletE := emptysletE iv_Σ c16_Γr |}.

(** The scrutinee [r : R (k (λx:Prop. g x))] is typed through the η step. *)
(* NOT BUILT (the universe part): as [wf_arities_context_instE_inst]. *)
Definition arity_spine_case_predicateE_inst :=
  @arity_spine_case_predicateE _ iv_Σ iv_wfE c16_Γr c16_ci iv_mdecl iv_idecl [] [c16_keta1] [] sProp (tRel 0)
    c16_wf_Γr iv_declared_inductive c16_cu c16_wf_sort_Prop c16_sp_par1 c16_sp_nil c16_r_eta.

Definition inductive_ind_ind_bodies_lengthE_inst :=
  inductive_ind_ind_bodies_lengthE iv_Σ iv_ind iv_mdecl iv_idecl iv_wfE iv_declared_inductive.
