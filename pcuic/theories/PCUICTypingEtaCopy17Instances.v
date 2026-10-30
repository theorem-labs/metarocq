(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the hypotheses of [PCUICFixWitnessEta]

  Each lemma of [PCUICFixWitnessEta] that has a premise (the class fields included) is applied
  here to a concrete instance with every premise proved.

  The environment [c17_env]: the inductive [I (A : Prop) : Prop] of [si_env]
  ([PCUICCumulativitySpecEtaClosureInstances]) and, declared after it, an axiom whose type
  [c17_P' := Π F:Prop→Prop. Π G:(Prop→Prop)→Prop. Π a:G F. Π h:(G (λy:Prop. F y) → Prop). h a]
  is typed only through an η step: [h a] needs [a : G F] at [G (λy:Prop. F y)] ([k_a_T] of
  [PCUICTypingEtaCopy15Instances], the step [G (λy:Prop. F y) ≡ G F]). So the proof [c17_wfE] of
  [wfE c17_env] contains that η step, and every instance below whose lemma has a [wfE] premise
  carries it there.

  The context [c17_Γb := [b : h a; h : G (λy:Prop. F y) → Prop; a : G F; G; F]]: the type of [b]
  is typed through the same η step, so [wf_localE] of it does too. The declared type
  [c17_dty := Π x : (λB:Prop. I B) (h a). (λC:Prop. C) (h a)] of the fixpoint body [c17_d] is
  typed through it (twice), [check_one_fix] fails on it (its domain is a β-redex), and its
  reducts [c17_ty1] (domain reduced) and [c17_ty2] (both redexes reduced) pass the check.

  Instances, and where the η step is:
  | lemma | η step in a premise |
  |---|---|
  | [check_one_fix_closed_redE], [check_one_cofix_closed_redE], [shape_check_closed_redE] (both checks), [red_mkApps_smash_witnessE] | in [wfE c17_env] |
  | [mfix_on_ind_red_convE] | in [wfE], [wf_localE c17_Γb] and the [isType] of the declared type |
  | [mfix_body_on_red_uniqueE] | in [wfE] and the typing of the declared type ([on_def_type]) |
  | [wf_local_nth_error_welltypedE] | in [wf_localE c17_Γb] (the entry the lemma reads) |
  | [isType_rec_arg_welltypedE], [welltyped_prod_codomainE] | in [wfE] and the [isTypeE] / [welltypedE] premise |
  | [mfix_body_on_red_convE] | WEAK, IMPOSSIBLE (below) |
  | [shape_check_eq_term_uptoE] | WEAK, IMPOSSIBLE (below) |

  The two WEAK instances are tagged IMPOSSIBLE because of the RULE SETS of the relations in
  their premises, which contain no η rule. Neither lemma carries [wfE Σ] (the premise that
  WOULD hold every declaration's typing derivation, and so could carry an η step); their
  environment premise is checked below in each case, so the tag covers EVERY premise:
  - [mfix_body_on_red_convE]: its premises are [ClosedBodies Σ] (closedness of constant bodies
    and freshness of names), [is_closed_context Γ] and [is_open_term Γ (dtype d)] (booleans of
    [on_free_vars]), and [mfix_body_on check (red Σ Γ) mind d] (an equation on [check] and a
    [red] derivation). [red] is the reflexive-transitive closure of [red1], whose 32
    constructors ([PCUICReduction.v]: 10 head rules [red_beta], [red_zeta], [red_rel],
    [red_iota], [red_fix], [red_cofix_case], [red_cofix_proj], [red_delta], [red_prim_op],
    [red_proj], and 22 congruences) contain no η rule. [ClosedBodies Σ] is the ENVIRONMENT
    premise here, and it is a closedness and freshness statement about the declarations, not a
    typing derivation: it holds no derivation at all, so it can carry no η step, whatever the
    environment is typed through. The instance runs in [c17_env] (its [ClosedBodies] comes from
    [c17_wfE]) on the declared type above.
  - [shape_check_eq_term_uptoE]: its premise is [eq_term_upto_univ], whose 16 constructors
    ([PCUICEquality.v], [eq_Rel] … [eq_Prim]) each relate two terms with the same head
    constructor; none is an η rule. Its [Σ] is only the global environment that
    [eq_term_upto_univ] compares universes in: the field reads no typing of it and takes no
    [wfE], so the lemma has no environment premise that could hold an η step. The instance
    relates two terms that differ in a binder name.
  The Coq lemmas [c17_red_no_eta_contraction] and [c17_eq_term_no_eta] below are spot checks of
  that property, not proofs of the tags: each proves one shape, in one direction, at the top
  level only (a [red] derivation never contracts [λx:A. f x] to [f] when [f] is not a λ; the
  pair with the λ on the left is never related by [eq_term_upto_univ_napp]). They say nothing
  about η-expansion, about steps under a binder, or about the λ on the right.

  The class [ShapeCheckE] is inhabited by [check_one_fix_shapeE] and [check_one_cofix_shapeE]
  ([PCUICFixWitnessEta]). *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICEquality PCUICReduction PCUICClosedBodies PCUICWellScopedCumulativity
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions PCUICClosedTypEta
     PCUICWeakeningEnvTypEta PCUICWeakeningTypEta PCUICSubstitutionEta PCUICWsCumulEtaCtx PCUICEtaC1b
     PCUICCumulativitySpecEtaClosureInstances PCUICTypingEtaCopy15Instances PCUICFixWitness
     PCUICFixWitnessEta.
From Equations.Prop Require Import DepElim.

#[local] Existing Instance default_checker_flags.

(** ** Binder judgments *)

Lemma c17_vass {Σ : global_env_ext} (na : aname) (Γ : context) T s :
  Σ ;;; Γ |-E T : tSort s -> isSortRel s na.(binder_relevance) ->
  PCUICTyping.lift_typing typingE Σ Γ (j_vass na T).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma c17_vass_s {Σ : global_env_ext} (na : aname) (Γ : context) T s :
  Σ ;;; Γ |-E T : tSort s -> isSortRel s na.(binder_relevance) ->
  PCUICTyping.lift_typing typingE Σ Γ (j_vass_s na T s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

(** ** The η step, in the empty environment [rf_Σ] *)

(** [c17_Γh := [h : G (λy:Prop. F y) → Prop; a : G F; G; F]]. *)
Definition c17_Γh : context := k_Γ ,, vass c1b_na k_PT.

Lemma c17_wf_Γh : wf_localE rf_Σ c17_Γh.
Proof. apply localenv_cons_abs; [exact k_wf_Γ|exact (c17_vass c1b_na k_Γ k_PT _ k_PT_typed Logic.eq_refl)]. Qed.

(** [h a] in [c17_Γh]. *)
Definition c17_hy : term := tApp (tRel 0) (tRel 1).

Lemma c17_a_T_h : rf_Σ ;;; c17_Γh |-E tRel 1 : lift0 1 k_T.
Proof. exact (weakeningE rf_Σ k_Γ [vass c1b_na k_PT] (tRel 0) k_T wc_wfE c17_wf_Γh k_a_T). Qed.

Lemma c17_PT_h : rf_Σ ;;; c17_Γh |-E lift0 1 k_PT : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
Proof. exact (weakeningE rf_Σ k_Γ [vass c1b_na k_PT] k_PT _ wc_wfE c17_wf_Γh k_PT_typed). Qed.

Lemma c17_h_typed : rf_Σ ;;; c17_Γh |-E tRel 0 : lift0 1 k_PT.
Proof. exact (typeE_Rel _ _ 0 (vass c1b_na k_PT) c17_wf_Γh Logic.eq_refl). Qed.

(** The η step is inside this derivation (through [k_a_T]). *)
Lemma c17_hy_typed : rf_Σ ;;; c17_Γh |-E c17_hy : tSort sProp.
Proof.
  exact (typeE_App _ _ (tRel 0) c1b_na (lift0 1 k_T) (tSort sProp) _ (tRel 1) c17_PT_h c17_h_typed c17_a_T_h).
Qed.

(** [c17_Γb := [b : h a] ++ c17_Γh]: the type of [b] is typed through the η step. *)
Definition c17_Γb : context := c17_Γh ,, vass c1b_na c17_hy.

Lemma c17_wf_Γb : wf_localE rf_Σ c17_Γb.
Proof. apply localenv_cons_abs; [exact c17_wf_Γh|exact (c17_vass c1b_na c17_Γh c17_hy _ c17_hy_typed Logic.eq_refl)]. Qed.

(** The closed proposition [c17_P'], typed through the η step. *)
Definition c17_P4 : term := tProd c1b_na k_PT c17_hy.
Definition c17_P3 : term := tProd c1b_na wc_U c17_P4.
Definition c17_P2 : term := tProd c1b_na wc_G_ty c17_P3.
Definition c17_P' : term := tProd c1b_na rf_F c17_P2.

Lemma c17_P4_typed : rf_Σ ;;; k_Γ |-E c17_P4 : tSort sProp.
Proof.
  exact (typeE_Prod _ _ c1b_na k_PT c17_hy (Sort.sort_of_product sProp (Sort.super sProp)) sProp
           (c17_vass_s c1b_na k_Γ k_PT _ k_PT_typed Logic.eq_refl) c17_hy_typed).
Qed.

Lemma c17_P3_typed : rf_Σ ;;; wc_Γ |-E c17_P3 : tSort sProp.
Proof.
  exact (typeE_Prod _ _ c1b_na wc_U c17_P4 sProp sProp
           (c17_vass_s c1b_na wc_Γ wc_U sProp wc_U_typed Logic.eq_refl) c17_P4_typed).
Qed.

Lemma c17_P2_typed : rf_Σ ;;; rf_Γ |-E c17_P2 : tSort sProp.
Proof.
  exact (typeE_Prod _ _ c1b_na wc_G_ty c17_P3 _ sProp
           (c17_vass_s c1b_na rf_Γ wc_G_ty _ (wc_G_ty_typed rf_Γ rf_wf_Γ) Logic.eq_refl) c17_P3_typed).
Qed.

Lemma c17_P'_typed : rf_Σ ;;; [] |-E c17_P' : tSort sProp.
Proof.
  exact (typeE_Prod _ _ c1b_na rf_F c17_P2 _ sProp
           (c17_vass_s c1b_na [] rf_F _ (rf_F_typed [] localenv_nil) Logic.eq_refl) c17_P2_typed).
Qed.

(** ** The environment [c17_env]: [si_env] and the axiom [c17_ax : c17_P'] *)

Definition c17_kn : kername := (MPfile ["FWInst"], "ax").
Definition c17_cb : constant_body :=
  {| cst_type := c17_P'; cst_body := None; cst_universes := Monomorphic_ctx; cst_relevance := Relevant |}.
Definition c17_env : global_env :=
  {| universes := ContextSet.empty;
     declarations := [(c17_kn, ConstantDecl c17_cb); (si_kn, InductiveDecl si_mdecl)];
     retroknowledge := Retroknowledge.empty |}.
Definition c17_Σ : global_env_ext := (c17_env, Monomorphic_ctx).

Lemma c17_ext_si : PCUICEnvironment.extends rf_Σ.1 si_env.
Proof.
  eapply extends_strictly_on_decls_extends.
  split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
  now exists [(si_kn, InductiveDecl si_mdecl)].
Qed.

Lemma c17_P'_typed_si : si_Σ ;;; [] |-E c17_P' : tSort sProp.
Proof. exact (env_propE_typing weakening_envE rf_Σ wc_wfE [] _ _ c17_P'_typed si_env wc_wfE si_wfE c17_ext_si). Qed.

Lemma c17_on_constant : on_constant_decl (PCUICTyping.lift_typing typingE) si_Σ c17_cb.
Proof. split; [exact tt|]. exists sProp. split; [exact c17_P'_typed_si|]. split; [exact I|reflexivity]. Qed.

(** [wfE c17_env]: its constant is typed through the η step. *)
Lemma c17_wfE : wfE c17_env.
Proof.
  split; [exact (fst si_wfE)|]. split; [exact (fst (snd si_wfE))|].
  apply globenv_decl; [exact (snd (snd si_wfE))|].
  constructor.
  - constructor; [discriminate|constructor].
  - exact si_on_udecl.
  - exact c17_on_constant.
  - cbn. intros op h. discriminate h.
Qed.

Definition c17_cbs : ClosedBodies c17_env := @wfE_ClosedBodies _ c17_env c17_wfE.
#[local] Existing Instance c17_cbs.

Lemma c17_ext : PCUICEnvironment.extends rf_Σ.1 c17_env.
Proof.
  eapply extends_strictly_on_decls_extends.
  split => //=. eapply incl_cs_refl. 2:eapply Retroknowledge.extends_refl.
  now exists [(c17_kn, ConstantDecl c17_cb); (si_kn, InductiveDecl si_mdecl)].
Qed.

Definition c17_wty {Γ t T} (h : rf_Σ ;;; Γ |-E t : T) : c17_Σ ;;; Γ |-E t : T :=
  env_propE_typing weakening_envE rf_Σ wc_wfE Γ t T h c17_env wc_wfE c17_wfE c17_ext.

Definition c17_wloc {Γ} (h : wf_localE rf_Σ Γ) : wf_localE c17_Σ Γ :=
  PCUICWeakeningEnvTypEta.weaken_wf_localE rf_Σ c17_env Γ wc_wfE c17_ext c17_wfE h.

(** ** Typing in [c17_Σ] *)

Lemma c17_declared_inductive : declared_inductive c17_Σ si_ind si_mdecl si_idecl.
Proof. split; [right; left; reflexivity|reflexivity]. Qed.

Lemma c17_I_typed (Γ : context) : wf_localE c17_Σ Γ -> c17_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
Proof. intros h. exact (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h c17_declared_inductive Logic.eq_refl). Qed.

Lemma c17_P_typed (Γ : context) : wf_localE c17_Σ Γ -> c17_Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

Lemma c17_wf_P (Γ : context) : wf_localE c17_Σ Γ -> wf_localE c17_Σ (Γ ,, vass si_na si_P).
Proof. intros h. apply localenv_cons_abs; [exact h|exact (c17_vass si_na Γ si_P _ (c17_P_typed Γ h) Logic.eq_refl)]. Qed.

Lemma c17_arity_typed (Γ : context) : wf_localE c17_Σ Γ ->
  c17_Σ ;;; Γ |-E si_arity : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
Proof.
  intros h. apply typeE_Prod; [exact (c17_vass_s si_na Γ si_P _ (c17_P_typed Γ h) Logic.eq_refl)|].
  exact (c17_P_typed _ (c17_wf_P Γ h)).
Qed.

(** [λB:Prop. I B] and [λC:Prop. C], both of type [Prop → Prop]. *)
Definition c17_lamI : term := tLambda si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Definition c17_lamC : term := tLambda si_na si_P (tRel 0).

Lemma c17_lamI_typed (Γ : context) : wf_localE c17_Σ Γ -> c17_Σ ;;; Γ |-E c17_lamI : si_arity.
Proof.
  intros h. have h1 := c17_wf_P Γ h.
  apply typeE_Lambda; [exact (c17_vass si_na Γ si_P _ (c17_P_typed Γ h) Logic.eq_refl)|].
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P (tSort sProp) _ (tRel 0) (c17_arity_typed _ h1)
           (c17_I_typed _ h1) (typeE_Rel _ _ 0 (vass si_na si_P) h1 Logic.eq_refl)).
Qed.

Lemma c17_lamC_typed (Γ : context) : wf_localE c17_Σ Γ -> c17_Σ ;;; Γ |-E c17_lamC : si_arity.
Proof.
  intros h. apply typeE_Lambda; [exact (c17_vass si_na Γ si_P _ (c17_P_typed Γ h) Logic.eq_refl)|].
  exact (typeE_Rel _ _ 0 (vass si_na si_P) (c17_wf_P Γ h) Logic.eq_refl).
Qed.

Lemma c17_app_typed (Γ : context) f A : wf_localE c17_Σ Γ ->
  c17_Σ ;;; Γ |-E f : si_arity -> c17_Σ ;;; Γ |-E A : si_P -> c17_Σ ;;; Γ |-E tApp f A : tSort sProp.
Proof. intros h hf hA. exact (typeE_App _ _ f si_na si_P (tSort sProp) _ A (c17_arity_typed Γ h) hf hA). Qed.

Definition c17_wf_Γh_x : wf_localE c17_Σ c17_Γh := c17_wloc c17_wf_Γh.
Definition c17_wf_Γb_x : wf_localE c17_Σ c17_Γb := c17_wloc c17_wf_Γb.
Definition c17_hy_typed_x : c17_Σ ;;; c17_Γh |-E c17_hy : tSort sProp := c17_wty c17_hy_typed.

(** [h a] in [c17_Γb], typed through the η step. *)
Definition c17_hb : term := lift0 1 c17_hy.

Lemma c17_hb_typed : c17_Σ ;;; c17_Γb |-E c17_hb : si_P.
Proof. exact (c17_wty (weakeningE rf_Σ c17_Γh [vass c1b_na c17_hy] c17_hy (tSort sProp) wc_wfE c17_wf_Γb c17_hy_typed)). Qed.

(** ** The fixpoint body [c17_d] and its reducts *)

Definition c17_D : term := tApp c17_lamI c17_hb.
Definition c17_C : term := tApp c17_lamC (lift0 1 c17_hb).
Definition c17_dty : term := tProd c1b_na c17_D c17_C.
Definition c17_ty1 : term := tProd c1b_na (tApp (tInd si_ind []) c17_hb) c17_C.
Definition c17_ty2 : term := tProd c1b_na (tApp (tInd si_ind []) c17_hb) (lift0 1 c17_hb).
Definition c17_d : def term := {| dname := c1b_na; dtype := c17_dty; dbody := tRel 0; rarg := 0 |}.

Lemma c17_D_typed : c17_Σ ;;; c17_Γb |-E c17_D : tSort sProp.
Proof. exact (c17_app_typed _ _ _ c17_wf_Γb_x (c17_lamI_typed _ c17_wf_Γb_x) c17_hb_typed). Qed.

Lemma c17_wf_Γbx : wf_localE c17_Σ (c17_Γb ,, vass c1b_na c17_D).
Proof. apply localenv_cons_abs; [exact c17_wf_Γb_x|exact (c17_vass c1b_na c17_Γb c17_D _ c17_D_typed Logic.eq_refl)]. Qed.

Lemma c17_C_typed : c17_Σ ;;; c17_Γb ,, vass c1b_na c17_D |-E c17_C : tSort sProp.
Proof.
  have hb := weakeningE c17_Σ c17_Γb [vass c1b_na c17_D] c17_hb si_P c17_wfE c17_wf_Γbx c17_hb_typed.
  exact (c17_app_typed _ _ _ c17_wf_Γbx (c17_lamC_typed _ c17_wf_Γbx) hb).
Qed.

Lemma c17_dty_typed : c17_Σ ;;; c17_Γb |-E c17_dty : tSort (Sort.sort_of_product sProp sProp).
Proof.
  exact (typeE_Prod _ _ c1b_na c17_D c17_C sProp sProp (c17_vass_s c1b_na c17_Γb c17_D _ c17_D_typed Logic.eq_refl)
           c17_C_typed).
Qed.

Lemma c17_isT_dty : isTypeE c17_Σ c17_Γb c17_dty.
Proof. exact (has_sort_isTypeE _ c17_dty_typed). Qed.

Lemma c17_red1 : red c17_Σ c17_Γb c17_dty c17_ty1.
Proof.
  apply red1_red. apply prod_red_l.
  exact (@red_beta c17_Σ c17_Γb si_na si_P (tApp (tInd si_ind []) (tRel 0)) c17_hb).
Qed.

Lemma c17_red2 : red c17_Σ c17_Γb c17_dty c17_ty2.
Proof.
  etransitivity; [exact c17_red1|].
  apply red1_red. apply prod_red_r.
  exact (@red_beta c17_Σ (c17_Γb ,, vass c1b_na (tApp (tInd si_ind []) c17_hb)) si_na si_P (tRel 0) (lift0 1 c17_hb)).
Qed.

Lemma c17_check_dty : check_one_fix c17_d = None.
Proof. reflexivity. Qed.

Lemma c17_check_ty1 : check_one_fix (def_with_type c17_d c17_ty1) = Some si_kn.
Proof. reflexivity. Qed.

Lemma c17_check_ty2 : check_one_fix (def_with_type c17_d c17_ty2) = Some si_kn.
Proof. reflexivity. Qed.

Lemma c17_closed_Γb : is_closed_context c17_Γb.
Proof. reflexivity. Qed.

Lemma c17_open_dty : is_open_term c17_Γb c17_dty.
Proof. reflexivity. Qed.

(** ** Spot checks of the rule-set property behind the two WEAK instances (one shape, one
    direction, top level only; the tags rest on the constructor lists, see the header) *)

Lemma c17_red1_lambda_head (Σ : global_env) (Γ : context) na A b u :
  red1 Σ Γ (tLambda na A b) u -> ∑ A' b', u = tLambda na A' b'.
Proof.
  intros h. depelim h; try solve [do 2 eexists; reflexivity].
  all: match goal with H : tLambda _ _ _ = mkApps _ _ |- _ =>
         apply (f_equal decompose_app) in H; rewrite decompose_app_mkApps in H; cbn in *; try discriminate; done end.
Qed.

Lemma c17_red_lambda_head (Σ : global_env) (Γ : context) na A b u :
  red Σ Γ (tLambda na A b) u -> ∑ A' b', u = tLambda na A' b'.
Proof.
  intros h. remember (tLambda na A b) as t eqn:e. induction h in na, A, b, e |- *; subst.
  - eapply c17_red1_lambda_head; eassumption.
  - do 2 eexists; reflexivity.
  - destruct (IHh1 _ _ _ Logic.eq_refl) as (A' & b' & ->). exact (IHh2 _ _ _ Logic.eq_refl).
Qed.

(** An η-contraction [λx:A. f x ⇝ f] is never a [red] derivation when [f] is not a λ. *)
Lemma c17_red_no_eta_contraction (Σ : global_env) (Γ : context) na A f :
  isLambda f = false -> red Σ Γ (tLambda na A (tApp (lift0 1 f) (tRel 0))) f -> False.
Proof. intros hf h. destruct (c17_red_lambda_head _ _ _ _ _ _ h) as (A' & b' & ->). discriminate hf. Qed.

Lemma c17_eq_term_lambda_head Σ cmp_universe cmp_sort pb napp na A b u :
  eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tLambda na A b) u -> ∑ na' A' b', u = tLambda na' A' b'.
Proof. intros h. depelim h; do 3 eexists; reflexivity. Qed.

(** An η pair [λx:A. f x], [f] is never related by [eq_term_upto_univ] when [f] is not a λ. *)
Lemma c17_eq_term_no_eta Σ cmp_universe cmp_sort pb napp na A f :
  isLambda f = false -> eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp (tLambda na A (tApp (lift0 1 f) (tRel 0))) f -> False.
Proof. intros hf h. destruct (c17_eq_term_lambda_head _ _ _ _ _ _ _ _ _ h) as (na' & A' & b' & ->). discriminate hf. Qed.

(** ** The instances *)

(** [check_one_fix_closed_redE]: in [c17_Σ] (η in [wfE]); the codomain of a type whose recursive
    argument is [I Prop] is β-reduced. *)
Definition c17_fty : term := tProd c1b_na (tApp (tInd si_ind []) si_P) (tApp c17_lamC si_P).
Definition c17_fv : term := tProd c1b_na (tApp (tInd si_ind []) si_P) si_P.
Definition c17_fd : def term := {| dname := c1b_na; dtype := c17_fty; dbody := tRel 0; rarg := 0 |}.

Lemma c17_fty_red : c17_Σ ;;; [] ⊢ c17_fty ⇝ c17_fv.
Proof.
  split; [reflexivity|reflexivity|]. apply red1_red. apply prod_red_r.
  exact (@red_beta c17_Σ ([] ,, vass c1b_na (tApp (tInd si_ind []) si_P)) si_na si_P (tRel 0) si_P).
Qed.

Definition check_one_fix_closed_redE_inst :
  check_one_fix (def_with_type c17_fd c17_fv) = Some si_kn :=
  @check_one_fix_closed_redE _ c17_Σ c17_wfE [] c17_fd c17_fty c17_fv si_kn c17_fty_red Logic.eq_refl.

Definition shape_check_closed_redE_fix_inst :
  check_one_fix (def_with_type c17_fd c17_fv) = Some si_kn :=
  @shape_check_closed_redE check_one_fix check_one_fix_shapeE _ c17_Σ c17_wfE [] c17_fd c17_fty c17_fv si_kn
    c17_fty_red Logic.eq_refl.

(** [check_one_cofix_closed_redE]: the argument of the conclusion [I ((λC:Prop. C) x)] is β-reduced. *)
Definition c17_cty : term := tProd c1b_na si_P (tApp (tInd si_ind []) (tApp c17_lamC (tRel 0))).
Definition c17_cv : term := tProd c1b_na si_P (tApp (tInd si_ind []) (tRel 0)).
Definition c17_cd : def term := {| dname := c1b_na; dtype := c17_cty; dbody := tRel 0; rarg := 0 |}.

Lemma c17_cty_red : c17_Σ ;;; [] ⊢ c17_cty ⇝ c17_cv.
Proof.
  split; [reflexivity|reflexivity|]. apply red1_red. apply prod_red_r. apply app_red_r.
  exact (@red_beta c17_Σ ([] ,, vass c1b_na si_P) si_na si_P (tRel 0) (tRel 0)).
Qed.

Definition check_one_cofix_closed_redE_inst :
  PCUICTyping.check_one_cofix (def_with_type c17_cd c17_cv) = Some si_kn :=
  @check_one_cofix_closed_redE _ c17_Σ c17_wfE [] c17_cd c17_cty c17_cv si_kn c17_cty_red Logic.eq_refl.

Definition shape_check_closed_redE_cofix_inst :
  PCUICTyping.check_one_cofix (def_with_type c17_cd c17_cv) = Some si_kn :=
  @shape_check_closed_redE PCUICTyping.check_one_cofix check_one_cofix_shapeE _ c17_Σ c17_wfE [] c17_cd c17_cty
    c17_cv si_kn c17_cty_red Logic.eq_refl.

(** [shape_check_eq_term_uptoE] (WEAK, IMPOSSIBLE): two types that differ in a binder name. *)
Definition c17_na' : aname := mkBindAnn (nNamed "x") Relevant.
Definition c17_fty' : term := tProd c17_na' (tApp (tInd si_ind []) si_P) (tApp c17_lamC si_P).

Lemma c17_eq_fty : compare_term c17_Σ c17_Σ Conv c17_fty c17_fty'.
Proof. eapply eq_Prod; reflexivity. Qed.

Definition shape_check_eq_term_uptoE_inst :
  check_one_fix (def_with_type c17_fd c17_fty) = check_one_fix (def_with_type c17_fd c17_fty') :=
  @shape_check_eq_term_uptoE check_one_fix check_one_fix_shapeE c17_Σ _ _ c17_fd c17_fty c17_fty' c17_eq_fty.

(** [mfix_body_on_red_convE] (WEAK, IMPOSSIBLE): the declared type [c17_dty] in [c17_Γb], whose
    reduct [c17_ty1] passes [check_one_fix]. *)
Definition mfix_body_on_red_convE_inst :
  mfix_body_on check_one_fix (conv_witnessE c17_Σ c17_Γb) si_kn c17_d :=
  @mfix_body_on_red_convE _ c17_Σ c17_cbs check_one_fix c17_Γb si_kn c17_d c17_closed_Γb c17_open_dty
    (c17_ty1; (c17_check_ty1, c17_red1)).

(** [mfix_on_ind_red_convE]: η in [wfE], [wf_localE c17_Γb] and the [isType] of [c17_dty]. *)
Definition c17_ok : kername -> bool := fun mind => check_recursivity_kind (lookup_env c17_Σ) mind Finite.

Lemma c17_mfix_red : mfix_on_ind check_one_fix (red c17_Σ c17_Γb) c17_ok [c17_d].
Proof.
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [exact (c17_ty1; (c17_check_ty1, c17_red1))|constructor].
Qed.

Lemma c17_all_isT : All (fun d => on_type (PCUICTyping.lift_typing typingE) c17_Σ c17_Γb (dtype d)) [c17_d].
Proof. constructor; [exact c17_isT_dty|constructor]. Qed.

Definition mfix_on_ind_red_convE_inst :
  mfix_on_ind check_one_fix (conv_witnessE c17_Σ c17_Γb) c17_ok [c17_d] :=
  @mfix_on_ind_red_convE _ c17_Σ c17_wfE check_one_fix c17_ok c17_Γb [c17_d] c17_wf_Γb_x
    c17_all_isT c17_mfix_red.

(** [mfix_body_on_red_uniqueE]: two different reducts of [c17_dty] give the same block. *)
Lemma c17_ond : on_def_type (PCUICTyping.lift_typing1 (typingE c17_Σ)) c17_Γb c17_d.
Proof. exact (c17_vass c1b_na c17_Γb c17_dty _ c17_dty_typed Logic.eq_refl). Qed.

Definition mfix_body_on_red_uniqueE_inst : si_kn = si_kn :=
  @mfix_body_on_red_uniqueE _ c17_Σ c17_wfE check_one_fix check_one_fix_shapeE c17_Γb c17_d si_kn si_kn c17_ond
    (c17_ty1; (c17_check_ty1, c17_red1)) (c17_ty2; (c17_check_ty2, c17_red2)).

(** [wf_local_nth_error_welltypedE]: the entry [b : h a] of [c17_Γb], typed through η. *)
Definition wf_local_nth_error_welltypedE_inst : welltypedE c17_Σ (skipn 1 c17_Γb) c17_hy :=
  @wf_local_nth_error_welltypedE _ c17_Σ c17_Γb 0 (vass c1b_na c17_hy) c17_wf_Γb_x Logic.eq_refl.

(** [isType_rec_arg_welltypedE]: [Π b : h a. Prop] in [c17_Γh]; its argument type is [h a]. *)
Definition c17_Thb : term := tProd c1b_na c17_hy (tSort sProp).

Lemma c17_isT_Thb : isTypeE c17_Σ c17_Γh c17_Thb.
Proof.
  apply (has_sort_isTypeE (Sort.sort_of_product sProp (Sort.super sProp))).
  apply typeE_Prod; [exact (c17_vass_s c1b_na c17_Γh c17_hy _ c17_hy_typed_x Logic.eq_refl)|].
  apply typeE_Sort; [exact (c17_wloc c17_wf_Γb)|cbn; trivial].
Qed.

Definition isType_rec_arg_welltypedE_inst :=
  @isType_rec_arg_welltypedE _ c17_Σ c17_wfE c17_Γh c17_Thb [vass c1b_na c17_hy] (tSort sProp) 0
    (vass c1b_na c17_hy) c17_isT_Thb Logic.eq_refl Logic.eq_refl.

(** [welltyped_prod_codomainE]: [Π z : Prop. h a] in [c17_Γh]; its codomain is typed through η. *)
Lemma c17_wt_prod : welltypedE c17_Σ c17_Γh (tProd si_na si_P (lift0 1 c17_hy)).
Proof.
  pose proof (c17_wf_P c17_Γh c17_wf_Γh_x) as w.
  econstructor. apply typeE_Prod; [exact (c17_vass_s si_na c17_Γh si_P _ (c17_P_typed _ c17_wf_Γh_x) Logic.eq_refl)|].
  exact (weakeningE c17_Σ c17_Γh [vass si_na si_P] c17_hy (tSort sProp) c17_wfE w c17_hy_typed_x).
Qed.

Definition welltyped_prod_codomainE_inst :=
  @welltyped_prod_codomainE _ c17_Σ c17_wfE c17_Γh si_na si_P (lift0 1 c17_hy) c17_wt_prod.

(** [red_mkApps_smash_witnessE]: a β-redex reduces to [let x := Prop : Type in I x]; the witness
    smashes the let-in. *)
Definition c17_let_ctx : context := [vdef c1b_na si_P (tSort (Sort.super sProp))].
Definition c17_let : term := it_mkProd_or_LetIn c17_let_ctx (mkApps (tInd si_ind []) [tRel 0]).
Definition c17_redex : term := tApp (tLambda c1b_na si_P c17_let) si_P.

Lemma c17_redex_red : c17_Σ ;;; [] ⊢ c17_redex ⇝ it_mkProd_or_LetIn c17_let_ctx (mkApps (tInd si_ind []) [tRel 0]).
Proof.
  split; [reflexivity|reflexivity|]. apply red1_red.
  exact (@red_beta c17_Σ [] c1b_na si_P c17_let si_P).
Qed.

Definition red_mkApps_smash_witnessE_inst :=
  @red_mkApps_smash_witnessE _ c17_Σ c17_wfE [] c17_redex c17_let_ctx si_ind [] [tRel 0] c17_redex_red.
