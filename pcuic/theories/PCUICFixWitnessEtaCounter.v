(* Distributed under the terms of the MIT license. *)

(** * The closed-only E forms of the (co)fixpoint witness lemmas are false

  Base [mfix_body_on_conv_closed_red] ([PCUICFixWitness]) turns the conversion
  witness of [wf_fixpoint]/[wf_cofixpoint] into a reduction witness, from the
  premises [wf Σ], [is_closed_context Γ] and [is_open_term Γ (dtype d)] only. Its
  proof reads the conversion off common reducts ([ws_cumul_pb_alt_closed]). With
  [conv_witness] replaced by [conv_witnessE] (η conversion, [PCUICTypingEta]) and
  nothing else changed, the statement is false. Each theorem below takes the E form
  as a hypothesis and derives [False]:

  - [mfix_body_on_conv_closed_redE_fix_false]: at [check := check_one_fix]
    (instance [check_one_fix_shape]);
  - [mfix_body_on_conv_closed_redE_cofix_false]: at [check := check_one_cofix]
    (instance [check_one_cofix_shape]);
  - [mfix_body_on_conv_closed_redE_false]: the form generic in the check;
  - [wf_cofixpoint_allE_false]: the E form of [wf_cofixpoint_all]
    ([PCUICInductiveInversion]), with [wf_cofixpoint] replaced by [wf_cofixpointE].

  **Witness.** [fwe_I] is [tInd fwe_ind []], the inductive of the environment
  [fwe_env]: [CoInductive I (A : Prop) : Prop :=], no constructor ([fwe_wf] proves
  it well-formed). [fwe_lam = λy:Prop. I y] is the η-expansion of [I]
  ([cumulSpecE_eta_contract]). [check_one_fix] and [check_one_cofix] are syntactic:
  they need a [tInd] head where [fwe_lam] has a λ.
  - Fixpoint: [fwe_fix_ty = Π(x : I). Prop] passes [check_one_fix] at [rarg = 0];
    the declared type [fwe_fix_dtype = Π(x : λy:Prop. I y). Prop] is η-convertible
    to it (η in the domain).
  - Cofixpoint: [fwe_cofix_ty = I] passes [check_one_cofix]; the declared type is
    [fwe_lam] itself (η at the head of the codomain).
  Both declared types are [red1]-normal in every environment and context
  ([fwe_red_normal_fix_dtype], [fwe_red_normal_lam]), so their only reduct is
  themselves, and the check fails on them ([fwe_check_fix_dtype],
  [fwe_check_cofix_dtype]).

  **What is refuted, and what is not.** The witness is NOT typable as a type: a λ
  has a product type up to [ws_cumul_pbE] ([typingE_Lambda_prod]), so it is never
  typed at a sort ([lambda_not_sortE]); hence neither declared type is a type, over
  [typingE] under [wfE Σ] ([fwe_fix_dtype_not_typeE], [fwe_cofix_dtype_not_typeE])
  and over base [typing] under [wf Σ] ([fwe_fix_dtype_not_type],
  [fwe_cofix_dtype_not_type]). [fwe_lam] itself is well typed, at [Prop → Prop]
  ([fwe_lam_typed]): only its use as a type fails. So these theorems refute ONLY
  the closed-only forms (premises [is_closed_context Γ] / [is_open_term Γ (dtype d)]);
  a form with a typing premise on [dtype d] is not refuted here and remains open. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars
     PCUICReduction PCUICArityRed PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICCumulativitySpecEtaClosureInstances PCUICTypingEta PCUICWellScopedCumulativity
     PCUICFixWitness PCUICClosedBodies PCUICClosedTypEta PCUICWellScopedCumulativityEta
     PCUICEtaA6 PCUICEtaC1b.

Import PCUICOnFreeVars (is_open_term, is_closed_context).

Implicit Types (cf : checker_flags).

(** ** The environment: [CoInductive I (A : Prop) : Prop :=], no constructor *)

Definition fwe_kn : kername := (MPfile ["FixWitnessEta"], "I").
Definition fwe_ind : inductive := {| inductive_mind := fwe_kn; inductive_ind := 0 |}.
Definition fwe_na : aname := mkBindAnn nAnon Relevant.

Definition fwe_idecl : one_inductive_body :=
  {| ind_name := "I"; ind_indices := []; ind_sort := sProp; ind_type := si_arity;
     ind_kelim := IntoAny; ind_ctors := []; ind_projs := []; ind_relevance := Relevant |}.

Definition fwe_mdecl : mutual_inductive_body :=
  {| ind_finite := CoFinite; ind_npars := 1; ind_params := si_params; ind_bodies := [fwe_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition fwe_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(fwe_kn, InductiveDecl fwe_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition fwe_Σ : global_env_ext := (fwe_env, Monomorphic_ctx).

Section Declaration.
  #[local] Existing Instance default_checker_flags.

  (** The declaration is checked in the empty environment [si_Σ0]; its arity and
      parameters are those of [si_mdecl] ([PCUICCumulativitySpecEtaClosureInstances]). *)
  Lemma fwe_on_ind_body :
    on_ind_body cumulSpec0 (lift_typing typing) si_Σ0 fwe_kn fwe_mdecl 0 fwe_idecl.
  Proof.
    unshelve econstructor.
    - exact [].
    - exists (tSort sProp). split; [reflexivity|].
      apply arity_red_sort. apply whd_stop. reflexivity.
    - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
    - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
    - constructor.
    - exact I.
    - reflexivity.
    - reflexivity.
    - exact I.
  Qed.

  Lemma fwe_on_inductive : on_inductive cumulSpec0 (lift_typing typing) si_Σ0 fwe_kn fwe_mdecl.
  Proof.
    constructor.
    - constructor; [exact fwe_on_ind_body|constructor].
    - exact (si_wf_P [] si_wf_nil).
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma fwe_wf : wf fwe_env.
  Proof.
    split.
    - split; [|split].
      + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
      + intros x Hx.
        change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                              (LevelSet.singleton Level.lzero))) in Hx.
        apply LevelSet.union_spec in Hx as [Hx|Hx].
        * exfalso. eapply LevelSet.empty_spec. exact Hx.
        * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
      + exists si_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    - split.
      { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                          |intros i h; discriminate h]. }
      apply globenv_decl; [constructor|].
      constructor.
      + constructor.
      + exact si_on_udecl.
      + exact fwe_on_inductive.
      + (* on_prim_decl: no boolean type is registered *)
        cbn. intros i h; discriminate h.
  Qed.

  Lemma fwe_wfE : wfE fwe_env.
  Proof. exact (wf_incl_E fwe_wf). Qed.

End Declaration.

(** ** The witness terms *)

Definition fwe_I : term := tInd fwe_ind [].
Definition fwe_T : term := tSort sProp.

(** [λy:Prop. I y], the η-expansion of [I]. *)
Definition fwe_lam : term := tLambda fwe_na fwe_T (tApp fwe_I (tRel 0)).

(** Fixpoint: the checked type and the declared type. *)
Definition fwe_fix_ty : term := tProd fwe_na fwe_I (tSort sProp).
Definition fwe_fix_dtype : term := tProd fwe_na fwe_lam (tSort sProp).
Definition fwe_fix_d : def term :=
  {| dname := fwe_na; dtype := fwe_fix_dtype; dbody := tRel 0; rarg := 0 |}.

(** Cofixpoint: the checked type and the declared type. *)
Definition fwe_cofix_ty : term := fwe_I.
Definition fwe_cofix_d : def term :=
  {| dname := fwe_na; dtype := fwe_lam; dbody := tRel 0; rarg := 0 |}.

(** ** What the checks see *)

Lemma fwe_check_fix_ty : check_one_fix (def_with_type fwe_fix_d fwe_fix_ty) = Some fwe_kn.
Proof. reflexivity. Qed.

Lemma fwe_check_fix_dtype : check_one_fix (def_with_type fwe_fix_d fwe_fix_dtype) = None.
Proof. reflexivity. Qed.

Lemma fwe_check_cofix_ty : check_one_cofix (def_with_type fwe_cofix_d fwe_cofix_ty) = Some fwe_kn.
Proof. reflexivity. Qed.

Lemma fwe_check_cofix_dtype : check_one_cofix (def_with_type fwe_cofix_d fwe_lam) = None.
Proof. reflexivity. Qed.

(** ** The declared types are [red1]-normal, in every environment and context *)

Lemma fwe_red_normal_Ind Σ Γ i u v : red1 Σ Γ (tInd i u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma fwe_red_normal_body Σ Γ na X v : red1 Σ (Γ ,, vass na X) (tApp fwe_I (tRel 0)) v -> False.
Proof.
  unfold fwe_I. intros H. inv_red H.
  all: first [eapply fwe_red_normal_Ind; eassumption | eapply red_normal_Rel0; eassumption].
Qed.

Lemma fwe_red_normal_lam Σ Γ v : red1 Σ Γ fwe_lam v -> False.
Proof.
  exact (red_normal_lam Σ Γ fwe_na fwe_T (tApp fwe_I (tRel 0))
           (fun v => red_normal_Sort Σ Γ sProp v) (fwe_red_normal_body Σ Γ fwe_na fwe_T) v).
Qed.

Lemma fwe_red_normal_fix_dtype Σ Γ v : red1 Σ Γ fwe_fix_dtype v -> False.
Proof.
  unfold fwe_fix_dtype. intros H. inv_red H.
  all: first [eapply fwe_red_normal_lam; eassumption | eapply red_normal_Sort; eassumption].
Qed.

(** ** The premises of the E forms hold *)

Lemma fwe_fix_dtype_open : is_open_term ([] : context) fwe_fix_dtype.
Proof. vm_compute; reflexivity. Qed.

Lemma fwe_lam_open : is_open_term ([] : context) fwe_lam.
Proof. vm_compute; reflexivity. Qed.

Lemma fwe_cofix_mfix_open : All (fun d => is_open_term ([] : context) (dtype d)) [fwe_cofix_d].
Proof. constructor; [exact fwe_lam_open|constructor]. Qed.

(** [λy:Prop. I y] ≡ [I], by one η step. *)
Lemma fwe_lam_conv {cf} (Σ : global_env_ext) Γ : convSpecE Σ Γ fwe_lam fwe_I.
Proof. exact (cumulSpecE_eta_contract Σ Γ Conv fwe_na fwe_T fwe_I). Qed.

Lemma fwe_fix_premise {cf} (Σ : global_env_ext) :
  mfix_body_on check_one_fix (conv_witnessE Σ []) fwe_kn fwe_fix_d.
Proof.
  exists fwe_fix_ty. split; [exact fwe_check_fix_ty|]. split.
  - vm_compute; reflexivity.
  - exact (cumulE_Prod Σ [] Conv fwe_na fwe_na fwe_lam fwe_I (tSort sProp) (tSort sProp)
             eq_refl (fwe_lam_conv Σ []) (cumulE_Refl _ _ _ _)).
Qed.

Lemma fwe_cofix_premise {cf} (Σ : global_env_ext) :
  mfix_body_on check_one_cofix (conv_witnessE Σ []) fwe_kn fwe_cofix_d.
Proof.
  exists fwe_cofix_ty. split; [exact fwe_check_cofix_ty|]. split.
  - vm_compute; reflexivity.
  - exact (fwe_lam_conv Σ []).
Qed.

Lemma fwe_wf_cofixpointE {cf} : wf_cofixpointE fwe_Σ [] [fwe_cofix_d].
Proof.
  exists fwe_kn. split; [discriminate|]. split.
  - constructor; [exact (fwe_cofix_premise fwe_Σ)|constructor].
  - reflexivity.
Qed.

(** ** The refutations

  Each witness below is NOT typable as a type ([fwe_fix_dtype_not_typeE],
  [fwe_cofix_dtype_not_typeE]). So each theorem refutes ONLY the closed-only form,
  with premises [is_closed_context Γ] / [is_open_term Γ (dtype d)]; a form with a
  typing premise on [dtype d] remains open. *)

(** [mfix_body_on_conv_closed_red] at [check_one_fix], over [conv_witnessE].
    Its witness is NOT typable as a type ([fwe_fix_dtype_not_typeE]): this refutes
    ONLY the closed-only form (premises [is_closed_context] / [is_open_term]); a
    typed form remains open. *)
Theorem mfix_body_on_conv_closed_redE_fix_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ)
          (shape : ShapeCheck check_one_fix) (Γ : context) (mind : kername) (d : def term),
      is_closed_context Γ -> is_open_term Γ (dtype d) ->
      mfix_body_on check_one_fix (conv_witnessE Σ Γ) mind d ->
      mfix_body_on check_one_fix (closed_red Σ Γ) mind d) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags fwe_Σ fwe_wf check_one_fix_shape [] fwe_kn fwe_fix_d
              closed_context_nil fwe_fix_dtype_open (fwe_fix_premise fwe_Σ)) as [ty [hc r]].
  have e := rt_from_normal _ _ _ (fwe_red_normal_fix_dtype fwe_Σ []) (clrel_rel r).
  subst ty. rewrite fwe_check_fix_dtype in hc. discriminate hc.
Qed.

(** [mfix_body_on_conv_closed_red] at [check_one_cofix], over [conv_witnessE].
    Its witness is NOT typable as a type ([fwe_cofix_dtype_not_typeE]): this refutes
    ONLY the closed-only form (premises [is_closed_context] / [is_open_term]); a
    typed form remains open. *)
Theorem mfix_body_on_conv_closed_redE_cofix_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ)
          (shape : ShapeCheck check_one_cofix) (Γ : context) (mind : kername) (d : def term),
      is_closed_context Γ -> is_open_term Γ (dtype d) ->
      mfix_body_on check_one_cofix (conv_witnessE Σ Γ) mind d ->
      mfix_body_on check_one_cofix (closed_red Σ Γ) mind d) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags fwe_Σ fwe_wf check_one_cofix_shape [] fwe_kn fwe_cofix_d
              closed_context_nil fwe_lam_open (fwe_cofix_premise fwe_Σ)) as [ty [hc r]].
  have e := rt_from_normal _ _ _ (fwe_red_normal_lam fwe_Σ []) (clrel_rel r).
  subst ty. rewrite fwe_check_cofix_dtype in hc. discriminate hc.
Qed.

(** [mfix_body_on_conv_closed_red] over [conv_witnessE], generic in the check.
    Its witness is NOT typable as a type ([fwe_fix_dtype_not_typeE]): this refutes
    ONLY the closed-only form (premises [is_closed_context] / [is_open_term]); a
    typed form remains open. *)
Corollary mfix_body_on_conv_closed_redE_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ)
          (check : def term -> option kername) (shape : ShapeCheck check)
          (Γ : context) (mind : kername) (d : def term),
      is_closed_context Γ -> is_open_term Γ (dtype d) ->
      mfix_body_on check (conv_witnessE Σ Γ) mind d ->
      mfix_body_on check (closed_red Σ Γ) mind d) -> False.
Proof.
  intros H. apply mfix_body_on_conv_closed_redE_fix_false.
  intros cf Σ wfΣ shape. exact (H cf Σ wfΣ check_one_fix shape).
Qed.

(** [wf_cofixpoint_all] over [wf_cofixpointE].
    Its witness is NOT typable as a type ([fwe_cofix_dtype_not_typeE]): this refutes
    ONLY the closed-only form (premises [is_closed_context] / [is_open_term]); a
    typed form remains open. *)
Theorem wf_cofixpoint_allE_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context)
          (mfix : mfixpoint term),
      is_closed_context Γ ->
      All (fun d => is_open_term Γ (dtype d)) mfix ->
      wf_cofixpointE Σ Γ mfix ->
      ∑ mind, check_recursivity_kind (lookup_env Σ) mind CoFinite *
      All (fun d => ∑ ctx i u args,
        Σ ;;; Γ ⊢ dtype d ⇝
          it_mkProd_or_LetIn ctx
            (mkApps (tInd {| inductive_mind := mind; inductive_ind := i |} u) args)) mfix) ->
  False.
Proof.
  intros H.
  destruct (H default_checker_flags fwe_Σ fwe_wf [] [fwe_cofix_d] closed_context_nil
              fwe_cofix_mfix_open fwe_wf_cofixpointE) as [mind [_ hall]].
  destruct (snd All_tip hall) as (ctx & i & u & args & r).
  have e := rt_from_normal _ _ _ (fwe_red_normal_lam fwe_Σ []) (clrel_rel r).
  have hc := check_one_cofix_it_mkProd (d := fwe_cofix_d) (ctx := ctx)
               (i := {| inductive_mind := mind; inductive_ind := i |}) (u := u) (l := args).
  rewrite e fwe_check_cofix_dtype in hc. discriminate hc.
Qed.

(** ** The witness is not typable as a type *)

Section NotAType.
  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}.

  (** A λ has, up to [ws_cumul_pbE], a product type. *)
  Lemma typingE_Lambda_prod {Γ t T} :
    Σ ;;; Γ |-E t : T ->
    forall na A b, t = tLambda na A b ->
    ∑ B, ws_cumul_pbE Cumul Σ Γ (tProd na A B) T.
  Proof using wfΣ.
    induction 1; intros na' A' b' hlam; try discriminate hlam.
    - injection hlam; intros; subst.
      eexists. apply ws_cumul_pbE_refl.
      + eapply typing_closed_contextE. eapply typeE_Lambda; eassumption.
      + eapply type_is_open_termE. eapply typeE_Lambda; eassumption.
    - match goal with
      | ih : forall _ _ _, _ = tLambda _ _ _ -> _ |- _ => destruct (ih _ _ _ hlam) as [B' hB']
      end.
      exists B'. refine (ws_cumul_pbE_trans _ _ _ hB' _).
      apply into_ws_cumul_pbE_spec.
      + assumption.
      + exact (wsE_ctx hB').
      + exact (wsE_right hB').
      + eapply subject_is_open_termE; eassumption.
  Qed.

  (** A λ is never typed at a sort. *)
  Lemma lambda_not_sortE {Γ na A b s} : Σ ;;; Γ |-E tLambda na A b : tSort s -> False.
  Proof using wfΣ.
    intros h. destruct (typingE_Lambda_prod h _ _ _ eq_refl) as [B hB].
    eapply ws_cumul_pbE_Prod_Sort_inv. exact hB.
  Qed.

  (** The domain of a typed product is typed at a sort. *)
  Lemma typingE_Prod_dom {Γ t T} :
    Σ ;;; Γ |-E t : T ->
    forall na A B, t = tProd na A B -> ∑ s, Σ ;;; Γ |-E A : tSort s.
  Proof.
    induction 1; intros na' A' B' hprod; try discriminate hprod.
    - injection hprod; intros; subst.
      match goal with h : context [j_vass_s _ _ _] |- _ => destruct h as (_ & s & hs & _) end.
      exists s. exact hs.
    - match goal with
      | ih : forall _ _ _, _ = tProd _ _ _ -> _ |- _ => exact (ih _ _ _ hprod)
      end.
  Qed.

  (** The declared type of the fixpoint witness is not a type, in any context. *)
  Lemma fwe_fix_dtype_not_typeE Γ : on_type (lift_typing typingE) Σ Γ fwe_fix_dtype -> False.
  Proof using wfΣ.
    intros (_ & s & hs & _).
    destruct (typingE_Prod_dom hs _ _ _ eq_refl) as [s' hs'].
    exact (lambda_not_sortE hs').
  Qed.

  (** The declared type of the cofixpoint witness is not a type, in any context. *)
  Lemma fwe_cofix_dtype_not_typeE Γ : on_type (lift_typing typingE) Σ Γ fwe_lam -> False.
  Proof using wfΣ.
    intros (_ & s & hs & _). exact (lambda_not_sortE hs).
  Qed.

End NotAType.

(** The same over base [typing], under [wf Σ] (base [typing] ⊆ [typingE]). *)
Lemma fwe_fix_dtype_not_type {cf} {Σ : global_env_ext} (wfΣ : wf Σ) Γ :
  isType Σ Γ fwe_fix_dtype -> False.
Proof.
  intros (_ & s & hs & _).
  destruct (typingE_Prod_dom (typing_incl_E wfΣ hs) _ _ _ eq_refl) as [s' hs'].
  exact (lambda_not_sortE (wfΣ := wf_incl_E wfΣ) hs').
Qed.

Lemma fwe_cofix_dtype_not_type {cf} {Σ : global_env_ext} (wfΣ : wf Σ) Γ :
  isType Σ Γ fwe_lam -> False.
Proof.
  intros (_ & s & hs & _).
  exact (lambda_not_sortE (wfΣ := wf_incl_E wfΣ) (typing_incl_E wfΣ hs)).
Qed.

(** [fwe_lam] is well typed, at [Prop → Prop]: only its use as a type fails. *)
Section Typed.
  #[local] Existing Instance default_checker_flags.

  Lemma fwe_declared_inductive : declared_inductive fwe_Σ fwe_ind fwe_mdecl fwe_idecl.
  Proof. split; [left; reflexivity|reflexivity]. Qed.

  Lemma fwe_Prop_typed Γ : wf_local fwe_Σ Γ -> fwe_Σ ;;; Γ |- tSort sProp : tSort (Sort.super sProp).
  Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

  Lemma fwe_vass Γ : wf_local fwe_Σ Γ -> lift_typing typing fwe_Σ Γ (j_vass fwe_na (tSort sProp)).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (fwe_Prop_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma fwe_vass_s Γ :
    wf_local fwe_Σ Γ -> lift_typing typing fwe_Σ Γ (j_vass_s fwe_na (tSort sProp) (Sort.super sProp)).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (fwe_Prop_typed Γ h)|]. split; [reflexivity|reflexivity].
  Qed.

  Lemma fwe_wf_P Γ : wf_local fwe_Σ Γ -> wf_local fwe_Σ (Γ ,, vass fwe_na (tSort sProp)).
  Proof. intros h. apply localenv_cons_abs; [exact h|exact (fwe_vass Γ h)]. Qed.

  Lemma fwe_lam_typed : fwe_Σ ;;; [] |- fwe_lam : tProd fwe_na (tSort sProp) (tSort sProp).
  Proof.
    have w0 : wf_local fwe_Σ [] by constructor.
    have w1 := fwe_wf_P [] w0.
    unfold fwe_lam, fwe_T.
    apply type_Lambda; [exact (fwe_vass [] w0)|].
    refine (type_App _ _ fwe_I fwe_na (tSort sProp) (tSort sProp)
              (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0) _ _ _).
    - apply type_Prod; [exact (fwe_vass_s _ w1)|].
      exact (fwe_Prop_typed _ (fwe_wf_P _ w1)).
    - exact (type_Ind _ _ fwe_ind [] fwe_mdecl fwe_idecl w1 fwe_declared_inductive eq_refl).
    - exact (type_Rel _ _ 0 (vass fwe_na (tSort sProp)) w1 eq_refl).
  Qed.

End Typed.
