(* Distributed under the terms of the MIT license. *)

(** * Context-relative facts for [ws_cumul_pbE] and [ws_cumul_ctx_pbE]

  The E counterparts of the context-relative lemmas of base [PCUICConversion],
  [PCUICContextConversion] and [PCUICWellScopedCumulativity] that the E copies
  of the typing infrastructure use. Each lemma restates its base twin over
  [ws_cumul_pbE] ([PCUICWellScopedCumulativityEta]) and [ws_cumul_ctx_pbE]
  ([PCUICContextConversionEta]); the unscoped algorithmic relation [cumulAlgo_gen]
  of base becomes the canonical join [JoinE] ([PCUICEtaI5]), so the unscoped
  context relations are [cumul_pb_context JoinE pb Σ]. Where base assumes
  [wf Σ], the lemmas here assume [ClosedBodies Σ] or nothing; each comment says
  which.

  - Scoping projections, [Conv ⊆ Cumul], forgetting and recovering the scoping of
    a context relation.
  - Context cumulativity at any [pb] ([ws_cumul_pbE_ws_cumul_ctx_pb]): the context
    is replaced by one with the right context's types and the left context's
    let-bodies ([mix_ctx]); conversion does not read assumption types
    ([ws_cumul_pbE_bodies], from [BE_ctx]), and the two contexts are convertible,
    so the conversion moves by the context conversion of [PCUICContextConversionEta].
  - Substitution of convertible terms ([untyped_substitution_ws_cumul_pbE_subst_conv]):
    one term at depth 0 by a β-redex ([ws_cumul_pbE_subst1_conv]); a list at
    depth 0 one element at a time ([ws_cumul_pbE_subst0_conv]); under a context by
    abstracting it and peeling the binders again ([ws_cumul_pbE_subst_conv_gen]).
    No reduct of the substituted terms is used.
  - The relative context relation [ws_cumul_ctx_pbE_rel], its weakening and its
    substitution; [ws_cumul_pbE_it_mkProd_or_LetIn].

  ** What is not as in base

  Base [ws_cumul_pb_red] and [ws_cumul_pb_alt_closed] say that two terms are related
  iff they have reducts that [compare_term] relates. With η the left-to-right half
  is false: [λx:A. f x] and [f] are related, both are normal, and no comparison of
  [compare_term] relates a λ and a variable ([ws_cumul_pbE_red_false]). The
  right-to-left half holds and is [into_ws_cumul_pbE_red].

**The hypotheses are satisfiable:** [ClosedBodies Σ] by any well-formed environment
  ([wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]); every [ws_cumul_pbE],
  [ws_cumul_ctx_pbE] and [JoinE] premise by reflexivity; the scoping premises by
  any scoped context and terms; [untyped_subslet] by an empty substitution or a
  single assumption. Instances: [PCUICWsCumulEtaCtxInstances]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICSigmaCalculus PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICWellScopedCumulativity PCUICSubstitution PCUICConversion PCUICContextConversion
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICConfluence PCUICTypingEta
     PCUICClosedTyp PCUICEtaDefs PCUICEtaCanon PCUICEtaC1aR PCUICEtaC1b PCUICEtaFInst PCUICEtaFInstEquiv
     PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2
     PCUICWellScopedCumulativityEta PCUICConversionEtaCongr PCUICWsCumulEtaSubst
     PCUICEtaA6 PCUICEtaA6More PCUICContextConversionEta PCUICClosedBodies.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** ** Scoping helpers (syntactic) *)

Lemma on_free_vars_subst_gen_k (p : nat -> bool) k s t :
  forallb (on_free_vars p) s ->
  on_free_vars (shiftnP (k + #|s|) p) t ->
  on_free_vars (shiftnP k p) (subst s k t).
Proof.
  intros hs ht. rewrite -substP_shiftnP_gen. by apply on_free_vars_subst_gen.
Qed.

Lemma shiftnP_add3 a b c p : shiftnP a (shiftnP b (shiftnP c p)) =1 shiftnP (a + (b + c)) p.
Proof. intros i. rewrite shiftnP_add shiftnP_add. now rewrite Nat.add_assoc. Qed.

Lemma open_app3_inv (Γ Δ Γ' : context) t :
  is_open_term (Γ ,,, Δ ,,, Γ') t -> on_free_vars (shiftnP #|Γ'| (shiftnP #|Δ| (shiftnP #|Γ| xpred0))) t.
Proof.
  intros h. rewrite (on_free_vars_ext _ _ t (shiftnP_add3 _ _ _ _)).
  move: h. rewrite !app_context_length. exact id.
Qed.

Lemma closed_app3_inv (Γ Δ Γ' : context) :
  is_closed_context (Γ ,,, Δ ,,, Γ') ->
  [× is_closed_context Γ, on_free_vars_ctx (shiftnP #|Γ| xpred0) Δ &
     on_free_vars_ctx (shiftnP #|Δ| (shiftnP #|Γ| xpred0)) Γ'].
Proof.
  rewrite !on_free_vars_ctx_app => /andP [/andP [h1 h2] h3]. split; [exact h1|exact h2|].
  eapply on_free_vars_ctx_impl; [|exact h3]. intros i.
  rewrite app_context_length shiftnP_add. exact id.
Qed.

(** ** Scoping projections, [Conv ⊆ Cumul], and the context relation without scoping

  None of these needs a premise on the environment; base's twins assume [wf Σ]
  (except [ws_cumul_pb_eq_le], whose proof uses no section variable). *)

Section NoPremise.

  Context {cf : checker_flags} {Σ : global_env_ext}.

  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  Lemma ws_cumul_pbE_is_closed_context {pb Γ x y} : WS pb Γ x y -> is_closed_context Γ.
  Proof. exact wsE_ctx. Qed.

  Lemma ws_cumul_pbE_is_open_term_left {pb Γ x y} : WS pb Γ x y -> is_open_term Γ x.
  Proof. exact wsE_left. Qed.

  Lemma ws_cumul_pbE_is_open_term_right {pb Γ x y} : WS pb Γ x y -> is_open_term Γ y.
  Proof. exact wsE_right. Qed.

  Lemma ws_cumul_pbE_eq_le {Γ t u} : WS Conv Γ t u -> WS Cumul Γ t u.
  Proof.
    intros [hΓ ht hu j]. constructor; try assumption.
    exact (JoinE_sym Σ Γ Cumul t u (JoinE_sym Σ Γ Conv u t j)).
  Qed.

  Lemma ws_cumul_declsE_closed {pb Γ d d'} : ws_cumul_declsE pb Σ Γ d d' -> is_closed_context Γ.
  Proof. unfold ws_cumul_declsE. intros []; exact (wsE_ctx eqt). Qed.

  Lemma ws_cumul_ctx_pbE_closed_left {pb Γ Γ'} : ws_cumul_ctx_pbE pb Σ Γ Γ' -> is_closed_context Γ.
  Proof.
    induction 1 as [|d d' Γ Γ' h IH hd]; [reflexivity|].
    rewrite on_free_vars_ctx_snoc IH /=.
    unfold ws_cumul_declsE in hd.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA];
      rewrite /on_free_vars_decl /test_decl /=.
    - exact (wsE_left hA).
    - now rewrite (wsE_left hb) (wsE_left hA).
  Qed.

  Lemma ws_cumul_ctx_pbE_forget {pb Γ Γ'} :
    ws_cumul_ctx_pbE pb Σ Γ Γ' -> cumul_pb_context (@JoinE cf) pb Σ Γ Γ'.
  Proof.
    induction 1 as [|d d' Γ Γ' h IH hd]; constructor; [exact IH|].
    unfold ws_cumul_declsE in hd.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; constructor.
    all: first [assumption | exact (wsE_join hA) | exact (wsE_join hb)].
  Qed.

  Lemma into_ws_cumul_ctx_pbE {pb Γ Γ'} :
    is_closed_context Γ -> is_closed_context Γ' ->
    cumul_pb_context (@JoinE cf) pb Σ Γ Γ' -> ws_cumul_ctx_pbE pb Σ Γ Γ'.
  Proof.
    intros hΓ hΓ' h. induction h as [|d d' Γ Γ' h IH hd] in hΓ, hΓ' |- *; constructor.
    all: move: hΓ hΓ'; rewrite !on_free_vars_ctx_snoc => /andP [hΓ hd1] /andP [hΓ' hd2].
    - exact (IH hΓ hΓ').
    - have hlen : #|Γ| = #|Γ'| := All2_fold_length h.
      rewrite -hlen in hd2. move: hd1 hd2.
      unfold ws_cumul_declsE.
      destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA];
        rewrite /on_free_vars_decl /test_decl /=.
      + intros h1 h2. constructor; [exact hna|exact (into_ws_cumul_pbE hA hΓ h1 h2)].
      + move=> /andP [h1 h1'] /andP [h2 h2'].
        constructor; [exact hna|exact (into_ws_cumul_pbE hb hΓ h1 h2)|exact (into_ws_cumul_pbE hA hΓ h1' h2')].
  Qed.

  Lemma ws_cumul_ctx_pbE_refl_pb {pb} {Γ : context} : is_closed_context Γ -> ws_cumul_ctx_pbE pb Σ Γ Γ.
  Proof.
    induction Γ as [|[na [b|] A] Γ IH]; intros h; constructor.
    all: try (move: h; rewrite on_free_vars_ctx_snoc => /andP [h1 h2]).
    all: try (apply IH; exact h1).
    all: unfold ws_cumul_declsE; constructor; try reflexivity.
    all: move: h2; rewrite /on_free_vars_decl /test_decl /=; try move/andP => [h2 h3].
    all: apply ws_cumul_pbE_refl; assumption.
  Qed.

  Lemma conv_cumul_contextE {Γ Δ} :
    ws_cumul_ctx_pbE Conv Σ Γ Δ -> ws_cumul_ctx_pbE Cumul Σ Γ Δ.
  Proof.
    induction 1 as [|d d' Γ Γ' h IH hd]; constructor; [exact IH|].
    unfold ws_cumul_declsE in *.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; constructor.
    all: first [assumption | now apply ws_cumul_pbE_eq_le].
  Qed.

  Lemma ws_cumul_ctx_pbE_app_same {pb Γ Γ' Δ} :
    is_closed_context (Γ ,,, Δ) ->
    ws_cumul_ctx_pbE pb Σ Γ Γ' -> ws_cumul_ctx_pbE pb Σ (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    intros hcl h. induction Δ as [|d Δ IH]; [exact h|].
    move: hcl. rewrite /= on_free_vars_ctx_snoc => /andP [hcl hd].
    constructor; [exact (IH hcl)|].
    unfold ws_cumul_declsE.
    destruct d as [na [b|] A]; constructor; try reflexivity.
    all: move: hd; rewrite /on_free_vars_decl /test_decl /=; try move/andP => [hd hd'].
    all: apply ws_cumul_pbE_refl; assumption.
  Qed.

End NoPremise.

(** The E twins of base's registrations [PCUICWellScopedCumulativity.v:146] and [:523]. *)
#[global] Hint Resolve ws_cumul_pbE_is_closed_context ws_cumul_pbE_is_open_term_left ws_cumul_pbE_is_open_term_right : fvs.
#[global] Hint Resolve ws_cumul_ctx_pbE_closed_left : fvs.

(** The unscoped context relations over [JoinE]. Base's twins are stated over
    [cumulAlgo_gen]; like them, these need no premise. *)

Lemma cumul_context_app_sameE {cf : checker_flags} Σ Γ Γ' Δ :
  cumul_context (@JoinE cf) Σ Γ Γ' ->
  cumul_context (@JoinE cf) Σ (Γ ,,, Δ) (Γ' ,,, Δ).
Proof.
  intros HΔ.
  induction Δ as [|[na [b|] ty] Δ IH]; auto; constructor; auto; constructor; try reflexivity.
  all: apply JoinE_refl.
Qed.

Lemma eq_context_upto_names_conv_contextE {cf : checker_flags} (Σ : global_env_ext) :
  subrelation eq_context_upto_names (fun Γ Γ' => conv_context (@JoinE cf) Σ Γ Γ').
Proof.
  intros Γ Γ' h. induction h as [|d d' Γ Γ' hd h IH]; constructor; [exact IH|].
  destruct hd; subst; constructor; try assumption; apply JoinE_refl.
Qed.

(** [compare_term] is in the spec, in any context. Base's twin needs no premise either. *)
Lemma eq_term_upto_univ_cumulSpecE {cf : checker_flags} (Σ : global_env_ext) (Γ : context) {pb} M N :
  compare_term Σ Σ pb M N -> Σ ;;; Γ ⊢ M ≤sE[pb] N.
Proof. intros h. apply cumulSpec0_incl_E. exact (eq_term_upto_univ_cumulSpec Σ Γ M N h). Qed.

(** The inductives of a block, at two equal universe instances. No premise, as in base. *)
Lemma conv_indsE {cf : checker_flags} (Σ : global_env_ext) Γ u u' ind mdecl :
  cmp_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  is_closed_context Γ ->
  ws_cumul_pbE_terms Σ Γ (inds (inductive_mind ind) u (ind_bodies mdecl))
    (inds (inductive_mind ind) u' (ind_bodies mdecl)).
Proof.
  move=> equ hΓ.
  unfold inds. generalize #|ind_bodies mdecl|.
  induction n; constructor; auto.
  constructor; [exact hΓ|reflexivity|reflexivity|].
  eexists _, _. split; [apply rt_refl|split; [apply rt_refl|]].
  cbn [canon]. constructor.
  rewrite /cmp_global_instance_finst /cmp_global_instance_eta /finst_mode.
  match goal with |- context [Nat.leb ?a ?b] => destruct (Nat.leb a b) end.
  all: apply cmp_instance_opt_variance; exact equ.
Qed.

(** ** Contexts that differ only in assumption types *)

Section Bodies.

  Context {cf : checker_flags} {Σ : global_env_ext}.

  (** The join reads a context only through its let-bodies ([BE_ctx]). *)
  Lemma JoinE_bodies {Γ Γ' pb t u} :
    upto_domain_r_bodies Γ Γ' -> JoinE Σ Γ pb t u -> JoinE Σ Γ' pb t u.
  Proof.
    intros hc h. destruct (JoinE_BE Σ Γ pb t u h) as (v & v' & hv & hv' & e).
    apply (BE_JoinE Σ Γ' pb t u v v').
    - exact (BE_ctx Σ _ _ _ _ hc hv).
    - exact (BE_ctx Σ _ _ _ _ hc hv').
    - exact (RF_canon Σ _ _ _ _ e).
  Qed.

  Lemma ws_cumul_pbE_bodies {pb Γ Γ' t u} :
    upto_domain_r_bodies Γ Γ' -> is_closed_context Γ' ->
    ws_cumul_pbE pb Σ Γ t u -> ws_cumul_pbE pb Σ Γ' t u.
  Proof.
    intros hc hΓ' [hΓ ht hu j]. have hlen : #|Γ| = #|Γ'| := All2_length hc.
    constructor; [exact hΓ'| | |exact (JoinE_bodies hc j)].
    all: move: ht hu; rewrite hlen; intros; assumption.
  Qed.

End Bodies.

(** The context with the right context's names and types and the left context's
    let-bodies. *)
Definition mix_decl (d' d : context_decl) : context_decl :=
  {| decl_name := decl_name d; decl_body := decl_body d'; decl_type := decl_type d |}.

Fixpoint mix_ctx (Γ' Γ : context) : context :=
  match Γ', Γ with
  | d' :: Γ', d :: Γ => mix_decl d' d :: mix_ctx Γ' Γ
  | _, _ => []
  end.

Lemma mix_ctx_length Γ' Γ : #|Γ'| = #|Γ| -> #|mix_ctx Γ' Γ| = #|Γ|.
Proof.
  induction Γ' as [|d' Γ' IH] in Γ |- *; destruct Γ as [|d Γ]; cbn; try discriminate; [reflexivity|].
  intros e. injection e as e. now rewrite (IH Γ e).
Qed.

Lemma mix_ctx_bodies Γ' Γ : #|Γ'| = #|Γ| ->
  upto_domain_r_bodies Γ' (mix_ctx Γ' Γ) × upto_domain_r_bodies (mix_ctx Γ' Γ) Γ'.
Proof.
  induction Γ' as [|d' Γ' IH] in Γ |- *; destruct Γ as [|d Γ]; cbn; try discriminate.
  - split; constructor.
  - intros e. injection e as e. destruct (IH Γ e) as [h1 h2].
    split; constructor; try assumption; cbn.
    all: destruct (decl_body d'); constructor; reflexivity.
Qed.

(** ** Context cumulativity at any [pb] *)

Section ContextCumulativity.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  Lemma mix_ctx_closed {pb' Γ' Γ} :
    ws_cumul_ctx_pbE pb' Σ Γ' Γ -> is_closed_context (mix_ctx Γ' Γ).
  Proof.
    induction 1 as [|d' d Γ' Γ h IH hd]; [reflexivity|].
    cbn [mix_ctx]. rewrite on_free_vars_ctx_snoc IH /=.
    have hlen : #|mix_ctx Γ' Γ| = #|Γ'|.
    { rewrite (mix_ctx_length _ _ (All2_fold_length h)). symmetry. exact (All2_fold_length h). }
    rewrite hlen. unfold ws_cumul_declsE in hd.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA];
      rewrite /on_free_vars_decl /test_decl /mix_decl /=.
    - exact (wsE_right hA).
    - now rewrite (wsE_left hb) (wsE_right hA).
  Qed.

  Lemma mix_ctx_conv {pb' Γ' Γ} :
    ws_cumul_ctx_pbE pb' Σ Γ' Γ -> ws_cumul_ctx_pbE Conv Σ (mix_ctx Γ' Γ) Γ.
  Proof.
    intros hc. induction hc as [|d' d Γ' Γ h IH hd]; [constructor|].
    have hcl : is_closed_context (mix_ctx Γ' Γ) := mix_ctx_closed h.
    have hlen : #|Γ'| = #|Γ| := All2_fold_length h.
    destruct (mix_ctx_bodies Γ' Γ hlen) as [hb1 _].
    have hlen' : #|mix_ctx Γ' Γ| = #|Γ'| by rewrite (mix_ctx_length _ _ hlen).
    cbn [mix_ctx]. constructor; [exact IH|].
    unfold ws_cumul_declsE in *.
    destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA]; rewrite /mix_decl /=; constructor.
    - reflexivity.
    - apply ws_cumul_pbE_refl; [exact hcl|]. move: (wsE_right hA). by rewrite hlen'.
    - reflexivity.
    - exact (ws_cumul_pbE_bodies hb1 hcl hb).
    - apply ws_cumul_pbE_refl; [exact hcl|]. move: (wsE_right hA). by rewrite hlen'.
  Qed.

  (** Base [ws_cumul_pb_ws_cumul_ctx], at any [pb'] for the context. Base assumes
      [wf Σ]; here [ClosedBodies Σ]. [ws_cumul_pbE_ws_cumul_ctx]
      ([PCUICContextConversionEta]) is the [Conv] case. *)
  Lemma ws_cumul_pbE_ws_cumul_ctx_pb {pb pb' Γ Γ' T U} :
    ws_cumul_ctx_pbE pb' Σ Γ' Γ -> WS pb Γ T U -> WS pb Γ' T U.
  Proof.
    intros hc h.
    pose proof (ws_cumul_pbE_ws_cumul_ctx (wfΣ := wfΣ)
                  (ws_cumul_ctx_pbE_sym (wfΣ := wfΣ) (mix_ctx_conv hc)) h) as h1.
    destruct (mix_ctx_bodies Γ' Γ (All2_fold_length hc)) as [_ hb2].
    exact (ws_cumul_pbE_bodies hb2 (ws_cumul_ctx_pbE_closed_left hc) h1).
  Qed.

  Lemma ws_cumul_declsE_ws_cumul_ctx {pb pb' Γ Γ' d d'} :
    ws_cumul_ctx_pbE pb' Σ Γ' Γ -> ws_cumul_declsE pb Σ Γ d d' -> ws_cumul_declsE pb Σ Γ' d d'.
  Proof.
    intros hc hd. unfold ws_cumul_declsE in *.
    destruct hd; constructor; try assumption; eapply ws_cumul_pbE_ws_cumul_ctx_pb; eassumption.
  Qed.

  Lemma ws_cumul_declsE_trans {pb Γ d d' d''} :
    ws_cumul_declsE pb Σ Γ d d' -> ws_cumul_declsE pb Σ Γ d' d'' -> ws_cumul_declsE pb Σ Γ d d''.
  Proof.
    unfold ws_cumul_declsE. intros h1 h2. destruct h1; depelim h2; constructor.
    all: first [etransitivity; eassumption | eapply ws_cumul_pbE_trans; eassumption].
  Qed.

  #[global] Instance ws_cumul_ctx_pbE_trans pb : Transitive (ws_cumul_ctx_pbE pb Σ).
  Proof.
    eapply All2_fold_trans.
    intros Γ Γ' Γ'' d d' d'' h1 _ _ hd hd'.
    eapply ws_cumul_declsE_trans; [exact hd|].
    exact (ws_cumul_declsE_ws_cumul_ctx h1 hd').
  Qed.

  (** Base [context_cumulativity_app], under [ClosedBodies Σ] in place of [wf Σ]. *)
  Lemma context_cumulativity_appE {pb Γ Γ' Δ Δ'} :
    ws_cumul_ctx_pbE Cumul Σ Γ' Γ ->
    ws_cumul_ctx_pbE pb Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
    ws_cumul_ctx_pbE pb Σ (Γ' ,,, Δ) (Γ' ,,, Δ').
  Proof.
    intros cum conv.
    pose proof (length_of conv). len in H.
    eapply All2_fold_app; eauto.
    1: eapply ws_cumul_ctx_pbE_refl_pb; exact (ws_cumul_ctx_pbE_closed_left cum).
    eapply All2_fold_app_inv in conv as []. 2:lia.
    eapply All2_fold_impl_ind; tea.
    intros. simpl in X1.
    pose proof (All2_fold_length cum).
    eapply ws_cumul_declsE_ws_cumul_ctx; [|exact X1].
    eapply ws_cumul_ctx_pbE_app_same; [|exact cum].
    eapply is_closed_context_cumul_app;
      [exact (ws_cumul_declsE_closed X1)|exact (ws_cumul_ctx_pbE_closed_left cum)|lia].
  Qed.

End ContextCumulativity.

(** Base's instance [ws_cumul_decls_trans] ([PCUICWellScopedCumulativity.v:466]) in its
    class form over [ws_cumul_declsE]. Base's instance name is taken by the lemma
    [ws_cumul_declsE_trans], so the instance is a new constant whose body is that
    lemma. Base's [wf Σ] is [ClosedBodies Σ] here, as for [ws_cumul_declsE_trans]. *)
#[global]
Instance ws_cumul_declsE_Transitive {cf : checker_flags} {pb} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}
  {Γ : context} : Transitive (ws_cumul_declsE pb Σ Γ).
Proof. exact (fun _ _ _ => ws_cumul_declsE_trans). Qed.

(** ** Substitution of convertible terms *)

Section SubstConv.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  Lemma WS_trans {pb Γ t u v} : WS pb Γ t u -> WS pb Γ u v -> WS pb Γ t v.
  Proof. exact (fun h1 h2 => ws_cumul_pbE_trans (Σ := Σ) (wfΣ := wfΣ) _ _ _ h1 h2). Qed.

  (** One term, at depth 0: [c{0 := t} ≡ (λ_. c) t ≡ (λ_. c) t' ≡ c{0 := t'}]. *)
  Lemma ws_cumul_pbE_subst1_conv {Γ t t' c} :
    on_free_vars (shiftnP 1 (shiftnP #|Γ| xpred0)) c ->
    WS Conv Γ t t' -> WS Conv Γ (c {0 := t}) (c {0 := t'}).
  Proof.
    intros hc h.
    have hΓ := wsE_ctx h.
    have hf : is_open_term Γ (tLambda (mkBindAnn nAnon Relevant) (tSort sProp) c) by rewrite /= hc.
    have r1 : Σ ;;; Γ ⊢ tApp (tLambda (mkBindAnn nAnon Relevant) (tSort sProp) c) t ⇝ c {0 := t}.
    { split; [exact hΓ| |apply red1_red; apply red_beta]. rewrite /= hc (wsE_left h). reflexivity. }
    have r2 : Σ ;;; Γ ⊢ tApp (tLambda (mkBindAnn nAnon Relevant) (tSort sProp) c) t' ⇝ c {0 := t'}.
    { split; [exact hΓ| |apply red1_red; apply red_beta]. rewrite /= hc (wsE_right h). reflexivity. }
    eapply WS_trans; [exact (red_ws_cumul_pbE_inv r1)|].
    eapply WS_trans; [exact (ws_cumul_pbE_App_r hf h)|].
    exact (red_ws_cumul_pbE r2).
  Qed.

  Lemma subst0_cons (s : list term) x c : subst0 (x :: s) c = (subst s 1 c) {0 := x}.
  Proof. change (x :: s) with ([x] ++ s). now rewrite subst_app_simpl. Qed.

  Lemma subst0_cons_lift (s : list term) x c :
    subst0 s (subst [lift0 #|s| x] 0 c) = subst0 (x :: s) c.
  Proof.
    rewrite distr_subst /= (simpl_subst_k s x 0 #|s| eq_refl).
    now rewrite (subst0_cons s x c).
  Qed.

  (** A list, at depth 0, one element at a time. *)
  Lemma ws_cumul_pbE_subst0_conv {Γ s s'} :
    is_closed_context Γ -> ws_cumul_pbE_terms Σ Γ s s' ->
    forall c, on_free_vars (shiftnP #|s| (shiftnP #|Γ| xpred0)) c ->
    WS Conv Γ (subst0 s c) (subst0 s' c).
  Proof.
    intros hΓ h. induction h as [|a a' s s' ha hs IH]; intros c hc.
    - rewrite !subst_empty. apply ws_cumul_pbE_refl; [exact hΓ|].
      cbn [length] in hc. rewrite (on_free_vars_ext _ _ c (shiftnP0 _)) in hc. exact hc.
    - have hlen : #|s| = #|s'| := All2_length hs.
      have hsl : forallb (is_open_term Γ) s := WT_open_left hs.
      have hsc : on_free_vars (shiftnP 1 (shiftnP #|Γ| xpred0)) (subst s 1 c).
      { apply on_free_vars_subst_gen_k; [exact hsl|exact hc]. }
      have hc2 : on_free_vars (shiftnP #|s| (shiftnP #|Γ| xpred0)) (subst [lift0 #|s| a'] 0 c).
      { apply on_free_vars_subst1.
        - apply on_free_vars_lift0. rewrite (on_free_vars_ext _ _ a' (addnP_shiftnP _ _)). exact (wsE_right ha).
        - rewrite (on_free_vars_ext _ _ c (shiftnP_add 1 #|s| _)). exact hc. }
      have e3 : subst0 (a' :: s) c = subst0 s (subst [lift0 #|s| a'] 0 c) by rewrite subst0_cons_lift.
      have e4 : subst0 (a' :: s') c = subst0 s' (subst [lift0 #|s| a'] 0 c) by rewrite hlen subst0_cons_lift.
      rewrite (subst0_cons s a c). eapply WS_trans; [exact (ws_cumul_pbE_subst1_conv hsc ha)|].
      rewrite -(subst0_cons s a' c) e3 e4.
      exact (IH _ hc2).
  Qed.

  (** [tLetIn] with convertible bodies: the codomains in the left let-context. *)
  Lemma ws_cumul_pbE_LetIn_body_inv {pb Γ na na' b b' A A' X Y} :
    WS Conv Γ b b' ->
    WS pb Γ (tLetIn na b A X) (tLetIn na' b' A' Y) -> WS pb (Γ ,, vdef na b A) X Y.
  Proof.
    intros hb h.
    have hΓ := wsE_ctx h.
    move: (wsE_left h). cbn [on_free_vars]. move/and3P => [hb0 hA hX].
    move: (wsE_right h). cbn [on_free_vars]. move/and3P => [_ _ hY].
    have hΓ1 : is_closed_context (Γ ,, vdef na b A) := closed_snoc_vdef Γ na b A hΓ hb0 hA.
    have hrX : red Σ (Γ ,, vdef na b A) X (lift 1 0 (X {0 := b}))
      := red_rel_all (Σ := Σ) (Γ := Γ ,, vdef na b A) (i := 0) (body := b) (t := X) eq_refl.
    have hrY : red Σ (Γ ,, vdef na b A) Y (lift 1 0 (Y {0 := b}))
      := red_rel_all (Σ := Σ) (Γ := Γ ,, vdef na b A) (i := 0) (body := b) (t := Y) eq_refl.
    have h1 := red_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb)
                 (closed_red_of hΓ1 (open_snoc Γ _ X hX) hrX).
    have h5 := red_ws_cumul_pbE_inv (Σ := Σ) (wfΣ := wfΣ) (pb := pb)
                 (closed_red_of hΓ1 (open_snoc Γ _ Y hY) hrY).
    have h2 := ws_cumul_pbE_LetIn_inv (wfΣ := wfΣ) h.
    have h3 := weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb) (Γ := Γ) (Γ' := [])
                 (Γ'' := [vdef na b A]) h2 hΓ1.
    have h4 : WS Conv Γ (Y {0 := b'}) (Y {0 := b}) := ws_cumul_pbE_subst1_conv hY (ws_cumul_pbE_sym _ _ hb).
    have h4' := weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := Conv) (Γ := Γ) (Γ' := [])
                 (Γ'' := [vdef na b A]) h4 hΓ1.
    exact (WS_trans h1 (WS_trans h3 (WS_trans (ws_cumul_eq_pbE h4') h5))).
  Qed.

  (** Under a context: abstract it, convert by [ws_cumul_pbE_subst0_conv], and peel
      the binders one at a time; a let-binder needs its two bodies convertible,
      which is the same statement at a smaller depth. *)
  Lemma ws_cumul_pbE_subst_conv_gen {Γ s s'} Γ' :
    is_closed_context Γ -> ws_cumul_pbE_terms Σ Γ s s' ->
    on_free_vars_ctx (shiftnP #|s| (shiftnP #|Γ| xpred0)) Γ' ->
    forall b, on_free_vars (shiftnP #|Γ'| (shiftnP #|s| (shiftnP #|Γ| xpred0))) b ->
    WS Conv (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
  Proof.
    intros hΓ hs. induction Γ' as [|d Γ' IH]; intros hΓ' b hb.
    - rewrite subst_context_nil /=. apply (ws_cumul_pbE_subst0_conv hΓ hs).
      cbn [length] in hb. rewrite (on_free_vars_ext _ _ b (shiftnP0 _)) in hb. exact hb.
    - move: hΓ'. rewrite on_free_vars_ctx_snoc => /andP [hΓ' hd].
      have hlen : #|s| = #|s'| := All2_length hs.
      have hm : on_free_vars (shiftnP #|Γ'| (shiftnP #|s| (shiftnP #|Γ| xpred0))) (mkProd_or_LetIn d b).
      { destruct d as [na [bd|] A]; move: hd; rewrite /on_free_vars_decl /test_decl /mkProd_or_LetIn /=.
        - move=> /andP [h1 h2]. rewrite h1 h2 /= (on_free_vars_ext _ _ b (shiftnP_add 1 _ _)). exact hb.
        - intros h1. rewrite h1 /= (on_free_vars_ext _ _ b (shiftnP_add 1 _ _)). exact hb. }
      have h := IH hΓ' _ hm.
      rewrite subst_context_snoc0. cbn [length].
      destruct d as [na [bd|] A]; cbn in h |- *.
      + move: hd; rewrite /on_free_vars_decl /test_decl /= => /andP [hbd _].
        have hbody := IH hΓ' bd hbd.
        rewrite /subst_decl /map_decl /=.
        exact (ws_cumul_pbE_LetIn_body_inv hbody h).
      + rewrite /subst_decl /map_decl /=.
        destruct (ws_cumul_pbE_Prod_Prod_inv_l h) as [_ _ h3]. exact h3.
  Qed.

  (** Base [untyped_substitution_ws_cumul_pb_subst_conv], under [ClosedBodies Σ] in
      place of [wf Σ]. *)
  Lemma untyped_substitution_ws_cumul_pbE_subst_conv {Γ Δ Δ' Γ' s s' b} :
    ws_cumul_pbE_terms Σ Γ s s' ->
    is_closed_context (Γ ,,, Δ ,,, Γ') ->
    is_closed_context (Γ ,,, Δ' ,,, Γ') ->
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ s' Δ' ->
    is_open_term (Γ ,,, Δ ,,, Γ') b ->
    WS Conv (Γ ,,, subst_context s 0 Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
  Proof.
    move=> eqsub cl _ subs _ clb.
    have hlen := untyped_subslet_length subs.
    destruct (closed_app3_inv _ _ _ cl) as [hΓ _ hΓ'].
    apply (ws_cumul_pbE_subst_conv_gen Γ' hΓ eqsub).
    - by rewrite hlen.
    - move: (open_app3_inv _ _ _ _ clb). by rewrite hlen.
  Qed.

  (** Base [substitution_ws_cumul_pb_subst_conv], under [ClosedBodies Σ]. *)
  Lemma substitution_ws_cumul_pbE_subst_conv {pb Γ Γ0 Γ1 Δ s s' T U} :
    untyped_subslet Γ s Γ0 ->
    untyped_subslet Γ s' Γ1 ->
    ws_cumul_pbE_terms Σ Γ s s' ->
    is_closed_context (Γ ,,, Γ1) ->
    WS pb (Γ ,,, Γ0 ,,, Δ) T U ->
    WS pb (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T) (subst s' #|Δ| U).
  Proof.
    move=> subss subss' eqsub cl eqty.
    have clctx := wsE_ctx eqty.
    have clU := wsE_right eqty.
    eapply WS_trans.
    - eapply untyped_substitution_ws_cumul_pbE; tea. exact (WT_open_left eqsub).
    - eapply ws_cumul_eq_pbE.
      eapply (untyped_substitution_ws_cumul_pbE_subst_conv (Δ := Γ0) (Δ' := Γ1)); tea.
      have H : #|Γ0| = #|Γ1|.
      { rewrite -(untyped_subslet_length subss) -(untyped_subslet_length subss').
        apply (All2_length eqsub). }
      rewrite on_free_vars_ctx_app cl /=.
      move: clctx. rewrite on_free_vars_ctx_app !app_context_length H => /andP [] //.
  Qed.

  (** Base [substitution_ws_cumul_ctx_pb], under [ClosedBodies Σ]. *)
  Lemma substitution_ws_cumul_ctx_pbE {Γ Δ Δ' Γ' s s'} :
    untyped_subslet Γ s Δ ->
    untyped_subslet Γ s' Δ' ->
    ws_cumul_pbE_terms Σ Γ s s' ->
    is_closed_context (Γ ,,, Δ ,,, Γ') ->
    is_closed_context (Γ ,,, Δ' ,,, Γ') ->
    ws_cumul_ctx_pbE Conv Σ (Γ ,,, subst_context s 0 Γ') (Γ ,,, subst_context s' 0 Γ').
  Proof.
    move=> subs subs' eqsub cl cl'.
    have hlen := untyped_subslet_length subs.
    destruct (closed_app3_inv _ _ _ cl) as [hΓ _ hΓ'].
    rewrite -hlen in hΓ'.
    induction Γ' as [|d Γ' IH].
    - rewrite !subst_context_nil /=. exact (ws_cumul_ctx_pbE_refl_pb hΓ).
    - move: hΓ'. rewrite on_free_vars_ctx_snoc => /andP [hΓ' hd].
      have cl0 : is_closed_context (Γ ,,, Δ ,,, Γ').
      { move: cl. by rewrite /= on_free_vars_ctx_snoc => /andP []. }
      have cl0' : is_closed_context (Γ ,,, Δ' ,,, Γ').
      { move: cl'. by rewrite /= on_free_vars_ctx_snoc => /andP []. }
      rewrite !subst_context_snoc0. constructor; [exact (IH cl0 cl0' hΓ')|].
      unfold ws_cumul_declsE.
      destruct d as [na [bd|] A]; move: hd; rewrite /on_free_vars_decl /test_decl /=.
      + move=> /andP [h1 h2]. rewrite /subst_decl /map_decl /=. constructor; [reflexivity| |].
        * exact (ws_cumul_pbE_subst_conv_gen Γ' hΓ eqsub hΓ' bd h1).
        * exact (ws_cumul_pbE_subst_conv_gen Γ' hΓ eqsub hΓ' A h2).
      + intros h1. rewrite /subst_decl /map_decl /=. constructor; [reflexivity|].
        exact (ws_cumul_pbE_subst_conv_gen Γ' hΓ eqsub hΓ' A h1).
  Qed.

End SubstConv.

(** ** The relative context relation *)

Definition ws_cumul_ctx_pbE_rel {cf : checker_flags} (pb : conv_pb) (Σ : global_env_ext) (Γ Δ Δ' : context) :=
  is_closed_context Γ ×
  All2_fold (fun Γ' _ => All_decls_alpha_pb pb (fun pb x y => ws_cumul_pbE pb Σ (Γ ,,, Γ') x y)) Δ Δ'.

Section Rel.

  Context {cf : checker_flags} {Σ : global_env_ext}.

  (** Base [ws_cumul_ctx_pb_rel_app] assumes [wf Σ]; this needs nothing. *)
  Lemma ws_cumul_ctx_pbE_rel_app {pb Γ Δ Δ'} :
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' <~> ws_cumul_ctx_pbE pb Σ (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    split; intros h.
    + eapply All2_fold_app => //.
      * destruct h. now apply ws_cumul_ctx_pbE_refl_pb.
      * eapply All2_fold_impl; tea. 1:apply h.
        intros ???? []; constructor; auto.
    + eapply All2_fold_app_inv in h as [].
      2:{ move: (length_of h). len; lia. }
      split.
      { now apply ws_cumul_ctx_pbE_closed_left in a. }
      eapply All2_fold_impl; tea => /=.
      intros ???? []; constructor; auto.
  Qed.

End Rel.

Section RelCB.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}.

  Local Notation WS pb Γ := (ws_cumul_pbE pb Σ Γ).

  (** Base [weaken_ws_cumul_pb], under [ClosedBodies Σ]. *)
  Lemma weaken_ws_cumul_pbE {pb Γ t u} Δ :
    is_closed_context Δ -> WS pb Γ t u -> WS pb (Δ ,,, Γ) t u.
  Proof.
    move=> clΔ a.
    have hΓ := wsE_ctx a. have ht := wsE_left a. have hu := wsE_right a.
    pose proof (weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := pb) (Γ := []) (Γ' := Γ) (Γ'' := Δ)
                  (M := t) (N := u)) as X.
    rewrite !app_context_nil_l in X.
    specialize (X a clΔ).
    rewrite !lift_closed in X; [by rewrite is_open_term_closed|by rewrite is_open_term_closed|].
    rewrite PCUICClosed.closed_ctx_lift in X; [by rewrite is_closed_ctx_closed|].
    exact X.
  Qed.

  (** Base [weaken_ws_cumul_ctx_pb_rel], under [ClosedBodies Σ]. *)
  Lemma weaken_ws_cumul_ctx_pbE_rel {pb Γ Γ' Δ Δ'} :
    is_closed_context Γ ->
    ws_cumul_ctx_pbE_rel pb Σ Γ' Δ Δ' ->
    ws_cumul_ctx_pbE_rel pb Σ (Γ ,,, Γ') Δ Δ'.
  Proof.
    intros wf [cl eq].
    split.
    { rewrite on_free_vars_ctx_app wf /=.
      eapply on_free_vars_ctx_impl; [|exact cl].
      intros i h. discriminate h. }
    induction eq.
    - simpl. constructor.
    - constructor; auto.
      destruct p; constructor; auto.
      all: rewrite -app_context_assoc; eapply weaken_ws_cumul_pbE; tea.
  Qed.

  (** Base [ws_cumul_pb_it_mkProd_or_LetIn], under [ClosedBodies Σ]. The let-body
      at [pb] is [ws_cumul_pbE_LetIn_pb] ([PCUICWsCumulEtaSubst]). *)
  Lemma ws_cumul_pbE_it_mkProd_or_LetIn {pb} (Δ Γ Γ' : context) (B B' : term) :
    ws_cumul_ctx_pbE_rel Conv Σ Δ Γ Γ' ->
    WS pb (Δ ,,, Γ) B B' ->
    WS pb Δ (it_mkProd_or_LetIn Γ B) (it_mkProd_or_LetIn Γ' B').
  Proof.
    intros [_ cv].
    move: B B' Γ' Δ cv.
    induction Γ as [|d Γ] using rev_ind; move=> B B' Γ' Δ;
    destruct Γ' as [|d' Γ'] using rev_ind; try clear IHΓ';
      move=> H; try solve [simpl; auto].
    + depelim H. apply app_eq_nil in H; intuition discriminate.
    + depelim H. apply app_eq_nil in H; intuition discriminate.
    + assert (clen : #|Γ| = #|Γ'|).
      { apply All2_fold_length in H.
        autorewrite with len in H; simpl in H. lia. }
      apply All2_fold_app_inv in H as [cd cctx] => //.
      depelim cd; depelim a.
      - rewrite !it_mkProd_or_LetIn_app => //=.
        simpl. move=> HB. apply ws_cumul_pbE_Prod => /= //.
        eapply IHΓ.
        * unshelve eapply (All2_fold_impl cctx).
          simpl. intros ? ? * X. now rewrite !app_context_assoc in X.
        * now rewrite app_context_assoc in HB.
      - rewrite !it_mkProd_or_LetIn_app => //=.
        simpl. intros HB. cbn. apply ws_cumul_pbE_LetIn_pb => //; auto.
        eapply IHΓ.
        * unshelve eapply (All2_fold_impl cctx).
          simpl. intros ?? * X. now rewrite !app_context_assoc in X.
        * now rewrite app_context_assoc in HB.
  Qed.

  (** Base [substitution_ws_cumul_ctx_pb_subst_conv], under [ClosedBodies Σ]. *)
  Lemma substitution_ws_cumul_ctx_pbE_subst_conv {Γ Γ' Γ'0 Γ'' Δ Δ' s s' pb} :
    ws_cumul_ctx_pbE_rel pb Σ (Γ ,,, Γ' ,,, Γ'') Δ Δ' ->
    ws_cumul_pbE_terms Σ Γ s s' ->
    untyped_subslet Γ s Γ' ->
    untyped_subslet Γ s' Γ'0 ->
    is_closed_context (Γ ,,, Γ'0) ->
    ws_cumul_ctx_pbE_rel pb Σ (Γ ,,, subst_context s 0 Γ'') (subst_context s #|Γ''| Δ) (subst_context s' #|Γ''| Δ').
  Proof.
    intros [cl cum] eqs hs hs' cl'.
    split.
    { eapply is_closed_subst_context; tea. 1: exact (WT_open_left eqs).
      apply (untyped_subslet_length hs). }
    eapply All2_fold_fold_context_k.
    eapply All2_fold_impl_ind; tea. clear cum.
    move=> Δ0 Δ'0 d d'; cbn => /All2_fold_length len _ ad.
    eapply All_decls_alpha_pb_map.
    destruct ad; constructor; auto.
    all: cbn; rewrite -/(subst_context _ _ _).
    all: rewrite -app_context_assoc (subst_context_app0 s Γ'' Δ0).
    all: rewrite - !length_app.
    all: relativize #|Δ'0 ++ Γ''|; [eapply (substitution_ws_cumul_pbE_subst_conv hs hs' eqs)|] => //.
    all: try (rewrite app_context_assoc //).
    all: len.
  Qed.

  (** Base [ws_cumul_pb_terms_subst], under [ClosedBodies Σ]. *)
  Lemma ws_cumul_pbE_terms_subst {Γ Γ' Γ'' Δ s s' args args'} :
    is_closed_context (Γ ,,, Γ'') ->
    untyped_subslet Γ s Γ' ->
    untyped_subslet Γ s' Γ'' ->
    ws_cumul_pbE_terms Σ Γ s s' ->
    ws_cumul_pbE_terms Σ (Γ ,,, Γ' ,,, Δ) args args' ->
    ws_cumul_pbE_terms Σ (Γ ,,, subst_context s 0 Δ) (map (subst s #|Δ|) args) (map (subst s' #|Δ|) args').
  Proof.
    intros wf cl cl' convs conv.
    eapply All2_map.
    eapply (All2_impl conv).
    intros x y eqxy.
    eapply substitution_ws_cumul_pbE_subst_conv; eauto.
  Qed.

  (** Base [red_terms_ws_cumul_pb_terms], under [ClosedBodies Σ]. *)
  Lemma red_terms_ws_cumul_pbE_terms {Γ u u'} :
    red_terms Σ Γ u u' -> ws_cumul_pbE_terms Σ Γ u u'.
  Proof.
    move=> Hu; eapply All2_impl; eauto. intros.
    now eapply red_ws_cumul_pbE.
  Qed.

  (** Base [eq_terms_ws_cumul_pb_terms], under [ClosedBodies Σ]. *)
  Lemma eq_terms_ws_cumul_pbE_terms Γ u u' :
    is_closed_context Γ ->
    forallb (is_open_term Γ) u ->
    forallb (is_open_term Γ) u' ->
    All2 (eq_term Σ Σ) u u' -> ws_cumul_pbE_terms Σ Γ u u'.
  Proof.
    intros hΓ hu hu' h. induction h as [|x y l l' hxy h IH]; constructor.
    - move: hu hu' => /= /andP [hx _] /andP [hy _].
      apply ws_cumul_pb_incl_E. constructor; assumption.
    - apply IH; [move: hu => /= /andP []|move: hu' => /= /andP []]; auto.
  Qed.

  (** Base [PCUICConversion.subst_instance_ws_cumul_ctx_pb_rel], under
      [ClosedBodies Σ]. ([Typing/PCUICUnivSubstitutionTyp] has a different lemma of
      the same name, over [cumul_context cumulSpec0].) *)
  Lemma subst_instance_ws_cumul_ctx_pbE_rel {Γ Δ u u' pb} :
    is_closed_context (Γ ,,, Δ) ->
    cmp_universe_instance (eq_universe Σ) u u' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ (subst_instance u Δ) (subst_instance u' Δ).
  Proof.
    move=> cl equ.
    split.
    { move: cl. rewrite on_free_vars_ctx_app => /andP [] //. }
    induction Δ as [|d Δ IH].
    - constructor.
    - move: cl; rewrite /= on_free_vars_ctx_snoc => /andP [clΔ hd].
      rewrite !subst_instance_cons; constructor; [exact (IH clΔ)|].
      destruct d as [na [b|] ty]; move: hd; rewrite /on_free_vars_decl /test_decl /=.
      + move=> /andP [onb onty]. constructor; [reflexivity| |].
        all: apply ws_cumul_pb_incl_E; constructor.
        all: try (rewrite on_free_vars_ctx_app; apply/andP; split; [move: clΔ; rewrite on_free_vars_ctx_app => /andP [] //|];
                  rewrite on_free_vars_ctx_subst_instance; move: clΔ; rewrite on_free_vars_ctx_app => /andP [] //).
        all: try (rewrite on_free_vars_subst_instance app_context_length subst_instance_length;
                  move: onb onty; rewrite app_context_length; auto).
        all: try (eapply eq_term_compare_term); eapply eq_term_upto_univ_subst_instance; try typeclasses eauto; auto.
      + intros onty. constructor; [reflexivity|].
        apply ws_cumul_pb_incl_E; constructor.
        * rewrite on_free_vars_ctx_app; apply/andP; split; [move: clΔ; rewrite on_free_vars_ctx_app => /andP [] //|].
          rewrite on_free_vars_ctx_subst_instance; move: clΔ; rewrite on_free_vars_ctx_app => /andP [] //.
        * rewrite on_free_vars_subst_instance app_context_length subst_instance_length.
          move: onty; rewrite app_context_length; auto.
        * rewrite on_free_vars_subst_instance app_context_length subst_instance_length.
          move: onty; rewrite app_context_length; auto.
        * eapply eq_term_compare_term; eapply eq_term_upto_univ_subst_instance; try typeclasses eauto; auto.
  Qed.

  (** Base [weakening_cumul0], over the unscoped join, under [ClosedBodies Σ]. *)
  Lemma weakening_cumul0E {Γ : closed_context} {Γ'' : open_context Γ}
    {M N : open_term Γ} n :
    n = #|Γ''| ->
    JoinE Σ Γ Cumul M N ->
    JoinE Σ (Γ ,,, Γ'') Cumul (lift0 n M) (lift0 n N).
  Proof.
    intros -> h.
    have hcl : is_closed_context (Γ ,,, Γ'').
    { rewrite on_free_vars_ctx_app (proj2_sig Γ) /=. exact (proj2_sig Γ''). }
    have hw := weakening_ws_cumul_pbE (Σ := Σ) (wfΣ := wfΣ) (pb := Cumul) (Γ := Γ) (Γ' := []) (Γ'' := Γ'')
                 (into_ws_cumul_pbE h (proj2_sig Γ) (proj2_sig M) (proj2_sig N)) hcl.
    cbn in hw. exact (wsE_join hw).
  Qed.

  (** The right-to-left half of base [ws_cumul_pb_red] (and of the same statement
      [ws_cumul_pb_alt_closed]), under [ClosedBodies Σ]. The other half is false
      with η: [ws_cumul_pbE_red_false]. *)
  Lemma into_ws_cumul_pbE_red {pb Γ t u} :
    (∑ v v', [× Σ ;;; Γ ⊢ t ⇝ v, Σ ;;; Γ ⊢ u ⇝ v' &
      compare_term Σ (global_ext_constraints Σ) pb v v']) ->
    WS pb Γ t u.
  Proof.
    intros (v & v' & [rv rv' c]).
    have hΓ := clrel_ctx rv.
    pose proof (closed_red_open_right_cb (wfΣ := wfΣ) rv) as hv.
    pose proof (closed_red_open_right_cb (wfΣ := wfΣ) rv') as hv'.
    have h : WS pb Γ v v'.
    { apply ws_cumul_pb_incl_E. eapply ws_cumul_pb_compare; [exact hΓ|exact hv|exact hv'|exact c]. }
    eapply red_ws_cumul_pbE_left; [exact rv|].
    eapply red_ws_cumul_pbE_right; [exact rv'|exact h].
  Qed.

End RelCB.

(** ** The left-to-right half of base [ws_cumul_pb_red] is false with η

  [ws_cumul_pbE_red_false] and [ws_cumul_pbE_alt_closed_false] record why the route
  through [compare_term] on reducts does not exist for the η relation: a proof that
  reads two related terms off common reducts compared by [compare_term] has no η
  counterpart. They are kept on purpose and are not dead code; a proof over
  [ws_cumul_pbE] reads the canonical join [JoinE] ([ws_cumul_pbE_forget]) or an
  inversion lemma of [PCUICEtaA6] instead.

  Witness, in the empty environment and the context [f : Prop → Prop]:
  [λx:Prop. f x] and [f] are related (one η step). Both are normal: [f] is an
  assumption and [f x] has a variable head. A λ and a variable are not related by
  [compare_term]. The witness is well typed over [typingE]
  ([rf_witness_typed]: the context is well formed, and both terms have type
  [Prop → Prop]); the refuted statement is untyped, as base's is. *)

Section RedFalse.

  #[local] Existing Instance default_checker_flags.

  Definition rf_Σ : global_env_ext := (empty_global_env, Monomorphic_ctx).
  Definition rf_F : term := tProd c1b_na (tSort sProp) (tSort sProp).
  Definition rf_Γ : context := [vass c1b_na rf_F].
  Definition rf_t : term := tLambda c1b_na (tSort sProp) (tApp (tRel 1) (tRel 0)).

  Lemma rf_Rel1_normal Σ v : red1 Σ (rf_Γ ,, vass c1b_na (tSort sProp)) (tRel 1) v -> False.
  Proof.
    intros H. inv_red H.
    match goal with e : option_map decl_body _ = _ |- _ => cbn in e; discriminate e end.
  Qed.

  Lemma rf_body_normal Σ v : red1 Σ (rf_Γ ,, vass c1b_na (tSort sProp)) (tApp (tRel 1) (tRel 0)) v -> False.
  Proof.
    intros H. inv_red H.
    - eapply rf_Rel1_normal; eassumption.
    - eapply red_normal_Rel0; eassumption.
  Qed.

  Lemma rf_t_normal Σ v : red1 Σ rf_Γ rf_t v -> False.
  Proof.
    apply red_normal_lam; [intros w; apply red_normal_Sort|intros w; apply rf_body_normal].
  Qed.

  Lemma rf_f_normal Σ v : red1 Σ rf_Γ (tRel 0) v -> False.
  Proof. apply red_normal_Rel0. Qed.

  Lemma rf_premise : ws_cumul_pbE Conv rf_Σ rf_Γ rf_t (tRel 0).
  Proof.
    constructor; try reflexivity.
    exists (tRel 0), (tRel 0). split; [|split].
    - apply rt_step; right. cbn. exact (eta_red canon_la (tRel 0) canon_dom).
    - cbn. apply rt_refl.
    - apply compare_term_eta_refl.
  Qed.

  (** The witness is typable. *)
  Lemma rf_wf_sort : wf_sort rf_Σ sProp.
  Proof. cbn; trivial. Qed.

  Lemma rf_P_typed (Γ : context) : wf_localE rf_Σ Γ -> rf_Σ ;;; Γ |-E tSort sProp : tSort (Sort.super sProp).
  Proof. intros h. apply typeE_Sort; [exact h|exact rf_wf_sort]. Qed.

  Lemma rf_P_vass (Γ : context) : wf_localE rf_Σ Γ -> lift_typing typingE rf_Σ Γ (j_vass c1b_na (tSort sProp)).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (rf_P_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma rf_F_typed (Γ : context) : wf_localE rf_Σ Γ ->
    rf_Σ ;;; Γ |-E rf_F : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
  Proof.
    intros h. unfold rf_F. apply typeE_Prod.
    - split; [exact tt|]. exists (Sort.super sProp).
      split; [exact (rf_P_typed Γ h)|]. split; reflexivity.
    - apply rf_P_typed. apply localenv_cons_abs; [exact h|exact (rf_P_vass Γ h)].
  Qed.

  Lemma rf_wf_Γ : wf_localE rf_Σ rf_Γ.
  Proof.
    apply localenv_cons_abs; [constructor|].
    split; [exact tt|]. exists (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)).
    split; [exact (rf_F_typed [] localenv_nil)|]. split; [exact I|reflexivity].
  Qed.

  Lemma rf_f_typed : rf_Σ ;;; rf_Γ |-E tRel 0 : rf_F.
  Proof. exact (typeE_Rel _ _ 0 (vass c1b_na rf_F) rf_wf_Γ eq_refl). Qed.

  Lemma rf_t_typed : rf_Σ ;;; rf_Γ |-E rf_t : rf_F.
  Proof.
    have hΓ1 : wf_localE rf_Σ (rf_Γ ,, vass c1b_na (tSort sProp)).
    { apply localenv_cons_abs; [exact rf_wf_Γ|exact (rf_P_vass rf_Γ rf_wf_Γ)]. }
    unfold rf_t, rf_F. apply typeE_Lambda; [exact (rf_P_vass rf_Γ rf_wf_Γ)|].
    apply (typeE_App _ _ (tRel 1) c1b_na (tSort sProp) (tSort sProp)
             (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 0)).
    - exact (rf_F_typed _ hΓ1).
    - exact (typeE_Rel _ _ 1 (vass c1b_na rf_F) hΓ1 eq_refl).
    - exact (typeE_Rel _ _ 0 (vass c1b_na (tSort sProp)) hΓ1 eq_refl).
  Qed.

  (** In an environment that meets the refuted statement's premise [wf Σ] (and
      [wfE Σ]), [f : Prop → Prop] is a well-formed context, and [λx:Prop. f x]
      and [f] both have type [Prop → Prop] in it. *)
  Lemma rf_witness_typed :
    [× wf rf_Σ, wfE rf_Σ, wf_localE rf_Σ rf_Γ,
       rf_Σ ;;; rf_Γ |-E rf_t : rf_F & rf_Σ ;;; rf_Γ |-E tRel 0 : rf_F].
  Proof.
    split; [exact (@wf_empty_global_env default_checker_flags)
           |exact (wf_incl_E (@wf_empty_global_env default_checker_flags))
           |exact rf_wf_Γ|exact rf_t_typed|exact rf_f_typed].
  Qed.

End RedFalse.

(** **Refuted:** the left-to-right half of base [ws_cumul_pb_red] over
    [ws_cumul_pbE], even under [wf Σ]. *)
Theorem ws_cumul_pbE_red_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) pb Γ t u,
     ws_cumul_pbE pb Σ Γ t u ->
     ∑ v v', [× Σ ;;; Γ ⊢ t ⇝ v, Σ ;;; Γ ⊢ u ⇝ v' &
       compare_term Σ (global_ext_constraints Σ) pb v v']) -> False.
Proof.
  intros H.
  destruct (H default_checker_flags rf_Σ (@wf_empty_global_env default_checker_flags)
              Conv rf_Γ rf_t (tRel 0) rf_premise) as (v & v' & [rv rv' c]).
  have e1 := rt_from_normal _ _ _ (rf_t_normal rf_Σ) (clrel_rel rv).
  have e2 := rt_from_normal _ _ _ (rf_f_normal rf_Σ) (clrel_rel rv').
  subst v v'. depelim c.
Qed.

(** The same statement, up to binder order, as base's other copy
    [ws_cumul_pb_alt_closed]: base binds [pb] before [Σ]; here [pb] comes after
    [wfΣ]. The binders are independent, so the two orders give equivalent
    statements. *)
Corollary ws_cumul_pbE_alt_closed_false :
  (forall (cf : checker_flags) (Σ : global_env_ext) (wfΣ : wf Σ) pb Γ t u,
     ws_cumul_pbE pb Σ Γ t u ->
     ∑ v v', [× closed_red Σ Γ t v, closed_red Σ Γ u v' &
       compare_term Σ (global_ext_constraints Σ) pb v v']) -> False.
Proof. exact ws_cumul_pbE_red_false. Qed.
