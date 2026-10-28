(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, plan row A5: congruences for [ws_cumul_pbE]

  New statements over [ws_cumul_pbE] (A1), proved from the join congruences of
  A2 ([PCUICEtaI5A2.v]) and A3. This is not a copy of [PCUICConversion.v]
  (prim-ops row F2 edits that file); base lemmas are used by import only.

  - λ: NO annotation and NO domain premise ([ws_cumul_pbE_Lambda]): [canon]
    erases both, which is the point of the E relation.
  - Π, application, [mkApps], projection, evar, sort, constant, inductive and
    constructor spines, primitives, let-in, case, fixpoints, cofixpoints.
  - The η rule itself ([ws_cumul_pbE_eta_l], [_eta_r]; obligation 9).
  - [it_mkLambda_or_LetIn] and [it_mkProd_or_LetIn] on the codomain.

  One base form is weaker here. [ws_cumul_pbE_LetIn_bo] compares the let-body at
  [Conv], as the spec rule [cumulE_LetIn] and U1''s [eqη_LetIn] both do. Base's
  [ws_cumul_pb_LetIn_bo] allows [pb] there by zeta and substitution, which is
  A7's substitution lemma for [ws_cumul_pbE]. For the same reason
  [ws_cumul_pbE_it_mkProd_or_LetIn_codom] takes the codomain at [pb] only over an
  assumption context; [_codom_conv] covers every context at [Conv].

  **Hypotheses satisfiable (FRAC's rule):** [wf Σ] by any well-formed
  environment; the scoping premises by any scoped context and terms; every
  [ws_cumul_pbE] premise by reflexivity ([ws_cumul_pbE_refl]); the universe
  premises by the reflexivity of [compare_universe]/[compare_sort]. C4-side. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICLiftSubst PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICEtaFInst PCUICEtaI5 PCUICEtaI5Trans PCUICEtaI5A2 PCUICEtaI5EtaL
     PCUICWellScopedCumulativityEta PCUICClosedBodies.

Definition ws_cumul_pbE_terms {cf : checker_flags} (r : finst_construct_rule) (Σ : global_env_ext)
  (Γ : context) : list term -> list term -> Type :=
  All2 (ws_cumul_pbE r Conv Σ Γ).

(** ** Scoping helpers *)

Lemma open_app_inv (Γ Δ : context) t :
  is_open_term (Γ ,,, Δ) t -> on_free_vars (shiftnP #|Δ| (shiftnP #|Γ| xpred0)) t.
Proof.
  intros h.
  have e : shiftnP #|Δ| (shiftnP #|Γ| xpred0) =1 shiftnP (#|Δ| + #|Γ|) xpred0 by apply shiftnP_add.
  rewrite (on_free_vars_ext _ _ t e) -app_context_length. exact h.
Qed.

Lemma open_snoc_inv (Γ : context) d t :
  is_open_term (Γ ,, d) t -> on_free_vars (shiftnP 1 (shiftnP #|Γ| xpred0)) t.
Proof. intros h. exact (open_app_inv Γ [d] t h). Qed.

Lemma closed_snoc_inv (Γ : context) d :
  is_closed_context (Γ ,, d) -> is_closed_context Γ × on_free_vars_decl (shiftnP #|Γ| xpred0) d.
Proof. rewrite on_free_vars_ctx_snoc => /andP [h1 h2]. now split. Qed.

Lemma closed_snoc_vass_inv (Γ : context) na A :
  is_closed_context (Γ ,, vass na A) -> is_closed_context Γ × is_open_term Γ A.
Proof. intros h. destruct (closed_snoc_inv Γ _ h) as [h1 h2]. now split. Qed.

Lemma closed_snoc_vdef_inv (Γ : context) na b A :
  is_closed_context (Γ ,, vdef na b A) -> [× is_closed_context Γ, is_open_term Γ b & is_open_term Γ A].
Proof.
  intros h. destruct (closed_snoc_inv Γ _ h) as [h1 h2].
  move: h2. rewrite /on_free_vars_decl /test_decl /= => /andP [h3 h4]. now split.
Qed.

Section A5.

  Context {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ} {r : finst_construct_rule}.

  Local Notation WS pb Γ := (ws_cumul_pbE r pb Σ Γ).
  Local Notation WT Γ := (ws_cumul_pbE_terms r Σ Γ).
  Local Notation J Γ pb := (JoinE r Σ Γ pb).

  Lemma WT_join {Γ l l'} : WT Γ l l' -> All2 (J Γ Conv) l l'.
  Proof. intros h. eapply All2_impl; [exact h|]. intros x y hx. exact (wsE_join hx). Qed.

  Lemma WT_open_left {Γ l l'} : WT Γ l l' -> forallb (is_open_term Γ) l.
  Proof. induction 1; cbn; [reflexivity|]. now rewrite (wsE_left r0) IHX. Qed.

  Lemma WT_open_right {Γ l l'} : WT Γ l l' -> forallb (is_open_term Γ) l'.
  Proof. induction 1; cbn; [reflexivity|]. now rewrite (wsE_right r0) IHX. Qed.

  Lemma WT_refl {Γ l} : is_closed_context Γ -> forallb (is_open_term Γ) l -> WT Γ l l.
  Proof.
    intros hΓ. induction l as [|a l IH]; cbn; [constructor|].
    move/andP => [ha hl]. constructor; [exact (ws_cumul_pbE_refl hΓ ha)|exact (IH hl)].
  Qed.

  (** ** Atoms *)

  Lemma ws_cumul_pbE_Sort {pb Γ s s'} :
    is_closed_context Γ -> compare_sort Σ pb s s' -> WS pb Γ (tSort s) (tSort s').
  Proof. intros hΓ h. constructor; try reflexivity; [exact hΓ|]. now apply JoinE_Sort. Qed.

  Lemma ws_cumul_pbE_Const {pb Γ c u u'} :
    is_closed_context Γ -> cmp_universe_instance (compare_universe Σ Conv) u u' ->
    WS pb Γ (tConst c u) (tConst c u').
  Proof. intros hΓ h. constructor; try reflexivity; [exact hΓ|]. now apply JoinE_Const. Qed.

  Lemma ws_cumul_pbE_Evar {pb Γ ev args args'} :
    WT Γ args args' -> is_closed_context Γ -> WS pb Γ (tEvar ev args) (tEvar ev args').
  Proof.
    intros h hΓ. constructor; [exact hΓ|exact (WT_open_left h)|exact (WT_open_right h)|].
    apply JoinE_Evar. exact (WT_join h).
  Qed.

  (** ** Application *)

  Lemma ws_cumul_pbE_App {pb Γ t t' u u'} :
    WS pb Γ t t' -> WS Conv Γ u u' -> WS pb Γ (tApp t u) (tApp t' u').
  Proof.
    intros [hΓ ht ht' jt] [_ hu hu' ju]. constructor; [exact hΓ| | |].
    - cbn [on_free_vars]. now rewrite ht hu.
    - cbn [on_free_vars]. now rewrite ht' hu'.
    - now apply JoinE_App.
  Qed.

  Lemma ws_cumul_pbE_App_l {pb Γ f f' u} :
    WS pb Γ f f' -> is_open_term Γ u -> WS pb Γ (tApp f u) (tApp f' u).
  Proof. intros h hu. apply ws_cumul_pbE_App; [exact h|exact (ws_cumul_pbE_refl (wsE_ctx h) hu)]. Qed.

  Lemma ws_cumul_pbE_App_r {pb Γ f u v} :
    is_open_term Γ f -> WS Conv Γ u v -> WS pb Γ (tApp f u) (tApp f v).
  Proof. intros hf h. apply ws_cumul_pbE_App; [exact (ws_cumul_pbE_refl (wsE_ctx h) hf)|exact h]. Qed.

  Lemma ws_cumul_pbE_mkApps {pb Γ hd hd' args args'} :
    WS pb Γ hd hd' -> WT Γ args args' -> WS pb Γ (mkApps hd args) (mkApps hd' args').
  Proof.
    intros h ha. induction ha as [|a a' l l' haa _ IH] in hd, hd', h |- *; cbn; [exact h|].
    apply IH. exact (ws_cumul_pbE_App h haa).
  Qed.

  Lemma ws_cumul_pbE_mkApps_weak {Γ u1 u2 l} :
    forallb (is_open_term Γ) l -> WS Conv Γ u1 u2 -> WS Conv Γ (mkApps u1 l) (mkApps u2 l).
  Proof. intros hl h. apply ws_cumul_pbE_mkApps; [exact h|exact (WT_refl (wsE_ctx h) hl)]. Qed.

  Lemma ws_cumul_pbE_Proj_c {pb Γ p u v} : WS Conv Γ u v -> WS pb Γ (tProj p u) (tProj p v).
  Proof.
    intros [hΓ hu hv j]. constructor; [exact hΓ|exact hu|exact hv|]. now apply JoinE_Proj.
  Qed.

  (** ** Products *)

  Lemma ws_cumul_pbE_Prod {pb Γ na na' A A' B B'} :
    eq_binder_annot na na' -> WS Conv Γ A A' -> WS pb (Γ ,, vass na A) B B' ->
    WS pb Γ (tProd na A B) (tProd na' A' B').
  Proof.
    intros hna [hΓ hA hA' jA] [_ hB hB' jB]. constructor; [exact hΓ| | |].
    - cbn [on_free_vars]. now rewrite hA (open_snoc_inv Γ _ B hB).
    - cbn [on_free_vars]. now rewrite hA' (open_snoc_inv Γ _ B' hB').
    - now apply JoinE_Prod.
  Qed.

  Lemma ws_cumul_pbE_Prod_l {pb Γ na na' A A' B} :
    eq_binder_annot na na' -> is_open_term (Γ ,, vass na A) B -> WS Conv Γ A A' ->
    WS pb Γ (tProd na A B) (tProd na' A' B).
  Proof.
    intros hna hB h. apply ws_cumul_pbE_Prod; [exact hna|exact h|].
    apply ws_cumul_pbE_refl; [exact (closed_snoc_vass Γ na A (wsE_ctx h) (wsE_left h))|exact hB].
  Qed.

  Lemma ws_cumul_pbE_Prod_r {pb Γ na A B B'} :
    WS pb (Γ ,, vass na A) B B' -> WS pb Γ (tProd na A B) (tProd na A B').
  Proof.
    intros h. destruct (closed_snoc_vass_inv Γ na A (wsE_ctx h)) as [hΓ hA].
    apply ws_cumul_pbE_Prod; [exact eq_refl|exact (ws_cumul_pbE_refl hΓ hA)|exact h].
  Qed.

  (** ** λ, without annotation or domain premise *)

  Lemma ws_cumul_pbE_Lambda {pb Γ na na' A A' b b'} :
    is_open_term Γ A' -> WS Conv (Γ ,, vass na A) b b' ->
    WS pb Γ (tLambda na A b) (tLambda na' A' b').
  Proof.
    intros hA' [hΓA hb hb' j]. destruct (closed_snoc_vass_inv Γ na A hΓA) as [hΓ hA].
    constructor; [exact hΓ| | |].
    - cbn [on_free_vars]. now rewrite hA (open_snoc_inv Γ _ b hb).
    - cbn [on_free_vars]. now rewrite hA' (open_snoc_inv Γ _ b' hb').
    - now apply JoinE_Lambda.
  Qed.

  Lemma ws_cumul_pbE_Lambda_l {pb Γ na na' A A' b} :
    is_closed_context Γ -> is_open_term Γ A -> is_open_term Γ A' -> is_open_term (Γ ,, vass na A) b ->
    WS pb Γ (tLambda na A b) (tLambda na' A' b).
  Proof.
    intros hΓ hA hA' hb. apply ws_cumul_pbE_Lambda; [exact hA'|].
    exact (ws_cumul_pbE_refl (closed_snoc_vass Γ na A hΓ hA) hb).
  Qed.

  Lemma ws_cumul_pbE_Lambda_r {pb Γ na A b b'} :
    WS Conv (Γ ,, vass na A) b b' -> WS pb Γ (tLambda na A b) (tLambda na A b').
  Proof.
    intros h. apply ws_cumul_pbE_Lambda; [|exact h].
    exact (snd (closed_snoc_vass_inv Γ na A (wsE_ctx h))).
  Qed.

  (** ** η *)

  Lemma ws_cumul_pbE_eta_l {pb Γ na A t u} :
    WS Conv (Γ ,, vass na A) t (tApp (lift0 1 u) (tRel 0)) -> is_open_term Γ u ->
    WS pb Γ (tLambda na A t) u.
  Proof.
    intros [hΓA ht _ j] hu. destruct (closed_snoc_vass_inv Γ na A hΓA) as [hΓ hA].
    have hl : is_open_term Γ (tLambda na A t).
    { cbn [on_free_vars]. now rewrite hA (open_snoc_inv Γ _ t ht). }
    constructor; [exact hΓ|exact hl|exact hu|].
    exact (I5_eta_l_case_holds Σ wfΣ r Γ pb na A t u hΓ hl hu j).
  Qed.

  Lemma ws_cumul_pbE_eta_r {pb Γ na A t u} :
    WS Conv (Γ ,, vass na A) (tApp (lift0 1 u) (tRel 0)) t -> is_open_term Γ u ->
    WS pb Γ u (tLambda na A t).
  Proof.
    intros h hu. apply ws_cumul_pbE_sym_pb. apply ws_cumul_pbE_eta_l; [|exact hu].
    symmetry. exact h.
  Qed.

  (** ** Let-in *)

  Lemma ws_cumul_pbE_LetIn {pb Γ na na' t t' A A' u u'} :
    eq_binder_annot na na' -> WS Conv Γ t t' -> WS Conv Γ A A' -> WS Conv (Γ ,, vdef na t A) u u' ->
    WS pb Γ (tLetIn na t A u) (tLetIn na' t' A' u').
  Proof.
    intros hna [hΓ ht ht' jt] [_ hA hA' jA] [_ hu hu' ju].
    have hl : is_open_term Γ (tLetIn na t A u).
    { cbn [on_free_vars]. now rewrite ht hA (open_snoc_inv Γ _ u hu). }
    have hr : is_open_term Γ (tLetIn na' t' A' u').
    { cbn [on_free_vars]. now rewrite ht' hA' (open_snoc_inv Γ _ u' hu'). }
    constructor; [exact hΓ|exact hl|exact hr|].
    exact (JoinE_LetIn Σ wfΣ r Γ pb na na' t t' A A' u u' hΓ hl hr hna jt jA ju).
  Qed.

  Lemma ws_cumul_pbE_LetIn_bo {pb Γ na t A u u'} :
    WS Conv (Γ ,, vdef na t A) u u' -> WS pb Γ (tLetIn na t A u) (tLetIn na t A u').
  Proof.
    intros h. destruct (closed_snoc_vdef_inv Γ na t A (wsE_ctx h)) as [hΓ ht hA].
    apply ws_cumul_pbE_LetIn; [exact eq_refl|exact (ws_cumul_pbE_refl hΓ ht)|exact (ws_cumul_pbE_refl hΓ hA)|exact h].
  Qed.

  Lemma ws_cumul_pbE_LetIn_tm {pb Γ na na' t t' A u} :
    eq_binder_annot na na' -> is_open_term Γ A -> is_open_term (Γ ,, vdef na t A) u ->
    WS Conv Γ t t' -> WS pb Γ (tLetIn na t A u) (tLetIn na' t' A u).
  Proof.
    intros hna hA hu h. have hΓ := wsE_ctx h.
    apply ws_cumul_pbE_LetIn; [exact hna|exact h|exact (ws_cumul_pbE_refl hΓ hA)|].
    exact (ws_cumul_pbE_refl (closed_snoc_vdef Γ na t A hΓ (wsE_left h) hA) hu).
  Qed.

  Lemma ws_cumul_pbE_LetIn_ty {pb Γ na na' t A A' u} :
    eq_binder_annot na na' -> is_open_term Γ t -> is_open_term (Γ ,, vdef na t A) u ->
    WS Conv Γ A A' -> WS pb Γ (tLetIn na t A u) (tLetIn na' t A' u).
  Proof.
    intros hna ht hu h. have hΓ := wsE_ctx h.
    apply ws_cumul_pbE_LetIn; [exact hna|exact (ws_cumul_pbE_refl hΓ ht)|exact h|].
    exact (ws_cumul_pbE_refl (closed_snoc_vdef Γ na t A hΓ ht (wsE_left h)) hu).
  Qed.

  (** ** Spines and primitives *)

  Lemma ws_cumul_pbE_Ind {pb Γ ind u u' l l'} :
    cumul_Ind_univ Σ pb ind #|l| u u' -> is_closed_context Γ -> WT Γ l l' ->
    WS pb Γ (mkApps (tInd ind u) l) (mkApps (tInd ind u') l').
  Proof.
    intros hu hΓ h. constructor; [exact hΓ| | |].
    - rewrite on_free_vars_mkApps /=. exact (WT_open_left h).
    - rewrite on_free_vars_mkApps /=. exact (WT_open_right h).
    - apply JoinE_Ind; [exact hu|exact (WT_join h)].
  Qed.

  Lemma ws_cumul_pbE_Construct {pb Γ i k u u' l l'} :
    cumul_Construct_univ Σ pb i k #|l| u u' -> is_closed_context Γ -> WT Γ l l' ->
    WS pb Γ (mkApps (tConstruct i k u) l) (mkApps (tConstruct i k u') l').
  Proof.
    intros hu hΓ h. constructor; [exact hΓ| | |].
    - rewrite on_free_vars_mkApps /=. exact (WT_open_left h).
    - rewrite on_free_vars_mkApps /=. exact (WT_open_right h).
    - apply JoinE_Construct; [exact hu|exact (WT_join h)].
  Qed.

  Lemma ws_cumul_pbE_Prim {pb Γ p p'} :
    onPrims (WS Conv Γ) (eq_universe Σ) p p' -> is_closed_context Γ -> WS pb Γ (tPrim p) (tPrim p').
  Proof.
    intros h hΓ. destruct h as [i|f|s|a a' hl hd ht hv].
    1-3: constructor; try reflexivity; [exact hΓ|now apply JoinE_canon_eq].
    constructor; [exact hΓ| | |].
    - cbn [on_free_vars]. simp test_prim. cbn.
      now rewrite (WT_open_left hv) (wsE_left hd) (wsE_left ht).
    - cbn [on_free_vars]. simp test_prim. cbn.
      now rewrite (WT_open_right hv) (wsE_right hd) (wsE_right ht).
    - apply JoinE_Prim. constructor; [exact hl|exact (wsE_join hd)|exact (wsE_join ht)|exact (WT_join hv)].
  Qed.

  (** ** Case *)

  Lemma ws_cumul_pbE_Case {pb Γ ci p p' c c' brs brs'} :
    is_open_term Γ (tCase ci p c brs) -> is_open_term Γ (tCase ci p' c' brs') ->
    WT Γ (pparams p) (pparams p') ->
    cmp_universe_instance (compare_universe Σ Conv) (puinst p) (puinst p') ->
    eq_context_upto_names (pcontext p) (pcontext p') ->
    WS Conv (Γ ,,, inst_case_predicate_context p) (preturn p) (preturn p') ->
    WS Conv Γ c c' ->
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
            WS Conv (Γ ,,, inst_case_branch_context p br) (bbody br) (bbody br')) brs brs' ->
    WS pb Γ (tCase ci p c brs) (tCase ci p' c' brs').
  Proof.
    intros hl hr hpars hu hctx hret hc hbrs. have hΓ := wsE_ctx hc.
    constructor; [exact hΓ|exact hl|exact hr|].
    apply (JoinE_Case Σ wfΣ r); try assumption.
    - exact (WT_join hpars).
    - exact (wsE_join hret).
    - exact (wsE_join hc).
    - eapply All2_impl; [exact hbrs|]. intros br br' [h1 h2]. exact (h1, wsE_join h2).
  Qed.

  (** The reflexive pieces of a case need no scoping. *)
  Lemma JoinE_Case_refl_brs Γ p (brs : list (branch term)) :
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
            J (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br')) brs brs.
  Proof. apply All2_refl. intros br. split; [reflexivity|apply JoinE_refl]. Qed.

  Lemma ws_cumul_pbE_Case_c {pb Γ ci p c c' brs} :
    is_open_term Γ (tCase ci p c brs) -> WS Conv Γ c c' ->
    WS pb Γ (tCase ci p c brs) (tCase ci p c' brs).
  Proof.
    intros hl hc. have hΓ := wsE_ctx hc.
    have hr : is_open_term Γ (tCase ci p c' brs).
    { move: hl. cbn [on_free_vars]. move/and5P => [h1 h2 h3 _ h5]. apply/and5P; split; try assumption.
      exact (wsE_right hc). }
    constructor; [exact hΓ|exact hl|exact hr|].
    apply (JoinE_Case Σ wfΣ r); try assumption.
    - apply All2_refl. intros x. apply JoinE_refl.
    - reflexivity.
    - reflexivity.
    - apply JoinE_refl.
    - exact (wsE_join hc).
    - apply JoinE_Case_refl_brs.
  Qed.

  Lemma ws_cumul_pbE_Case_brs {pb Γ ci p c brs brs'} :
    is_closed_context Γ -> is_open_term Γ (tCase ci p c brs) -> is_open_term Γ (tCase ci p c brs') ->
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
            WS Conv (Γ ,,, inst_case_branch_context p br) (bbody br) (bbody br')) brs brs' ->
    WS pb Γ (tCase ci p c brs) (tCase ci p c brs').
  Proof.
    intros hΓ hl hr hbrs. constructor; [exact hΓ|exact hl|exact hr|].
    apply (JoinE_Case Σ wfΣ r); try assumption.
    - apply All2_refl. intros x. apply JoinE_refl.
    - reflexivity.
    - reflexivity.
    - apply JoinE_refl.
    - apply JoinE_refl.
    - eapply All2_impl; [exact hbrs|]. intros br br' [h1 h2]. exact (h1, wsE_join h2).
  Qed.

  Lemma ws_cumul_pbE_Case_p {pb Γ ci p p' c brs} :
    is_closed_context Γ -> is_open_term Γ (tCase ci p c brs) -> is_open_term Γ (tCase ci p' c brs) ->
    All2 (J Γ Conv) (pparams p) (pparams p') ->
    cmp_universe_instance (compare_universe Σ Conv) (puinst p) (puinst p') ->
    eq_context_upto_names (pcontext p) (pcontext p') ->
    J (Γ ,,, inst_case_predicate_context p) Conv (preturn p) (preturn p') ->
    WS pb Γ (tCase ci p c brs) (tCase ci p' c brs).
  Proof.
    intros hΓ hl hr hpars hu hctx hret. constructor; [exact hΓ|exact hl|exact hr|].
    apply (JoinE_Case Σ wfΣ r); try assumption.
    - apply JoinE_refl.
    - apply JoinE_Case_refl_brs.
  Qed.

  (** ** Fixpoints and cofixpoints *)

  Definition ws_mfix_rel Γ (mfix mfix' : mfixpoint term) :=
    All2 (fun d d' => WS Conv Γ (dtype d) (dtype d') × WS Conv (Γ ,,, fix_context mfix) (dbody d) (dbody d') ×
                      (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) mfix mfix'.

  Lemma ws_mfix_rel_join {Γ mfix mfix'} : ws_mfix_rel Γ mfix mfix' ->
    All2 (fun d d' => J Γ Conv (dtype d) (dtype d') × J (Γ ,,, fix_context mfix) Conv (dbody d) (dbody d') ×
                      (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) mfix mfix'.
  Proof.
    intros h. eapply All2_impl; [exact h|]. intros d d' (h1 & h2 & h3 & h4).
    exact (wsE_join h1, (wsE_join h2, (h3, h4))).
  Qed.

  Lemma mfix_open_aux Γ Δ (l l' : mfixpoint term) :
    All2 (fun d d' => WS Conv Γ (dtype d) (dtype d') × WS Conv (Γ ,,, Δ) (dbody d) (dbody d') ×
                      (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) l l' ->
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0)) (on_free_vars (shiftnP #|Δ| (shiftnP #|Γ| xpred0)))) l ×
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0)) (on_free_vars (shiftnP #|Δ| (shiftnP #|Γ| xpred0)))) l'.
  Proof.
    induction 1 as [|d d' l l' (h1 & h2 & _ & _) _ [IH1 IH2]]; cbn; [now split|].
    rewrite /test_def.
    rewrite (wsE_left h1) (wsE_right h1) (open_app_inv Γ Δ _ (wsE_left h2)) (open_app_inv Γ Δ _ (wsE_right h2)).
    now rewrite IH1 IH2.
  Qed.

  Lemma ws_mfix_rel_open {Γ mfix mfix'} (h : ws_mfix_rel Γ mfix mfix') :
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0)) (on_free_vars (shiftnP #|mfix| (shiftnP #|Γ| xpred0)))) mfix ×
    forallb (test_def (on_free_vars (shiftnP #|Γ| xpred0)) (on_free_vars (shiftnP #|mfix'| (shiftnP #|Γ| xpred0)))) mfix'.
  Proof.
    rewrite -(All2_length h) -(fix_context_length mfix).
    exact (mfix_open_aux Γ (fix_context mfix) mfix mfix' h).
  Qed.

  Lemma ws_cumul_pbE_Fix {pb Γ mfix mfix' idx} :
    is_closed_context Γ -> ws_mfix_rel Γ mfix mfix' -> WS pb Γ (tFix mfix idx) (tFix mfix' idx).
  Proof.
    intros hΓ h. destruct (ws_mfix_rel_open h) as [h1 h2].
    constructor; [exact hΓ|exact h1|exact h2|]. apply JoinE_Fix. exact (ws_mfix_rel_join h).
  Qed.

  Lemma ws_cumul_pbE_CoFix {pb Γ mfix mfix' idx} :
    is_closed_context Γ -> ws_mfix_rel Γ mfix mfix' -> WS pb Γ (tCoFix mfix idx) (tCoFix mfix' idx).
  Proof.
    intros hΓ h. destruct (ws_mfix_rel_open h) as [h1 h2].
    constructor; [exact hΓ|exact h1|exact h2|]. apply JoinE_CoFix. exact (ws_mfix_rel_join h).
  Qed.

  (** ** Binder telescopes on the codomain *)

  Lemma ws_cumul_pbE_mkLambda_or_LetIn_codom {pb Γ d u v} :
    WS Conv (Γ ,, d) u v -> WS pb Γ (mkLambda_or_LetIn d u) (mkLambda_or_LetIn d v).
  Proof.
    destruct d as [na [b|] A]; cbn; intros h.
    - exact (ws_cumul_pbE_LetIn_bo h).
    - exact (ws_cumul_pbE_Lambda_r h).
  Qed.

  Lemma ws_cumul_pbE_it_mkLambda_or_LetIn_codom {pb Δ Γ u v} :
    WS Conv (Δ ,,, Γ) u v -> WS pb Δ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v).
  Proof.
    induction Γ as [|d Γ IH] in pb, u, v |- *; cbn; intros h.
    - exact (ws_cumul_eq_pbE h).
    - apply IH. exact (ws_cumul_pbE_mkLambda_or_LetIn_codom h).
  Qed.

  Lemma ws_cumul_pbE_it_mkProd_or_LetIn_codom_conv {pb Δ Γ B B'} :
    WS Conv (Δ ,,, Γ) B B' -> WS pb Δ (it_mkProd_or_LetIn Γ B) (it_mkProd_or_LetIn Γ B').
  Proof.
    induction Γ as [|[na [b|] A] Γ IH] in pb, B, B' |- *; cbn; intros h.
    - exact (ws_cumul_eq_pbE h).
    - apply IH. exact (ws_cumul_pbE_LetIn_bo h).
    - apply IH. exact (ws_cumul_pbE_Prod_r h).
  Qed.

  Lemma ws_cumul_pbE_it_mkProd_or_LetIn_codom {pb Δ Γ B B'} :
    assumption_context Γ ->
    WS pb (Δ ,,, Γ) B B' -> WS pb Δ (it_mkProd_or_LetIn Γ B) (it_mkProd_or_LetIn Γ B').
  Proof.
    induction Γ as [|[na [b|] A] Γ IH] in B, B' |- *; cbn; intros ha h; [exact h| |].
    - exfalso. inversion ha.
    - apply IH; [inversion ha; assumption|]. exact (ws_cumul_pbE_Prod_r h).
  Qed.

End A5.
