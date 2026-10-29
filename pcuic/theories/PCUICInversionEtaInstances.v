(* Distributed under the terms of the MIT license. *)

(** * Satisfying instances of the lemmas of [PCUICInversionEta], and the checker's contract

  **The contract.** The five [T6_facts] fields of the checker's
  [safechecker/theories/PCUICTypingEtaHyps.v] (branch [wip/etak-k7-2026-10-29]) that are rows
  of [PCUICInversion] are copied here verbatim, under the checker's notation
  [Σ ;;; Γ ⊢E t ≤ u] ([ws_cumul_pbE Cumul Σ Γ t u]), and each is inhabited by its E lemma:
  [T6_inversion_Const_fit], [T6_inversion_LetIn_fit], [T6_inversion_Prod_fit],
  [T6_inversion_Rel_fit], [T6_inversion_Sort_fit].

  **The instances.** Each lemma of [PCUICInversionEta] that has a premise and does not conclude
  [False] is applied here to a concrete typing derivation in a well-formed environment, every
  premise proved. [inversion_VarE] and [inversion_EvarE] conclude [False]: no instance. The
  environments:
  - [si_Σ] ([PCUICCumulativitySpecEtaClosureInstances]): [Inductive I (A : Prop) : Prop := c : I A],
    with [si_wfE];
  - [Σ_po] ([PCUICEtaPrimOpInstance]): [int : Set], [land : int -> int -> int] and the primitive
    integers registered on [int]; [iv_po_wf_ext] re-proves its [wf_ext] unsquashed (the file has
    only [∥ wf_ext Σ_po ∥]), [iv_po_wfE] its [wfE];
  - [iv_Σ], declared here: [CoInductive R (A : Prop) : Prop := mkR { f : A }], a coinductive record
    with one projection, well formed ([iv_wf]) and so well formed for the η typing ([iv_wfE]).

  The derivation for [inversion_RelE] ends in an η step: in the context
  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g], the variable [y] is typed at
  [k (λx:Prop. g x)] by [typeE_Cumul], so the lemma's conclusion relates [k g] and
  [k (λx:Prop. g x)] in [ws_cumul_pbE]. [into_ws_cumulE] is applied to the same pair. The
  [match] of [inversion_CaseE] types its branch through a β-step. The others are the direct rule
  of their term former. The [match] derivation follows [cp_match_typed] of
  [PCUICTypingEtaCopies1Instances] (branch [wip/eta-e3-copies1-2026-10-29], not landed). *)

From Stdlib Require Import ssreflect ssrbool PrimInt63.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICOnFreeVars PCUICTyping
     PCUICCases PCUICEquality PCUICArityRed PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICClosedBodies PCUICEtaI5
     PCUICWellScopedCumulativityEta PCUICGuardClosure
     PCUICCumulativitySpecEtaClosureInstances PCUICEtaPrimOpInstance PCUICInversionEta.

Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.

(** ** The checker's [T6_facts] fields, verbatim, inhabited by the E lemmas *)

Section ContractFit.

  Context {cf : checker_flags}.

  Definition T6_inversion_Const_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {c : kername} {u : Instance.t} {T : term}, Σ;;; Γ |-E tConst c u : T -> ∑ decl : constant_body, wf_localE Σ Γ × declared_constant Σ c decl × consistent_instance_ext Σ (cst_universes decl) u × Σ ;;; Γ ⊢E (cst_type decl)@[u] ≤ T
    := @inversion_ConstE cf.

  Definition T6_inversion_LetIn_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {b : term} {B : term} {t : term} {T : term}, Σ;;; Γ |-E tLetIn na b B t : T -> ∑ A : term, lift_typing typingE Σ Γ (j_vdef na b B) × Σ;;; Γ,, vdef na b B |-E t : A × Σ ;;; Γ ⊢E tLetIn na b B A ≤ T
    := @inversion_LetInE cf.

  Definition T6_inversion_Prod_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {na : aname} {A : term} {B : term} {T : term}, Σ;;; Γ |-E tProd na A B : T -> ∑ s1 s2 : sort, lift_typing typingE Σ Γ (j_vass_s na A s1) × Σ;;; Γ,, vass na A |-E B : tSort s2 × Σ ;;; Γ ⊢E tSort (Sort.sort_of_product s1 s2) ≤ T
    := @inversion_ProdE cf.

  Definition T6_inversion_Rel_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {n : nat} {T : term}, Σ;;; Γ |-E tRel n : T -> ∑ decl : context_decl, wf_localE Σ Γ × nth_error Γ n = Some decl × Σ ;;; Γ ⊢E lift0 (S n) (decl_type decl) ≤ T
    := @inversion_RelE cf.

  Definition T6_inversion_Sort_fit :
    forall (Σ : global_env_ext) (wfΣ : wfE Σ) {Γ : context} {s : sort} {T : term}, Σ;;; Γ |-E tSort s : T -> wf_localE Σ Γ × wf_sort Σ s × Σ ;;; Γ ⊢E tSort (Sort.super s) ≤ T
    := @inversion_SortE cf.

End ContractFit.

#[local] Existing Instance default_checker_flags.
#[local] Existing Instance si_cb.

(** ** Typing pieces, in any environment *)

(** [Prop → Prop], [∀P:Prop. P] and [λx:Prop. x]. *)
Definition iv_PP : term := tProd si_na si_P si_P.
Definition iv_sPP : sort := Sort.sort_of_product (Sort.super sProp) (Sort.super sProp).
Definition iv_False : term := tProd si_na si_P (tRel 0).
Definition iv_id : term := tLambda si_na si_P (tRel 0).

Section Generic.

  Context (Σ : global_env_ext).

  Lemma iv_P_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E si_P : tSort (Sort.super sProp).
  Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

  Lemma iv_vass (Γ : context) (na : aname) A s :
    Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) -> lift_typing typingE Σ Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma iv_vass_s (Γ : context) (na : aname) A s :
    Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typingE Σ Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma iv_vdef (Γ : context) (na : aname) b A s :
    Σ ;;; Γ |-E b : A -> Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typingE Σ Γ (j_vdef na b A).
  Proof. intros hb h r. split; [exact hb|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma iv_wf_vass (Γ : context) (na : aname) A s :
    wf_localE Σ Γ -> Σ ;;; Γ |-E A : tSort s -> isSortRel s na.(binder_relevance) ->
    wf_localE Σ (Γ ,, vass na A).
  Proof. intros h hA r. apply localenv_cons_abs; [exact h|exact (iv_vass Γ na A s hA r)]. Qed.

  Lemma iv_wf_P (Γ : context) : wf_localE Σ Γ -> wf_localE Σ (Γ ,, vass si_na si_P).
  Proof. intros h. exact (iv_wf_vass Γ si_na si_P _ h (iv_P_typed Γ h) eq_refl). Qed.

  Lemma iv_PP_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E iv_PP : tSort iv_sPP.
  Proof.
    intros h. unfold iv_PP, iv_sPP. apply typeE_Prod.
    - exact (iv_vass_s Γ si_na si_P _ (iv_P_typed Γ h) eq_refl).
    - exact (iv_P_typed _ (iv_wf_P Γ h)).
  Qed.

  Lemma iv_False_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E iv_False : si_P.
  Proof.
    intros h. unfold iv_False.
    exact (typeE_Prod _ _ si_na si_P (tRel 0) (Sort.super sProp) sProp
             (iv_vass_s Γ si_na si_P _ (iv_P_typed Γ h) eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P Γ h) eq_refl)).
  Qed.

  Lemma iv_id_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E iv_id : iv_PP.
  Proof.
    intros h. unfold iv_id, iv_PP. apply typeE_Lambda.
    - exact (iv_vass Γ si_na si_P _ (iv_P_typed Γ h) eq_refl).
    - exact (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P Γ h) eq_refl).
  Qed.

  (** [(λx:Prop. x) (∀P:Prop. P) : Prop]. *)
  Lemma iv_app_typed (Γ : context) : wf_localE Σ Γ -> Σ ;;; Γ |-E tApp iv_id iv_False : si_P.
  Proof.
    intros h.
    exact (typeE_App _ _ iv_id si_na si_P si_P _ iv_False (iv_PP_typed Γ h) (iv_id_typed Γ h)
             (iv_False_typed Γ h)).
  Qed.

  (** [let z : Prop := ∀P:Prop. P in ...]. *)
  Lemma iv_vdef_False (Γ : context) : wf_localE Σ Γ -> lift_typing typingE Σ Γ (j_vdef si_na iv_False si_P).
  Proof. intros h. exact (iv_vdef Γ si_na iv_False si_P _ (iv_False_typed Γ h) (iv_P_typed Γ h) eq_refl). Qed.

  Lemma iv_wf_vdef (Γ : context) : wf_localE Σ Γ -> wf_localE Σ (Γ ,, vdef si_na iv_False si_P).
  Proof. intros h. apply localenv_cons_def; [exact h|exact (iv_vdef_False Γ h)]. Qed.

  (** [let z : Prop := ∀P:Prop. P in z]. *)
  Lemma iv_let_typed (Γ : context) : wf_localE Σ Γ ->
    Σ ;;; Γ |-E tLetIn si_na iv_False si_P (tRel 0) : tLetIn si_na iv_False si_P si_P.
  Proof.
    intros h. apply typeE_LetIn; [exact (iv_vdef_False Γ h)|].
    exact (typeE_Rel _ _ 0 (vdef si_na iv_False si_P) (iv_wf_vdef Γ h) eq_refl).
  Qed.

  (** [let z : Prop := ∀P:Prop. P in λx:Prop. x]. *)
  Lemma iv_letlam_typed (Γ : context) : wf_localE Σ Γ ->
    Σ ;;; Γ |-E tLetIn si_na iv_False si_P iv_id : tLetIn si_na iv_False si_P iv_PP.
  Proof.
    intros h. apply typeE_LetIn; [exact (iv_vdef_False Γ h)|].
    exact (iv_id_typed _ (iv_wf_vdef Γ h)).
  Qed.

End Generic.

(** ** Instances in [si_Σ] *)

(** *** The η-typed variable

  [g : Prop → Prop, k : (Prop → Prop) → Prop, y : k g ⊢ y : k (λx:Prop. g x)]. *)

Definition iv_K : term := tProd si_na iv_PP si_P.
Definition iv_Γg : context := [vass si_na iv_PP].
Definition iv_Γkg : context := [vass si_na iv_K; vass si_na iv_PP].
Definition iv_Γk : context := [vass si_na (tApp (tRel 0) (tRel 1)); vass si_na iv_K; vass si_na iv_PP].
Definition iv_kg : term := tApp (tRel 1) (tRel 2).
Definition iv_eta_g : term := tLambda si_na si_P (tApp (tRel 3) (tRel 0)).
Definition iv_keta : term := tApp (tRel 1) iv_eta_g.

Lemma iv_K_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E iv_K : tSort (Sort.sort_of_product iv_sPP (Sort.super sProp)).
Proof.
  intros h. unfold iv_K. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na iv_PP _ (iv_PP_typed si_Σ Γ h) eq_refl).
  - exact (iv_P_typed si_Σ _ (iv_wf_vass si_Σ Γ si_na iv_PP _ h (iv_PP_typed si_Σ Γ h) eq_refl)).
Qed.

Lemma iv_wf_Γg : wf_localE si_Σ iv_Γg.
Proof. exact (iv_wf_vass si_Σ [] si_na iv_PP _ localenv_nil (iv_PP_typed si_Σ [] localenv_nil) eq_refl). Qed.

Lemma iv_wf_Γkg : wf_localE si_Σ iv_Γkg.
Proof. exact (iv_wf_vass si_Σ iv_Γg si_na iv_K _ iv_wf_Γg (iv_K_typed iv_Γg iv_wf_Γg) eq_refl). Qed.

Lemma iv_kg0_typed : si_Σ ;;; iv_Γkg |-E tApp (tRel 0) (tRel 1) : si_P.
Proof.
  exact (typeE_App _ _ (tRel 0) si_na iv_PP si_P _ (tRel 1) (iv_K_typed iv_Γkg iv_wf_Γkg)
           (typeE_Rel _ _ 0 (vass si_na iv_K) iv_wf_Γkg eq_refl)
           (typeE_Rel _ _ 1 (vass si_na iv_PP) iv_wf_Γkg eq_refl)).
Qed.

Lemma iv_wf_Γk : wf_localE si_Σ iv_Γk.
Proof. exact (iv_wf_vass si_Σ iv_Γkg si_na (tApp (tRel 0) (tRel 1)) sProp iv_wf_Γkg iv_kg0_typed eq_refl). Qed.

Lemma iv_y_typed : si_Σ ;;; iv_Γk |-E tRel 0 : iv_kg.
Proof. exact (typeE_Rel _ _ 0 (vass si_na (tApp (tRel 0) (tRel 1))) iv_wf_Γk eq_refl). Qed.

Lemma iv_eta_g_typed : si_Σ ;;; iv_Γk |-E iv_eta_g : iv_PP.
Proof.
  have w : wf_localE si_Σ (iv_Γk ,, vass si_na si_P) := iv_wf_P si_Σ iv_Γk iv_wf_Γk.
  unfold iv_eta_g, iv_PP. apply typeE_Lambda.
  - exact (iv_vass si_Σ iv_Γk si_na si_P _ (iv_P_typed si_Σ iv_Γk iv_wf_Γk) eq_refl).
  - exact (typeE_App _ _ (tRel 3) si_na si_P si_P _ (tRel 0) (iv_PP_typed si_Σ _ w)
             (typeE_Rel _ _ 3 (vass si_na iv_PP) w eq_refl)
             (typeE_Rel _ _ 0 (vass si_na si_P) w eq_refl)).
Qed.

Lemma iv_keta_typed : si_Σ ;;; iv_Γk |-E iv_keta : si_P.
Proof.
  exact (typeE_App _ _ (tRel 1) si_na iv_PP si_P _ iv_eta_g (iv_K_typed iv_Γk iv_wf_Γk)
           (typeE_Rel _ _ 1 (vass si_na iv_K) iv_wf_Γk eq_refl) iv_eta_g_typed).
Qed.

(** [k g ≤ k (λx:Prop. g x)]: congruence, and the symmetric of one [cumul_eta_l] step. *)
Lemma iv_spec_eta : cumulSpecE si_Σ iv_Γk iv_kg iv_keta.
Proof.
  unfold cumulSpecE, iv_kg, iv_keta, iv_eta_g.
  apply cumulE_App; [apply cumulE_Refl|].
  apply cumulE_Sym. apply cumul_eta_l. apply cumulE_Refl.
Qed.

Lemma iv_rel_typed : si_Σ ;;; iv_Γk |-E tRel 0 : iv_keta.
Proof. exact (typeE_Cumul _ _ (tRel 0) iv_kg iv_keta sProp iv_y_typed iv_keta_typed iv_spec_eta). Qed.

Lemma iv_join_eta : JoinE si_Σ iv_Γk Cumul iv_kg iv_keta.
Proof. exact (wsE_join (into_ws_cumul_pbE_spec (Σ := si_Σ) iv_spec_eta eq_refl eq_refl eq_refl)). Qed.

Lemma into_ws_cumulE_inst : si_Σ ;;; iv_Γk ⊢E iv_kg ≤ iv_keta.
Proof. exact (into_ws_cumulE si_Σ si_wfE iv_y_typed iv_keta_typed iv_join_eta). Qed.

Lemma typing_closed_ctxE_inst : is_closed_context iv_Γk.
Proof. exact (typing_closed_ctxE si_Σ si_wfE iv_Γk (tRel 0) iv_keta iv_rel_typed). Qed.

Lemma typing_ws_cumul_pbE_inst : si_Σ ;;; iv_Γk ⊢E iv_keta ≤ iv_keta.
Proof. exact (typing_ws_cumul_pbE si_Σ si_wfE Cumul iv_Γk (tRel 0) iv_keta iv_rel_typed). Qed.

(** The conclusion relates [k g], the declared type of [y], with [k (λx:Prop. g x)]. *)
Lemma inversion_RelE_inst :
  ∑ decl, wf_localE si_Σ iv_Γk × (nth_error iv_Γk 0 = Some decl) ×
    si_Σ ;;; iv_Γk ⊢E lift0 1 (decl_type decl) ≤ iv_keta.
Proof. exact (inversion_RelE si_Σ si_wfE iv_rel_typed). Qed.

(** *** Sorts, products, abstractions, let-ins, applications *)

Lemma inversion_SortE_inst :
  wf_localE si_Σ [] × wf_sort si_Σ sProp × si_Σ ;;; [] ⊢E tSort (Sort.super sProp) ≤ tSort (Sort.super sProp).
Proof. exact (inversion_SortE si_Σ si_wfE (iv_P_typed si_Σ [] localenv_nil)). Qed.

Lemma inversion_ProdE_inst :
  ∑ s1 s2, lift_typing typingE si_Σ [] (j_vass_s si_na si_P s1) ×
    si_Σ ;;; [] ,, vass si_na si_P |-E tRel 0 : tSort s2 ×
    si_Σ ;;; [] ⊢E tSort (Sort.sort_of_product s1 s2) ≤ si_P.
Proof. exact (inversion_ProdE si_Σ si_wfE (iv_False_typed si_Σ [] localenv_nil)). Qed.

Definition inversion_Prod_sizeE_inst :=
  inversion_Prod_sizeE si_Σ si_wfE (iv_False_typed si_Σ [] localenv_nil).

Lemma inversion_LambdaE_inst :
  ∑ B, lift_typing typingE si_Σ [] (j_vass si_na si_P) ×
    si_Σ ;;; [] ,, vass si_na si_P |-E tRel 0 : B ×
    si_Σ ;;; [] ⊢E tProd si_na si_P B ≤ iv_PP.
Proof. exact (inversion_LambdaE si_Σ si_wfE (iv_id_typed si_Σ [] localenv_nil)). Qed.

Lemma inversion_LetInE_inst :
  ∑ A, lift_typing typingE si_Σ [] (j_vdef si_na iv_False si_P) ×
    si_Σ ;;; [] ,, vdef si_na iv_False si_P |-E tRel 0 : A ×
    si_Σ ;;; [] ⊢E tLetIn si_na iv_False si_P A ≤ tLetIn si_na iv_False si_P si_P.
Proof. exact (inversion_LetInE si_Σ si_wfE (iv_let_typed si_Σ [] localenv_nil)). Qed.

Lemma inversion_AppE_inst :
  ∑ na A B, si_Σ ;;; [] |-E iv_id : tProd na A B × si_Σ ;;; [] |-E iv_False : A ×
    si_Σ ;;; [] ⊢E B{0 := iv_False} ≤ si_P.
Proof. exact (inversion_AppE si_Σ si_wfE (iv_app_typed si_Σ [] localenv_nil)). Qed.

Definition inversion_App_sizeE_inst :=
  inversion_App_sizeE si_Σ si_wfE (iv_app_typed si_Σ [] localenv_nil).

(** [let z : Prop := ∀P:Prop. P in λx:Prop. x] is [it_mkLambda_or_LetIn [x : Prop; z := ∀P:Prop. P] x]. *)
Lemma inversion_it_mkLambda_or_LetInE_inst :
  ∑ A, si_Σ ;;; [] ,,, [vass si_na si_P; vdef si_na iv_False si_P] |-E tRel 0 : A ×
    si_Σ ;;; [] ⊢E it_mkProd_or_LetIn [vass si_na si_P; vdef si_na iv_False si_P] A
      ≤ tLetIn si_na iv_False si_P iv_PP.
Proof.
  exact (@inversion_it_mkLambda_or_LetInE _ si_Σ si_wfE [] [vass si_na si_P; vdef si_na iv_False si_P]
           (tRel 0) _ (iv_letlam_typed si_Σ [] localenv_nil)).
Qed.

(** *** The inductive [I] and its constructor *)

Lemma iv_ind_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E tInd si_ind [] : si_arity.
Proof. intros h. exact (typeE_Ind _ _ si_ind [] si_mdecl si_idecl h si_declared_inductive eq_refl). Qed.

Lemma iv_cstr_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tConstruct si_ind 0 [] : tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof.
  intros h.
  exact (typeE_Construct _ _ si_ind 0 [] si_mdecl si_idecl si_cdecl h si_declared_constructor eq_refl).
Qed.

Lemma inversion_IndE_inst :
  ∑ mdecl idecl, wf_localE si_Σ [] × declared_inductive si_Σ si_ind mdecl idecl ×
    consistent_instance_ext si_Σ (ind_universes mdecl) [] ×
    si_Σ ;;; [] ⊢E subst_instance [] idecl.(ind_type) ≤ si_arity.
Proof. exact (inversion_IndE si_Σ si_wfE (iv_ind_typed [] localenv_nil)). Qed.

Lemma inversion_ConstructE_inst :
  ∑ mdecl idecl cdecl, wf_localE si_Σ [] × declared_constructor si_Σ.1 (si_ind, 0) mdecl idecl cdecl ×
    consistent_instance_ext si_Σ (ind_universes mdecl) [] ×
    si_Σ ;;; [] ⊢E type_of_constructor mdecl cdecl (si_ind, 0) [] ≤
      tProd si_na si_P (tApp (tInd si_ind []) (tRel 0)).
Proof. exact (inversion_ConstructE si_Σ si_wfE (iv_cstr_typed [] localenv_nil)). Qed.

(** [I X : Prop] when [X : Prop]. *)
Lemma iv_IX_typed (Γ : context) X : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E X : si_P ->
  si_Σ ;;; Γ |-E tApp (tInd si_ind []) X : si_P.
Proof.
  intros h hX.
  exact (typeE_App _ _ (tInd si_ind []) si_na si_P si_P _ X (iv_PP_typed si_Σ Γ h) (iv_ind_typed Γ h) hX).
Qed.

(** *** A [match]

  In the context [x : Prop], [match c x as z in I x return I x with c => c x end]: the branch
  returns [c x] at the branch type [(λ z : I x. I x) (c x)], which a β-step relates to [I x]. *)

Definition iv_Ix (k : nat) : term := tApp (tInd si_ind []) (tRel k).
Definition iv_Γ1 : context := [vass si_na si_P].
Definition iv_ci : case_info := {| ci_ind := si_ind; ci_npar := 1; ci_relevance := Relevant; ci_cofix_nondep := true |}.
Definition iv_mp : predicate term :=
  {| pparams := [tRel 0]; puinst := []; pcontext := ind_predicate_context si_ind si_mdecl si_idecl;
     preturn := iv_Ix 1 |}.
Definition iv_disc : term := tApp (tConstruct si_ind 0 []) (tRel 0).
Definition iv_br : branch term := {| bcontext := []; bbody := iv_disc |}.
Definition iv_match : term := tCase iv_ci iv_mp iv_disc [iv_br].
Definition iv_zna : aname := {| binder_name := nNamed (ind_name si_idecl); binder_relevance := Relevant |}.

Lemma iv_wf_Γ1 : wf_localE si_Σ iv_Γ1.
Proof. exact (iv_wf_P si_Σ [] localenv_nil). Qed.

Lemma iv_x_typed : si_Σ ;;; iv_Γ1 |-E tRel 0 : si_P.
Proof. exact (typeE_Rel _ _ 0 (vass si_na si_P) iv_wf_Γ1 eq_refl). Qed.

Lemma iv_wf_mp : wf_predicate si_mdecl si_idecl iv_mp.
Proof. split; [reflexivity|]. constructor; [reflexivity|constructor]. Qed.

Lemma iv_wf_br : wf_branch si_cdecl iv_br.
Proof. constructor. Qed.

Lemma iv_Ix0_typed : si_Σ ;;; iv_Γ1 |-E iv_Ix 0 : si_P.
Proof. exact (iv_IX_typed iv_Γ1 (tRel 0) iv_wf_Γ1 iv_x_typed). Qed.

Lemma iv_wf_pctx : wf_localE si_Σ (iv_Γ1 ,, vass iv_zna (iv_Ix 0)).
Proof. exact (iv_wf_vass si_Σ iv_Γ1 iv_zna (iv_Ix 0) sProp iv_wf_Γ1 iv_Ix0_typed eq_refl). Qed.

Lemma iv_pret_typed : si_Σ ;;; iv_Γ1 ,, vass iv_zna (iv_Ix 0) |-E iv_Ix 1 : si_P.
Proof.
  exact (iv_IX_typed _ (tRel 1) iv_wf_pctx (typeE_Rel _ _ 1 (vass si_na si_P) iv_wf_pctx eq_refl)).
Qed.

Lemma iv_cstr_prod_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E tProd si_na si_P (tApp (tInd si_ind []) (tRel 0))
    : tSort (Sort.sort_of_product (Sort.super sProp) sProp).
Proof.
  intros h. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na si_P _ (iv_P_typed si_Σ Γ h) eq_refl).
  - exact (iv_IX_typed _ (tRel 0) (iv_wf_P si_Σ Γ h)
             (typeE_Rel _ _ 0 (vass si_na si_P) (iv_wf_P si_Σ Γ h) eq_refl)).
Qed.

Lemma iv_disc_typed : si_Σ ;;; iv_Γ1 |-E iv_disc : iv_Ix 0.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ (tRel 0)
           (iv_cstr_prod_typed iv_Γ1 iv_wf_Γ1) (iv_cstr_typed iv_Γ1 iv_wf_Γ1) iv_x_typed).
Qed.

Lemma iv_ctx_inst : ctx_inst (typingE si_Σ) iv_Γ1 [tRel 0] [vass si_na si_P].
Proof. econstructor; [|constructor]. exact iv_x_typed. Qed.

Lemma iv_bty_typed :
  si_Σ ;;; iv_Γ1 |-E tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc : si_P.
Proof.
  refine (typeE_App _ _ (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_zna (iv_Ix 0) si_P _ iv_disc
            _ _ iv_disc_typed).
  - apply typeE_Prod.
    + exact (iv_vass_s si_Σ iv_Γ1 iv_zna (iv_Ix 0) sProp iv_Ix0_typed eq_refl).
    + exact (iv_P_typed si_Σ _ iv_wf_pctx).
  - apply typeE_Lambda.
    + exact (iv_vass si_Σ iv_Γ1 iv_zna (iv_Ix 0) sProp iv_Ix0_typed eq_refl).
    + exact iv_pret_typed.
Qed.

Lemma iv_br_typed :
  si_Σ ;;; iv_Γ1 |-E iv_disc : tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc.
Proof.
  refine (typeE_Cumul _ _ iv_disc (iv_Ix 0) _ sProp iv_disc_typed iv_bty_typed _).
  apply cumulE_Sym. exact (cumulE_beta _ _ Conv iv_zna (iv_Ix 0) (iv_Ix 1) iv_disc).
Qed.

Lemma iv_case_side :
  case_side_conditions (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) si_Σ iv_Γ1 iv_ci iv_mp sProp
    si_mdecl si_idecl [] (case_predicate_context si_ind si_mdecl si_idecl iv_mp).
Proof.
  constructor.
  - reflexivity.
  - exact iv_wf_mp.
  - reflexivity.
  - exact iv_wf_pctx.
  - exact (alpha_eq_reflexive (pcontext iv_mp)).
  - reflexivity.
  - reflexivity.
  - exact iv_ctx_inst.
  - reflexivity.
Qed.

Lemma iv_case_brs :
  case_branch_typing (fun Γ => wf_localE si_Σ Γ) (typingE si_Σ) iv_Γ1 iv_ci iv_mp sProp si_mdecl si_idecl
    (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl iv_mp) (preturn iv_mp))
    [iv_br].
Proof.
  constructor.
  - constructor; [exact iv_wf_br|constructor].
  - constructor; [|constructor].
    split; [constructor|]. cbv zeta. split; [|split].
    + exact iv_wf_Γ1.
    + exact iv_br_typed.
    + exact iv_bty_typed.
Qed.

Definition iv_match_ty : term :=
  mkApps (it_mkLambda_or_LetIn (case_predicate_context si_ind si_mdecl si_idecl iv_mp) (preturn iv_mp))
    ([] ++ [iv_disc]).

Lemma iv_match_typed : si_Σ ;;; iv_Γ1 |-E iv_match : iv_match_ty.
Proof.
  eapply (typeE_Case _ _ iv_ci iv_mp iv_disc [iv_br] [] sProp si_mdecl si_idecl).
  - exact si_declared_inductive.
  - exact iv_pret_typed.
  - exact iv_disc_typed.
  - exact iv_case_side.
  - exact iv_case_brs.
Qed.

Definition inversion_CaseE_inst := inversion_CaseE si_Σ si_wfE iv_match_typed.

(** *** A fixpoint

  [fix f (x : I (∀P:Prop. P)) : I (∀P:Prop. P) := x], structural on [x]. *)

Definition iv_IF : term := tApp (tInd si_ind []) iv_False.
Definition iv_fix_ty : term := tProd si_na iv_IF iv_IF.
Definition iv_mfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_fix_ty; dbody := tLambda si_na iv_IF (tRel 0); rarg := 0 |}].
Definition iv_Γf : context := [vass si_na iv_fix_ty].

Lemma iv_IF_typed (Γ : context) : wf_localE si_Σ Γ -> si_Σ ;;; Γ |-E iv_IF : si_P.
Proof. intros h. exact (iv_IX_typed Γ iv_False h (iv_False_typed si_Σ Γ h)). Qed.

Lemma iv_wf_IF (Γ : context) : wf_localE si_Σ Γ -> wf_localE si_Σ (Γ ,, vass si_na iv_IF).
Proof. intros h. exact (iv_wf_vass si_Σ Γ si_na iv_IF sProp h (iv_IF_typed Γ h) eq_refl). Qed.

Lemma iv_fix_ty_typed (Γ : context) : wf_localE si_Σ Γ ->
  si_Σ ;;; Γ |-E iv_fix_ty : tSort (Sort.sort_of_product sProp sProp).
Proof.
  intros h. unfold iv_fix_ty. apply typeE_Prod.
  - exact (iv_vass_s si_Σ Γ si_na iv_IF sProp (iv_IF_typed Γ h) eq_refl).
  - exact (iv_IF_typed _ (iv_wf_IF Γ h)).
Qed.

Lemma iv_wf_Γf : wf_localE si_Σ iv_Γf.
Proof. exact (iv_wf_vass si_Σ [] si_na iv_fix_ty _ localenv_nil (iv_fix_ty_typed [] localenv_nil) eq_refl). Qed.

Lemma iv_fix_body_typed : si_Σ ;;; iv_Γf |-E tLambda si_na iv_IF (tRel 0) : lift0 1 iv_fix_ty.
Proof.
  change (lift0 1 iv_fix_ty) with (tProd si_na iv_IF iv_IF).
  apply typeE_Lambda.
  - exact (iv_vass si_Σ iv_Γf si_na iv_IF sProp (iv_IF_typed iv_Γf iv_wf_Γf) eq_refl).
  - exact (typeE_Rel _ _ 0 (vass si_na iv_IF) (iv_wf_IF iv_Γf iv_wf_Γf) eq_refl).
Qed.

Lemma iv_fix_guard : fix_guard si_Σ [] iv_mfix.
Proof.
  change (guard_cl Fix si_Σ [] iv_mfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma iv_wf_fix : wf_fixpointE si_Σ [] iv_mfix.
Proof.
  split; [reflexivity|]. split; [reflexivity|].
  exists si_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_fix_ty. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma iv_fix_typed : si_Σ ;;; [] |-E tFix iv_mfix 0 : iv_fix_ty.
Proof.
  refine (typeE_Fix _ _ iv_mfix 0 _ localenv_nil iv_fix_guard eq_refl _ _ iv_wf_fix).
  - constructor; [|constructor].
    exact (iv_vass si_Σ [] si_na iv_fix_ty _ (iv_fix_ty_typed [] localenv_nil) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef si_Σ iv_Γf si_na _ (lift0 1 iv_fix_ty) _ iv_fix_body_typed
             (iv_fix_ty_typed iv_Γf iv_wf_Γf) eq_refl).
Qed.

Definition inversion_FixE_inst := inversion_FixE si_Σ si_wfE iv_fix_typed.

(** ** Instances in [Σ_po]: a constant and a primitive integer *)

(** [Σ_po_wf] of [PCUICEtaPrimOpInstance], unsquashed: the same proof without its first
    [constructor]. *)
Lemma iv_po_wf_ext : wf_ext Σ_po.
Proof.
  split; [|exact po_udecl_ok].
  split; [exact po_univs_ok|]. split; [exact po_retro_wf|].
  cbn. constructor.
  - constructor; [constructor|].
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_land_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_land_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

Definition iv_po_wfE : wfE Σ_po0 := wf_incl_E (fst iv_po_wf_ext).

Lemma iv_po_declared_int : declared_constant Σ_po po_int_kn po_int_body.
Proof. right; left; reflexivity. Qed.

Lemma iv_land_typed : Σ_po ;;; [] |-E tConst po_land_kn [] : po_land_ty.
Proof. exact (typeE_Const _ _ po_land_kn [] po_land_body localenv_nil Σ_po_declared_land eq_refl). Qed.

Lemma inversion_ConstE_inst :
  ∑ decl, wf_localE Σ_po [] × declared_constant Σ_po po_land_kn decl ×
    consistent_instance_ext Σ_po (cst_universes decl) [] ×
    Σ_po ;;; [] ⊢E subst_instance [] (cst_type decl) ≤ po_land_ty.
Proof. exact (inversion_ConstE Σ_po iv_po_wfE iv_land_typed). Qed.

(** The literal [1] of the primitive integers. *)
Definition iv_one : prim_val := prim_int 1%uint63.

Lemma iv_prim_typed : Σ_po ;;; [] |-E tPrim iv_one : prim_type iv_one po_int_kn.
Proof.
  refine (typeE_Prim Σ_po [] iv_one po_int_kn po_int_body localenv_nil eq_refl
            iv_po_declared_int _ _).
  - split; reflexivity.
  - constructor.
Qed.

Lemma inversion_PrimE_inst :
  ∑ prim_ty cdecl,
    [× wf_localE Σ_po [],
      primitive_constant Σ_po (prim_val_tag iv_one) = Some prim_ty,
      declared_constant Σ_po prim_ty cdecl,
      primitive_invariants (prim_val_tag iv_one) cdecl,
      primitive_typing_hyps (typingE Σ_po) Σ_po [] iv_one &
      Σ_po ;;; [] ⊢E prim_type iv_one prim_ty ≤ prim_type iv_one po_int_kn].
Proof. exact (inversion_PrimE Σ_po iv_po_wfE iv_prim_typed). Qed.

(** ** The environment [iv_env]: [CoInductive R (A : Prop) : Prop := mkR { f : A }] *)

Definition iv_kn : kername := (MPfile ["InvInst"], "R").
Definition iv_ind : inductive := {| inductive_mind := iv_kn; inductive_ind := 0 |}.
Definition iv_fna : aname := mkBindAnn (nNamed "f") Relevant.

Definition iv_cdecl : constructor_body :=
  {| cstr_name := "mkR"; cstr_args := [vass iv_fna (tRel 0)]; cstr_indices := [];
     cstr_type := tProd si_na si_P (tProd iv_fna (tRel 0) (tApp (tRel 2) (tRel 1))); cstr_arity := 1 |}.

(** The projection [f]: in the context [A : Prop, r : R A], its type is [A]. *)
Definition iv_pdecl : projection_body := {| proj_name := "f"; proj_relevance := Relevant; proj_type := tRel 1 |}.

Definition iv_idecl : one_inductive_body :=
  {| ind_name := "R"; ind_indices := []; ind_sort := sProp; ind_type := si_arity;
     ind_kelim := IntoAny; ind_ctors := [iv_cdecl]; ind_projs := [iv_pdecl]; ind_relevance := Relevant |}.

Definition iv_mdecl : mutual_inductive_body :=
  {| ind_finite := CoFinite; ind_npars := 1; ind_params := si_params; ind_bodies := [iv_idecl];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition iv_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(iv_kn, InductiveDecl iv_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition iv_Σ : global_env_ext := (iv_env, Monomorphic_ctx).

Definition iv_Γi : context := arities_context [iv_idecl].

Lemma iv_wf_Γi : wf_local si_Σ0 iv_Γi.
Proof.
  apply localenv_cons_abs; [constructor|].
  exact (si_vass _ (mkBindAnn (nNamed "R") rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
Qed.

(** The constructor type [Π A : Prop. A -> R A], in the arities context. *)
Lemma iv_ctype_typed :
  si_Σ0 ;;; iv_Γi |- cstr_type iv_cdecl
    : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.sort_of_product sProp sProp)).
Proof.
  have w2 := si_wf_P iv_Γi iv_wf_Γi.
  have hA : si_Σ0 ;;; iv_Γi ,, vass si_na si_P |- tRel 0 : tSort sProp :=
    type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl.
  have w3 : wf_local si_Σ0 ((iv_Γi ,, vass si_na si_P) ,, vass iv_fna (tRel 0)).
  { apply localenv_cons_abs; [exact w2|exact (si_vass _ iv_fna _ _ hA eq_refl)]. }
  apply type_Prod.
  - exact (si_vass_s _ si_na _ _ (si_P_typed iv_Γi iv_wf_Γi) eq_refl).
  - apply type_Prod.
    + exact (si_vass_s _ iv_fna _ _ hA eq_refl).
    + refine (type_App _ _ (tRel 2) si_na si_P (tSort sProp)
                (Sort.sort_of_product (Sort.super sProp) (Sort.super sProp)) (tRel 1) _ _ _).
      * exact (si_arity_typed _ w3).
      * exact (type_Rel _ _ 2 (vass (mkBindAnn (nNamed "R") rel_of_Type) si_arity) w3 eq_refl).
      * exact (type_Rel _ _ 1 (vass si_na si_P) w3 eq_refl).
Qed.

Lemma iv_on_constructor :
  on_constructor cumulSpec0 (lift_typing typing) si_Σ0 iv_mdecl 0 iv_idecl [] iv_cdecl [sProp].
Proof.
  have w2 := si_wf_P iv_Γi iv_wf_Γi.
  unshelve econstructor.
  - reflexivity.
  - reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon Relevant) _ _ iv_ctype_typed eq_refl).
  - split; [exact tt|].
    exact (si_vass_s _ iv_fna _ _ (type_Rel _ _ 0 (vass si_na si_P) w2 eq_refl) eq_refl).
  - constructor.
  - cbn. eapply pos_ass.
    + apply pos_arg_closed. reflexivity.
    + eapply pos_ass.
      * apply pos_arg_closed. reflexivity.
      * exact (pos_concl _ _ _ [vass iv_fna (tRel 0); vass si_na si_P] [tRel 1]
                 (All_cons (x := tRel 1) (eq_refl : is_true (closedn 2 (tRel 1))) All_nil)).
  - intros v e. discriminate e.
  - destruct lets_in_constructor_types; [exact I|reflexivity].
Qed.

Lemma iv_on_ind_body :
  on_ind_body cumulSpec0 (lift_typing typing) si_Σ0 iv_kn iv_mdecl 0 iv_idecl.
Proof.
  unshelve econstructor.
  - exact [[sProp]].
  - exists (tSort sProp). split; [reflexivity|].
    apply arity_red_sort. apply whd_stop. reflexivity.
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
  - exact (si_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (si_arity_typed [] si_wf_nil) eq_refl).
  - constructor; [exact iv_on_constructor|constructor].
  - cbn. constructor; try reflexivity.
    constructor; [|constructor]. cbn. constructor; cbn; reflexivity.
  - reflexivity.
  - reflexivity.
  - exact I.
Qed.

Lemma iv_on_inductive : on_inductive cumulSpec0 (lift_typing typing) si_Σ0 iv_kn iv_mdecl.
Proof.
  constructor.
  - constructor; [exact iv_on_ind_body|constructor].
  - exact (si_wf_P [] si_wf_nil).
  - reflexivity.
  - reflexivity.
Qed.

(** [si_wf]'s proof, with [iv_on_inductive] for the declaration. *)
Lemma iv_wf : wf iv_env.
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
    + exact iv_on_inductive.
    + cbn. intros i h; discriminate h.
Qed.

Definition iv_wfE : wfE iv_env := wf_incl_E iv_wf.

Lemma iv_declared_inductive : declared_inductive iv_Σ iv_ind iv_mdecl iv_idecl.
Proof. split; [left; reflexivity|reflexivity]. Qed.

Lemma iv_declared_constructor : declared_constructor iv_Σ (iv_ind, 0) iv_mdecl iv_idecl iv_cdecl.
Proof. split; [exact iv_declared_inductive|reflexivity]. Qed.

(** ** Instances in [iv_Σ]: a cofixpoint and a projection *)

Definition iv_R (X : term) : term := tApp (tInd iv_ind []) X.

Lemma iv_Rind_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E tInd iv_ind [] : si_arity.
Proof. intros h. exact (typeE_Ind _ _ iv_ind [] iv_mdecl iv_idecl h iv_declared_inductive eq_refl). Qed.

Lemma iv_RX_typed (Γ : context) X : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E X : si_P -> iv_Σ ;;; Γ |-E iv_R X : si_P.
Proof.
  intros h hX.
  exact (typeE_App _ _ (tInd iv_ind []) si_na si_P si_P _ X (iv_PP_typed iv_Σ Γ h) (iv_Rind_typed Γ h) hX).
Qed.

(** [mkR : Π A : Prop. A -> R A]. *)
Lemma iv_mkR_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tConstruct iv_ind 0 [] : tProd si_na si_P (tProd iv_fna (tRel 0) (iv_R (tRel 1))).
Proof.
  intros h.
  exact (typeE_Construct _ _ iv_ind 0 [] iv_mdecl iv_idecl iv_cdecl h iv_declared_constructor eq_refl).
Qed.

Lemma iv_mkR_ty_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tProd si_na si_P (tProd iv_fna (tRel 0) (iv_R (tRel 1)))
    : tSort (Sort.sort_of_product (Sort.super sProp) (Sort.sort_of_product sProp sProp)).
Proof.
  intros h.
  have w1 := iv_wf_P iv_Σ Γ h.
  have hA : iv_Σ ;;; Γ ,, vass si_na si_P |-E tRel 0 : tSort sProp :=
    typeE_Rel _ _ 0 (vass si_na si_P) w1 eq_refl.
  have w2 := iv_wf_vass iv_Σ _ iv_fna (tRel 0) sProp w1 hA eq_refl.
  apply typeE_Prod; [exact (iv_vass_s iv_Σ Γ si_na si_P _ (iv_P_typed iv_Σ Γ h) eq_refl)|].
  apply typeE_Prod; [exact (iv_vass_s iv_Σ _ iv_fna (tRel 0) sProp hA eq_refl)|].
  exact (iv_RX_typed _ (tRel 1) w2 (typeE_Rel _ _ 1 (vass si_na si_P) w2 eq_refl)).
Qed.

(** *** A cofixpoint

  In the context [p : ∀P:Prop. P], [cofix g : R (∀P:Prop. P) := mkR (∀P:Prop. P) p]. *)

Definition iv_RF : term := iv_R iv_False.
Definition iv_cofix_body : term := tApp (tApp (tConstruct iv_ind 0 []) iv_False) (tRel 1).
Definition iv_cmfix : mfixpoint term :=
  [{| dname := si_na; dtype := iv_RF; dbody := iv_cofix_body; rarg := 0 |}].
Definition iv_Γc : context := [vass si_na iv_False].
Definition iv_Γcf : context := [vass si_na iv_RF; vass si_na iv_False].

Lemma iv_wf_Γc : wf_localE iv_Σ iv_Γc.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_False sProp localenv_nil (iv_False_typed iv_Σ [] localenv_nil) eq_refl). Qed.

Lemma iv_RF_typed (Γ : context) : wf_localE iv_Σ Γ -> iv_Σ ;;; Γ |-E iv_RF : si_P.
Proof. intros h. exact (iv_RX_typed Γ iv_False h (iv_False_typed iv_Σ Γ h)). Qed.

(** [mkR (∀P:Prop. P) : (∀P:Prop. P) -> R (∀P:Prop. P)]. *)
Lemma iv_mkRF_typed (Γ : context) : wf_localE iv_Σ Γ ->
  iv_Σ ;;; Γ |-E tApp (tConstruct iv_ind 0 []) iv_False : tProd iv_fna iv_False iv_RF.
Proof.
  intros h.
  exact (typeE_App _ _ (tConstruct iv_ind 0 []) si_na si_P _ _ iv_False (iv_mkR_ty_typed Γ h)
           (iv_mkR_typed Γ h) (iv_False_typed iv_Σ Γ h)).
Qed.

Lemma iv_wf_Γcf : wf_localE iv_Σ iv_Γcf.
Proof. exact (iv_wf_vass iv_Σ iv_Γc si_na iv_RF sProp iv_wf_Γc (iv_RF_typed iv_Γc iv_wf_Γc) eq_refl). Qed.

Lemma iv_cofix_body_typed : iv_Σ ;;; iv_Γcf |-E iv_cofix_body : lift0 1 iv_RF.
Proof.
  have hF := iv_False_typed iv_Σ iv_Γcf iv_wf_Γcf.
  have wF := iv_wf_vass iv_Σ iv_Γcf iv_fna iv_False sProp iv_wf_Γcf hF eq_refl.
  refine (typeE_App _ _ (tApp (tConstruct iv_ind 0 []) iv_False) iv_fna iv_False iv_RF
            (Sort.sort_of_product sProp sProp) (tRel 1) _ (iv_mkRF_typed iv_Γcf iv_wf_Γcf) _).
  - apply typeE_Prod; [exact (iv_vass_s iv_Σ iv_Γcf iv_fna iv_False sProp hF eq_refl)|].
    exact (iv_RF_typed _ wF).
  - exact (typeE_Rel _ _ 1 (vass si_na iv_False) iv_wf_Γcf eq_refl).
Qed.

Lemma iv_cofix_guard : cofix_guard iv_Σ iv_Γc iv_cmfix.
Proof.
  change (guard_cl CoFix iv_Σ iv_Γc iv_cmfix). apply gc_check.
  split; [vm_compute; reflexivity|]. exists 30. vm_compute. reflexivity.
Qed.

Lemma iv_wf_cofix : wf_cofixpointE iv_Σ iv_Γc iv_cmfix.
Proof.
  exists iv_kn. split; [discriminate|]. split; [|reflexivity].
  constructor; [|constructor].
  exists iv_RF. split; [reflexivity|]. split; [reflexivity|apply cumulE_Refl].
Qed.

Lemma iv_cofix_typed : iv_Σ ;;; iv_Γc |-E tCoFix iv_cmfix 0 : iv_RF.
Proof.
  refine (typeE_CoFix _ _ iv_cmfix 0 _ iv_wf_Γc iv_cofix_guard eq_refl _ _ iv_wf_cofix).
  - constructor; [|constructor].
    exact (iv_vass iv_Σ iv_Γc si_na iv_RF sProp (iv_RF_typed iv_Γc iv_wf_Γc) eq_refl).
  - constructor; [|constructor].
    exact (iv_vdef iv_Σ iv_Γcf si_na iv_cofix_body (lift0 1 iv_RF) sProp iv_cofix_body_typed
             (iv_RF_typed iv_Γcf iv_wf_Γcf) eq_refl).
Qed.

Definition inversion_CoFixE_inst := inversion_CoFixE iv_Σ iv_wfE iv_cofix_typed.

(** *** A projection

  In the context [r : R (∀P:Prop. P)], [r.(f) : ∀P:Prop. P]. *)

Definition iv_proj : projection := {| proj_ind := iv_ind; proj_npars := 1; proj_arg := 0 |}.
Definition iv_Γr : context := [vass si_na iv_RF].

Lemma iv_wf_Γr : wf_localE iv_Σ iv_Γr.
Proof. exact (iv_wf_vass iv_Σ [] si_na iv_RF sProp localenv_nil (iv_RF_typed [] localenv_nil) eq_refl). Qed.

Lemma iv_declared_projection : declared_projection iv_Σ iv_proj iv_mdecl iv_idecl iv_cdecl iv_pdecl.
Proof. split; [exact iv_declared_constructor|split; reflexivity]. Qed.

Lemma iv_proj_typed : iv_Σ ;;; iv_Γr |-E tProj iv_proj (tRel 0) : iv_False.
Proof.
  exact (typeE_Proj _ _ iv_proj (tRel 0) [] iv_mdecl iv_idecl iv_cdecl iv_pdecl [iv_False]
           iv_declared_projection (typeE_Rel _ _ 0 (vass si_na iv_RF) iv_wf_Γr eq_refl) eq_refl).
Qed.

Definition inversion_ProjE_inst := inversion_ProjE iv_Σ iv_wfE iv_proj_typed.
