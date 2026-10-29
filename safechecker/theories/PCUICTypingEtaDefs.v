(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICUnivSubst PCUICEquality
     PCUICReduction PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta
     PCUICWellScopedCumulativity PCUICWellScopedCumulativityEta PCUICContextSubst.
From Equations.Type Require Import Relation.
From Equations Require Import Equations.

(** * ETAK (EtaK7): the definitional η copies the η checker needs

  FORECAST-ONLY placeholder; to be replaced by an import of the canonical files when they land (the
  typing notions from ArityLane's pcuic T0 copies, the bidirectional judgments from EtaMetaLane's
  [BDTypingEta]); must not diverge from them. (Stream lead's ruling, 2026-10-29: this file must in the
  end import those definitions and redefine none of them.)

  BET-64 EtaCheckerLane, worker EtaK7, 2026-10-29; base [frac/eta] @ [0cb773a4].

  Definitions only: no hypothesis. Each one is the base definition with [typing] replaced by [typingE]
  and the cumulativity by [ws_cumul_pbE]:
  - [isTypeE], [isTypeRelE], [wf_local_relE]: [EnvironmentTyping.v:2752-2783] at [typingE];
  - NOT here any more: the bidirectional judgments, now imported (re-exported) from the canonical
    [BDTypingEta] (EtaMetaLane), whose cumulativity premises are [JoinE] (base's unscoped twin);
  - [subsletE] ([PCUICSubstitution.v:45]), [spine_substE] ([PCUICSpine.v:226]), [typing_spineE]
    ([PCUICArities.v:44]), and [ctx_instE] (the generic [ctx_inst] at [typingE], as base [PCUICSpine.v:28]
    instantiates it at [typing]). Not here: [ws_cumul_ctx_pbE_rel], canonical in [PCUICWsCumulEtaCtx]
    (P3, ArityLane, [frac/eta] @ [d8120081]), and [typingE_welltypedE], which is the constructor
    [iswelltypedE] ([PCUICTypingEta]).

  Plan rows: T0 owns [isType], [subslet], [spine_subst], [typing_spine]; T6 owns [Bidirectional/BD*].
  When those rows land, their files own these definitions and this file goes. *)

Implicit Types (cf : checker_flags) (Σ : global_env_ext) (Γ : context).

(** ** Well-scoped cumulativity notations over [ws_cumul_pbE] *)

Notation " Σ ;;; Γ ⊢E t ≤[ pb ] u " := (ws_cumul_pbE pb Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤[ pb ]  u") : type_scope.
Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.
Notation " Σ ;;; Γ ⊢E t = u " := (ws_cumul_pbE Conv Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  =  u") : type_scope.

(** ** Types over [typingE]

  FORECAST-ONLY placeholder; to be replaced by an import of ArityLane's pcuic T0 copies when they land;
  must not diverge from them. *)

Definition isTypeRelE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (rel : relevance) :=
  on_type_rel (lift_typing typingE) Σ Γ t rel.

Definition isTypeE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) :=
  on_type (lift_typing typingE) Σ Γ t.

Definition isTypeRelE_isTypeE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t : term) (r : relevance) :
  isTypeRelE Σ Γ t r -> isTypeE Σ Γ t.
Proof. apply lift_sorting_forget_rel. Defined.
Coercion isTypeRelE_isTypeE : isTypeRelE >-> isTypeE.

Definition wf_local_relE `{checker_flags} Σ := All_local_rel (lift_typing1 (typingE Σ)).

Notation ctx_instE Σ := (PCUICTyping.ctx_inst (typingE Σ)).

(** [PCUICSpine.ctx_inst_sub] at [typingE]. *)
Fixpoint ctx_inst_subE {cf:checker_flags} {Σ Γ Δ args} (c : ctx_instE Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | ctx_inst_nil => []
  | ctx_inst_ass na t i inst Δ P c => ctx_inst_subE c ++ [i]
  | ctx_inst_def na b t inst Δ c => ctx_inst_subE c ++ [b]
  end.

Definition isWfArityE {cf : checker_flags} Σ (Γ : context) T :=
  (isTypeE Σ Γ T × { ctx & { s & (destArity [] T = Some (ctx, s)) } }).

Definition isTypeE_welltypedE {cf Σ} {Γ T} : isTypeE Σ Γ T -> welltypedE Σ Γ T.
Proof. intros [_ [s []]]. now econstructor. Qed.

Definition isTypeRelE_welltypedE {cf Σ} {Γ T r} : isTypeRelE Σ Γ T r -> welltypedE Σ Γ T.
Proof. intros [_ [s []]]. now econstructor. Qed.

Definition has_sort_isTypeE {cf Σ} {Γ T} s : Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof. repeat (eexists; tea). Defined.

Definition has_sort_isTypeRelE {cf Σ} {Γ T} s r :
  isSortRel s r -> Σ ;;; Γ |-E T : tSort s -> isTypeRelE Σ Γ T r.
Proof. repeat (eexists; tea). Defined.

(** ** Bidirectional typing over E: CANONICAL, imported

  Stream lead's ruling (2026-10-29, ~09:45Z): the bidirectional judgments are EtaMetaLane's [BDTypingEta]
  ([pcuic/theories/Bidirectional/BDTypingEta.v], [fork/wip/eta-meta-bdtyping-2026-10-29] @ [b0523fbf]; to be
  re-pointed to the landed hash). This file no longer defines them. [BDTypingEta]'s [checkE_Cumul] and the
  case rule's parameters compare with [JoinE] (base's unscoped [cumulAlgo]/[convAlgo] twin); the checker
  builds them from its [ws_cumul_pbE] results with [checkE_Cumul_ws] / [All2_ws_cumul_pbE_JoinE], and a
  consumer that needs the scoped relation back uses [JoinE_ws_cumul_pbE]. [BDTypingEta] derives no
  signature; the checker's proofs ([depelim]) need one, so it is derived here. *)

From MetaRocq.PCUIC Require Export BDTypingEta.

Derive Signature for inferingE infering_sortE infering_prodE infering_induE checkingE.

(** ** Substitutions, spines and context cumulativity over E

  FORECAST-ONLY placeholder; to be replaced by an import of ArityLane's pcuic T0 copies when they land;
  must not diverge from them. *)

Inductive subsletE {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptysletE : subsletE Σ Γ [] []
| cons_let_assE Δ s na t T : subsletE Σ Γ s Δ ->
              Σ ;;; Γ |-E t : subst0 s T ->
             subsletE Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_defE Δ s na t T :
    subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E subst0 s t : subst0 s T ->
    subsletE Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).
Derive Signature for subsletE.

Record spine_substE {cf:checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubstE {
  spine_dom_wfE : wf_localE Σ Γ;
  spine_codom_wfE : wf_localE Σ (Γ ,,, Δ);
  inst_ctx_substE :> context_subst Δ inst s;
  inst_subsletE :> subsletE Σ Γ s Δ }.
Arguments inst_ctx_substE {cf Σ Γ inst s Δ}.
Arguments inst_subsletE {cf Σ Γ inst s Δ}.

Inductive typing_spineE {cf} Σ (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nilE ty ty' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ ty' ->
    Σ ;;; Γ ⊢E ty ≤ ty' ->
    typing_spineE Σ Γ ty [] ty'

| type_spine_consE ty hd tl na A B B' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ (tProd na A B) ->
    Σ ;;; Γ ⊢E ty ≤ tProd na A B ->
    Σ ;;; Γ |-E hd : A ->
    typing_spineE Σ Γ (subst10 hd B) tl B' ->
    typing_spineE Σ Γ ty (hd :: tl) B'.
Derive Signature for typing_spineE.
