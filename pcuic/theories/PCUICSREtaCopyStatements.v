(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICUtils PCUICOnOne
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICGlobalEnv PCUICWeakeningEnv PCUICWeakeningEnvConv
     PCUICWeakeningEnvTyp PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSubstitution PCUICContextSubst PCUICCasesContexts PCUICClosed PCUICClosedTyp PCUICClosedConv PCUICCasesWfTyp
     PCUICCumulativity PCUICGeneration PCUICReduction
     PCUICAlpha PCUICEquality PCUICValidity PCUICParallelReductionConfluence
     PCUICConfluence PCUICContextConversion PCUICContextConversionTyp
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICConversion PCUICInversion PCUICContexts PCUICArities
     PCUICWellScopedCumulativity PCUICGuardCondition
     PCUICParallelReduction PCUICSpine PCUICInductives PCUICFixWitness PCUICInductiveInversion
     PCUICSigmaCalculus PCUICPrimitiveRed PCUICOnFreeVars.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICWsCumulEtaCtx
     PCUICConversionEtaCongr PCUICTypingEtaNotions PCUICClosedBodies
     PCUICSubstitutionEta PCUICAritiesEta.
From MetaRocq.PCUIC.Typing Require PCUICUnivSubstitutionTypEta.

From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).
(* IMPLICIT STATUS. Each statement writes every binder with the implicit status, the name and
   the position of base's compiled lemma (its [Arguments] line), environment binder included:
   a base implicit [{wfΣ : wf Σ}] is written [{wfΣ : wfE Σ}], a base explicit named
   [(wfΣ : wf Σ.1)] is written [(wfΣ : wfE Σ.1)].
   A [Definition … : Type] cannot carry implicit status: Rocq drops it with the warning
   [unexpected-implicit-declaration] (silenced below), and a hypothesis declared with the
   Definition's NAME ([Context (H : X_statement)], [fun H : X_statement => …], a class field
   [f : X_statement], [Lemma l : X_statement]) gets every argument explicit. So does
   [Context (H : <body text>)]. The implicit status is kept only when the BODY TEXT is the type
   of a class field or of a [fun] binder, which is how lanes/eta/impl/srstmt-implcheck.py
   checks it (lanes/eta/sr-statement-note.md, "Implicit status"), and when the copy declares
   [<base>E] with this text. *)
Local Set Warnings "-unexpected-implicit-declaration".

(** * E statements of the copy lemmas that base [PCUICSR] uses (T0 copies 15-18)

  Forecast file for EtaMetaLane: NOT registered in [_RocqProject.in]; no proof. Each
  [<base>E_statement] is the statement the E copy (copy 15 [PCUICSpineEta], 16
  [PCUICInductivesEta], 17 [PCUICFixWitnessEta], 18 [PCUICInductiveInversionEta]) commits to
  prove under the name [<base>E]. Source: [pcuic/theories/PCUICSR.v] at [d8120081] (identical
  at [da1eb84b]); the base statements were printed by [About] under [Set Printing All]
  (lanes/eta/sr-statement-note.md has the table, the use lines and the verdicts).

  Use: forecast hypotheses or section variables only, NEVER [Admitted]. The landing E SR has
  ZERO hypotheses left from this set: each is discharged by the copy's [<base>E]. Any change
  to a statement goes to EtaMetaLane the same minute.

  Twin rule: [typing] → [typingE] ([;;; |-] → [;;; |-E]), [wf_local] → [wf_localE], [wf] →
  [wfE], [wf_global_ext] → [wf_global_extE], [isType] → [isTypeE], [wf_local_rel] →
  [wf_local_relE], [ctx_inst] → [ctx_instE], [convSpec] → [convSpecE], [ws_cumul_pb pb Σ Γ]
  (base notation [Σ ;;; Γ ⊢ t ≤[pb] u]) → [ws_cumul_pbE pb Σ Γ], [ws_cumul_pb_terms] →
  [ws_cumul_pbE_terms], [ws_cumul_ctx_pb] (base notation [Σ ⊢ Γ ≤[pb] Δ]) →
  [ws_cumul_ctx_pbE], [ws_cumul_ctx_pb_rel] → [ws_cumul_ctx_pbE_rel],
  [wf_fixpoint]/[wf_cofixpoint] → [wf_fixpointE]/[wf_cofixpointE], [subslet] → [subsletE]
  ([PCUICSubstitutionEta], copy 10), [typing_spine] ([PCUICArities]'s) → [typing_spineE]
  ([PCUICAritiesEta], copy 14; NOT [PCUICGenerationEta.typing_spineE], which is not
  imported), and each base definition of the copy files → its E twin below. Reduction
  ([Σ ;;; Γ ⊢ t ⇝ u], [red1]) is unchanged.

  [isTypeE] is [PCUICTypingEtaNotions.isTypeE := on_type (lift_typing typingE)].

  Statement labelled NOT TWIN (ADDED ClosedBodies), as the stream lead's class ruling of
  2026-10-29 09:30Z allows (lanes/eta/closedbodies-register.md, row 1):
  [type_mkAppsE_statement] adds exactly [{wfΣ : ClosedBodies Σ}] after [Σ], which base
  [PCUICSpine.type_mkApps] has not: [ws_cumul_pbE] → [cumulSpecE] ([ws_cumul_pbE_forget_spec])
  needs it. [wfE] supplies it through [wfE_ClosedBodies] ([Typing/PCUICClosedTypEta.v]).

  The check: this file typechecks against [d8120081] plus the files that
  [wip/eta-e3-copies2-2026-10-29] @ [1da9a004] (which contains [fork/frac/eta] = [07a50edd])
  changes; no block is commented. *)

(** ** E twins of the copy-file definitions that the statements mention

  FORECAST COPIES: [ctx_inst_subE], [decl_ws_cumul_pbE], [spine_substE], [arity_spineE] and
  [wf_arity_spineE] (copy 15, [PCUICSpineEta]), [wf_subsletE] (copy 16,
  [PCUICInductivesEta]) and [decl_ws_cumul_pbE] (copy 18, [PCUICInductiveInversionEta]) below
  are stand-ins for the definitions those copies will own, with this exact text. Two
  [Record spine_substE] declarations are two different types, so at landing this file (or the
  E SR) must import the copies' definitions and delete these. *)

(** Copy 15, [PCUICSpine.v:903] [ctx_inst_sub] (its argument is over [PCUICSpine]'s
    notation [ctx_inst Σ := ctx_inst (typing Σ)]). [ctx_instE] itself, the twin of the
    notation [PCUICSpine.v:28], is [PCUICTypingEtaNotions.ctx_instE]. The constructors are
    qualified because [PCUICSpine.v:1164] declares a lemma named [ctx_inst_ass]. *)
Fixpoint ctx_inst_subE {cf : checker_flags} {Σ : global_env_ext} {Γ Δ args}
  (c : ctx_instE Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | PCUICTyping.ctx_inst_nil => []
  | PCUICTyping.ctx_inst_ass na t i inst Δ P c => ctx_inst_subE c ++ [i]
  | PCUICTyping.ctx_inst_def na b t inst Δ c => ctx_inst_subE c ++ [b]
  end.

(** Copy 18, [PCUICInductiveInversion.v:856] notation [decl_ws_cumul_pb]. *)
Notation decl_ws_cumul_pbE Σ Γ :=
  (All_decls_alpha_pb Conv (fun pb (x0 y0 : term) => ws_cumul_pbE pb Σ Γ x0 y0)).

(** Copy 15, [PCUICSpine.v:226] [spine_subst]. *)
Record spine_substE {cf : checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubstE {
  spine_dom_wfE : wf_localE Σ Γ;
  spine_codom_wfE : wf_localE Σ (Γ ,,, Δ);
  inst_ctx_substE :> context_subst Δ inst s;
  inst_subsletE :> subsletE Σ Γ s Δ }.
Arguments inst_ctx_substE {cf Σ Γ inst s Δ}.
Arguments inst_subsletE {cf Σ Γ inst s Δ}.

(** Copy 15, [PCUICSpine.v:274] [arity_spine]. *)
Inductive arity_spineE {cf : checker_flags} (Σ : global_env_ext) (Γ : context) :
  term -> list term -> term -> Type :=
| arity_spine_nilE ty : arity_spineE Σ Γ ty [] ty
| arity_spine_convE ty ty' : isTypeE Σ Γ ty' ->
  ws_cumul_pbE Cumul Σ Γ ty ty' -> arity_spineE Σ Γ ty [] ty'
| arity_spine_defE : forall (tl : list term)
                      (na : aname) (A a B B' : term),
                    arity_spineE Σ Γ (B {0 := a}) tl B' ->
                    arity_spineE Σ Γ (tLetIn na a A B) tl B'
| arity_spine_assE : forall (hd : term) (tl : list term)
                      (na : aname) (A B B' : term),
                    Σ ;;; Γ |-E hd : A ->
                    arity_spineE Σ Γ (B {0 := hd}) tl B' ->
                    arity_spineE Σ Γ (tProd na A B) (hd :: tl) B'.

(* Base derives it ([PCUICSpine.v:289]); a [Signature] instance is reached by [depelim] and
   [noconf] with no name in the text, so the twin carries it too. *)
Derive Signature for arity_spineE.

(** Copy 15, [PCUICSpine.v:291] [wf_arity_spine]. *)
Record wf_arity_spineE {cf:checker_flags} Σ Γ T args T' :=
{ wf_arity_spine_wfE : isTypeE Σ Γ T;
  wf_arity_spine_spineE : arity_spineE Σ Γ T args T' }.

(** Copy 16, [PCUICInductives.v:623] [wf_subslet]. *)
Record wf_subsletE {cf} Σ Γ s Δ :=
  { wf_subslet_ctxE : wf_localE Σ (Γ ,,, Δ);
    wf_subslet_subsletE :> subsletE Σ Γ s Δ }.

(** ** Copy 15: [PCUICSpine] *)

Definition ctx_inst_cumulE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {pb : conv_pb} {Γ : list context_decl} {i : list term} {Δ Δ' : list context_decl},
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
  ctx_instE Σ Γ i (List.rev Δ) ->
  wf_local_relE Σ Γ Δ ->
  wf_local_relE Σ Γ Δ' ->
  ctx_instE Σ Γ i (List.rev Δ').

Definition ctx_inst_instE_statement : Type :=
  forall {cf : checker_flags} (Σ : global_env_ext) (ext : universes_decl) (u : Instance.t)
    (Γ : context) (i : list term) (Δ : context),
  PCUICUnivSubstitutionTypEta.wf_global_extE Σ.1 ext ->
  ctx_instE (Σ.1, ext) Γ i Δ ->
  consistent_instance_ext Σ ext u ->
  ctx_instE Σ Γ@[u] (map (subst_instance u) i) Δ@[u].

Definition ctx_inst_open_termsE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    (Γ : context) (args : list term) (Δ : context),
  ctx_instE Σ Γ args Δ ->
  All (fun t : term => is_open_term Γ t) args.

Definition ctx_inst_spine_substE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ : list context_decl} {args : list term},
  wf_localE Σ (Γ ,,, Δ) ->
  forall ci : ctx_instE Σ Γ args (List.rev Δ),
  spine_substE Σ Γ args (ctx_inst_subE ci) Δ.

Definition inversion_mkApps_directE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {f : term} {u : list term} {T : term},
  isTypeE Σ Γ T ->
  Σ ;;; Γ |-E mkApps f u : T ->
  ∑ (A : term) (s' : sort),
    (Σ ;;; Γ |-E f : A) × (Σ ;;; Γ |-E A : tSort s') × typing_spineE Σ Γ A u T.

Definition spine_subst_appE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : list context_decl} {Δ : context}
    {Δ' : list context_decl} {inst inst' insts : list term},
  #|inst| = context_assumptions Δ ->
  wf_localE Σ (Γ ,,, Δ ,,, Δ') ->
  spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ ->
  spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') ->
  spine_substE Σ Γ (inst ++ inst') insts (Δ ,,, Δ').

Definition spine_subst_app_invE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ : context} {Δ' : list context_decl} {inst inst' insts : list term},
  #|inst| = context_assumptions Δ ->
  spine_substE Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ->
  spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ ×
  spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ').

Definition spine_subst_ctx_instE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ Δ : context} {args s : list term},
  spine_substE Σ Γ args s Δ ->
  ctx_instE Σ Γ args (List.rev Δ).

Definition spine_subst_cumulE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Δ : list context_decl} {args : list term} {Γ Γ' : context},
  assumption_context Γ -> assumption_context Γ' ->
  wf_localE Σ (Δ ,,, Γ) ->
  wf_localE Σ (Δ ,,, Γ') ->
  ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' ->
  spine_substE Σ Δ args (List.rev args) Γ ->
  spine_substE Σ Δ args (List.rev args) Γ'.

Definition spine_subst_inj_substE_statement : Prop :=
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {inst s s' : list term} {Δ : context},
  spine_substE Σ Γ inst s Δ ->
  spine_substE Σ Γ inst s' Δ ->
  s = s'.

Definition spine_subst_smashE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {inst s : list term} {Δ : context},
  spine_substE Σ Γ inst s Δ ->
  spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ).

Definition spine_subst_subst_to_extended_list_kE_statement : Prop :=
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {args s : list term} {Δ : context},
  spine_substE Σ Γ args s Δ ->
  map (subst0 s) (to_extended_list_k Δ 0) = args.

Definition subslet_skipnE_statement : Type :=
  forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (s : list term) (Δ : context) (n : nat),
  subsletE Σ Γ s Δ ->
  subsletE Σ Γ (skipn n s) (skipn n Δ).

(** NOT TWIN (ADDED ClosedBodies), closedbodies-register row 1: the binder
    [{wfΣ : ClosedBodies Σ}] is not in base [PCUICSpine.type_mkApps]; [typeE_Cumul] needs
    [cumulSpecE], and [ws_cumul_pbE_forget_spec] gives it only under [ClosedBodies Σ]. Its SR
    consumers ([PCUICSR.v:2101, 2545, 2937], all in [sr_red1]) hold [wfΣ : wf Σ.1] through
    [env_prop]. *)
Definition type_mkAppsE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ}
    {Γ : context} {t : term} {u : list term} {T t_ty : term},
  Σ ;;; Γ |-E t : t_ty ->
  typing_spineE Σ Γ t_ty u T ->
  Σ ;;; Γ |-E mkApps t u : T.

Definition typing_spine_invE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ : context} {T : term} {args args' : list term} {T' : term},
  #|args| = context_assumptions Δ ->
  typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
  ∑ args_sub : list term,
    spine_substE Σ Γ args args_sub Δ × typing_spineE Σ Γ (subst0 args_sub T) args' T'.

Definition typing_spine_nth_errorE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ : context} {T : term} {args : list term} {n : nat} {arg concl : term},
  typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args concl ->
  nth_error args n = Some arg ->
  n < context_assumptions Δ ->
  ∑ decl : context_decl,
    (nth_error (smash_context [] Δ) (context_assumptions Δ - S n) = Some decl) ×
    (Σ ;;; Γ |-E arg : subst0 (List.rev (firstn n args)) (decl_type decl)).

Definition typing_spine_strengthenE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {T : term} {args : list term} {U : term},
  typing_spineE Σ Γ T args U ->
  forall T' : term,
  isTypeE Σ Γ T' ->
  ws_cumul_pbE Cumul Σ Γ T' T ->
  typing_spineE Σ Γ T' args U.

Definition wf_local_alphaE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    (Γ Γ' : list context_decl),
  eq_context_upto_names Γ Γ' ->
  wf_localE Σ Γ ->
  wf_localE Σ Γ'.

Definition ws_cumul_ctx_pb_eq_leE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {pb : conv_pb} {Γ Δ : context},
  ws_cumul_ctx_pbE Conv Σ Γ Δ ->
  ws_cumul_ctx_pbE pb Σ Γ Δ.

Definition ws_cumul_ctx_pb_rel_smashE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {pb : conv_pb} {Γ Δ Δ' : list context_decl},
  wf_localE Σ (Γ ,,, Δ) ->
  wf_localE Σ (Γ ,,, Δ') ->
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
  ws_cumul_ctx_pbE_rel pb Σ Γ (smash_context [] Δ) (smash_context [] Δ').

Definition ws_cumul_ctx_pb_rel_transE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {pb : conv_pb} {Γ Δ Δ' Δ'' : list context_decl},
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ' Δ'' ->
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ''.

Definition ws_cumul_pb_expand_lets_ws_cumul_ctxE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {pb le' : conv_pb} {Γ Δ Δ' : list context_decl} {T T' : term},
  wf_localE Σ (Γ ,,, Δ) ->
  wf_localE Σ (Γ ,,, Δ') ->
  ws_cumul_pbE le' Σ (Γ ,,, Δ) T T' ->
  ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
  ws_cumul_pbE le' Σ (Γ ,,, smash_context [] Δ) (expand_lets Δ T) (expand_lets Δ' T').

(** C1 addition for EtaMetaLane's T2a ([PCUICSpine.v:415]). *)
Definition wf_arity_spine_typing_spineE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {T : term} {args : list term} {T' : term},
  wf_arity_spineE Σ Γ T args T' ->
  typing_spineE Σ Γ T args T'.

(** C1 addition for EtaMetaLane's T2a ([PCUICSpine.v:782]). *)
Definition spine_subst_smash_app_invE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ : context} {Δ' : list context_decl} {δ δ' : list term},
  #|δ| = context_assumptions Δ ->
  spine_substE Σ Γ (δ ++ δ') (List.rev (δ ++ δ')) (smash_context [] (Δ ,,, Δ')) ->
  spine_substE Σ Γ δ (List.rev δ) (smash_context [] Δ) ×
  spine_substE Σ Γ δ' (List.rev δ')
    (subst_context_let_expand (List.rev δ) Δ (smash_context [] Δ')).

(** ** Copy 16: [PCUICInductives] *)

(** TWIN. Not named in [PCUICSR]'s text: base declares [#[global] Hint Resolve isType_intro :
    pcuic] ([PCUICInductives.v:288-289]) and SR's [pcuic]/[pcuics] tactics search that
    database, so copy 16 must re-register [isType_introE] in [pcuic]. *)
Definition isType_introE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {T : term} {s : sort},
  Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.

Definition declared_projection_type_and_eqE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {mdecl : mutual_inductive_body}
    {idecl : one_inductive_body} {p : projection} {cdecl : constructor_body} {pdecl : projection_body}
    (wfΣ : wfE Σ.1) (Hdecl : declared_projection Σ p mdecl idecl cdecl pdecl),
  let u := abstract_instance (ind_universes mdecl) in
  (ind_ctors idecl = [cdecl] ×
   isTypeE (Σ.1, ind_universes mdecl)
     (vass {| binder_name := nNamed (ind_name idecl); binder_relevance := ind_relevance idecl |}
        (mkApps (tInd (proj_ind p) u) (to_extended_list (smash_context [] (ind_params mdecl)))) ::
      smash_context [] (ind_params mdecl)) (proj_type pdecl)) ×
  (∑ decl : context_decl,
    [× nth_error (smash_context [] (cstr_args cdecl))
         (context_assumptions (cstr_args cdecl) - S (proj_arg p)) = Some decl,
       isTypeE (Σ.1, ind_universes mdecl)
         (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,,
          skipn (context_assumptions (cstr_args cdecl) - proj_arg p) (smash_context [] (cstr_args cdecl)))
         (decl_type decl),
       wf_localE (Σ.1, ind_universes mdecl)
         (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, smash_context [] (cstr_args cdecl)),
       projection_type mdecl (proj_ind p) (proj_arg p) (decl_type decl) = proj_type pdecl &
       projection_type mdecl (proj_ind p) (proj_arg p) (decl_type decl) =
       projection_type' mdecl (proj_ind p) (proj_arg p) (decl_type decl)]).

Definition instantiate_indsE_statement : Prop :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1}
    {u : Instance.t} {mind : kername} {mdecl : mutual_inductive_body},
  declared_minductive Σ.1 mind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (inds mind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl))@[u] =
  inds mind u (ind_bodies mdecl).

Definition isType_mkApps_IndE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body}
    (decli : declared_inductive Σ ind mdecl idecl)
    {Γ : context} {puinst : Instance.t} {args inst : list term},
  consistent_instance_ext Σ (ind_universes mdecl) puinst ->
  spine_substE Σ Γ args inst (ind_params mdecl ,,, ind_indices idecl)@[puinst] ->
  Σ ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst].

Definition isType_mkApps_Ind_invE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {ind : inductive} {u : Instance.t}
    {args : list term} (wfΣ : wfE Σ.1)
    {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    (declm : declared_inductive Σ.1 ind mdecl idecl),
  wf_localE Σ Γ ->
  isTypeE Σ Γ (mkApps (tInd ind u) args) ->
  ∑ parsubst argsubst : list term,
    let parctx := (ind_params mdecl)@[u] in
    let argctx := subst_context parsubst 0 (ind_indices idecl)@[u] in
    [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
       spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
       #|firstn (ind_npars mdecl) args| = ind_npars mdecl,
       #|skipn (ind_npars mdecl) args| = context_assumptions (ind_indices idecl) &
       consistent_instance_ext Σ (ind_universes mdecl) u].

Definition map_subst_let_expand_to_extended_listE_statement : Prop :=
  forall {cf : checker_flags} {Σ : global_env_ext} {s : list term} {Γ Δ : context},
  spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
  map (subst_let_expand (List.rev s) Δ) (to_extended_list Δ) = s.

Definition on_minductive_wf_params_indices_instE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body}
    (decli : declared_inductive Σ ind mdecl idecl) (u : Instance.t),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ ((ind_params mdecl ,,, ind_indices idecl)@[u]).

Definition red_it_mkProd_or_LetIn_smashE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    (Γ : list context_decl) (ctx : context) (t u : term) (n : nat) (c : context_decl),
  Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u ->
  nth_error (List.rev (smash_context [] ctx)) n = Some c ->
  ∑ (ctx' : context) (t' : term) (d : context_decl),
    [× decompose_prod_assum [] u = (ctx', t'),
       nth_error (List.rev (smash_context [] ctx')) n = Some d &
       Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d].

Definition typing_expand_lets_genE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ Γ' : list context_decl} {t T : term},
  Σ ;;; Γ ,,, Δ ,,, Γ' |-E t : T ->
  Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' |-E
    expand_lets_k Δ #|Γ'| t : expand_lets_k Δ #|Γ'| T.

Definition wf_local_expand_letsE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ Δ Γ' : list context_decl},
  wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
  wf_localE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ').

(** C1 addition for EtaMetaLane's T2a ([PCUICInductives.v:2697]). Route: its base proof
    reaches [type_it_mkProd_or_LetIn_inv], whose raw-form site goes through
    [ws_cumul_pbE_LetIn_l_inv] (t0-plan.md:168). *)
Definition isType_case_predicateE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {ci : case_info}
    {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    (u : Instance.t) (params : list term) (ps : sort),
  wf_localE Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_substE Σ Γ params (List.rev params) (smash_context [] (subst_instance u (ind_params mdecl))) ->
  isTypeE Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps)).

(** C1 addition for EtaMetaLane's T2a ([PCUICInductives.v:2803]). *)
Definition arity_spine_case_predicateE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {ci : case_info}
    {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {u : Instance.t} {params indices : list term} {ps : sort} {c : term},
  wf_localE Σ Γ ->
  declared_inductive Σ ci mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_sort Σ ps ->
  spine_substE Σ Γ params (List.rev params)
    (smash_context [] (subst_instance u (ind_params mdecl))) ->
  spine_substE Σ Γ indices (List.rev indices)
    (subst_context_let_expand (List.rev params)
        (subst_instance u (ind_params mdecl))
        (smash_context [] (subst_instance u (ind_indices idecl)))) ->
  Σ ;;; Γ |-E c : mkApps (tInd ci u) (params ++ indices) ->
  arity_spineE Σ Γ
    (it_mkProd_or_LetIn
      (pre_case_predicate_context_gen ci mdecl idecl params u)
      (tSort ps))
    (indices ++ [c]) (tSort ps).

(** ** Copy 17: [PCUICFixWitness]

  [PCUICSR] uses only the class [ShapeCheck] (in its own [mfix_on_ind_red1_body], [:82]) and its
  field [shape_check_dbody] ([:95]), which mention no typing: base, no statement. *)

(** ** Copy 18: [PCUICInductiveInversion]

  [on_constructor_wf_args] ([PCUICInductiveInversion.v:267]) IS used, qualified, at
  [PCUICSR.v:2397] ([PCUICInductiveInversion.on_constructor_wf_args]); EtaMetaLane closes that
  site in its E SR with its own [on_constructor_wf_arities_pars_argsE]; no statement here. *)

(** TWIN. The universe clause comes over E from [ws_cumul_pbE_Ind_l_inv]
    ([cmp_global_instance_finst] := [cmp_global_instance_eta], [PCUICEtaFInst.v:284]); napp
    here is the full arity [head_arity Σ (IndRef i)], so [finst_ind_glue_full]
    ([PCUICEtaFInstGlue.v:37]) turns it into base [cmp_global_instance], i.e.
    [cmp_ind_universes]. *)
Definition Construct_Ind_ind_eqE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} (wfΣ : wfE Σ.1)
    {Γ : context} {n : nat} {i : inductive} {args : list term} {u : Instance.t}
    {i' : inductive} {args' : list term} {u' : Instance.t} {mdecl : mutual_inductive_body}
    {idecl : one_inductive_body} {cdecl : constructor_body},
  Σ ;;; Γ |-E mkApps (tConstruct i n u) args : mkApps (tInd i' u') args' ->
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  ((((i = i' × cmp_ind_universes Σ i (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u') ×
     consistent_instance_ext Σ (ind_universes mdecl) u) ×
    consistent_instance_ext Σ (ind_universes mdecl) u') ×
   #|args| = ind_npars mdecl + context_assumptions (cstr_args cdecl)) ×
  (∑ parsubst argsubst parsubst' argsubst' : list term,
    let parctx := (ind_params mdecl)@[u] in
    let parctx' := (ind_params mdecl)@[u'] in
    let argctx := subst_context parsubst 0
      (subst_context (inds (inductive_mind i) u (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)@[u]) in
    let argctx2 := subst_context parsubst' 0
      (subst_context (inds (inductive_mind i) u' (ind_bodies mdecl)) #|ind_params mdecl| (cstr_args cdecl)@[u']) in
    let argctx' := subst_context parsubst' 0 (ind_indices idecl)@[u'] in
    [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
       spine_substE Σ Γ (firstn (ind_npars mdecl) args') parsubst' parctx',
       spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
       spine_substE Σ Γ (skipn (ind_npars mdecl) args') argsubst' argctx' &
       ∑ s : list sort,
         sorts_local_ctx (lift_typing typingE) Σ Γ argctx2 s ×
         ws_cumul_pbE_terms Σ Γ (firstn (ind_npars mdecl) args) (firstn (ind_npars mdecl) args') ×
         ws_cumul_pbE_terms Σ Γ
           (map (subst0 (argsubst ++ parsubst) ∘
                 subst (inds (inductive_mind i) u (ind_bodies mdecl)) (#|cstr_args cdecl| + #|ind_params mdecl|) ∘
                 subst_instance u) (cstr_indices cdecl))
           (skipn (ind_npars mdecl) args')]).

Definition cmp_global_instance_ind_invE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    (cmp_universe : conv_pb -> Relation_Definitions.relation Universe.t) (pb : conv_pb)
    (ind : inductive) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (napp : nat)
    (u u' : Instance.t),
  RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
  declared_inductive Σ ind mdecl idecl ->
  cmp_global_instance Σ cmp_universe pb (IndRef ind) napp u u' ->
  ((context_assumptions (ind_indices idecl) + context_assumptions (ind_params mdecl) <= napp ×
    (∑ l : list Variance.t, ind_variance mdecl = Some l × cmp_universe_instance_variance cmp_universe pb l u u')) +
   cmp_universe_instance (cmp_universe Conv) u u')%type.

Definition constructor_cumulative_indicesE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {c : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {cdecl : constructor_body} {u u' : Instance.t} {napp : nat},
  declared_constructor Σ c mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ c.1 napp u u' ->
  forall (Γ : context) (pars pars' parsubst parsubst' : list term),
  spine_substE Σ Γ pars parsubst (ind_params mdecl)@[u] ->
  spine_substE Σ Γ pars' parsubst' (ind_params mdecl)@[u'] ->
  ws_cumul_pbE_terms Σ Γ pars pars' ->
  let argctx := subst_context (ind_subst mdecl c.1 u) #|ind_params mdecl| (cstr_args cdecl)@[u] in
  let argctx' := subst_context (ind_subst mdecl c.1 u') #|ind_params mdecl| (cstr_args cdecl)@[u'] in
  let pargctx := subst_context parsubst 0 argctx in
  let pargctx' := subst_context parsubst' 0 argctx' in
  ws_cumul_ctx_pbE_rel Cumul Σ Γ (smash_context [] pargctx) (smash_context [] pargctx') ×
  ws_cumul_pbE_terms Σ (Γ ,,, smash_context [] pargctx)
    (map (subst parsubst (context_assumptions (cstr_args cdecl)))
       (map (expand_lets argctx) (map (subst_instance u) (cstr_indices cdecl))))
    (map (subst parsubst' (context_assumptions (cstr_args cdecl)))
       (map (expand_lets argctx') (map (subst_instance u') (cstr_indices cdecl)))).

Definition conv_decls_fix_contextE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {mfix mfix1 : list (def term)},
  wf_localE Σ Γ ->
  All2 (fun d d' : def term =>
          ws_cumul_pbE Conv Σ Γ (dtype d) (dtype d') × eq_binder_annot (dname d) (dname d'))
    mfix mfix1 ->
  All2_fold (fun Δ _ : context => decl_ws_cumul_pbE Σ (Γ ,,, Δ)) (fix_context mfix) (fix_context mfix1).

Definition declared_constructor_valid_tyE_statement : Type :=
  forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mdecl : mutual_inductive_body)
    (idecl : one_inductive_body) (i : inductive) (n : nat) (cdecl : constructor_body) (u : Instance.t),
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeE Σ Γ (type_of_constructor mdecl cdecl (i, n) u).

Definition into_ws_cumul_pb_termsE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : list context_decl} {l l' : list term},
  All2 (convSpecE Σ Γ) l l' ->
  is_closed_context Γ ->
  forallb (is_open_term Γ) l ->
  forallb (is_open_term Γ) l' ->
  ws_cumul_pbE_terms Σ Γ l l'.

(** Same proposition as [Typing/PCUICClosedTypEta.isType_is_open_termE] (twin of the
    homonym [Typing/PCUICClosedTyp.isType_is_open_term]) except that [Γ T] are explicit. *)
Definition isType_is_open_termE_statement : Prop :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    (Γ : context) (T : term),
  isTypeE Σ Γ T ->
  is_open_term Γ T.

Definition on_constructor_instE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {ind : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {cdecl : constructor_body}
    (declc : declared_constructor Σ ind mdecl idecl cdecl) (u : Instance.t),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ ((arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)@[u]) ×
  (∑ inst : list term,
    spine_substE Σ ((arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)@[u])
      (map (subst_instance u) (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
       map (subst_instance u) (cstr_indices cdecl))
      inst ((ind_params mdecl)@[u] ,,, (ind_indices idecl)@[u])).

Definition on_constructor_inst_wf_argsE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {ind : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {cdecl : constructor_body}
    (declc : declared_constructor Σ ind mdecl idecl cdecl) (u : Instance.t),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ ((ind_params mdecl)@[u] ,,,
    subst_context (ind_subst mdecl ind.1 u) #|ind_params mdecl| (cstr_args cdecl)@[u]).

Definition positive_cstr_closed_indicesE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {i : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {cdecl : constructor_body},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (fun t : term => closedn (context_assumptions (cstr_args cdecl) + #|ind_params mdecl|) t)
    (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)).

Definition pre_case_branch_context_eqE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
    {params : list term} {puinst : Instance.t} {bctx : list aname} {cdecl : constructor_body},
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) puinst ->
  wf_branch_gen cdecl bctx ->
  eq_context_upto_names
    (pre_case_branch_context ind mdecl params puinst cdecl)
    (case_branch_context_gen ind mdecl params puinst bctx cdecl).

Definition subslet_projsE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {i : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {args : list term},
  declared_inductive Σ.1 i mdecl idecl ->
  match ind_ctors idecl return Type with
  | [cs] =>
    on_projections mdecl (inductive_mind i) (inductive_ind i) idecl (ind_indices idecl) cs ->
    forall (Γ : context) (t : term) (u : Instance.t),
    let indsubst := inds (inductive_mind i) u (ind_bodies mdecl) in
    Σ ;;; Γ |-E t : mkApps (tInd i u) args ->
    wf_subsletE Σ Γ (projs_inst i (ind_npars mdecl) (context_assumptions (cstr_args cs)) t)
      (subst_context (List.rev args) 0
        (subst_context (extended_subst (ind_params mdecl)@[u] 0) 0
          (smash_context []
            (subst_context (inds (inductive_mind i) u (ind_bodies mdecl))
              #|ind_params mdecl| (cstr_args cs)@[u]))))
  | _ => True
  end.

Definition type_tCoFix_invE_statement : Type :=
  forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mfix : mfixpoint term) (idx : nat) (T : term),
  wfE Σ ->
  Σ ;;; Γ |-E tCoFix mfix idx : T ->
  ∑ d : def term,
    ((nth_error mfix idx = Some d × wf_cofixpointE Σ Γ mfix) ×
     (Σ ;;; Γ |-E subst0 (cofix_subst mfix) (dbody d) : dtype d)) ×
    ws_cumul_pbE Cumul Σ Γ (dtype d) T.

Definition type_tFix_invE_statement : Type :=
  forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mfix : mfixpoint term) (idx : nat) (T : term),
  wfE Σ ->
  Σ ;;; Γ |-E tFix mfix idx : T ->
  ∑ (T' : term) (rarg : nat) (f : term),
    ((unfold_fix mfix idx = Some (rarg, f) × wf_fixpointE Σ Γ mfix) × (Σ ;;; Γ |-E f : T')) ×
    ws_cumul_pbE Cumul Σ Γ T' T.

Definition wf_case_branches_types'E_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info}
    {p : predicate term} (ps : sort) (args : list term) (brs : list (branch term)),
  declared_inductive Σ ci mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  wf_branches idecl brs ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  All2i (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
    let cstr_br_ctx := case_branch_context_nopars ci mdecl p.(puinst) cdecl in
    let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    [× wf_branch cdecl br,
       wf_localE Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, cstr_br_ctx),
       wf_localE Σ (Γ ,,, (ind_params mdecl)@[puinst p] ,,, brctx'),
       wf_localE Σ (Γ ,,, brctxty.1) &
       Σ ;;; Γ ,,, brctxty.1 |-E brctxty.2 : tSort ps])
    0 (ind_ctors idecl) brs.

Definition wf_case_predicate_contextE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info}
    {p : predicate term} {args : list term},
  declared_inductive Σ ci.(ci_ind) mdecl idecl ->
  isTypeE Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  wf_localE Σ (Γ ,,, predctx).

(** Route (A) of t0-plan §6 risk 5: twin statement, a proof without [mfix_on_ind_inv]. *)
Definition wf_cofixpoint_typing_spineE_statement : Prop :=
  forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (ind : inductive) (u : Instance.t)
    (mfix : mfixpoint term) (idx : nat) (d : def term) (args args' : list term),
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  wf_cofixpointE Σ Γ mfix ->
  nth_error mfix idx = Some d ->
  isTypeE Σ Γ (dtype d) ->
  typing_spineE Σ Γ (dtype d) args (mkApps (tInd ind u) args') ->
  check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite.

(** C1 addition for EtaMetaLane's T6 (the E copy of [Bidirectional/BDToPCUIC]):
    [PCUICInductiveInversion.v:3794]. Route [INFERENCE]: base's proof reads the universe
    clause of [invert_cumul_ind_ind], false over η below the arity; here [isTypeE] of
    [mkApps (tInd ind u) args] makes [args] the full arity, so [invert_cumul_ind_indE] with
    [finst_ind_glue_full] ([PCUICEtaFInstGlue.v:37]) gives the clause. *)
Definition ctx_inst_app_weakE_statement : Type :=
  forall {H : checker_flags} (Σ : global_env_ext) (wfΣ : wfE Σ.1) (ind : inductive)
    (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
    (isdecl : declared_inductive Σ.1 ind mdecl idecl) (Γ : context) (wfΓ : wf_localE Σ Γ)
    (params args : list term) (u v : Instance.t),
  isTypeE Σ Γ (mkApps (tInd ind u) args) ->
  consistent_instance_ext Σ (ind_universes mdecl) v ->
  ctx_instE Σ Γ params (List.rev (subst_instance v (ind_params mdecl))) ->
  ws_cumul_pbE Cumul Σ Γ (mkApps (tInd ind u) args)
    (mkApps (tInd ind v) (params ++ skipn (ind_npars mdecl) args)) ->
  ctx_instE Σ Γ (params ++ skipn (ind_npars mdecl) args)
    (List.rev (subst_instance v (ind_params mdecl ,,, ind_indices idecl))).

(** C1 addition for EtaMetaLane's T6 (the E copy of [Bidirectional/BDFromPCUIC]):
    [PCUICInductiveInversion.v:3616]. Its base proof inverts only its own universe premise
    ([cmp_global_instance_ind_inv]), builds cumulativity in the constructing direction
    ([into_ws_cumul_pb], [cumul_ctx_relSpec_Algo]) and reads the declaration's variance clause
    ([on_ctype_variance]); the presumed-false class enters only through
    [positive_cstr_closed_args], whose closure holds the risk-5 rows of copy 18 (see the
    note). *)
Definition projection_cumulative_indicesE_statement : Type :=
  forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
    {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {cdecl : constructor_body}
    {p : projection} {pdecl : projection_body} {u u' : Instance.t},
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  on_udecl_prop Σ (ind_universes mdecl) ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  consistent_instance_ext Σ (ind_universes mdecl) u' ->
  cmp_ind_universes Σ p.(proj_ind) (ind_npars mdecl) u u' ->
  ws_cumul_pbE Cumul Σ (projection_context p.(proj_ind) mdecl idecl u)
    (subst_instance u pdecl.(proj_type)) (subst_instance u' pdecl.(proj_type)).
