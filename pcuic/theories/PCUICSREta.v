(* Distributed under the terms of the MIT license. *)

(** * Subject reduction over [typingE] (row T1): the E copy of [PCUICSR]

  HEADER: see the end of this comment block for the forecast structure. *)

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
     PCUICSigmaCalculus PCUICPrimitiveRed PCUICOnFreeVars PCUICContextReduction
     PCUICSR.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure
     PCUICTypingEta PCUICTypingEtaInd PCUICTypingEtaNotions PCUICClosedBodies
     PCUICClosedTypEta PCUICWeakeningEnvTypEta PCUICWeakeningTypEta PCUICCasesWfTypEta
     PCUICGuardClosureEta PCUICWfUniversesEta
     PCUICEtaI5 PCUICEtaI5A2 PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICWsCumulEtaSubst PCUICEtaA6 PCUICEtaA6Ind PCUICEtaA6More PCUICEtaJoinSpec PCUICEtaFInstGlue
     PCUICContextConversionEta PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp
     PCUICInversionEta PCUICSREtaConv.
From MetaRocq.PCUIC.Typing Require PCUICUnivSubstitutionTypEta.
From MetaRocq.PCUIC Require PCUICGenerationEta.

From Stdlib Require Import ssreflect ssrbool Utf8.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From Equations.Prop Require Import DepElim.
Local Set SimplIsCbn.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Ltac rename_hyp h ht ::= my_rename_hyp h ht.

Arguments Nat.sub : simpl nomatch.
Arguments Sort.sort_of_product : simpl nomatch.

Local Notation " Σ ;;; Γ ⊢E t ≤[ pb ] u " := (ws_cumul_pbE pb Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤[ pb ]  u") : type_scope.
Local Notation " Σ ;;; Γ ⊢E t ≤ u " := (ws_cumul_pbE Cumul Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  ≤  u") : type_scope.
Local Notation " Σ ;;; Γ ⊢E t = u " := (ws_cumul_pbE Conv Σ Γ t u) (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢E  t  =  u") : type_scope.

(** ** FORECAST BLOCK

  Every fact below is a FORECAST: an E copy that is not on this branch will prove it, under exactly
  this name and with exactly this statement. Landing a row is: delete its part of this block (the
  definitions and the class of that row, and the [Context] line of that class in section [SREta]),
  import the copy. No proof below the block changes. Nothing here is an axiom: the classes are
  premises of every lemma that uses them, and [Print Assumptions] shows them as such. *)

(* The braces in the statements record base's implicit status; Rocq honours them on the class
   projections. *)
Local Set Warnings "-unexpected-implicit-declaration".

(** *** Definitions *)

(* FORECAST-ONLY: proved by copy 10 (PCUICSubstitutionEta.v, twin of PCUICSubstitution.v:45 subslet);
   delete when it lands. Text: the statement note's forecast stand-in, verbatim. *)
Inductive subsletE {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptysletE : subsletE Σ Γ [] []
| cons_let_assE Δ s na t T : subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E t : subst0 s T ->
    subsletE Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_defE Δ s na t T :
    subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E subst0 s t : subst0 s T ->
    subsletE Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).

(* FORECAST-ONLY: proved by copy 14 (PCUICAritiesEta.v, twin of PCUICArities.v:44 typing_spine, the
   ARITIES one); delete when it lands. Text: the statement note's forecast stand-in, verbatim. *)
Inductive typing_spineE {cf} Σ (Γ : context) : term -> list term -> term -> Type :=
| type_spine_nilE ty ty' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ ty' ->
    ws_cumul_pbE Cumul Σ Γ ty ty' ->
    typing_spineE Σ Γ ty [] ty'
| type_spine_consE ty hd tl na A B B' :
    isTypeE Σ Γ ty ->
    isTypeE Σ Γ (tProd na A B) ->
    ws_cumul_pbE Cumul Σ Γ ty (tProd na A B) ->
    Σ ;;; Γ |-E hd : A ->
    typing_spineE Σ Γ (subst10 hd B) tl B' ->
    typing_spineE Σ Γ ty (hd :: tl) B'.

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v, twin of PCUICSpine.v:903 ctx_inst_sub); delete
   when it lands. Text: PCUICSREtaCopyStatements.v, verbatim. *)
Fixpoint ctx_inst_subE {cf : checker_flags} {Σ : global_env_ext} {Γ Δ args}
  (c : ctx_instE Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | PCUICTyping.ctx_inst_nil => []
  | PCUICTyping.ctx_inst_ass na t i inst Δ P c => ctx_inst_subE c ++ [i]
  | PCUICTyping.ctx_inst_def na b t inst Δ c => ctx_inst_subE c ++ [b]
  end.

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v, twin of PCUICSpine.v:226 spine_subst); delete
   when it lands. Text: PCUICSREtaCopyStatements.v, verbatim. *)
Record spine_substE {cf : checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubstE {
  spine_dom_wfE : wf_localE Σ Γ;
  spine_codom_wfE : wf_localE Σ (Γ ,,, Δ);
  inst_ctx_substE :> context_subst Δ inst s;
  inst_subsletE :> subsletE Σ Γ s Δ }.
Arguments inst_ctx_substE {cf Σ Γ inst s Δ}.
Arguments inst_subsletE {cf Σ Γ inst s Δ}.

(* FORECAST-ONLY: proved by copy 16 (PCUICInductivesEta.v, twin of PCUICInductives.v:623 wf_subslet);
   delete when it lands. Text: PCUICSREtaCopyStatements.v, verbatim. *)
Record wf_subsletE {cf} Σ Γ s Δ :=
  { wf_subslet_ctxE : wf_localE Σ (Γ ,,, Δ);
    wf_subslet_subsletE :> subsletE Σ Γ s Δ }.

(* FORECAST-ONLY: proved by copy 18 (PCUICInductiveInversionEta.v, twin of the notation
   PCUICInductiveInversion.v:856 decl_ws_cumul_pb); delete when it lands. Text:
   PCUICSREtaCopyStatements.v, verbatim. *)
Notation decl_ws_cumul_pbE Σ Γ :=
  (All_decls_alpha_pb Conv (fun pb (x0 y0 : term) => ws_cumul_pbE pb Σ Γ x0 y0)).

(** *** T2a: the twins of the [PCUICValidity] lemmas that [PCUICSR] uses

  No statement note covers T2a. Each field is the exact twin of its base lemma (relation renamed,
  nothing else); together they are the T2a writer's contract. *)

(* FORECAST-ONLY: proved by T2a (PCUICValidityEta.v); delete when it lands. *)
Class SRForecastT2a := {
  (* twin of PCUICValidity.v:356 validity *)
  validityE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T},
    Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T ;
  (* twin of PCUICValidity.v:381 inversion_mkApps (typing_spine = the PCUICArities one) *)
  inversion_mkAppsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ f u T},
    Σ ;;; Γ |-E mkApps f u : T ->
    ∑ A, Σ ;;; Γ |-E f : A × typing_spineE Σ Γ A u T
}.

(** *** Copy 9 ([Typing/PCUICContextConversionTypEta.v]): the statements of
    [wip/eta-e3-copy9-2026-10-29] @ [d46f9387], which are the twins of base. *)

(* FORECAST-ONLY: proved by copy 9 (Typing/PCUICContextConversionTypEta.v); delete when it lands. *)
Class SRForecastCopy9 := {
  (* twin of Typing/PCUICContextConversionTyp.v:400 closed_context_conversion *)
  closed_context_conversionE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} Γ {t T Γ'},
    Σ ;;; Γ |-E t : T ->
    wf_localE Σ Γ' ->
    ws_cumul_ctx_pbE Conv Σ Γ Γ' ->
    Σ ;;; Γ' |-E t : T ;
  (* twin of Typing/PCUICContextConversionTyp.v:387 context_conversion; base [cumulAlgo_gen] →
     [JoinE] *)
  context_conversionE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1} Γ {t T Γ'},
    Σ ;;; Γ |-E t : T ->
    wf_localE Σ Γ' ->
    conv_context (@JoinE cf) Σ Γ Γ' ->
    Σ ;;; Γ' |-E t : T
}.

(** *** Copy 10 ([PCUICSubstitutionEta.v]): twins of base [PCUICSubstitution]. The statement note
    gives names only; each statement is base's (file:line) with the relations renamed. *)

(* FORECAST-ONLY: proved by copy 10 (PCUICSubstitutionEta.v); delete when it lands. *)
Class SRForecastCopy10 := {
  (* PCUICSubstitution.v:1824 isType_substitution *)
  isType_substitutionE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ T},
    subsletE Σ Γ s Γ' ->
    isTypeE Σ (Γ ,,, Γ' ,,, Δ) T ->
    isTypeE Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T) ;
  (* PCUICSubstitution.v:1306 isType_wf_local *)
  isType_wf_localE :
    forall {cf:checker_flags} {Σ : global_env_ext} {Γ T},
    isTypeE Σ Γ T -> wf_localE Σ Γ ;
  (* PCUICSubstitution.v:66 subslet_ass_tip *)
  subslet_ass_tipE :
    forall {cf} {Σ : global_env_ext} {Γ na t T},
    Σ ;;; Γ |-E t : T ->
    subsletE Σ Γ [t] [vass na T] ;
  (* PCUICSubstitution.v:57 subslet_def *)
  subslet_defE :
    forall {cf} {Σ : global_env_ext} {Γ Δ s na t T t'},
    subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E subst0 s t : subst0 s T ->
    t' = subst0 s t ->
    subsletE Σ Γ (t' :: s) (Δ ,, vdef na t T) ;
  (* PCUICSubstitution.v:108 subslet_length *)
  subslet_lengthE :
    forall {cf:checker_flags} {Σ : global_env_ext} {Γ s Δ},
    subsletE Σ Γ s Δ -> #|s| = #|Δ| ;
  (* PCUICSubstitution.v:829 subslet_untyped_subslet *)
  subslet_untyped_subsletE :
    forall {cf:checker_flags} (Σ : global_env_ext) Γ s Γ',
    subsletE Σ Γ s Γ' -> untyped_subslet Γ s Γ' ;
  (* PCUICSubstitution.v:1795 substitution *)
  substitutionE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ t T},
    subsletE Σ Γ s Γ' ->
    Σ ;;; Γ ,,, Γ' ,,, Δ |-E t : T ->
    Σ ;;; Γ ,,, subst_context s 0 Δ |-E subst s #|Δ| t : subst s #|Δ| T ;
  (* PCUICSubstitution.v:1865 substitution0 *)
  substitution0E :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ n u U t T},
    Σ ;;; Γ ,, vass n U |-E t : T -> Σ ;;; Γ |-E u : U ->
    Σ ;;; Γ |-E t {0 := u} : T {0 := u} ;
  (* PCUICSubstitution.v:1876 substitution_let *)
  substitution_letE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ n u U t T},
    Σ ;;; Γ ,, vdef n u U |-E t : T ->
    Σ ;;; Γ |-E t {0 := u} : T {0 := u} ;
  (* PCUICSubstitution.v:1856 substitution_wf_local *)
  substitution_wf_localE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ},
    subsletE Σ Γ s Γ' ->
    wf_localE Σ (Γ ,,, Γ' ,,, Δ) ->
    wf_localE Σ (Γ ,,, subst_context s 0 Δ) ;
  (* PCUICSubstitution.v:576 wf_arities_context *)
  wf_arities_contextE :
    forall {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} {mind mdecl},
    declared_minductive Σ mind mdecl ->
    wf_localE (Σ, ind_universes mdecl) (arities_context mdecl.(ind_bodies))
}.

(** *** Copy 12 ([PCUICContextsEta.v]): twins of base [PCUICContexts]; names only in the note. *)

(* FORECAST-ONLY: proved by copy 12 (PCUICContextsEta.v); delete when it lands. *)
Class SRForecastCopy12 := {
  (* PCUICContexts.v:133 sorts_local_ctx_wf_local *)
  sorts_local_ctx_wf_localE :
    forall {cf:checker_flags} (Σ : global_env_ext) Γ Δ s,
    wf_localE Σ Γ ->
    sorts_local_ctx (lift_typing typingE) Σ Γ Δ s ->
    wf_localE Σ (Γ ,,, Δ) ;
  (* PCUICContexts.v:591 subslet_lift *)
  subslet_liftE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} (Γ Δ : context) s Δ',
    wf_localE Σ (Γ ,,, Δ) ->
    subsletE Σ Γ s Δ' ->
    subsletE Σ (Γ ,,, Δ) (map (lift0 #|Δ|) s) (lift_context #|Δ| 0 Δ') ;
  (* PCUICContexts.v:682 typing_expand_lets *)
  typing_expand_letsE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ t T,
    Σ ;;; Γ ,,, Δ |-E t : T ->
    Σ ;;; Γ ,,, smash_context [] Δ |-E expand_lets Δ t : expand_lets Δ T ;
  (* PCUICContexts.v:370 wf_local_smash_end (section WfEnv: {cf} {Σ} {wfΣ : wf Σ}) *)
  wf_local_smash_endE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ Δ,
    wf_localE Σ (Γ ,,, Δ) -> wf_localE Σ (Γ ,,, smash_context [] Δ)
}.

(** *** Copy 14 ([PCUICAritiesEta.v]): twins of base [PCUICArities] (section [WfEnv]:
    [{cf} {Σ : global_env_ext} {wfΣ : wf Σ}]); names only in the note. *)

(* FORECAST-ONLY: proved by copy 14 (PCUICAritiesEta.v); delete when it lands. *)
Class SRForecastCopy14 := {
  (* PCUICArities.v:228 type_ws_cumul_pb. NOT TWIN (ADDED ClosedBodies): closedbodies-register row
     2; base has no environment premise ([Proof using Type]). Same place as in the note's
     [type_mkAppsE]. *)
  type_ws_cumul_pbE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ} {pb Γ t} T {U},
    Σ ;;; Γ |-E t : T ->
    isTypeE Σ Γ U ->
    ws_cumul_pbE pb Σ Γ T U ->
    Σ ;;; Γ |-E t : U ;
  (* PCUICArities.v:213 isType_tProd *)
  isType_tProdE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {na A B},
    isTypeE Σ Γ (tProd na A B) <~>
    (isTypeRelE Σ Γ A na.(binder_relevance) × isTypeE Σ (Γ,, vass na A) B) ;
  (* PCUICArities.v:633 on_minductive_wf_params *)
  on_minductive_wf_paramsE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind mdecl} {u},
    declared_minductive Σ.1 ind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ (subst_instance u (ind_params mdecl)) ;
  (* PCUICArities.v:527 subslet_inds *)
  subslet_indsE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind u mdecl idecl},
    declared_inductive Σ.1 ind mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subsletE Σ [] (inds (inductive_mind ind) u (ind_bodies mdecl))
      (subst_instance u (arities_context (ind_bodies mdecl))) ;
  (* PCUICArities.v:126 ws_cumul_ctx_pb_app *)
  ws_cumul_ctx_pb_appE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {le Γ Γ' Δ Δ'},
    #|Δ| = #|Δ'| ->
    ws_cumul_ctx_pbE le Σ (Γ ,,, Δ) (Γ' ,,, Δ') <~>
    ws_cumul_ctx_pbE le Σ Γ Γ' × ws_cumul_ctx_pbE_rel le Σ Γ Δ Δ'
}.

(** *** Copy 15 ([PCUICSpineEta.v]): the statement note's statements, verbatim
    ([PCUICSREtaCopyStatements.v] @ [c232bd3d], [<base>E_statement] → field [<base>E]). *)

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v); delete when it lands. *)
Class SRForecastCopy15 := {
  ctx_inst_cumulE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {pb : conv_pb} {Γ : list context_decl} {i : list term} {Δ Δ' : list context_decl},
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ctx_instE Σ Γ i (List.rev Δ) ->
    wf_local_relE Σ Γ Δ ->
    wf_local_relE Σ Γ Δ' ->
    ctx_instE Σ Γ i (List.rev Δ') ;
  ctx_inst_instE :
    forall {cf : checker_flags} (Σ : global_env_ext) (ext : universes_decl) (u : Instance.t)
      (Γ : context) (i : list term) (Δ : context),
    PCUICUnivSubstitutionTypEta.wf_global_extE Σ.1 ext ->
    ctx_instE (Σ.1, ext) Γ i Δ ->
    consistent_instance_ext Σ ext u ->
    ctx_instE Σ Γ@[u] (map (subst_instance u) i) Δ@[u] ;
  ctx_inst_open_termsE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall (Γ : context) (args : list term) (Δ : context),
    ctx_instE Σ Γ args Δ ->
    All (fun t : term => is_open_term Γ t) args ;
  ctx_inst_spine_substE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ : list context_decl} {args : list term},
    wf_localE Σ (Γ ,,, Δ) ->
    forall ci : ctx_instE Σ Γ args (List.rev Δ),
    spine_substE Σ Γ args (ctx_inst_subE ci) Δ ;
  inversion_mkApps_directE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {f : term} {u : list term} {T : term},
    isTypeE Σ Γ T ->
    Σ ;;; Γ |-E mkApps f u : T ->
    ∑ (A : term) (s' : sort),
      (Σ ;;; Γ |-E f : A) × (Σ ;;; Γ |-E A : tSort s') × typing_spineE Σ Γ A u T ;
  spine_subst_appE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : list context_decl} {Δ : context}
      {Δ' : list context_decl} {inst inst' insts : list term},
    #|inst| = context_assumptions Δ ->
    wf_localE Σ (Γ ,,, Δ ,,, Δ') ->
    spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ ->
    spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') ->
    spine_substE Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ;
  spine_subst_app_invE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ : context} {Δ' : list context_decl} {inst inst' insts : list term},
    #|inst| = context_assumptions Δ ->
    spine_substE Σ Γ (inst ++ inst') insts (Δ ,,, Δ') ->
    spine_substE Σ Γ inst (skipn #|Δ'| insts) Δ ×
    spine_substE Σ Γ inst' (firstn #|Δ'| insts) (subst_context (skipn #|Δ'| insts) 0 Δ') ;
  spine_subst_ctx_instE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ Δ : context} {args s : list term},
    spine_substE Σ Γ args s Δ ->
    ctx_instE Σ Γ args (List.rev Δ) ;
  spine_subst_cumulE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Δ : list context_decl} {args : list term} {Γ Γ' : context},
    assumption_context Γ -> assumption_context Γ' ->
    wf_localE Σ (Δ ,,, Γ) ->
    wf_localE Σ (Δ ,,, Γ') ->
    ws_cumul_ctx_pbE_rel Cumul Σ Δ Γ Γ' ->
    spine_substE Σ Δ args (List.rev args) Γ ->
    spine_substE Σ Δ args (List.rev args) Γ' ;
  spine_subst_inj_substE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {inst s s' : list term} {Δ : context},
    spine_substE Σ Γ inst s Δ ->
    spine_substE Σ Γ inst s' Δ ->
    s = s' ;
  spine_subst_smashE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {inst s : list term} {Δ : context},
    spine_substE Σ Γ inst s Δ ->
    spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ) ;
  spine_subst_subst_to_extended_list_kE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {args s : list term} {Δ : context},
    spine_substE Σ Γ args s Δ ->
    map (subst0 s) (to_extended_list_k Δ 0) = args ;
  subslet_skipnE :
    forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (s : list term) (Δ : context) (n : nat),
    subsletE Σ Γ s Δ ->
    subsletE Σ Γ (skipn n s) (skipn n Δ) ;
  (* NOT TWIN (ADDED ClosedBodies), closedbodies-register row 1, as in the note. *)
  type_mkAppsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ},
    forall {Γ : context} {t : term} {u : list term} {T t_ty : term},
    Σ ;;; Γ |-E t : t_ty ->
    typing_spineE Σ Γ t_ty u T ->
    Σ ;;; Γ |-E mkApps t u : T ;
  typing_spine_invE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ : context} {T : term} {args args' : list term} {T' : term},
    #|args| = context_assumptions Δ ->
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) (args ++ args') T' ->
    ∑ args_sub : list term,
      spine_substE Σ Γ args args_sub Δ × typing_spineE Σ Γ (subst0 args_sub T) args' T' ;
  typing_spine_nth_errorE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ : context} {T : term} {args : list term} {n : nat} {arg concl : term},
    typing_spineE Σ Γ (it_mkProd_or_LetIn Δ T) args concl ->
    nth_error args n = Some arg ->
    n < context_assumptions Δ ->
    ∑ decl : context_decl,
      (nth_error (smash_context [] Δ) (context_assumptions Δ - S n) = Some decl) ×
      (Σ ;;; Γ |-E arg : subst0 (List.rev (firstn n args)) (decl_type decl)) ;
  typing_spine_strengthenE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {T : term} {args : list term} {U : term},
    typing_spineE Σ Γ T args U ->
    forall T' : term,
    isTypeE Σ Γ T' ->
    ws_cumul_pbE Cumul Σ Γ T' T ->
    typing_spineE Σ Γ T' args U ;
  wf_local_alphaE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall Γ Γ' : list context_decl,
    eq_context_upto_names Γ Γ' ->
    wf_localE Σ Γ ->
    wf_localE Σ Γ' ;
  ws_cumul_ctx_pb_eq_leE :
    forall {cf : checker_flags} {Σ : global_env_ext} {pb : conv_pb} {Γ Δ : context},
    ws_cumul_ctx_pbE Conv Σ Γ Δ ->
    ws_cumul_ctx_pbE pb Σ Γ Δ ;
  ws_cumul_ctx_pb_rel_smashE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {pb : conv_pb} {Γ Δ Δ' : list context_decl},
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ (smash_context [] Δ) (smash_context [] Δ') ;
  ws_cumul_ctx_pb_rel_transE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {pb : conv_pb} {Γ Δ Δ' Δ'' : list context_decl},
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ' Δ'' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ'' ;
  ws_cumul_pb_expand_lets_ws_cumul_ctxE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {pb le' : conv_pb} {Γ Δ Δ' : list context_decl} {T T' : term},
    wf_localE Σ (Γ ,,, Δ) ->
    wf_localE Σ (Γ ,,, Δ') ->
    ws_cumul_pbE le' Σ (Γ ,,, Δ) T T' ->
    ws_cumul_ctx_pbE_rel pb Σ Γ Δ Δ' ->
    ws_cumul_pbE le' Σ (Γ ,,, smash_context [] Δ) (expand_lets Δ T) (expand_lets Δ' T')
}.

(** *** Copy 16 ([PCUICInductivesEta.v]): the statement note's statements, verbatim. *)

(* FORECAST-ONLY: proved by copy 16 (PCUICInductivesEta.v); delete when it lands. *)
Class SRForecastCopy16 := {
  declared_projection_type_and_eqE :
    forall {cf : checker_flags} {Σ : global_env_ext} {mdecl : mutual_inductive_body}
      {idecl : one_inductive_body} {p : projection} {cdecl : constructor_body} {pdecl : projection_body},
    wfE Σ.1 ->
    declared_projection Σ p mdecl idecl cdecl pdecl ->
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
         projection_type' mdecl (proj_ind p) (proj_arg p) (decl_type decl)]) ;
  instantiate_indsE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ.1 ->
    forall {u : Instance.t} {mind : kername} {mdecl : mutual_inductive_body},
    declared_minductive Σ.1 mind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    (inds mind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl))@[u] =
    inds mind u (ind_bodies mdecl) ;
  isType_mkApps_IndE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body},
    declared_inductive Σ ind mdecl idecl ->
    forall {Γ : context} {puinst : Instance.t} {args inst : list term},
    consistent_instance_ext Σ (ind_universes mdecl) puinst ->
    spine_substE Σ Γ args inst (ind_params mdecl ,,, ind_indices idecl)@[puinst] ->
    Σ ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst] ;
  isType_mkApps_Ind_invE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {ind : inductive} {u : Instance.t}
      {args : list term},
    wfE Σ.1 ->
    forall {mdecl : mutual_inductive_body} {idecl : one_inductive_body},
    declared_inductive Σ.1 ind mdecl idecl ->
    wf_localE Σ Γ ->
    isTypeE Σ Γ (mkApps (tInd ind u) args) ->
    ∑ parsubst argsubst : list term,
      let parctx := (ind_params mdecl)@[u] in
      let argctx := subst_context parsubst 0 (ind_indices idecl)@[u] in
      [× spine_substE Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx,
         spine_substE Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx,
         #|firstn (ind_npars mdecl) args| = ind_npars mdecl,
         #|skipn (ind_npars mdecl) args| = context_assumptions (ind_indices idecl) &
         consistent_instance_ext Σ (ind_universes mdecl) u] ;
  map_subst_let_expand_to_extended_listE :
    forall {cf : checker_flags} {Σ : global_env_ext} {s : list term} {Γ Δ : context},
    spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
    map (subst_let_expand (List.rev s) Δ) (to_extended_list Δ) = s ;
  on_minductive_wf_params_indices_instE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body},
    declared_inductive Σ ind mdecl idecl ->
    forall u : Instance.t,
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ ((ind_params mdecl ,,, ind_indices idecl)@[u]) ;
  red_it_mkProd_or_LetIn_smashE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall (Γ : list context_decl) (ctx : context) (t u : term) (n : nat) (c : context_decl),
    Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u ->
    nth_error (List.rev (smash_context [] ctx)) n = Some c ->
    ∑ (ctx' : context) (t' : term) (d : context_decl),
      [× decompose_prod_assum [] u = (ctx', t'),
         nth_error (List.rev (smash_context [] ctx')) n = Some d &
         Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d] ;
  typing_expand_lets_genE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ Γ' : list context_decl} {t T : term},
    Σ ;;; Γ ,,, Δ ,,, Γ' |-E t : T ->
    Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' |-E
      expand_lets_k Δ #|Γ'| t : expand_lets_k Δ #|Γ'| T ;
  wf_local_expand_letsE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ Γ' : list context_decl},
    wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
    wf_localE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ')
}.

(** *** Copy 18 ([PCUICInductiveInversionEta.v]): the statement note's statements, verbatim. *)

(* FORECAST-ONLY: proved by copy 18 (PCUICInductiveInversionEta.v); delete when it lands. *)
Class SRForecastCopy18 := {
  Construct_Ind_ind_eqE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ.1 ->
    forall {Γ : context} {n : nat} {i : inductive} {args : list term} {u : Instance.t}
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
             (skipn (ind_npars mdecl) args')]) ;
  cmp_global_instance_ind_invE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall (cmp_universe : conv_pb -> Relation_Definitions.relation Universe.t) (pb : conv_pb)
      (ind : inductive) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (napp : nat)
      (u u' : Instance.t),
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    declared_inductive Σ ind mdecl idecl ->
    cmp_global_instance Σ cmp_universe pb (IndRef ind) napp u u' ->
    ((context_assumptions (ind_indices idecl) + context_assumptions (ind_params mdecl) <= napp ×
      (∑ l : list Variance.t, ind_variance mdecl = Some l × cmp_universe_instance_variance cmp_universe pb l u u')) +
     cmp_universe_instance (cmp_universe Conv) u u')%type ;
  constructor_cumulative_indicesE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {c : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
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
         (map (expand_lets argctx') (map (subst_instance u') (cstr_indices cdecl)))) ;
  conv_decls_fix_contextE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {mfix mfix1 : list (def term)},
    wf_localE Σ Γ ->
    All2 (fun d d' : def term =>
            ws_cumul_pbE Conv Σ Γ (dtype d) (dtype d') × eq_binder_annot (dname d) (dname d'))
      mfix mfix1 ->
    All2_fold (fun Δ _ : context => decl_ws_cumul_pbE Σ (Γ ,,, Δ)) (fix_context mfix) (fix_context mfix1) ;
  declared_constructor_valid_tyE :
    forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mdecl : mutual_inductive_body)
      (idecl : one_inductive_body) (i : inductive) (n : nat) (cdecl : constructor_body) (u : Instance.t),
    wfE Σ.1 ->
    wf_localE Σ Γ ->
    declared_constructor Σ.1 (i, n) mdecl idecl cdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    isTypeE Σ Γ (type_of_constructor mdecl cdecl (i, n) u) ;
  into_ws_cumul_pb_termsE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : list context_decl} {l l' : list term},
    All2 (convSpecE Σ Γ) l l' ->
    is_closed_context Γ ->
    forallb (is_open_term Γ) l ->
    forallb (is_open_term Γ) l' ->
    ws_cumul_pbE_terms Σ Γ l l' ;
  (* Same proposition as [Typing/PCUICClosedTypEta.isType_is_open_termE] (implicit [Γ T]); this
     field shadows that name here, as the copy-18 lemma will. *)
  isType_is_open_termE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall (Γ : context) (T : term),
    isTypeE Σ Γ T ->
    is_open_term Γ T ;
  on_constructor_instE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {ind : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {cdecl : constructor_body},
    declared_constructor Σ ind mdecl idecl cdecl ->
    forall u : Instance.t,
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ ((arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)@[u]) ×
    (∑ inst : list term,
      spine_substE Σ ((arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)@[u])
        (map (subst_instance u) (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl|) ++
         map (subst_instance u) (cstr_indices cdecl))
        inst ((ind_params mdecl)@[u] ,,, (ind_indices idecl)@[u])) ;
  on_constructor_inst_wf_argsE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {ind : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {cdecl : constructor_body},
    declared_constructor Σ ind mdecl idecl cdecl ->
    forall u : Instance.t,
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ ((ind_params mdecl)@[u] ,,,
      subst_context (ind_subst mdecl ind.1 u) #|ind_params mdecl| (cstr_args cdecl)@[u]) ;
  positive_cstr_closed_indicesE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {i : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {cdecl : constructor_body},
    declared_constructor Σ.1 i mdecl idecl cdecl ->
    All (fun t : term => closedn (context_assumptions (cstr_args cdecl) + #|ind_params mdecl|) t)
      (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)) ;
  pre_case_branch_context_eqE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {params : list term} {puinst : Instance.t} {bctx : list aname} {cdecl : constructor_body},
    declared_inductive Σ ind mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) puinst ->
    wf_branch_gen cdecl bctx ->
    eq_context_upto_names
      (pre_case_branch_context ind mdecl params puinst cdecl)
      (case_branch_context_gen ind mdecl params puinst bctx cdecl) ;
  subslet_projsE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {i : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {args : list term},
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
    end ;
  type_tCoFix_invE :
    forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mfix : mfixpoint term) (idx : nat) (T : term),
    wfE Σ ->
    Σ ;;; Γ |-E tCoFix mfix idx : T ->
    ∑ d : def term,
      ((nth_error mfix idx = Some d × wf_cofixpointE Σ Γ mfix) ×
       (Σ ;;; Γ |-E subst0 (cofix_subst mfix) (dbody d) : dtype d)) ×
      ws_cumul_pbE Cumul Σ Γ (dtype d) T ;
  type_tFix_invE :
    forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (mfix : mfixpoint term) (idx : nat) (T : term),
    wfE Σ ->
    Σ ;;; Γ |-E tFix mfix idx : T ->
    ∑ (T' : term) (rarg : nat) (f : term),
      ((unfold_fix mfix idx = Some (rarg, f) × wf_fixpointE Σ Γ mfix) × (Σ ;;; Γ |-E f : T')) ×
      ws_cumul_pbE Cumul Σ Γ T' T ;
  wf_case_branches_types'E :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info}
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
      0 (ind_ctors idecl) brs ;
  wf_case_predicate_contextE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info}
      {p : predicate term} {args : list term},
    declared_inductive Σ ci.(ci_ind) mdecl idecl ->
    isTypeE Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
    wf_predicate mdecl idecl p ->
    let predctx := case_predicate_context ci mdecl idecl p in
    wf_localE Σ (Γ ,,, predctx) ;
  (* Route (A) of t0-plan §6 risk 5: twin statement, a proof without [mfix_on_ind_inv]. *)
  wf_cofixpoint_typing_spineE :
    forall {cf : checker_flags} (Σ : global_env_ext) (Γ : context) (ind : inductive) (u : Instance.t)
      (mfix : mfixpoint term) (idx : nat) (d : def term) (args args' : list term),
    wfE Σ.1 ->
    wf_localE Σ Γ ->
    wf_cofixpointE Σ Γ mfix ->
    nth_error mfix idx = Some d ->
    isTypeE Σ Γ (dtype d) ->
    typing_spineE Σ Γ (dtype d) args (mkApps (tInd ind u) args') ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite
}.

Local Set Warnings "unexpected-implicit-declaration".

(** ** End of the FORECAST BLOCK *)

Section SREta.

(* FORECAST-ONLY: one premise per row of the block above; delete each line when its row lands. *)
Context {FT2a : SRForecastT2a} {F9 : SRForecastCopy9} {F10 : SRForecastCopy10}
  {F12 : SRForecastCopy12} {F14 : SRForecastCopy14} {F15 : SRForecastCopy15}
  {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}.

(** ** Probe: the forecast fields resolve, with their implicit arguments *)

Lemma sr_probe_validity {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T} :
  Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T.
Proof. intros h. exact (validityE h). Qed.

Lemma sr_probe_type_ws_cumul_pb {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T U} :
  Σ ;;; Γ |-E t : T -> isTypeE Σ Γ U -> Σ ;;; Γ ⊢E T ≤ U -> Σ ;;; Γ |-E t : U.
Proof. intros h hU c. exact (type_ws_cumul_pbE T h hU c). Qed.

Lemma sr_probe_spine {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ T args U T'} :
  typing_spineE Σ Γ T args U -> isTypeE Σ Γ T' -> Σ ;;; Γ ⊢E T' ≤ T -> typing_spineE Σ Γ T' args U.
Proof. intros sp hT c. exact (typing_spine_strengthenE wfΣ sp T' hT c). Qed.

End SREta.
