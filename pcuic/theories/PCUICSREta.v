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
(* FORECAST-ONLY (with [subsletE]): base derives it for [subslet]; the checker forecast's [subsletE]
   has it too. *)
Derive Signature for subsletE.

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
(* FORECAST-ONLY (with [typing_spineE]): base derives it for [PCUICArities.typing_spine]. *)
Derive Signature for typing_spineE.

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

(* FORECAST-ONLY: canonical home PCUICTypingEtaNotions.v (cross-lane-commitments.md C2, EtaCheckerLane's
   map); delete when it lands. Text: safechecker/theories/PCUICTypingEtaDefs.v @ 26749b27:75-80,
   verbatim. The E forms of [PCUICTyping.has_sort_isType]/[has_sort_isTypeRel]. *)
Definition has_sort_isTypeE {cf Σ} {Γ T} s : Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof. repeat (eexists; tea). Defined.

Definition has_sort_isTypeRelE {cf Σ} {Γ T} s r :
  isSortRel s r -> Σ ;;; Γ |-E T : tSort s -> isTypeRelE Σ Γ T r.
Proof. repeat (eexists; tea). Defined.

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
  (* note @ 0583b56e: twin of PCUICInductives.v:284; base SR uses it only through the [pcuic]
     hint database, so it is registered as a local [pcuic] hint in section [SREta]. *)
  isType_introE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {T : term} {s : sort},
    Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T ;
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

(* FORECAST-ONLY: the [pcuic] hints that the copies re-register for their E lemmas (note @ 0583b56e:
   copy 16 [isType_introE]; copy 15 the coercion fields of [spine_substE]; copy 18
   [isType_is_open_termE]); delete with their rows. *)
#[local] Hint Resolve isType_introE : pcuic.
#[local] Hint Resolve inst_ctx_substE inst_subsletE : pcuic.
#[local] Hint Resolve isType_is_open_termE : pcuic.

(** The E counterparts of base's [typing]-specific [pcuic] hints that SR's [pcuic]/[pcuics]
    searches use ([PCUICTyping.has_sort_isType], [typing_wf_local]). *)
#[local] Hint Resolve has_sort_isTypeE typingE_wf_local : pcuic.

(** ** Helpers of [PCUICSR.v] before [sr_red1]

  Lines are base lines of [PCUICSR.v] at [d8120081]. Purely syntactic helpers are base's (this file
  imports [PCUICSR]); the E twins of [red_has_rec_arg], [mfix_body_on_red_type],
  [mfix_on_ind_red1_type], [conv_context_rel_reln], [conv_context_rel_to_extended_list],
  [eq_context_alpha_conv], [conv_ctx_set_binder_name], [red_one_decl_red_ctx],
  [into_closed_red_ctx], [red_one_decl_red_context], [red_one_decl_ws_cumul_ctx_pb],
  [wt_cumul_pb_refl], [ws_cumul_pb_meta_refl], [ws_cumul_pb_eq_trans], [eq_ws_cumul_pb_trans],
  [ws_cumul_pb_terms_eq_trans], [eq_ws_cumul_pb_terms_trans], [wt_terms_ws_cumul_pb],
  [weakening_ws_cumul_ctx_pb], [closed_red1_ws_cumul_pb] and [type_Cumul_alt] are in
  [PCUICSREtaConv]; [ws_cumul_pb_terms_refl]'s is the landed [WT_refl]. *)

(** Base [declared_projection_declared_constructor] ([:123]). *)
Lemma declared_projection_declared_constructorE {cf}
  {Σ} {wfΣ : wfE Σ} {p mdecl mdecl' idecl idecl' pdecl cdecl cdecl'} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  declared_constructor Σ (p.(proj_ind), 0) mdecl' idecl' cdecl' ->
  mdecl = mdecl' /\ idecl = idecl' /\ cdecl = cdecl'.
Proof.
  intros [[] ?] [].
  unshelve eapply declared_inductive_to_gen in H, H2; eauto.
  pose proof (declared_inductive_inj H H2). intuition auto. subst.
  rewrite H0 in H3. congruence.
Qed.

(** Base [conv_context_smash_end] ([:140]). *)
Lemma conv_context_smash_endE {cf Σ} {wfΣ : wfE Σ} (Γ Δ Δ' : context) :
  wf_localE Σ (Γ ,,, Δ) ->
  wf_localE Σ (Γ ,,, Δ') ->
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, Δ) (Γ ,,, Δ') ->
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, smash_context [] Δ) (Γ ,,, smash_context [] Δ').
Proof.
  intros wf wf' cv.
  apply (fst ws_cumul_ctx_pbE_rel_app).
  apply (snd ws_cumul_ctx_pbE_rel_app) in cv.
  eapply ws_cumul_ctx_pb_rel_smashE => //.
Qed.

(** Base [spine_subst_inst_subst] ([:267]). *)
Lemma spine_subst_inst_substE {cf} {Σ} {Γ inst s Δ Δ'} :
  spine_substE Σ Γ inst s Δ ->
  subst_context s 0 Δ' = subst_context (List.rev inst) 0 (expand_lets_ctx Δ Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_kE sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite subst_context_subst_context. len.
  rewrite subst_context_lift_context_cancel. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

(** Base [spine_subst_inst_subst_term] ([:282]). *)
Lemma spine_subst_inst_subst_termE {cf} {Σ} {Γ inst s Δ Δ'} :
  spine_substE Σ Γ inst s Δ ->
  subst s 0 Δ' = subst (List.rev inst) 0 (expand_lets Δ Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_kE sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite distr_subst. len.
  rewrite simpl_subst_k. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

(** Base [spine_subst_inst_subst_k] ([:307]). *)
Lemma spine_subst_inst_subst_kE {cf} {Σ} {Γ inst s Δ k Δ'} :
  spine_substE Σ Γ inst s Δ ->
  subst_context s k Δ' = subst_context (List.rev inst) k (expand_lets_k_ctx Δ k Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_kE sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev.
  rewrite subst_context_subst_context. len.
  rewrite subst_context_lift_context_cancel. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

(** Base [spine_subst_inst_subst_term_k] ([:322]). *)
Lemma spine_subst_inst_subst_term_kE {cf} {Σ} {Γ inst s Δ k Δ'} :
  spine_substE Σ Γ inst s Δ ->
  subst s k Δ' = subst (List.rev inst) k (expand_lets_k Δ k Δ').
Proof.
  intros sp. pose proof (spine_subst_subst_to_extended_list_kE sp).
  rewrite -H.
  rewrite /expand_lets_ctx /expand_lets_k_ctx /=.
  rewrite -map_rev /expand_lets_k.
  rewrite -{2}(Nat.add_0_r k) distr_subst_rec. len.
  rewrite simpl_subst_k. now len.
  f_equal.
  rewrite map_rev. rewrite H.
  apply context_subst_subst_extended_subst. apply sp.
Qed.

(** Base [isType_weaken] ([:337]). *)
Lemma isType_weakenE {cf} {Σ Γ Δ T} {wfΣ : wfE Σ} :
  wf_localE Σ Δ ->
  isTypeE Σ Γ T ->
  isTypeE Σ (Δ ,,, Γ) T.
Proof.
  intros wfΔ HT.
  apply lift_typing_impl with (1 := HT) => ?? Hs.
  eapply weaken_ctxE; tea.
Qed.

(** Base [cmp_global_instance_cstr_irrelevant] ([:349]). *)
Lemma cmp_global_instance_cstr_irrelevantE {cf} {Σ} {wfΣ : wfE Σ} {ci c} {mdecl idecl cdecl u u'} :
  declared_constructor Σ (ci, c) mdecl idecl cdecl ->
  cmp_ind_universes Σ ci (context_assumptions (ind_params mdecl) + #|cstr_indices cdecl|) u u' ->
  cmp_global_instance Σ.1 (compare_universe Σ) Conv (ConstructRef ci c)
    (ind_npars mdecl + context_assumptions (cstr_args cdecl)) u u'.
Proof.
  intros declc.
  pose proof (on_declared_constructorE declc).
  pose proof (on_declared_constructorE declc) as [[onind oib] [ctor_sorts [hnth onc]]].
  intros Hu. pose proof (cmp_global_instance_length _ _ _ _ _ _ _ Hu).
  rewrite /cmp_global_instance_gen /cmp_opt_variance /= /lookup_constructor /lookup_constructor_gen.
  unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
  rewrite (declared_inductive_lookup_gen declc'.p1) (proj2 declc').
  rewrite -(cstr_args_length onc).
  case: leb_spec_Set; try lia.
  move=> _. destruct (ind_variance mdecl) eqn:hv => /=; [lia|].
  eapply cmp_global_instance_ind_invE in Hu; [|exact wfΣ|tc|apply declc.p1].
  destruct Hu as [(_ & l & indv & _) | Hu]; [congruence|exact Hu].
Qed.

(** Base [wf_pre_case_branch_context] ([:369]). *)
Lemma wf_pre_case_branch_contextE {cf} {Σ} {wfΣ : wfE Σ} {Γ ci mdecl idecl p} {br : branch term} {cdecl} :
  declared_inductive Σ ci mdecl idecl ->
  wf_branch_gen cdecl (forget_types (bcontext br)) ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_localE Σ (Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl) ->
  wf_localE Σ (Γ,,, pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
Proof.
  move=> decli wfbr cu wf.
  eapply wf_local_alphaE; tea.
  eapply All2_app. 2:eapply All2_refl; reflexivity.
  eapply All2_symP. tc.
  rewrite /case_branch_context_gen.
  eapply pre_case_branch_context_eqE; eauto.
Qed.

(** Base [conv_refl'] ([:384]): base's algorithmic [Σ ;;; Γ |- x = y] is [JoinE Σ Γ Conv x y]
    (stream lead's ruling, 2026-10-29 09:26Z); base's [wf Σ] is not used. *)
Lemma conv_refl'E {cf} {Σ} {Γ x y} :
  x = y ->
  JoinE Σ Γ Conv x y.
Proof. intros ->. apply JoinE_refl. Qed.

(** Base [on_constructor_wf_args] ([:431]). *)
Lemma on_constructor_wf_argsE {cf} {Σ} {wfΣ : wfE Σ} {ind c mdecl idecl cdecl u} :
  declared_constructor Σ (ind, c) mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  wf_localE Σ (subst_instance u (ind_params mdecl) ,,,
    (subst_context (ind_subst mdecl ind u)) #|ind_params mdecl| (subst_instance u (cstr_args cdecl))).
Proof.
  intros decl cu.
  pose proof (on_constructor_instE wfΣ decl _ cu) as [wf _].
  rewrite !subst_instance_app_ctx in wf.
  rewrite -app_context_assoc -(app_context_nil_l (_ ,,, _)) app_context_assoc in wf.
  eapply substitution_wf_localE in wf; tea.
  2:eapply (subslet_indsE decl cu).
  rewrite app_context_nil_l subst_context_app closed_ctx_subst in wf.
  rewrite closedn_subst_instance_context.
  eapply (declared_inductive_closed_paramsE decl).
  now simpl in wf; len in wf.
Qed.

(** Base instance [conv_context_refl] ([:450]), over [JoinE]. *)
#[global]
Instance conv_context_reflE {cf} Σ : CRelationClasses.Reflexive (All2_fold (conv_decls (@JoinE cf) Σ)).
Proof.
  intros x. induction x as [|[na [b|] ty] x IH]; constructor; auto; constructor; auto;
    apply JoinE_refl.
Qed.

(** Base [red1_it_mkLambda_or_LetIn_ctx] ([:678]). Base's [wf Σ] is not used, so this has none. *)
Lemma red1_it_mkLambda_or_LetIn_ctx_cb {cf} {Σ : global_env_ext} Γ Δ Δ' u :
  OnOne2_local_env (fun Δ : context => on_one_decl (red1 Σ (Γ ,,, Δ))) Δ Δ' ->
  red1 Σ Γ (it_mkLambda_or_LetIn Δ u)
       (it_mkLambda_or_LetIn Δ' u).
Proof.
  induction 1 in u |- *.
  - depelim p; subst; rewrite /it_mkLambda_or_LetIn /=. eapply red1_it_mkLambda_or_LetIn.
    simpl. now constructor.
  - depelim p; subst; rewrite /=; eapply red1_it_mkLambda_or_LetIn.
    destruct s as [[red ->]|[red ->]]; constructor; auto.
  - simpl. apply IHX.
Qed.

(** Base [ctx_inst_merge] ([:709]). *)
Lemma ctx_inst_mergeE {cf} {Σ} {wfΣ : wfE Σ} Γ inst inst' Δ :
  wf_localE Σ (Γ ,,, (List.rev Δ)) ->
  PCUICTyping.ctx_inst
    (fun (Γ : context) (t T : term) =>
    forall u : term, closed_red1 Σ Γ t u -> Σ;;; Γ |-E u : T) Γ inst Δ ->
  ctx_instE Σ Γ inst Δ ->
  OnOne2 (closed_red1 Σ Γ) inst inst' ->
  ctx_instE Σ Γ inst' Δ.
Proof.
  intros wf c.
  induction c in inst', wf |- *; intros ctxi; depelim ctxi; intros o.
  - depelim o.
  - depelim o. constructor. apply t0. auto.
    rewrite -(List.rev_involutive Δ).
    rewrite subst_telescope_subst_context.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    eapply ctx_inst_cumulE; [exact wfΣ| |..].
    2:{ instantiate (1:=subst_context [i] 0 (List.rev Δ)).
        rewrite -subst_telescope_subst_context List.rev_involutive. exact ctxi. }
    apply (snd ws_cumul_ctx_pbE_rel_app).
    eapply conv_cumul_contextE.
    eapply substitution_ws_cumul_ctx_pbE_red_subst.
    now eapply wf_local_closed_contextE in wf.
    pose proof (wf_local_closed_contextE (typingE_wf_local t2)).
    constructor; [|constructor].
    now eapply closed_red1_red.
    repeat constructor.
    specialize (t0 _ c0).
    eapply All_local_env_app_inv, substitution_wf_localE; tea.
    now eapply subslet_ass_tipE.
    eapply All_local_env_app_inv, substitution_wf_localE; tea.
    now eapply subslet_ass_tipE.
    constructor; auto. eapply IHc.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_localE; tea.
    repeat (constructor; tea). rewrite subst_empty; tea.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    exact wf. tas. tas.
  - constructor. eapply IHc; eauto.
    simpl in wf. rewrite - !/(app_context _ _) app_context_assoc in wf.
    rewrite -subst_context_subst_telescope.
    eapply substitution_wf_localE; tea.
    repeat (constructor; tea). eapply subslet_defE. constructor.
    all:rewrite !subst_empty //.
    eapply All_local_env_app_inv in wf as [wf _]. depelim wf. now eapply unlift_TermTyp.
Qed.

(** Base [ctx_inst_merge'] ([:756]). *)
Lemma ctx_inst_merge'E {cf} {Σ} {wfΣ : wfE Σ} Γ inst inst' Δ :
  wf_localE Σ (Γ ,,, Δ) ->
  PCUICTyping.ctx_inst
    (fun (Γ : context) (t T : term) =>
    forall u : term, closed_red1 Σ Γ t u → Σ;;; Γ |-E u : T) Γ inst (List.rev Δ) ->
  ctx_instE Σ Γ inst (List.rev Δ) ->
  OnOne2 (closed_red1 Σ Γ) inst inst' ->
  ctx_instE Σ Γ inst' (List.rev Δ).
Proof.
  intros. eapply ctx_inst_mergeE; try rewrite ?(List.rev_involutive Δ) //; tea.
Qed.

(** Base [SR_red1] ([:784]). *)
Definition SR_red1E {cf} Σ Γ t T :=
  forall u (Hu : closed_red1 Σ Γ t u), Σ ;;; Γ |-E u : T.

Local Notation welltypedE' Σ Γ t := (∑ T, Σ ;;; Γ |-E t : T).
Local Notation welltyped_termsE Σ Γ := (All (fun t => welltypedE' Σ Γ t)).

(** Base [spine_subst_wt_terms] ([:1105]). *)
Lemma spine_subst_wt_termsE {cf} {Σ Γ inst s Δ} : spine_substE Σ Γ inst s Δ ->
  welltyped_termsE Σ Γ inst.
Proof.
  move/spine_subst_ctx_instE.
  induction 1; try constructor; auto.
  now exists t.
Qed.

(** Base [on_constructor_closed_indices] ([:1138]). *)
Lemma on_constructor_closed_indicesE {cf} {Σ} {wfΣ : wfE Σ} :
  forall {i mdecl idecl cdecl},
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  All (is_open_term (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl)) (cstr_indices cdecl).
Proof.
  intros.
  pose proof (on_declared_constructorE H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_impl in X. 2: intros ??; apply unlift_TermTyp.
  now eapply ctx_inst_open_termsE in X.
Qed.

(** Base [on_constructor_wf_arities_pars_args] ([:1150]). *)
Lemma on_constructor_wf_arities_pars_argsE {cf} {Σ} {wfΣ : wfE Σ} {i mdecl idecl cdecl} :
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  wf_localE (Σ.1, ind_universes mdecl) (arities_context (ind_bodies mdecl) ,,, ind_params mdecl ,,, cstr_args cdecl).
Proof.
  move=> H.
  pose proof (on_declared_constructorE H) as [[onmind oib] [cs [hnth onc]]].
  move/on_cargs/sorts_local_ctx_wf_localE: onc => H'.
  apply H'.
  apply weaken_wf_localE; tea.
  eapply (wf_arities_contextE H).
  now apply onParams in onmind.
Qed.

(** Base [on_constructor_closed_indices_inst] ([:1174]). *)
Lemma on_constructor_closed_indices_instE {cf} {Σ} {wfΣ : wfE Σ} {i mdecl idecl cdecl u} :
  declared_constructor Σ.1 i mdecl idecl cdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  All (is_open_term (ind_params mdecl ,,, cstr_args cdecl)@[u])
    (map (subst (inds (inductive_mind (fst i)) u (ind_bodies mdecl))
           (#|cstr_args cdecl| + #|ind_params mdecl|)) (cstr_indices cdecl)@[u]).
Proof.
  intros H cu.
  unshelve epose proof (H' := declared_constructor_to_gen H); eauto.
  pose proof (on_declared_constructorE H) as [[onmind oib] [cs [hnth onc]]].
  pose proof (onc.(on_cindices)).
  eapply ctx_inst_impl in X. 2: intros ??; apply unlift_TermTyp.
  eapply ctx_inst_instE in X; tea.
  eapply ctx_inst_open_termsE in X; [|exact wfΣ].
  eapply All_map, All_impl; tea.
  cbn; intros x clx.
  rewrite -[_ ,,, _]app_context_nil_l -[_ ,,, cstr_args cdecl]app_context_assoc app_context_assoc in clx.
  rewrite !subst_instance_app_ctx in clx.
  eapply (is_open_term_subst (Γ := []) (s:=inds (inductive_mind i.1) u (ind_bodies mdecl))) in clx.
  3:eapply inds_is_open_terms. 3:len.
  rewrite app_context_nil_l subst_context_app in clx.
  rewrite closed_ctx_subst in clx.
  eapply declared_inductive_closed_params_instE.
  unshelve eapply declared_inductive_from_gen; eauto.
  len in clx. len.
  rewrite app_context_nil_l app_context_assoc.
  epose proof (on_constructor_wf_arities_pars_argsE H).
  eapply (PCUICUnivSubstitutionTypEta.wf_local_instantiateE (decl:=InductiveDecl mdecl)) in X0; tea.
  rewrite !subst_instance_app_ctx in X0.
  now eapply wf_local_closed_contextE in X0. apply H'.
  eapply PCUICUnivSubstitutionTypEta.declared_inductive_wf_global_extE; eauto.
  unshelve eapply declared_minductive_from_gen; eauto.
Qed.

(** Base [closed_red1_it_mkLambda_or_LetIn] ([:1264]). Base's [wf Σ] is not used. *)
Lemma closed_red1_it_mkLambda_or_LetIn_cb {cf} {Σ : global_env_ext} {Γ} {Δ t u} :
  Σ ;;; Γ ,,, Δ ⊢ t ⇝1 u -> Σ ;;; Γ ⊢ it_mkLambda_or_LetIn Δ t ⇝1 it_mkLambda_or_LetIn Δ u.
Proof.
  intros [clΓΔ opt r].
  split; eauto with fvs.
  - rewrite on_free_vars_ctx_app in clΓΔ. now move/andP: clΓΔ.
  - rewrite on_free_vars_it_mkLambda_or_LetIn.
    rewrite on_free_vars_ctx_app in clΓΔ. move/andP: clΓΔ => [].
    rewrite shiftnP_add -length_app opt andb_true_r //.
  - now eapply red1_it_mkLambda_or_LetIn.
Qed.

(** Base [closed_red1_mkApps_left] ([:1276]). Base's [wf Σ] is not used. *)
Lemma closed_red1_mkApps_left_cb {cf} {Σ : global_env_ext} {Γ} {t u ts} :
  Σ ;;; Γ ⊢ t ⇝1 u ->
  forallb (is_open_term Γ) ts ->
  Σ ;;; Γ ⊢ mkApps t ts ⇝1 mkApps u ts.
Proof.
  intros r cl.
  split; eauto with fvs.
  - rewrite on_free_vars_mkApps (clrel_src r) //.
  - eapply red1_mkApps_f, r.
Qed.

(** Base [weakening_closed_red1] ([:1287]), under [ClosedBodies Σ]. *)
Lemma weakening_closed_red1_cb {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ Γ' Γ'' : context} {M N} :
  closed_red1 Σ (Γ,,, Γ') M N ->
  is_closed_context (Γ ,,, Γ'') ->
  closed_red1 Σ (Γ,,, Γ'',,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros r cl. split => //.
  apply is_closed_context_lift => //. apply r.
  apply is_open_term_lift, r.
  apply weakening_red1_cb => //. eapply on_free_vars_impl, r => //.
  apply r.
Qed.

(** Base [closed_red1_case_branch_type] ([:1299]), under [ClosedBodies Σ]. *)
Lemma closed_red1_case_branch_type_cb {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ} {ret ret'} {ind mdecl idecl k cdecl br p} :
  let cb := case_branch_type ind mdecl idecl p br ret k cdecl in
  let cb' := case_branch_type ind mdecl idecl p br ret' k cdecl in
  wf_branch cdecl br ->
  is_open_term (Γ ,,, cb.1) cb.2 ->
  is_closed_context (Γ ,,, cb.1) ->
  Σ ;;; Γ ⊢ ret ⇝1 ret' ->
  Σ ;;; Γ ,,, cb.1 ⊢ cb.2 ⇝1 cb'.2.
Proof.
  intros cb cb' wfbr op r.
  split => //.
  eapply closed_red1_mkApps_left_cb => //.
  - relativize #|cstr_args cdecl|; [eapply (weakening_closed_red1_cb (Γ':=[]))|] => //.
    apply (case_branch_context_length_args wfbr).
  - move: op; rewrite on_free_vars_mkApps => /andP[] //.
Qed.

(** Base [inst_case_branch_context_eq] ([:1316]). *)
Lemma inst_case_branch_context_eqE {cf} {Σ} {wfΣ : wfE Σ} {p br} {ind mdecl cdecl} :
  declared_minductive Σ (inductive_mind ind) mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
  eq_context_upto_names br.(bcontext) (cstr_branch_context ind mdecl cdecl) ->
  eq_context_upto_names (inst_case_branch_context p br) (pre_case_branch_context ind mdecl p.(pparams) p.(puinst) cdecl).
Proof.
  intros declm cu eqbr.
  rewrite /inst_case_branch_context /pre_case_branch_context.
  rewrite /inst_case_context.
  eapply alpha_eq_subst_context.
  etransitivity; tea.
  - eapply alpha_eq_subst_instance; tea.
  - rewrite /cstr_branch_context subst_instance_expand_lets_ctx subst_instance_subst_context //.
    rewrite instantiate_indsE //.
    reflexivity.
Qed.

(** Base [declared_projection_indices] ([:1344]). *)
Lemma declared_projection_indicesE {cf} {Σ} {wfΣ : wfE Σ} {p mdecl idecl cdecl pdecl} :
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  #|ind_indices idecl| = 0.
Proof.
  move=> isdecl.
  case: (on_declared_projectionE isdecl) => onind. cbn.
  destruct ind_cunivs as [] => /= // => [] [] [] [] //.
  destruct l as [] => //. intros sorts onprojs hp.
  now destruct onprojs.
Qed.

(** Base [substitution_ws_cumul_pb_subst_conv] ([:1360], the SR-local one). *)
Lemma substitution_ws_cumul_pb_subst_convE {cf} {Σ} {wfΣ : wfE Σ} {le Γ Γ0 Γ1 Δ s s' T U} :
  subsletE Σ Γ s Γ0 ->
  wf_subsletE Σ Γ s' Γ1 ->
  ws_cumul_pbE_terms Σ Γ s s' ->
  Σ;;; Γ ,,, Γ0 ,,, Δ ⊢E T ≤[le] U ->
  Σ;;; Γ ,,, subst_context s 0 Δ ⊢E subst s #|Δ| T ≤[le] subst s' #|Δ| U.
Proof.
  intros subs subs' eq.
  eapply substitution_ws_cumul_pbE_subst_conv; tea.
  * now eapply subslet_untyped_subsletE.
  * eapply subslet_untyped_subsletE, subs'.
  * eapply wf_local_closed_contextE, subs'.
Qed.

(** Base [wf_subslet_skipn] ([:1374]). *)
Lemma wf_subslet_skipnE {cf Σ Γ s Δ n} :
  wf_subsletE Σ Γ s Δ → wf_subsletE Σ Γ (skipn n s) (skipn n Δ).
Proof.
  intros []; split; auto using subslet_skipnE.
  now eapply All_local_env_app_skipn.
Qed.

(** Base [isType_subst_arities] ([:1381]). *)
Lemma isType_subst_aritiesE {cf} {Σ} {wfΣ : wfE Σ} {ind mdecl idecl u} {Γ T} :
  declared_inductive Σ ind mdecl idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isTypeE Σ ((arities_context (ind_bodies mdecl))@[u] ,,, Γ) T ->
  isTypeE Σ (subst_context (ind_subst mdecl ind u) 0 Γ) (subst (ind_subst mdecl ind u) #|Γ| T).
Proof.
  intros isdecl cu.
  rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
  move/(isType_substitutionE (subslet_indsE isdecl cu)).
  rewrite app_context_nil_l //.
Qed.

(** Base [wt_closed_red1] ([:1393]). *)
Lemma wt_closed_red1E {cf} {Σ} {wfΣ : wfE Σ} {Γ T U} :
  welltypedE' Σ Γ T ->
  red1 Σ Γ T U ->
  Σ ;;; Γ ⊢ T ⇝1 U.
Proof.
  intros [ty HT] r.
  split => //.
  eapply wf_local_closed_contextE, typingE_wf_local, HT.
  now eapply subject_is_open_termE in HT.
Qed.

(** Base [isType_expand_lets] ([:1404]). *)
Lemma isType_expand_letsE  {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ T} :
  isTypeE Σ (Γ ,,, Δ) T ->
  isTypeE Σ (smash_context [] Γ ,,, expand_lets_ctx Γ Δ) (expand_lets_k Γ #|Δ| T).
Proof.
  intros (_ & s & Hs & _). eapply has_sort_isTypeE. revert Hs.
  rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
  move/(typing_expand_lets_genE wfΣ); rewrite app_context_nil_l => hs.
  apply hs.
Qed.

(** Base [isType_subst_extended_subst] ([:1414]). *)
Lemma isType_subst_extended_substE {cf} {Σ} {wfΣ : wfE Σ} {Γ Δ T} :
  isTypeE Σ (Γ ,,, Δ) T ->
  isTypeE Σ (smash_context [] Γ ,,, subst_context (extended_subst Γ 0) 0 Δ)
    (subst (extended_subst Γ 0) #|Δ| T).
Proof.
  intros (_ & s & Hs & _). eapply has_sort_isTypeE.
  have wfctx := typingE_wf_local Hs.
  generalize Hs.
  rewrite -[_ ,,, _]app_context_nil_l app_context_assoc.
  move/(typing_expand_lets_genE wfΣ); rewrite app_context_nil_l => hs.
  rewrite /expand_lets_ctx /expand_lets_k_ctx in hs.
  rewrite closed_ctx_lift /= in hs.
  move/(closed_wf_localE wfΣ): wfctx. rewrite closedn_ctx_app => /andP[] //.
  rewrite /expand_lets_k /= in hs.
  rewrite lift_closed in hs. eapply subject_closedE in Hs.
  now len in Hs.
  apply hs.
Qed.

(** Base [isType_mkApps_Ind_proj_inv] ([:1433]). *)
Lemma isType_mkApps_Ind_proj_invE {cf:checker_flags} {Σ Γ p u pars} (wfΣ : wfE Σ.1)
  {mdecl idecl cdecl pdecl} (declm : declared_projection Σ.1 p mdecl idecl cdecl pdecl) :
  isTypeE Σ Γ (mkApps (tInd p.(proj_ind) u) pars) ->
    let parctx := (subst_instance u (ind_params mdecl)) in
    [× spine_substE Σ Γ pars (List.rev pars) (smash_context [] parctx),
       #|pars| = ind_npars mdecl,
       idecl.(ind_indices) = [] &
       consistent_instance_ext Σ (ind_universes mdecl) u].
Proof.
  move=> isTy. generalize isTy. apply isType_wf_localE in isTy.
  move/(isType_mkApps_Ind_invE wfΣ declm isTy) => [parsubst [argsubst [sp sargs hp hargs cu]]].
  generalize (declared_projection_indicesE declm).
  move/length_nil => hindices.
  move: hargs; rewrite hindices /=.
  move/length_nil/skipn_nil_length.
  move/firstn_length_le_inv: hp => hle hge.
  have heq: #|pars| = ind_npars mdecl by lia.
  split => //.
  rewrite -heq in sp.
  rewrite firstn_all in sp.
  now apply: (spine_subst_smashE wfΣ).
Qed.

(** Base [lift_judgment_SR] ([:1465]). *)
Lemma lift_judgment_SRE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ na na' tm tm' ty ty' u :
  lift_typing0 (fun t T : term =>
    Σ ;;; Γ |-E t : T ×
    forall u : term, Σ ;;; Γ ⊢ t ⇝1 u -> Σ;;; Γ |-E u : T)
    (j_decl_s (mkdecl na tm ty) u) ->
  on_one_decl (fun t t' => Σ ;;; Γ ⊢ t ⇝1 t') (mkdecl na tm ty) (mkdecl na' tm' ty') ->
  lift_typing typingE Σ Γ (j_decl_s (mkdecl na' tm' ty') u).
Proof.
  cbn; intros tu Hdecl.
  destruct tm as [tm|], tm' as [tm'|] => //; destruct Hdecl as (<- & h). 1: destruct h as [[h <-] | [h <-]].
  all: apply lift_sorting_it_impl_gen with tu => //= [] [] HT IHT; eauto.
  eapply type_ws_cumul_pbE; tea.
  { eapply lift_sorting_forget_rel, lift_sorting_forget_univ, lift_sorting_it_impl_gen with tu => // Ht. now apply Ht. }
  eapply (red_ws_cumul_pbE (pb:=Cumul)).
  now eapply closed_red1_red.
Qed.

(** Base [case_nondep_predicate_conv] ([:1550]). It needs four SR-local syntactic lemmas
    ([case_predicate_context_vass], [mk_ctx_subst_snoc_ass], [subst0_cons_nondep],
    [on_free_vars_it_mkLambda_or_LetIn]), imported from base [PCUICSR]. *)
Lemma case_nondep_predicate_convE {cf} {Σ} {wfΣ : wfE Σ} {Γ ci mdecl idecl p indices c c' ps} :
  let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  #|indices ++ [c]| = context_assumptions predctx ->
  Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps ->
  on_free_vars (strengthenP 0 1 xpredT) p.(preturn) ->
  forallb (is_open_term Γ) indices ->
  is_open_term Γ c ->
  is_open_term Γ c' ->
  Σ ;;; Γ ⊢E mkApps ptm (indices ++ [c]) = mkApps ptm (indices ++ [c']).
Proof.
  intros predctx ptm hlen pret hnd hidx hc hc'.
  have [na [T [Δ eqΔ]]] : ∑ na T Δ, predctx = vass na T :: Δ.
  { apply case_predicate_context_vass.
    change (0 < context_assumptions predctx). rewrite -hlen length_app /=. lia. }
  have hΔ : context_assumptions Δ = #|indices|.
  { move: hlen. rewrite eqΔ length_app /=. lia. }
  have clΓ : is_closed_context Γ.
  { have wfΓ := typingE_wf_local pret.
    apply All_local_env_app_inv in wfΓ as [wfΓ _].
    now eapply wf_local_closed_contextE. }
  have hptm : is_open_term Γ ptm.
  { eapply subject_is_open_termE, PCUICGenerationEta.type_it_mkLambda_or_LetInE, pret. }
  set (s := mk_ctx_subst Δ indices).
  have r : forall x, is_open_term Γ x ->
    Σ ;;; Γ ⊢ mkApps ptm (indices ++ [x]) ⇝ subst0 (x :: s) (preturn p).
  { intros x hx. rewrite /s -(mk_ctx_subst_snoc_ass na T) // -eqΔ.
    eapply into_closed_red => //.
    - eapply red_betas_typedE; tea. rewrite eqΔ length_app /= hΔ. lia.
    - rewrite on_free_vars_mkApps hptm forallb_app hidx /= hx //. }
  transitivity (subst0 (c :: s) (preturn p)).
  - now eapply red_ws_cumul_pbE, r.
  - rewrite (subst0_cons_nondep c c' s _ hnd). symmetry. now eapply red_ws_cumul_pbE, r.
Qed.

(** Base [typing_spine_prim_arg_types] ([:1591]). *)
Lemma typing_spine_prim_arg_typesE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ r tags res T} {ls : list prim_lit} ty ty' :
  PCUICPrimOpType.prim_arg_types r tags res = Some ty ->
  Σ ;;; Γ ⊢E ty ≤ ty' ->
  #|ls| = #|tags| ->
  typing_spineE Σ Γ ty' (map term_of_lit ls) T ->
  Σ ;;; Γ ⊢E res ≤ T.
Proof.
  induction tags as [|t tags ih] in ls, ty, ty' |- *; intros hty hle hlen hsp.
  - destruct ls => //. cbn in hty. noconf hty.
    depelim hsp. etransitivity; tea.
  - destruct ls as [|l ls] => //. cbn in hty, hlen.
    destruct (PCUICPrimOpType.prim_tag_type r t) as [a|] eqn:ht => //.
    destruct (PCUICPrimOpType.prim_arg_types r tags res) as [rest|] eqn:hrest => //.
    cbn in hty. noconf hty.
    depelim hsp.
    assert (hP : Σ ;;; Γ ⊢E tImpl a rest ≤ tProd na A B) by (etransitivity; tea).
    unfold tImpl in hP.
    eapply ws_cumul_pbE_Prod_Prod_inv in hP as [_ _ hcod].
    eapply substitution0_ws_cumul_pbE in hcod; [|exact (subject_is_open_termE t0)].
    unfold subst1 in hcod. rewrite simpl_subst_k in hcod; [reflexivity|].
    eapply ih.
    4: exact hsp.
    1: reflexivity.
    1: exact hcod.
    lia.
Qed.

(** Base [readback_typed] ([:1652]). *)
Lemma readback_typedE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ s r v res} :
  wf_localE Σ Γ ->
  PCUICPrimOpType.prim_shape_type Σ.1.(retroknowledge) s = Some res ->
  on_prim_op_result Σ s ->
  readback Σ s r = Some v ->
  Σ ;;; Γ |-E v : res.
Proof.
  intros wfΓ hsh hres hrb.
  destruct s, r; cbn in hrb, hsh, hres => //.
  - noconf hrb.
    destruct hres as (kn & d & [hpc hd hinv]).
    unfold PCUICPrimOpType.prim_tag_type, EnvironmentTyping.retro_type_constant in hsh.
    pose proof hpc as hpc'. cbn in hpc'. rewrite hpc' in hsh. cbn in hsh. noconf hsh.
    eapply (typeE_Prim Σ Γ (prim_int i) kn d); tea.
    constructor.
  - destruct (Retroknowledge.retro_bool _) as [ind|] eqn:hb => //.
    noconf hrb. cbn in hsh. noconf hsh.
    destruct hres as (i & mdecl & idecl & hpb & hdi).
    assert (e : Some i = Some ind) by exact (eq_trans (eq_sym hpb) hb). noconf e.
    pose proof hdi as [hmind hnth].
    unshelve epose proof (hl := declared_minductive_to_gen hmind); eauto.
    destruct (lookup_on_global_env_prim wfΣ hl) as (Σ' & [_ _ hretro hpd]).
    cbn in hpd. specialize (hpd ind). forward hpd.
    { exact (eq_trans (f_equal Retroknowledge.retro_bool hretro) hb). }
    specialize (hpd eq_refl).
    unfold on_prim_bool_decl in hpd.
    destruct (ind_bodies mdecl) as [|idecl0 []] eqn:hbodies => //.
    destruct hpd as [_ _ huniv _ hctors].
    destruct (inductive_ind ind) as [|n] eqn:hii; cbn in hnth; [noconf hnth|now destruct n].
    destruct (ind_ctors idecl) as [|cT [|cF []]] eqn:hct => //.
    destruct hctors as [hT hF].
    assert (hctor : forall j cdecl, nth_error (ind_ctors idecl) j = Some cdecl ->
      cstr_type cdecl = tRel 0 -> Σ ;;; Γ |-E tConstruct ind j [] : tInd ind []).
    { intros j cdecl hj hty.
      assert (h := typeE_Construct Σ Γ ind j [] mdecl idecl cdecl wfΓ).
      forward h by (split; tea).
      forward h by (unfold consistent_instance_ext, consistent_instance; now rewrite huniv).
      enough (e : type_of_constructor mdecl cdecl (ind, j) [] = tInd ind []) by now rewrite e in h.
      unfold type_of_constructor. rewrite hty hbodies. cbn.
      destruct ind as [mind ii]. cbn in hii. now subst ii. }
    destruct b.
    + eapply (hctor 0 cT); [now rewrite hct|apply hT].
    + eapply (hctor 1 cF); [now rewrite hct|apply hF].
Qed.

(** Base [prim_op_head_type] ([:1702]). Under [wfE] the registering declaration's conversion is
    [cumulSpecE0]; it moves to [Σ], the instance and the context by [weakening_env_convSpecE],
    [convSpecE_subst_instance] (P2), and enters [ws_cumul_pbE] by I5's [into_ws_cumul_pbE_spec]
    in place of base [cumulSpec_cumulAlgo]. *)
Lemma prim_op_head_typeE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ c u decl op A} :
  wf_localE Σ Γ ->
  declared_constant Σ c decl ->
  consistent_instance_ext Σ (cst_universes decl) u ->
  prim_op_of Σ c = Some op ->
  Σ ;;; Γ ⊢E (cst_type decl)@[u] ≤ A ->
  ∑ res Tp,
    [× PCUICPrimOpType.prim_shape_type Σ.1.(retroknowledge) (po_shape (info op)) = Some res,
       PCUICPrimOpType.prim_arg_types Σ.1.(retroknowledge) (po_args (info op)) res = Some Tp,
       Σ ;;; Γ ⊢E Tp ≤ A,
       on_prim_op_result Σ (po_shape (info op)) &
       All (prim_op_tag_declared Σ) (po_args (info op))].
Proof.
  intros wfΓ hdecl cu hop hle.
  unshelve epose proof (hg := declared_constant_to_gen hdecl); eauto.
  destruct (lookup_on_global_env_prim_decl wfΣ hg) as (Σ' & [onΣ' ext hretro hpd]).
  cbn in hpd. specialize (hpd op). forward hpd.
  { unfold prim_op_of in *. cbn. rewrite hretro. exact hop. }
  destruct hpd as [_ huniv [Tp [hTp hconv]] hargsinv hres].
  rewrite hretro in hTp. unfold PCUICPrimOpType.prim_op_type in hTp.
  destruct (PCUICPrimOpType.prim_shape_type _ (po_shape (info op))) as [res|] eqn:hsh => //.
  exists res, Tp.
  destruct (prim_shape_type_closed_inst _ _ _ u hsh) as [hclres hures].
  destruct (prim_arg_types_closed_inst _ _ _ _ u hTp hclres hures) as [hclTp huTp].
  assert (hext : extends Σ' Σ.1)
    by (eapply extends_decls_extends, strictly_extends_decls_extends_decls; tea).
  split; [reflexivity|exact hTp| | |].
  - change (cumulSpecE0 (Σ', cst_universes decl) [] Conv (cst_type decl) Tp) in hconv.
    eapply (weakening_env_convSpecE Σ' Σ.1 (cst_universes decl) []) in hconv; tea.
    eapply (convSpecE_subst_instance (Σ.1, cst_universes decl) [] u _ _ Σ.2) in hconv.
    2:{ eapply PCUICUnivSubstitutionTypEta.consistent_instance_valid_constraintsE; tea.
        split; [exact wfΣ|]. now eapply (weaken_lookup_on_global_env' _ _ (ConstantDecl decl)). }
    rewrite huTp in hconv. cbn in hconv.
    assert (hcl : closed (cst_type decl)@[u]).
    { rewrite closedn_subst_instance. eapply declared_constant_closed_typeE; tea. }
    have hws : Σ ;;; [] ⊢E (cst_type decl)@[u] = Tp.
    { apply into_ws_cumul_pbE_spec; [destruct Σ; exact hconv|reflexivity|..];
        now eapply closedn_on_free_vars. }
    eapply (weakening_ws_cumul_pbE (Γ := []) (Γ' := []) (Γ'' := Γ)) in hws.
    2: rewrite app_context_nil_l; now eapply wf_local_closed_contextE.
    cbn in hws. rewrite app_context_nil_l !lift_closed in hws; tas.
    etransitivity; [|exact hle]. eapply ws_cumul_pbE_eq_le. now symmetry.
  - destruct (po_shape (info op)); cbn in hres |- *.
    + destruct hres as (kn & d & [hpc hd hinv]). exists kn, d. split; tas.
      * cbn in hpc |- *. now rewrite -hretro.
      * eapply weakening_env_declared_constant; tea.
    + destruct hres as (i & mdecl & idecl & hpb & hdi). exists i, mdecl, idecl. split.
      * exact (eq_trans (f_equal Retroknowledge.retro_bool (eq_sym hretro)) hpb).
      * eapply weakening_env_declared_inductive; tea.
  - eapply All_impl; [exact hargsinv|]. intros t (kn & d & [hpc hd hinv]).
    exists kn, d. split; tas.
    + unfold primitive_constant in hpc |- *. now rewrite -hretro.
    + eapply weakening_env_declared_constant; tea.
Qed.

(** Base [sr_prim_op] ([:1764]). *)
Lemma sr_prim_opE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ c u decl op ls r v T} :
  Σ ;;; Γ |-E mkApps (tConst c u) (map term_of_lit ls) : T ->
  prim_op_of Σ c = Some op ->
  declared_constant Σ c decl ->
  prim_op_denote op ls = Some r ->
  readback Σ (po_shape (info op)) r = Some v ->
  Σ ;;; Γ |-E v : T.
Proof.
  intros ht hop _ hden hrb.
  pose proof (validityE ht) as isT.
  eapply inversion_mkApps_directE in ht as (A & s & hc & _ & hsp); tea.
  eapply inversion_ConstE in hc as (decl' & wfΓ & hdecl' & cu & hle); tea.
  destruct (prim_op_head_typeE wfΓ hdecl' cu hop hle) as (res & Tp & [hsh hTp hTA hres _]).
  pose proof (prim_op_denote_args _ _ _ hden) as hargs.
  eapply (typing_spine_prim_arg_typesE Tp A) in hsp; tea.
  2:{ apply (f_equal (@length _)) in hargs. now rewrite length_map in hargs. }
  pose proof (readback_typedE (Σ := Σ) (res := res) wfΓ hsh hres hrb) as hv.
  now eapply (type_ws_cumul_pbE (pb := Cumul) res).
Qed.

(** Base [isType_prim_tag_constant] ([:1795]). *)
Lemma isType_prim_tag_constantE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t kn d} :
  wf_localE Σ Γ -> t <> primArray ->
  declared_constant Σ kn d -> primitive_invariants t d ->
  isTypeE Σ Γ (tConst kn []).
Proof.
  intros wfΓ hna hd hinv.
  destruct t; try congruence; cbn in hinv.
  all: destruct hinv as [hty hbod huniv]; eapply has_sort_isTypeE with (s := _@[[]]);
    change (tSort ?s@[[]]) with (tSort s)@[[]];
    rewrite <- hty; refine (typeE_Const _ _ _ [] _ wfΓ hd _); rewrite huniv //.
Qed.

(** Base [isType_prim_shape_type] ([:1808]); the field [isType_prim_shape_type] of [T1_facts]. *)
Lemma isType_prim_shape_typeE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ s res} :
  wf_localE Σ Γ ->
  PCUICPrimOpType.prim_shape_type Σ.1.(retroknowledge) s = Some res ->
  on_prim_op_result Σ s ->
  isTypeE Σ Γ res.
Proof.
  intros wfΓ hsh hres. destruct s; cbn in hsh, hres.
  - destruct hres as (kn & d & [hpc hd hinv]).
    unfold PCUICPrimOpType.prim_tag_type, EnvironmentTyping.retro_type_constant in hsh.
    pose proof hpc as hpc'. cbn in hpc'. rewrite hpc' in hsh. cbn in hsh. noconf hsh.
    eapply isType_prim_tag_constantE; tea. discriminate.
  - assert (hrb : ∑ v, readback Σ SBool (RBool true) = Some v).
    { cbn in hsh |- *. destruct (Retroknowledge.retro_bool _) => //. now eexists. }
    destruct hrb as [v hrb].
    exact (validityE (readback_typedE (s := SBool) (res := res) wfΓ hsh hres hrb)).
Qed.

(** Base [isType_prim_arg_types] ([:1828]); the field [isType_prim_arg_types] of [T1_facts]. *)
Lemma isType_prim_arg_typesE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ tags res T} :
  wf_localE Σ Γ ->
  (forall t, In t tags -> t <> primArray) ->
  All (prim_op_tag_declared Σ) tags ->
  PCUICPrimOpType.prim_arg_types Σ.1.(retroknowledge) tags res = Some T ->
  isTypeE Σ Γ res -> isTypeE Σ Γ T.
Proof.
  intros wfΓ. induction tags as [|t tags ih] in T |- *; cbn; intros hna hall h hres.
  - noconf h. exact hres.
  - depelim hall.
    destruct (PCUICPrimOpType.prim_tag_type _ t) as [a|] eqn:ht => //.
    destruct (PCUICPrimOpType.prim_arg_types _ tags res) as [rest|] eqn:hr => //.
    cbn in h. noconf h.
    destruct p as (kn & d & [hpc hd hinv]).
    unfold PCUICPrimOpType.prim_tag_type in ht.
    destruct (EnvironmentTyping.retro_type_constant _ t) as [kn'|] eqn:hrt => //.
    cbn in ht. noconf ht.
    assert (ept : primitive_constant Σ t = EnvironmentTyping.retro_type_constant (retroknowledge Σ) t)
      by (destruct t; reflexivity).
    rewrite ept hrt in hpc. noconf hpc.
    assert (hnat : t <> primArray) by (apply hna; now left).
    assert (hrest : isTypeE Σ Γ rest).
    { eapply (ih rest); tea; try reflexivity. intros t' ht'. apply hna. now right. }
    assert (hdom : isTypeRelE Σ Γ (tConst kn' []) Relevant).
    { destruct t; try congruence; cbn in hinv.
      all: destruct hinv as [hty hbod huniv]; split; [constructor|];
        exists (Sort.type0@[[]]); repeat split.
      all: try reflexivity.
      all: change (tSort ?s@[[]]) with (tSort s)@[[]];
        rewrite <- hty; refine (typeE_Const _ _ _ [] _ wfΓ hd _); rewrite huniv //. }
    unfold tImpl.
    eapply (isType_tProdE (na := mkBindAnn nAnon Relevant)). split; [exact hdom|].
    eapply (isType_liftE (n := 1) (Γ := Γ ,, vass (mkBindAnn nAnon Relevant) (tConst kn' []))); cbn; tea.
    + lia.
    + constructor; tea.
Qed.

(** Base [typing_spine_prim_args] ([:1870]). Base's algorithmic [Σ ;;; Γ ⊢ A = ty_a] is
    [ws_cumul_pbE Conv] (it is base's [ws_cumul_pb], not [cumulAlgo]). *)
Lemma typing_spine_prim_argsE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ r tags res T} {args : list term} ty ty' :
  PCUICPrimOpType.prim_arg_types r tags res = Some ty ->
  Σ ;;; Γ ⊢E ty ≤ ty' ->
  #|args| <= #|tags| ->
  typing_spineE Σ Γ ty' args T ->
  (forall i a t, nth_error args i = Some a -> nth_error tags i = Some t ->
     ∑ A ty_a, [× PCUICPrimOpType.prim_tag_type r t = Some ty_a,
                 Σ ;;; Γ |-E a : A & Σ ;;; Γ ⊢E A = ty_a]) ×
  (#|args| < #|tags| -> ∑ na A B, Σ ;;; Γ ⊢E tProd na A B ≤ T).
Proof.
  induction tags as [|t tags ih] in args, ty, ty' |- *; intros hty hle hlen hsp.
  - destruct args as [|x args]; [|cbn in hlen; lia].
    split; [intros i a t' ha; destruct i; discriminate ha|cbn; lia].
  - cbn in hty.
    destruct (PCUICPrimOpType.prim_tag_type r t) as [a|] eqn:ht => //.
    destruct (PCUICPrimOpType.prim_arg_types r tags res) as [rest|] eqn:hrest => //.
    cbn in hty. noconf hty.
    destruct args as [|x args].
    + depelim hsp. split.
      * intros n a0 t0 ha; destruct n; discriminate ha.
      * intros _. unfold tImpl in hle. do 3 eexists. etransitivity; tea.
    + depelim hsp.
      assert (hP : Σ ;;; Γ ⊢E tImpl a rest ≤ tProd na A B) by (etransitivity; tea).
      unfold tImpl in hP.
      eapply ws_cumul_pbE_Prod_Prod_inv in hP as [_ hdom hcod].
      eapply substitution0_ws_cumul_pbE in hcod; [|exact (subject_is_open_termE t0)].
      unfold subst1 in hcod. rewrite simpl_subst_k in hcod; [reflexivity|].
      destruct (ih args rest (B {0 := x}) eq_refl hcod ltac:(cbn in hlen; lia) hsp) as [P1 P2].
      split.
      * intros [|n] a0 tg ha htg; cbn in ha, htg.
        -- noconf ha. noconf htg. exists A, a. split; tas. now symmetry.
        -- eapply P1; tea.
      * intros hlt. apply P2. cbn in hlt. lia.
Qed.

(** Base [prim_app_typing_inv] ([:1911]). *)
Lemma prim_app_typing_invE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ c u op args T} :
  prim_op_of Σ c = Some op ->
  Σ ;;; Γ |-E mkApps (tConst c u) args : T ->
  #|args| <= arity op ->
  (forall i a tag, nth_error args i = Some a -> nth_error (po_args (info op)) i = Some tag ->
     ∑ kn, (primitive_constant Σ tag = Some kn) × (Σ ;;; Γ |-E a : tConst kn [])) ×
  (#|args| < arity op -> ∑ na A B, Σ ;;; Γ ⊢E tProd na A B ≤ T).
Proof.
  intros hop ht hlen.
  pose proof (validityE ht) as isT.
  eapply inversion_mkApps_directE in ht as (A & s & hc & _ & hsp); tea.
  eapply inversion_ConstE in hc as (decl & wfΓ & hdecl & cu & hle); tea.
  destruct (prim_op_head_typeE wfΓ hdecl cu hop hle) as (res & Tp & [hsh hTp hTA hres hargs]).
  destruct (typing_spine_prim_argsE Tp A hTp hTA hlen hsp) as [P1 P2].
  split; [|exact P2].
  intros i a tag ha htg.
  destruct (P1 i a tag ha htg) as (A' & ty_a & [htt hta hconvA]).
  unfold PCUICPrimOpType.prim_tag_type in htt.
  destruct (EnvironmentTyping.retro_type_constant _ tag) as [kn|] eqn:hrt => //.
  cbn in htt. noconf htt.
  exists kn. split; [exact hrt|].
  eapply (nth_error_all htg) in hargs as (kn' & d & [hpc hd hinv]).
  assert (ept : primitive_constant Σ tag = EnvironmentTyping.retro_type_constant (retroknowledge Σ) tag)
    by (destruct tag; reflexivity).
  rewrite ept hrt in hpc. noconf hpc.
  eapply (type_ws_cumul_pbE (pb := Cumul) A'); tea.
  - eapply isType_prim_tag_constantE; tea.
    eapply po_args_not_array, nth_error_In; tea.
  - now eapply ws_cumul_pbE_eq_le.
Qed.

(** ** [sr_red1E]: subject reduction for one closed reduction step

  Base [sr_red1] ([:1942-3632]) is one [typing_ind_env] induction whose 17 premises are proved
  in one script. Here each premise of [typingE_ind_env] at base's three predicates is its own
  lemma [sr_red1E_<rule>], whose statement is that premise, computed by [sr_case_type]; each
  proof starts as base's does ([intros Σ wfΣ Γ wfΓ; unfold SR_red1; intros **; rename_all_hyps;
  auto], then base's [2-15] preprocessing, [sr_pre]) and continues with base's bullets for that
  rule, in base's order. [sr_red1E] then applies [typingE_ind_env] to them. *)

(** Hypothesis names for [typingE]/[wfE], as base [PCUICTyping.my_rename_hyp] gives for
    [typing]/[wf] ([Typing/PCUICWeakeningEnvTypEta.my_rename_hypE] is local to its file): the
    copied proofs refer to them. *)
Ltac my_rename_hypSR h th :=
  match th with
  | (wfE ?E) => fresh "wf" E
  | (wfE (fst_ctx ?E)) => fresh "wf" E
  | (wfE _) => fresh "wf"
  | (typingE _ _ ?t _) => fresh "type" t
  | (@cumulSpecE _ _ _ ?t _) => fresh "cumul" t
  | (@convSpecE _ _ ?t _) => fresh "conv" t
  | (All_local_env (lift_sorting (@typingE _) _ _) ?G) => fresh "wf" G
  | (All_local_env (lift_sorting (@typingE _) _) _) => fresh "wf"
  | context [typingE _ _ (_ ?t) _] => fresh "IH" t
  | _ => my_rename_hyp h th
  end.

Ltac rename_hyp h ht ::= my_rename_hypSR h ht.

(** The [n]-th premise of a chain of non-dependent arrows. *)
Ltac sr_nth_prem T n :=
  lazymatch n with
  | O => lazymatch T with ?A -> _ => constr:(A) end
  | S ?m => lazymatch T with _ -> ?B => sr_nth_prem B m end
  end.

(** The [n]-th premise of [typingE_ind_env] at base's predicates of [sr_red1], β-normal. *)
Ltac sr_case_type cf n :=
  let T := type of (@typingE_ind_env cf (@SR_red1E cf)
      (fun Σ Γ j =>
        lift_typing0 (fun t T => Σ ;;; Γ |-E t : T × forall u, Σ ;;; Γ ⊢ t ⇝1 u -> Σ ;;; Γ |-E u : T) j)
      (fun Σ Γ => wf_localE Σ Γ ×
        (forall Γ' Δ' Δ,
          Γ = Γ' ,,, Δ' ->
          OnOne2_local_env (fun Δ : context => on_one_decl (closed_red1 Σ (Γ',,, Δ))) Δ' Δ ->
          wf_local_relE Σ Γ' Δ))) in
  let T := eval cbv beta in T in
  let A := sr_nth_prem T n in
  exact A.

(** Base's preprocessing of the cases [2-15] (one reduction step inverted, the impossible and
    the congruence-by-constructor steps closed), then of the primitive-operation steps whose
    subject is not an application of a constant. *)
Ltac sr_pre_on Hu :=
  match goal with
    | [H : (_ ;;; _ |- _ <=s _) |- _ ] => idtac
    | _ =>
      invert_closed_red Hu;
      try solve [invert_mkApps_fix_eq];
      try solve [econstructor; eauto];
      try solve [
        match goal with
        | h : _ = mkApps _ ?args |- _ =>
          let e := fresh "e" in
          apply (f_equal nApp) in h as e ; simpl in e ;
          rewrite nApp_mkApps in e ; simpl in e ;
          destruct args ; discriminate
        end
      ]
  end;
  try solve [ match goal with
    | [ H : _ = mkApps (tConst _ _) (map term_of_lit ?ls) |- _ ] =>
        destruct ls using MRList.rev_ind;
        [ cbn in H; discriminate H | rewrite map_app mkApps_app in H; cbn in H; discriminate H ]
    | [ H : mkApps (tConst _ _) (map term_of_lit ?ls) = _ |- _ ] =>
        destruct ls using MRList.rev_ind;
        [ cbn in H; discriminate H | rewrite map_app mkApps_app in H; cbn in H; discriminate H ]
    end ].

Ltac sr_pre := match goal with [ Hu : closed_red1 _ _ _ _ |- _ ] => sr_pre_on Hu end.

Ltac sr_intro := intros Σ wfΣ Γ wfΓ; unfold SR_red1E; intros **; rename_all_hyps; auto.

(** *** Premise 1: the judgement predicate *)
Lemma sr_red1E_Pj {cf : checker_flags} : ltac:(sr_case_type cf 0).
Proof. sr_intro. Qed.

(** *** Premise 2: contexts ([:1981-2004]) *)
Lemma sr_red1E_ctx {cf : checker_flags} : ltac:(sr_case_type cf 1).
Proof.
  sr_intro.
  split; auto. intros Γ' Δ' Δ ->. clear X0.
  induction 1.
  * depelim X. apply All_local_rel_abs.
    now eapply All_local_env_app_inv.
    eapply lift_judgment_SRE with (2 := p).
    eapply lift_sorting_it_impl_gen with (tu := tu) => //.
  * depelim X. apply All_local_rel_def.
    now eapply All_local_env_app_inv.
    eapply lift_judgment_SRE with (2 := p); tea.
    eapply lift_sorting_it_impl_gen with tu => //=.
  * assert (wf_localE Σ (Γ' ,,, Γ'0) × lift_typing typingE Σ (Γ' ,,, Γ) (j_decl d) × is_closed_context (Γ' ,,, Γ)) as (wfΓ' & ond & clΓ').
    { depelim X; specialize (IHX0 _ X); clear X; pose proof (wf_local_closed_contextE all).
      all: split; [|now split].
      all: eapply All_local_env_app_inv in all as [wfΓ _]; eapply All_local_env_app in wfΓ; tea. }
    clear wfΓ X IHX0.
    apply All_local_rel_snoc.
    1: now apply All_local_env_app_inv in wfΓ'.
    apply lift_typing_impl with (1 := ond) => // ?? Hty.
    eapply closed_context_conversionE; tea.
    eapply red_one_decl_ws_cumul_ctx_pbE => //.
    eapply OnOne2_local_env_impl; tea.
    intros ???. eapply on_one_decl_impl => ???; firstorder.
Qed.

(** *** Premise 3: variables; δ for a let-bound variable ([:2006-2015]) *)
Lemma sr_red1E_Rel {cf : checker_flags} : ltac:(sr_case_type cf 2).
Proof.
  sr_intro. sr_pre.
  rewrite heq_nth_error in H. destruct decl as [na b ty]; noconf H.
  simpl.
  eapply All_local_env_nth_error in wfΓ as X0; tea.
  apply unlift_TermTyp in X0.
  cbn in *.
  rewrite <- (firstn_skipn (S n) Γ).
  eapply weakening_lengthE; auto.
  { rewrite firstn_length_le; auto. apply nth_error_Some_length in heq_nth_error. auto with arith. }
  now unfold app_context; rewrite firstn_skipn.
Qed.

(** *** Premise 4: sorts (no reduct) *)
Lemma sr_red1E_Sort {cf : checker_flags} : ltac:(sr_case_type cf 3).
Proof. sr_intro. sr_pre. Qed.

(** *** Premise 5: products; the domain step ([:2017-2027]) *)
Lemma sr_red1E_Prod {cf : checker_flags} : ltac:(sr_case_type cf 4).
Proof.
  sr_intro. sr_pre.
  assert (X1' : lift_typing typingE Σ Γ (j_vass_s na N1 s1)).
  1: now unshelve eapply lift_judgment_SRE with (1 := X1) => //.
  constructor; eauto.
  unshelve eapply (closed_context_conversionE _ typeb).
  1: constructor; tas.
  1: now eapply lift_sorting_forget_univ.
  constructor.
  now eapply ws_cumul_ctx_pbE_refl, wf_local_closed_contextE.
  constructor; auto. eapply red_ws_cumul_pbE.
  now eapply closed_red1_red.
Qed.

(** *** Premise 6: λ-abstractions; the domain step ([:2029-2039]). Base's algorithmic
    [cumul_red_r] on [cumul_refl'] is [JoinE_red_r]. *)
Lemma sr_red1E_Lambda {cf : checker_flags} : ltac:(sr_case_type cf 5).
Proof.
  sr_intro. sr_pre.
  assert (X1' : lift_typing typingE Σ Γ (j_vass na M')).
  1: now unshelve eapply lift_judgment_SRE with (1 := X1) => //.
  eapply type_Cumul_altE. eapply typeE_Lambda; eauto.
  unshelve eapply (closed_context_conversionE _ typeb). pcuic.
  constructor. now eapply ws_cumul_ctx_pbE_refl, wf_local_closed_contextE.
  constructor; auto. eapply red_ws_cumul_pbE. now eapply closed_red1_red.
  assert (Σ ;;; Γ |-E tLambda na t b : tProd na t bty). econstructor; pcuics.
  now eapply validityE in X2.
  apply JoinE_red_r, red1_red. constructor. apply Hu.
Qed.

(** *** Premise 7: let-ins; ζ ([:2041-2049]), the value step ([:2051-2062]) and the type step
    ([:2064-2076]). *)
Lemma sr_red1E_LetIn {cf : checker_flags} : ltac:(sr_case_type cf 6).
Proof.
  sr_intro. sr_pre.
  - (* LetIn body *)
    eapply type_Cumul_altE.
    apply (substitution_letE (Γ := Γ) (n := na) (u := b) (U := b_ty) (t := b') (T := b'_ty) typeb').
    specialize (typingE_wf_local typeb') as wfd.
    assert (Σ ;;; Γ |-E tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty).
    econstructor; eauto.
    eapply (validityE X2).
    apply JoinE_red_r, red1_red. constructor.

  - (* LetIn value *)
    assert (X1' : lift_typing typingE Σ Γ (j_vdef na r b_ty)).
    { unshelve eapply lift_judgment_SRE with (1 := X1); tea. split => //. right; now split. }
    eapply type_Cumul_altE.
    econstructor; eauto.
    unshelve eapply (closed_context_conversionE _ typeb'). pcuic.
    constructor. eapply ws_cumul_ctx_pbE_refl; eauto. constructor; auto.
    now eapply red_ws_cumul_pbE, closed_red1_red. apply ws_cumul_pbE_refl; eauto. now repeat inv_on_free_vars.
    assert (Σ ;;; Γ |-E tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty). econstructor; eauto.
    eapply (validityE X2).
    apply JoinE_red_r, red1_red. constructor. apply Hu.

  - (* LetIn type annotation *)
    assert (X1' : lift_typing typingE Σ Γ (j_vdef na b r)).
    { unshelve eapply lift_judgment_SRE with (1 := X1); tea. split => //. left; now split. }
    eapply type_Cumul_altE.
    econstructor; eauto.
    unshelve eapply (closed_context_conversionE _ typeb'). pcuic.
    constructor; auto. eapply ws_cumul_ctx_pbE_refl; eauto. constructor; auto.
    eapply ws_cumul_pbE_refl; eauto; repeat inv_on_free_vars =>//.
    apply: red_ws_cumul_pbE Hu.
    assert (Σ ;;; Γ |-E tLetIn na b b_ty b' : tLetIn na b b_ty b'_ty). econstructor; eauto.
    eapply (validityE X2).
    apply JoinE_red_r, red1_red. constructor. apply Hu.
Qed.

(** *** Premise 9: constants; δ ([:2127-2143]) and a registered operation of arity zero
    ([:2145-2152]). *)
Lemma sr_red1E_Const {cf : checker_flags} : ltac:(sr_case_type cf 8).
Proof.
  sr_intro. sr_pre.
  - (* Constant unfolding *)
    unshelve epose proof (H' := declared_constant_to_gen H); eauto.
    unshelve epose proof (H0' := declared_constant_to_gen H0); eauto.
    unshelve epose proof (declared_constant_inj decl decl0 _ _); tea; subst decl.
    destruct decl0 as [ty body' univs]; simpl in *; subst body'.
    eapply on_declared_constantE in H as (Hb & s & Ht & _); tas; cbn in Hb, Ht.
    rewrite <- (app_context_nil_l Γ).
    apply subject_closedE in Hb as clb; tas.
    apply type_closedE in Hb as clty; tas.
    replace (subst_instance u body)
      with (lift0 #|Γ| (subst_instance u body)).
    replace (subst_instance u ty)
      with (lift0 #|Γ| (subst_instance u ty)).
    2-3: rewrite -subst_instance_lift lift_closed; cbnr; tas.
    eapply weakeningE; tea.
    now rewrite app_context_nil_l.
    eapply (PCUICUnivSubstitutionTypEta.typing_subst_instance_declE _ []); tea.

  - (* red_prim_op on a constant: an operation of arity zero *)
    match goal with
    | [ H : ?tm = mkApps (tConst _ _) (map term_of_lit _) |- _ ;;; _ |-E _ : ?T ] =>
        assert (ht : Σ ;;; Γ |-E tm : T) by (eapply typeE_Const; eauto); rewrite H in ht
    | [ H : mkApps (tConst _ _) (map term_of_lit _) = ?tm |- _ ;;; _ |-E _ : ?T ] =>
        assert (ht : Σ ;;; Γ |-E tm : T) by (eapply typeE_Const; eauto); rewrite <- H in ht
    end.
    eapply sr_prim_opE; tea.
Qed.

(** *** Premises 10-11: inductives and constructors (no reduct) *)
Lemma sr_red1E_Ind {cf : checker_flags} : ltac:(sr_case_type cf 9).
Proof. sr_intro. sr_pre. Qed.

Lemma sr_red1E_Construct {cf : checker_flags} : ltac:(sr_case_type cf 10).
Proof. sr_intro. sr_pre. Qed.

(** *** Premise 16: primitive values; the three array steps ([:3602-3627]) *)
Lemma sr_red1E_Prim {cf : checker_flags} : ltac:(sr_case_type cf 15).
Proof.
  sr_intro. sr_pre.
  - eapply OnOne2_prod_inv in X2 as [X2 _].
    destruct X. depelim X0. depelim X1.
    Transparent prim_type.
    eapply (typeE_Prim _ _ (primArray; primArrayModel (set_array_value arr value))); tea.
    constructor; cbn; eauto.
    solve_all.
    eapply OnOne2_All_All; tea; cbn; intuition eauto.

  - destruct X. depelim X0. depelim X1.
    Transparent prim_type.
    eapply (typeE_Prim _ _ (primArray; primArrayModel (set_array_default arr def))); tea.
    constructor; cbn; eauto.

  - pose proof (typeE_Prim _ _ _ _ _ wfΓ heq_primitive_constant H0 H1 X0). eapply validityE in X3.
    destruct X. depelim X0. depelim X1.
    eapply (type_ws_cumul_pbE (pb:=Conv)); tea.
    eapply (typeE_Prim _ _ (primArray; primArrayModel (set_array_type arr ty))); tea.
    constructor; cbn; eauto.
    * eapply type_ws_cumul_pbE; tea. eapply has_sort_isTypeE; eauto.
      now eapply (red_ws_cumul_pbE (pb:=Conv)), closed_red1_red.
    * solve_all.
      eapply type_ws_cumul_pbE; tea. eapply has_sort_isTypeE; eauto.
      now eapply (red_ws_cumul_pbE (pb:=Conv)), closed_red1_red.
    * simp prim_type. eapply ws_cumul_pbE_App.
      eapply ws_cumul_pbE_refl; fvs. cbn.
      now symmetry; eapply red_ws_cumul_pbE, closed_red1_red.
Qed.

(** *** Premise 17: the conversion rule ([:3629-3631]) *)
Lemma sr_red1E_Cumul {cf : checker_flags} : ltac:(sr_case_type cf 16).
Proof.
  sr_intro.
  specialize (forall_u _ Hu).
  eapply typeE_Cumul; tea.
Qed.

End SREta.
