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
(* The landed T0 copies 10, 12, 14 (frac/eta 59eb717d) and 15 (frac/eta d49d1c19): the canonical
   [subsletE] ([PCUICSubstitutionEta]), [typing_spineE] ([PCUICAritiesEta], the twin of
   [PCUICArities.typing_spine]), [spine_substE] and [ctx_inst_subE] ([PCUICSpineEta]), and their
   lemmas. *)
From MetaRocq.PCUIC Require Import PCUICSubstitutionEta PCUICContextsEta PCUICAritiesEta PCUICSpineEta.
(* C9 (cross-lane-commitments.md): E3's global symmetry and transitivity instances for
   [ws_cumul_ctx_pbE Conv] and the term lists ([conv_context_symE], [ws_cumul_pbE_terms_sym],
   [ws_cumul_pbE_terms_trans]), which replace the three [#[local]] instances this file had. *)
From MetaRocq.PCUIC Require Import PCUICWsCumulEtaInstancesGlobal.
(* Copy 9 (gated at d46f9387, merged into this branch): [context_conversionE] and
   [closed_context_conversionE], with the statements the forecast block had. *)
From MetaRocq.PCUIC.Typing Require Import PCUICContextConversionTypEta.
(* T2a (a2a2adfc, merged into this branch): [validityE], [inversion_mkAppsE], the lemmas it proves
   for copy 16 and its forecast class [ValForecastCopy16], a premise of section [SREta] below. *)
From MetaRocq.PCUIC Require Import PCUICValidityEta.
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

(** ** FORECAST BLOCK

  Every fact below is a FORECAST: an E copy that is not on this branch will prove it, under exactly
  this name and with exactly this statement. Landing a row is: delete its part of this block (the
  definitions and the class of that row, and the [Context] line of that class in section [SREta]),
  import the copy. No proof below the block changes. Nothing here is an axiom: the classes are
  premises of every lemma that uses them, and [Print Assumptions] shows them as such. *)

(* Text and implicit status. The fields of copies 16 and 18 here and in T2a's class are the
   statement note's text (PCUICSREtaCopyStatements.v @ 33a87a58), which writes each binder with
   the implicit status, name and position of base's COMPILED lemma: [{wfΣ : wfE Σ}] where base has
   [{wfΣ : wf Σ}], an explicit environment premise exactly where base has one
   ([Construct_Ind_ind_eqE], [declared_projection_type_and_eqE], [isType_mkApps_Ind_invE],
   [declared_constructor_valid_tyE], [type_tCoFix_invE], [type_tFix_invE],
   [wf_cofixpoint_typing_spineE]). The note's [<base>E_statement] Definitions are never referenced
   by name (that would make every argument explicit): their text is copied into class fields, whose
   projections keep the braces. Copies 10, 12 and 14 (frac/eta 59eb717d) and copy 15 (frac/eta
   d49d1c19) have landed: their classes were deleted after a compiled-form identity check of each
   field against the landed lemma, and the copies are imported. *)
Local Set Warnings "-unexpected-implicit-declaration".

(** *** Definitions

  [subsletE], [typing_spineE], [spine_substE] (with its fields) and [ctx_inst_subE] are the landed
  canonical ones (copies 10, 14 and 15, imported above, with their [Derive Signature]);
  [has_sort_isTypeE], [has_sort_isTypeRelE] and [isWfArityE] are [PCUICTypingEtaNotions]'s.
  [validityE] and [inversion_mkAppsE] are T2a's proved lemmas. The definitions below are the
  forecast ones no landed file has yet. *)

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

(** *** Copy 16 ([PCUICInductivesEta.v]): the statement note's statements, verbatim.
    [declared_projection_type_and_eqE], [isType_mkApps_Ind_invE] and
    [on_minductive_wf_params_indices_instE] are fields of T2a's [ValForecastCopy16] (the note's
    text, environment premise explicit). *)

(* FORECAST-ONLY: proved by copy 16 (PCUICInductivesEta.v); delete when it lands. *)
Class SRForecastCopy16 := {
  (* note @ 0583b56e: twin of PCUICInductives.v:284; base SR uses it only through the [pcuic]
     hint database, so it is registered as a local [pcuic] hint in section [SREta]. *)
  isType_introE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {T : term} {s : sort},
    Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T ;
  instantiate_indsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ.1},
    forall {u : Instance.t} {mind : kername} {mdecl : mutual_inductive_body},
    declared_minductive Σ.1 mind mdecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    (inds mind (abstract_instance (ind_universes mdecl)) (ind_bodies mdecl))@[u] =
    inds mind u (ind_bodies mdecl) ;
  isType_mkApps_IndE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
      {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body}
      (decli : declared_inductive Σ ind mdecl idecl)
      {Γ : context} {puinst : Instance.t} {args inst : list term},
    consistent_instance_ext Σ (ind_universes mdecl) puinst ->
    spine_substE Σ Γ args inst (ind_params mdecl ,,, ind_indices idecl)@[puinst] ->
    Σ ;;; Γ |-E mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst] ;
  map_subst_let_expand_to_extended_listE :
    forall {cf : checker_flags} {Σ : global_env_ext} {s : list term} {Γ Δ : context},
    spine_substE Σ Γ s (List.rev s) (smash_context [] Δ) ->
    map (subst_let_expand (List.rev s) Δ) (to_extended_list Δ) = s ;
  red_it_mkProd_or_LetIn_smashE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall (Γ : list context_decl) (ctx : context) (t u : term) (n : nat) (c : context_decl),
    Σ ;;; Γ ⊢ it_mkProd_or_LetIn ctx t ⇝ u ->
    nth_error (List.rev (smash_context [] ctx)) n = Some c ->
    ∑ (ctx' : context) (t' : term) (d : context_decl),
      [× decompose_prod_assum [] u = (ctx', t'),
         nth_error (List.rev (smash_context [] ctx')) n = Some d &
         Σ ;;; Γ ,,, skipn (#|smash_context [] ctx| - n) (smash_context [] ctx) ⊢ decl_type c ⇝ decl_type d] ;
  typing_expand_lets_genE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall {Γ Δ Γ' : list context_decl} {t T : term},
    Σ ;;; Γ ,,, Δ ,,, Γ' |-E t : T ->
    Σ ;;; Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ' |-E
      expand_lets_k Δ #|Γ'| t : expand_lets_k Δ #|Γ'| T ;
  wf_local_expand_letsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall {Γ Δ Γ' : list context_decl},
    wf_localE Σ (Γ ,,, Δ ,,, Γ') ->
    wf_localE Σ (Γ ,,, smash_context [] Δ ,,, expand_lets_ctx Δ Γ')
}.

(** *** Copy 18 ([PCUICInductiveInversionEta.v]): the statement note's statements, verbatim. *)

(* FORECAST-ONLY: proved by copy 18 (PCUICInductiveInversionEta.v); delete when it lands. *)
Class SRForecastCopy18 := {
  Construct_Ind_ind_eqE :
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
             (skipn (ind_npars mdecl) args')]) ;
  cmp_global_instance_ind_invE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
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
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
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
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
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
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall {Γ : list context_decl} {l l' : list term},
    All2 (convSpecE Σ Γ) l l' ->
    is_closed_context Γ ->
    forallb (is_open_term Γ) l ->
    forallb (is_open_term Γ) l' ->
    ws_cumul_pbE_terms Σ Γ l l' ;
  (* The twin of base [PCUICInductiveInversion.isType_is_open_term] (PCUICInductiveInversion.v:4039,
     [Arguments {cf Σ wfΣ} Γ T _]), which copy 18 will twin. Checked in compiled form at the switch
     to frac/eta d49d1c19: the same type as the landed
     [Typing/PCUICClosedTypEta.isType_is_open_termE] (both-way ascription), but that one is the twin
     of base [Typing/PCUICClosedTyp.isType_is_open_term], with [Γ T] IMPLICIT
     ([Arguments {cf Σ wfΣ Γ T} _]); so it is kept. This field shadows that name here, as the
     copy-18 lemma will. *)
  isType_is_open_termE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall (Γ : context) (T : term),
    isTypeE Σ Γ T ->
    is_open_term Γ T ;
  on_constructor_instE :
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
        inst ((ind_params mdecl)@[u] ,,, (ind_indices idecl)@[u])) ;
  on_constructor_inst_wf_argsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
      {ind : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {cdecl : constructor_body}
      (declc : declared_constructor Σ ind mdecl idecl cdecl) (u : Instance.t),
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ ((ind_params mdecl)@[u] ,,,
      subst_context (ind_subst mdecl ind.1 u) #|ind_params mdecl| (cstr_args cdecl)@[u]) ;
  positive_cstr_closed_indicesE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall {i : inductive × nat} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {cdecl : constructor_body},
    declared_constructor Σ.1 i mdecl idecl cdecl ->
    All (fun t : term => closedn (context_assumptions (cstr_args cdecl) + #|ind_params mdecl|) t)
      (map (expand_lets (cstr_args cdecl)) (cstr_indices cdecl)) ;
  pre_case_branch_context_eqE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
    forall {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body}
      {params : list term} {puinst : Instance.t} {bctx : list aname} {cdecl : constructor_body},
    declared_inductive Σ ind mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) puinst ->
    wf_branch_gen cdecl bctx ->
    eq_context_upto_names
      (pre_case_branch_context ind mdecl params puinst cdecl)
      (case_branch_context_gen ind mdecl params puinst bctx cdecl) ;
  subslet_projsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
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
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
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
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ},
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

(* FORECAST-ONLY: one premise per class: T2a's one ([PCUICValidityEta], which its lemmas take too)
   and this block's two; delete each when its copy lands. *)
Context {V16 : ValForecastCopy16} {F16 : SRForecastCopy16} {F18 : SRForecastCopy18}.

(* FORECAST-ONLY: the [pcuic] hints that the copies re-register for their E lemmas (note @ 0583b56e:
   copy 16 [isType_introE]; copy 18 [isType_is_open_termE]); delete with their rows. Copy 15's,
   the coercion fields of [spine_substE], are registered globally by [PCUICSpineEta]. *)
#[local] Hint Resolve isType_introE : pcuic.
#[local] Hint Resolve isType_is_open_termE : pcuic.

(** The E counterparts of base's [typing]-specific [pcuic] hints that SR's [pcuic]/[pcuics]
    searches use ([PCUICTyping.has_sort_isType], [typing_wf_local]). *)
#[local] Hint Resolve has_sort_isTypeE typingE_wf_local : pcuic.

(* Symmetry and transitivity of the E context and term-list relations, which base's [symmetry] and
   [transitivity] calls find as instances for [ws_cumul_ctx_pb] and [ws_cumul_pb_terms], are E3's
   global instances ([PCUICWsCumulEtaInstancesGlobal], imported above; C9). They replaced this
   file's three [#[local]] instances, whose compiled forms they equal (names included). *)

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
  eapply cmp_global_instance_ind_invE in Hu; [|tc|apply declc.p1].
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
  pose proof (on_constructor_instE decl _ cu) as [wf _].
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
    eapply ctx_inst_cumulE.
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
  eapply ctx_inst_open_termsE in X.
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
  move/typing_expand_lets_genE; rewrite app_context_nil_l => hs.
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
  move/typing_expand_lets_genE; rewrite app_context_nil_l => hs.
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
  now apply: spine_subst_smashE.
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

(** *** Conversion facts at [subsletE] that the landed layer states at base [subslet]

  [PCUICWsCumulEtaSubst.substitution_ws_cumul_pbE] (the twin of base
  [PCUICConversion.substitution_ws_cumul_pb]) takes base's [subslet], from before [subsletE]
  existed. Its [subsletE] form, [substitution_ws_cumul_pbE_subslet], is in [PCUICSREtaConv], and
  the scoping of a [subsletE] is copy 10's [subsletE_open_terms]; both were local here before
  copy 10 landed. The lemma below gives the same kind of conclusion from the landed [_cb]
  reduction facts. *)

(** Base [PCUICConversion.closed_red_red_subst0] ([:477]) under [ClosedBodies Σ] in place of
    [wf Σ]: the landed [closed_red_red_subst_cb] at an empty context. *)
Lemma closed_red_red_subst0_cb {cf} {Σ : global_env_ext} {cbΣ : ClosedBodies Σ} {Γ Δ s s' b} :
  is_closed_context (Γ ,,, Δ) ->
  All2 (closed_red Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  is_open_term (Γ ,,, Δ) b ->
  Σ ;;; Γ ⊢ subst0 s b ⇝ subst0 s' b.
Proof.
  intros. eapply (closed_red_red_subst_cb (Γ' := [])); tea.
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

(** *** Premise 8: applications; β ([:2078-2088]), fixpoint unfolding ([:2090-2102]), the
    argument step ([:2104-2116]) and a registered operation applied ([:2118-2125]). *)
Lemma sr_red1E_App {cf : checker_flags} : ltac:(sr_case_type cf 7).
Proof.
  sr_intro. sr_pre.
  - (* β. [cumul_Prod_invE]: the domains are [Conv]-related even over η (audit §7 C1). *)
    eapply substitution0E; eauto.
    pose proof typet as typet'.
    eapply inversion_LambdaE in typet' as (B' & Ht & Hb & HU) =>//.
    apply cumul_Prod_invE in HU as [eqann eqA leqB] => //.
    pose proof (validityE typet) as i.
    eapply isType_tProdE in i as [Hdom Hcodom]; auto.
    eapply type_ws_cumul_pbE; eauto.
    destruct Hcodom as (_ & scodom & Hcodom & _).
    unshelve eapply (closed_context_conversionE _ Hb); pcuic.
    constructor. now apply ws_cumul_ctx_pbE_refl, wf_local_closed_contextE. constructor; auto.

  - (* Fixpoint unfolding *)
    assert (args <> []) by (destruct args; simpl in *; congruence).
    symmetry in H3. apply tApp_mkApps_inj in H3 as [-> Hu]; auto.
    rewrite mkApps_nonempty; auto.
    epose (last_nonempty_eq H4). rewrite <- Hu in e. rewrite <- e.
    clear e.
    specialize (inversion_mkAppsE typet) as [T' [appty spty]].
    have vT' := (validityE appty).
    eapply type_tFix_invE in appty as [T [arg [fn' [[[Hnth wffix] Hty]]]]]; auto.
    rewrite H in Hnth. noconf Hnth.
    eapply typeE_App; eauto.
    eapply type_mkAppsE; [|tea].
    eapply type_ws_cumul_pbE; eauto.

  - (* Application congruence for argument; base's [red_cumul_inv] is [JoinE_red_r] *)
    intuition auto.
    eapply type_Cumul_altE; [eapply typeE_App| |]; eauto with wf.
    eapply validityE.
    eapply typeE_App; eauto. eapply JoinE_red_r.
    eapply (red_red_cb (Γ := Γ) (Δ := [vass na A]) (Γ' := []) (s := [u]) (s' := [N2])); eauto.
    erewrite -> on_free_vars_ctx_on_ctx_free_vars.
    eapply on_free_vars_ctx_snoc_ass; tea.
    eapply type_closedE in typeu. now eapply closedn_on_free_vars.
    eapply type_closedE in typet. cbn in typet; repeat inv_on_free_vars.
    cbn. now eapply closedn_on_free_vars. constructor. apply: red1_red Hu. constructor.
    all:repeat constructor. cbn.
    rewrite -(shiftnP_add 1) addnP_shiftnP. repeat inv_on_free_vars => //.

  - (* red_prim_op on an application: an operation applied to literals *)
    match goal with
    | [ H : ?tm = mkApps (tConst _ _) (map term_of_lit _) |- _ ;;; _ |-E _ : ?T ] =>
        assert (ht : Σ ;;; Γ |-E tm : T) by (eapply typeE_App; eauto); rewrite H in ht
    | [ H : mkApps (tConst _ _) (map term_of_lit _) = ?tm |- _ ;;; _ |-E _ : ?T ] =>
        assert (ht : Σ ;;; Γ |-E tm : T) by (eapply typeE_App; eauto); rewrite <- H in ht
    end.
    eapply sr_prim_opE; tea.
Qed.

(** *** Premise 12: case analyses; ι ([:2154-2522]), a cofixpoint in the discriminee
    ([:2524-2570]), a parameter step ([:2572-2801]), a return-clause step ([:2803-2860]), the
    discriminee step ([:2862-2890]) and a branch step ([:2892-2919]).

    E-specific steps (each a landed fact): base's [PCUICAlpha.inst_case_predicate_context_eq]
    takes an unused [wf Σ]; here [PCUICCasesContexts.inst_case_predicate_context_eq], which gives
    the equation. Base's algorithmic [upto_names_conv_context] is
    [eq_context_upto_names_conv_contextE] into [into_ws_cumul_ctx_pbE]. Base's
    [cumulAlgo_cumulSpec] is [ws_cumul_pbE_forget_spec]; [closed_red1_open_right] (which takes
    [wf Σ]) is [closed_red_open_right_cb]; [red1_on_free_vars] is [red1_on_free_vars_cb]. *)
Lemma sr_red1E_Case {cf : checker_flags} : ltac:(sr_case_type cf 11).
Proof.
  sr_intro. sr_pre.
  - (* iota reduction *)
    clear forall_u forall_u0 X X0.
    unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
    destruct X4 as [wfcpc IHcpc].
    eassert (ctx_instE _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as IHctxi.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    hide X8.
    pose proof typec as typec''.
    unfold iota_red.
    pose proof typec as typec'.
    eapply inversion_mkAppsE in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_ConstructE Σ wf) in tyc as [mdecl' [idecl' [cdecl [wfl [declc [Hu tyc]]]]]].
    eapply typing_spine_strengthenE in tyargs; tea.
    have openargs : forallb (is_open_term Γ) args.
    { repeat inv_on_free_vars; auto. }
    clear tyc.
    2:{ eapply validityE. econstructor; tea. }
    unshelve eapply Construct_Ind_ind_eqE in typec'; eauto.
    unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
    pose proof (declared_inductive_inj isdecl' (proj1 declc')) as [-> ->].
    destruct typec' as [[[[[_ equ] cu] cu'] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci']]]]].
    destruct ci' as [cparsubst0 iparsubst0 idxsubst0 subsidx [s [typectx [Hpars Hargs]]]].
    pose proof (on_declared_constructorE declc) as [[onind oib] [ctor_sorts [hnth onc]]].
    unshelve epose proof (constructor_cumulative_indicesE declc Hu cu' equ _ _ _ _ _ cparsubst0 iparsubst0 Hpars).
    set (argctxu1 := subst_context _ _ _) in X |- *.
    set (argctxu := subst_context _ _ _) in X |- *.
    simpl in X.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in X |- *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in X |- *.
    destruct X as [cumargs convidx]; eauto.
    assert(wfparu : wf_localE Σ (subst_instance (puinst p) (ind_params mdecl))).
    { eapply on_minductive_wf_paramsE; eauto.
      destruct isdecl; eauto.  }
    assert (wfps : wf_sort Σ ps).
    { eapply validityE in IHp; auto. eapply isType_wf_universesE in IHp; tea.
      move: IHp => /= /PCUICWfUniverses.wf_sort_reflect //. }
    have lenpars := (wf_predicate_length_pars H0).
    unfold hidebody in X8.
    set (ptm := it_mkLambda_or_LetIn _ _).
    rename c0 into c.
    assert (isTypeE Σ Γ (mkApps ptm (indices ++ [mkApps (tConstruct ci c u) args]))).
    { eapply validityE. econstructor; eauto. all :constructor; eauto. apply (All2i_impl X8). intuition auto. }
    eapply All2i_nth_error in X8; tea.
    2:{ destruct declc. simpl in e. exact e. }
    cbn in X8.
    destruct X8 as (bctxeq & (wfcbc & _) & (hb & _) & cbty & _).
    cbn -[case_branch_type_gen] in hb.
    rewrite case_branch_type_fst in hb.
    set (prebrctx := pre_case_branch_context ci mdecl (pparams p) (puinst p) cdecl).
    set (ibrctx := (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)) in *.
    set (brctx := (inst_case_context (pparams p) (puinst p) (bcontext br))).
    assert (wfbr : wf_branch cdecl br).
    { eapply Forall2_All2, All2_nth_error in H5; tea.
      eapply declc. }
    assert(eqctx : eq_context_upto_names ibrctx brctx).
    { rewrite /brctx /ibrctx.
      rewrite /case_branch_context /case_branch_context_gen.
      etransitivity.
      eapply eq_binder_annots_eq.
      eapply wf_pre_case_branch_context_gen; tea.
      unfold pre_case_branch_context_gen.
      rewrite /inst_case_context.
      now eapply alpha_eq_subst_context, alpha_eq_subst_instance. }
    assert (convbrctx' : ws_cumul_ctx_pbE Conv Σ (Γ ,,, brctx) (Γ ,,, ibrctx)).
    { etransitivity; tea.
      eapply ws_cumul_ctx_pb_appE; revgoals.
      3:eapply ws_cumul_ctx_pbE_refl; eapply wf_local_closed_contextE; auto.
      split. apply ws_cumul_ctx_pbE_refl. now eapply wf_local_closed_contextE.
      eapply eq_context_alpha_convE => //. now symmetry.
      eapply wf_local_closed_contextE. eapply typingE_wf_local in hb.
      eapply wf_local_alphaE; tea. eapply All2_app => //. reflexivity.
      now apply typingE_wf_local, wf_local_closed_contextE in hb.
      rewrite /brctx /ibrctx; len.
      rewrite case_branch_context_length //. }
    assert (convbrctx'' : ws_cumul_ctx_pbE Conv Σ (Γ ,,, ibrctx) (Γ ,,, prebrctx)).
    { rewrite /ibrctx /prebrctx.
      symmetry.
      apply ws_cumul_ctx_pbE_rel_app.
      eapply eq_context_alpha_convE.
      eapply pre_case_branch_context_eqE; tea.
      eapply wf_local_closed_contextE. eapply wf_pre_case_branch_contextE; tea.
      now apply typingE_wf_local, wf_local_closed_contextE in cbty. }
    assert (prewf : wf_localE Σ (Γ ,,, prebrctx)).
    { eapply wf_pre_case_branch_contextE; tea. }
    assert (prewfs : wf_localE Σ (Γ ,,, smash_context [] prebrctx)).
    { eapply wf_local_smash_endE; tea. }
    assert (wfbrctx' : wf_localE Σ (Γ ,,, brctx)).
    { eapply wf_local_alphaE. eapply All2_app; tea. eapply All2_refl; reflexivity. assumption. }
    assert (convbrctxsmash : ws_cumul_ctx_pbE Conv Σ
        (Γ ,,, smash_context [] (case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl))
        (Γ ,,, smash_context [] brctx)).
    { eapply conv_context_smash_endE; tea. now symmetry. }
    assert (spbrctx : spine_substE Σ Γ (skipn (ind_npars mdecl) args) (List.rev (skipn (ind_npars mdecl) args))
      (smash_context [] prebrctx)).
    { pose proof (spine_subst_smashE idxsubst0).
      eapply spine_subst_cumulE in X0. eapply X0. all:tea.
      1-2:apply smash_context_assumption_context; pcuic.
      eapply X0.
      move: cumargs.
      rewrite /pargctxu /argctxu.
      move: iparsubst0.
      rewrite (firstn_app_left).
      now rewrite (wf_predicate_length_pars H0).
      intros iparsubst0.
      clear X5 IHctxi. unshelve epose proof (ctx_inst_spine_substE _ Hctxi).
      eapply PCUICWeakeningTypEta.weaken_wf_localE; tea. exact (on_minductive_wf_params_indices_instE isdecl _ cu').
      rewrite (spine_subst_inst_substE iparsubst0).
      intros cum.
      eapply ws_cumul_ctx_pb_rel_transE; tea.
      apply ws_cumul_ctx_pbE_rel_app.
      apply ws_cumul_ctx_pbE_refl_pb.
      now apply wf_local_closed_contextE in prewfs. }
    eapply closed_context_conversionE in hb.
    3:{ symmetry. eapply convbrctx'. }
    eapply typing_expand_letsE in hb.
    eapply (substitutionE (Δ := [])) in hb.
    2:{ eapply (spine_subst_cumulE (Γ' := smash_context [] brctx)) in spbrctx; tea.
        eapply spbrctx.
        1-2:apply smash_context_assumption_context; pcuic.
        now apply wf_local_smash_endE.
        apply ws_cumul_ctx_pb_rel_smashE => //.
        apply ws_cumul_ctx_pbE_rel_app. apply ws_cumul_ctx_pb_eq_leE. symmetry.
        etransitivity; tea. }
    rewrite subst_context_nil -heq_ind_npars in hb *.
    eapply (type_ws_cumul_pbE (pb:=Cumul)). exact hb. 3:auto.
    assumption. clear hb.
    rewrite /case_branch_type.
    set cbtyg := (case_branch_type_gen _ _ _ _ _ _ _ _ _).
    transitivity (subst0 (List.rev (skipn (ind_npars mdecl) args)) (expand_lets prebrctx cbtyg.2)).
    { eapply ws_cumul_pbE_eq_le.
      eapply (substitution_ws_cumul_pbE_subslet (Γ'' := [])). eapply spbrctx.
      symmetry. apply (ws_cumul_pb_expand_lets_ws_cumul_ctxE (pb:=Cumul)); tea.
      eapply wt_cumul_pb_reflE.
      rewrite case_branch_type_fst in cbty.
      eapply closed_context_conversionE in cbty. exact cbty.
      auto. auto.
      eapply ws_cumul_ctx_pbE_rel_app; tea. eapply ws_cumul_ctx_pb_eq_leE.
      symmetry. now transitivity (Γ ,,, ibrctx). }
    cbn.
    rewrite lift_mkApps !subst_mkApps.
    pose proof (wf_branch_length wfbr).
    have lenskip: #|skipn (ind_npars mdecl) args| = (context_assumptions (cstr_args cdecl)).
    { rewrite List.length_skipn eqargs; lia. }
    have lenfirst: #|firstn (ind_npars mdecl) args| = (context_assumptions (ind_params mdecl)).
    { rewrite firstn_length_le; try lia. now rewrite -(declared_minductive_ind_nparsE isdecl). }
    have brctxlen : #|prebrctx| = #|cstr_args cdecl|.
    { now rewrite /prebrctx !lengths. }
    have pparamsl : #|pparams p| = context_assumptions (ind_params mdecl).
    { move: (wf_predicate_length_pars H0).
      now rewrite (declared_minductive_ind_nparsE isdecl). }

    rewrite simpl_lift; try lia.
    rewrite subst_subst_lift // !(context_assumptions_subst_context, subst_context_length, lengths) //; try lia.
    rewrite map_app /= !map_app. eapply ws_cumul_pbE_eq_le.
    have wfparsargs : wf_localE Σ
      (subst_instance u (ind_params mdecl),,,
        subst_context (inds (inductive_mind ci) u (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance u (cstr_args cdecl))).
    { exact (on_constructor_wf_argsE declc Hu). }
    have wfparsargs' : wf_localE Σ
      (subst_instance (puinst p) (ind_params mdecl),,,
        subst_context (inds (inductive_mind ci) (puinst p) (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance (puinst p) (cstr_args cdecl))).
    { exact (on_constructor_wf_argsE declc cu'). }
    eapply ws_cumul_pbE_mkApps; tea.
    { eapply wt_cumul_pb_reflE. eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE; tea. }
    rewrite firstn_app_left // /= in iparsubst0.
    rewrite firstn_app_left // /= in Hpars.
    rewrite skipn_all_app_eq // in subsidx.
    have brctxass : context_assumptions prebrctx = context_assumptions (cstr_args cdecl).
    { now rewrite /prebrctx !lengths. }
    assert (eqargts : ws_cumul_pbE_terms Σ Γ (skipn (ind_npars mdecl) args)
      (skipn (ind_npars mdecl) args)).
    { pose proof (spine_subst_ctx_instE spbrctx).
      apply ctx_inst_open_termsE in X0.
      eapply All_All2; tea. cbn; intros.
      apply ws_cumul_pbE_refl; tea. }

    eapply All2_app.
    * set(indsub := inds _ _ _).
      relativize (map (subst0 _) _).
      2:{
        rewrite !map_map_compose. apply map_ext => x.
        symmetry.
        rewrite -/(subst_let_expand _ _ _) -/(subst_let_expand_k _ _ _ _).
        rewrite -brctxass -brctxlen -expand_lets_eq.
        rewrite {1 2}/prebrctx {1 2}/pre_case_branch_context {1}subst_context_length.
        rewrite /subst_let_expand_k (expand_lets_subst_comm _ _ _) !lengths.
        relativize (context_assumptions _).
        erewrite <- subst_app_simpl. 2:now rewrite !lengths.
        rewrite subst_app_decomp.
        relativize #|cstr_args cdecl|.
        erewrite subst_let_expand_app.
        2-4:rewrite ?lengths; try lia; reflexivity.
        rewrite /subst_let_expand.
        reflexivity. }
      move: Hargs.
      move: convidx.
      intros cv convidx.
      eapply (ws_cumul_pbE_terms_subst (Δ := [])) in cv.
      3:{ exact (spine_subst_smashE idxsubst0). }
      3:{ exact (spine_subst_smashE idxsubst0). }
      all:tea. 2:{ eapply wf_local_closed_contextE. eapply wf_local_smash_endE; tea. eapply idxsubst0. }
      2:{ eapply All2_rev => //. }
      rewrite subst_context_nil /= in cv. simpl in cv.
      rewrite skipn_all_app_eq // in convidx.

      assert(ws_cumul_pbE_terms Σ Γ
        (map
         (fun x : term =>
          subst0 (List.rev args)
            (expand_lets (argctxu1 ++ subst_instance u (ind_params mdecl)) (subst_instance u x)))
          (cstr_indices cdecl)) indices).
      { eapply eq_ws_cumul_pbE_terms_trans; tea.
        pose proof (positive_cstr_closed_indicesE declc).
        eapply All_map_inv in X0.
        eapply All_map_eq, All_impl; tea.
        cbn; intros x.
        intros cl.
        epose proof
          ( @spine_subst_appE cf Σ Γ (subst_instance u (ind_params mdecl))
            (subst_context
              (inds (inductive_mind ci) u (ind_bodies mdecl))
               #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))
          (firstn (ind_npars mdecl) args)
          (skipn (ind_npars mdecl) args) (cargsubst ++ cparsubst)) as X3.
        rewrite lenfirst in X3. len in X3.
        specialize (X3 eq_refl).
        forward X3. { rewrite -app_context_assoc. eapply PCUICWeakeningTypEta.weaken_wf_localE; tea. }
        forward X3. {
          rewrite skipn_all_app_eq; len.
          now rewrite -(PCUICContextSubst.context_subst_length idxsubst0); len.
          apply cparsubst0. }
        forward X3. {
          pose proof (PCUICContextSubst.context_subst_length idxsubst0).
          len in H8.
          rewrite firstn_app H8 firstn_all Nat.sub_diag /= app_nil_r skipn_all_app_eq //. }
        rewrite firstn_skipn in X3.
        rewrite (spine_subst_inst_subst_termE X3).
        f_equal.
        (* Base: [PCUICInductiveInversion.on_constructor_wf_args declc] (copy 18, qualified at base
           [:2397]; the note lists it as not used). Its conclusion is that of SR's own
           [on_constructor_wf_arities_pars_args], whose E twin is proved above. *)
        pose proof (on_constructor_wf_arities_pars_argsE declc).
        eapply closed_wf_localE in X4; tea.
        rewrite !closedn_ctx_app /= in X4 *.
        move/andb_and: X4 => [] /andb_and [] clar clp clargs.
        len in clargs.
        rewrite -(subst_closedn (inds (inductive_mind ci) u (ind_bodies mdecl))
              (context_assumptions (ind_params mdecl ,,, cstr_args cdecl))
              (expand_lets _ _)).
        { rewrite /argctxu1.
          relativize (context_assumptions _).
          eapply (closedn_expand_lets 0).
          rewrite !closedn_ctx_app /=.
          apply andb_true_iff; split.
          rewrite closedn_subst_instance_context.
          eapply (declared_inductive_closed_paramsE isdecl).
          rewrite subst_instance_length.
          eapply (closedn_ctx_subst 0). simpl.
          rewrite /ind_subst inds_length.
          now rewrite closedn_subst_instance_context.
          eapply closed_inds.
          rewrite /= length_app subst_context_length !subst_instance_length.
          rewrite Nat.add_comm in cl.
          eapply (PCUICClosed.closedn_expand_lets) in cl.
          rewrite closedn_subst_instance.
          now rewrite Nat.add_comm.
          rewrite /= !context_assumptions_app /= context_assumptions_subst_context //
            !context_assumptions_subst_instance //. }
        relativize (context_assumptions _).
        erewrite <-(expand_lets_subst_comm _ _ _).
        2:{ now rewrite /argctxu1 !context_assumptions_app
              !context_assumptions_subst_context !context_assumptions_subst_instance. }
        f_equal.
        * rewrite subst_context_app closed_ctx_subst.
          rewrite closedn_subst_instance_context.
          now apply (declared_inductive_closed_paramsE isdecl).
          f_equal. len.
          rewrite closed_ctx_subst //.
          rewrite /argctxu1. simpl.
          eapply (closedn_ctx_subst 0). simpl.
          rewrite /ind_subst inds_length closedn_subst_instance_context //.
          eapply closed_inds.
        * now rewrite /argctxu1; len. }
      clear convidx.
      etransitivity; tea.
      eapply (eq_ws_cumul_pbE_terms_trans (U:=
       (map (subst0 (List.rev (skipn (ind_npars mdecl) args)))
      (map (subst iparsubst (context_assumptions (cstr_args cdecl)))
         (map (expand_lets argctxu)
            (map (subst_instance (puinst p)) (cstr_indices cdecl))))))).
      2:{
        rewrite !map_map_compose.
        rewrite !map_map_compose in cv.
        eapply All2_map_inv, All2_All in cv.
        eapply All2_map, All_All2; tea.
        cbn; intros x Hx.
        eapply ws_cumul_pbE_eq_trans.
        symmetry; tea.
        rewrite (spine_subst_inst_subst_term_kE cparsubst0).
        pose proof (subst_let_expand_app).
        relativize (context_assumptions (cstr_args cdecl)).
        erewrite <-subst_app_simpl. 2:now len.
        rewrite -List.rev_app_distr firstn_skipn. len.
        rewrite lenskip expand_lets_app /argctxu1.
        rewrite context_assumptions_subst_context context_assumptions_subst_instance //. }

      rewrite /argctxu. simpl.
      rewrite !map_map_compose. apply All_map_eq.
      eapply All_impl.
      exact (All_map_inv _ _ _ (positive_cstr_closed_indicesE declc)).
      cbn => x.
      rewrite -(closed_ctx_subst indsub 0 (subst_instance _ _ ,,, _)).
      { now eapply closed_wf_localE in wfparsargs'. }
      relativize (#|ind_params _| + _).
      erewrite expand_lets_subst_comm; rewrite !lengths.
      2:rewrite !lengths; lia.
      rewrite -context_assumptions_app Nat.add_comm.
      move/(PCUICClosed.closedn_expand_lets) => /=. rewrite /= !lengths => clx.
      rewrite (subst_closedn indsub (_ + _)).
      relativize (_ + _). eapply (closedn_expand_lets 0).
      2-3:rewrite /= !lengths // closedn_subst_instance //.
      eapply closed_wf_localE; tea. now rewrite Nat.add_comm.
      rewrite (spine_subst_inst_subst_term_kE iparsubst0).
      change (ind_subst _ _ _) with indsub.
      relativize (context_assumptions _).
      erewrite <-subst_app_simpl. 2:now len.
      rewrite List.length_rev lenskip /=.
      relativize (context_assumptions _).
      erewrite <- expand_lets_app => //.
      now rewrite !lengths.

    * rewrite lift_mkApps /= !subst_mkApps /=. constructor. 2:constructor.
      rewrite !map_app.
      rewrite -{3}(firstn_skipn (ind_npars mdecl) args) -brctxlen -brctxass.
      rewrite - !expand_lets_eq_map.
      rewrite -/(expand_lets_k (bcontext br) 0 _).
      relativize (to_extended_list (cstr_args cdecl)).
      erewrite map_expand_lets_to_extended_list.
      2:{ etransitivity.
        2:apply to_extended_list_case_branch_context.
        rewrite /prebrctx.
        eapply conv_context_rel_to_extended_listE.
        apply ws_cumul_ctx_pbE_rel_app. symmetry. tea.
        now eapply Forall2_All2 in wfbr. }
      rewrite -map_expand_lets_to_extended_list.
      rewrite !map_map_compose.
      rewrite [map (fun x => _) (to_extended_list _)](@map_subst_let_expand_to_extended_listE _ cf Σ _ Γ); tea.
      relativize (map _ _).
      2:{ eapply map_ext => x. rewrite -/(subst_let_expand _ _ _).
          now rewrite subst_let_expand_lift_id //; len. }
      rewrite map_id.
      transitivity (mkApps (tConstruct ci c (puinst p)) args).
      rewrite -(firstn_skipn (ind_npars mdecl) args).
      eapply ws_cumul_pbE_mkApps; tea.
      eapply ws_cumul_pbE_refl => //.
      eapply All2_app. eapply All2_symP => //. intro; now symmetry.
      rewrite firstn_skipn //.
      rewrite firstn_skipn.
      eapply into_ws_cumul_pbE_spec.
      2:now eapply wf_local_closed_contextE.
      2:{ rewrite on_free_vars_mkApps /= //. }
      2:{ rewrite on_free_vars_mkApps /= //. }
      eapply eq_term_upto_univ_cumulSpecE.
      eapply eq_term_upto_univ_mkApps.
      2:reflexivity.
      constructor. eapply cmp_global_instance_sym; tc.
      rewrite eqargs.
      now eapply (cmp_global_instance_cstr_irrelevantE declc).

  - (* Case on a cofix: the cofix unfolds in the discriminee, and the return clause does not
       mention the discriminee *)
    destruct X0, X4.
    eassert (ctx_instE _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isty : isTypeE Σ Γ (mkApps ptm (indices ++ [mkApps (tCoFix mfix idx) args]))).
    { eapply validityE. econstructor; eauto. econstructor; eauto.
      constructor; eauto.
      apply (All2i_impl X8). intuition auto. }
    have typecof := typec.
    eapply inversion_mkAppsE in typecof as [? [tcof tsp]] => //.
    eapply type_tCoFix_invE in tcof as [d [[[Hnth wfcofix] Hbody] Hcum]] => //.
    unfold unfold_cofix in H.
    rewrite Hnth in H. noconf H.
    pose proof (validityE Hbody) as vbody.
    eapply typing_spine_strengthenE in tsp; [|exact vbody|exact Hcum].
    have typec' : Σ ;;; Γ |-E mkApps (subst0 (cofix_subst mfix) (dbody d)) args :
      mkApps (tInd ci (puinst p)) (pparams p ++ indices).
    { eapply type_mkAppsE; tea. }
    have hck := tsp.
    eapply wf_cofixpoint_typing_spineE in hck; tea.
    unfold check_recursivity_kind in hck.
    unshelve epose proof (isdecl' := declared_inductive_to_gen isdecl); eauto.
    rewrite isdecl'.p1 in hck.
    apply ReflectEq.eqb_eq in hck.
    have hnd : on_free_vars (strengthenP 0 1 xpredT) (preturn p).
    { match goal with h : implb (isCoFinite (ind_finite mdecl)) _ = true |- _ => move: h end.
      now rewrite hck. }
    have lenidx : #|indices| = context_assumptions (ind_indices idecl).
    { have hl := ctx_inst_length X5. len in hl. rewrite context_assumptions_rev in hl. len in hl.
      match goal with hw : wf_predicate _ _ _ |- _ => pose proof (wf_predicate_length_pars hw) end.
      pose proof (declared_minductive_ind_nparsE isdecl). lia. }
    have hidx : forallb (is_open_term Γ) indices.
    { have isty' := isty. eapply isType_is_open_termE in isty'.
      move: isty'. rewrite on_free_vars_mkApps forallb_app. now move=> /andP[] _ /andP[]. }
    eapply type_ws_cumul_pbE. eapply typeE_Case; eauto. 1: econstructor; eauto.
    1:econstructor; eauto.
    * solve_all.
    * tas.
    * eapply ws_cumul_pbE_eq_le.
      eapply case_nondep_predicate_convE; tea.
      + rewrite length_app /=. erewrite case_predicate_context_assumptions; tea. lia.
      + now eapply subject_is_open_termE in typec'.
      + now eapply subject_is_open_termE in typec.

  - (* Case congruence on a parameter *)
    eassert (ctx_instE _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    destruct X0, X4.
    assert (isTypeE Σ Γ (mkApps (it_mkLambda_or_LetIn (case_predicate_context ci mdecl idecl p) (preturn p)) (indices ++ [c]))).
    { eapply validityE. econstructor; eauto. all: econstructor; eauto.
      eapply (All2i_impl X8); intuition auto. }
    set (ptm := it_mkLambda_or_LetIn _ _) in *.
    cbn -[ptm it_mkLambda_or_LetIn] in *.
    have wfparinds : wf_localE Σ
      (Γ,,, subst_instance (puinst p) (ind_params mdecl,,, ind_indices idecl)).
    { eapply PCUICWeakeningTypEta.weaken_wf_localE; tea.
      eapply (on_minductive_wf_params_indices_instE isdecl _ H1). }
    have ctxi' : ctx_instE Σ Γ (params' ++ indices)
        (List.rev
           (subst_instance p.(puinst) (ind_params mdecl,,, ind_indices idecl))).
    { eapply OnOne2_prod_inv in X3 as [X3 _].
      eapply OnOne2_app_r in X3.
      unshelve eapply (ctx_inst_merge'E _ _ _ _ _ X6 X5); tea. }
    pose proof X5 as X5'.
    unshelve epose proof (ctx_inst_spine_substE _ X5); tea.
    eapply spine_subst_smashE in X4; tea.
    eapply ctx_inst_length in X5. len in X5.
    rewrite context_assumptions_rev in X5. len in X5.
    pose proof (wf_predicate_length_pars H0). simpl in H.
    pose proof (declared_minductive_ind_nparsE isdecl).
    have lenidx : (#|List.rev indices| = (context_assumptions (ind_indices idecl))) by (len; lia).
    rewrite subst_instance_app smash_context_app_expand in X4.
    eapply spine_subst_app_invE in X4 as [sppars spargs]; tea. 2:len.
    len in sppars. len in spargs.
    rewrite List.rev_app_distr in sppars spargs.
    rewrite skipn_app - !lenidx !skipn_all /= Nat.sub_diag skipn_0 in sppars spargs.
    rewrite firstn_app firstn_all Nat.sub_diag /= app_nil_r in spargs.
    rewrite subst_instance_app List.rev_app_distr in X6.
    have lenpars' := (OnOne2_length X3).
    unshelve epose proof (ctx_inst_spine_substE _ ctxi');tea.
    pose proof (spine_codom_wfE _ _ _ _ _ X4);tea.
    pose proof (spine_subst_smashE X4); tea. all:tea.
    rewrite subst_instance_app smash_context_app_expand in X9.
    eapply spine_subst_app_invE in X9 as [sppars' spargs']; tea.
    2:len. len in sppars'. len in spargs'.
    rewrite List.rev_app_distr in sppars' spargs'.
    rewrite skipn_app - !lenidx !skipn_all /= Nat.sub_diag skipn_0 in sppars' spargs'.
    rewrite firstn_app firstn_all Nat.sub_diag /= app_nil_r in spargs'.
    have wfp' : wf_predicate mdecl idecl (set_pparams p params').
    { move: H0. rewrite /wf_predicate /wf_predicate_gen /=.
      rewrite (OnOne2_length X3). intuition auto. }
    have redpars : red_terms Σ Γ (pparams p) params'.
    { eapply OnOne2_prod_inv in X3 as [cv _].
      clear -cv H H3. inv_on_free_vars.
      cbn in *; repeat inv_on_free_vars. clear b a2 a1 a0.
      induction cv; cbn; constructor; auto using closed_red1_red;
      cbn in *; repeat inv_on_free_vars; auto.
      apply red_terms_refl => //. now apply into_closed_red. }
    have convctx' :
      ws_cumul_ctx_pbE Conv Σ (case_predicate_context ci mdecl idecl p ++ Γ)
      (case_predicate_context ci mdecl idecl (set_pparams p params') ++ Γ).
    { move: X2 => cv.
      rewrite /case_predicate_context /case_predicate_context_gen.
      eapply ws_cumul_ctx_pbE_rel_app.
      eapply conv_ctx_set_binder_nameE.
      { change (pcontext (set_pparams p params')) with (pcontext p).
        eapply wf_pre_case_predicate_context_gen; tea. }
      { now eapply wf_pre_case_predicate_context_gen. }
      rewrite /pre_case_predicate_context_gen /inst_case_context.
      cbn [pparams puinst set_pparams].
      eapply ws_cumul_ctx_pbE_rel_app.
      eapply substitution_ws_cumul_ctx_pbE_red_subst.
      3:eapply subslet_untyped_subsletE, sppars.
      2:eapply All2_rev => //.
      clear cv.
      rewrite -app_context_assoc. eapply is_closed_context_weaken. fvs.
      rewrite -on_free_vars_ctx_on_ctx_free_vars -closedP_shiftnP_eq
       -closed_ctx_on_ctx_free_vars.
      rewrite closedn_ctx_app !lengths.
      apply/andP; split. 2:cbn -[ind_predicate_context].
      2:rewrite closedn_subst_instance_context. 2:eapply closed_ind_predicate_context; tea.
      2:eapply declared_minductive_closedE, isdecl.
      eapply closedn_smash_context.
      now eapply declared_inductive_closed_params_instE. }
    have isty' : isTypeE Σ Γ (mkApps (tInd ci (puinst p)) (params' ++ indices)).
    { eapply has_sort_isTypeE; eapply isType_mkApps_IndE; tea. }
    have wfcpc' : wf_localE Σ (Γ ,,, case_predicate_context ci mdecl idecl (set_pparams p params')).
    { eapply wf_case_predicate_contextE; tea. }
    have eqindices : ws_cumul_pbE_terms Σ Γ indices indices.
    { now eapply spine_subst_wt_termsE, wt_terms_ws_cumul_pbE in spargs'. }
    have typec' : Σ;;; Γ |-E c : mkApps (tInd ci (puinst p)) (params' ++ indices).
    { eapply type_ws_cumul_pbE; tea.
      eapply ws_cumul_pbE_eq_le. eapply ws_cumul_pbE_mkApps.
      { apply ws_cumul_pbE_refl; [now eapply wf_local_closed_contextE|reflexivity]. }
      eapply All2_app => //. now apply: red_terms_ws_cumul_pbE_terms. }
    set (pctx := (inst_case_predicate_context (set_pparams p params'))) in *.
    have eqctx : eq_context_upto_names (case_predicate_context ci mdecl idecl (set_pparams p params')) pctx.
    { rewrite /pctx (PCUICCasesContexts.inst_case_predicate_context_eq (p := set_pparams p params') X1).
      reflexivity. }
    have wfpctx : wf_localE Σ (Γ,,, inst_case_predicate_context (set_pparams p params')).
    { eapply wf_local_alphaE; tea; auto.
      eapply All2_app => //. reflexivity. }
    have eqpctx : ws_cumul_ctx_pbE Conv Σ (Γ ,,, pctx) (Γ ,,, case_predicate_context ci mdecl idecl (set_pparams p params')).
    { symmetry.
      rewrite /pctx.
      eapply into_ws_cumul_ctx_pbE => //.
      now eapply wf_local_closed_contextE.
      now eapply wf_local_closed_contextE.
      eapply eq_context_upto_names_conv_contextE.
      eapply All2_app; [exact eqctx|reflexivity]. }
    epose proof (wf_case_branches_types'E (p:=set_pparams p params') ps _ brs isdecl isty' wfp').
    cbv zeta in X9; forward_keep X9.
    { eapply closed_context_conversionE; tea. }
    do 2 forward X9 by auto.
    eapply (type_ws_cumul_pbE (pb := Conv)); tea.
    { econstructor; tea. all: econstructor; tea.
      (* The branches contexts also depend on the parameters. *)
      apply All2i_nth_hyp in X9.
      eapply All2i_All2i_mix in X8; tea. clear X9.
      eapply (All2i_impl X8); clear X8.
      intros cstr cdecl br. cbv zeta.
      rewrite !case_branch_type_fst.
      do 2 case. move=> hnth [] wfbr wfbctxargs wfbrctx wfcbc' wfcbcty'.
      case => eqbctx. case. case => wfbctx _.
      move=> [] [] Hbody IHbody [] brty IHbrty.
      eapply and_assum. solve_all. move=> cvcbc.
      apply and_assum; [|move=> wfcb'].
      { now eapply typingE_wf_local in wfcbcty'. }
      split => //.
      have declc : declared_constructor Σ (ci, cstr) mdecl idecl cdecl.
      { split => //. }
      have convbctx : ws_cumul_ctx_pbE Conv Σ (Γ,,, case_branch_context ci mdecl p (forget_types (bcontext br)) cdecl)
        (Γ,,, case_branch_context ci mdecl (set_pparams p params') (forget_types (bcontext br)) cdecl).
      { rewrite /case_branch_context /case_branch_context_gen.
        eapply ws_cumul_ctx_pbE_rel_app.
        eapply conv_ctx_set_binder_nameE. eapply wf_pre_case_branch_context_gen; tea.
        eapply wf_pre_case_branch_context_gen; tea.
        rewrite /case_branch_context /case_branch_context_gen.
        eapply (substitution_ws_cumul_ctx_pbE_subst_conv (Γ' := smash_context [] (ind_params mdecl)@[puinst p]) (Γ'':=[])).
        2:{ eapply All2_rev.
          eapply OnOne2_prod_inv in X3 as [redp _].
          now eapply red_terms_ws_cumul_pbE_terms. }
        apply ws_cumul_ctx_pbE_rel_app.
        eapply ws_cumul_ctx_pbE_refl, wf_local_closed_contextE.
        rewrite /=. rewrite /cstr_branch_context.
        rewrite subst_instance_expand_lets_ctx.
        eapply wf_local_expand_letsE.
        epose proof (on_constructor_inst_wf_argsE declc (puinst p) H1) as onc.
        rewrite -app_context_assoc; eapply PCUICWeakeningTypEta.weaken_wf_localE; auto.
        rewrite subst_instance_subst_context.
        now rewrite subst_instance_inds (subst_instance_id_mdecl _ _ _ H1).
        eapply subslet_untyped_subsletE, sppars. eapply subslet_untyped_subsletE, sppars'.
        eapply wf_local_closed_contextE.
        eapply wf_local_smash_endE.
        apply PCUICWeakeningTypEta.weaken_wf_localE => //. eapply on_minductive_wf_paramsE; tea. eapply isdecl. }
      eapply (type_ws_cumul_pbE (pb:=Conv)); tea.
      + eapply closed_context_conversionE; tea.
      + eapply has_sort_isTypeE with (s := ps). exact wfcbcty'.
      + eapply ws_cumul_pbE_mkApps; tea.
        { rewrite /ptm. cbn [preturn set_pparams].
          rewrite !lift_it_mkLambda_or_LetIn.
          eapply ws_cumul_pbE_it_mkLambda_or_LetIn.
          relativize #|cstr_args cdecl|.
          eapply weakening_ws_cumul_ctx_pbE; tea.
          apply ws_cumul_ctx_pbE_refl, wf_local_closed_contextE => //.
          now apply (case_branch_context_length_args wfbr).
          rewrite !case_predicate_context_length // /= Nat.add_0_r.
          relativize #|pcontext p|. relativize #|cstr_args cdecl|.
          eapply weakening_ws_cumul_pbE; tea.
          apply isType_ws_cumul_pbE_refl. now eapply has_sort_isTypeE.
          now apply wf_local_closed_contextE.
          now apply case_branch_context_length_args.
          now rewrite case_predicate_context_length. }
        cbn.
        eapply All2_app.
        - rewrite /case_branch_context /case_branch_context_gen /pre_case_branch_context
          /pre_case_branch_context_gen /inst_case_context. cbn.
          symmetry. rewrite /subst_context PCUICRenameConv.map2_set_binder_name_fold ?lengths.
          now apply wf_branch_length.
          rewrite -/(subst_context _ _ _).
          relativize #|cstr_args cdecl|.
          eapply ws_cumul_pbE_terms_subst.
          2:eapply subslet_untyped_subsletE, sppars'.
          2:eapply subslet_untyped_subsletE, sppars.
          { eapply wf_local_closed_contextE, wf_local_smash_endE, PCUICWeakeningTypEta.weaken_wf_localE => //.
            eapply (on_minductive_wf_paramsE isdecl) => //. }
          { apply All2_rev; symmetry. now apply red_terms_ws_cumul_pbE_terms. }
          { epose proof (on_constructor_closed_indices_instE declc (u:=puinst p) H1).
            eapply WT_refl.
            { rewrite /cstr_branch_context.
              apply wf_local_closed_contextE.
              move: wfbrctx.
              move/wf_local_expand_letsE. cbn.
              rewrite subst_instance_expand_lets_ctx map2_set_binder_name_expand_lets ?lengths //.
              apply (wf_branch_length wfbr).
              rewrite subst_instance_subst_context instantiate_indsE //.
              eapply declc. }
            rewrite 2!forallb_map.
            eapply All_map_inv in X8. eapply All_forallb, All_impl; tea.
            cbn; intros x clx.
            apply closedn_on_free_vars.
            rewrite -on_free_vars_closedn in clx.
            len. rewrite !map2_length !lengths.
            now apply wf_branch_length. rewrite lengths in clx.
            rewrite (wf_branch_length wfbr).
            rewrite (Nat.add_comm _ #|Γ|) Nat.add_assoc (Nat.add_comm _ #|Γ|).
            rewrite -(context_assumptions_subst_instance (puinst p)) closedn_expand_lets_eq.
            eapply closedn_ctx_upwards. eapply (declared_inductive_closed_params_instE declc). lia.
            len. rewrite (Nat.add_comm #|ind_params mdecl|).
            eapply closed_upwards; tea. len. }
          pose proof (wf_branch_length wfbr).
          now rewrite map2_length !lengths.
        - apply All2_tip, ws_cumul_pbE_mkApps; [apply into_ws_cumul_pbE => //; try apply JoinE_refl|].
          now eapply wf_local_closed_contextE.
          eapply All2_app. eapply All2_map.
          eapply OnOne2_prod_inv in X3 as [X3 _].
          eapply red_terms_ws_cumul_pbE_terms in redpars.
          eapply All2_impl; tea. intros.
          relativize #|cstr_args cdecl|; [eapply (weakening_ws_cumul_pbE (Γ' := []))|] => //.
          now eapply wf_local_closed_contextE.
          now eapply case_branch_context_length_args.
          eapply WT_refl. now apply wf_local_closed_contextE.
          eapply forallb_impl. 2:eapply closedn_to_extended_list.
          intros. rewrite !lengths. rewrite case_branch_context_length_args //.
          eapply closedn_on_free_vars, closed_upwards; tea. lia. }
    + rewrite /ptm.
      eapply ws_cumul_pbE_mkApps.
      { eapply ws_cumul_pbE_it_mkLambda_or_LetIn => //.
        now symmetry. cbn [preturn set_pparams].
        eapply wt_cumul_pb_reflE; eauto. }
      eapply All2_app; eauto. apply All2_tip.
      now eapply wt_cumul_pb_reflE.

  - (* Case congruence on the return clause context *)
    clear IHHu. destruct X0, X4 as [].
    eassert (ctx_instE _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isTypeE Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validityE. econstructor; eauto. econstructor; eauto.
      split; eauto.
      apply (All2i_impl X8). intuition auto. }
    assert (closed_red1 Σ (Γ,,, case_predicate_context ci mdecl idecl p)
      (preturn p) preturn').
    { eapply closed_red1_eq_context_upto_names; tea.
      rewrite PCUICCasesContexts.inst_case_predicate_context_eq => //.
      reflexivity. }
    have hnd' : (isCoFinite (ind_finite mdecl) ==>
      on_free_vars (strengthenP 0 1 xpredT) preturn') = true.
    { match goal with
      | h : implb (isCoFinite (ind_finite mdecl)) _ = true,
        hr : closed_red1 _ _ (preturn p) preturn' |- _ => move: h; pose proof hr as hred
      end.
      case: (isCoFinite (ind_finite mdecl)) => //= hfv.
      eapply PCUICClosedTyp.red1_on_free_vars_cb; [exact (clrel_rel hred)|exact hfv|].
      apply on_ctx_free_vars_nondep.
      exact (on_free_vars_ctx_on_ctx_free_vars_xpredT (clrel_ctx hred)). }
    eapply type_ws_cumul_pbE; tea.
    * eapply typeE_Case; eauto. constructor; eauto. constructor; eauto.
      epose proof (wf_case_branches_types'E (p:=set_preturn p preturn') ps _ brs isdecl (validityE typec) H0
        (forall_u _ X3) H5 X1).
      eapply All2i_All2_mix_left in X8. 2:exact (Forall2_All2 _ _ H5). clear H5.
      eapply (All2i_All2i_mix X4) in X8. clear X4.
      eapply (All2i_impl X8); intuition auto; clear X8.
      rewrite !case_branch_type_fst in a3 a4 *.
      set (cbty' := case_branch_type _ _ _ _ _ _ _ _) in *.
      set (cbty := case_branch_type _ _ _ _ _ _ _ _) in b0.
      have btyred : Σ ;;; Γ,,, cbty.1 ⊢ cbty.2 ⇝1 cbty'.2.
      { rewrite /cbty /cbty'.
        apply: closed_red1_case_branch_type_cb => //.
        eapply subject_closedE in a4. now apply closedn_on_free_vars.
        now eapply wf_local_closed_contextE.
        now apply closed_red1_it_mkLambda_or_LetIn_cb. }
      destruct a1 as [wfparctx wfparctx' wfcbc wfcbty].
      split => //. split => //.
      eapply type_ws_cumul_pbE; tea.
      now eapply has_sort_isTypeE.
      eapply (ws_cumul_pbE_ws_cumul_ctx_pb (pb':=Cumul)); tea.
      2:eapply closed_red1_ws_cumul_pbE, btyred.
      now apply ws_cumul_ctx_pbE_refl_pb, wf_local_closed_contextE.
    * eapply ws_cumul_pbE_eq_le, ws_cumul_pbE_mkApps; tea.
      2:{ eapply WT_refl => //.
          eapply isType_is_open_termE in X0.
          rewrite on_free_vars_mkApps in X0.
          now move/andP: X0=> []. }
      eapply ws_cumul_pbE_it_mkLambda_or_LetIn; tea.
      now eapply ws_cumul_ctx_pbE_refl, wf_local_closed_contextE.
      cbn [preturn set_preturn].
      symmetry; apply closed_red1_ws_cumul_pbE => //.

  - (* Case congruence on discriminee *)
    destruct X0, X4.
    eassert (ctx_instE _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    set (ptm := it_mkLambda_or_LetIn _ _).
    assert (isTypeE Σ Γ (mkApps ptm (indices ++ [c]))).
    { eapply validityE. econstructor; eauto. econstructor; eauto.
      constructor; eauto.
      apply (All2i_impl X8). intuition auto. }
    eapply type_ws_cumul_pbE. eapply typeE_Case; eauto. 1: econstructor; eauto.
    1:econstructor; eauto.
    * solve_all.
    * tas.
    * eapply ws_cumul_pbE_eq_le, ws_cumul_pbE_mkApps; tea.
      eapply wt_cumul_pb_reflE. eapply PCUICGenerationEta.type_it_mkLambda_or_LetInE; tea.
      apply into_ws_cumul_pb_termsE.
      + eapply All2_app. apply All2_refl. reflexivity.
        apply All2_tip. eapply (ws_cumul_pbE_forget_spec (pb:=Conv)).
        symmetry. now eapply closed_red1_ws_cumul_pbE.
      + now apply wf_local_closed_contextE.
      + eapply isType_is_open_termE in X0.
        rewrite on_free_vars_mkApps in X0.
        move/andP: X0=> []. generalize (closed_red_open_right_cb (closed_red1_red Hu)).
        rewrite !forallb_app /= => clc' clptm /and3P[] -> /=.
        now rewrite clc'.
      + eapply isType_is_open_termE in X0. rewrite on_free_vars_mkApps in X0.
        now move/andP: X0 => [].

  - (* Case congruence on branches *)
    destruct X0, X4.
    eassert (ctx_instE _ _ _ _) as Hctxi by (eapply ctx_inst_impl with (1 := X5); now intros ? []).
    eassert (PCUICEnvTyping.ctx_inst _ _ _ _) as X6.
    { eapply ctx_inst_impl with (1 := X5). intros t T [? r]; pattern Γ, t, T in r; exact r. }
    clear X5; rename Hctxi into X5.
    eapply typeE_Case; eauto. econstructor; eauto.
    econstructor; eauto.
    * eapply Forall2_All2 in H5.
      move: (All2_sym _ _ _ H5) => wfb.
      red. eapply All2_Forall2.
      apply All2_sym.
      eapply (OnOne2_All2_All2 X3 wfb); auto.
      intros [] []; simpl. intros.
      destruct X0 as [_ eq]. subst bcontext0. exact H4.
    * apply Forall2_All2 in H5. eapply All2i_All2_mix_left in X8; tea.
      eapply (OnOne2_All2i_All2i X3 X8).
      intros n [] []; simpl. intros. intuition auto.
      intros n [ctx b] [ctx' b'] cdecl; cbn.
      rewrite !case_branch_type_fst.
      intros [red <-].
      move=> [] wfbr [] convctx [] [] wfcbc IHcbc [] [] Hb IHb [] Hbty IHbty.
      intuition auto. clear b0.
      eapply IHb. eapply closed_red1_eq_context_upto_names; tea.
      eapply All2_app.
      2:reflexivity. etransitivity.
      2:eapply pre_case_branch_context_eqE; cbn; tea.
      apply inst_case_branch_context_eqE => //. apply isdecl.
Qed.

(** *** Premise 13: projections; of a cofixpoint ([:2921-3021]), of a constructor
    ([:3023-3294]) and the discriminee step ([:3296-3326]). Base's algorithmic
    [conv_cumul]/[conv_sym]/[PCUICCumulativity.red_conv] on a reduction of the original type to
    the reduct's is [JoinE_red_r]. *)
Lemma sr_red1E_Proj {cf : checker_flags} : ltac:(sr_case_type cf 12).
Proof.
  sr_intro. sr_pre.
  - (* Proj CoFix reduction *)
    assert(typecofix : Σ ;;; Γ |-E tProj p (mkApps (tCoFix mfix idx) args0) : subst0 (mkApps (tCoFix mfix idx) args0 :: List.rev args)
      (subst_instance u pdecl.(proj_type))).
    { econstructor; eauto. }
    inv_on_free_vars.
    generalize typec.
    move/inversion_mkAppsE => [ty [tcof tsp]]; auto.
    move/type_tCoFix_invE: (tcof) => [d [[[Hnth wfcofix] Hbody] Hcum]]; auto.
    rewrite /unfold_cofix Hnth in H; noconf H.
    simpl in *.
    generalize typec.
    move/validityE/(isType_mkApps_Ind_proj_invE _ isdecl) => [sppars hargs hinds cu].
    have lenargs : #|args| = context_assumptions (ind_params mdecl).
    { pose proof (subslet_lengthE sppars) as hl. move: hl; now len. }
    eapply type_Cumul_altE; [econstructor|..]; eauto.
    + eapply typing_spine_strengthenE in tsp. 3:tea.
      eapply type_mkAppsE. eauto. eauto.
      now eapply validityE in Hbody.
    + now eapply validityE in typecofix.
    + apply JoinE_red_r.
      rewrite (subst_app_simpl [mkApps (subst0 (cofix_subst mfix) (dbody d)) args0]) (subst_app_simpl [mkApps (tCoFix mfix idx) args0]).
      apply clrel_rel.
      destruct (on_declared_projectionE isdecl) as [[oi hctors] onp].
      eassert (projsubs := subslet_projsE (args := args) isdecl).
      set (oib := declared_inductive_invE _ _ _ _) in *. simpl in onp, projsubs.
      rewrite hctors in projsubs.
      destruct onp as [[[tyargctx onps] Hp2] onp].
      destruct (ind_cunivs oib) as [|? []] eqn:hcunivs; try rewrite hcunivs // in tyargctx.
      specialize (projsubs onps).
      epose proof (declared_projection_type_and_eqE wf isdecl) as [[hctors' hty] [decl'' [Hdecl Hty wfdecl peq peq']]].
      red in onp.
      unfold projection_type, projection_type' in *.
      set (indsubst := inds _ _ _) in *.
      set (projsubst := projs _ _ _) in *.
      set (indb := vass _ _) in *.
      rewrite -peq peq'. cbn.
      rewrite subst_instance_subst.
      rewrite (distr_subst_rec _ _ _ 1 0) /=.
      rewrite [_@[u]]subst_instance_projs.
      rewrite projs_subst_above //.
      rewrite !distr_subst !subst_projs_inst /=.
      rewrite projs_length Nat.add_0_r.
      rewrite !subst_instance_subst.
      rewrite -(Nat.add_1_r p.(proj_arg)) subst_instance_lift.
      rewrite -commut_lift_subst_rec // -(commut_lift_subst_rec _ _ 1 p.(proj_arg)) //.
      rewrite !simpl_subst_k //.
      specialize (projsubs _ _ _ typec).

      eapply (closed_red_red_subst0_cb (Γ := Γ)
        (Δ := skipn (context_assumptions (cstr_args cdecl) - p.(proj_arg))
          (subst_context (List.rev args) 0
          (subst_context (extended_subst (ind_params mdecl)@[u] 0) 0 (smash_context []
          (subst_context (inds (inductive_mind p.(proj_ind)) u (ind_bodies mdecl))
          #|ind_params mdecl| (subst_instance u (cstr_args cdecl)))))))); auto.
      ** eapply wf_local_closed_contextE.
          eapply All_local_env_app_skipn.
          apply wf_subslet_ctxE in projsubs.
          apply projsubs.
      ** elim: p.(proj_arg). simpl. constructor.
        intros n Hn. constructor; auto.
        eapply closed_red1_red.
        split. fvs. cbn. rewrite on_free_vars_mkApps.
        apply/andP; split; fvs.
        eapply red_cofix_proj.
        unfold unfold_cofix. rewrite Hnth. reflexivity.

      ** rewrite -subst_projs_inst.
        have: (p.(proj_arg) = context_assumptions (cstr_args cdecl) -
           (context_assumptions (cstr_args cdecl) - p.(proj_arg))) by lia.
        move=> {1}->. rewrite -skipn_projs map_skipn subst_projs_inst.
        eapply untyped_subslet_skipn. destruct p as [[[? ?] ?] ?]. simpl in *.
        rewrite /indsubst.
        eapply subslet_untyped_subsletE.
        eapply projsubs.

      ** move: Hty.
        move/(PCUICUnivSubstitutionTypEta.isType_subst_instance_declE _ _ _ _ (InductiveDecl mdecl) u _ _).
        unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
        move/(_ _ isdecl'.p1.p1.p1 cu).
        rewrite !subst_instance_app_ctx -app_context_assoc.
        move/(isType_subst_aritiesE isdecl cu).
        rewrite subst_context_app.
        rewrite closed_k_ctx_subst //.
        eapply (declared_inductive_closed_params_instE isdecl).
        move/isType_subst_extended_substE.
        move/(isType_weakenE wfΓ); rewrite app_context_assoc.
        move/(isType_substitutionE sppars).
        rewrite -skipn_subst_instance - !skipn_subst_context.
        rewrite -(subst_context_smash_context _ _ []).
        rewrite subst_instance_smash /=.
        len.
        rewrite length_skipn; len.
        assert (context_assumptions (cstr_args cdecl) -
            (context_assumptions (cstr_args cdecl) - p.(proj_arg)) = p.(proj_arg)) by lia.
        rewrite H.
        move/isType_is_open_termE. len.
        rewrite !length_skipn; len. rewrite H //.
        rewrite subst_instance_subst // /indsubst.
        rewrite subst_instance_inds.
        rewrite (subst_instance_id_mdecl _ _ _ cu) //.
        rewrite subst_instance_extended_subst //.

  - (* Proj Constructor reduction *)
    pose proof (validityE typec).
    simpl in typec.
    pose proof typec as typec'.
    eapply inversion_mkAppsE in typec as [A [tyc tyargs]]; auto.
    eapply (inversion_ConstructE Σ wf) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
    pose proof typec' as typec''.
    destruct (declared_projection_declared_constructorE isdecl declc) as [? []]. subst mdecl' idecl' cdecl'.
    epose proof (declared_projection_type_and_eqE wf isdecl).
    unshelve eapply Construct_Ind_ind_eqE in typec'; eauto.
    destruct (on_declared_constructorE declc) as [[onmind oin] [cs [Hnth onc]]].
    simpl in typec'. simpl in X2.
    eassert (projsubsl := subslet_projsE (args := map (lift0 #|ind_params mdecl|) args) isdecl).
    set(oib := declared_inductive_invE _ wf wf _) in *.
    pose proof (onProjections oib) as onProjs. clearbody oib.
    destruct (isdecl) as [_ [hnth _]].
    destruct (ind_projs idecl).
    eapply nth_error_Some_length in hnth. simpl in hnth.
    lia.
    simpl in *.
    move: (proj2 declc).
    destruct ind_ctors as [|? []] => //. intros [= ->].
    destruct X2 as [[_ projty] projeq].
    destruct typec' as [[[[[_ equ] _] cu] eqargs] [cparsubst [cargsubst [iparsubst [iidxsubst ci]]]]].
    destruct ci as [cparsubst0 iparsubst0 idxsubst0 subsidx [s [typectx [Hpars Hargs]]]].
    destruct ind_cunivs as [|? ?] => //; noconf Hnth.
    specialize (projsubsl onProjs).
    have noidx := (on_projections_indices onProjs).
    destruct onProjs.
    eapply nth_error_alli in on_projs; eauto.
    2:eapply isdecl. simpl in on_projs.
    epose proof (declared_constructor_valid_tyE _ _ _ _ _ 0 cdecl _ wf wfΓ declc Hu) as Hty.
    eapply typing_spine_strengthenE in tyargs; tea.
    rewrite -(firstn_skipn (ind_npars mdecl) args0) in tyargs, H |- *.
    assert(#|firstn (ind_npars mdecl) args0| = ind_npars mdecl).
    rewrite firstn_length_le. lia. lia.
    rewrite nth_error_app_ge in H. rewrite H2.
    pose proof (onNpars onmind).
    pose proof (proj2 (proj2 isdecl)). simpl in *. lia.
    rewrite H2 in H. destruct (proj2 isdecl). simpl in H4.
    destruct p as [pind pnpars parg]. cbn in *. subst pnpars.
    replace (ind_npars mdecl + parg - ind_npars mdecl) with parg in H by lia.
    unfold type_of_constructor in tyargs, Hty.
    rewrite onc.(cstr_eq) in tyargs, Hty.
    rewrite !subst_instance_it_mkProd_or_LetIn !subst_it_mkProd_or_LetIn in tyargs, Hty.
    eapply typing_spine_invE in tyargs as [arg_sub [spargs sp]]; eauto.
    2:{ rewrite !context_assumptions_fold.
        rewrite context_assumptions_subst_instance. rewrite H2.
        apply onNpars in onmind. lia. }
    rewrite closed_ctx_subst in spargs.
    { eapply closed_wf_localE; eauto. eapply on_minductive_wf_paramsE; eauto.
      destruct declc as [[] ?]; eauto. }
    pose proof (spine_subst_inj_substE spargs cparsubst0). subst arg_sub.
    clear Hty.
    rewrite subst_it_mkProd_or_LetIn in sp.
    rewrite !subst_instance_mkApps !subst_mkApps in sp.
    eapply typing_spine_nth_errorE in sp; eauto.
    2:{ rewrite !context_assumptions_fold. rewrite context_assumptions_subst_instance.
        clear sp. eapply nth_error_Some_length in H.
        rewrite List.length_skipn in H. lia. }
    destruct sp as [decl [Hnth Hu0]].
    simpl in on_projs. red in on_projs. len in Hnth.
    eapply (type_ws_cumul_pbE (pb:=Cumul)); eauto.
    { rewrite firstn_skipn.
      unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
      eapply (PCUICUnivSubstitutionTypEta.isType_subst_instance_declE _ _ _ _ _ u wf isdecl'.p1.p1.p1) in projty; eauto.
      apply lift_sorting_f_it_impl with (tu := projty) => // Hs.
      rewrite /= /map_decl /= in Hs.
      eapply (weaken_ctxE Γ) in Hs; auto.
      rewrite (subst_app_simpl [_]).
      destruct projeq as [decl' [hnthargs hty wf' projeq1 projty']].
      eapply (substitution0E (T := tSort _)).
      eapply (substitutionE (Γ' := subst_instance u (smash_context [] (ind_params mdecl)))
        (Δ := [vass _ _]) (T := tSort _)); eauto.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smashE in iparsubst0; auto.
      rewrite subst_instance_smash.
      eapply iparsubst0. exact Hs. simpl.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite [subst_instance_instance _ _](subst_instance_id_mdecl Σ) // subst_instance_to_extended_list.
      rewrite firstn_all2 in iparsubst0. lia.
      eapply spine_subst_smashE in iparsubst0; auto.
      rewrite subst_instance_smash /=.
      rewrite /to_extended_list (spine_subst_subst_to_extended_list_kE iparsubst0).
      assumption. }
    rewrite firstn_skipn.
    rewrite smash_context_app smash_context_acc in on_projs.
    rewrite nth_error_app_lt in on_projs.
    { autorewrite with len. simpl.
      eapply nth_error_Some_length in Hnth. autorewrite with len in Hnth.
      now simpl in Hnth. }
    rewrite nth_error_subst_context in on_projs.
    epose proof (nth_error_lift_context_eq _ (smash_context [] (ind_params mdecl))) as dnth.
    autorewrite with len in dnth. simpl in dnth.
    erewrite -> dnth in on_projs. clear dnth.
    unshelve epose proof (constructor_cumulative_indicesE declc Hu cu equ _ _ _ _ _ spargs iparsubst0 Hpars).
    move: X2.
    set (argsu1 := subst_instance u0 (cstr_args cdecl)) in *.
    set (argsu := subst_instance u (cstr_args cdecl)) in *.
    set (argctxu1 := subst_context _ _ argsu1) in *.
    set (argctxu := subst_context _ _ argsu) in *.
    simpl.
    set (pargctxu1 := subst_context cparsubst 0 argctxu1) in *.
    set (pargctxu := subst_context iparsubst 0 argctxu) in *.
    move=> [cumargs _]; eauto.
    destruct cumargs as [clargs cumargs].
    eapply PCUICRedTypeIrrelevance.All2_fold_nth_ass in cumargs.
    3:eapply smash_context_assumption_context; constructor.
    2:{ unfold pargctxu1, argctxu1, argsu1.
        autorewrite with len in Hnth. eapply Hnth. }
    destruct cumargs as [decl' [Hdecl' cum]].
    rewrite !(smash_context_subst []) in Hnth.
    rewrite -(subst_instance_smash u0 _ []) !nth_error_subst_context nth_error_map in Hnth.
    destruct projeq as [decl'' [Hdecl Hty wfdecl Hty1 Hty2]].
    rewrite Hdecl /= in on_projs, Hnth.
    destruct on_projs as [declna decltyeq declrel].
    noconf Hnth. simpl in *.
    move: Hu0; len.
    assert (parg < context_assumptions (cstr_args cdecl)).
    eapply nth_error_Some_length in H3. lia.
    replace (context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S parg))
      with parg by lia.
    move=> Hu0. rewrite -Hty1 Hty2. clear decltyeq.
    unfold projection_type'.
    set (indsubst1 := inds _ _ _).
    set (projsubst := projs _ _ _).
    rewrite !subst_instance_subst subst_instance_lift !subst_instance_subst.
    epose proof (commut_lift_subst_rec _ _ 1 parg parg ltac:(reflexivity)) as hnarg.
    rewrite Nat.add_1_r in hnarg. rewrite <- hnarg => //. clear hnarg.
    rewrite (subst_app_decomp [_]) !lengths heq_length /= lift_mkApps /=.
    rewrite (distr_subst [_]) /= !lengths.
    rewrite simpl_subst_k // [subst_instance _ projsubst]subst_instance_projs.
    epose proof (subst_app_simpl (List.rev (firstn parg (skipn (ind_npars mdecl) args0))) _ 0) as hs.
    rewrite !lengths /= in hs.
    assert(#|firstn parg (skipn (ind_npars mdecl) args0)| = parg) as hnarg.
    { rewrite firstn_length_le // length_skipn; lia. }
    rewrite hnarg in hs. rewrite <- hs. clear hs. rewrite subst_app_decomp.
    epose proof (subst_app_simpl
      (map (subst0 [mkApps (tConstruct pind 0 u0) (map (lift0 (ind_npars mdecl)) args0)])
        (projs pind (ind_npars mdecl) parg))) as hs.
    rewrite !lengths in hs.
    rewrite -{}hs subst_app_decomp !lengths (distr_subst (List.rev args)) !lengths.
    assert (map (subst0 (List.rev args)) (subst_instance u (extended_subst (ind_params mdecl) 0)) =
      iparsubst) as ->.
    { rewrite firstn_all2 in iparsubst0. lia.
      rewrite subst_instance_extended_subst.
      pose proof (inst_ctx_substE iparsubst0).
      eapply context_subst_extended_subst in X2.
      rewrite X2. eapply map_ext.
      intros. now rewrite subst_inst Upn_0. }
    len in cum. simpl in cum.
    move: Hdecl'.
    rewrite /pargctxu /argctxu /argsu !smash_context_subst_empty -(subst_instance_smash _ _ []).
    rewrite !nth_error_subst_context nth_error_map Hdecl. simpl => [= Hdecl'].
    subst decl'. simpl in cum.
    len in cum; simpl in cum.
    assert(context_assumptions (cstr_args cdecl) -
      S (context_assumptions (cstr_args cdecl) - S parg) = parg) by lia.
    rewrite H5 in cum.
    set (idx := S (context_assumptions (cstr_args cdecl) - S parg)) in *.
    assert (wfpargctxu1 : wf_localE Σ (Γ ,,, skipn idx (smash_context [] pargctxu1))).
    { simpl. apply All_local_env_app_skipn. apply wf_local_smash_endE; auto.
      apply idxsubst0. }
    destruct cum as [[cr mapd] cumdecls].
    destruct decl'' as [na [b|] ty]; simpl in mapd; try discriminate.
    depelim cumdecls. cbn in *. rename eqt into cum.
    eapply (substitution_ws_cumul_pbE_subslet (Γ' := skipn idx (smash_context [] pargctxu1)) (Γ'' := [])
      (s := skipn idx (List.rev (skipn (ind_npars mdecl) args0)))) in cum.
    2:{ eapply spine_subst_smashE in idxsubst0; eauto.
        eapply subslet_skipnE, idxsubst0. }
    assert (skipn idx (List.rev (skipn (ind_npars mdecl) args0)) = (List.rev (firstn parg (skipn (ind_npars mdecl) args0)))) as eq.
    { rewrite /idx skipn_rev. lia_f_equal. rewrite length_skipn; lia. }
    assert (parg = #|List.rev (firstn parg (skipn (ind_npars mdecl) args0))|) as hnarg'.
    { rewrite !lengths firstn_length_le ?length_skipn; lia. }
    rewrite eq in cum.
    rewrite subst_context_nil in cum. simpl in cum.
    rewrite -(subst_app_simpl' _ _ 0) in cum => //.
    rewrite subst_app_decomp in cum.
    etransitivity; [eapply cum|clear cum].
    rewrite -(subst_app_simpl' _ _ 0) //.
    rewrite subst_app_decomp.
    rewrite (subslet_lengthE iparsubst0); len.
    assert (wf_localE Σ (Γ ,,, subst_instance u (ind_params mdecl))).
    { eapply PCUICWeakeningTypEta.weaken_wf_localE; eauto. eapply on_minductive_wf_paramsE => //. pcuic.
      apply declc. }
    eapply (substitution_ws_cumul_pbE_subslet (Γ'' := [])); eauto. eapply iparsubst0.
    simpl.
    rewrite (distr_subst_rec _ _ _ #|ind_params mdecl| 0); len => /=.
    rewrite /indsubst1 subst_instance_inds.
    rewrite (subst_instance_id_mdecl Σ u mdecl) //.
    rewrite (subst_closedn (List.rev args)).
    { eapply (closedn_subst _ 0).
      eapply closed_inds.
      simpl; len.
      rewrite closedn_subst_instance.
      clear projsubsl.
      eapply closed_wf_localE in wfdecl.
      rewrite closedn_ctx_app in wfdecl.
      move/andb_and: wfdecl => [_ wfdecl]. len in wfdecl.
      simpl in wfdecl.
      eapply closedn_ctx_decl in wfdecl; eauto.
      len in wfdecl.
      simpl in wfdecl.
      eapply closed_upwards. eauto.
      lia. auto. }
    assert (ind_npars mdecl = #|List.rev args|) as eqargs'. len.
    rewrite map_map_compose map_subst_lift0_subst -(map_map_compose _ _ _ (subst0 _)).
    rewrite subst_projs_inst projs_inst_subst subst_mkApps /=.
    rewrite {3}eqargs' map_map_compose map_subst_lift_id.
    eapply (weakeningE _ _ ((ind_params mdecl)@[u])) in typec'' => //.
    rewrite !lift_mkApps in typec''. len in typec''.
    eapply (substitution_ws_cumul_pb_subst_convE (Γ := _ ,,, _) (Δ := [])); auto.
    { rewrite -(subst_instance_length u).
      eapply subslet_liftE; eauto. rewrite -eq.
      eapply spine_subst_smashE in idxsubst0; eauto.
      eapply subslet_skipnE. eapply idxsubst0. }
    { specialize (projsubsl (Γ ,,, subst_instance u (ind_params mdecl))).
      rewrite -projs_inst_lift.
      rewrite -{1}H5 -projs_inst_skipn.
      specialize (projsubsl (lift0 #|ind_params mdecl| (mkApps (tConstruct pind 0 u0) args0)) u).
      forward projsubsl.
      rewrite lift_mkApps //.
      eapply wf_subslet_skipnE, projsubsl. }
    { eapply All2_map.
      eapply All2_from_nth_error.
      { autorewrite with len. lia. }
      intros n x x' Hn nth nth'.
      rewrite nth_error_projs_inst in nth'.
      lia. noconf nth'.
      rewrite /= lift_mkApps /=.
      symmetry. eapply red_ws_cumul_pbE.
      eapply closed_red1_red.
      eapply wt_closed_red1E.
      { eapply nth_error_Some_length in H3.
        have: parg - S n < #|ind_projs idecl| by lia.
        clear hnth.
        move/nth_error_Some' => [pdecl' hnth].
       eexists. econstructor; tea. split; [eapply isdecl|]. cbn. split => //. tea. len. }
      constructor.
      eapply (f_equal (option_map (lift0 #|ind_params mdecl|))) in nth.
      simpl in nth. rewrite -nth nth_error_map. f_equal.
      rewrite nth_error_rev_inv; autorewrite with len; try lia.
      rewrite hnarg.
      rewrite firstn_skipn_comm nth_error_skipn.
      rewrite -{1}[args0](firstn_skipn (ind_npars mdecl + parg)).
      rewrite nth_error_app1 // firstn_length_le; autorewrite with len; try lia. cbn. lia. }
    { simpl. autorewrite with len.
      rewrite -(subst_instance_length u (ind_params mdecl)).
      simpl. eapply ws_cumul_pbE_refl.
      rewrite -skipn_lift_context.
      eapply wf_local_closed_contextE.
      eapply All_local_env_app_skipn.
      eapply weakening_wf_localE => //.
      eapply wf_local_smash_endE, idxsubst0.
      move: Hty.
      unshelve epose proof (declc' := declared_constructor_to_gen declc); eauto.
      move/(PCUICUnivSubstitutionTypEta.isType_subst_instance_declE _ _ _ _ (InductiveDecl mdecl) u _ _).
      rewrite !subst_instance_app_ctx -app_context_assoc.
      intro foo. pose (fun x y z => isType_subst_aritiesE isdecl cu (foo x y z)).
      move:i. clear foo.
      intro foo. pose (fun x y z => isType_is_open_termE _ _ (foo x y z)).
      move:i. clear foo. len.
      rewrite length_skipn; len.
      assert (context_assumptions (cstr_args cdecl) -
          (context_assumptions (cstr_args cdecl) - parg) = parg) by lia.
      cbn. rewrite H6.
      rewrite length_skipn; len. rewrite H5. intro foo.
      eapply on_free_vars_impl; [| eapply foo]; eauto.
      move=> i'. rewrite /shiftnP !orb_false_r.
      move/Nat.ltb_lt => lt. apply/Nat.ltb_lt. lia. }

  - (* Proj congruence: discriminee reduction *)
    eapply type_ws_cumul_pbE; [econstructor|..]; eauto.
    eapply validityE; eauto.
    instantiate (1:= tProj p c).
    econstructor; eauto.
    eapply ws_cumul_pbE_eq_le.
    rewrite (subst_app_simpl [c']) (subst_app_simpl [c]).
    set(bann := {| binder_name := nAnon; binder_relevance := idecl.(ind_relevance) |}).
    eapply (untyped_substitution_ws_cumul_pbE_subst_conv (Γ := Γ)
      (Γ' := []) (Δ := [vass bann (mkApps (tInd p.(proj_ind) u) args)])
      (Δ' := [vass bann (mkApps (tInd p.(proj_ind) u) args)])); auto.
    4-5:repeat constructor.
    * symmetry. apply red_terms_ws_cumul_pbE_terms; constructor; auto.
      now apply closed_red1_red.
    * rewrite on_free_vars_ctx_app andb_true_r on_free_vars_ctx_app H /=.
      cbn. rewrite shiftnP_add /=.
      move/validityE/isType_is_open_termE: typec => -> //.
    * rewrite on_free_vars_ctx_app andb_true_r on_free_vars_ctx_app H /=.
      cbn. rewrite shiftnP_add /=.
      move/validityE/isType_is_open_termE: typec => -> //.
    * have := (declared_projection_type_and_eqE wf isdecl).
      move=> [[hctors isTy] Hdecl].
      move/validityE/(isType_mkApps_Ind_proj_invE _ isdecl): typec => [sppars hpars hargs cu].
      move/(PCUICUnivSubstitutionTypEta.isType_subst_instance_declE _ _ _ _ (InductiveDecl mdecl) u _ _) : isTy.
      unshelve epose proof (isdecl' := declared_projection_to_gen isdecl); eauto.
      move/(_ _ isdecl'.p1.p1.p1 cu).
      move/(isType_weakenE wfΓ).
      rewrite [_@[u]](subst_instance_app_ctx _ _ [_]).
      rewrite app_context_assoc subst_instance_smash.
      move/(isType_substitutionE sppars) => /=. len.
      move/isType_is_open_termE => /=. now cbn.
Qed.

(** *** Premise 14: fixpoints; the impossible step ([:3328-3331]), a type step ([:3333-3419],
    with the witness transported by [mfix_on_ind_red1_typeE]) and a body step ([:3420-3476]).
    Base's algorithmic context conversion [conv_context cumulAlgo_gen] is
    [conv_context (@JoinE cf)], built from [conv_decls_fix_contextE] with [ws_cumul_pbE_forget]. *)
Lemma sr_red1E_Fix {cf : checker_flags} : ltac:(sr_case_type cf 13).
Proof.
  sr_intro. sr_pre.
  - (* Fix congruence *)
    match goal with H : mkApps (tFix _ _) _ = _ |- _ =>
      apply mkApps_Fix_spec in H; simpl in H; subst args end.
    simpl. destruct narg; discriminate.

  - (* Fix congruence: type reduction *)
    match goal with H : wf_fixpointE _ _ _ |- _ => rename H into wffix end.
    match goal with H : OnOne2 _ mfix mfix1 |- _ => rename H into X4 end.
    match goal with H : is_true (forallb (test_def _ _) mfix) |- _ => rename H into H2 end.
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : conv_context (@JoinE cf) Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf wfΓ X X4 H2 fixl F18.
      eapply All2_fold_app => //.
      reflexivity.
      eapply All2_fold_impl.
      eapply (conv_decls_fix_contextE (Γ := Γ)) => //.
      move: H2.
      assert (clΓ := wf_local_closed_contextE wfΓ).
      clear fixl. move: #|mfix|. induction X4; constructor.
      * destruct p as [[r p] e]. noconf e. split.
        now apply closed_red1_ws_cumul_pbE. rewrite H. reflexivity.
      * cbn in H2. move/andP: H2 => [_ Htl].
        eapply forallb_All in Htl. eapply All_All2; tea.
        move=> [dname dty dbod] /= h. rewrite /test_def /=;
        move/andP=> [hty _]. split; try reflexivity.
        eapply ws_cumul_pbE_refl => //.
      * move/andP: H2 => [/andP [Hty _] _].
        split; try reflexivity. apply ws_cumul_pbE_refl => //.
      * eapply IHX4. simpl in H2; now move/andP: H2 => [].
      * cbn. intros ???? []; constructor; eauto; now apply ws_cumul_pbE_forget. }
    assert (All (on_def_type (lift_typing typingE Σ) Γ) mfix1).
    { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        destruct d as [na ty bo ra], d' as [na' ty' bo' ra']; cbn in *; noconf eq.
        rewrite /on_def_type /=.
        apply lift_sorting_it_impl_gen with HT' => //; now intros [_ IH]. }
    assert (wf_localE Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wfE; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_altE.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0);
        [ apply wfE_wf_cases_env
        | eapply wf_local_wf_cases_ctxE; tea
        | | eauto ].
      constructor; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
      apply (OnOne2_All_All X4 X3).
      + intros d Hj.
        unfold on_def_body. rewrite -fixl.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT IHT.
        eapply context_conversionE; eauto.
      + move=> [na ty b rarg] [na' ty' b' rarg'] [[[red Hred] eq] HT] HB.
        rewrite /= in red, Hred, eq, HB, HT.
        noconf eq.
        destruct HB as ((Hb & IHb) & s & (Ht & IHt) & e & er); cbn in *.
        eassert (Σ ;;; Γ ,,, _ |-E lift0 _ ty' : tSort s).
        2: repeat (eexists; cbn). 4: eassumption.
        2,3: eapply context_conversionE; eauto.
        all: rewrite -fixl.
        { eapply IHt. eapply (weakening_closed_red1_cb (Γ' := [])); eauto. now eapply wf_local_closed_contextE. }
        eapply type_Cumul_altE. eapply Hb.
        eapply has_sort_isTypeE. rewrite fixl. eassumption.
        apply JoinE_red_l, red1_red.
        eapply (weakening_red1_cb _ []); [exact _| |eapply red].
        pose proof (Hs := HT.2.π2.1.1).
        eapply subject_closedE in Hs.
        eapply (closedn_on_free_vars (P:=xpredT)) in Hs.
        now eapply on_free_vars_any_xpredT.

    * destruct wffix as [isl [hr hm]].
      have o : OnOne2 (fun x y : def term => Σ ;;; Γ ⊢ dtype x ⇝ dtype y
          × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix mfix1.
      { eapply OnOne2_impl; tea; cbn; intros x y [[r _] e];
          split; [now eapply closed_red1_red|exact e]. }
      split; [|split].
      + eapply (forallb_OnOne2 o); [|exact isl].
        intros x y [_ e]; cbn. now case: e => _ -> _.
      + eapply (forallb_OnOne2 o); [|exact hr].
        intros [na ty bo ra] [na' ty' bo' ra'] [r e]; cbn in r, e.
        case: e => <- <- <-.
        exact (red_has_rec_arg_cb (d := {| dname := na; dtype := ty; dbody := bo; rarg := ra |}) r).
      + exact (mfix_on_ind_red1_typeE Γ mfix mfix1 o hm).
    * eapply isTypeRelE_isTypeE. eapply All_nth_error in X0; eauto.
    * destruct disj as [<-|[[red Hred] eq]].
      + apply JoinE_refl.
      + apply JoinE_red_r, red1_red, red.

  - (* Fix congruence in body *)
    match goal with H : wf_fixpointE _ _ _ |- _ => rename H into wffix end.
    match goal with H : OnOne2 _ mfix mfix1 |- _ => rename H into X4 end.
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf X4.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction X4.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n'; f_equal. apply IHX4. }
    assert (All (on_def_type (lift_typing typingE Σ) Γ) mfix1).
    { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        destruct d as [na ty bo ra], d' as [na' ty' bo' ra']; cbn in *; noconf eq.
        unfold on_def_type in HT' |- *; cbn in *.
        apply lift_typing_impl with (1 := HT'); now intros ?? []. }
    assert (wf_localE Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wfE; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_altE.
    econstructor; eauto.
    * eapply (fix_guard_red1 _ _ _ _ 0);
        [ apply wfE_wf_cases_env
        | eapply wf_local_wf_cases_ctxE; tea
        | | eauto ].
      apply fix_red_body; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
       apply (OnOne2_All_All X4 X3).
      + intros d Hj.
        rewrite -convctx.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT //.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[[red IH] eq] HT] HB.
        noconf eq.
        rewrite -convctx.
        apply lift_sorting_it_impl_gen with HB => //= [] [Ht IHt] //. eauto.
    * destruct wffix as [isl [hr hm]].
      have o : OnOne2 (fun x y : def term =>
          closed_red1 Σ (Γ ,,, fix_context mfix) (dbody x) (dbody y)
          × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix mfix1.
      { eapply OnOne2_impl; tea; cbn; intros x y [[r _] e]; split; [exact r|exact e]. }
      split; [|split].
      + eapply (forallb_OnOne2 o); [|exact isl].
        intros x y [r _] h; cbn in h |- *.
        exact (isLambda_red1 _ _ _ _ h (clrel_rel r)).
      + eapply (forallb_OnOne2 o); [|exact hr].
        intros [na ty bo ra] [na' ty' bo' ra'] [_ e] h; cbn in e.
        case: e => <- <- <-. exact h.
      + exact (mfix_on_ind_red1_body _ mfix mfix1 o hm).
    * eapply isTypeRelE_isTypeE. eapply All_nth_error in X0; eauto.
    * destruct disj as [<-|[_ eq]]; [apply JoinE_refl|].
      destruct decl as [na ty bo ra], decl' as [na' ty' bo' ra']; cbn in *; noconf eq.
      apply JoinE_refl.
Qed.

(** *** Premise 15: cofixpoints; a type step ([:3478-3553]) and a body step ([:3555-3600]) *)
Lemma sr_red1E_CoFix {cf : checker_flags} : ltac:(sr_case_type cf 14).
Proof.
  sr_intro. sr_pre.
  - (* CoFix congruence: type reduction *)
    match goal with H : wf_cofixpointE _ _ _ |- _ => rename H into wffix end.
    match goal with H : OnOne2 _ mfix mfix1 |- _ => rename H into X4 end.
    match goal with H : is_true (forallb (test_def _ _) mfix) |- _ => rename H into H2 end.
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : conv_context (@JoinE cf) Σ (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix1)).
    { clear -wf wfΓ X X4 H2 fixl F18.
      eapply All2_fold_app => //; trea.
      eapply All2_fold_impl.
      eapply (conv_decls_fix_contextE (Γ := Γ)) => //.
      move: H2.
      assert (clΓ := wf_local_closed_contextE wfΓ).
      clear fixl. move: #|mfix|. induction X4; constructor.
      * destruct p as [[r p] e]. noconf e. split.
        now apply closed_red1_ws_cumul_pbE. rewrite H. reflexivity.
      * cbn in H2. move/andP: H2 => [_ Htl].
        eapply forallb_All in Htl. eapply All_All2; tea.
        move=> [dname dty dbod] /= h. rewrite /test_def /=;
        move/andP=> [hty _]. split; try reflexivity.
        eapply ws_cumul_pbE_refl => //.
      * move/andP: H2 => [/andP [Hty _] _].
        split; try reflexivity. apply ws_cumul_pbE_refl => //.
      * eapply IHX4. simpl in H2; now move/andP: H2 => [].
      * cbn. intros ???? []; constructor; eauto; now apply ws_cumul_pbE_forget. }
    assert (All (on_def_type (lift_typing typingE Σ) Γ) mfix1).
      { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        destruct d as [na ty bo ra], d' as [na' ty' bo' ra']; cbn in *; noconf eq.
        rewrite /on_def_type /=.
        apply lift_sorting_it_impl_gen with HT' => //. now intros [_ IH]. }
    assert (wf_localE Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wfE; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_altE.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0);
        [ apply wfE_wf_cases_env
        | eapply wf_local_wf_cases_ctxE; tea
        | | eauto ].
      constructor; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
      apply (OnOne2_All_All X4 X3).
      + intros d Hj.
        unfold on_def_body. rewrite -fixl.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT IHT.
        eapply context_conversionE; eauto.
      + move=> [na ty b rarg] [na' ty' b' rarg'] [[[red Hred] eq] HT] HB.
        rewrite /= in red, Hred, eq, HB, HT.
        noconf eq.
        destruct HB as ((Hb & IHb) & s & (Ht & IHt) & e & er); cbn in *.
        eassert (Σ ;;; Γ ,,, _ |-E lift0 _ ty' : tSort s).
        2: repeat (eexists; cbn). 4: eassumption.
        2,3: eapply context_conversionE; eauto.
        all: rewrite -fixl.
        { eapply IHt. eapply (weakening_closed_red1_cb (Γ' := [])); eauto. now eapply wf_local_closed_contextE. }
        eapply type_Cumul_altE. eapply Hb.
        eapply has_sort_isTypeE. rewrite fixl. eassumption.
        apply JoinE_red_l, red1_red.
        eapply (weakening_red1_cb _ []); [exact _| |eapply red].
        pose proof (Hs := HT.2.π2.1.1).
        eapply subject_closedE in Hs.
        eapply (closedn_on_free_vars (P:=xpredT)) in Hs.
        now eapply on_free_vars_any_xpredT.

    * eapply mfix_on_ind_red1_typeE; [|exact wffix].
      eapply OnOne2_impl; tea; cbn; intros x y [[r _] e];
        split; [now eapply closed_red1_red|exact e].
    * eapply isTypeRelE_isTypeE. eapply All_nth_error in X0; eauto.
    * destruct disj as [<-|[[red Hred] eq]].
      + apply JoinE_refl.
      + apply JoinE_red_r, red1_red, red.

  - (* CoFix congruence in body *)
    match goal with H : wf_cofixpointE _ _ _ |- _ => rename H into wffix end.
    match goal with H : OnOne2 _ mfix mfix1 |- _ => rename H into X4 end.
    assert(fixl :#|fix_context mfix| = #|fix_context mfix1|) by now (rewrite !fix_context_length; apply (OnOne2_length X4)).
    assert(convctx : fix_context mfix = fix_context mfix1).
    { clear -wf X4.
      change fix_context with (fix_context_gen 0).
      generalize 0. induction X4.
      destruct p as [_ eq]. noconf eq. simpl in H; noconf H.
      simpl. intros. now rewrite H H0.
      simpl. intros n'; f_equal. apply IHX4. }
    assert (All (on_def_type (lift_typing typingE Σ) Γ) mfix1).
    { apply (OnOne2_All_All X4 X1).
      * intros d HT.
        apply lift_typing_impl with (1 := HT); now intros ?? [Hty _].
      * intros d d' [[red _] eq] HT'.
        destruct d as [na ty bo ra], d' as [na' ty' bo' ra']; cbn in *; noconf eq.
        unfold on_def_type in HT' |- *; cbn in *.
        apply lift_typing_impl with (1 := HT'); now intros ?? []. }
    assert (wf_localE Σ (Γ ,,, fix_context mfix1)).
    { apply All_mfix_wfE; auto. }
    destruct (OnOne2_nth_error _ _ _ decl _ X4 heq_nth_error) as [decl' [eqnth disj]].
    eapply type_Cumul_altE.
    econstructor; eauto.
    * eapply (cofix_guard_red1 _ _ _ _ 0);
        [ apply wfE_wf_cases_env
        | eapply wf_local_wf_cases_ctxE; tea
        | | eauto ].
      apply cofix_red_body; eauto.
      eapply OnOne2_impl; tea; cbn; intuition auto.
      apply a2. apply a2.
    * eapply (OnOne2_All_mix_left X1) in X4.
       apply (OnOne2_All_All X4 X3).
       + intros d Hj.
        rewrite -convctx.
        eapply lift_typing_impl with (1 := Hj) => ?? [] HT //.
      + move=> [na ty b rarg] [na' ty' b' rarg'] /= [[[red IH] eq] HT] HB.
        noconf eq.
        rewrite -convctx.
        apply lift_sorting_it_impl_gen with HB => //= [] [Ht IHt] //. eauto.
    * eapply (mfix_on_ind_red1_body (closed_red1 Σ (Γ ,,, fix_context mfix))); [|exact wffix].
      eapply OnOne2_impl; tea; cbn; intros x y [[r _] e]; split; [exact r|exact e].
    * eapply isTypeRelE_isTypeE. eapply All_nth_error in X0; eauto.
    * destruct disj as [<-|[_ eq]]; [apply JoinE_refl|].
      destruct decl as [na ty bo ra], decl' as [na' ty' bo' ra']; cbn in *; noconf eq.
      apply JoinE_refl.
Qed.

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

(** *** The theorem *)

(** Base [sr_red1] ([:1942]). *)
Lemma sr_red1E {cf:checker_flags} :
  env_propE SR_red1E
    (fun Σ Γ j =>
      lift_typing0 (fun t T => Σ ;;; Γ |-E t : T × forall u, Σ ;;; Γ ⊢ t ⇝1 u -> Σ ;;; Γ |-E u : T) j)
      (fun Σ Γ => wf_localE Σ Γ ×
        (forall Γ' Δ' Δ,
          Γ = Γ' ,,, Δ' ->
          OnOne2_local_env (fun Δ : context => on_one_decl (closed_red1 Σ (Γ',,, Δ))) Δ' Δ ->
          wf_local_relE Σ Γ' Δ)).
Proof.
  apply typingE_ind_env.
  - exact sr_red1E_Pj.
  - exact sr_red1E_ctx.
  - exact sr_red1E_Rel.
  - exact sr_red1E_Sort.
  - exact sr_red1E_Prod.
  - exact sr_red1E_Lambda.
  - exact sr_red1E_LetIn.
  - exact sr_red1E_App.
  - exact sr_red1E_Const.
  - exact sr_red1E_Ind.
  - exact sr_red1E_Construct.
  - exact sr_red1E_Case.
  - exact sr_red1E_Proj.
  - exact sr_red1E_Fix.
  - exact sr_red1E_CoFix.
  - exact sr_red1E_Prim.
  - exact sr_red1E_Cumul.
Qed.

(** ** Corollaries ([:3634-3703]) *)

(** Base [sr_stmt] ([:3634]). *)
Definition sr_stmtE {cf:checker_flags} (Σ : global_env_ext) Γ t T :=
  forall u, red Σ Γ t u -> Σ ;;; Γ |-E u : T.

(** Base [typing_closed_red1] ([:3637]). *)
Lemma typing_closed_red1E {cf:checker_flags} {Σ : global_env_ext} {Γ t u T} {wfΣ : wfE Σ} :
   Σ ;;; Γ |-E t : T ->
   red1 Σ Γ t u ->
   Σ ;;; Γ ⊢ t ⇝1 u.
Proof.
  intros Ht hr. split; auto.
  * now apply typingE_wf_local, wf_local_closed_contextE in Ht.
  * now eapply subject_is_open_termE.
Qed.

(** Base [typing_closed_red] ([:3647]). *)
Lemma typing_closed_redE {cf:checker_flags} {Σ : global_env_ext} {Γ t u T} {wfΣ : wfE Σ} :
   Σ ;;; Γ |-E t : T ->
   red Σ Γ t u ->
   Σ ;;; Γ ⊢ t ⇝ u.
Proof.
  intros Ht hr. split; auto.
  * now apply typingE_wf_local, wf_local_closed_contextE in Ht.
  * now eapply subject_is_open_termE.
Qed.

(** Base [subject_reduction1] ([:3657]). *)
Lemma subject_reduction1E {cf Σ} {wfΣ : wfE Σ} {Γ t u T}
  : Σ ;;; Γ |-E t : T -> red1 Σ Γ t u -> Σ ;;; Γ |-E u : T.
Proof.
  intros. eapply (env_propE_typing sr_red1E); tea.
  now eapply typing_closed_red1E.
Qed.

(** Base [subject_reduction] ([:3664]); the field [subject_reduction] of [T1_facts]. *)
Theorem subject_reductionE {cf:checker_flags} :
  forall (Σ : global_env_ext) Γ t u T, wfE Σ -> Σ ;;; Γ |-E t : T -> red Σ Γ t u -> Σ ;;; Γ |-E u : T.
Proof.
  intros * wfΣ Hty Hred.
  induction Hred; eauto.
  eapply (env_propE_typing sr_red1E); eauto.
  now eapply typing_closed_red1E.
Qed.

(** Base [subject_reduction1_closed] ([:3673]). *)
Corollary subject_reduction1_closedE {cf:checker_flags} :
  forall (Σ : global_env_ext) Γ t u T, wfE Σ ->
  Σ ;;; Γ |-E t : T -> Σ ;;; Γ ⊢ t ⇝1 u -> Σ ;;; Γ |-E u : T.
Proof.
  intros * wfΣ Hty Hred.
  now eapply (env_propE_typing sr_red1E).
Qed.

(** Base [subject_reduction_closed] ([:3681]). *)
Corollary subject_reduction_closedE {cf:checker_flags} :
  forall (Σ : global_env_ext) Γ t u T, wfE Σ ->
  Σ ;;; Γ |-E t : T -> Σ ;;; Γ ⊢ t ⇝ u -> Σ ;;; Γ |-E u : T.
Proof.
  intros * wfΣ Hty Hred.
  eapply subject_reductionE; tea. apply Hred.
Qed.

(** Base [type_reduction] ([:3689]). Base's [conv_cumul] of [PCUICCumulativity.red_conv] is
    [JoinE_red_l]. *)
Lemma type_reductionE {cf} {Σ} {wfΣ : wfE Σ} {Γ t A B} :
  Σ ;;; Γ |-E t : A -> red Σ Γ A B -> Σ ;;; Γ |-E t : B.
Proof.
  intros Ht Hr.
  eapply type_Cumul_altE. eassumption.
  apply lift_sorting_it_impl_gen with (validityE Ht) => // HA.
  eapply subject_reductionE; eassumption.
  now apply JoinE_red_l.
Qed.

(** Base [type_reduction_closed] ([:3699]); the field [type_reduction_closed] of [T1_facts]. *)
Lemma type_reduction_closedE {cf} {Σ} {wfΣ : wfE Σ} {Γ t A B} :
  Σ ;;; Γ |-E t : A -> Σ ;;; Γ ⊢ A ⇝ B -> Σ ;;; Γ |-E t : B.
Proof.
  intros Ht Hr. eapply type_reductionE; tea. exact Hr.
Qed.

(** ** Base section [SRContext] ([:3705-3976]). Its syntactic lemmas ([red1_ctx_app],
    [red1_red_ctx], [closed_red1_ctx], [red_ctx_clos_rt_red1_ctx],
    [eq_context_upto_names_upto_names], [red_ctx_app_context_l]) are base's. *)
Section SRContextE.
  Context {cf:checker_flags}.

  (** Base [wf_local_isType_nth] ([:3739]). *)
  Lemma wf_local_isType_nthE {Σ} {wfΣ : wfE Σ} Γ n decl :
    wf_localE Σ Γ ->
    nth_error Γ n = Some decl ->
    ∑ s, Σ ;;; Γ |-E lift0 (S n) (decl_type decl) : tSort s.
  Proof.
    intros wfΓ Hnth.
    eapply All_local_env_nth_error in wfΓ as H; tea.
    apply nth_error_Some_length in Hnth.
    destruct H as (_ & s & Hs & _).
    eapply weakeningE with (Γ' := firstn (S n) Γ) in Hs; cbn in Hs; eauto.
    2: rewrite /app_context firstn_skipn //.
    rewrite firstn_length_le // /app_context firstn_skipn in Hs.
    now eexists.
  Qed.

  (** Base [subject_reduction_ctx] ([:3757]). Base's algorithmic context conversion
      [conv_context cumulAlgo_gen] is [conv_context (@JoinE cf)]; its [red_conv] steps are
      [JoinE_red_l]. *)
  Lemma subject_reduction_ctxE {Σ} {wfΣ : wfE Σ} Γ Γ' t T :
    red1_ctx Σ Γ Γ' ->
    Σ ;;; Γ |-E t : T -> Σ ;;; Γ' |-E t : T.
  Proof.
    assert(OnOne2_local_env
      (fun (Δ : context) => on_one_decl
         (fun (t t' : term) => red1 Σ.1 Δ t t')) Γ Γ' ->
         conv_context (@JoinE cf) Σ Γ Γ').
    { clear. induction 1.
      - destruct p as [<- r]. constructor; auto.
        reflexivity. constructor. reflexivity.
        now apply JoinE_red_l, red1_red.
      - destruct p; subst. constructor.
        reflexivity.
        destruct s as [[red ->]|[red ->]].
        all: constructor; try reflexivity; try apply JoinE_refl; now apply JoinE_red_l, red1_red.
      - constructor; auto.
        destruct d as [na [b|] ty]; constructor; try reflexivity; apply JoinE_refl. }
    intros r H.
    specialize (X r).
    assert(wf_localE Σ Γ').
    apply typingE_wf_local in H.
    induction H in Γ', r, X |-  *; depelim r.
    - constructor; auto. cbn in o.
      destruct o as [<- r].
      apply lift_sorting_it_impl_gen with t1 => // Hs.
      eapply subject_reduction1E in Hs; eauto.
    - depelim X.
      constructor; auto.
      apply lift_sorting_it_impl_gen with t1 => // Hs.
      eapply context_conversionE; eauto.
    - depelim X.
      destruct o as [<- [[r ->]|[r <-]]].
      all: constructor; auto.
      all: apply lift_sorting_it_impl_gen with t1 => // Hs.
      + eapply type_reductionE; tea. pcuic.
      + eapply subject_reduction1E; eauto.
      + eapply subject_reduction1E; eauto.
    - depelim X.
      constructor; auto.
      apply lift_sorting_it_impl_gen with t1 => // Hs.
      all: eapply context_conversionE; eauto.
    - eapply context_conversionE; eauto.
  Qed.

  (** Base [wf_local_red1] ([:3804]). *)
  Lemma wf_local_red1E {Σ} {wfΣ : wfE Σ} {Γ Γ'} :
    red1_ctx Σ Γ Γ' -> wf_localE Σ Γ -> wf_localE Σ Γ'.
  Proof.
    induction 1; cbn in *.
    - destruct p as [-> r]. intro e. inversion e; subst; cbn in *.
      constructor; tas.
      apply lift_sorting_it_impl_gen with X0 => // Hs.
      eapply subject_reduction1E; tea.
    - intro e. inversion e; subst; cbn in *.
      destruct p as [-> [[? []]|[? []]]]; constructor; cbn; tas.
      all: apply lift_sorting_it_impl_gen with X0 => // Hs.
      + eapply type_reductionE; tea. pcuic.
      + eapply subject_reduction1E; tea.
      + eapply subject_reduction1E; tea.
    - intro H; inversion H; subst; constructor; cbn in *; auto.
      all: apply lift_sorting_it_impl_gen with X1 => // Hs.
      all: eapply subject_reduction_ctxE; tea.
  Qed.

  (** Base [wf_local_red] ([:3846]). *)
  Lemma wf_local_redE {Σ} {wfΣ : wfE Σ} {Γ Γ'} :
    red_ctx Σ Γ Γ' -> wf_localE Σ Γ -> wf_localE Σ Γ'.
  Proof.
    intros h. red in h. apply red_ctx_clos_rt_red1_ctx in h.
    induction h; eauto using wf_local_red1E.
  Qed.

  (** Base [wf_local_subst1] ([:3861]). *)
  Lemma wf_local_subst1E {Σ} {wfΣ : wfE Σ} Γ na b t Γ' :
      wf_localE Σ (Γ ,,, [],, vdef na b t ,,, Γ') ->
      wf_localE Σ (Γ ,,, subst_context [b] 0 Γ').
  Proof.
    induction Γ' as [|d Γ']; [now inversion 1|].
    change (d :: Γ') with (Γ' ,, d).
    destruct d as [na' [bd|] ty]; rewrite !app_context_cons; intro HH.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *.
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subsletE Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_defE Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_localE_app_l in X. inversion X; subst; cbn in *; now eapply unlift_TermTyp.
      }
      constructor; cbn; auto.
      apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
      eapply substitutionE; tea.
    - rewrite subst_context_snoc0. simpl.
      inversion HH; subst; cbn in *.
      change (Γ,, vdef na b t ,,, Γ') with (Γ ,,, [vdef na b t] ,,, Γ') in *.
      assert (subsletE Σ Γ [b] [vdef na b t]). {
        pose proof (cons_let_defE Σ Γ [] [] na b t) as XX.
        rewrite !subst_empty in XX. apply XX. constructor.
        apply wf_localE_app_l in X. inversion X; subst; cbn in *; now eapply unlift_TermTyp. }
      constructor; cbn; auto.
      apply lift_typing_f_impl with (1 := X0) => // ?? Hs.
      eapply substitutionE; tea.
  Qed.

  (** Base [isType_red1] ([:3899]). *)
  Lemma isType_red1E {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ A B} :
     isTypeE Σ Γ A ->
     red1 Σ Γ A B ->
     isTypeE Σ Γ B.
  Proof.
    intros HT red.
    apply lift_sorting_it_impl_gen with HT => // Hs.
    eapply subject_reduction1E; eauto.
  Qed.

  (** Base [isWfArity_red1] ([:3909]). *)
  Lemma isWfArity_red1E {Σ} {wfΣ : wfE Σ} {Γ A B} :
    isWfArityE Σ Γ A ->
    red1 Σ Γ A B ->
    isWfArityE Σ Γ B.
  Proof.
    intros [isty H] re.
    split. eapply isType_red1E; eauto.
    clear isty; revert H.
    induction re using red1_ind_all.
    (* red_prim_op: a tConst-headed application is not an arity. *)
    all: try (intros [?ctxp [?sp Hdp]];
              match type of Hdp with
              | destArity [] (mkApps (tConst _ _) (map term_of_lit ?ls)) = _ =>
                  destruct ls using MRList.rev_ind;
                  [ cbn in Hdp; discriminate
                  | rewrite map_app mkApps_app in Hdp; cbn in Hdp; discriminate ]
              end).
    all: intros [ctx [s H1]]; cbn in *; try discriminate.
    - rewrite destArity_app in H1.
      case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
        [|rewrite ee in H1; discriminate].
      pose proof (subst_destArity [] b' [b] 0) as H; cbn in H.
      rewrite ee in H. eexists _, s'. eassumption.
    - rewrite destArity_tFix in H1; discriminate.
    - rewrite destArity_app in H1.
      case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
        rewrite ee in H1; [|discriminate].
      eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
    - rewrite destArity_app in H1.
      case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
        rewrite ee in H1; [|discriminate].
      eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
    - rewrite destArity_app in H1.
      case_eq (destArity [] b'); [intros [ctx' s']|]; intro ee;
        rewrite ee in H1; [|discriminate].
      forward IHre. { eexists _, s'; tea. }
      destruct IHre as [ctx'' [s'' ee']].
      eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
    - rewrite destArity_app in H1.
      case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
        rewrite ee in H1; [|discriminate].
      eexists _, s'. cbn. rewrite destArity_app ee. reflexivity.
    - rewrite destArity_app in H1.
      case_eq (destArity [] M2); [intros [ctx' s']|]; intro ee;
        rewrite ee in H1; [|discriminate].
      forward IHre. { eexists _, s'; tea. }
      destruct IHre as [ctx'' [s'' ee']].
      eexists _, s''. cbn. rewrite destArity_app ee'. reflexivity.
  Qed.

  (** Base [isWfArity_red] ([:3959]). *)
  Lemma isWfArity_redE {Σ} {wfΣ : wfE Σ} {Γ A B} :
    isWfArityE Σ Γ A ->
    red Σ Γ A B ->
    isWfArityE Σ Γ B.
  Proof.
    induction 2 using red_rect'.
    - easy.
    - now eapply isWfArity_red1E.
  Qed.

  (** Base [isType_red] ([:3969]); the field [isType_red] of [T1_facts]. *)
  Lemma isType_redE {Σ} {wfΣ : wfE Σ} {Γ T U} :
    isTypeE Σ Γ T -> red Σ Γ T U -> isTypeE Σ Γ U.
  Proof.
    intros HT red; apply lift_sorting_it_impl_gen with HT => // Hs.
    eapply subject_reductionE; eauto.
  Qed.

End SRContextE.

(** Base [isType_tLetIn] ([:3978]). Base reads a reduct [tSort s'] of the let-in's type off
    [ws_cumul_pb_Sort_r_inv]; over E only a canonical-form chain is available
    ([ws_cumul_pbE_Sort_r_inv], [PCUICEtaA6.v:207]), so this takes the T1 audit's route (§5),
    with no reduct: [ws_cumul_pbE_LetIn_l_inv] gives [A'{0:=t} ≤ tSort s] in [Γ];
    [weakening_ws_cumul_pbE] moves it under the [vdef]; [red_expand_letE] gives
    [A' ⇝ lift0 1 (A'{0:=t})] there; transitivity. The sort is the one of the hypothesis, and
    [typing_wf_sortE] (copy 13) gives its well-formedness. *)
Lemma isType_tLetInE {cf} {Σ} {HΣ' : wfE Σ} {Γ} {na t A B}
  : isTypeE Σ Γ (tLetIn na t A B)
    <~> (lift_typing typingE Σ Γ (j_vdef na t A) × isTypeE Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as (_ & s & H & _).
    pose proof (typing_wf_sortE HΣ' H) as wfs.
    apply inversion_LetInE in H as (A' & HtA & HB & H); tas.
    split; tas.
    have wfΓd := typingE_wf_local HB.
    eapply has_sort_isTypeE.
    eapply (type_ws_cumul_pbE (pb := Cumul) A'); [exact HB| |].
    + eapply has_sort_isTypeE. eapply typeE_Sort; tea.
    + apply ws_cumul_pbE_LetIn_l_inv in H.
      eapply (weakening_ws_cumul_pbE (Γ' := []) (Γ'' := [vdef na t A])) in H.
      2: exact (wf_local_closed_contextE wfΓd).
      cbn in H.
      etransitivity; [|exact H].
      eapply red_ws_cumul_pbE, red_expand_letE; tea.
      exact (type_is_open_termE HB).
  - destruct HH as (HtA & HB).
    apply lift_sorting_f_it_impl with HB => // Hs.
    eapply type_reductionE; tas.
    * econstructor; tea.
    * apply red1_red.
      apply red_zeta with (b':=tSort _).
Qed.

(** ** The checker's contract: [T1_facts] and [T2a_facts]

  The fields of [T1_facts] and [T2a_facts] of the checker's [safechecker/theories/
  PCUICTypingEtaHyps.v] ([wip/etak-k7-2026-10-29] @ [0bbee83d]), verbatim, each inhabited by its
  lemma here. The [T1] fits are this file's theorems (under the forecast block); the [T2a] fits
  are T2a's proved [validityE] and [inversion_mkAppsE] ([PCUICValidityEta]), as this file uses
  them. *)

Definition T1_isType_prim_arg_types_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {tags : list prim_tag} {res : term} {T : term}, wf_localE Σ Γ -> (forall t : prim_tag, In t tags -> t <> primArray) -> All (prim_op_tag_declared Σ) tags -> PCUICPrimOpType.prim_arg_types (retroknowledge Σ.1) tags res = Some T -> isTypeE Σ Γ res -> isTypeE Σ Γ T
  := @isType_prim_arg_typesE cf.

Definition T1_isType_prim_shape_type_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {s : PrimitiveOps.prim_shape} {res : term}, wf_localE Σ Γ -> PCUICPrimOpType.prim_shape_type (retroknowledge Σ.1) s = Some res -> on_prim_op_result Σ s -> isTypeE Σ Γ res
  := @isType_prim_shape_typeE cf.

Definition T1_isType_red_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {T : term} {U : term}, isTypeE Σ Γ T -> PCUICReduction.red Σ Γ T U -> isTypeE Σ Γ U
  := @isType_redE cf.

Definition T1_subject_reduction_fit {cf : checker_flags} :
  forall (Σ : global_env_ext) (Γ : context) (t : term) (u : term) (T : term), wfE Σ -> Σ;;; Γ |-E t : T -> PCUICReduction.red Σ Γ t u -> Σ;;; Γ |-E u : T
  := @subject_reductionE cf.

Definition T1_type_reduction_closed_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {A : term} {B : term}, Σ;;; Γ |-E t : A -> Σ ;;; Γ ⊢ A ⇝ B -> Σ;;; Γ |-E t : B
  := @type_reduction_closedE cf.

Definition T2a_inversion_mkApps_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-E mkApps f u : T -> ∑ A : term, Σ;;; Γ |-E f : A × typing_spineE Σ Γ A u T
  := fun Σ wfΣ Γ f u T h => inversion_mkAppsE h.

Definition T2a_validity_fit {cf : checker_flags} :
  forall {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-E t : T -> isTypeE Σ Γ T
  := fun Σ wfΣ Γ t T h => validityE h.

End SREta.
