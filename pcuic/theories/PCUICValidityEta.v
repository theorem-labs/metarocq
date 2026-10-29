(* Distributed under the terms of the MIT license. *)

(** * Validity over [typingE] (row T2a): the E copy of [PCUICValidity]

  The E twin of every lemma of base [PCUICValidity] whose statement mentions typing or
  conversion: [typing] → [typingE], [wf] → [wfE], [wf_local] → [wf_localE], [isType] →
  [isTypeE], [isWfArity] → [isWfArityE], [lift_typing typing] → [lift_typing typingE],
  [cumulSpec0] → [cumulSpecE0], [env_prop] → [env_propE] ([PCUICTypingEtaInd]),
  [typing_spine] (the [PCUICArities] one) → [typing_spineE], [arity_spine] → [arity_spineE].
  Nothing else changes; each name takes the suffix [E] (plan [t0-plan.md] §2, D1). The base
  file imports [PCUICInversion]; this file uses [PCUICInversionEta].

  Base lemmas NOT copied, because they mention neither typing nor conversion (they are
  imported from base [PCUICValidity] and used as they are): [eq_binder_annots_eq_ctx]
  ([eq_context_upto_names], syntactic), [eq_term_set_binder_name] ([eq_term], syntactic
  equality up to universes), [All2_eq_binder_subst_context_inst] and
  [wf_pre_case_predicate_context_gen] (binder annotations).

  Map, base → E: [isType_weaken_full] → [isType_weaken_fullE]; [isType_extends] →
  [isType_extendsE]; [isType_Sort_inv] → [isType_Sort_invE]; [isWfArity_subst_instance_decl]
  → [isWfArity_subst_instance_declE]; [isType_weakening] → [isType_weakeningE];
  [type_ctx_wf_univ] → [type_ctx_wf_univE]; [validity_wf_local] → [validity_wf_localE];
  [validity_env] → [validity_envE]; [validity] → [validityE]; [wf_local_validity] →
  [wf_local_validityE]; the notation [validity_term] → [validity_termE]; [inversion_mkApps] →
  [inversion_mkAppsE]; [type_App'] → [type_App'E]; [type_mkApps_arity] → [type_mkApps_arityE].

  [validityE] and [inversion_mkAppsE] are the two fields of [SRForecastT2a]
  ([PCUICSREta.v]) and of the checker's [T2a_facts]
  ([safechecker/theories/PCUICTypingEtaHyps.v], branch [wip/etak-k7-2026-10-29]):
  [PCUICValidityEtaInstances] type-checks both lemmas against both texts.

  **The forecast block.** Validity uses lemmas of the T0 copies 10, 14, 15 and 16 that are not
  on this branch. Each is a field of a class of the block below, with the name and the
  statement the copy commits to: the text of [PCUICSREta.v]'s forecast classes where that file
  has the lemma, else the exact base twin. The classes are premises ([Context]) of the lemmas
  that use them, never axioms; [Print Assumptions] shows them as arguments. The block also
  holds the E twins of the copy-file definitions the statements mention ([subsletE],
  [typing_spineE], [ctx_inst_subE], [spine_substE]: the text of [PCUICSREta.v];
  [arity_spineE], [wf_arity_spineE]: base twins).

  **Local proofs of copy lemmas.** Ten lemmas of copies 10, 12, 14, 15 and 16 that validity
  uses follow from landed facts (and, for two of them, from fields of the block) in a few
  lines; they are PROVED in the section "Copy lemmas proved here", under the name and the
  statement the copy commits to, so they are not forecasts. When the copy lands, delete them
  and import it.

  **The hypotheses are satisfiable:** [wfE Σ] by any well-formed environment ([wf_incl_E]),
  each typing premise by a concrete derivation; [PCUICValidityEtaInstances] gives an instance
  of every lemma family with premises. *)

From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICUtils PCUICTactics PCUICCases
     PCUICContextSubst PCUICLiftSubst PCUICTyping PCUICSigmaCalculus
     PCUICClosed PCUICClosedConv PCUICClosedTyp PCUICWeakeningEnv PCUICWeakeningEnvTyp
     PCUICWeakeningConv PCUICWeakeningTyp
     PCUICSubstitution PCUICReduction PCUICCumulativity PCUICGeneration
     PCUICUnivSubst PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp PCUICConfluence
     PCUICConversion PCUICContexts PCUICEquality
     PCUICArities PCUICSpine PCUICInductives
     PCUICWellScopedCumulativity PCUICWfUniverses PCUICOnFreeVars PCUICValidity.
From MetaRocq.PCUIC Require Import PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd
     PCUICTypingEtaNotions PCUICClosedBodies PCUICClosedTypEta PCUICWeakeningEnvTypEta
     PCUICWeakeningTypEta PCUICUnivSubstitutionTypEta PCUICWfUniversesEta
     PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICWsCumulEtaSubst PCUICEtaJoinSpec
     PCUICWsCumulEtaCtx PCUICWsCumulEtaCtxTyp PCUICInversionEta.
(* Not imported: its [typing_spineE] is the twin of [PCUICGeneration.typing_spine], not of the
   [PCUICArities] one defined below. *)
From MetaRocq.PCUIC Require PCUICGenerationEta.

From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Arguments Nat.sub : simpl never.

(** [PCUICTyping.v:456] [has_sort_isType]. *)
Definition has_sort_isTypeE {cf Σ} {Γ T} s
  : Σ ;;; Γ |-E T : tSort s -> isTypeE Σ Γ T.
Proof.
  repeat (eexists; tea).
Defined.

(** [PCUICTyping.v:470] [isWfArity]. *)
Definition isWfArityE {cf:checker_flags} Σ (Γ : context) T :=
  (isTypeE Σ Γ T × { ctx & { s & (destArity [] T = Some (ctx, s)) } }).

(** ** FORECAST BLOCK

  Every class field below is a FORECAST: an E copy that is not on this branch will prove it,
  under exactly this name and with exactly this statement. Landing a copy is: delete its class
  here (and its definitions), delete its [Context] line in section [ValidityEta], import the
  copy. No proof below the block changes. Nothing here is an axiom. *)

(* The braces in the statements record the implicit status of the source; Rocq honours them
   on the class projections. *)
Local Set Warnings "-unexpected-implicit-declaration".

(** *** Definitions *)

(* FORECAST-ONLY: proved by copy 10 (PCUICSubstitutionEta.v, twin of PCUICSubstitution.v:45
   subslet); delete when it lands. Text: PCUICSREta.v, verbatim. *)
Inductive subsletE {cf:checker_flags} Σ (Γ : context) : list term -> context -> Type :=
| emptysletE : subsletE Σ Γ [] []
| cons_let_assE Δ s na t T : subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E t : subst0 s T ->
    subsletE Σ Γ (t :: s) (Δ ,, vass na T)
| cons_let_defE Δ s na t T :
    subsletE Σ Γ s Δ ->
    Σ ;;; Γ |-E subst0 s t : subst0 s T ->
    subsletE Σ Γ (subst0 s t :: s) (Δ ,, vdef na t T).

(* FORECAST-ONLY: proved by copy 14 (PCUICAritiesEta.v, twin of PCUICArities.v:44
   typing_spine); delete when it lands. Text: PCUICSREta.v, verbatim. *)
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

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v, twin of PCUICSpine.v:903 ctx_inst_sub);
   delete when it lands. Text: PCUICSREta.v, verbatim. *)
Fixpoint ctx_inst_subE {cf : checker_flags} {Σ : global_env_ext} {Γ Δ args}
  (c : ctx_instE Σ Γ args Δ) {struct c} : list term :=
  match c return _ with
  | PCUICTyping.ctx_inst_nil => []
  | PCUICTyping.ctx_inst_ass na t i inst Δ P c => ctx_inst_subE c ++ [i]
  | PCUICTyping.ctx_inst_def na b t inst Δ c => ctx_inst_subE c ++ [b]
  end.

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v, twin of PCUICSpine.v:226 spine_subst);
   delete when it lands. Text: PCUICSREta.v, verbatim. *)
Record spine_substE {cf : checker_flags} Σ Γ inst s (Δ : context) := mkSpineSubstE {
  spine_dom_wfE : wf_localE Σ Γ;
  spine_codom_wfE : wf_localE Σ (Γ ,,, Δ);
  inst_ctx_substE :> context_subst Δ inst s;
  inst_subsletE :> subsletE Σ Γ s Δ }.
Arguments inst_ctx_substE {cf Σ Γ inst s Δ}.
Arguments inst_subsletE {cf Σ Γ inst s Δ}.

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v, twin of PCUICSpine.v:274 arity_spine);
   delete when it lands. Text: the base twin. *)
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

Derive Signature for arity_spineE.

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v, twin of PCUICSpine.v:291
   wf_arity_spine); delete when it lands. Text: the base twin. *)
Record wf_arity_spineE {cf:checker_flags} Σ Γ T args T' :=
{ wf_arity_spine_wfE : isTypeE Σ Γ T;
  wf_arity_spine_spineE : arity_spineE Σ Γ T args T' }.

(** *** Copy 10 ([PCUICSubstitutionEta.v]) *)

(* FORECAST-ONLY: proved by copy 10 (PCUICSubstitutionEta.v); delete when it lands.
   Text of each field: PCUICSREta.v, class SRForecastCopy10, verbatim. *)
Class ValForecastCopy10 := {
  (* PCUICSubstitution.v:1824 isType_substitution *)
  isType_substitutionE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' s Δ T},
    subsletE Σ Γ s Γ' ->
    isTypeE Σ (Γ ,,, Γ' ,,, Δ) T ->
    isTypeE Σ (Γ ,,, subst_context s 0 Δ) (subst s #|Δ| T) ;
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
    Σ ;;; Γ |-E t {0 := u} : T {0 := u}
}.

(** *** Copy 14 ([PCUICAritiesEta.v]) *)

(* FORECAST-ONLY: proved by copy 14 (PCUICAritiesEta.v); delete when it lands.
   Text: PCUICSREta.v, class SRForecastCopy14, verbatim. *)
Class ValForecastCopy14 := {
  (* PCUICArities.v:527 subslet_inds *)
  subslet_indsE :
    forall {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {ind u mdecl idecl},
    declared_inductive Σ.1 ind mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    subsletE Σ [] (inds (inductive_mind ind) u (ind_bodies mdecl))
      (subst_instance u (arities_context (ind_bodies mdecl)))
}.

(** *** Copy 15 ([PCUICSpineEta.v]) *)

(* FORECAST-ONLY: proved by copy 15 (PCUICSpineEta.v); delete when it lands.
   Text of the first five fields: PCUICSREta.v, class SRForecastCopy15, verbatim. The last two
   are in neither PCUICSREta.v nor the statement note: their text is the exact base twin
   (section [WfEnv] of [PCUICSpine.v:322]: [{cf} {Σ : global_env_ext} {wfΣ : wf Σ}]). *)
Class ValForecastCopy15 := {
  ctx_inst_spine_substE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ Δ : list context_decl} {args : list term},
    wf_localE Σ (Γ ,,, Δ) ->
    forall ci : ctx_instE Σ Γ args (List.rev Δ),
    spine_substE Σ Γ args (ctx_inst_subE ci) Δ ;
  spine_subst_smashE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {inst s : list term} {Δ : context},
    spine_substE Σ Γ inst s Δ ->
    spine_substE Σ Γ inst (List.rev inst) (smash_context [] Δ) ;
  spine_subst_subst_to_extended_list_kE :
    forall {cf : checker_flags} {Σ : global_env_ext} {Γ : context} {args s : list term} {Δ : context},
    spine_substE Σ Γ args s Δ ->
    map (subst0 s) (to_extended_list_k Δ 0) = args ;
  (* NOT TWIN (ADDED ClosedBodies), closedbodies-register row 1, as in the note. *)
  type_mkAppsE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ},
    forall {Γ : context} {t : term} {u : list term} {T t_ty : term},
    Σ ;;; Γ |-E t : t_ty ->
    typing_spineE Σ Γ t_ty u T ->
    Σ ;;; Γ |-E mkApps t u : T ;
  typing_spine_strengthenE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {Γ : context} {T : term} {args : list term} {U : term},
    typing_spineE Σ Γ T args U ->
    forall T' : term,
    isTypeE Σ Γ T' ->
    ws_cumul_pbE Cumul Σ Γ T' T ->
    typing_spineE Σ Γ T' args U ;
  (* PCUICSpine.v:415 wf_arity_spine_typing_spine; base twin *)
  wf_arity_spine_typing_spineE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ T args T'},
    wf_arity_spineE Σ Γ T args T' ->
    typing_spineE Σ Γ T args T' ;
  (* PCUICSpine.v:782 spine_subst_smash_app_inv; base twin *)
  spine_subst_smash_app_invE :
    forall {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Δ Δ' δ δ'},
    #|δ| = context_assumptions Δ ->
    spine_substE Σ Γ (δ ++ δ') (List.rev (δ ++ δ')) (smash_context [] (Δ ,,, Δ')) ->
    spine_substE Σ Γ δ (List.rev δ) (smash_context [] Δ) ×
    spine_substE Σ Γ δ' (List.rev δ')
      (subst_context_let_expand (List.rev δ) Δ (smash_context [] Δ'))
}.

(** *** Copy 16 ([PCUICInductivesEta.v]) *)

(* FORECAST-ONLY: proved by copy 16 (PCUICInductivesEta.v); delete when it lands.
   Text of the first three fields: PCUICSREta.v, class SRForecastCopy16, verbatim. The last two
   are in neither PCUICSREta.v nor the statement note: their text is the exact base twin. *)
Class ValForecastCopy16 := {
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
  on_minductive_wf_params_indices_instE :
    forall {cf : checker_flags} {Σ : global_env_ext}, wfE Σ ->
    forall {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body},
    declared_inductive Σ ind mdecl idecl ->
    forall u : Instance.t,
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_localE Σ ((ind_params mdecl ,,, ind_indices idecl)@[u]) ;
  (* PCUICInductives.v:2697 isType_case_predicate; base twin *)
  isType_case_predicateE :
    forall {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {ci : case_info}
      {mdecl idecl} u params ps,
    wf_localE Σ Γ ->
    declared_inductive Σ ci mdecl idecl ->
    consistent_instance_ext Σ (ind_universes mdecl) u ->
    wf_sort Σ ps ->
    spine_substE Σ Γ params (List.rev params) (smash_context [] (subst_instance u (ind_params mdecl))) ->
    isTypeE Σ Γ
      (it_mkProd_or_LetIn
        (pre_case_predicate_context_gen ci mdecl idecl params u)
        (tSort ps)) ;
  (* PCUICInductives.v:2803 arity_spine_case_predicate; base twin *)
  arity_spine_case_predicateE :
    forall {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {ci : case_info}
      {mdecl idecl} {u params indices ps} {c},
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
      (indices ++ [c]) (tSort ps)
}.

Local Set Warnings "unexpected-implicit-declaration".

(** ** End of the FORECAST BLOCK *)

Section ValidityEta.

(* FORECAST-ONLY: one premise per class of the block above; delete each when its copy lands. *)
Context {V10 : ValForecastCopy10} {V14 : ValForecastCopy14} {V15 : ValForecastCopy15}
  {V16 : ValForecastCopy16}.

(** ** Copy lemmas proved here

  Each has the name and the statement its copy commits to (the text of [PCUICSREta.v] where
  that file has the lemma, else the base twin), and a proof from landed facts. Delete each when
  its copy lands. *)

(** Copy 10, [PCUICSubstitution.v:1306] [isType_wf_local]; text of [PCUICSREta.v]. *)
Lemma isType_wf_localE {cf:checker_flags} {Σ : global_env_ext} {Γ T} :
  isTypeE Σ Γ T -> wf_localE Σ Γ.
Proof. intros h. exact (lift_typingE_wf_local h). Qed.

(** Copy 14, [PCUICArities.v:228] [type_ws_cumul_pb]; text of [PCUICSREta.v] (NOT TWIN,
    ADDED [ClosedBodies]: closedbodies-register row 2). *)
Lemma type_ws_cumul_pbE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : ClosedBodies Σ} {pb Γ t} T {U} :
  Σ ;;; Γ |-E t : T ->
  isTypeE Σ Γ U ->
  ws_cumul_pbE pb Σ Γ T U ->
  Σ ;;; Γ |-E t : U.
Proof.
  intros ht hU c.
  eapply typeE_Cumul; [exact ht|exact hU.2.π2.1|].
  destruct pb.
  - exact (ws_cumul_pbE_forget_spec (ws_cumul_pbE_eq_le c)).
  - exact (ws_cumul_pbE_forget_spec c).
Qed.

(** Copy 14, [PCUICArities.v:213] [isType_tProd]; text of [PCUICSREta.v]. *)
Lemma isType_tProdE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} {na A B} :
  isTypeE Σ Γ (tProd na A B) <~>
  (isTypeRelE Σ Γ A na.(binder_relevance) × isTypeE Σ (Γ,, vass na A) B).
Proof.
  split; intro HH.
  - destruct HH as (_ & s & H & _).
    destruct (inversion_ProdE Σ wfΣ H) as [s1 [s2 [HA [HB _]]]].
    apply lift_sorting_forget_univ in HA.
    split; [exact HA|exact (has_sort_isTypeE _ HB)].
  - destruct HH as [HA HB].
    pose proof (lift_sorting_extract HA).
    destruct HB as (_ & sB & HB & _).
    eapply has_sort_isTypeE.
    eapply typeE_Prod; eassumption.
Defined.

(** Copy 14, [PCUICArities.v:288] [isType_apply]; base twin. *)
Lemma isType_applyE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ na A B t} :
  isTypeE Σ Γ (tProd na A B) ->
  Σ ;;; Γ |-E t : A ->
  isTypeE Σ Γ (B {0 := t}).
Proof.
  intros hP ht.
  destruct (fst (isType_tProdE (wfΣ := wfΣ)) hP) as [hA hB].
  have sub : subsletE Σ Γ [t] [vass na A].
  { constructor; [constructor|]. now rewrite subst_empty. }
  exact (isType_substitutionE (Δ := []) sub hB).
Qed.

(** Copy 14, [PCUICArities.v:373] [type_mkProd_or_LetIn]; base twin. *)
Lemma type_mkProd_or_LetInE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ} d {u t s} :
  lift_typing typingE Σ Γ (j_decl_s d (Some u)) ->
  Σ ;;; Γ ,, d |-E t : tSort s ->
  match decl_body d return Type with
  | Some b => Σ ;;; Γ |-E mkProd_or_LetIn d t : tSort s
  | None => Σ ;;; Γ |-E mkProd_or_LetIn d t : tSort (Sort.sort_of_product u s)
  end.
Proof.
  destruct d as [na [b|] dty] => [Hd Ht|Hd Ht]; rewrite /mkProd_or_LetIn /=.
  - eapply typeE_Cumul.
    + eapply typeE_LetIn; [exact (lift_sorting_forget_univ Hd)|exact Ht].
    + eapply typeE_Sort; [exact (lift_typingE_wf_local Hd)|exact (typing_wf_sortE wfΣ Ht)].
    + eapply convSpecE_cumulSpecE, red1_cumulSpecE. constructor.
  - eapply typeE_Prod; [exact Hd|exact Ht].
Qed.

(** Copy 14, [PCUICArities.v:439] [type_it_mkProd_or_LetIn_sorts]; base twin. *)
Lemma type_it_mkProd_or_LetIn_sortsE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ}
  {Γ Γ' us t s} :
  sorts_local_ctx (lift_typing typingE) Σ Γ Γ' us ->
  Σ ;;; Γ ,,, Γ' |-E t : tSort s ->
  Σ ;;; Γ |-E it_mkProd_or_LetIn Γ' t : tSort (sort_of_products us s).
Proof.
  revert Γ us s t.
  induction Γ' as [|[na [b|] ty] Γ' IH]; simpl; move=> Γ us s t equ Ht.
  - destruct us => //.
  - destruct equ as [equ hd].
    eapply IH; [exact equ|].
    exact (type_mkProd_or_LetInE (vdef na b ty) (lift_sorting_extract hd) Ht).
  - destruct us as [|u us] => //. destruct equ as [equ hd].
    simpl.
    eapply IH; [exact equ|].
    exact (type_mkProd_or_LetInE (vass na ty) hd Ht).
Qed.

(** Copy 15, [PCUICSpine.v:341] [typing_spine_refl]; base twin. *)
Lemma typing_spine_reflE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ T} :
  isTypeE Σ Γ T ->
  typing_spineE Σ Γ T [] T.
Proof.
  intros isty. constructor; [exact isty|exact isty|].
  exact (isType_ws_cumul_pbE_refl (pb := Cumul) Γ T isty).
Qed.

(** Copy 12, [PCUICContexts.v:145] [instantiate_minductive]; base twin. *)
Lemma instantiate_minductiveE {cf:checker_flags} Σ ind mdecl u Γ t T :
  wfE Σ.1 ->
  declared_minductive Σ.1 ind mdecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  (Σ.1, ind_universes mdecl) ;;; Γ |-E t : T ->
  Σ ;;; subst_instance u Γ |-E subst_instance u t : subst_instance u T.
Proof.
  intros wfΣ isdecl Hu Ht.
  unshelve eapply declared_minductive_to_gen in isdecl; eauto.
  red in isdecl.
  exact (typing_subst_instance_declE Σ Γ t T ind (InductiveDecl mdecl) u wfΣ isdecl Ht Hu).
Qed.

(** Copy 16, [PCUICInductives.v:1558] [declared_projection_type]; base twin, from the field
    [declared_projection_type_and_eqE] of the forecast block. *)
Lemma declared_projection_typeE {cf:checker_flags} {Σ : global_env_ext} {mdecl idecl p cdecl pdecl} :
  wfE Σ.1 ->
  declared_projection Σ p mdecl idecl cdecl pdecl ->
  let u := abstract_instance (ind_universes mdecl) in
  isTypeE (Σ.1, ind_universes mdecl)
    ((vass {| binder_name := nNamed idecl.(ind_name); binder_relevance := idecl.(ind_relevance) |} (mkApps (tInd p.(proj_ind) u)
          (to_extended_list (smash_context [] (ind_params mdecl)))))::
        smash_context [] (ind_params mdecl)) pdecl.(proj_type).
Proof.
  intros wfΣ declp u.
  exact (declared_projection_type_and_eqE wfΣ declp).1.2.
Qed.

(** ** The copy of [PCUICValidity] *)

Section Validity.
  Context `{cf : config.checker_flags}.

  Lemma isType_weaken_fullE : weaken_env_prop_full cumulSpecE0 (lift_typing typingE) (fun Σ Γ t T => isTypeE Σ Γ T).
  Proof.
    do 2 red. intros (Σ & φ) **.
    unshelve eapply weaken_env_prop_typingE; cbn. 5: apply X2.
    all: assumption.
  Qed.

  Lemma isType_extendsE (Σ : global_env) (Σ' : global_env) (φ : universes_decl) :
    wfE Σ -> wfE Σ' ->
    extends Σ Σ' ->
    forall Γ : context,
    forall t0 : term,
    isTypeE (Σ, φ) Γ t0 -> isTypeE (Σ', φ) Γ t0.
  Proof.
    intros wfΣ wfΣ' ext Γ t Hty.
    eapply weaken_env_prop_typingE; cbn; tas. 3: eassumption. all: assumption.
  Qed.

  Lemma isType_Sort_invE {Σ : global_env_ext} {Γ s} : wfE Σ -> isTypeE Σ Γ (tSort s) -> wf_sort Σ s.
  Proof.
    intros wfΣ (_ & u & Hu & _).
    exact (inversion_SortE Σ wfΣ Hu).2.1.
  Qed.

  Lemma isWfArity_subst_instance_declE {Σ Γ T c decl u} :
    wfE Σ.1 ->
    lookup_env Σ.1 c = Some decl ->
    isWfArityE (Σ.1, universes_decl_of_decl decl) Γ T ->
    consistent_instance_ext Σ (universes_decl_of_decl decl) u ->
    isWfArityE Σ (subst_instance u Γ) (subst_instance u T).
  Proof.
    destruct Σ as [Σ φ]. intros X X0 [isTy [ctx [s eq]]] X1.
    split. eapply isType_subst_instance_declE; eauto.
    exists (subst_instance u ctx), (subst_instance_sort u s).
    rewrite (subst_instance_destArity []) eq. intuition auto.
  Qed.

  Lemma isType_weakeningE {Σ Γ T} :
    wfE Σ.1 ->
    wf_localE Σ Γ ->
    isTypeE Σ [] T ->
    isTypeE Σ Γ T.
  Proof.
    intros wfΣ wfΓ HT.
    apply lift_typing_impl with (1 := HT) => ?? hs.
    exact (weaken_ctxE Γ wfΣ wfΓ hs).
  Qed.

  Lemma type_ctx_wf_univE Σ Γ Δ s : type_local_ctx (lift_typing typingE) Σ Γ Δ s -> wf_sort Σ s.
  Proof.
    induction Δ as [|[na [b|] ty] Δ IH]; simpl; auto.
    - intros [h _]; auto.
    - intros [h _]; auto.
  Qed.

  Lemma validity_wf_localE {Σ} Γ Δ:
    All_local_rel (lift_typing typingE Σ) Γ Δ ->
    ∑ xs, sorts_local_ctx (lift_typing typingE) Σ Γ Δ xs.
  Proof.
    induction 1.
    - exists []; cbn; auto.
    - destruct IHX as [xs Hxs].
      eexists (_ :: xs). cbn. split; auto.
      unshelve eapply lift_sorting_extract; tea.
    - destruct IHX as [xs Hxs].
      exists xs; cbn. split; auto.
  Qed.

  Theorem validity_envE :
    env_propE (fun Σ Γ t T => isTypeE Σ Γ T)
      (fun Σ Γ j => lift_sorting (fun _ T => isTypeE Σ Γ T) (fun _ s => wf_sort Σ s) j)
      (fun Σ Γ => wf_localE Σ Γ).
  Proof.
    apply typingE_ind_env.

    - (* Pj *)
      intros Σ wfΣ Γ j X.
      apply lift_sorting_impl with (1 := X).
      + intros t T [_ HT]; exact HT.
      + intros T s [_ HT]; exact (isType_Sort_invE wfΣ HT).

    - (* PΓ *)
      intros Σ wfΣ Γ wfΓ _ _. exact wfΓ.

    - (* Rel *)
      intros Σ wfΣ Γ wfΓ n decl heq _.
      destruct (All_local_env_nth_error wfΓ heq) as (_ & s & Hs & _).
      eapply isType_liftE; eauto.
      1: now apply nth_error_Some_length in heq.
      now eapply has_sort_isTypeE.

    - (* Universe *)
      intros Σ wfΣ Γ wfΓ u _ wfu.
      eapply has_sort_isTypeE with (s := Sort.super (Sort.super u)).
      eapply typeE_Sort; [exact wfΓ|].
      now apply wf_sort_super.

    - (* Product *)
      intros Σ wfΣ Γ wfΓ na t b s1 s2 _ _ Pj _ Pb.
      eapply has_sort_isTypeE.
      apply unlift_TypUniv in Pj.
      pose proof (isType_Sort_invE wfΣ Pb) as wfs2.
      eapply typeE_Sort; [exact wfΓ|].
      now apply wf_sort_product.

    - (* Lambda *)
      intros Σ wfΣ Γ wfΓ na t b bty _ Hj _ _ Pb.
      eapply lift_sorting_ex_it_impl_gen with Pb => // Hs.
      intros _.
      pose proof (lift_sorting_extract Hj) as Hj'.
      eexists; split; [eapply typeE_Prod; eassumption|constructor].

    - (* Let *)
      intros Σ wfΣ Γ wfΓ na b b_ty b' b'_ty _ Hj _ _ Pb'.
      apply lift_sorting_it_impl_gen with Pb' => // Hs.
      eapply typeE_Cumul.
      + eapply typeE_LetIn; [exact Hj|exact Hs].
      + eapply typeE_Sort; [exact wfΓ|exact (typing_wf_sortE wfΣ Hs)].
      + eapply convSpecE_cumulSpecE, red1_cumulSpecE. constructor.

    - (* Application *)
      intros Σ wfΣ Γ wfΓ t na A B u s _ _ _ _ Pt Hu _.
      apply lift_sorting_it_impl_gen with Pt => // Hs'.
      move: (typing_wf_sortE wfΣ Hs') => wfs.
      eapply (substitution0E (n := na) (T := tSort _)); [|exact Hu].
      destruct (inversion_ProdE Σ wfΣ Hs') as [s1 [s2 [_ [Hs Hle]]]].
      have clΓA : is_closed_context (Γ ,, vass na A)
        := wf_local_closed_contextE (wfΣ := wfΣ) (typingE_wf_local Hs).
      eapply (weakening_ws_cumul_pbE (pb:=Cumul) (Γ' := []) (Γ'' := [vass na A])) in Hle; [|exact clΓA].
      simpl in Hle.
      eapply (type_ws_cumul_pbE (pb:=Cumul) (tSort s2)); [exact Hs| |].
      { eapply has_sort_isTypeE. eapply typeE_Sort; [exact (typingE_wf_local Hs)|exact wfs]. }
      etransitivity; [|exact Hle].
      eapply into_ws_cumul_pbE_spec; [| exact clΓA | reflexivity | reflexivity].
      eapply eq_term_upto_univ_cumulSpecE. constructor.
      apply leq_sort_product.

    - (* Constant *)
      intros Σ wfΣ Γ wfΓ cst u decl _ _ declc cu.
      eapply declared_constant_invE in wfΣ as Hc; eauto.
      apply lift_sorting_forget_body, lift_sorting_forget_rel in Hc.
      eapply isType_weakeningE; eauto.
      unshelve eapply declared_constant_to_gen in declc; eauto.
      eapply isType_subst_instance_declE with (Γ:=[]); eauto. simpl.
      exact weaken_env_prop_typingE.

    - (* Inductive type *)
      intros Σ wfΣ Γ wfΓ ind u mdecl idecl isdecl _ _ cu.
      destruct (on_declared_inductiveE (wfΣ := wfΣ) isdecl) as [onmind oib].
      pose proof (onArity oib) as har.
      apply lift_sorting_forget_rel in har.
      eapply isType_weakeningE; eauto.
      destruct isdecl as [declm _].
      unshelve eapply declared_minductive_to_gen in declm; eauto.
      eapply isType_subst_instance_declE with (Γ:=[]); eauto.

    - (* Constructor type *)
      intros Σ wfΣ Γ wfΓ ind i u mdecl idecl cdecl isdecl _ _ cu.
      destruct (on_declared_constructorE (wfΣ := wfΣ) isdecl) as [[oni oib] [cs [declc onc]]].
      unfold type_of_constructor.
      pose proof (on_ctype onc) as Hc.
      apply lift_sorting_forget_rel in Hc.
      eapply lift_typing_fu_impl with (f := fun t => _ (_ t)) (1 := Hc) => //= ?? Hs.
      2: now eapply relevance_subst_opt.
      eapply instantiate_minductiveE in Hs; eauto.
      2:(destruct isdecl as [[] ?]; eauto).
      simpl in Hs.
      eapply (weaken_ctxE (Γ:=[]) Γ); eauto.
      eapply (substitutionE (Γ := []) (s := inds _ _ _) (Δ := [])); eauto.
      eapply subslet_indsE; eauto. destruct isdecl; eauto.
      now rewrite app_context_nil_l.

    - (* Case predicate application *)
      intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl _ _ _ _ predctx wfpred cu
        wfpctx pret IHpret _ _ _ ctxi Hc _ _ ptm _ _.
      have ctxi' : ctx_instE Σ Γ (pparams p ++ indices)
        (List.rev (subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl))).
      { eapply ctx_inst_impl with (1 := ctxi). now intros t T [Hty _]. }
      have wfΓΔ : wf_localE Σ (Γ ,,, subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl)).
      { apply weaken_wf_localE; [exact wfΣ|exact wfΓ|].
        exact (on_minductive_wf_params_indices_instE wfΣ isdecl _ cu). }
      pose proof (spine_subst_smashE wfΣ (ctx_inst_spine_substE wfΣ wfΓΔ ctxi')) as sp.
      rewrite subst_instance_app_ctx in sp.
      destruct (on_declared_inductiveE (wfΣ := wfΣ) isdecl) as [onmind oib].
      have hlen : #|pparams p| = context_assumptions (subst_instance (puinst p) (ind_params mdecl)).
      { len. rewrite (wf_predicate_length_pars wfpred). now rewrite onmind.(onNpars). }
      destruct (spine_subst_smash_app_invE hlen sp) as [sppars spidx].
      have wfps : wf_sort Σ ps := typing_wf_sortE wfΣ pret.
      have typred : isTypeE Σ Γ (it_mkProd_or_LetIn predctx (tSort ps)).
      { eapply All_local_env_app_inv in wfpctx as [_ onp].
        eapply validity_wf_localE in onp as [xs Hs].
        eapply has_sort_isTypeE.
        eapply type_it_mkProd_or_LetIn_sortsE; tea.
        exact IHpret.2.π2.1. }
      pose proof (isType_case_predicateE (wfΣ := wfΣ) (puinst p) (pparams p) ps wfΓ isdecl cu wfps sppars)
        as tycp.
      rewrite /ptm. eapply (has_sort_isTypeE ps).
      refine (type_mkAppsE (PCUICGenerationEta.type_it_mkLambda_or_LetInE _ _ _ _ _ pret) _).
      refine (typing_spine_strengthenE wfΣ (wf_arity_spine_typing_spineE
        {| wf_arity_spine_wfE := tycp;
           wf_arity_spine_spineE := arity_spine_case_predicateE wfΓ isdecl cu wfps sppars spidx Hc |})
        _ typred _).
      rewrite /predctx /case_predicate_context /case_predicate_context_gen.
      apply into_ws_cumul_pbE_spec.
      + apply eq_term_upto_univ_cumulSpecE.
        eapply PCUICEquality.eq_term_leq_term.
        eapply eq_term_set_binder_name; [|reflexivity].
        now eapply wf_pre_case_predicate_context_gen.
      + exact (wf_local_closed_contextE wfΓ).
      + exact (isType_is_open_termE typred).
      + exact (isType_is_open_termE tycp).

    - (* Proj *)
      intros Σ wfΣ Γ wfΓ p c u mdecl idecl cdecl pdecl isdecl args _ _ Hc IHc heq_length.
      pose proof isdecl as isdecl'.
      eapply declared_projection_typeE in isdecl'; eauto.
      destruct (isType_mkApps_Ind_invE wfΣ isdecl.p1.p1 wfΓ IHc)
        as [parsubst [argsubst [sppar sparg lenpars lenargs cu]]].
      eapply lift_typing_fu_impl with (f := fun t => _ (_ t)) (1 := isdecl') => // ?? Hs.
      2: now eapply relevance_subst_opt.
      unshelve epose proof (isdecl_ := declared_projection_to_gen isdecl); eauto.
      eapply (typing_subst_instance_declE _ _ _ _ _ _ _ wfΣ isdecl_.p1.p1.p1) in Hs; eauto.
      simpl in Hs.
      eapply (weaken_ctxE Γ) in Hs; eauto.
      rewrite -heq_length in sppar. rewrite firstn_all in sppar.
      rewrite subst_instance_cons in Hs.
      rewrite subst_instance_smash in Hs. simpl in Hs.
      pose proof (spine_subst_smashE wfΣ sppar) as sppar'. clear sppar. rename sppar' into sppar.
      eapply (substitutionE (Δ := [_]) sppar) in Hs.
      simpl in Hs.
      eapply (substitutionE (Γ' := [_]) (s := [c]) (Δ := [])) in Hs.
      simpl in Hs. rewrite !(subst_app_simpl [c] (List.rev _)) /=. eassumption.
      constructor. constructor.
      simpl. rewrite subst_empty.
      rewrite subst_instance_mkApps subst_mkApps /=.
      rewrite [subst_instance_instance _ _](subst_instance_id_mdecl Σ u _ cu); auto.
      rewrite subst_instance_to_extended_list.
      rewrite subst_instance_smash.
      rewrite (spine_subst_subst_to_extended_list_kE sppar).
      assumption.

    - (* Fix *)
      intros Σ wfΣ Γ wfΓ mfix n decl types _ hnth _ hty _ _ _ _.
      exact (lift_sorting_forget_rel (nth_error_all hnth hty)).

    - (* CoFix *)
      intros Σ wfΣ Γ wfΓ mfix n decl types _ hnth _ hty _ _ _ _.
      exact (lift_sorting_forget_rel (nth_error_all hnth hty)).

    - (* Primitive *)
      intros Σ wfΣ Γ wfΓ p prim_ty cdecl _ hprim H0 H1 X0 X1.
      depelim X0; depelim X1; simp prim_type; cbn in *.
      1-3:destruct H1 as [hty hbod huniv]; eapply has_sort_isTypeE with (s := _@[[]]); change (tSort ?s@[[]]) with (tSort s)@[[]];
          rewrite <- hty; refine (typeE_Const _ _ _ [] _ wfΓ H0 _); rewrite huniv //.
      set (s := sType (Universe.make' (array_level a))).
      destruct H1 as [hty' hbod huniv].
      eapply has_sort_isTypeE with s.
      eapply (typeE_App _ _ _ _ (tSort s) (tSort s)); tea; cycle 1.
      + eapply (typeE_Const _ _ _ [array_level a]) in H0; tea. rewrite hty' in H0. cbn in H0. exact H0.
        red. rewrite huniv. simpl. rtoProp; intuition eauto. eapply LevelSet.mem_spec. eapply (wfl (array_level a, 0)). cbn. lsets.
        cbn. red. destruct check_univs => //. red. red. intros v H c. csets.
      + econstructor. 2: econstructor; eauto. 2: constructor; tas.
        all: repeat (eexists; tea; cbn).
        1,3: econstructor; eauto.
        all: apply relevance_super.

    - (* Conv *)
      intros Σ wfΣ Γ wfΓ t A B s _ _ _ HB _ _.
      now eapply has_sort_isTypeE with (s := s).
  Qed.

End Validity.

Corollary validityE {cf:checker_flags} {Σ} {wfΣ : wfE Σ} {Γ t T} :
  Σ ;;; Γ |-E t : T -> isTypeE Σ Γ T.
Proof.
  intros h. exact (env_propE_typing validity_envE Σ wfΣ Γ t T h).
Defined.

Lemma wf_local_validityE `{cf : checker_flags} {Σ} {wfΣ : wfE Σ} Γ Δ :
  wf_localE Σ (Γ ,,, Δ) ->
  ∑ us, sorts_local_ctx (lift_typing typingE) Σ Γ Δ us.
Proof.
  move=> wfΓΔ.
  apply: validity_wf_localE.
  now apply: (All_local_env_app_inv _).2.
Qed.

(* This corollary relies strongly on validity to ensure
   every type in the derivation is well-typed. *)
Lemma inversion_mkAppsE {cf} {Σ} {wfΣ :  wfE Σ.1} {Γ f u T} :
  Σ ;;; Γ |-E mkApps f u : T ->
  ∑ A, Σ ;;; Γ |-E f : A × typing_spineE Σ Γ A u T.
Proof.
  induction u in f, T |- *.
  { simpl. intros h. exists T. split; [exact h|].
    exact (typing_spine_reflE (validityE h)). }
  intros Hf. simpl in Hf.
  destruct u.
  - simpl in Hf.
    pose proof (validityE Hf) as hT.
    destruct (inversion_AppE Σ wfΣ Hf) as [na' [A' [B' [Hf' [Ha HA''']]]]].
    exists (tProd na' A' B'). split; [exact Hf'|].
    pose proof (validityE Hf') as hP.
    eapply type_spine_consE; [exact hP|exact hP| |exact Ha|].
    + exact (isType_ws_cumul_pbE_refl (pb := Cumul) Γ _ hP).
    + eapply type_spine_nilE; [|exact hT|exact HA'''].
      exact (isType_applyE hP Ha).
  - specialize (IHu (tApp f a) T).
    specialize (IHu Hf) as [T' [H' H'']].
    destruct (inversion_AppE Σ wfΣ H') as [na' [A' [B' [Hf' [Ha HA''']]]]].
    exists (tProd na' A' B'). split; [exact Hf'|].
    pose proof (validityE Hf') as hP.
    eapply type_spine_consE; [exact hP|exact hP| |exact Ha|].
    + exact (isType_ws_cumul_pbE_refl (pb := Cumul) Γ _ hP).
    + exact (typing_spine_strengthenE wfΣ H'' _ (isType_applyE hP Ha) HA''').
Qed.

(** "Economical" typing rule for applications, not requiring to check the product type *)
Lemma type_App'E {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t na A B u} :
  Σ;;; Γ |-E t : tProd na A B ->
  Σ;;; Γ |-E u : A -> Σ;;; Γ |-E tApp t u : B {0 := u}.
Proof.
  intros Ht Hu.
  destruct (validityE Ht) as (_ & s & Hs & _).
  eapply typeE_App; eauto.
Qed.

(** This principle is useful when the type [tty] is an arity (of the form [it_mkProd_or_LetIn _ (tSort _)]),
    as it avoids having to give intermediate well-typing and cumulativity proofs. *)
Lemma type_mkApps_arityE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t u tty T} :
  Σ;;; Γ |-E t : tty ->
  arity_spineE Σ Γ tty u T ->
  Σ;;; Γ |-E mkApps t u : T.
Proof.
  intros Ht Hty.
  pose proof (validityE Ht).
  eapply type_mkAppsE; tea.
  eapply wf_arity_spine_typing_spineE.
  constructor; tas.
Qed.

End ValidityEta.

(* To deprecate *)
Notation validity_termE wf Ht := (validityE (wfΣ:=wf) Ht).
