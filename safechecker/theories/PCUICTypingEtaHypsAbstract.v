(* Distributed under the terms of the MIT license. *)
(** * ETAK (EtaK7Abs): the K7 bundle [EtaFacts] over abstract relations, its E instance and its base instance

  REPORT (lane lead's conditions 1 and 5, 2026-10-29):
  - field shapes jointly inhabitable with eta relation replaced by base; does NOT show eta bundle consistent nor forecast envs satisfy anything
  - This does not discharge any E hypothesis; T1 remains

  BET-64 EtaCheckerLane, worker EtaK7Abs, 2026-10-29; branch cut from [wip/etak-k4qual-2026-10-29] @ [5bab1cc9]
  (it contains the K7 line tip [f384f5c7]). This file changes nothing the checker sees: [EtaFacts] and its eight
  classes stay in [PCUICTypingEtaHyps], untouched, and nothing imports this file.

  - [EtaRels]: one parameter per E judgment that a field of the eight classes names ([wfE], [typingE],
    [wf_localE], [wf_local_relE], [isTypeE], [isTypeRelE], [typing_spineE], [spine_substE], [ctx_instE],
    [ws_cumul_pbE], [ws_cumul_pbE_terms], [ws_cumul_ctx_pbE], [ws_cumul_ctx_pbE_rel], the five bidirectional
    judgments [inferingE], [infering_sortE], [infering_prodE], [infering_induE], [checkingE], and
    [wf_local_bd_relE]), and two for reduction ([PCUICReduction.red] and [closed_red]; η does not change
    reduction, so both instances below take base's). The generic combinators [lift_typing], [lift_sorting],
    [PCUICTyping.ctx_inst] and [All2] stay; a field that applies one of them to an E judgment applies it to the
    parameter. Base's [red_terms] ([All2 (closed_red Σ Γ)]) becomes [All2] of the [closed_red] parameter.
    Untyped and universe notions ([whnf], [whnf_red], [declared_*], [consistent_instance_ext], [leq_sort],
    [on_prim_op_result], [cmp_ind_universes], ...) are not relations η replaces and stay as they are.
  - [T0_factsAbs] ... [T6BDc_factsAbs]: one abstract field [<field>_abs] per field [<field>] of [T0_facts] ...
    [T6BDc_facts] (44 fields, in the same order), whose statement is the field's text with each E judgment
    replaced by its parameter (local notations [|-A], [⊢A] mirror [|-E], [⊢E]); [EtaFactsAbs] is [EtaFacts]
    over them.
  - E instance [RelsE]: [T*_facts <~> T*_factsAbs RelsE] for each class and [EtaFacts <-> EtaFactsAbs RelsE],
    each proved by repacking the fields; the field types agree by conversion (unfolding [RelsE]).
  - Base instance [RelsB]: base MetaRocq ([wf], [typing], [wf_local], [isType], [isTypeRel],
    [PCUICArities.typing_spine], [PCUICSpine.spine_subst], [ws_cumul_pb], ..., the bidirectional judgments of
    [BDTyping]); [T*_facts_base : T*_factsAbs RelsB] and [EtaFactsAbs_base : EtaFactsAbs RelsB], each field
    the base lemma of the same name (BDToPCUIC, BDUnique, BDFromPCUIC, PCUICSR, PCUICValidity,
    PCUICInductives, PCUICInductiveInversion, PCUICArities, PCUICClassification, PCUICNormal,
    PCUICContextConversionTyp).
  - Fields that cannot be stated abstractly: none. Fields whose base instance is not provable: none. *)
From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICLiftSubst PCUICUnivSubst
     PCUICSigmaCalculus PCUICEquality PCUICReduction PCUICOnFreeVars PCUICClosed PCUICTyping PCUICCumulativity
     PCUICCumulativitySpec PCUICWellScopedCumulativity PCUICContextSubst PCUICCases PCUICNormal PCUICPosition
     PCUICConversion PCUICFixWitness PCUICWfUniverses PCUICClosedBodies PCUICSpine PCUICWeakeningEnv
     PCUICInductiveInversion PCUICContextConversionTyp
     PCUICCumulativitySpecEta PCUICTypingEta PCUICTypingEtaInd PCUICEtaI5 PCUICWellScopedCumulativityEta
     PCUICConversionEtaCongr PCUICContextConversionEta PCUICWsCumulEtaSubst PCUICEtaA6
     PCUICClosedTypEta PCUICWeakeningEnvTypEta.
From MetaRocq.PCUIC Require Import PCUICWsCumulEtaCtx.
From MetaRocq.SafeChecker Require Import PCUICTypingEtaDefs.
(** The hypothesis bundle, imported last (as its own header asks of its users). *)
From MetaRocq.SafeChecker Require Import PCUICTypingEtaHyps.
(** Base metatheory, required without import and named qualified. *)
From MetaRocq.PCUIC Require PCUICArities PCUICInductives PCUICSR PCUICValidity PCUICClassification
     BDTyping BDToPCUIC BDFromPCUIC BDUnique.

(** ** The relations the fields name *)
Record EtaRels := {
  r_wf : global_env -> Type;
  r_typing : global_env_ext -> context -> term -> term -> Type;
  r_wf_local : global_env_ext -> context -> Type;
  r_wf_local_rel : global_env_ext -> context -> context -> Type;
  r_isType : global_env_ext -> context -> term -> Type;
  r_isTypeRel : global_env_ext -> context -> term -> relevance -> Type;
  r_typing_spine : global_env_ext -> context -> term -> list term -> term -> Type;
  r_spine_subst : global_env_ext -> context -> list term -> list term -> context -> Type;
  r_ctx_inst : global_env_ext -> context -> list term -> context -> Type;
  r_ws_cumul_pb : conv_pb -> global_env_ext -> context -> term -> term -> Type;
  r_ws_cumul_pb_terms : global_env_ext -> context -> list term -> list term -> Type;
  r_ws_cumul_ctx_pb : conv_pb -> global_env_ext -> context -> context -> Type;
  r_ws_cumul_ctx_pb_rel : conv_pb -> global_env_ext -> context -> context -> context -> Type;
  r_infering : global_env_ext -> context -> term -> term -> Type;
  r_infering_sort : global_env_ext -> context -> term -> sort -> Type;
  r_infering_prod : global_env_ext -> context -> term -> aname -> term -> term -> Type;
  r_infering_indu : global_env_ext -> context -> inductive -> term -> Instance.t -> list term -> Type;
  r_checking : global_env_ext -> context -> term -> term -> Type;
  r_wf_local_bd_rel : global_env_ext -> context -> context -> Type;
  r_red : global_env -> context -> term -> term -> Type;
  r_closed_red : global_env_ext -> context -> term -> term -> Type }.

(** ** The eight classes over [R : EtaRels]

  Each field [<field>_abs] is the field [<field>] of the class of the same row in [PCUICTypingEtaHyps], with
  [wfE] → [wfA], [Σ ;;; Γ |-E …] → [Σ ;;; Γ |-A …] (typing and the five bidirectional judgments),
  [Σ ;;; Γ ⊢E T ≤ U] → [Σ ;;; Γ ⊢A T ≤ U], [Σ ;;; Γ ⊢ t ⇝ u] → [Σ ;;; Γ ⊢A t ⇝ u], [PCUICReduction.red] →
  [redA], [red_terms] → [red_termsA], and [<judgment>E] → [<judgment>A] for the other judgments. *)
Section Abstract.
  Context {cf : checker_flags} (R : EtaRels).

  Local Abbreviation wfA := (r_wf R).
  Local Abbreviation typingA := (r_typing R).
  Local Abbreviation wf_localA := (r_wf_local R).
  Local Abbreviation wf_local_relA := (r_wf_local_rel R).
  Local Abbreviation isTypeA := (r_isType R).
  Local Abbreviation isTypeRelA := (r_isTypeRel R).
  Local Abbreviation typing_spineA := (r_typing_spine R).
  Local Abbreviation spine_substA := (r_spine_subst R).
  Local Abbreviation ctx_instA := (r_ctx_inst R).
  Local Abbreviation ws_cumul_pb_termsA := (r_ws_cumul_pb_terms R).
  Local Abbreviation ws_cumul_ctx_pbA := (r_ws_cumul_ctx_pb R).
  Local Abbreviation ws_cumul_ctx_pb_relA := (r_ws_cumul_ctx_pb_rel R).
  Local Abbreviation checkingA := (r_checking R).
  Local Abbreviation infering_sortA := (r_infering_sort R).
  Local Abbreviation wf_local_bd_relA := (r_wf_local_bd_rel R).
  Local Abbreviation redA := (r_red R).
  Local Abbreviation red_termsA Σ Γ := (All2 (r_closed_red R Σ Γ)).
  Local Notation " Σ ;;; Γ |-A t : T " := (r_typing R Σ Γ t T) (at level 50, Γ, t, T at next level).
  Local Notation " Σ ;;; Γ |-A t ▹ T " := (r_infering R Σ Γ t T) (at level 50, Γ, t, T at next level).
  Local Notation " Σ ;;; Γ |-A t ▹□ u " := (r_infering_sort R Σ Γ t u) (at level 50, Γ, t, u at next level).
  Local Notation " Σ ;;; Γ |-A t ▹Π ( na , A , B ) " := (r_infering_prod R Σ Γ t na A B)
    (at level 50, Γ, t, na, A, B at next level).
  Local Notation " Σ ;;; Γ |-A t ▹{ ind } ( u , args ) " := (r_infering_indu R Σ Γ ind t u args)
    (at level 50, Γ, t, ind, u, args at next level).
  Local Notation " Σ ;;; Γ |-A t ◃ T " := (r_checking R Σ Γ t T) (at level 50, Γ, t, T at next level).
  Local Notation " Σ ;;; Γ ⊢A t ≤ u " := (r_ws_cumul_pb R Cumul Σ Γ t u) (at level 50, Γ, t, u at next level).
  Local Notation " Σ ;;; Γ ⊢A t ⇝ u " := (r_closed_red R Σ Γ t u) (at level 50, Γ, t, u at next level).

  (** T0 (the typing infrastructure). *)
  Class T0_factsAbs := {
    closed_context_cumulativity_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ.1} (Γ : context) {pb : conv_pb} {t : term} {T : term} {Γ' : context}, Σ;;; Γ |-A t : T -> wf_localA Σ Γ' -> ws_cumul_ctx_pbA pb Σ Γ' Γ -> Σ;;; Γ' |-A t : T ;
    inductive_cumulative_indices_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {ind : inductive} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {u : Instance.t} {u' : Instance.t} {napp : nat}, declared_inductive Σ ind mdecl idecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> consistent_instance_ext Σ (ind_universes mdecl) u' -> PCUICEquality.cmp_ind_universes Σ ind napp u u' -> forall (Γ : context) (pars : list term) (pars' : list term) (parsubst : list term) (parsubst' : list term), spine_substA Σ Γ pars parsubst (ind_params mdecl)@[u] -> spine_substA Σ Γ pars' parsubst' (ind_params mdecl)@[u'] -> ws_cumul_pb_termsA Σ Γ pars pars' -> let indctx := (ind_indices idecl)@[u] in let indctx' := (ind_indices idecl)@[u'] in let pindctx := subst_context parsubst 0 indctx in let pindctx' := subst_context parsubst' 0 indctx' in ws_cumul_ctx_pb_relA Cumul Σ Γ (smash_context [] pindctx) (smash_context [] pindctx') ;
    invert_type_mkApps_ind_abs :
      forall (Σ : global_env_ext) (Γ : context) (ind : inductive) (u : Instance.t) (args : list term) (T : term) (mdecl : mutual_inductive_body) (idecl : one_inductive_body), wfA Σ.1 -> declared_inductive Σ.1 ind mdecl idecl -> Σ;;; Γ |-A mkApps (tInd ind u) args : T -> typing_spineA Σ Γ (ind_type idecl)@[u] args T × consistent_instance_ext Σ (ind_universes mdecl) u ;
    isTypeRel_cstr_type_abs :
      forall (Σ : global_env_ext) (mdecl : mutual_inductive_body) (idecl : one_inductive_body) (cdecl : constructor_body) (n : nat), wfA Σ.1 -> nth_error (ind_bodies mdecl) n = Some idecl -> cstr_type cdecl = it_mkProd_or_LetIn (ind_params mdecl,,, cstr_args cdecl) (mkApps (tRel (#|ind_params mdecl,,, cstr_args cdecl| + (#|ind_bodies mdecl| - S n))) (to_extended_list_k (ind_params mdecl) #|cstr_args cdecl| ++ cstr_indices cdecl)) -> isTypeA Σ [] (ind_type idecl) -> redA Σ.1 [] (ind_type idecl) (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isTypeA Σ [] (it_mkProd_or_LetIn (ind_params mdecl) (it_mkProd_or_LetIn (ind_indices idecl) (tSort (ind_sort idecl)))) -> isSortRel (ind_sort idecl) (ind_relevance idecl) -> ctx_instA Σ (arities_context (ind_bodies mdecl),,, ind_params mdecl,,, cstr_args cdecl) (cstr_indices cdecl) (List.rev (lift_context #|cstr_args cdecl| 0 (ind_indices idecl))) -> isTypeA Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) -> isTypeRelA Σ (arities_context (ind_bodies mdecl)) (cstr_type cdecl) (ind_relevance idecl) ;
    isType_mkApps_Ind_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) {Γ : context} {puinst : Instance.t} {args : list term} {inst : list term}, consistent_instance_ext Σ (ind_universes mdecl) puinst -> spine_substA Σ Γ args inst (ind_params mdecl,,, ind_indices idecl)@[puinst] -> Σ;;; Γ |-A mkApps (tInd ind puinst) args : tSort (ind_sort idecl)@[puinst] ;
    isType_mkApps_Ind_inv_abs :
      forall {Σ : global_env_ext} {Γ : context} {ind : inductive} {u : Instance.t} {args : list term} (wfΣ : wfA Σ.1) {mdecl : mutual_inductive_body} {idecl : one_inductive_body} (declm : declared_inductive Σ.1 ind mdecl idecl), wf_localA Σ Γ -> isTypeA Σ Γ (mkApps (tInd ind u) args) -> ∑ parsubst argsubst : list term, let parctx := (ind_params mdecl)@[u] in let argctx := subst_context parsubst 0 (ind_indices idecl)@[u] in [× spine_substA Σ Γ (firstn (ind_npars mdecl) args) parsubst parctx, spine_substA Σ Γ (skipn (ind_npars mdecl) args) argsubst argctx, #|firstn (ind_npars mdecl) args| = ind_npars mdecl, #|skipn (ind_npars mdecl) args| = context_assumptions (ind_indices idecl) & consistent_instance_ext Σ (ind_universes mdecl) u] ;
    on_minductive_wf_params_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {ind : kername} {mdecl : mutual_inductive_body} {u : Instance.t}, declared_minductive Σ.1 ind mdecl -> consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localA Σ (ind_params mdecl)@[u] ;
    on_minductive_wf_params_indices_inst_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (u : Instance.t), consistent_instance_ext Σ (ind_universes mdecl) u -> wf_localA Σ (ind_params mdecl,,, ind_indices idecl)@[u] ;
    typing_spine_ind_type_inv_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {mdecl : mutual_inductive_body} {ind : inductive} {idecl : one_inductive_body} (decli : declared_inductive Σ ind mdecl idecl) (Γ : context) (u : Instance.t) (args : list term) (T : term), wf_localA Σ Γ -> consistent_instance_ext Σ (ind_universes mdecl) u -> typing_spineA Σ Γ (ind_type idecl)@[u] args T -> typing_spineA Σ Γ (it_mkProd_or_LetIn (ind_params mdecl,,, ind_indices idecl) (tSort (ind_sort idecl)))@[u] args T ;
    wf_case_branch_type_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term), declared_inductive Σ ci mdecl idecl -> isTypeA Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-A preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> forall (i : nat) (cdecl : constructor_body) (br : branch term), declared_constructor Σ (ci, i) mdecl idecl cdecl -> wf_branch cdecl br -> let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localA Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localA Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localA Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-A brctxty.2 : tSort ps] ;
    wf_case_predicate_context_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} {args : list term}, declared_inductive Σ ci mdecl idecl -> isTypeA Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in wf_localA Σ (Γ,,, predctx) ;
    wf_case_branches_types'_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {mdecl : mutual_inductive_body} {idecl : one_inductive_body} {ci : case_info} {p : predicate term} (ps : sort) (args : list term) (brs : list (branch term)), declared_inductive Σ ci mdecl idecl -> isTypeA Σ Γ (mkApps (tInd ci (puinst p)) (pparams p ++ args)) -> wf_predicate mdecl idecl p -> let predctx := case_predicate_context ci mdecl idecl p in Σ;;; Γ,,, predctx |-A preturn p : tSort ps -> let ptm := it_mkLambda_or_LetIn predctx (preturn p) in wf_branches idecl brs -> All2 PCUICEquality.eq_decl_upto_names (pcontext p) (ind_predicate_context ci mdecl idecl) -> All2i (fun (i : nat) (cdecl : constructor_body) (br : branch term) => let cstr_br_ctx := case_branch_context_nopars ci mdecl (puinst p) cdecl in let brctx' := map2 set_binder_name (forget_types (bcontext br)) cstr_br_ctx in let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in [× wf_branch cdecl br, wf_localA Σ (Γ,,, (ind_params mdecl)@[puinst p],,, cstr_br_ctx), wf_localA Σ (Γ,,, (ind_params mdecl)@[puinst p],,, brctx'), wf_localA Σ (Γ,,, brctxty.1) & Σ;;; Γ,,, brctxty.1 |-A brctxty.2 : tSort ps]) 0 (ind_ctors idecl) brs
  }.

  (** U (untyped plumbing). *)
  Class U_factsAbs := {
    whnf_red_inv_abs :
      forall {Σ : global_env_ext} (Γ : context) (t t' : term), wfA Σ -> whnf RedFlags.default Σ Γ t -> Σ ;;; Γ ⊢A t ⇝ t' -> whnf_red Σ Γ t t'
  }.

  (** T1 (subject reduction). *)
  Class T1_factsAbs := {
    isType_prim_shape_type_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {s : PrimitiveOps.prim_shape} {res : term}, wf_localA Σ Γ -> PCUICPrimOpType.prim_shape_type (retroknowledge Σ.1) s = Some res -> on_prim_op_result Σ s -> isTypeA Σ Γ res ;
    isType_red_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {T : term} {U : term}, isTypeA Σ Γ T -> redA Σ Γ T U -> isTypeA Σ Γ U ;
    subject_reduction_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (u : term) (T : term), wfA Σ -> Σ;;; Γ |-A t : T -> redA Σ Γ t u -> Σ;;; Γ |-A u : T ;
    type_reduction_closed_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {t : term} {A : term} {B : term}, Σ;;; Γ |-A t : A -> Σ ;;; Γ ⊢A A ⇝ B -> Σ;;; Γ |-A t : B
  }.

  (** T2a (validity). *)
  Class T2a_factsAbs := {
    inversion_mkApps_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ.1} {Γ : context} {f : term} {u : list term} {T : term}, Σ;;; Γ |-A mkApps f u : T -> ∑ A : term, Σ;;; Γ |-A f : A × typing_spineA Σ Γ A u T ;
    validity_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-A t : T -> isTypeA Σ Γ T
  }.

  (** T6 (inversion and classification). *)
  Class T6_factsAbs := {
    typing_spine_smash_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ.1) (Γ : context) (Δ : context) (T : term) (args : list term) (T' : term), typing_spineA Σ Γ (it_mkProd_or_LetIn Δ T) args T' -> typing_spineA Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'
  }.

  (** T6, bidirectional soundness. *)
  Class T6BD_factsAbs := {
    checking_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfA Σ), wf_localA Σ Γ -> isTypeA Σ Γ T -> Σ;;; Γ |-A t ◃ T -> Σ;;; Γ |-A t : T ;
    ctx_inst_bd_typing_abs :
      forall (Σ : global_env_ext) (Γ : list context_decl) (l : list term) (Δ : list context_decl) (wfΣ : wfA Σ), wf_localA Σ (Γ,,, Δ) -> PCUICTyping.ctx_inst (checkingA Σ) Γ l (List.rev Δ) -> ctx_instA Σ Γ l (List.rev Δ) ;
    infering_ind_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (ind : inductive) (u : Instance.t) (args : list term) (wfΣ : wfA Σ), wf_localA Σ Γ -> Σ;;; Γ |-A t ▹{ ind}(u, args) -> Σ;;; Γ |-A t : mkApps (tInd ind u) args ;
    infering_prod_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (na : aname) (A : term) (B : term) (wfΣ : wfA Σ), wf_localA Σ Γ -> Σ;;; Γ |-A t ▹Π (na, A, B) -> Σ;;; Γ |-A t : tProd na A B ;
    infering_sort_isTypeRel_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfA Σ), wf_localA Σ Γ -> Σ;;; Γ |-A t ▹□ u -> isTypeRelA Σ Γ t (relevance_of_sort u) ;
    infering_sort_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (u : sort) (wfΣ : wfA Σ), wf_localA Σ Γ -> Σ;;; Γ |-A t ▹□ u -> Σ;;; Γ |-A t : tSort u ;
    infering_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (t : term) (T : term) (wfΣ : wfA Σ), wf_localA Σ Γ -> Σ;;; Γ |-A t ▹ T -> Σ;;; Γ |-A t : T ;
    lift_sorting_lift_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (j : judgment) (wfΣ : wfA Σ), wf_localA Σ Γ -> lift_sorting (checkingA Σ Γ) (infering_sortA Σ Γ) j -> lift_typing typingA Σ Γ j ;
    wf_local_bd_rel_typing_abs :
      forall (Σ : global_env_ext) (Γ : context) (Γ' : context) (wfΣ : wfA Σ), wf_localA Σ Γ -> wf_local_bd_relA Σ Γ Γ' -> wf_local_relA Σ Γ Γ'
  }.

  (** T6, bidirectional uniqueness. *)
  Class T6BDu_factsAbs := {
    infering_checking_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {T : term} {T' : term}, on_free_vars (shiftnP #|Γ| xpred0) T' -> Σ;;; Γ |-A t ▹ T -> Σ;;; Γ |-A t ◃ T' -> Σ ;;; Γ ⊢A T ≤ T' ;
    infering_ind_ind_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {ind : inductive} {ind' : inductive} {u : Instance.t} {u' : Instance.t} {args : list term} {args' : list term}, Σ;;; Γ |-A t ▹{ ind}(u, args) -> Σ;;; Γ |-A t ▹{ ind'}(u', args') -> ∑ args'' : list term, [× ind = ind', u = u', red_termsA Σ Γ args args'' & red_termsA Σ Γ args' args''] ;
    infering_ind_infering_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {ind : inductive} {u : Instance.t} {args : list term} {T : term}, Σ;;; Γ |-A t ▹{ ind}(u, args) -> Σ;;; Γ |-A t ▹ T -> ∑ args' : list term, Σ ;;; Γ ⊢A T ⇝ mkApps (tInd ind u) args' × red_termsA Σ Γ args args' ;
    infering_prod_infering_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {na : aname} {A : term} {B : term} {T : term}, Σ;;; Γ |-A t ▹Π (na, A, B) -> Σ;;; Γ |-A t ▹ T -> ∑ A' B' : term, [× Σ ;;; Γ ⊢A T ⇝ tProd na A' B', Σ ;;; Γ ⊢A A ⇝ A' & Σ ;;; Γ,, vass na A ⊢A B ⇝ B'] ;
    infering_prod_prod_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {na : aname} {na' : aname} {A : term} {A' : term} {B : term} {B' : term}, Σ;;; Γ |-A t ▹Π (na, A, B) -> Σ;;; Γ |-A t ▹Π (na', A', B') -> ∑ A'' B'' : term, [× na = na', Σ ;;; Γ ⊢A A ⇝ A'', Σ ;;; Γ ⊢A A' ⇝ A'', Σ ;;; Γ,, vass na A ⊢A B ⇝ B'' & Σ ;;; Γ,, vass na A' ⊢A B' ⇝ B''] ;
    infering_sort_infering_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} {wfΓ : wf_localA Σ Γ} {t : term} {u : sort} {T : term}, Σ;;; Γ |-A t ▹□ u -> Σ;;; Γ |-A t ▹ T -> Σ ;;; Γ ⊢A T ⇝ tSort u ;
    infering_sort_sort_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {u : sort} {u' : sort}, Σ;;; Γ |-A t ▹□ u -> Σ;;; Γ |-A t ▹□ u' -> u = u' ;
    infering_unique_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} (wfΓ : wf_localA Σ Γ) {t : term} {T : term} {T' : term}, Σ;;; Γ |-A t ▹ T -> Σ;;; Γ |-A t ▹ T' -> ∑ T'' : term, Σ ;;; Γ ⊢A T ⇝ T'' × Σ ;;; Γ ⊢A T' ⇝ T'' ;
    isTypeRel_unique_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} {T : term} {rel : relevance} {rel' : relevance}, isTypeRelA Σ Γ T rel -> isTypeRelA Σ Γ T rel' -> rel = rel'
  }.

  (** T6, bidirectional completeness. *)
  Class T6BDc_factsAbs := {
    ctx_inst_typing_bd_abs :
      forall (Σ : global_env_ext) (Γ : context) (l : list term) (Δ : context) (wfΣ : wfA Σ), ctx_instA Σ Γ l Δ -> PCUICTyping.ctx_inst (checkingA Σ) Γ l Δ ;
    lift_typing_lift_sorting_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : context} {tm : option term} {ty : term} {rel : option relevance}, lift_typing typingA Σ Γ (Judge tm ty None rel) -> lift_sorting (checkingA Σ Γ) (infering_sortA Σ Γ) (Judge tm ty None rel) ;
    typing_checking_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-A t : T -> Σ;;; Γ |-A t ◃ T ;
    typing_infering_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {t : term} {T : term}, Σ;;; Γ |-A t : T -> ∑ T' : term, Σ;;; Γ |-A t ▹ T' × Σ ;;; Γ ⊢A T' ≤ T ;
    typing_infering_sort_abs :
      forall {Σ : global_env_ext} {wfΣ : wfA Σ} {Γ : context} {t : term} {u : sort}, Σ;;; Γ |-A t : tSort u -> ∑ u' : sort, Σ;;; Γ |-A t ▹□ u' × leq_sort Σ u' u ;
    wf_local_rel_wf_local_bd_abs :
      forall {Σ : global_env_ext} (wfΣ : wfA Σ) {Γ : list context_decl} {Γ' : context}, wf_local_relA Σ Γ Γ' -> wf_local_bd_relA Σ Γ Γ'
  }.
End Abstract.

(** [EtaFacts] over the abstract classes: the squashes of the eight. *)
Class EtaFactsAbs {cf : checker_flags} (R : EtaRels) : Prop := {
  eta_T0_abs : ∥ T0_factsAbs R ∥ ;
  eta_U_abs : ∥ U_factsAbs R ∥ ;
  eta_T1_abs : ∥ T1_factsAbs R ∥ ;
  eta_T2a_abs : ∥ T2a_factsAbs R ∥ ;
  eta_T6_abs : ∥ T6_factsAbs R ∥ ;
  eta_T6BD_abs : ∥ T6BD_factsAbs R ∥ ;
  eta_T6BDu_abs : ∥ T6BDu_factsAbs R ∥ ;
  eta_T6BDc_abs : ∥ T6BDc_factsAbs R ∥ }.

(** ** The E instance: the existing bundle *)

(** The E judgments, as the fields of [PCUICTypingEtaHyps] name them. *)
Definition RelsE {cf : checker_flags} : EtaRels := {|
  r_wf := wfE;
  r_typing := typingE;
  r_wf_local := fun Σ Γ => wf_localE Σ Γ;
  r_wf_local_rel := wf_local_relE;
  r_isType := isTypeE;
  r_isTypeRel := isTypeRelE;
  r_typing_spine := typing_spineE;
  r_spine_subst := spine_substE;
  r_ctx_inst := fun Σ => ctx_instE Σ;
  r_ws_cumul_pb := ws_cumul_pbE;
  r_ws_cumul_pb_terms := ws_cumul_pbE_terms;
  r_ws_cumul_ctx_pb := ws_cumul_ctx_pbE;
  r_ws_cumul_ctx_pb_rel := ws_cumul_ctx_pbE_rel;
  r_infering := inferingE;
  r_infering_sort := infering_sortE;
  r_infering_prod := infering_prodE;
  r_infering_indu := infering_induE;
  r_checking := checkingE;
  r_wf_local_bd_rel := fun Σ Γ Γ' => wf_local_bd_relE Σ Γ Γ';
  r_red := PCUICReduction.red;
  r_closed_red := PCUICWellScopedCumulativity.closed_red |}.

(** Each class of [PCUICTypingEtaHyps] is its abstract class at [RelsE]: the fields are repacked one by one,
    each field type of one side converting to the other's. *)
Section EInstance.
  Context {cf : checker_flags}.

  Lemma T0_facts_abs_iff : T0_facts <~> T0_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma U_facts_abs_iff : U_facts <~> U_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma T1_facts_abs_iff : T1_facts <~> T1_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma T2a_facts_abs_iff : T2a_facts <~> T2a_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma T6_facts_abs_iff : T6_facts <~> T6_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma T6BD_facts_abs_iff : T6BD_facts <~> T6BD_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma T6BDu_facts_abs_iff : T6BDu_facts <~> T6BDu_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma T6BDc_facts_abs_iff : T6BDc_facts <~> T6BDc_factsAbs RelsE.
  Proof. split; intros []; constructor; assumption. Qed.

  Lemma EtaFacts_abs_iff : EtaFacts <-> EtaFactsAbs RelsE.
  Proof.
    split.
    - intros [[h0] [hu] [h1] [h2a] [h6] [hbd] [hbdu] [hbdc]]. constructor; constructor.
      + exact (fst T0_facts_abs_iff h0).
      + exact (fst U_facts_abs_iff hu).
      + exact (fst T1_facts_abs_iff h1).
      + exact (fst T2a_facts_abs_iff h2a).
      + exact (fst T6_facts_abs_iff h6).
      + exact (fst T6BD_facts_abs_iff hbd).
      + exact (fst T6BDu_facts_abs_iff hbdu).
      + exact (fst T6BDc_facts_abs_iff hbdc).
    - intros [[h0] [hu] [h1] [h2a] [h6] [hbd] [hbdu] [hbdc]]. constructor; constructor.
      + exact (snd T0_facts_abs_iff h0).
      + exact (snd U_facts_abs_iff hu).
      + exact (snd T1_facts_abs_iff h1).
      + exact (snd T2a_facts_abs_iff h2a).
      + exact (snd T6_facts_abs_iff h6).
      + exact (snd T6BD_facts_abs_iff hbd).
      + exact (snd T6BDu_facts_abs_iff hbdu).
      + exact (snd T6BDc_facts_abs_iff hbdc).
  Qed.
End EInstance.

(** ** The base instance: base MetaRocq's judgments, every field a base lemma *)

Definition RelsB {cf : checker_flags} : EtaRels := {|
  r_wf := PCUICTyping.wf;
  r_typing := PCUICTyping.typing;
  r_wf_local := fun Σ Γ => All_local_env (lift_typing1 (PCUICTyping.typing Σ)) Γ;
  r_wf_local_rel := PCUICTyping.wf_local_rel;
  r_isType := PCUICTyping.isType;
  r_isTypeRel := PCUICTyping.isTypeRel;
  r_typing_spine := PCUICArities.typing_spine;
  r_spine_subst := PCUICSpine.spine_subst;
  r_ctx_inst := fun Σ => PCUICTyping.ctx_inst (PCUICTyping.typing Σ);
  r_ws_cumul_pb := PCUICWellScopedCumulativity.ws_cumul_pb;
  r_ws_cumul_pb_terms := fun Σ Γ => All2 (PCUICWellScopedCumulativity.ws_cumul_pb Conv Σ Γ);
  r_ws_cumul_ctx_pb := PCUICWellScopedCumulativity.ws_cumul_ctx_pb;
  r_ws_cumul_ctx_pb_rel := PCUICConversion.ws_cumul_ctx_pb_rel;
  r_infering := BDTyping.infering;
  r_infering_sort := BDTyping.infering_sort;
  r_infering_prod := BDTyping.infering_prod;
  r_infering_indu := BDTyping.infering_indu;
  r_checking := BDTyping.checking;
  r_wf_local_bd_rel := fun Σ Γ Γ' =>
    All_local_rel (lift_sorting1 (BDTyping.checking Σ) (BDTyping.infering_sort Σ)) Γ Γ';
  r_red := PCUICReduction.red;
  r_closed_red := PCUICWellScopedCumulativity.closed_red |}.

Section BaseInstance.
  Context {cf : checker_flags}.

  (** Each bullet proves the field of the same name, in the class order, by the base lemma of that name. *)
  Lemma T0_facts_base : T0_factsAbs RelsB.
  Proof.
    constructor.
    - exact (@PCUICContextConversionTyp.closed_context_cumulativity cf).
    - exact (@PCUICInductiveInversion.inductive_cumulative_indices cf).
    - exact (@PCUICInductives.invert_type_mkApps_ind cf).
    - exact (@PCUICInductiveInversion.isTypeRel_cstr_type cf).
    - exact (@PCUICInductives.isType_mkApps_Ind cf).
    - exact (@PCUICInductives.isType_mkApps_Ind_inv cf).
    - exact (@PCUICArities.on_minductive_wf_params cf).
    - exact (@PCUICInductives.on_minductive_wf_params_indices_inst cf).
    - exact (@PCUICInductives.typing_spine_ind_type_inv cf).
    - exact (@PCUICInductiveInversion.wf_case_branch_type cf).
    - exact (@PCUICInductiveInversion.wf_case_predicate_context cf).
    - exact (@PCUICInductiveInversion.wf_case_branches_types' cf).
  Qed.

  Lemma U_facts_base : U_factsAbs RelsB.
  Proof. constructor. exact (@PCUICNormal.whnf_red_inv cf). Qed.

  Lemma T1_facts_base : T1_factsAbs RelsB.
  Proof.
    constructor.
    - exact (@PCUICSR.isType_prim_shape_type cf).
    - exact (@PCUICSR.isType_red cf).
    - exact (@PCUICSR.subject_reduction cf).
    - exact (@PCUICSR.type_reduction_closed cf).
  Qed.

  Lemma T2a_facts_base : T2a_factsAbs RelsB.
  Proof.
    constructor.
    - exact (@PCUICValidity.inversion_mkApps cf).
    - exact (@PCUICValidity.validity cf).
  Qed.

  Lemma T6_facts_base : T6_factsAbs RelsB.
  Proof. constructor. exact (@PCUICClassification.typing_spine_smash cf). Qed.

  Lemma T6BD_facts_base : T6BD_factsAbs RelsB.
  Proof.
    constructor.
    - exact (@BDToPCUIC.checking_typing cf).
    - exact (@BDToPCUIC.ctx_inst_bd_typing cf).
    - exact (@BDToPCUIC.infering_ind_typing cf).
    - exact (@BDToPCUIC.infering_prod_typing cf).
    - exact (@BDToPCUIC.infering_sort_isTypeRel cf).
    - exact (@BDToPCUIC.infering_sort_typing cf).
    - exact (@BDToPCUIC.infering_typing cf).
    - exact (@BDToPCUIC.lift_sorting_lift_typing cf).
    - exact (@BDToPCUIC.wf_local_bd_rel_typing cf).
  Qed.

  Lemma T6BDu_facts_base : T6BDu_factsAbs RelsB.
  Proof.
    constructor.
    - exact (@BDUnique.infering_checking cf).
    - exact (@BDUnique.infering_ind_ind cf).
    - exact (@BDUnique.infering_ind_infering cf).
    - exact (@BDUnique.infering_prod_infering cf).
    - exact (@BDUnique.infering_prod_prod cf).
    - exact (@BDUnique.infering_sort_infering cf).
    - exact (@BDUnique.infering_sort_sort cf).
    - exact (@BDUnique.infering_unique cf).
    - exact (@BDUnique.isTypeRel_unique cf).
  Qed.

  Lemma T6BDc_facts_base : T6BDc_factsAbs RelsB.
  Proof.
    constructor.
    - exact (@BDFromPCUIC.ctx_inst_typing_bd cf).
    - exact (@BDFromPCUIC.lift_typing_lift_sorting cf).
    - exact (@BDFromPCUIC.typing_checking cf).
    - exact (@BDFromPCUIC.typing_infering cf).
    - exact (@BDFromPCUIC.typing_infering_sort cf).
    - exact (@BDFromPCUIC.wf_local_rel_wf_local_bd cf).
  Qed.

  Lemma EtaFactsAbs_base : EtaFactsAbs RelsB.
  Proof.
    constructor; constructor.
    - exact T0_facts_base.
    - exact U_facts_base.
    - exact T1_facts_base.
    - exact T2a_facts_base.
    - exact T6_facts_base.
    - exact T6BD_facts_base.
    - exact T6BDu_facts_base.
    - exact T6BDc_facts_base.
  Qed.
End BaseInstance.
