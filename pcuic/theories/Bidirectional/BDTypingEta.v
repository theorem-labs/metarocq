(* Distributed under the terms of the MIT license.   *)

(** * Bidirectional typing over the η relations (plan row T6)

  A copy of base [Bidirectional/BDTyping.v] over the η relations of [typingE]. These
  are the CANONICAL bidirectional E judgments (stream lead, 2026-10-29 09:05Z); the
  η checker's forecast copies ([safechecker/theories/PCUICTypingEtaDefs.v] on
  [wip/etak-k7-2026-10-29]) are to import them.

  It restates, with the relation changed and nothing else: the five mutual judgments
  [inferingE], [infering_sortE], [infering_prodE], [infering_induE], [checkingE]
  (base [BDTyping.v:40-164]), their notations, marked [|-E] ([BDTyping.v:166-170]),
  [wf_local_bdE] and [wf_local_bd_relE] ([BDTyping.v:171-172]), [tybranchesE] and
  [branchesE_size] ([BDTyping.v:175-194]), the size functions [inferingE_size] ...
  [checkingE_size] and their positivity ([BDTyping.v:196-244]), and the induction
  principle [bidir_ind_envE] with its machinery [env_prop_bdE], [typing_sumE],
  [typing_sumE_size], [Ptyping_sumE] ([BDTyping.v:248-743]). Names put [E] after the
  relation name, as [PCUICTypingEtaInd] does ([typingE_size], [tybranchesE]); the
  constructor names are the forecast's ([inferE_Rel], ..., [checkE_Cumul]). As in base,
  [tybranchesE]/[branchesE_size] shadow the [typingE] ones of [PCUICTypingEtaInd] in a
  file that imports both, as base [BDTyping] shadows [PCUICTyping]'s.

  ** Design point A: the conversion premises are [JoinE] (ruled 2026-10-29 09:26Z)

  Base [check_Cumul] compares with [Σ ;;; Γ |- T <= T'] ([BDTyping.v:163]), which is
  [cumulAlgo_gen Σ Γ Cumul] ([PCUICCumulativity.v:21-31]): an UNSCOPED join, by [red1]
  steps on either side, ended by [compare_term]. Base [infer_Case] compares the
  parameters with [convAlgo] ([BDTyping.v:102]), the same at [Conv]. The faithful twin
  is the canonical join of I5, [JoinE Σ Γ pb t u] ([PCUICEtaI5.v:56-60]): unscoped,
  [(R_c ∪ eta1)*] from [canon] on either side, ended by [eq_term_upto_univ_eta]. It is
  the only [JoinE] on the tree (no other definition of that name; the files that abbreviate
  it as [J] do so [Local]ly), so it is used unqualified; it is also the relation over which
  [ws_cumul_pbE] is defined and which the checker's [type_Cumul_alt] consumes
  ([safechecker/theories/PCUICTypingEtaHyps.v:741-742] at [0bbee83d]).
  The other two candidates:
  - [ws_cumul_pbE] ([PCUICWellScopedCumulativityEta.v:35-40]) is scoping × [JoinE], the
    twin of base [ws_cumul_pb], not of [cumulAlgo]: it would add three scoping premises
    that base [checking] does not have;
  - [cumulSpecE] is the twin of the declarative [cumulSpec], which base [BDTyping]
    does not use.
  What each choice costs. Soundness (BDToPCUIC, checking ⇒ typingE): base turns
  [cumulAlgo] into [cumulSpec] with [into_ws_cumul_pb] and the scoping the typing
  derivations give, then [cumulAlgo_cumulSpec] ([BDToPCUIC.v:421-424]); here the same
  step is [into_ws_cumul_pbE] then [ws_cumul_pbE_forget_spec] (or [I5_join_to_spec]),
  scoping from [type_is_open_termE]/[subject_is_open_termE]. With [ws_cumul_pbE] the
  scoping would come for free. Completeness (BDFromPCUIC, typingE ⇒ checking): base
  forgets a [ws_cumul_pb] built from [cumulSpec] ([ws_cumul_pb_forget_cumul],
  [BDFromPCUIC.v:52,412]); here [into_ws_cumul_pbE_spec] then [ws_cumul_pbE_forget]. The
  checker: base builds [checking] from the conversion's [ws_cumul_pb] with
  [ws_cumul_pb_forget_cumul]/[_conv] ([safechecker/theories/PCUICTypeChecker.v:470,
  2590, 2945]); the η checker builds [checkingE] the same way with [ws_cumul_pbE_forget]
  ([checkE_Cumul_ws] below). The η conversion's [isconv_term_sound] is to conclude
  [ws_cumul_pbE]; at [0bbee83d] it is still at stage G7 and concludes base [conv_cum]
  ([PCUICSafeConversionEta.v:5610-5613], [PCUICConvCumInversion.v:18]).
  FINDING: the checker's forecast puts [ws_cumul_pbE Cumul Σ Γ T T'] in [checkE_Cumul]
  and [All2 (ws_cumul_pbE Conv Σ Γ)] in [inferE_Case]; here they are
  [JoinE Σ Γ Cumul T T'] and [All2 (JoinE Σ Γ Conv)]. The bridges, each way:
  [ws_cumul_pbE_forget] (forecast ⇒ here, no premise; [checkE_Cumul_ws],
  [All2_ws_cumul_pbE_JoinE]), and [into_ws_cumul_pbE] (here ⇒ forecast, given
  [is_closed_context Γ] and both sides open; [JoinE_ws_cumul_pbE]).

  ** Design point B: the (co)fixpoint witness stays the base reduction witness

  Base [infer_Fix]/[infer_CoFix] carry [wf_fixpoint_red]/[wf_cofixpoint_red]
  ([BDTyping.v:30-37]): a REDUCT of each declared type passes the check. [typingE]
  carries [wf_fixpointE]/[wf_cofixpointE] ([PCUICTypingEta.v:33-40]): a type related by
  [conv_witnessE] ([PCUICTypingEta.v:30-31], [convSpecE]) passes it. [red] is unchanged in
  the η world, so the witness is base's definition, reused, as the forecast does.
  - Soundness direction, red ⇒ [conv_witnessE]: TRUE, proved below
    ([wf_fixpoint_red_wf_fixpointE], [wf_cofixpoint_red_wf_cofixpointE]) from
    [mfix_body_on_red_convE], the twin of [PCUICFixWitness.v:244-254] with [wf Σ] replaced
    by [ClosedBodies Σ]. It and the typed form [mfix_on_ind_red_convE] (the twin of
    [PCUICFixWitness.v:256-266] with [wf] replaced by [wfE]) live in copy 17's
    [PCUICFixWitnessEta], imported here (cross-lane commitment C4). A closed reduction is
    a [ws_cumul_pbE] ([red_ws_cumul_pbE]), hence a [convSpecE]
    ([ws_cumul_pbE_forget_spec]); the premise is [ClosedBodies Σ], not base [wf Σ].
  - Completeness direction, [conv_witnessE] ⇒ red (base [mfix_on_ind_conv_red],
    [PCUICFixWitness.v:217-225], used at [BDFromPCUIC.v:357,372]): its CLOSED-ONLY form is
    FALSE over η, refuted in [PCUICFixWitnessEtaCounter.v]
    ([mfix_body_on_conv_closed_redE_fix_false], [_cofix_false],
    [mfix_body_on_conv_closed_redE_false], [wf_cofixpoint_allE_false], branch
    [wip/eta-e3-fixrefute-2026-10-29]); the refuting witnesses are not typable as types
    ([fwe_fix_dtype_not_typeE], [fwe_cofix_dtype_not_typeE]). Base's form carries
    [wf_local Σ Γ] and [isType Σ Γ (dtype d)] for every body; its E form, with [wf_localE]
    and [isType] over [typingE], is not refuted and is not proved here: by the ruled route
    (t0-plan.md §6 risk 5, row PCUICFixWitness) it is a typed reduct lemma proved WITH E
    subject reduction (T1). So the completeness of this system for [tFix]/[tCoFix]
    (T6BDc) waits for T1. The witness is not changed. *)

From Stdlib Require Import Bool List Arith Lia.
From Stdlib Require String.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICUtils
  PCUICPosition PCUICTyping PCUICCumulativity PCUICReduction PCUICOnFreeVars
  PCUICWellScopedCumulativity PCUICClosedBodies PCUICCumulativitySpecEta PCUICTypingEta
  PCUICEtaI5 PCUICWellScopedCumulativityEta PCUICClosedTypEta BDTyping PCUICFixWitnessEta.

From MetaRocq.Utils Require Export LibHypsNaming.
From Stdlib Require Import ssreflect.
From Stdlib Require ssrbool.
Set Asymmetric Patterns.
From Equations.Type Require Import Relation.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Implicit Types (cf : checker_flags) (Σ : global_env_ext) (Γ : context).

Reserved Notation " Σ ;;; Γ |-E t ▹ T " (at level 50, Γ, t, T at next level).
Reserved Notation " Σ ;;; Γ |-E t ▹□ u " (at level 50, Γ, t, u at next level).
Reserved Notation " Σ ;;; Γ |-E t ▹Π ( na , A , B ) " (at level 50, Γ, t, na, A, B at next level).
Reserved Notation " Σ ;;; Γ |-E t ▹{ ind } ( u , args )" (at level 50, Γ, t, ind, u, args at next level).
Reserved Notation " Σ ;;; Γ |-E t ◃ T " (at level 50, Γ, t, T at next level).
Reserved Notation "'wf_local_bdE' Σ Γ " (at level 9, Σ, Γ at next level).
Reserved Notation "'wf_local_bd_relE' Σ Γ Γ'" (at level 9, Σ, Γ, Γ' at next level).

(** The (co)fixpoint witnesses are base's [wf_fixpoint_red]/[wf_cofixpoint_red]
    ([BDTyping.v:30-37]), reused: they mention only [red], which η does not change. *)

Inductive inferingE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| inferE_Rel n decl :
  nth_error Γ n = Some decl ->
  Σ ;;; Γ |-E tRel n ▹ lift0 (S n) (decl_type decl)

| inferE_Sort s :
  wf_sort Σ s ->
  Σ ;;; Γ |-E tSort s ▹ tSort (Sort.super s)

| inferE_Prod na A B s1 s2 :
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vass_s na A s1) ->
  Σ ;;; Γ ,, vass na A |-E B ▹□ s2 ->
  Σ ;;; Γ |-E tProd na A B ▹ tSort (Sort.sort_of_product s1 s2)

| inferE_Lambda na A t B :
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vass na A) ->
  Σ ;;; Γ ,, vass na A |-E t ▹ B ->
  Σ ;;; Γ |-E tLambda na A t ▹ tProd na A B

| inferE_LetIn na b B t A :
  lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vdef na b B) ->
  Σ ;;; Γ ,, vdef na b B |-E t ▹ A ->
  Σ ;;; Γ |-E tLetIn na b B t ▹ tLetIn na b B A

| inferE_App t na A B u :
  Σ ;;; Γ |-E t ▹Π (na,A,B) ->
  Σ ;;; Γ |-E u ◃ A ->
  Σ ;;; Γ |-E tApp t u ▹ B{0 := u}

| inferE_Const cst u :
  forall decl (isdecl : declared_constant Σ.1 cst decl),
  consistent_instance_ext Σ (cst_universes decl) u ->
  Σ ;;; Γ |-E tConst cst u ▹ subst_instance u (cst_type decl)

| inferE_Ind ind u :
  forall mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  Σ ;;; Γ |-E tInd ind u ▹ subst_instance u (ind_type idecl)

| inferE_Construct ind i u :
  forall mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  Σ ;;; Γ |-E tConstruct ind i u ▹ type_of_constructor mdecl cdecl (ind, i) u

| inferE_Case ci p c brs args u ps mdecl idecl :
  let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  Σ ;;; Γ |-E c ▹{ci} (u,args) ->
  declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
  Σ ;;; Γ ,,, predctx |-E p.(preturn) ▹□ ps ->
  (* case_side_conditions *)
  mdecl.(ind_npars) = ci.(ci_npar) ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  wf_predicate mdecl idecl p ->
  consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
  wf_local_bd_relE Σ Γ predctx ->
  is_allowed_elimination Σ (ind_kelim idecl) ps ->
  isSortRel ps ci.(ci_relevance) ->
  ctx_inst (checkingE Σ) Γ (pparams p)
      (List.rev mdecl.(ind_params)@[p.(puinst)]) ->
  implb (isCoFinite mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) p.(preturn)) = true ->
  cmp_ind_universes Σ ci #|args| u (puinst p) ->
  All2 (JoinE Σ Γ Conv) (firstn (ci_npar ci) args) (pparams p) ->
  (* case_branch_typing *)
  wf_branches idecl brs ->
  All2i (fun i cdecl br =>
    eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
    let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
    wf_local_bd_relE Σ Γ brctxty.1 ×
    Σ ;;; Γ ,,, brctxty.1 |-E br.(bbody) ◃ brctxty.2)
    0 idecl.(ind_ctors) brs ->
  Σ ;;; Γ |-E tCase ci p c brs ▹ mkApps ptm (skipn ci.(ci_npar) args ++ [c])

| inferE_Proj p c u mdecl idecl cdecl pdecl args :
  declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
  Σ ;;; Γ |-E c ▹{p.(proj_ind)} (u,args) ->
  #|args| = ind_npars mdecl ->
  Σ ;;; Γ |-E tProj p c ▹ subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type))

| inferE_Fix mfix n decl :
  fix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (on_def_type (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ) mfix ->
  All (on_def_body (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) (fix_context mfix) Γ) mfix ->
  wf_fixpoint_red Σ Γ mfix ->
  Σ ;;; Γ |-E tFix mfix n ▹ dtype decl

| inferE_CoFix mfix n decl :
  cofix_guard Σ Γ mfix ->
  nth_error mfix n = Some decl ->
  All (on_def_type (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ) mfix ->
  All (on_def_body (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) (fix_context mfix) Γ) mfix ->
  wf_cofixpoint_red Σ Γ mfix ->
  Σ ;;; Γ |-E tCoFix mfix n ▹ dtype decl

| inferE_Prim p prim_ty cdecl :
   primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
   declared_constant Σ prim_ty cdecl ->
   primitive_invariants (prim_val_tag p) cdecl ->
   primitive_typing_hyps (checkingE Σ) Σ Γ p ->
   Σ ;;; Γ |-E tPrim p ▹ prim_type p prim_ty

with infering_sortE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> sort -> Type :=
| inferE_sort_Sort t T u:
  Σ ;;; Γ |-E t ▹ T ->
  red Σ Γ T (tSort u) ->
  Σ ;;; Γ |-E t ▹□ u

with infering_prodE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> aname -> term -> term -> Type :=
| inferE_prod_Prod t T na A B:
  Σ ;;; Γ |-E t ▹ T ->
  red Σ Γ T (tProd na A B) ->
  Σ ;;; Γ |-E t ▹Π (na,A,B)

with infering_induE `{checker_flags} (Σ : global_env_ext) (Γ : context) : inductive -> term -> Instance.t -> list term -> Type :=
| inferE_ind_Ind ind t T u args:
  Σ ;;; Γ |-E t ▹ T ->
  red Σ Γ T (mkApps (tInd ind u) args) ->
  Σ ;;; Γ |-E t ▹{ind} (u,args)

with checkingE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| checkE_Cumul t T T':
  Σ ;;; Γ |-E t ▹ T ->
  JoinE Σ Γ Cumul T T' ->
  Σ ;;; Γ |-E t ◃ T'

where " Σ ;;; Γ |-E t ▹ T " := (@inferingE _ Σ Γ t T) : type_scope
and " Σ ;;; Γ |-E t ▹□ u " := (@infering_sortE _ Σ Γ t u) : type_scope
and " Σ ;;; Γ |-E t ▹Π ( na , A , B ) " := (@infering_prodE _ Σ Γ t na A B) : type_scope
and " Σ ;;; Γ |-E t ▹{ ind } ( u , args ) " := (@infering_induE _ Σ Γ ind t u args) : type_scope
and " Σ ;;; Γ |-E t ◃ T " := (@checkingE _ Σ Γ t T) : type_scope
and "'wf_local_bdE' Σ Γ" := (All_local_env (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ)
and "'wf_local_bd_relE' Σ Γ Γ'" := (All_local_rel (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ Γ').

(** ** Bridges to the checker's forecast form (design point A)

  The forecast compares with [ws_cumul_pbE]. Forecast ⇒ here: [ws_cumul_pbE_forget],
  no premise. Here ⇒ forecast: [into_ws_cumul_pbE], given the scoping. *)

Lemma checkE_Cumul_ws `{checker_flags} {Σ Γ t T T'} :
  Σ ;;; Γ |-E t ▹ T -> ws_cumul_pbE Cumul Σ Γ T T' -> Σ ;;; Γ |-E t ◃ T'.
Proof. intros ht hc. econstructor; [exact ht|exact (ws_cumul_pbE_forget hc)]. Qed.

Lemma All2_ws_cumul_pbE_JoinE `{checker_flags} {Σ Γ l l'} :
  All2 (ws_cumul_pbE Conv Σ Γ) l l' -> All2 (JoinE Σ Γ Conv) l l'.
Proof. intros h. eapply All2_impl; [exact h|]. intros x y hxy. exact (ws_cumul_pbE_forget hxy). Qed.

Lemma JoinE_ws_cumul_pbE `{checker_flags} {Σ Γ pb T T'} :
  is_closed_context Γ -> is_open_term Γ T -> is_open_term Γ T' ->
  JoinE Σ Γ pb T T' -> ws_cumul_pbE pb Σ Γ T T'.
Proof. intros hΓ hT hT' hj. exact (into_ws_cumul_pbE hj hΓ hT hT'). Qed.

(** ** The (co)fixpoint witness: red ⇒ [conv_witnessE] (design point B, soundness)

  Per declaration, copy 17's [mfix_body_on_red_convE] ([PCUICFixWitnessEta]), the twin of
  [PCUICFixWitness.v:244-254] with [wf Σ] replaced by [ClosedBodies Σ] (a reduction fact). *)

Section FixWitnessRedConv.
  Context {cf : checker_flags} {Σ : global_env_ext} {cb : ClosedBodies Σ}.

  Lemma wf_fixpoint_red_wf_fixpointE {Γ mfix} :
    is_closed_context Γ -> All (fun d => is_open_term Γ (dtype d)) mfix ->
    wf_fixpoint_red Σ Γ mfix -> wf_fixpointE Σ Γ mfix.
  Proof using cb.
    intros clΓ allop (isl & hr & h).
    split; [exact isl|split; [exact hr|]].
    refine (mfix_on_ind_All2 _ (fun _ hk => hk) h).
    apply All_All2_refl. eapply All_impl; [exact allop|]. intros d opd m.
    now apply mfix_body_on_red_convE.
  Qed.

  Lemma wf_cofixpoint_red_wf_cofixpointE {Γ mfix} :
    is_closed_context Γ -> All (fun d => is_open_term Γ (dtype d)) mfix ->
    wf_cofixpoint_red Σ Γ mfix -> wf_cofixpointE Σ Γ mfix.
  Proof using cb.
    intros clΓ allop h.
    refine (mfix_on_ind_All2 _ (fun _ hk => hk) h).
    apply All_All2_refl. eapply All_impl; [exact allop|]. intros d opd m.
    now apply mfix_body_on_red_convE.
  Qed.

End FixWitnessRedConv.

Definition tybranchesE {cf} Σ Γ ci mdecl idecl p ptm n ctors brs :=
  All2i
  (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
    (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
    let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
    (wf_local_bd_relE Σ Γ brctxty.1) ×
    Σ;;; Γ,,, brctxty.1 |-E bbody br ◃ brctxty.2)
  n ctors brs.

Definition branchesE_size {cf} {Σ Γ ci mdecl idecl p ptm brs}
   (checking_size : forall Σ Γ t T, Σ ;;; Γ |-E t ◃ T  -> size)
   (infering_size : forall Σ Γ t s, Σ ;;; Γ |-E t ▹□ s -> size)
  {n ctors}
  (a : tybranchesE Σ Γ ci mdecl idecl p ptm n ctors brs) : size :=

  (all2i_size _ (fun i cdecl br p =>
    (Nat.max
      (All_local_rel_sorting_size (checking_size Σ) (infering_size _) _ _ p.2.1)
      (checking_size _ _ _ _ p.2.2)))
  a).

Fixpoint inferingE_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |-E t ▹ T) {struct d} : size
with infering_sortE_size `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |-E t ▹□ u) {struct d} : size
with infering_prodE_size `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |-E t ▹Π (na, A,B)) {struct d} : size
with infering_induE_size `{checker_flags} {Σ Γ ind t ui args} (d : Σ ;;; Γ |-E t ▹{ind} (ui,args)) {struct d} : size
with checkingE_size `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |-E t ◃ T) {struct d} : size.
Proof.
  all: destruct d ;
    repeat lazymatch goal with
          | H : inferingE _ _ _ _ |- _ => apply inferingE_size in H
          | H : infering_sortE _ _ _ _ |- _ => apply infering_sortE_size in H
          | H : infering_prodE _ _ _ _ _ _ |- _ => apply infering_prodE_size in H
          | H : infering_induE _ _ _ _ _ _ |- _ => apply infering_induE_size in H
          | H : checkingE _ _ _ _ |- _ => apply checkingE_size in H
          | H : wf_local_bdE _ _ |- _ => apply (All_local_env_sorting_size _ _ (checkingE_size _ _) (infering_sortE_size _ _) _) in H
          | H : wf_local_bd_relE _ _ _ |- _ => apply (All_local_rel_sorting_size (checkingE_size _ _) (infering_sortE_size _ _) _) in H
          | H : primitive_typing_hyps _ _ _ _ |- _ => apply (primitive_typing_hyps_size _ (checkingE_size _)) in H
          end ;
    match goal with
    | H : lift_sorting _ _ _, H' : size |- _ => exact (S (Nat.max H' (lift_sorting_size (checkingE_size _ _ _) (infering_sortE_size _ _ _) _ H)))
    | H : All2i _ _ _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | |- _ => exact 1
    end.
    - exact (S (Nat.max a0 (Nat.max i (Nat.max i0 (Nat.max (ctx_inst_size _ (checkingE_size _) c1) (branchesE_size (checkingE_size _) (infering_sortE_size _) a2)))))).
    - exact (S (Nat.max
        (all_size _ (fun x p => on_def_type_sorting_size (infering_sortE_size _ Σ) _ _ p) a)
        (all_size (on_def_body _ _ _) (fun x p => on_def_body_sorting_size (checkingE_size _ _) (infering_sortE_size _ Σ) _ _ _ p) a0))).
    - exact (S (Nat.max
        (all_size _ (fun x p => on_def_type_sorting_size (infering_sortE_size _ Σ) _ _ p) a)
        (all_size (on_def_body _ _ _) (fun x p => on_def_body_sorting_size (checkingE_size _ _) (infering_sortE_size _ Σ) _ _ _ p) a0))).
  Defined.

Fixpoint inferingE_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |-E t ▹ T)
  : inferingE_size d > 0
with infering_sortE_size_pos `{checker_flags} {Σ Γ t u} (d : Σ ;;; Γ |-E t ▹□ u) {struct d}
  : infering_sortE_size d > 0
with infering_prodE_size_pos `{checker_flags} {Σ Γ t na A B} (d : Σ ;;; Γ |-E t ▹Π (na,A,B)) {struct d}
  : infering_prodE_size d > 0
with infering_induE_size_pos `{checker_flags} {Σ Γ t ind ui args} (d : Σ ;;; Γ |-E t ▹{ind} (ui,args)) {struct d}
  : infering_induE_size d > 0
with checkingE_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |-E t ◃ T) {struct d}
  : checkingE_size d > 0.
Proof.
  all: destruct d ; cbn.
  all: lia.
Qed.

Section BidirectionalInductionE.

  (* Named [wfl_sizeE]/[wfl_size_relE], not base's [wfl_size]/[wfl_size_rel]: they abbreviate the
     sizes over the E judgments, and the same-name rule (cross-lane-commitments.md C6) forbids a
     second object under a base name. *)
  #[local] Notation wfl_sizeE := (All_local_env_sorting_size (@checkingE_size _ _) (@infering_sortE_size _ _) _).
  #[local] Notation wfl_size_relE := (All_local_rel_sorting_size (@checkingE_size _ _) (@infering_sortE_size _ _) _ _).

  Context `{cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wfE Σ).
  Context (Pcheck : context -> term -> term -> Type).
  Context (Pinfer : context -> term -> term -> Type).
  Context (Psort : context -> term -> sort -> Type).
  Context (Pprod : context -> term -> aname -> term -> term -> Type).
  Context (Pind : context -> inductive -> term -> Instance.t -> list term -> Type).
  Context (Pj : context -> judgment -> Type).
  Context (PΓ : context -> Type).
  Context (PΓ_rel : context -> context -> Type).

(** This is what we wish to prove mutually given the previous predicates *)
  Definition env_prop_bdE :=
    (forall Γ j, lift_sorting1 (checkingE Σ) (infering_sortE Σ) Γ j -> Pj Γ j) ×
    (forall Γ , wf_local_bdE Σ Γ -> PΓ Γ) ×
    (forall Γ Γ', wf_local_bd_relE Σ Γ Γ' -> PΓ_rel Γ Γ') ×
    (forall Γ t T, Σ ;;; Γ |-E t ◃ T -> Pcheck Γ t T) ×
    (forall Γ t T, Σ ;;; Γ |-E t ▹ T -> Pinfer Γ t T) ×
    (forall Γ t u, Σ ;;; Γ |-E t ▹□ u -> Psort Γ t u) ×
    (forall Γ t na A B, Σ ;;; Γ |-E t ▹Π (na,A,B) -> Pprod Γ t na A B) ×
    (forall Γ ind t u args, Σ ;;; Γ |-E t ▹{ind} (u,args) -> Pind Γ ind t u args).

  (** To prove the needed induction principle, we unite all possible typing judgments in a big sum type,
      on which we define a suitable notion of size, wrt. which we perform well-founded induction
  *)

  Inductive typing_sumE : Type :=
    | judgment_consE : forall (Γ : context) j, lift_sorting1 (checkingE Σ) (infering_sortE Σ) Γ j -> typing_sumE
    | context_consE : forall (Γ : context) (wfΓ : wf_local_bdE Σ Γ), typing_sumE
    | context_rel_consE : forall (Γ Γ' : context) (wfΓ' : wf_local_bd_relE Σ Γ Γ'), typing_sumE
    | check_consE : forall (Γ : context) T t, Σ ;;; Γ |-E t ◃ T -> typing_sumE
    | inf_consE : forall (Γ : context) T t, Σ ;;; Γ |-E t ▹ T -> typing_sumE
    | sort_consE : forall (Γ : context) t u, Σ ;;; Γ |-E t ▹□ u -> typing_sumE
    | prod_consE : forall (Γ : context) t na A B, Σ ;;; Γ |-E t ▹Π (na,A,B) -> typing_sumE
    | ind_consE : forall (Γ : context) ind t u args, Σ ;;; Γ |-E t ▹{ind} (u,args) -> typing_sumE.

  Definition typing_sumE_size (d : typing_sumE) :=
  match d with
    | judgment_consE _ _ d => (lift_sorting_size (@checkingE_size _ _ _) (@infering_sortE_size _ _ _) _ d)
    | context_consE Γ wfΓ => wfl_sizeE wfΓ
    | context_rel_consE _ _ wfΓ' => wfl_size_relE wfΓ'
    | check_consE _ _ _ d => (checkingE_size d)
    | inf_consE _ _ _ d => (inferingE_size d)
    | sort_consE _ _ _ d => (infering_sortE_size d)
    | prod_consE _ _ _ _ _ d => (infering_prodE_size d)
    | ind_consE _ _ _ _ _ d => (infering_induE_size d)
  end.

  Definition Ptyping_sumE (d : typing_sumE) :=
  match d with
    | judgment_consE Γ j _ => Pj Γ j
    | context_consE Γ _ => PΓ Γ
    | context_rel_consE Γ Γ' _ => PΓ_rel Γ Γ'
    | check_consE Γ T t _ => Pcheck Γ t T
    | inf_consE Γ T t _ => Pinfer Γ t T
    | sort_consE Γ T u _ => Psort Γ T u
    | prod_consE Γ T na A B _ => Pprod Γ T na A B
    | ind_consE Γ ind T u args _ => Pind Γ ind T u args
  end.

  Ltac applyIH := match goal with
    | IH : forall d', _ -> Ptyping_sumE d' |- Pj ?Γ ?j =>
      unshelve eapply (IH (judgment_consE Γ j _))
    | IH : forall d', _ -> Ptyping_sumE d' |- PΓ ?Γ =>
      unshelve eapply (IH (context_consE Γ _))
    | IH : forall d', _ -> Ptyping_sumE d' |- PΓ_rel ?Γ ?Γ' =>
      unshelve eapply (IH (context_rel_consE Γ Γ' _))
    | IH : forall d', _ -> Ptyping_sumE d' |- Pcheck ?Γ ?t ?T =>
      unshelve eapply (IH (check_consE Γ T t _))
    | IH : forall d', _ -> Ptyping_sumE d' |- Pinfer ?Γ ?t ?T =>
      unshelve eapply (IH (inf_consE Γ T t _))
    | IH : forall d', _ -> Ptyping_sumE d'|- Psort ?Γ ?t ?u =>
      unshelve eapply (IH (sort_consE Γ t u _))
    | IH : forall d', _ -> Ptyping_sumE d' |- Pprod ?Γ ?t ?na ?A ?B =>
      unshelve eapply (IH (prod_consE Γ t na A B _))
    | IH : forall d', _ -> Ptyping_sumE d' |- Pind ?Γ ?ind ?t ?u ?args =>
      unshelve eapply (IH (ind_consE Γ ind t u args _))
    end ;
    match goal with
    | |- dlexprod _ _ _ _ => constructor ; cbn ; lia
    | |- dlexprod _ _ _ _ =>
            constructor 2 ; cbn ; try lia
    | _ => assumption
    | wfΓ' : wf_local_bd_relE _ _ _ |- _ => fold (wfl_size_relE wfΓ'); cbn -[Nat.max] ; lia
    | _ => cbn -[Nat.max] ; lia
    | _ => idtac
    end.

  Lemma bidir_ind_envE :
    let Pdecl_check := fun Γ wfΓ t T tyT => Pcheck Γ t T in
    let Pdecl_sort := fun Γ wfΓ t u tyT => Psort Γ t u in
    let Pdecl_check_rel Γ := fun Δ _ t T _ => Pcheck (Γ,,,Δ) t T in
    let Pdecl_sort_rel Γ := fun Δ _ t u _ => Psort (Γ,,,Δ) t u in

    (forall (Γ : context) j,
      lift_sorting1 (fun Γ t T => checkingE Σ Γ t T × Pcheck Γ t T) (fun Γ t u => infering_sortE Σ Γ t u × Psort Γ t u) Γ j -> Pj Γ j) ->

    (forall (Γ : context) (wfΓ : wf_local_bdE Σ Γ),
      All_local_env_over_sorting (checkingE Σ) (infering_sortE Σ) Pdecl_check Pdecl_sort Γ wfΓ ->
      All_local_env (lift_sorting1 Pcheck Psort) Γ ->
      PΓ Γ) ->

    (forall (Γ Γ' : context) (wfΓ' : wf_local_bd_relE Σ Γ Γ'),
      All_local_env_over_sorting (fun Δ => checkingE Σ (Γ,,,Δ)) (fun Δ => infering_sortE Σ (Γ,,,Δ)) (Pdecl_check_rel Γ) (Pdecl_sort_rel Γ) Γ' wfΓ' ->
      All_local_rel (lift_sorting1 Pcheck Psort) Γ Γ' ->
      PΓ_rel Γ Γ') ->

    (forall (Γ : context) (n : nat) decl,
      nth_error Γ n = Some decl ->
      Pinfer Γ (tRel n) (lift0 (S n) (decl_type decl))) ->

    (forall (Γ : context) (s : sort),
      wf_sort Σ s->
      Pinfer Γ (tSort s) (tSort (Sort.super s))) ->

    (forall (Γ : context) (na : aname) (t b : term) (s1 s2 : sort),
      lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vass_s na t s1) ->
      Pj Γ (j_vass_s na t s1) ->
      Σ ;;; Γ,, vass na t |-E b ▹□ s2 ->
      Psort (Γ,, vass na t) b s2 ->
      Pinfer Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

    (forall (Γ : context) (na : aname) (t b bty : term),
      lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vass na t) ->
      Pj Γ (j_vass na t) ->
      Σ ;;; Γ,, vass na t |-E b ▹ bty ->
      Pinfer (Γ,, vass na t) b bty ->
      Pinfer Γ (tLambda na t b) (tProd na t bty)) ->

    (forall (Γ : context) (na : aname) (b B t A : term),
      lift_sorting (checkingE Σ Γ) (infering_sortE Σ Γ) (j_vdef na b B) ->
      Pj Γ (j_vdef na b B) ->
      Σ ;;; Γ,, vdef na b B |-E t ▹ A ->
      Pinfer (Γ,, vdef na b B) t A ->
      Pinfer Γ (tLetIn na b B t) (tLetIn na b B A)) ->

    (forall (Γ : context) (t : term) na A B u,
      Σ ;;; Γ |-E t ▹Π (na, A, B) ->
      Pprod Γ t na A B ->
      Σ ;;; Γ |-E u ◃ A ->
      Pcheck Γ u A ->
      Pinfer Γ (tApp t u) (subst10 u B)) ->

    (forall (Γ : context) (cst : kername) u (decl : constant_body),
      declared_constant Σ.1 cst decl ->
      consistent_instance_ext Σ (cst_universes decl) u ->
      Pinfer Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall (Γ : context) (ind : inductive) u mdecl idecl,
      declared_inductive Σ.1 ind mdecl idecl ->
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      Pinfer Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall (Γ : context) (ind : inductive) (i : nat) u
      mdecl idecl cdecl,
      declared_constructor Σ.1 (ind, i) mdecl idecl cdecl ->
      consistent_instance_ext Σ (ind_universes mdecl) u ->
      Pinfer Γ (tConstruct ind i u)
        (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Γ : context) ci p c brs args u ps mdecl idecl,
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      Σ ;;; Γ |-E c ▹{ci} (u,args) ->
      Pind Γ ci.(ci_ind) c u args ->
      declared_inductive Σ.1 ci.(ci_ind) mdecl idecl ->
      Σ ;;; Γ ,,, predctx |-E p.(preturn) ▹□ ps ->
      Psort (Γ ,,, predctx) p.(preturn) ps ->
      (* case_side_conditions (fun Σ Γ => wf_local Σ Γ) checking Σ Γ ci p ps
        mdecl idecl indices predctx -> *) (*issue with wf_local_rel vs wf_local *)
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) (puinst p) ->
      wf_local_bd_relE Σ Γ predctx ->
      PΓ_rel Γ predctx ->
      is_allowed_elimination Σ (ind_kelim idecl) ps ->
      isSortRel ps ci.(ci_relevance) ->
      ctx_inst (checkingE Σ) Γ (pparams p)
          (List.rev mdecl.(ind_params)@[p.(puinst)]) ->
      ctx_inst Pcheck Γ p.(pparams)
          (List.rev (subst_instance p.(puinst) mdecl.(ind_params))) ->
      implb (isCoFinite mdecl.(ind_finite)) (on_free_vars (strengthenP 0 1 ssrbool.xpredT) p.(preturn)) = true ->
      cmp_ind_universes Σ ci #|args| u (puinst p) ->
      All2 (JoinE Σ Γ Conv) (firstn (ci_npar ci) args) (pparams p) ->
      (* case_branch_typing *)
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        wf_local_bd_relE Σ Γ brctxty.1 ×
        PΓ_rel Γ brctxty.1 ×
        Σ ;;; Γ ,,, brctxty.1 |-E br.(bbody) ◃ brctxty.2 ×
        Pcheck (Γ ,,, brctxty.1) br.(bbody) brctxty.2)
        0 idecl.(ind_ctors) brs ->
      Pinfer Γ (tCase ci p c brs) (mkApps ptm (skipn ci.(ci_npar) args ++ [c]))) ->

    (forall (Γ : context) (p : projection) (c : term) u
      mdecl idecl cdecl pdecl args,
      declared_projection Σ.1 p mdecl idecl cdecl pdecl ->
      Σ ;;; Γ |-E c ▹{p.(proj_ind)} (u,args) ->
      Pind Γ p.(proj_ind) c u args ->
      #|args| = ind_npars mdecl ->
      Pinfer Γ (tProj p c) (subst0 (c :: List.rev args) pdecl.(proj_type)@[u])) ->

    (forall (Γ : context) (mfix : mfixpoint term) (n : nat) decl,
      fix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      All (on_def_type (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ) mfix ->
      All (on_def_type Pj Γ) mfix ->
      All (on_def_body (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) (fix_context mfix) Γ) mfix ->
      All (on_def_body Pj (fix_context mfix) Γ) mfix ->
      wf_fixpoint_red Σ Γ mfix ->
      Pinfer Γ (tFix mfix n) (dtype decl)) ->

    (forall (Γ : context) (mfix : mfixpoint term) (n : nat) decl,
      cofix_guard Σ Γ mfix ->
      nth_error mfix n = Some decl ->
      All (on_def_type (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) Γ) mfix ->
      All (on_def_type Pj Γ) mfix ->
      All (on_def_body (lift_sorting1 (checkingE Σ) (infering_sortE Σ)) (fix_context mfix) Γ) mfix ->
      All (on_def_body Pj (fix_context mfix) Γ) mfix ->      wf_cofixpoint_red Σ Γ mfix ->
      Pinfer Γ (tCoFix mfix n) (dtype decl)) ->

    (forall (Γ : context) p prim_ty cdecl,
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps (checkingE Σ) Σ Γ p ->
      primitive_typing_hyps Pcheck Σ Γ p ->
      Pinfer Γ (tPrim p) (prim_type p prim_ty)) ->

    (forall (Γ : context) (t T : term) (u : sort),
      Σ ;;; Γ |-E t ▹ T ->
      Pinfer Γ t T ->
      red Σ Γ T (tSort u) ->
      Psort Γ t u) ->

    (forall (Γ : context) (t T : term) (na : aname) (A B : term),
      Σ ;;; Γ |-E t ▹ T ->
      Pinfer Γ t T ->
      red Σ Γ T (tProd na A B) ->
      Pprod Γ t na A B) ->

    (forall (Γ : context) (ind : inductive) (t T : term) (ui : Instance.t)
      (args : list term),
      Σ ;;; Γ |-E t ▹ T ->
      Pinfer Γ t T ->
      red Σ Γ T (mkApps (tInd ind ui) args) ->
      Pind Γ ind t ui args) ->

    (forall (Γ : context) (t T T' : term),
      Σ ;;; Γ |-E t ▹ T ->
      Pinfer Γ t T ->
      JoinE Σ Γ Cumul T T' ->
      Pcheck Γ t T') ->

    env_prop_bdE.
  Proof using Type.
    intros Pdecl_check Pdecl_sort Pdecl_check_rel Pdecl_sort_rel Hj HΓ HΓRel HRel HSort HProd HLambda HLetIn HApp HConst HInd HConstruct HCase
      HProj HFix HCoFix HPrim HiSort HiProd HiInd HCheck ; unfold env_prop_bdE.
      pose (@Fix_F typing_sumE (precompose lt typing_sumE_size) Ptyping_sumE) as p.
    forward p.
    2:{
    enough (HP : forall x : typing_sumE, Ptyping_sumE x).
    - repeat split ; intros.
      + exact (HP (judgment_consE Γ j X)).
      + exact (HP (context_consE Γ X)).
      + exact (HP (context_rel_consE Γ Γ' X)).
      + exact (HP (check_consE Γ T t X)).
      + exact (HP (inf_consE Γ T t X)).
      + exact (HP (sort_consE Γ t u X)).
      + exact (HP (prod_consE Γ t na A B X)).
      + exact (HP (ind_consE Γ ind t u args X)).
    - intros x ; apply p.
      apply wf_precompose ; apply lt_wf.
    }
    clear p.
    intros d IH.
    destruct d ; simpl.
    5: destruct i.

    - eapply Hj; tea.
      eapply lift_sorting_size_impl with (csize := @checkingE_size _ _ _) (ssize := @infering_sortE_size _ _ _) (tu := l).
      all: intros ?? Hty Hlt; split; tas.
      all: applyIH.

    - eapply HΓ.
      2: { clear -IH wfΣ. induction wfΓ; cbn in *; simpl in *; constructor.
        1,3: apply IHwfΓ; intros; apply IH; lia.
        all: assert (0 < wfl_sizeE wfΓ) as Hpos by apply All_local_env_size_pos.
        all: eapply lift_sorting_size_impl with (csize := @checkingE_size _ _ _) (ssize := @infering_sortE_size _ _ _) (tu := t0).
        all: intros ?? Hty Hlt; unfold lift_sorting_size in Hlt; simpl in Hlt.
        all: applyIH. }
      dependent induction wfΓ.
      + constructor.
      + constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          cbn in H |- *. lia.
        * destruct t0 as (? & s & Hty & ?); cbn in *.
          assert (0 < wfl_sizeE wfΓ) by apply All_local_env_size_pos.
          red.
          applyIH.
      + destruct t0 as (Htm & s & Hty & _e); cbn in *.
        assert (0 < wfl_sizeE wfΓ) by apply All_local_env_size_pos.
        constructor.
        * apply IHwfΓ.
          intros ; apply IH.
          cbn in H |- *. lia.
        * red. cbn. applyIH.
        * red. cbn. applyIH.

    - eapply HΓRel.
      2: { clear -IH wfΣ. induction wfΓ'; cbn in *; simpl in *; constructor; fold (wf_local_bd_relE Σ Γ Γ0) in wfΓ'.
      1,3: apply IHwfΓ'; intros; apply IH; fold (wfl_size_relE wfΓ'); lia.
      all: assert (0 < wfl_size_relE wfΓ') as Hpos by apply All_local_env_size_pos.
      all: eapply lift_sorting_size_impl with (csize := @checkingE_size _ _ _) (ssize := @infering_sortE_size _ _ _) (tu := t0).
      all: intros ?? Hty Hlt; unfold lift_sorting_size in Hlt; simpl in Hlt.
      all: applyIH. }
      dependent induction wfΓ'; try fold (wf_local_bd_relE Σ Γ Γ0) in wfΓ'.
      + constructor.
      + constructor.
        * apply IHwfΓ'.
          intros ; apply IH.
          cbn in H |- *.
          fold (wfl_size_relE wfΓ').
          lia.
        * destruct t0 as (? & s & Hty & ?); cbn in *. red.
          assert (0 < wfl_size_relE wfΓ') by apply All_local_env_size_pos.
          applyIH.
      + destruct t0 as (Htm & s & Hty & _e); cbn in *.
        assert (0 < wfl_size_relE wfΓ') by apply All_local_env_size_pos.
        constructor.
        * apply IHwfΓ'.
          intros ; apply IH.
          cbn in H |- *.
          fold (wfl_size_relE wfΓ').
          lia.
        * red. cbn. applyIH.
        * red. cbn. applyIH.


    - destruct c.
      unshelve (eapply HCheck ; eauto) ; auto.
      all: applyIH.

    - unshelve eapply HRel ; auto.
      all: applyIH.

    - unshelve eapply HSort ; auto.
      all: applyIH.

    - unshelve eapply HProd ; auto.
      all: applyIH.

    - unshelve eapply HLambda ; auto.
      all: applyIH.

    - unshelve eapply HLetIn ; auto.
      all: applyIH.

    - eapply HApp ; eauto.
      all: applyIH.

    - unshelve eapply HConst ; auto.
      all: applyIH.

    - unshelve eapply HInd ; auto.
      all: applyIH.

    - unshelve eapply HConstruct ; auto.
      all: applyIH.

    - unshelve eapply HCase ; auto.
      1-3: by applyIH.
      + cbn in IH.
        clear - IH c1.
        induction c1.
        1: by constructor.
        * constructor.
          1: by applyIH.
          apply IHc1.
          intros.
          apply IH.
          cbn.
          lia.
        * constructor.
          apply IHc1.
          intros.
          apply IH.
          cbn -[Nat.max].
          lia.

      + cbn in IH.
        clear - IH a2.
        induction a2 as [|j cdecl br cdecls brs].
        1: by constructor.
        destruct r as (?&?&?).
        constructor.
        * repeat split.
          all: try assumption.
          all: applyIH.
          cbn.
          fold predctx ptm (wfl_size_relE a1).
          lia.
        * apply IHa2.
          intros.
          apply IH.
          simpl.
          lia.

    - unshelve eapply HProj ; auto.
      all: applyIH.

    - unshelve eapply HFix ; eauto.

      all: simpl in IH.
      all: remember (fix_context mfix) as mfixcontext.

      + remember (all_size _ _ a0) as s.
        clear -IH.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        * unfold on_def_type. applyIH.
        * apply (IHa s).
          intros.
          apply IH.
          cbn [all_size]. lia.

      + remember (all_size _ _ a) as size.
        clear -IH.
        induction a0.
        1: by constructor.
        constructor.
        * unfold on_def_body. applyIH.
        * apply IHa0.
          intros.
          apply IH.
          cbn in H |- *. lia.

    - unshelve eapply HCoFix ; eauto.

      all: cbn [typing_sumE_size inferingE_size] in IH.
      all: remember (fix_context mfix) as mfixcontext.
      + remember (all_size _ _ a0) as s.
        clear -IH.
        dependent induction a.
        1: by constructor.
        constructor ; cbn.
        * unfold on_def_type. applyIH.
        * apply (IHa s).
          intros.
          apply IH.
          cbn [all_size]. lia.

      + remember (all_size _ _ a) as size.
        clear -IH.
        induction a0.
        1: by constructor.
        constructor.
        * unfold on_def_body. applyIH.
        * apply IHa0.
          intros.
          apply IH.
          cbn in H |- *. lia.

    - unshelve eapply HPrim; eauto.
      simpl in IH.
      destruct p1; constructor; eauto.
      applyIH. applyIH. simpl in IH.
      clear -IH. induction hvalue; constructor; eauto.
      eapply (IH (check_consE _ _ _ p)). simpl; lia.
      eapply IHhvalue. intros; simpl. eapply IH. simpl. lia.

    - destruct i.
      unshelve (eapply HiSort ; try eassumption) ; try eassumption.
      all:applyIH.

    - destruct i.
      unshelve (eapply HiProd ; try eassumption) ; try eassumption.
      all: applyIH.

    - destruct i.
      unshelve (eapply HiInd ; try eassumption) ; try eassumption.
      all: applyIH.
Qed.

End BidirectionalInductionE.
