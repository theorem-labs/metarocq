(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICPrimitive
     PCUICOnFreeVars PCUICArityRed PCUICTyping
     PCUICCumulativitySpec PCUICCumulativitySpecEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation.
From Equations Require Import Equations.
Set Equations With UIP.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(** * Typing with function η

  [typingE] is a copy of base [typing] ([PCUICTyping]) in which the single
  conversion rule [type_Cumul] and the [conv_witness] used by the guard's
  [wf_fixpoint]/[wf_cofixpoint] premises are re-based on the η specification
  [cumulSpecE0]: [typingE] carries one conversion relation. The guard checker
  [fix_guard]/[cofix_guard] is unchanged. Its closure predicate [guard_cl]
  ([PCUICGuardClosure]) does read a conversion, in [gc_ctx], which is base
  [cumulSpec0]; the η copy of that file is not in this tree.

  [wfE]/[wf_extE] are the η well-formedness classes; [typing_incl_E] and
  [wf_incl_E] include the base relations into the η ones through
  [cumulSpec0_incl_E]. *)

(** The witness relation re-based on [convSpecE] = [cumulSpecE0 _ _ Conv]. *)
Definition conv_witnessE `{checker_flags} (Σ : global_env_ext) (Γ : context) (t ty : term) :=
  is_open_term Γ ty × convSpecE Σ Γ t ty.

Definition wf_fixpointE `{checker_flags} (Σ : global_env_ext) (Γ : context) (mfix : mfixpoint term) :=
  forallb (isLambda ∘ dbody) mfix × forallb has_rec_arg mfix ×
  mfix_on_ind check_one_fix (conv_witnessE Σ Γ)
    (fun mind => check_recursivity_kind (lookup_env Σ) mind Finite) mfix.

Definition wf_cofixpointE `{checker_flags} (Σ : global_env_ext) (Γ : context) (mfix : mfixpoint term) :=
  mfix_on_ind check_one_cofix (conv_witnessE Σ Γ)
    (fun mind => check_recursivity_kind (lookup_env Σ) mind CoFinite) mfix.

Reserved Notation "'wf_localE' Σ Γ " (at level 9, Σ, Γ at next level).
Reserved Notation " Σ ;;; Γ |-E t : T " (at level 50, Γ, t, T at next level).

Inductive typingE `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| typeE_Rel : forall n decl,
    wf_localE Σ Γ ->
    nth_error Γ n = Some decl ->
    Σ ;;; Γ |-E tRel n : lift0 (S n) decl.(decl_type)

| typeE_Sort : forall s,
    wf_localE Σ Γ ->
    wf_sort Σ s ->
    Σ ;;; Γ |-E tSort s : tSort (Sort.super s)

| typeE_Prod : forall na A B s1 s2,
    lift_typing typingE Σ Γ (j_vass_s na A s1) ->
    Σ ;;; Γ ,, vass na A |-E B : tSort s2 ->
    Σ ;;; Γ |-E tProd na A B : tSort (Sort.sort_of_product s1 s2)

| typeE_Lambda : forall na A t B,
    lift_typing typingE Σ Γ (j_vass na A) ->
    Σ ;;; Γ ,, vass na A |-E t : B ->
    Σ ;;; Γ |-E tLambda na A t : tProd na A B

| typeE_LetIn : forall na b B t A,
    lift_typing typingE Σ Γ (j_vdef na b B) ->
    Σ ;;; Γ ,, vdef na b B |-E t : A ->
    Σ ;;; Γ |-E tLetIn na b B t : tLetIn na b B A

| typeE_App : forall t na A B s u,
    Σ ;;; Γ |-E tProd na A B : tSort s ->
    Σ ;;; Γ |-E t : tProd na A B ->
    Σ ;;; Γ |-E u : A ->
    Σ ;;; Γ |-E tApp t u : B{0 := u}

| typeE_Const : forall cst u decl,
    wf_localE Σ Γ ->
    declared_constant Σ cst decl ->
    consistent_instance_ext Σ decl.(cst_universes) u ->
    Σ ;;; Γ |-E tConst cst u : decl.(cst_type)@[u]

| typeE_Ind : forall ind u mdecl idecl,
    wf_localE Σ Γ ->
    declared_inductive Σ ind mdecl idecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |-E tInd ind u : idecl.(ind_type)@[u]

| typeE_Construct : forall ind i u mdecl idecl cdecl,
    wf_localE Σ Γ ->
    declared_constructor Σ (ind, i) mdecl idecl cdecl ->
    consistent_instance_ext Σ mdecl.(ind_universes) u ->
    Σ ;;; Γ |-E tConstruct ind i u : type_of_constructor mdecl cdecl (ind, i) u

| typeE_Case : forall ci p c brs indices ps mdecl idecl,
    let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
    let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
    declared_inductive Σ ci.(ci_ind) mdecl idecl ->
    Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps ->
    Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
    case_side_conditions (fun Γ => wf_localE Σ Γ) (typingE Σ) Σ Γ ci p ps
                         mdecl idecl indices predctx  ->
    case_branch_typing (fun Γ => wf_localE Σ Γ) (typingE Σ) Γ ci p ps
                        mdecl idecl ptm brs ->
    Σ ;;; Γ |-E tCase ci p c brs : mkApps ptm (indices ++ [c])

| typeE_Proj : forall p c u mdecl idecl cdecl pdecl args,
    declared_projection Σ p mdecl idecl cdecl pdecl ->
    Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
    #|args| = ind_npars mdecl ->
    Σ ;;; Γ |-E tProj p c : subst0 (c :: List.rev args) pdecl.(proj_type)@[u]

| typeE_Fix : forall mfix n decl,
    wf_localE Σ Γ ->
    fix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (on_def_type (lift_typing1 (typingE Σ)) Γ) mfix ->
    All (on_def_body (lift_typing1 (typingE Σ)) (fix_context mfix) Γ) mfix ->
    wf_fixpointE Σ Γ mfix ->
    Σ ;;; Γ |-E tFix mfix n : decl.(dtype)

| typeE_CoFix : forall mfix n decl,
    wf_localE Σ Γ ->
    cofix_guard Σ Γ mfix ->
    nth_error mfix n = Some decl ->
    All (on_def_type (lift_typing1 (typingE Σ)) Γ) mfix ->
    All (on_def_body (lift_typing1 (typingE Σ)) (fix_context mfix) Γ) mfix ->
    wf_cofixpointE Σ Γ mfix ->
    Σ ;;; Γ |-E tCoFix mfix n : decl.(dtype)

| typeE_Prim p prim_ty cdecl :
    wf_localE Σ Γ ->
    primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
    declared_constant Σ prim_ty cdecl ->
    primitive_invariants (prim_val_tag p) cdecl ->
    primitive_typing_hyps (typingE Σ) Σ Γ p ->
    Σ ;;; Γ |-E tPrim p : prim_type p prim_ty

| typeE_Cumul : forall t A B s,
    Σ ;;; Γ |-E t : A ->
    Σ ;;; Γ |-E B : tSort s ->
    cumulSpecE Σ Γ A B ->
    Σ ;;; Γ |-E t : B

where " Σ ;;; Γ |-E t : T " := (typingE Σ Γ t T)
and "'wf_localE' Σ Γ " := (All_local_env (lift_typing1 (typingE Σ)) Γ).

(** ** E well-formedness classes. *)
Definition wfE `{checker_flags} := on_global_env cumulSpecE0 (lift_typing typingE).
Existing Class wfE.
#[global]
Hint Mode wfE + + : typeclass_intances.

Definition wf_extE `{checker_flags} := on_global_env_ext cumulSpecE0 (lift_typing typingE).
Existing Class wf_extE.
#[global]
Hint Mode wf_extE + + : typeclass_intances.

Inductive welltypedE {cf} Σ Γ t : Prop :=
| iswelltypedE A : Σ ;;; Γ |-E t : A -> welltypedE Σ Γ t.

Arguments iswelltypedE {cf Σ Γ t A} h.

(** ** Inclusion of the base relations into the E ones. *)

Lemma conv_witness_incl_E {cf : checker_flags} Σ Γ t ty :
  conv_witness Σ Γ t ty -> conv_witnessE Σ Γ t ty.
Proof.
  intros [h c]. split; [exact h|].
  exact (cumulSpec0_incl_E Σ Γ Conv t ty c).
Qed.

Lemma wf_fixpoint_incl_E {cf : checker_flags} Σ Γ mfix :
  wf_fixpoint Σ Γ mfix -> wf_fixpointE Σ Γ mfix.
Proof.
  intros (h1 & h2 & mind & ne & hb & hk).
  split; [exact h1|]. split; [exact h2|].
  exists mind. split; [exact ne|]. split; [|exact hk].
  eapply All_impl; [exact hb|].
  intros d [ty [e r]]. exists ty. split; [exact e|].
  now apply conv_witness_incl_E.
Qed.

Lemma wf_cofixpoint_incl_E {cf : checker_flags} Σ Γ mfix :
  wf_cofixpoint Σ Γ mfix -> wf_cofixpointE Σ Γ mfix.
Proof.
  intros (mind & ne & hb & hk).
  exists mind. split; [exact ne|]. split; [|exact hk].
  eapply All_impl; [exact hb|].
  intros d [ty [e r]]. exists ty. split; [exact e|].
  now apply conv_witness_incl_E.
Qed.

Lemma wf_localE_app_l {cf : checker_flags} Σ Γ Γ' :
  wf_localE Σ (Γ ,,, Γ') -> wf_localE Σ Γ.
Proof. intro h. now apply All_local_env_app_inv in h as []. Qed.
#[global]
Hint Immediate wf_localE_app_l : wf.

Lemma typing_incl_E_env `{checker_flags} :
  env_prop (fun Σ Γ t T => typingE Σ Γ t T)
           (fun Σ Γ j => lift_typing typingE Σ Γ j)
           (fun Σ Γ => wf_localE Σ Γ).
Proof.
  apply typing_ind_env.
  - (* Pj *) intros Σ wfΣ Γ j X.
    apply lift_typing_impl with (1 := X). now intros ?? [].
  - (* PΓ *) intros Σ wfΣ Γ wfΓ Hover Hall. exact Hall.
  - (* Rel *) intros; now econstructor.
  - (* Sort *) intros; now econstructor.
  - (* Prod *) intros; now econstructor.
  - (* Lambda *) intros; now econstructor.
  - (* LetIn *) intros; now econstructor.
  - (* App *) intros; now econstructor.
  - (* Const *) intros; now econstructor.
  - (* Ind *) intros; now econstructor.
  - (* Construct *) intros; now econstructor.
  - (* Case *)
    intros Σ wfΣ Γ wfΓ ci p c brs indices ps mdecl idecl isdecl Hglob HΓ
      eqnpars eqpctx predctx wfpred cons wfpredctxB pret IHpret HΓpred
      allowelim elimrel ctxinst Hc IHc cofin ptm wfbrs Hbrs.
    eapply typeE_Case; eauto.
    + econstructor; eauto.
      eapply ctx_inst_impl with (1 := ctxinst). now intros ?? [].
    + econstructor; eauto.
      eapply All2i_impl; [exact Hbrs|].
      intros i cdecl br. cbv beta.
      intros [eqc [hΓbr [[_ hbody] [_ hbty]]]].
      split; [exact eqc|]. split; [exact hΓbr|]. split; [exact hbody|exact hbty].
  - (* Proj *) intros; now econstructor.
  - (* Fix *)
    intros Σ wfΣ Γ wfΓ mfix n decl types guard hnth HΓtypes
      Hdt_b Hdt_E Hdb_b Hdb_E wffix.
    eapply typeE_Fix; try eassumption.
    + eapply wf_localE_app_l; exact HΓtypes.
    + now apply wf_fixpoint_incl_E.
  - (* CoFix *)
    intros Σ wfΣ Γ wfΓ mfix n decl types guard hnth HΓtypes
      Hdt_b Hdt_E Hdb_b Hdb_E wfcofix.
    eapply typeE_CoFix; try eassumption.
    + eapply wf_localE_app_l; exact HΓtypes.
    + now apply wf_cofixpoint_incl_E.
  - (* Prim *) intros; now econstructor.
  - (* Cumul *)
    intros Σ wfΣ Γ wfΓ t A B s HΓ Hta IHta HB IHB cum.
    eapply typeE_Cumul; [exact IHta|exact IHB|].
    now eapply cumulSpec0_incl_E.
Qed.

Lemma typing_incl_E `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ t T} :
  Σ ;;; Γ |- t : T -> Σ ;;; Γ |-E t : T.
Proof. intro h. exact (env_prop_typing typing_incl_E_env Σ wfΣ Γ t T h). Qed.

Lemma wf_local_incl_E `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} :
  wf_local Σ Γ -> wf_localE Σ Γ.
Proof. intro h. exact (env_prop_wf_local typing_incl_E_env Σ wfΣ Γ h). Qed.

Lemma wf_incl_E `{checker_flags} {Σ : global_env} :
  wf Σ -> wfE Σ.
Proof.
  intro wfΣ.
  unfold wfE, wf in *.
  eapply on_global_env_impl_config; [reflexivity| | |exact wfΣ].
  - intros Σ' Γ j HP HQ Hj.
    apply lift_typing_impl with (1 := Hj). intros t T HtT.
    now eapply typing_incl_E.
  - intros Σ' Γ t T pb HP HQ Hcmp.
    now eapply cumulSpec0_incl_E.
Qed.

Lemma wf_ext_incl_E `{checker_flags} {Σ : global_env_ext} :
  wf_ext Σ -> wf_extE Σ.
Proof.
  intros [hg hu]. split; [|exact hu].
  now eapply wf_incl_E.
Qed.
