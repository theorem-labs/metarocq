(** * Concrete instances of the premises of [trans_on_prim_decl_t2p]

    [trans_on_prim_decl_t2p] ([TemplateToPCUICCorrectness]) states that the
    Template→PCUIC translation preserves the [on_prim_decl] condition of a
    declaration.  Its premises are: Template's [Typing.wf Σg], PCUIC's [wf] of
    [trans_global_env Σg], the declaration's [Typing.on_global_decl] condition
    (with [WfAst.wf_decl_pred]), the closedness of its translated type, and its
    [Typing.on_prim_decl] condition.

    Each premise is proved here for the declaration [land] of the Template
    environment [Σ_po] of [prim_ops_instance_template.v], at the prefix it is
    checked against ([Σg := Σ_po_int], [ud := Monomorphic_ctx]), and the lemma
    is then applied to them.  The translation of [Σ_po_int] computes to
    [PCUICPrimInstances.Σ_po_int], whose PCUIC [wf] is
    [PCUICPrimInstanceTrans.Σ_po_int_wf]. *)

From MetaRocq.Utils Require Import utils.
From Stdlib Require Import ssreflect.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.PCUIC Require PCUICTyping PCUICCumulativitySpec PCUICProgram
  PCUICPrimInstances PCUICPrimInstanceTrans.
From MetaRocq.TemplatePCUIC Require TemplateToPCUIC TemplateToPCUICCorrectness.
From MetaRocq.TestSuite Require Import prim_ops_instance_template.

Import ListNotations.

Local Existing Instance default_checker_flags.

(** Premise [X0 : Typing.wf Σg] of [trans_on_prim_decl_t2p], at
    [Σg := Σ_po_int]. *)
Lemma Σ_po_int_wf_template : Typing.wf Σ_po_int.
Proof.
  split; [exact po_univs_ok|]. split; [exact po_retro_wf|].
  cbn. constructor; [constructor|].
  econstructor.
  - constructor.
  - exact po_udecl_ok.
  - cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
  - cbn. intros op hop. discriminate hop.
Qed.

(** The typing condition of [land] at the prefix [Σ_po_int]; the premise
    [Typing.on_global_decl] of [trans_on_prim_decl_t2p] is its
    [WfAst.wf_decl_pred] form, by [on_global_decl_wf]. *)
Lemma Σ_po_land_on_global_decl_template :
  Typing.on_global_decl Typing.cumul_gen (Typing.TemplateEnvTyping.lift_typing Typing.typing)
    (Σ_po_int, Monomorphic_ctx) po_land_kn (ConstantDecl po_land_body).
Proof.
  cbn. split; [exact tt|].
  exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
  repeat split. exact po_land_type_typed.
Qed.

(** Premise [Typing.on_prim_decl Typing.cumul_gen (Σg, ud) kn d] of
    [trans_on_prim_decl_t2p], for [land] at [Σg := Σ_po_int],
    [ud := Monomorphic_ctx]. *)
Lemma Σ_po_land_on_prim_decl_template :
  Typing.on_prim_decl Typing.cumul_gen (Σ_po_int, Monomorphic_ctx) po_land_kn
    (ConstantDecl po_land_body).
Proof.
  cbn. intros op hop. injection hop as <-.
  constructor; cbn; try reflexivity.
  - exists po_land_ty. split; [reflexivity|]. apply conv_refl'.
  - repeat constructor.
    all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
  - exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

(** The translation of the Template [Σ_po_int] is the PCUIC [Σ_po_int]. *)
Lemma trans_Σ_po_int_env :
  PCUICProgram.trans_env_env (TemplateToPCUIC.trans_global_env Σ_po_int) =
  PCUICPrimInstances.Σ_po_int.
Proof. reflexivity. Qed.

(** Premise [wfΣg : wf (trans_global_env Σg)] of [trans_on_prim_decl_t2p], at
    [Σg := Σ_po_int]. *)
Lemma trans_Σ_po_int_wf :
  PCUICTyping.wf (PCUICProgram.trans_env_env (TemplateToPCUIC.trans_global_env Σ_po_int)).
Proof. rewrite trans_Σ_po_int_env. exact PCUICPrimInstanceTrans.Σ_po_int_wf. Qed.

(** Premise [forall cb, d = ConstantDecl cb -> closed (trans (trans_global_env Σg)
    cb.(cst_type))] of [trans_on_prim_decl_t2p], for [land] at
    [Σg := Σ_po_int]. *)
Lemma trans_Σ_po_land_closed :
  forall cb, ConstantDecl po_land_body = Ast.Env.ConstantDecl cb ->
  PCUICAst.closedn 0 (TemplateToPCUIC.trans (TemplateToPCUIC.trans_global_env Σ_po_int)
    cb.(Ast.Env.cst_type)).
Proof. intros cb [= <-]. reflexivity. Qed.

(** [trans_on_prim_decl_t2p] applied to its premises for [land]: the translated
    declaration satisfies PCUIC's [on_prim_decl] in the translated prefix. *)
Lemma trans_Σ_po_land_on_prim_decl :
  PCUICTyping.on_prim_decl PCUICCumulativitySpec.cumulSpec0
    (PCUICProgram.trans_env_env (TemplateToPCUIC.trans_global_env Σ_po_int), Monomorphic_ctx)
    po_land_kn
    (TemplateToPCUIC.trans_global_decl (TemplateToPCUIC.trans_global_env Σ_po_int)
       (ConstantDecl po_land_body)).
Proof.
  exact (TemplateToPCUICCorrectness.trans_on_prim_decl_t2p Σ_po_int Σ_po_int_wf_template
    trans_Σ_po_int_wf Monomorphic_ctx po_land_kn (ConstantDecl po_land_body)
    (TemplateToPCUICCorrectness.on_global_decl_wf (Σ := (Σ_po_int, Monomorphic_ctx))
       Σ_po_int_wf_template Σ_po_land_on_global_decl_template)
    trans_Σ_po_land_closed Σ_po_land_on_prim_decl_template).
Qed.

(** Beside the primitive libraries' axioms, only Template's [guard_checking],
    which the statement of [Typing.wf] names. *)
Print Assumptions trans_Σ_po_land_on_prim_decl.
