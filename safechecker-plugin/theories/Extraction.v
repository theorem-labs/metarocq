(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import OrdersTac Ascii ExtrOcamlBasic ExtrOCamlInt63 ExtrOCamlFloats ExtrOCamlPString.
From MetaRocq.Utils Require Import utils.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl PCUICSafeChecker PCUICSafeConversion.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUICShared.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateChecker.

(** * Extraction setup for the safechecker phase of MetaRocq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)

(** Here we could extract uint63_from/to_model to the identity *)

Extraction Blacklist Classes config uGraph Universes Ast String List Nat Int Init
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality Classes
           Uint63 Induction Monad.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Extraction Inline Program.Wf.Fix_F_sub Program.Wf.Fix_sub.

Extraction Inline PCUICSafeConversion.Ret.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.
Extraction Inline Equations.Prop.Logic.transport Equations.Prop.Logic.transport_r MREquality.transport.
Extraction Inline Equations.Prop.Logic.True_rect_dep Equations.Prop.Logic.False_rect_dep.

(** This Inline is because of a problem of weak type variables (partial application?) *)
Extraction Inline PCUICPrimitive.prim_val_reflect_eq.

(** [memo_trans] and [trans_memo_release] are the Rocq identities
    ([TemplateToPCUICShared.v], [trans_shared_eq]), and they are extracted as
    they are written.  The two [Extract Constant] directives that replaced them
    by the memo of [trans_memo.ml] are gone: they put 7,206 bytes of
    hand-written OCaml inside the checker that [Print Assumptions] could not
    show -- the root report is the same 377 lines and 36 axioms with them and
    without them -- and they were measured to cost rather than save
    (LemmaPin_3: 1,452.99 s and 9.99 GiB without, 1,459.54 s and 11.00 GiB
    with, one concurrent pair, same box, 2 CPUs and 24 GiB each). *)

Set Extraction Output Directory "src".
(** The extracted checker runs the real, executable guard check
    [PCUICWfEnvImpl.real_guard_impl] ([check_guard_gen]). *)
Definition infer_and_print_template_program_with_guard {cf} {nor} :=
  @SafeTemplateChecker.infer_and_print_template_program cf nor PCUICWfEnvImpl.real_guard_impl.

Separate Extraction Wf.Fix_sub MakeOrderTac PCUICSafeChecker.typecheck_program
         infer_and_print_template_program_with_guard
         (* What the sharing test [MetaRocq Test Trans Sharing] calls *)
         SafeTemplateChecker.trans_program_unshared TemplateToPCUICShared.trans_shared
         TemplateToPCUIC.trans TemplateToPCUIC.trans_global_env TemplateToPCUIC.empty_trans_env
         (* The following directives ensure separate extraction does not produce name clashes *)
         Stdlib.Strings.String UnivSubst PCUICPretty.
