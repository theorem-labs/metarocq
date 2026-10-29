(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import OrdersTac Ascii ExtrOcamlBasic ExtrOCamlInt63 ExtrOCamlFloats ExtrOCamlPString.
From MetaRocq.Utils Require Import utils.
From MetaRocq.SafeChecker Require Import PCUICWfEnvImpl PCUICSafeChecker PCUICSafeConversion.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUICShared.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateChecker.
(* FORECAST tree only (EtaK7, 2026-10-29): the E checker behind the same command (see below). *)
From MetaRocq.SafeChecker Require PCUICWfEnvImplEta PCUICSafeReduceEta PCUICSafeConversionEta
  PCUICSafeConversionEtaFacts PCUICSafeReduceEtaBridge PCUICTypingEtaHyps PCUICCallByNeedSoundEta
  PCUICSafeCheckerEta PCUICEtaFactsCompose.
From MetaRocq.SafeCheckerPlugin Require SafeTemplateCheckerEta SafeTemplateCheckerEtaConv.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping.

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
(* FORECAST: the E conversion's [Ret] (uniform arity, stream lead's ruling). *)
Extraction Inline PCUICSafeConversionEta.Ret.

Extract Inductive Equations.Init.sigma => "( * )" ["(,)"].
Extract Constant Equations.Init.pr1 => "fst".
Extract Constant Equations.Init.pr2 => "snd".
Extraction Inline Equations.Init.pr1 Equations.Init.pr2.
Extraction Inline Equations.Prop.Logic.transport Equations.Prop.Logic.transport_r MREquality.transport.
Extraction Inline Equations.Prop.Logic.True_rect_dep Equations.Prop.Logic.False_rect_dep.

(** This Inline is because of a problem of weak type variables (partial application?) *)
Extraction Inline PCUICPrimitive.prim_val_reflect_eq.

(** The Template-to-PCUIC translation keeps the quoter's sharing: [memo_trans]
    is the identity in Rocq ([TemplateToPCUICShared.trans_shared_eq]) and the
    trusted memo on physical equality of [trans_memo.ml] at extraction.  These
    are the first safechecker extraction directives that replace a computation
    inside the checker; [Print Assumptions] cannot show them.  The shipped
    checker is correct only if [Trans_memo.memo Σ t k] returns [k ()] and
    [Trans_memo.release p] returns [p].  With one of [trans_memo.ml]'s test
    hooks armed, [Trans_memo.memo] raises the user error "trans_memo test"
    instead; it never returns another value, and the hooks are inert unless a
    [MetaRocq Test Memo …] command arms one for its own duration. *)
Extract Constant TemplateToPCUICShared.memo_trans => "Trans_memo.memo".
Extract Constant TemplateToPCUICShared.trans_memo_release => "Trans_memo.release".

Set Extraction Output Directory "src".
(** The extracted checker runs the real, executable guard check ([check_guard_gen]); on this FORECAST tree
    through its E-environment twin [PCUICWfEnvImplEta.real_guard_impl]. *)
(** FORECAST tree only (EtaK7, 2026-10-29; never lands on frac/eta as is; cutover F0 decides the real wiring).
    [MetaRocq SafeCheck] runs the E checker ([SafeTemplateCheckerEta]) under the SAME name the OCaml glue calls,
    so the glue and the integ harness are unchanged. The conversion is EtaConv's, through the oracle
    [SafeTemplateCheckerEtaConv.eta_conv_oracle]; the guard is [PCUICWfEnvImplEta.real_guard_impl]. Every other
    argument is a Prop (measured: EtaK7.md, PROP MEASUREMENT), so extraction erases it and the extracted
    signature is base's: the named hypotheses stay HYPOTHESES of this definition (they appear as its binders,
    which [Print Assumptions] and [About] show), no axiom is added. *)
(* Build-time evidence that every non-data argument below is a Prop, so extraction erases it. *)
Check (forall cf, @PCUICEtaFactsCompose.ReduceTypedFactsCoreE cf : Prop).
Check (forall cf, @PCUICEtaFactsCompose.WelltypedEContextE cf : Prop).
Check (forall cf, @PCUICTypingEtaHyps.EtaFacts cf : Prop).
Check (forall cf, @PCUICCallByNeedSoundEta.CbnConvSoundE cf : Prop).
Definition infer_and_print_template_program_with_guard {cf} {nor}
  (* EtaK7 dedup (lane lead, 2026-10-29): the six REDUCE facts that nothing else states and EtaPosK4's
     [welltypedE_context]; the conversion's [ReduceTypedFactsE], [ConvTypedFactsE] and
     [closed_context_conversionE] are built from these and [EtaF] inside [eta_conv_oracle]
     ([PCUICEtaFactsCompose]), so each fact is a binder of this definition once *)
  {reduce_coreE : @PCUICEtaFactsCompose.ReduceTypedFactsCoreE cf}
  {wt_contextE : @PCUICEtaFactsCompose.WelltypedEContextE cf}
  {EtaF : @PCUICTypingEtaHyps.EtaFacts cf}
  {cbnE : @PCUICCallByNeedSoundEta.CbnConvSoundE cf} :=
  SafeTemplateCheckerEta.infer_and_print_template_program (cf := cf) (nor := nor)
    (guard := PCUICWfEnvImplEta.real_guard_impl)
    (* the machine's full [ReduceTypedFacts welltypedE wf_extE], built from the small class, itself built
       ([#[export]] instances, given explicitly since their modules are only Required here) *)
    (reduce_factsE := @PCUICSafeReduceEtaBridge.reduce_typed_facts_E cf
                        (PCUICEtaFactsCompose.reduce_typed_facts_E_of_core (C := reduce_coreE) (EF := EtaF)
                           (WC := wt_contextE)))
    (CO := SafeTemplateCheckerEtaConv.eta_conv_oracle (cf := cf) (nor := nor) (EtaF := EtaF)
             (reduce_coreE := reduce_coreE) (wt_contextE := wt_contextE)).

(* FORECAST: no base checker root (f0-plan: the whole extracted set contains no base checker module); the
   E environment checker is a root instead *)
Separate Extraction Wf.Fix_sub MakeOrderTac
         PCUICSafeCheckerEta.typecheck_program SafeTemplateCheckerEta.trans_program_unshared
         infer_and_print_template_program_with_guard
         (* What the sharing test [MetaRocq Test Trans Sharing] calls *)
         (* FORECAST: the glue's [MetaRocq Test Trans Sharing] calls the E module's translations (same names and
            types as base [SafeTemplateChecker]'s), so no base [SafeTemplateChecker] is extracted *)
         SafeTemplateCheckerEta.trans_program TemplateToPCUICShared.trans_shared
         TemplateToPCUIC.trans TemplateToPCUIC.trans_global_env TemplateToPCUIC.empty_trans_env
         (* The following directives ensure separate extraction does not produce name clashes *)
         Stdlib.Strings.String UnivSubst PCUICPretty.
