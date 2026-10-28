From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

(** BET-319 row M: [GlobalMaps] takes the [PrimOpTypeSig] instance [TemplatePrimOpType]. *)
Module qTemplatePrimOpType <: QuotationOfPrimOpType TemplateTerm Env TemplatePrimOpType.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplatePrimOpType").
End qTemplatePrimOpType.

Module qTemplateGlobalMaps <: QuotationOfGlobalMaps TemplateTerm Env TemplateTermUtils TemplateEnvTyping TemplateConversion TemplateLookup TemplateArityRelation TemplatePrimOpType TemplateGlobalMaps.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateGlobalMaps").
End qTemplateGlobalMaps.
