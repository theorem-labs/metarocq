From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaRocq.Template Require Import Ast Typing.

Module qTemplateArityRelation <: QuotationOfArityRed TemplateTerm Env TemplateArityRelation.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateArityRelation").
End qTemplateArityRelation.
