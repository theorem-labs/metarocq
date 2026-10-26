From MetaRocq.Template Require Import Ast Typing.
From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qTemplateArityRelation <: QuotationOfArityRed TemplateTerm Env TemplateArityRelation.
  MetaRocq Run (tmMakeQuotationOfModule everything None "TemplateArityRelation").
End qTemplateArityRelation.
