From MetaRocq.PCUIC Require Import PCUICAst PCUICArityRed.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICArityRelation <: QuotationOfKernelRed PCUICTerm PCUICEnvironment PCUICArityRelation.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICArityRelation").
End qPCUICArityRelation.
