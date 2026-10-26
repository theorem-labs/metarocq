From MetaRocq.PCUIC Require Import PCUICAst PCUICArityRed PCUICTyping.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICGlobalMaps <: QuotationOfGlobalMaps PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICLookup PCUICArityRelation PCUICGlobalMaps.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICGlobalMaps").
End qPCUICGlobalMaps.
