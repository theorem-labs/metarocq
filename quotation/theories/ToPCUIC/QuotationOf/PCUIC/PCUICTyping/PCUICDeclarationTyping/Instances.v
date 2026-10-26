From MetaRocq.PCUIC Require Import PCUICAst PCUICArityRed PCUICTyping.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

Module qPCUICDeclarationTyping <: QuotationOfDeclarationTyping PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICConversionParSpec PCUICTypingDef PCUICLookup PCUICArityRelation PCUICGlobalMaps PCUICDeclarationTyping.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICDeclarationTyping").
End qPCUICDeclarationTyping.
