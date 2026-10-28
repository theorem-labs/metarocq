From MetaRocq.PCUIC Require Import PCUICAst PCUICArityRed PCUICTyping.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.

(** BET-319 row M: [GlobalMaps] takes the [PrimOpTypeSig] instance [PCUICPrimOpType]. *)
Module qPCUICPrimOpType <: QuotationOfPrimOpType PCUICTerm PCUICEnvironment PCUICPrimOpType.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICPrimOpType").
End qPCUICPrimOpType.

Module qPCUICGlobalMaps <: QuotationOfGlobalMaps PCUICTerm PCUICEnvironment PCUICTermUtils PCUICEnvTyping PCUICConversion PCUICLookup PCUICArityRelation PCUICPrimOpType PCUICGlobalMaps.
  MetaRocq Run (tmMakeQuotationOfModule everything None "PCUICGlobalMaps").
End qPCUICGlobalMaps.
