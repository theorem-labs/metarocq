From MetaRocq.PCUIC Require Import PCUICAst PCUICArityRed.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.Lists.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Equations.Type.
From MetaRocq.Quotation.ToPCUIC.Utils Require Import (hints) All_Forall.
From MetaRocq.Quotation.ToPCUIC.Common Require Import (hints) BasicAst Universes Kernames Environment.
From MetaRocq.Quotation.ToPCUIC.PCUIC Require Import (hints) PCUICAst utils.PCUICPrimitive.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import EnvironmentTyping.Sig.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.PCUIC Require Import PCUICArityRed.Instances.

#[export] Instance quote_whd_rel {zeta Σ Γ t args h l} : ground_quotable (@whd_rel zeta Σ Γ t args h l).
Proof.
  cbv [ground_quotable].
  revert t args h l.
  fix quote_whd_rel 5.
  change (forall t args h l, ground_quotable (@whd_rel zeta Σ Γ t args h l)) in quote_whd_rel.
  destruct 1.
  all: [ > replace_quotation_of_goal () .. ].
Defined.

#[export] Instance quote_arity_red {Σ Γ t Δ s} : ground_quotable (@arity_red Σ Γ t Δ s).
Proof.
  cbv [ground_quotable].
  revert Γ t Δ s.
  fix quote_arity_red 5.
  change (forall Γ t Δ s, ground_quotable (@arity_red Σ Γ t Δ s)) in quote_arity_red.
  destruct 1.
  all: [ > replace_quotation_of_goal () .. ].
Defined.

Module QuotePCUICArityRelation <: QuoteKernelRedSig PCUICTerm PCUICEnvironment PCUICArityRelation.
  #[export] Instance quote_arity_red {Σ Γ t Δ s} : ground_quotable (@PCUICArityRelation.arity_red Σ Γ t Δ s)
    := ltac:(cbv [PCUICArityRelation.arity_red]; exact _).
  #[export] Instance quote_whd_rel {zeta Σ Γ t args h l} : ground_quotable (@PCUICArityRelation.whd_rel zeta Σ Γ t args h l)
    := ltac:(cbv [PCUICArityRelation.whd_rel]; exact _).
End QuotePCUICArityRelation.
Export (hints) QuotePCUICArityRelation.
