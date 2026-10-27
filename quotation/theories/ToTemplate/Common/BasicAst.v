From MetaRocq.Quotation.ToTemplate Require Import Init.
From MetaRocq.Quotation.ToTemplate Require Import (hints) Stdlib.Init Stdlib.Floats Stdlib.Numbers Stdlib.Lists.
From MetaRocq.Quotation.ToTemplate.Utils Require Import (hints) utils All_Forall.
From MetaRocq.Quotation.ToTemplate.Common Require Import (hints) Kernames.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Utils Require Import MRUtils.
From MetaRocq.Template Require Import AstUtils (* for tFixType *).

#[export] Instance quote_name : ground_quotable name := ltac:(destruct 1; exact _).
#[export] Instance quote_relevance : ground_quotable relevance := ltac:(destruct 1; exact _).
#[export] Instance quote_binder_annot {A} {qA : quotation_of A} {quoteA : ground_quotable A} : ground_quotable (binder_annot A) := ltac:(destruct 1; exact _).
#[export] Instance quote_cast_kind : ground_quotable cast_kind := ltac:(destruct 1; exact _).
#[export] Instance quote_case_info : ground_quotable case_info := ltac:(destruct 1; exact _).
#[export] Instance quote_recursivity_kind : ground_quotable recursivity_kind := ltac:(destruct 1; exact _).
#[export] Instance quote_conv_pb : ground_quotable conv_pb := ltac:(destruct 1; exact _).
#[export] Hint Unfold aname : quotation.
#[export] Typeclasses Transparent aname.
#[export] Instance quote_def {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (def term) := ltac:(destruct 1; exact _).
#[export] Instance quote_judgment_ {term univ} {qterm : quotation_of term} {uterm : quotation_of univ} {quote_term : ground_quotable term} {quote_univ : ground_quotable univ} : ground_quotable (judgment_ term univ) := ltac:(destruct 1; exact _).
#[export] Instance quote_context_decl {term} {qterm : quotation_of term} {quote_term : ground_quotable term} : ground_quotable (context_decl term) := ltac:(destruct 1; exact _).
#[export] Hint Unfold mfixpoint : quotation.
#[export] Typeclasses Transparent mfixpoint.
#[local] Hint Unfold dtype dbody : quotation.
#[export] Instance quotation_of_mfixpoint {term} {m : mfixpoint term} {qterm : quotation_of term} {qm : tFixType quotation_of quotation_of m} : quotation_of m := ltac:(induction qm; destruct_head'_prod; destruct_head' def; exact _).
#[export] Hint Extern 0 (tFixType quotation_of quotation_of ?m) => assumption : typeclass_instances.
#[export] Instance quote_mfix_body_on {T check R mind d}
  {qT : quotation_of T} {quoteT : ground_quotable T}
  {qcheck : quotation_of check} {qR : quotation_of R}
  {quoteR : forall t u, ground_quotable (R t u)} :
  ground_quotable (@mfix_body_on T check R mind d)
  := ltac:(cbv [mfix_body_on]; exact _).
#[export] Instance quote_mfix_on_ind {T check R ok mfix}
  {qT : quotation_of T} {quoteT : ground_quotable T}
  {qcheck : quotation_of check} {qR : quotation_of R} {qok : quotation_of ok}
  {quoteR : forall t u, ground_quotable (R t u)} :
  ground_quotable (@mfix_on_ind T check R ok mfix)
  := ltac:(cbv [mfix_on_ind]; exact _).
#[export] Hint Unfold eq_binder_annot : quotation.
#[export] Typeclasses Transparent eq_binder_annot.
