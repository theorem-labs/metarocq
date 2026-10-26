From MetaRocq.Common Require Import BasicAst Environment EnvironmentTyping Universes.
From MetaRocq.Quotation.ToPCUIC Require Import Init.
From MetaRocq.Quotation.ToPCUIC Require Import (hints) Stdlib.Init Stdlib.Lists Stdlib.ssr.
From MetaRocq.Quotation.ToPCUIC.Utils Require Import (hints) All_Forall MROption MRProd.
From MetaRocq.Quotation.ToPCUIC.Common Require Import (hints) config BasicAst Kernames Universes Environment.
From MetaRocq.Quotation.ToPCUIC.QuotationOf.Common Require Import Environment.Sig EnvironmentTyping.Sig.
From Equations.Prop Require Import EqDecInstances.

Module QuoteLookup (Import T : Term) (Import E : EnvironmentSig T) (Import L : LookupSig T E) (Import EDec : EnvironmentDecide T E) (Import qE : QuotationOfEnvironment T E) (Import qL : QuotationOfLookup T E L) (Import qEDec : QuotationOfEnvironmentDecide T E EDec) (Import QuoteE : QuoteEnvironmentSig T E) <: QuoteLookupSig T E L.

  #[export] Hint Unfold
    consistent_instance_ext
  : quotation.
  #[export] Typeclasses Transparent
    consistent_instance_ext
  .

  Section with_refl.
    #[local] Hint Extern 2 => reflexivity : typeclass_instances.
    #[export] Polymorphic Instance quote_on_udecl_decl {F d} {quoteF1 : forall cb, d = ConstantDecl cb -> ground_quotable (F cb.(cst_universes))} {quoteF2 : forall mb, d = InductiveDecl mb -> ground_quotable (F mb.(ind_universes))} : ground_quotable (@on_udecl_decl _ F d) := ltac:(cbv [on_udecl_decl]; exact _).
  End with_refl.

  #[export] Instance quote_consistent_instance {cf lvs ϕ uctx u} : ground_quotable (@consistent_instance cf lvs ϕ uctx u) := ltac:(cbv [consistent_instance]; exact _).
  #[export] Instance quote_wf_universe {Σ u} : ground_quotable (@wf_universe Σ u)
    := ground_quotable_of_dec (@wf_universe_dec Σ u).
  #[export] Instance quote_wf_sort {Σ s} : ground_quotable (@wf_sort Σ s)
    := ground_quotable_of_dec (@wf_sort_dec Σ s).

  #[export] Instance quote_declared_constant {Σ id decl} : ground_quotable (@declared_constant Σ id decl) := ltac:(cbv [declared_constant]; exact _).
  #[export] Instance quote_declared_minductive {Σ mind decl} : ground_quotable (@declared_minductive Σ mind decl) := ltac:(cbv [declared_minductive]; exact _).
  #[export] Instance quote_declared_inductive {Σ ind mdecl decl} : ground_quotable (@declared_inductive Σ ind mdecl decl) := ltac:(cbv [declared_inductive]; exact _).
  #[export] Instance quote_declared_constructor {Σ cstr mdecl idecl cdecl} : ground_quotable (@declared_constructor Σ cstr mdecl idecl cdecl) := ltac:(cbv [declared_constructor]; exact _).
  #[export] Instance quote_declared_projection {Σ proj mdecl idecl cdecl pdecl} : ground_quotable (@declared_projection Σ proj mdecl idecl cdecl pdecl) := ltac:(cbv [declared_projection]; exact _).
End QuoteLookup.

Module QuoteEnvTyping (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import qT : QuotationOfTerm T) (Import qE : QuotationOfEnvironment T E) (Import qET : QuotationOfEnvTyping T E TU ET) (Import QuoteT : QuoteTerm T)  (Import QuoteE : QuoteEnvironmentSig T E) <: QuoteEnvTypingSig T E TU ET.

  #[export] Hint Unfold
    on_def_type
    on_def_body
    lift_typing0
  : quotation.
  #[export] Typeclasses Transparent
    on_def_type
    on_def_body
    lift_typing0
  .

  #[export] Instance quote_All_local_env {typing Γ} {qtyping : quotation_of typing} {quote_typing : forall Γ j, ground_quotable (typing Γ j)} : ground_quotable (@All_local_env typing Γ) := ltac:(induction 1; exact _).
  Import StrongerInstances.
  #[local] Hint Extern 2 (_ = _) => reflexivity : typeclass_instances.
  #[export] Instance quote_lift_sorting {checking sorting j} {qcheck : quotation_of checking} {qsorting : quotation_of sorting} {quote_check : forall tm, j_term j = Some tm -> ground_quotable (checking tm (j_typ j))} {quote_sorting : forall u, ground_quotable (sorting (j_typ j) u)} : ground_quotable (@lift_sorting checking sorting j) := ltac:(cbv [lift_sorting]; exact _).
  #[local] Typeclasses Transparent lift_sorting.
  #[export] Instance quote_All_local_env_over_sorting
   {checking sorting cproperty sproperty Γ H}
   {qchecking : quotation_of checking} {qsorting : quotation_of sorting} {qcproperty : quotation_of cproperty} {qsproperty : quotation_of sproperty}
   {quote_checking : forall Γ t T, ground_quotable (checking Γ t T)} {quote_sorting : forall Γ T u, ground_quotable (sorting Γ T u)} {quote_sproperty : forall Γ all t u tu, ground_quotable (sproperty Γ all t u tu)} {quote_cproperty : forall Γ all b t tb, ground_quotable (cproperty Γ all b t tb)}
    : ground_quotable (@All_local_env_over_sorting checking sorting cproperty sproperty Γ H) := ltac:(induction 1; cbv [lift_sorting j_term MROption.option_default] in *; exact _).
  #[export] Instance quote_All_local_env_over {typing property Γ H}
   {qtyping : quotation_of typing} {qproperty : quotation_of property}
   {quote_typing : forall Γ t T, ground_quotable (typing Γ t T)} {quote_property : forall Γ all b t tb, ground_quotable (property Γ all b t tb)}
    : ground_quotable (@All_local_env_over typing property Γ H)
    := ltac:(cbv [All_local_env_over]; exact _).

  #[export] Instance quote_ctx_inst {typing Γ ctx inst}
   {qtyping : quotation_of typing}
   {quote_typing : forall i t, ground_quotable (typing Γ i t)}
    : ground_quotable (@ctx_inst typing Γ ctx inst)
    := ltac:(induction 1; exact _).
End QuoteEnvTyping.

Module QuoteConversion (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import C : ConversionSig T E TU ET) (Import qT : QuotationOfTerm T) (Import qE : QuotationOfEnvironment T E) (Import qC : QuotationOfConversion T E TU ET C) (Import QuoteT : QuoteTerm T) (Import QuoteE : QuoteEnvironmentSig T E) <: QuoteConversionSig T E TU ET C.

  #[export] Instance quote_All_decls_alpha_pb {pb P b b'} {qP : quotation_of P} {quoteP : forall pb t t', ground_quotable (P pb t t')}
    : ground_quotable (@All_decls_alpha_pb pb P b b') := ltac:(induction 1; exact _).

  #[export] Instance quote_cumul_pb_decls {cumul_gen pb Σ Γ Γ' x y}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_decls cumul_gen pb Σ Γ Γ' x y)
    := ltac:(cbv [cumul_pb_decls]; exact _).

  #[export] Instance quote_cumul_pb_context {cumul_gen pb Σ Γ Γ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_pb_context cumul_gen pb Σ Γ Γ')
    := ltac:(cbv [cumul_pb_context]; exact _).

  #[export] Instance quote_cumul_ctx_rel {cumul_gen Σ Γ Δ Δ'}
   {qcumul_gen : quotation_of cumul_gen}
   {quote_cumul_gen : forall Γ pb t t', ground_quotable (cumul_gen Σ Γ pb t t')}
    : ground_quotable (@cumul_ctx_rel cumul_gen Σ Γ Δ Δ')
    := ltac:(cbv [cumul_ctx_rel]; exact _).
End QuoteConversion.

Module QuoteGlobalMaps (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E) (Import ET : EnvTypingSig T E TU) (Import C : ConversionSig T E TU ET) (Import L : LookupSig T E) (Import AR : ArityRedSig T E) (Import GM : GlobalMapsSig T E TU ET C L AR) (Import qT : QuotationOfTerm T) (Import qE : QuotationOfEnvironment T E) (Import qET : QuotationOfEnvTyping T E TU ET) (Import qC : QuotationOfConversion T E TU ET C) (Import qL : QuotationOfLookup T E L) (Import qAR : QuotationOfArityRed T E AR) (Import qGM :  QuotationOfGlobalMaps T E TU ET C L AR GM) (Import QuoteT : QuoteTerm T) (Import QuoteE : QuoteEnvironmentSig T E) (Import QuoteET : QuoteEnvTypingSig T E TU ET) (Import QuoteC : QuoteConversionSig T E TU ET C) (Import QuoteL : QuoteLookupSig T E L) (Import QuoteAR : QuoteArityRedSig T E AR) <: QuoteGlobalMapsSig T E TU ET C L AR GM.

  #[export] Hint Unfold
    mdecl_at_i
    constructor_univs
    on_constructors
    fresh_global
    nested_insts
  : quotation.
  #[export] Typeclasses Transparent
    mdecl_at_i
    constructor_univs
    on_constructors
    fresh_global
    nested_insts
  .

  Section GlobalMaps.
    Context {cf : config.checker_flags}
            {Pcmp: global_env_ext -> context -> conv_pb -> term -> term -> Type}
            {P : global_env_ext -> context -> judgment -> Type}
            {qPcmp : quotation_of Pcmp} {qP : quotation_of P}
            {quotePcmp : forall Σ Γ pb t T, ground_quotable (Pcmp Σ Γ pb t T)}
            {quoteP : forall Σ Γ j, ground_quotable (P Σ Γ j)}.

    #[export] Instance quote_on_context {Σ ctx} : ground_quotable (@on_context P Σ ctx)
      := ltac:(cbv [on_context]; exact _).

    #[export] Instance quote_type_local_ctx {Σ Γ Δ u} : ground_quotable (@type_local_ctx P Σ Γ Δ u)
      := ltac:(induction Δ; cbn [type_local_ctx]; exact _).

    #[export] Instance quote_sorts_local_ctx {Σ Γ Δ us} : ground_quotable (@sorts_local_ctx P Σ Γ Δ us)
      := ltac:(revert us; induction Δ, us; cbn [sorts_local_ctx]; exact _).

    #[export] Instance quote_on_type {Σ Γ T} : ground_quotable (@on_type P Σ Γ T)
      := ltac:(cbv [on_type]; exact _).
    #[export] Instance quote_on_type_rel {Σ Γ T r} : ground_quotable (@on_type_rel P Σ Γ T r)
      := ltac:(cbv [on_type_rel]; exact _).

    #[export] Instance quote_satisfiable_udecl {univs ϕ} : ground_quotable (@satisfiable_udecl univs ϕ)
      := ltac:(cbv [satisfiable_udecl]; exact _).
    #[export] Instance quote_valid_on_mono_udecl {univs ϕ} : ground_quotable (@valid_on_mono_udecl univs ϕ)
      := ltac:(cbv [valid_on_mono_udecl]; exact _).
    #[export] Instance quote_on_udecl {univs udecl} : ground_quotable (@on_udecl univs udecl)
      := ltac:(cbv [on_udecl]; exact _).

    Import StrongerInstances.
    #[local] Hint Extern 0 (quotation_of ?x) =>
      match goal with H : quotation_of x |- _ => exact H end : typeclass_instances.
    #[export] Instance quote_nested_inst : ground_quotable nested_inst
      := ltac:(destruct 1; exact _).
    #[export] Instance quote_nested_insts : ground_quotable nested_insts
      := ltac:(cbv [nested_insts]; exact _).
    #[export] Instance quote_nested_inst_ok {NI ctx x l} : ground_quotable (@nested_inst_ok NI ctx x l)
      := ltac:(cbv [nested_inst_ok];
        refine (@MetaRocq.Quotation.ToPCUIC.Stdlib.Init.quote_sigT _ _ _ _ _ (fun j qj => _));
        refine (@MetaRocq.Quotation.ToPCUIC.Stdlib.Init.quote_sigT _ _ _ _ _ (fun e qe => _));
        exact _).
    #[export] Instance quote_nested_uniform_cstr {mdecl k cdecl} : ground_quotable (@nested_uniform_cstr mdecl k cdecl)
      := ltac:(cbv [nested_uniform_cstr];
        refine (@MetaRocq.Quotation.ToPCUIC.Stdlib.Init.quote_sigT _ _ _ _ _ (fun rest qrest => _));
        refine (@MetaRocq.Quotation.ToPCUIC.Stdlib.Init.quote_sigT _ _ _ _ _ (fun rest1 qrest1 => _));
        exact _).
    #[export] Instance quote_nested_uniform {mdecl idecl k} : ground_quotable (@nested_uniform mdecl idecl k)
      := ltac:(cbv [nested_uniform]; exact _).
    #[export] Instance quote_nested_variance_ok {mdecl} : ground_quotable (@nested_variance_ok mdecl)
      := ltac:(cbv [nested_variance_ok]; exact _).

    (** The quotation of [positive_cstr_arg] names the whole mutual block; the other
        three relations are its later bodies. *)
    #[local] Instance quote_positive_args_inductive :
      inductive_quotation_of positive_args :=
      {| qinductive :=
           mkInd (inductive_mind qpositive_cstr_arg.(qinductive)) 1;
         qinst := qpositive_cstr_arg.(qinst) |}.
    #[local] Instance quote_positive_nested_ctors_inductive :
      inductive_quotation_of positive_nested_ctors :=
      {| qinductive :=
           mkInd (inductive_mind qpositive_cstr_arg.(qinductive)) 2;
         qinst := qpositive_cstr_arg.(qinst) |}.
    #[local] Instance quote_positive_nested_cstr_inductive :
      inductive_quotation_of positive_nested_cstr :=
      {| qinductive :=
           mkInd (inductive_mind qpositive_cstr_arg.(qinductive)) 3;
         qinst := qpositive_cstr_arg.(qinst) |}.

    (** One instance per relation of the mutual block, each by its own [*_mrect].
        [NI] grows under [pos_arg_nested], so every motive takes its quotation. *)
    Local Ltac quote_positive_mrect rect Σ mdecl :=
      apply (rect Σ mdecl
        (fun NI ctx t p => quotation_of NI -> quotation_of p)
        (fun NI ctx l p => quotation_of NI -> quotation_of p)
        (fun NI ctx ps nskip cs p => quotation_of NI -> quotation_of p)
        (fun NI ctx ps nskip c p => quotation_of NI -> quotation_of p));
      intros;
      repeat match goal with
      | H : quotation_of ?NI -> quotation_of _ |- _ =>
          specialize (H ltac:(exact _))
      end;
      exact _.
    #[export] Instance quote_positive_cstr_arg {Σ mdecl NI ctx t} :
      ground_quotable (@positive_cstr_arg Σ mdecl NI ctx t)
      := ltac:(
        intro p;
        pose proof (@quote_ground nested_insts quote_nested_insts NI) as qNI;
        revert NI ctx t p qNI;
        quote_positive_mrect positive_cstr_arg_mrect Σ mdecl).
    #[export] Instance quote_positive_args {Σ mdecl NI ctx l} :
      ground_quotable (@positive_args Σ mdecl NI ctx l)
      := ltac:(
        intro p;
        pose proof (@quote_ground nested_insts quote_nested_insts NI) as qNI;
        revert NI ctx l p qNI;
        quote_positive_mrect positive_args_mrect Σ mdecl).
    #[export] Instance quote_positive_nested_ctors {Σ mdecl NI ctx ps nskip cs} :
      ground_quotable (@positive_nested_ctors Σ mdecl NI ctx ps nskip cs)
      := ltac:(
        intro p;
        pose proof (@quote_ground nested_insts quote_nested_insts NI) as qNI;
        revert NI ctx ps nskip cs p qNI;
        quote_positive_mrect positive_nested_ctors_mrect Σ mdecl).
    #[export] Instance quote_positive_nested_cstr {Σ mdecl NI ctx ps nskip c} :
      ground_quotable (@positive_nested_cstr Σ mdecl NI ctx ps nskip c)
      := ltac:(
        intro p;
        pose proof (@quote_ground nested_insts quote_nested_insts NI) as qNI;
        revert NI ctx ps nskip c p qNI;
        quote_positive_mrect positive_nested_cstr_mrect Σ mdecl).

    #[export] Instance quote_positive_cstr {Σ mdecl i ctx t} : ground_quotable (@positive_cstr Σ mdecl i ctx t)
      := ltac:(induction 1; exact _).

    #[export] Instance quote_ind_respects_variance {Σ mdecl v indices} : ground_quotable (@ind_respects_variance Pcmp Σ mdecl v indices) := ltac:(cbv [ind_respects_variance]; exact _).
    #[export] Instance quote_cstr_respects_variance {Σ mdecl v cs} : ground_quotable (@cstr_respects_variance Pcmp Σ mdecl v cs) := ltac:(cbv [cstr_respects_variance]; exact _).
    #[export] Instance quote_on_constructor {Σ mdecl i idecl ind_indices cdecl cunivs} : ground_quotable (@on_constructor cf Pcmp P Σ mdecl i idecl ind_indices cdecl cunivs)
      := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_proj {mdecl mind i k p decl} : ground_quotable (@on_proj mdecl mind i k p decl) := ltac:(destruct 1; cbv [proj_type] in *; exact _).
    #[export] Instance quote_on_projection {mdecl mind i cdecl k p} : ground_quotable (@on_projection mdecl mind i cdecl k p) := ltac:(cbv [on_projection]; exact _).
    #[export] Instance quote_on_projections {mdecl mind i idecl ind_indices cdecl} : ground_quotable (@on_projections mdecl mind i idecl ind_indices cdecl) := ltac:(destruct 1; cbv [on_projection] in *; exact _).
    #[export] Instance quote_check_ind_sorts {Σ params kelim ind_indices cdecls ind_sort} : ground_quotable (@check_ind_sorts cf P Σ params kelim ind_indices cdecls ind_sort) := ltac:(cbv [check_ind_sorts check_constructors_smaller global_ext_constraints global_constraints] in *; exact _).
    #[export] Instance quote_on_ind_body {Σ mind mdecl i idecl} : ground_quotable (@on_ind_body cf Pcmp P Σ mind mdecl i idecl) := ltac:(destruct 1; cbv [it_mkProd_or_LetIn mkProd_or_LetIn ind_indices ind_sort] in *; exact _).
    #[export] Instance quote_on_variance {Σ univs variances} : ground_quotable (@on_variance cf Σ univs variances) := ltac:(cbv [on_variance consistent_instance_ext consistent_instance global_ext_constraints global_constraints]; exact _).
    #[export] Instance quote_on_inductive {Σ mind mdecl} : ground_quotable (@on_inductive cf Pcmp P Σ mind mdecl) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_constant_decl {Σ d} : ground_quotable (@on_constant_decl P Σ d) := ltac:(cbv [on_constant_decl]; exact _).
    #[export] Instance quote_on_global_decl {Σ kn d} : ground_quotable (@on_global_decl cf Pcmp P Σ kn d) := ltac:(cbv [on_global_decl]; exact _).
    #[export] Instance quote_on_global_decls_data {univs retro Σ kn d} : ground_quotable (@on_global_decls_data cf Pcmp P univs retro Σ kn d) := ltac:(destruct 1; exact _).
    #[export] Instance quote_on_global_decls {univs retro Σ} : ground_quotable (@on_global_decls cf Pcmp P univs retro Σ) := ltac:(induction 1; exact _).
    #[export] Instance quote_on_global_univs {univs} : ground_quotable (@on_global_univs univs) := ltac:(cbv [on_global_univs]; exact _).
    #[export] Instance quote_on_global_env {g} : ground_quotable (@on_global_env cf Pcmp P g) := ltac:(cbv [on_global_env]; exact _).
    #[export] Instance quote_on_global_env_ext {Σ} : ground_quotable (@on_global_env_ext cf Pcmp P Σ) := ltac:(cbv [on_global_env_ext]; exact _).
  End GlobalMaps.

  #[export] Existing Instances
    quote_on_context
    quote_type_local_ctx
    quote_sorts_local_ctx
    quote_on_type
    quote_on_type_rel
    quote_on_udecl
    quote_satisfiable_udecl
    quote_valid_on_mono_udecl
    quote_nested_inst
    quote_nested_insts
    quote_nested_inst_ok
    quote_nested_uniform_cstr
    quote_nested_uniform
    quote_nested_variance_ok
    quote_positive_cstr_arg
    quote_positive_args
    quote_positive_nested_ctors
    quote_positive_nested_cstr
    quote_positive_cstr
    quote_ind_respects_variance
    quote_cstr_respects_variance
    quote_on_constructor
    quote_on_proj
    quote_on_projection
    quote_on_projections
    quote_check_ind_sorts
    quote_on_ind_body
    quote_on_variance
    quote_on_inductive
    quote_on_constant_decl
    quote_on_global_decl
    quote_on_global_decls_data
    quote_on_global_decls
    quote_on_global_univs
    quote_on_global_env
    quote_on_global_env_ext
  .
End QuoteGlobalMaps.

Module QuoteDeclarationTyping (Import T : Term) (Import E : EnvironmentSig T) (Import TU : TermUtils T E)
       (Import ET : EnvTypingSig T E TU) (Import CT : ConversionSig T E TU ET)
       (Import CS : ConversionParSig T E TU ET) (Import Ty : Typing T E TU ET CT CS)
       (Import L : LookupSig T E) (Import AR : ArityRedSig T E) (Import GM : GlobalMapsSig T E TU ET CT L AR)
       (Import DT : DeclarationTypingSig T E TU ET CT CS Ty L AR GM)
       (Import qT : QuotationOfTerm T) (Import qE : QuotationOfEnvironment T E)
       (Import qET : QuotationOfEnvTyping T E TU ET) (Import qCT : QuotationOfConversion T E TU ET CT)
       (Import qTy : QuotationOfTyping T E TU ET CT CS Ty)
       (Import qGM : QuotationOfGlobalMaps T E TU ET CT L AR GM)
       (Import QuoteT : QuoteTerm T) (Import QuoteE : QuoteEnvironmentSig T E)
       (Import QuoteET : QuoteEnvTypingSig T E TU ET) (Import QuoteCT : QuoteConversionSig T E TU ET CT)
       (Import QuoteTy : QuoteTyping T E TU ET CT CS Ty)
       (Import QuoteL : QuoteLookupSig T E L) (Import QuoteGM : QuoteGlobalMapsSig T E TU ET CT L AR GM)
<: QuoteDeclarationTypingSig T E TU ET CT CS Ty L AR GM DT.

  #[export] Hint Unfold
    Forall_decls_typing
  : quotation.
  #[export] Typeclasses Transparent
    Forall_decls_typing
  .

  Import StrongerInstances.
  #[export] Instance quote_type_local_decl {cf Σ Γ d} : ground_quotable (@type_local_decl cf Σ Γ d) := ltac:(cbv [type_local_decl isType]; exact _).
  #[export] Instance quote_wf_local_rel {cf Σ Γ Γ'} : ground_quotable (@wf_local_rel cf Σ Γ Γ') := ltac:(cbv [wf_local_rel]; exact _).
End QuoteDeclarationTyping.
