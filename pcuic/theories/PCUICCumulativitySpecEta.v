(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Reflect PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICEquality
     PCUICLiftSubst PCUICUnivSubst PCUICCases PCUICOnFreeVars PCUICSigmaCalculus
     PCUICCumulativitySpec PCUICPrimitiveRed.

From Stdlib Require Import ssreflect ssrbool.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

(** * Specification of cumulativity with function η

  [cumulSpecE0] has the constructors of base [cumulSpec0] (renamed [cumulE_*]) plus
  [cumul_eta_l]. The new rule has no typing premise and ignores the domain of the
  λ: this relation is the specification; a checker compares domains as the kernel
  does. [cumul_eta_r] is derived through symmetry. *)

Reserved Notation " Σ ;;; Γ ⊢ t ≤sE[ pb ] u" (at level 50, Γ, t, u at next level,
  format "Σ  ;;;  Γ  ⊢  t  ≤sE[ pb ]  u").

Local Unset Elimination Schemes.
Inductive cumulSpecE0 {cf : checker_flags} (Σ : global_env_ext) Γ (pb : conv_pb) : term -> term -> Type :=

(* transitivity *)

| cumulE_Trans : forall t u v,
    is_closed_context Γ -> is_open_term Γ u ->
    Σ ;;; Γ ⊢ t ≤sE[pb] u ->
    Σ ;;; Γ ⊢ u ≤sE[pb] v ->
    Σ ;;; Γ ⊢ t ≤sE[pb] v

(* symmetry *)

| cumulE_Sym : forall t u,
    Σ ;;; Γ ⊢ t ≤sE[Conv] u ->
    Σ ;;; Γ ⊢ u ≤sE[pb] t

(* reflexivity *)

| cumulE_Refl : forall t,
    Σ ;;; Γ ⊢ t ≤sE[pb] t

(* Cumulativity rules *)

| cumulE_Ind : forall i u u' args args',
    cumul_Ind_univ Σ pb i #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tInd i u) args ≤sE[pb] mkApps (tInd i u') args'

| cumulE_Construct : forall i k u u' args args',
    cumul_Construct_univ Σ pb i k #|args| u u' ->
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) args args' ->
    Σ ;;; Γ ⊢ mkApps (tConstruct i k u) args ≤sE[pb] mkApps (tConstruct i k u') args'

| cumulE_Sort : forall s s',
    compare_sort Σ pb s s' ->
    Σ ;;; Γ ⊢ tSort s ≤sE[pb] tSort s'

| cumulE_Const : forall c u u',
    cmp_universe_instance (compare_universe Σ Conv) u u' ->
    Σ ;;; Γ ⊢ tConst c u ≤sE[pb] tConst c u'

(* congruence rules *)

| cumulE_Evar : forall e args args',
    All2 (fun t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) args args' ->
    Σ ;;; Γ ⊢ tEvar e args ≤sE[pb] tEvar e args'

| cumulE_App : forall t t' u u',
    Σ ;;; Γ ⊢ t ≤sE[pb] t' ->
    Σ ;;; Γ ⊢ u ≤sE[Conv] u' ->
    Σ ;;; Γ ⊢ tApp t u ≤sE[pb] tApp t' u'

| cumulE_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ ty ≤sE[Conv] ty' ->
    Σ ;;; Γ ,, vass na ty ⊢ t ≤sE[Conv] t' ->
    Σ ;;; Γ ⊢ tLambda na ty t ≤sE[pb] tLambda na' ty' t'

| cumulE_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ a ≤sE[Conv] a' ->
    Σ ;;; Γ ,, vass na a ⊢ b ≤sE[pb] b' ->
    Σ ;;; Γ ⊢ tProd na a b ≤sE[pb] tProd na' a' b'

| cumulE_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ;;; Γ ⊢ t ≤sE[Conv] t' ->
    Σ ;;; Γ ⊢ ty ≤sE[Conv] ty' ->
    Σ ;;; Γ ,, vdef na t ty ⊢ u ≤sE[Conv] u' ->
    Σ ;;; Γ ⊢ tLetIn na t ty u ≤sE[pb] tLetIn na' t' ty' u'

| cumulE_Case indn : forall p p' c c' brs brs',
    cumul_predicate (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) (compare_universe Σ Conv) Γ p p' ->
    Σ ;;; Γ ⊢ c ≤sE[Conv] c' ->
    cumul_branches (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) Γ p brs brs' ->
    Σ ;;; Γ ⊢ tCase indn p c brs ≤sE[pb] tCase indn p' c' brs'

| cumulE_Proj : forall p c c',
    Σ ;;; Γ ⊢ c ≤sE[Conv] c' ->
    Σ ;;; Γ ⊢ tProj p c ≤sE[pb] tProj p c'

| cumulE_Fix : forall mfix mfix' idx,
    cumul_mfixpoint (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tFix mfix idx ≤sE[pb] tFix mfix' idx

| cumulE_CoFix : forall mfix mfix' idx,
    cumul_mfixpoint (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) Γ mfix mfix' ->
    Σ ;;; Γ ⊢ tCoFix mfix idx ≤sE[pb] tCoFix mfix' idx

| cumulE_Prim p p' :
  onPrims (fun x y => Σ ;;; Γ ⊢ x ≤sE[Conv] y) (compare_universe Σ Conv) p p' ->
  Σ ;;; Γ ⊢ tPrim p ≤sE[pb] tPrim p'

(** Reductions *)

(** Beta red *)
| cumulE_beta : forall na t b a,
    Σ ;;; Γ ⊢ tApp (tLambda na t b) a ≤sE[pb] b {0 := a}

(** Let *)
| cumulE_zeta : forall na b t b',
    Σ ;;; Γ ⊢ tLetIn na b t b' ≤sE[pb] b' {0 := b}

| cumulE_rel i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    Σ ;;; Γ ⊢ tRel i ≤sE[pb] lift0 (S i) body

(** iota red *)
| cumulE_iota : forall ci c u args p brs br,
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    Σ ;;; Γ ⊢ tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs  ≤sE[pb] iota_red ci.(ci_npar) p args br

(** Fix unfolding, with guard *)
| cumulE_fix : forall mfix idx args narg fn,
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    Σ ;;; Γ ⊢ mkApps (tFix mfix idx) args ≤sE[pb] mkApps fn args

(** CoFix-case unfolding, only under a case whose return type does not depend on the
    scrutinee ([ci_cofix_nondep]).

    The premise [ip.(ci_cofix_nondep)] mirrors the base rule
    [PCUICCumulativitySpec.cumul_cofix_case] as BET-339 defines it: a cofixpoint
    scrutinee unfolds only under a match whose return clause cannot depend on it,
    because unfolding under a dependent one breaks subject reduction.

    FORECAST-TREE-ONLY CHANGE (commit 1e5bec98).  This file's own base, [frac/eta] at
    56b92b56, predates the [ci_cofix_nondep] field of [case_info], so the premise exists
    only on a tree that carries BET-339.  The real landing of this change belongs to the
    cutover F0, not here: it is reconciled when F0 lands this premise on [frac/eta] over
    BET-339's base rule, with [cumulSpec0_incl_E] (base ⊆ E) rechecked there.

    Without the premise the E relation would be strictly WIDER than base conversion in
    exactly the direction BET-339 closed: [cumulSpec0_incl_E] would still compile while
    [cumulSpecE0] admitted the step base no longer admits. *)
| cumulE_cofix_case : forall ip p mfix idx args narg fn brs,
    ip.(ci_cofix_nondep) ->
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tCase ip p (mkApps (tCoFix mfix idx) args) brs ≤sE[pb] tCase ip p (mkApps fn args) brs

(** CoFix-proj unfolding *)
| cumulE_cofix_proj : forall p mfix idx args narg fn,
    unfold_cofix mfix idx = Some (narg, fn) ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tCoFix mfix idx) args) ≤sE[pb] tProj p (mkApps fn args)

(** Constant unfolding *)
| cumulE_delta : forall c decl body (isdecl : declared_constant Σ c decl) u,
    decl.(cst_body) = Some body ->
    Σ ;;; Γ ⊢ tConst c u ≤sE[pb] body@[u]

(** Primitive operation: the same rule as [cumul_prim_op]. *)
| cumulE_prim_op : forall c decl u op ls r v,
    prim_op_of Σ c = Some op ->
    declared_constant Σ c decl ->
    cst_body decl = None ->
    prim_op_denote op ls = Some r ->
    readback Σ (po_shape (info op)) r = Some v ->
    Σ ;;; Γ ⊢ mkApps (tConst c u) (map term_of_lit ls) ≤sE[pb] v

(** Proj *)
| cumulE_proj : forall p args u arg,
    nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
    Σ ;;; Γ ⊢ tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args) ≤sE[pb] arg

(** Function eta (plan I1): no typing premise, the domain [A] is not compared. *)
| cumul_eta_l : forall na A t u,
    Σ ;;; Γ ,, vass na A ⊢ t ≤sE[Conv] tApp (lift0 1 u) (tRel 0) ->
    Σ ;;; Γ ⊢ tLambda na A t ≤sE[pb] u

where " Σ ;;; Γ ⊢ t ≤sE[ pb ] u " := (@cumulSpecE0 _ Σ Γ pb t u) : type_scope.

Definition convSpecE `{checker_flags} (Σ : global_env_ext) Γ := cumulSpecE0 Σ Γ Conv.
Definition cumulSpecE `{checker_flags} (Σ : global_env_ext) Γ := cumulSpecE0 Σ Γ Cumul.

#[global]
Instance cumul_specE_refl {cf:checker_flags} Σ Γ pb : Reflexive (cumulSpecE0 Σ Γ pb).
Proof. intro; apply cumulE_Refl. Qed.

(** The reflexivity instances base states for the specification relation
    ([PCUICCumulativitySpec]) at the term, declaration and context level, over
    [cumulSpecE0]. Base's names are kept for the algorithmic relation and for
    [JoinE], so each name here carries [specE] where base's relation word sits:
    [cumul_specE_refl] above is base's [cumul_spec_refl], and the seven below are
    base's [conv_refl'], [cumul_pb_decls_refl], [conv_decls_refl],
    [cumul_decls_refl], [cumul_pb_ctx_refl], [conv_ctx_refl] and [cumul_ctx_refl].
    Each is registered as base registers it, so that [reflexivity] and typeclass
    resolution close a goal of the E relation where they close base's. *)

#[global]
Instance conv_specE_refl' {cf:checker_flags} Σ Γ : Reflexive (convSpecE Σ Γ) := _.

#[global]
Instance cumul_pb_decls_specE_refl {cf:checker_flags} pb Σ Γ Γ' :
  Reflexive (cumul_pb_decls cumulSpecE0 pb Σ Γ Γ').
Proof.
  intros x. destruct x as [na [b|] ty]; constructor; auto.
  all:constructor; reflexivity.
Qed.

#[global]
Instance conv_decls_specE_refl {cf:checker_flags} Σ Γ Γ' :
  Reflexive (conv_decls cumulSpecE0 Σ Γ Γ') := _.
#[global]
Instance cumul_decls_specE_refl {cf:checker_flags} Σ Γ Γ' :
  Reflexive (cumul_decls cumulSpecE0 Σ Γ Γ') := _.

Section ContextConversionE.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).

  Global Instance cumul_pb_ctx_specE_refl pb : Reflexive (cumul_pb_context cumulSpecE0 pb Σ).
  Proof using Type.
    intro Γ; induction Γ; try econstructor; auto.
    all:reflexivity.
  Qed.

  Global Instance conv_ctx_specE_refl : Reflexive (conv_context cumulSpecE0 Σ) := _.
  Global Instance cumul_ctx_specE_refl : Reflexive (cumul_context cumulSpecE0 Σ) := _.

End ContextConversionE.

(** * Eliminator (S2): a copy of [cumulSpec0_rect] with one more hypothesis, for [cumul_eta_l]. *)

Lemma cumulSpecE0_rect :
  forall cf (Σ : global_env_ext)
         (P : forall cf Σ Γ pb u v, @cumulSpecE0 cf Σ Γ pb u v -> Type),

    (* beta *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (t b a : term),
        P cf Σ Γ pb (tApp (tLambda na t b) a) (b {0 := a}) (cumulE_beta _ _ _ _ _ _ _)) ->

    (* let *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (b t b' : term),
        P cf Σ Γ pb (tLetIn na b t b') (b' {0 := b}) (cumulE_zeta _ _ _ _ _ _ _)) ->

    (forall (Γ : context) (pb : conv_pb) (i : nat) (body : term)
            (pf : option_map decl_body (nth_error Γ i) = Some (Some body)),
        P cf Σ Γ pb (tRel i) ((lift0 (S i)) body) (cumulE_rel _ _ _ _ _ pf)) ->

    (* iota *)
    (forall (Γ : context) (pb : conv_pb) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
            (p : predicate term) (brs : list (branch term)) br
            (Hbrs : nth_error brs c = Some br)
            (Hnargs : #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat),
        P cf Σ Γ pb (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
          (iota_red ci.(ci_npar) p args br)
          (cumulE_iota _ _ _ _ _ _ _ _ _ _ Hbrs Hnargs)) ->

    (* fix unfolding *)
    (forall (Γ : context) (pb : conv_pb) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term)
            (Hufix : unfold_fix mfix idx = Some (narg, fn))
            (Hisctor : is_constructor narg args = true),
        P cf Σ Γ pb (mkApps (tFix mfix idx) args) (mkApps fn args)
          (cumulE_fix _ _ _ _ _ _ _ _ Hufix Hisctor)) ->

    (* cofix unfolding *)
    (forall (Γ : context) (pb : conv_pb) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
            (args : list term) (narg : nat) (fn : term) (brs : list (branch term))
            (Hnondep : ci.(ci_cofix_nondep))
            (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
        P cf Σ Γ pb (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)
          (cumulE_cofix_case _ _ _ _ _ _ _ _ _ _ _ Hnondep Hucofix)) ->

    (forall (Γ : context) (pb : conv_pb) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
            (narg : nat) (fn : term)
            (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
        P cf Σ Γ pb (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))
          (cumulE_cofix_proj _ _ _ _ _ _ _ _ _ Hucofix)) ->

    (* constant unfolding *)
    (forall (Γ : context) (pb : conv_pb) c (decl : constant_body) (body : term)
            (Hdecl_decl : declared_constant Σ c decl)
            (u : Instance.t)
            (Hdecl_body : cst_body decl = Some body),
        P cf Σ Γ pb (tConst c u) (subst_instance u body)
          (cumulE_delta _ _ _ _ _ _ Hdecl_decl _ Hdecl_body)) ->

    (* primitive operation *)
    (forall (Γ : context) (pb : conv_pb) c (decl : constant_body) (u : Instance.t)
            (op : prim_op) (ls : list prim_lit) (r : prim_result) (v : term)
            (Hop : prim_op_of Σ c = Some op)
            (Hdecl_decl : declared_constant Σ c decl)
            (Hdecl_body : cst_body decl = None)
            (Hdenote : prim_op_denote op ls = Some r)
            (Hreadback : readback Σ (po_shape (info op)) r = Some v),
        P cf Σ Γ pb (mkApps (tConst c u) (map term_of_lit ls)) v
          (cumulE_prim_op _ _ _ _ _ _ _ _ _ _ Hop Hdecl_decl Hdecl_body Hdenote Hreadback)) ->

    (* Proj *)
    (forall (Γ : context) (pb : conv_pb)p (args : list term) (u : Instance.t)
            (arg : term)
            (Hargs : nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg),
        P cf Σ Γ pb (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg
          (cumulE_proj _ _ _ _ _ _ _ Hargs)) ->

    (* transitivity *)
    (forall (Γ : context) (pb : conv_pb) (t u v : term)
            (Hclosed_ctx : is_closed_context Γ) (Hopen_term : is_open_term Γ u)
            (Htu : cumulSpecE0 Σ Γ pb t u) (_ : P cf Σ Γ pb t u Htu)
            (Huv : cumulSpecE0 Σ Γ pb u v) (_ : P cf Σ Γ pb u v Huv),
        P cf Σ Γ pb t v
          (cumulE_Trans _ _ _ _ _ _ Hclosed_ctx Hopen_term Htu Huv)) ->

    (* symmetry *)
    (forall (Γ : context) (pb : conv_pb) (t u : term)
            (Hut : cumulSpecE0 Σ Γ Conv u t) (_ : P cf Σ Γ Conv u t Hut),
        P cf Σ Γ pb t u
          (cumulE_Sym _ _ _ _ _ Hut)) ->

    (* reflexivity *)
    (forall (Γ : context) (pb : conv_pb) (t : term),
        P cf Σ Γ pb t t
          (cumulE_Refl _ _ _ _)) ->

    (* congruence rules *)

    (forall (Γ : context) (pb : conv_pb) (ev : nat) (l l' : list term)
            (H : All2 (cumulSpecE0 Σ Γ Conv) l l') (_ : All2_dep (P cf Σ Γ Conv) H),
        P cf Σ Γ pb (tEvar ev l) (tEvar ev l')
          (cumulE_Evar _ _ _ _ _ _ H)) ->

    (forall (Γ : context) (pb : conv_pb) (t t' u u' : term)
            (Htt' : cumulSpecE0 Σ Γ pb t t') (_ : P cf Σ Γ pb t t' Htt')
            (Huu' : cumulSpecE0 Σ Γ Conv u u') (_ : P cf Σ Γ Conv u u' Huu'),
        P cf Σ Γ pb (tApp t u) (tApp t' u')
          (cumulE_App _ _ _ _ _ _ _ Htt' Huu')) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : aname) (ty ty' t t' : term)
            (Hna : eq_binder_annot na na')
            (Hty : cumulSpecE0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
            (Ht : cumulSpecE0 Σ (Γ ,, vass na ty) Conv t t') ( _ : P cf Σ (Γ ,, vass na ty) Conv t t' Ht),
        P cf Σ Γ pb (tLambda na ty t) (tLambda na' ty' t')
          (cumulE_Lambda _ _ _ _ _ _ _ _ _ Hna Hty Ht)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : binder_annot name) (a a' b b' : term)
            (Hna : eq_binder_annot na na')
            (Ha : cumulSpecE0 Σ Γ Conv a a') (_ : P cf Σ Γ Conv a a' Ha)
            (Hb : cumulSpecE0 Σ (Γ,, vass na a) pb b b') (_ : P cf Σ (Γ,, vass na a) pb b b' Hb),
        P cf Σ Γ pb (tProd na a b) (tProd na' a' b')
          (cumulE_Prod _ _ _ _ _ _ _ _ _ Hna Ha Hb)) ->

    (forall (Γ : context) (pb : conv_pb) (na na' : binder_annot name) (t t' ty ty' u u' : term)
            (Hna : eq_binder_annot na na')
            (Ht : cumulSpecE0 Σ Γ Conv t t') (_ : P cf Σ Γ Conv t t' Ht)
            (Hty : cumulSpecE0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
            (Hu : cumulSpecE0 Σ (Γ,, vdef na t ty) Conv u u') (_ : P cf Σ (Γ,, vdef na t ty) Conv u u' Hu),
        P cf Σ Γ pb (tLetIn na t ty u) (tLetIn na' t' ty' u')
          (cumulE_LetIn _ _ _ _ _ _ _ _ _ _ _ Hna Ht Hty Hu)) ->

    (forall (Γ : context) (pb : conv_pb) (indn : case_info) (p p' : predicate term)
            (c c' : term) (brs brs' : list (branch term))
            (Hp : cumul_predicate (fun Γ => cumulSpecE0 Σ Γ Conv) (compare_universe Σ Conv) Γ p p')
            (_ : cumul_predicate_dep Hp (fun Γ => P cf Σ Γ Conv) (fun l l' _ => on_rel (fun _ _ => True) Universe.make' l l'))
            (Hc : cumulSpecE0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc)
            (Hbody : cumul_branches (fun Γ => cumulSpecE0 Σ Γ Conv) Γ p brs brs')
            (_ : All2_dep
                   (fun br br' Hc => P cf Σ (Γ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br') (snd Hc)) Hbody),
        P cf Σ Γ pb (tCase indn p c brs) (tCase indn p' c' brs')
          (cumulE_Case _ _ _ _ _ _ _ _ _ _ Hp Hc Hbody)) ->

    (forall (Γ : context) (pb : conv_pb)
            (p : projection) (c c' : term)
            (Hc : cumulSpecE0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc),
        P cf Σ Γ pb (tProj p c) (tProj p c')
          (cumulE_Proj _ _ _ _ _ _ Hc)) ->

    (forall (Γ : context) (pb : conv_pb)
            (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
            (H : All2
                   (fun x y : def term =>
                      (cumulSpecE0 Σ Γ Conv (dtype x) (dtype y))
                      * ((cumulSpecE0 Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y))
                           × (rarg x = rarg y)
                           × eq_binder_annot (dname x) (dname y)))
                   mfix mfix')
            (_ : All2_dep
                   (fun x y H
                    => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                   H),
        P cf Σ Γ pb (tFix mfix idx) (tFix mfix' idx)
          (cumulE_Fix _ _ _ _ _ _ H)) ->

    (forall (Γ : context) (pb : conv_pb)
            (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
            (H : All2
                   (fun x y : def term =>
                      (cumulSpecE0 Σ Γ Conv (dtype x) (dtype y))
                        × ((cumulSpecE0 Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y))
                             × (rarg x = rarg y)
                             × (eq_binder_annot (dname x) (dname y))))
                   mfix mfix')
            (_ : All2_dep
                   (fun x y H
                    => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                   H),
        P cf Σ Γ pb (tCoFix mfix idx) (tCoFix mfix' idx)
          (cumulE_CoFix _ _ _ _ _ _ H)) ->

    (forall Γ pb p p' (e : onPrims (cumulSpecE0 Σ Γ Conv) (eq_universe Σ) p p'),
      onPrims_dep (cumulSpecE0 Σ Γ Conv) (eq_universe Σ) (P cf Σ Γ Conv) (fun _ _ _ => True) p p' e ->
      P cf Σ Γ pb (tPrim p) (tPrim p') (cumulE_Prim _ _ _ _ _ e)) ->

    (* cumulativity rules *)

    (forall (Γ : context) (pb : conv_pb) (i : inductive) (u u' : list Level.t)
            (args args' : list term)
            (Hu : cumul_Ind_univ Σ pb i #|args| u u')
            (Hargs : All2 (cumulSpecE0 Σ Γ Conv) args args')
            (_ : All2_dep (P cf Σ Γ Conv) Hargs),
        P cf Σ Γ pb (mkApps (tInd i u) args) (mkApps (tInd i u') args')
          (cumulE_Ind _ _ _ _ _ _ _ _ Hu Hargs)) ->

    (forall (Γ : context) (pb : conv_pb) (i : inductive) (k : nat)
            (u u' : list Level.t) (args args' : list term)
            (Hu : cumul_Construct_univ Σ pb i k #|args| u u')
            (Hargs : All2 (cumulSpecE0 Σ Γ Conv) args args')
            (_ : All2_dep (P cf Σ Γ Conv) Hargs),
        P cf Σ Γ pb (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')
          (cumulE_Construct _ _ _ _ _ _ _ _ _ Hu Hargs)) ->

    (forall (Γ : context) (pb : conv_pb) (s s' : sort)
            (Hs : compare_sort Σ pb s s'),
        P cf Σ Γ pb (tSort s) (tSort s')
          (cumulE_Sort _ _ _ _ _ Hs)) ->

    (forall (Γ : context) (pb : conv_pb) (c : kername) (u u' : list Level.t)
            (Hu : cmp_universe_instance (compare_universe Σ Conv) u u'),
        P cf Σ Γ pb (tConst c u) (tConst c u')
          (cumulE_Const _ _ _ _ _ _ Hu)) ->

    (* function eta *)
    (forall (Γ : context) (pb : conv_pb) (na : aname) (A t u : term)
            (Ht : cumulSpecE0 Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)))
            (_ : P cf Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)) Ht),
        P cf Σ Γ pb (tLambda na A t) u
          (cumul_eta_l _ _ _ _ _ _ _ Ht)) ->

    forall (Γ : context) (pb : conv_pb) (t t0 : term) (Ht : @cumulSpecE0 cf Σ Γ pb t t0), P cf Σ Γ pb t t0 Ht.
Proof.
  intros. rename Ht into Xlast.
  revert Γ pb t t0 Xlast.
  fix aux 5. intros Γ pb t u Xlast.
  move aux at top.
  destruct Xlast.
  - eapply X9; eauto.
  - eapply X10; eauto.
  - eapply X11; eauto.
  - eapply X22; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct a; constructor; auto.
  - eapply X23; eauto. clear -a aux.
    revert args args' a.
    fix aux' 3; destruct a; constructor; auto.
  - eapply X24; eauto.
  - eapply X25; eauto.
  - eapply X12; eauto.
    revert args args' a.
    fix aux' 3; destruct a; constructor; auto.
  - eapply X13; eauto.
  - eapply X14; eauto.
  - eapply X15; eauto.
  - eapply X16; eauto.
  - eapply X17 ; eauto.
    + unfold cumul_predicate in *. destruct c0 as [c0 [cuniv [ccontext creturn]]].
      repeat split ; eauto.
      * revert c0. generalize (pparams p), (pparams p').
        fix aux' 3; destruct c0; constructor; auto.
      * apply Forall2_dep_from_nth_error; intros; exact I.
    + revert brs brs' c1.
      fix aux' 3; destruct c1; constructor; intuition auto.
  - eapply X18 ; eauto.
  - eapply X19 ; eauto.
    revert c. unfold cumul_mfixpoint.
    set (mfixAbs_context := fix_context mfix).
    clearbody mfixAbs_context.
    revert mfix mfix'.
    fix aux' 3; destruct c; constructor.
    + intuition auto.
    + auto.
  - eapply X20 ; eauto.
    revert c. unfold cumul_mfixpoint.
    set (mfixAbs_context := fix_context mfix).
    clearbody mfixAbs_context.
    revert mfix mfix'.
    fix aux' 3; destruct c; constructor.
    + intuition auto.
    + auto.
  - eapply X21; eauto.
    clear -o aux.
    induction o; constructor; auto.
    clear -a0 aux. revert a0.
    induction a0; constructor; auto.
  - eapply X; eauto.
  - eapply X0; eauto.
  - eapply X1; eauto.
  - eapply X2; eauto.
  - eapply X3; eauto.
  - eapply X4; eauto.
  - eapply X5; eauto.
  - eapply X6; eauto.
  - eapply X7; eauto.
  - eapply X8; eauto.
  - eapply X26; eauto.
Defined.

Notation cumulSpecE0_ind_all := cumulSpecE0_rect (only parsing).

Definition cumulSpecE0_rec
  : forall cf (Σ : global_env_ext)
           (P : forall cf Σ Γ pb u v, @cumulSpecE0 cf Σ Γ pb u v -> Set),
    _
  := cumulSpecE0_rect.

Definition cumulSpecE0_ind
  : forall cf (Σ : global_env_ext)
           (P : forall cf Σ Γ pb u v, @cumulSpecE0 cf Σ Γ pb u v -> Prop),
    _
  := cumulSpecE0_rec.

Lemma convSpecE0_ind_all :
  forall cf (Σ : global_env_ext)
         (P : forall cf Σ Γ pb u v, @cumulSpecE0 cf Σ Γ pb u v -> Type),

        (* beta *)
       (forall (Γ : context) (na : aname) (t b a : term),
        P cf Σ Γ Conv (tApp (tLambda na t b) a) (b {0 := a}) (cumulE_beta _ _ _ _ _ _ _)) ->

        (* let *)
       (forall (Γ : context) (na : aname) (b t b' : term), P cf Σ Γ Conv (tLetIn na b t b') (b' {0 := b}) (cumulE_zeta _ _ _ _ _ _ _)) ->

       (forall (Γ : context) (i : nat) (body : term)
               (pf : option_map decl_body (nth_error Γ i) = Some (Some body)),
           P cf Σ Γ Conv (tRel i) ((lift0 (S i)) body) (cumulE_rel _ _ _ _ _ pf)) ->

        (* iota *)
       (forall (Γ : context) (ci : case_info) (c : nat) (u : Instance.t) (args : list term)
          (p : predicate term) (brs : list (branch term)) br
          (Hbrs : nth_error brs c = Some br)
          (Hnargs : #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat),
           P cf Σ Γ Conv (tCase ci p (mkApps (tConstruct ci.(ci_ind) c u) args) brs)
             (iota_red ci.(ci_npar) p args br)
             (cumulE_iota _ _ _ _ _ _ _ _ _ _ Hbrs Hnargs)) ->

        (* fix unfolding *)
       (forall (Γ : context) (mfix : mfixpoint term) (idx : nat) (args : list term) (narg : nat) (fn : term)
               (Hufix : unfold_fix mfix idx = Some (narg, fn))
               (Hisctor : is_constructor narg args = true),
           P cf Σ Γ Conv (mkApps (tFix mfix idx) args) (mkApps fn args)
             (cumulE_fix _ _ _ _ _ _ _ _ Hufix Hisctor)) ->

      (* cofix unfolding *)
       (forall (Γ : context) ci (p : predicate term) (mfix : mfixpoint term) (idx : nat)
               (args : list term) (narg : nat) (fn : term) (brs : list (branch term))
               (Hnondep : ci.(ci_cofix_nondep))
               (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
           P cf Σ Γ Conv (tCase ci p (mkApps (tCoFix mfix idx) args) brs) (tCase ci p (mkApps fn args) brs)
             (cumulE_cofix_case _ _ _ _ _ _ _ _ _ _ _ Hnondep Hucofix)) ->

       (forall (Γ : context) (p : projection) (mfix : mfixpoint term) (idx : nat) (args : list term)
               (narg : nat) (fn : term)
               (Hucofix : unfold_cofix mfix idx = Some (narg, fn)),
           P cf Σ Γ Conv (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))
             (cumulE_cofix_proj _ _ _ _ _ _ _ _ _ Hucofix)) ->

        (* constant unfolding *)
       (forall (Γ : context) c (decl : constant_body) (body : term)
               (Hdecl_decl : declared_constant Σ c decl)
               (u : Instance.t)
               (Hdecl_body : cst_body decl = Some body),
           P cf Σ Γ Conv (tConst c u) (subst_instance u body)
             (cumulE_delta _ _ _ _ _ _ Hdecl_decl _ Hdecl_body)) ->

        (* primitive operation *)
       (forall (Γ : context) c (decl : constant_body) (u : Instance.t)
               (op : prim_op) (ls : list prim_lit) (r : prim_result) (v : term)
               (Hop : prim_op_of Σ c = Some op)
               (Hdecl_decl : declared_constant Σ c decl)
               (Hdecl_body : cst_body decl = None)
               (Hdenote : prim_op_denote op ls = Some r)
               (Hreadback : readback Σ (po_shape (info op)) r = Some v),
           P cf Σ Γ Conv (mkApps (tConst c u) (map term_of_lit ls)) v
             (cumulE_prim_op _ _ _ _ _ _ _ _ _ _ Hop Hdecl_decl Hdecl_body Hdenote Hreadback)) ->

        (* Proj *)
       (forall (Γ : context)p (args : list term) (u : Instance.t)
               (arg : term)
               (Hargs : nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg),
           P cf Σ Γ Conv (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg
             (cumulE_proj _ _ _ _ _ _ _ Hargs)) ->

        (* transitivity *)
       (forall (Γ : context) (t u v : term)
               (Hclosed_ctx : is_closed_context Γ) (Hopen_term : is_open_term Γ u)
               (Htu : cumulSpecE0 Σ Γ Conv t u) (_ : P cf Σ Γ Conv t u Htu)
               (Huv : cumulSpecE0 Σ Γ Conv u v) (_ : P cf Σ Γ Conv u v Huv),
           P cf Σ Γ Conv t v
             (cumulE_Trans _ _ _ _ _ _ Hclosed_ctx Hopen_term Htu Huv)) ->

        (* symmetry *)
       (forall (Γ : context) (t u : term)
               (Hut : cumulSpecE0 Σ Γ Conv u t) (_ : P cf Σ Γ Conv u t Hut),
           P cf Σ Γ Conv t u
             (cumulE_Sym _ _ _ _ _ Hut)) ->

        (* reflexivity *)
        (forall (Γ : context) (t : term),
            P cf Σ Γ Conv t t
              (cumulE_Refl _ _ _ _)) ->

        (* congruence rules *)

        (forall (Γ : context) (ev : nat) (l l' : list term)
                (H : All2 (cumulSpecE0 Σ Γ Conv) l l') (_ : All2_dep (P cf Σ Γ Conv) H),
            P cf Σ Γ Conv (tEvar ev l) (tEvar ev l')
              (cumulE_Evar _ _ _ _ _ _ H)) ->

        (forall (Γ : context) (t t' u u' : term)
                (Htt' : cumulSpecE0 Σ Γ Conv t t') (_ : P cf Σ Γ Conv t t' Htt')
                (Huu' : cumulSpecE0 Σ Γ Conv u u') (_ : P cf Σ Γ Conv u u' Huu'),
            P cf Σ Γ Conv (tApp t u) (tApp t' u')
              (cumulE_App _ _ _ _ _ _ _ Htt' Huu')) ->

        (forall (Γ : context) (na na' : aname) (ty ty' t t' : term)
                (Hna : eq_binder_annot na na')
                (Hty : cumulSpecE0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
                (Ht : cumulSpecE0 Σ (Γ ,, vass na ty) Conv t t') ( _ : P cf Σ (Γ ,, vass na ty) Conv t t' Ht),
            P cf Σ Γ Conv (tLambda na ty t) (tLambda na' ty' t')
              (cumulE_Lambda _ _ _ _ _ _ _ _ _ Hna Hty Ht)) ->

        (forall (Γ : context) (na na' : binder_annot name) (a a' b b' : term)
                (Hna : eq_binder_annot na na')
                (Ha : cumulSpecE0 Σ Γ Conv a a') (_ : P cf Σ Γ Conv a a' Ha)
                (Hb : cumulSpecE0 Σ (Γ,, vass na a) Conv b b') (_ : P cf Σ (Γ,, vass na a) Conv b b' Hb),
            P cf Σ Γ Conv (tProd na a b) (tProd na' a' b')
              (cumulE_Prod _ _ _ _ _ _ _ _ _ Hna Ha Hb)) ->

     (forall (Γ : context) (na na' : binder_annot name) (t t' ty ty' u u' : term)
             (Hna : eq_binder_annot na na')
             (Ht : cumulSpecE0 Σ Γ Conv t t') (_ : P cf Σ Γ Conv t t' Ht)
             (Hty : cumulSpecE0 Σ Γ Conv ty ty') (_ : P cf Σ Γ Conv ty ty' Hty)
             (Hu : cumulSpecE0 Σ (Γ,, vdef na t ty) Conv u u') (_ : P cf Σ (Γ,, vdef na t ty) Conv u u' Hu),
         P cf Σ Γ Conv (tLetIn na t ty u) (tLetIn na' t' ty' u')
           (cumulE_LetIn _ _ _ _ _ _ _ _ _ _ _ Hna Ht Hty Hu)) ->

      (forall (Γ : context) (indn : case_info) (p p' : predicate term)
              (c c' : term) (brs brs' : list (branch term))
              (Hp : cumul_predicate (fun Γ => cumulSpecE0 Σ Γ Conv) (compare_universe Σ Conv) Γ p p')
              (_ : cumul_predicate_dep Hp (fun Γ => P cf Σ Γ Conv) (fun l l' _ => on_rel (fun _ _ => True) Universe.make' l l'))
              (Hc : cumulSpecE0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc)
              (Hbody : cumul_branches (fun Γ => cumulSpecE0 Σ Γ Conv) Γ p brs brs')
              (_ : All2_dep
                     (fun br br' Hc => P cf Σ (Γ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br') (snd Hc)) Hbody),
          P cf Σ Γ Conv (tCase indn p c brs) (tCase indn p' c' brs')
            (cumulE_Case _ _ _ _ _ _ _ _ _ _ Hp Hc Hbody)) ->

       (forall (Γ : context)
               (p : projection) (c c' : term)
               (Hc : cumulSpecE0 Σ Γ Conv c c') (_ : P cf Σ Γ Conv c c' Hc),
           P cf Σ Γ Conv (tProj p c) (tProj p c')
             (cumulE_Proj _ _ _ _ _ _ Hc)) ->

       (forall (Γ : context)
               (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
               (H : cumul_mfixpoint (fun Γ => cumulSpecE0 Σ Γ Conv) Γ mfix mfix')
               (_ : All2_dep
                      (fun x y H
                       => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                      H),
           P cf Σ Γ Conv (tFix mfix idx) (tFix mfix' idx)
             (cumulE_Fix _ _ _ _ _ _ H)) ->

       (forall (Γ : context)
               (mfix : mfixpoint term) (mfix' : list (def term)) (idx : nat)
               (H : cumul_mfixpoint (fun Γ => cumulSpecE0 Σ Γ Conv) Γ mfix mfix')
               (_ : All2_dep
                      (fun x y H
                       => P cf Σ Γ Conv (dtype x) (dtype y) (fst H) × P cf Σ (Γ,,, fix_context mfix) Conv (dbody x) (dbody y) (fst (snd H)))
                      H),
           P cf Σ Γ Conv (tCoFix mfix idx) (tCoFix mfix' idx)
             (cumulE_CoFix _ _ _ _ _ _ H)) ->

      (forall Γ p p' (e : onPrims (cumulSpecE0 Σ Γ Conv) (eq_universe Σ) p p'),
        onPrims_dep (cumulSpecE0 Σ Γ Conv) (eq_universe Σ) (P cf Σ Γ Conv) (fun _ _ _ => True) p p' e ->
        P cf Σ Γ Conv (tPrim p) (tPrim p') (cumulE_Prim _ _ _ _ _ e)) ->

      (* cumulativity rules *)

      (forall (Γ : context) (i : inductive) (u u' : list Level.t)
              (args args' : list term)
              (Hu : cumul_Ind_univ Σ Conv i #|args| u u')
              (Hargs : All2 (cumulSpecE0 Σ Γ Conv) args args')
              (_ : All2_dep (P cf Σ Γ Conv) Hargs),
          P cf Σ Γ Conv (mkApps (tInd i u) args) (mkApps (tInd i u') args')
            (cumulE_Ind _ _ _ _ _ _ _ _ Hu Hargs)) ->

    (forall (Γ : context) (i : inductive) (k : nat)
            (u u' : list Level.t) (args args' : list term)
            (Hu : cumul_Construct_univ Σ Conv i k #|args| u u')
            (Hargs : All2 (cumulSpecE0 Σ Γ Conv) args args')
            (_ : All2_dep (P cf Σ Γ Conv) Hargs),
        P cf Σ Γ Conv (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args')
          (cumulE_Construct _ _ _ _ _ _ _ _ _ Hu Hargs)) ->

      (forall (Γ : context) (s s' : sort)
              (Hs : compare_sort Σ Conv s s'),
          P cf Σ Γ Conv (tSort s) (tSort s')
            (cumulE_Sort _ _ _ _ _ Hs)) ->

      (forall (Γ : context) (c : kername) (u u' : list Level.t)
              (Hu : cmp_universe_instance (compare_universe Σ Conv) u u'),
          P cf Σ Γ Conv (tConst c u) (tConst c u')
            (cumulE_Const _ _ _ _ _ _ Hu)) ->

      (* function eta *)
      (forall (Γ : context) (na : aname) (A t u : term)
              (Ht : cumulSpecE0 Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)))
              (_ : P cf Σ (Γ ,, vass na A) Conv t (tApp (lift0 1 u) (tRel 0)) Ht),
          P cf Σ Γ Conv (tLambda na A t) u
            (cumul_eta_l _ _ _ _ _ _ _ Ht)) ->

       forall (Γ : context) (t t0 : term) (Ht : cumulSpecE0 Σ Γ Conv t t0), P cf Σ Γ Conv t t0 Ht.
Proof.
  intros cf Σ P Hbeta Hzeta Hrel Hiota Hfix Hcofix_case Hcofix_proj Hdelta Hprim_op Hproj
    HTrans HSym HRefl HEvar HApp HLambda HProd HLetIn HCase HProj HFix HCoFix HPrim
    HInd HConstruct HSort HConst Heta Γ t t0 Ht.
  remember Conv as pb eqn:Hpb in Ht |- *.
  revert Hpb.
  induction Ht using cumulSpecE0_rect; intros Hpb; subst pb.
  all: try solve [ first [ eapply Hbeta | eapply Hzeta | eapply Hrel | eapply Hiota | eapply Hfix
                         | eapply Hcofix_case | eapply Hcofix_proj | eapply Hdelta | eapply Hprim_op | eapply Hproj
                         | eapply HRefl | eapply HSort | eapply HConst ]; eauto ].
  - eapply HTrans; eauto.
  - eapply HSym; eauto.
  - eapply HEvar. eapply All2_dep_impl; tea. cbv beta; intuition auto.
  - eapply HApp; eauto.
  - eapply HLambda; eauto.
  - eapply HProd; eauto.
  - eapply HLetIn; eauto.
  - eapply HCase; eauto.
    + cbv [cumul_predicate_dep] in *. repeat destruct ?; subst.
      destruct_head'_prod. repeat split; eauto.
      eapply All2_dep_impl; tea; cbv beta; intuition auto.
    + eapply All2_dep_impl; tea; cbv beta; intuition auto.
  - eapply HProj; eauto.
  - eapply HFix. eapply All2_dep_impl; tea; cbv beta; intuition auto.
  - eapply HCoFix. eapply All2_dep_impl; tea; cbv beta; intuition auto.
  - eapply HPrim. match goal with H : onPrims_dep _ _ _ _ _ _ _ |- _ => destruct H end;
      constructor; auto. eapply All2_dep_impl; tea; intuition auto.
  - eapply HInd. eapply All2_dep_impl; tea; cbv beta; intuition auto.
  - eapply HConstruct. eapply All2_dep_impl; tea; cbv beta; intuition auto.
  - eapply Heta; eauto.
Defined.

(** * Inclusion of the base specification (S1) *)

Lemma cumulSpec0_incl_E {cf} (Σ : global_env_ext) Γ pb t u :
  Σ ;;; Γ ⊢ t ≤s[pb] u -> Σ ;;; Γ ⊢ t ≤sE[pb] u.
Proof.
  revert Γ pb t u.
  apply (cumulSpec0_rect cf Σ (fun cf Σ Γ pb t u _ => @cumulSpecE0 cf Σ Γ pb t u)); intros.
  all: repeat match goal with
         | [ H : All2_dep _ _ |- _ ] => apply All2_undep in H
         end.
  - apply cumulE_beta.
  - apply cumulE_zeta.
  - now apply cumulE_rel.
  - now apply cumulE_iota.
  - now eapply cumulE_fix.
  - now eapply cumulE_cofix_case.
  - now eapply cumulE_cofix_proj.
  - now eapply cumulE_delta.
  - now eapply cumulE_prim_op.
  - now apply cumulE_proj.
  - now eapply cumulE_Trans.
  - now apply cumulE_Sym.
  - apply cumulE_Refl.
  - now apply cumulE_Evar.
  - now apply cumulE_App.
  - now apply cumulE_Lambda.
  - now apply cumulE_Prod.
  - now apply cumulE_LetIn.
  - apply cumulE_Case; auto.
    + cbv [cumul_predicate cumul_predicate_dep] in *.
      destruct Hp as [Hpars [Hu [Hctx Hret]]].
      destruct_head'_prod.
      repeat split; auto.
      now apply All2_undep in a.
    + unfold cumul_branches, cumul_branch in *.
      eapply All2_impl; [exact (All2_prod _ _ _ _ Hbody X1)|].
      intros x y [[Hctx _] Hb]. split; auto.
  - now apply cumulE_Proj.
  - apply cumulE_Fix. unfold cumul_mfixpoint.
    eapply All2_impl; [exact (All2_prod _ _ _ _ H X)|].
    intros x y [[_ [_ [Hr Hn]]] [Hty Hbo]]. repeat split; auto.
  - apply cumulE_CoFix. unfold cumul_mfixpoint.
    eapply All2_impl; [exact (All2_prod _ _ _ _ H X)|].
    intros x y [[_ [_ [Hr Hn]]] [Hty Hbo]]. repeat split; auto.
  - apply cumulE_Prim.
    match goal with H : onPrims_dep _ _ _ _ _ _ _ |- _ => destruct H end; constructor; auto.
    match goal with H : All2_dep _ _ |- _ => now apply All2_undep in H end.
  - now apply cumulE_Ind.
  - now apply cumulE_Construct.
  - now apply cumulE_Sort.
  - now apply cumulE_Const.
Qed.

(** * Derived eta lemmas (S4) *)

Section DerivedEta.
  Context {cf : checker_flags} (Σ : global_env_ext).

  (** The mirror rule. No scoping premise is needed: it is [cumulE_Sym] around [cumul_eta_l]. *)
  Lemma cumul_eta_r Γ pb na A t u :
    Σ ;;; Γ ,, vass na A ⊢ tApp (lift0 1 u) (tRel 0) ≤sE[Conv] t ->
    Σ ;;; Γ ⊢ u ≤sE[pb] tLambda na A t.
  Proof.
    intros H. apply cumulE_Sym, cumul_eta_l, cumulE_Sym, H.
  Qed.

  (** Eta contraction. No scoping premise is needed: [cumul_eta_l] on [cumulE_Refl]. *)
  Lemma cumulSpecE_eta_contract Γ pb na A u :
    Σ ;;; Γ ⊢ tLambda na A (tApp (lift0 1 u) (tRel 0)) ≤sE[pb] u.
  Proof.
    apply cumul_eta_l, cumulE_Refl.
  Qed.

  (** Two lambdas whose bodies are related are related, whatever their domains and
      binder annotations. *)
  Lemma cumulSpecE_lambda_domain Γ pb na na' A B t t' :
    is_closed_context Γ ->
    is_open_term Γ (tLambda na A t) ->
    is_open_term Γ (tLambda na' B t') ->
    Σ ;;; Γ ,, vass na A ⊢ t ≤sE[Conv] t' ->
    Σ ;;; Γ ⊢ tLambda na A t ≤sE[pb] tLambda na' B t'.
  Proof.
    intros clΓ onl onr H.
    apply cumul_eta_l.
    cbn in onl, onr. move/andP: onl => [onA _]. move/andP: onr => [_ ont'].
    assert (h0 : 0 <= 0) by lia.
    assert (He : (lift 1 1 t') {0 := tRel 0} = t').
    { unfold subst1. rewrite (subst_reli_lift_id 0 0 t' h0). apply lift0_id. }
    eapply cumulE_Trans with (u := t').
    - rewrite on_free_vars_ctx_snoc clΓ /=. exact onA.
    - replace #|Γ ,, vass na A| with (S #|Γ|) by reflexivity.
      rewrite shiftnP_S. exact ont'.
    - exact H.
    - apply cumulE_Sym.
      pose proof (cumulE_beta Σ (Γ ,, vass na A) Conv na' (lift0 1 B) (lift 1 1 t') (tRel 0)) as Hb.
      rewrite He in Hb. exact Hb.
  Qed.

End DerivedEta.
