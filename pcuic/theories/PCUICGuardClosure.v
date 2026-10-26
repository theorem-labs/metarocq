(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICClosed PCUICSigmaCalculus PCUICEquality
     PCUICReduction PCUICCumulativitySpec PCUICOnFreeVars.
From MetaRocq.PCUIC Require Export PCUICGuardChecker.

From Stdlib Require Import ssreflect ssrbool.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * The guard predicate as the closure of the executable check

  [guard_cl] is the least predicate on fixpoint and cofixpoint blocks that
  contains every *case-well-formed* block that [check_guard_gen] accepts and
  that is closed under the seven operations of [GuardCheckerCorrect]:
  one-step reduction (in a case-well-formed environment and context),
  equality up to names, extension of the environment, cumulativity of the
  context, universe instantiation, substitution of case-well-formed terms
  for the block's free variables, and renaming.

  Because every closure property is a constructor, each field of
  [GuardCheckerCorrect] ([PCUICGuardCondition]) becomes a theorem, and both
  [Axiom guard_checking] and [Axiom guard_checking_correct] disappear.

  The one syntactic invariant the closure maintains is *case well-formedness*
  ([wf_cases]): every [tCase] node carries the predicate and branch contexts
  that its inductive declares, and every [tProj] node a declared projection.
  Without it the closure would contain blocks whose branch contexts capture
  the block's own recursive names, since PCUIC's raw syntax never renumbers
  a branch context. *)

Implicit Types (cf : checker_flags).

(** ** Operations on blocks (moved here from [PCUICTyping]/[PCUICGuardCondition]) *)

Definition tFixCoFix (b : FixCoFix) := match b with Fix => tFix | CoFix => tCoFix end.

Definition subst_instance_mfix (mfix : list (def term)) u :=
  map (map_def (subst_instance u) (subst_instance u)) mfix.

Definition inst_mfix mfix σ :=
  map (map_def (inst σ) (inst (up (List.length mfix) σ))) mfix.

Definition rename_mfix mfix f :=
  map (map_def (rename f) (rename (shiftn (List.length mfix) f))) mfix.

(** [closedn] of a block in a context of length [k]: the conditions
    [closedn k (tFix mfix idx)] makes. *)
Definition closedn_mfix k (mfix : mfixpoint term) : bool :=
  forallb (test_def (closedn k) (closedn (#|mfix| + k))) mfix.

(** ** Case well-formedness

  [wf_cases Σ t] is the conjunction, over every [tCase] and [tProj] node of
  [t], of exactly the syntactic premises of [type_Case] and [type_Proj]
  ([PCUICTyping], [case_side_conditions] and [case_branch_typing]).  The
  other premises of those rules mention typing or universes and are left out
  on purpose. *)

(** [isCoFinite] itself is defined in [PCUICTyping], which comes later. *)
Definition is_cofinite (r : recursivity_kind) : bool :=
  match r with CoFinite => true | _ => false end.

Lemma eqb_eq_true {A} {R : ReflectEq A} (x y : A) : x = y -> eqb x y.
Proof. intros ->. apply eqb_refl. Qed.

Lemma eqb_annot_true {A} (na na' : binder_annot A) :
  eqb_binder_annot na na' -> eq_binder_annot na na'.
Proof. rewrite /eqb_binder_annot /eq_binder_annot. destruct Classes.eq_dec => //. Qed.

Lemma eqb_annot_of_eq {A} (na na' : binder_annot A) :
  eq_binder_annot na na' -> eqb_binder_annot na na'.
Proof. rewrite /eqb_binder_annot /eq_binder_annot. destruct Classes.eq_dec => //. Qed.

Definition eqb_decl_alpha (d d' : context_decl) : bool :=
  eqb_binder_annot d.(decl_name) d'.(decl_name) &&
  eqb d.(decl_body) d'.(decl_body) && eqb d.(decl_type) d'.(decl_type).

Definition eqb_context_alpha (Γ Δ : context) : bool :=
  forallb2 eqb_decl_alpha Γ Δ.

Lemma eqb_decl_alpha_elim d d' :
  eqb_decl_alpha d d' -> ∥ eq_decl_upto_names d d' ∥.
Proof.
  rewrite /eqb_decl_alpha.
  destruct (eqb_binder_annot d.(decl_name) d'.(decl_name)) eqn:ha;
  destruct (eqb d.(decl_body) d'.(decl_body)) eqn:hb;
  destruct (eqb d.(decl_type) d'.(decl_type)) eqn:ht; cbn; intros h; try discriminate.
  apply eqb_annot_true in ha. apply eqb_eq in hb. apply eqb_eq in ht.
  destruct d as [na bo ty], d' as [na' bo' ty']; cbn in *; subst.
  destruct bo' as [b|]; sq; constructor; assumption.
Qed.

Lemma eqb_decl_alpha_intro d d' :
  eq_decl_upto_names d d' -> eqb_decl_alpha d d'.
Proof.
  rewrite /eqb_decl_alpha.
  intros [na na' T h|na na' b T h]; cbn;
    rewrite (eqb_annot_of_eq _ _ h) !eqb_refl //.
Qed.

Lemma forallb2_All2_sq {A B} (f : A -> B -> bool) (P : A -> B -> Type) l l' :
  (forall x y, f x y -> ∥ P x y ∥) -> forallb2 f l l' -> ∥ All2 P l l' ∥.
Proof.
  intros hf. induction l in l' |- *; destruct l'; cbn; intros h; try discriminate.
  - sq. constructor.
  - move/andP: h => [] h1 h2.
    apply hf in h1. apply IHl in h2. sq. now constructor.
Qed.

Lemma All2_forallb2_impl {A B} (f : A -> B -> bool) (P : A -> B -> Type) l l' :
  (forall x y, P x y -> f x y) -> All2 P l l' -> forallb2 f l l'.
Proof.
  intros hf h. induction h => //=. apply/andP; split; auto.
Qed.

Lemma eqb_context_alpha_elim Γ Δ :
  eqb_context_alpha Γ Δ -> ∥ eq_context_upto_names Γ Δ ∥.
Proof. apply forallb2_All2_sq, eqb_decl_alpha_elim. Qed.

Lemma eqb_context_alpha_intro Γ Δ :
  eq_context_upto_names Γ Δ -> eqb_context_alpha Γ Δ.
Proof. apply All2_forallb2_impl, eqb_decl_alpha_intro. Qed.

Lemma eqb_context_alphaP Γ Δ :
  reflectProp (∥ eq_context_upto_names Γ Δ ∥) (eqb_context_alpha Γ Δ).
Proof.
  destruct (eqb_context_alpha Γ Δ) eqn:e; constructor.
  - apply eqb_context_alpha_elim. now rewrite e.
  - intros []. apply eqb_context_alpha_intro in X. congruence.
Qed.

(** The node condition of a [tCase], as a boolean.  Its last conjunct is
    typing's own condition on a case over a coinductive type: the return type
    does not mention the scrutinee, variable 0 of the predicate context. *)
Definition wf_case_node (Σ : global_env) (ci : case_info)
  (p : predicate term) (brs : list (branch term)) : bool :=
  match lookup_inductive Σ ci.(ci_ind) with
  | Some (mdecl, idecl) =>
    eqb mdecl.(ind_npars) ci.(ci_npar) &&
    wf_predicateb mdecl idecl p &&
    eqb_context_alpha p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) &&
    wf_branchesb idecl brs &&
    forallb2 (fun cdecl br =>
      eqb_context_alpha br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl))
      idecl.(ind_ctors) brs &&
    (is_cofinite mdecl.(ind_finite) ==>
     on_free_vars (strengthenP 0 1 xpredT) p.(preturn))
  | None => false
  end.

(** The same condition, with typing's own predicates, by name. *)
Definition wf_case_spec (Σ : global_env) (ci : case_info)
  (p : predicate term) (brs : list (branch term)) : Prop :=
  exists mdecl idecl,
    declared_inductive_gen (lookup_env Σ) ci.(ci_ind) mdecl idecl /\
    mdecl.(ind_npars) = ci.(ci_npar) /\
    wf_predicate mdecl idecl p /\
    ∥ eq_context_upto_names p.(pcontext)
        (ind_predicate_context ci.(ci_ind) mdecl idecl) ∥ /\
    wf_branches idecl brs /\
    ∥ All2 (fun cdecl br =>
        eq_context_upto_names br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl))
        idecl.(ind_ctors) brs ∥ /\
    (is_cofinite mdecl.(ind_finite) ==>
     on_free_vars (strengthenP 0 1 xpredT) p.(preturn)) = true.

Lemma wf_case_node_elim {Σ ci p brs} :
  wf_case_node Σ ci p brs -> wf_case_spec Σ ci p brs.
Proof.
  rewrite /wf_case_node.
  destruct (lookup_inductive Σ ci.(ci_ind)) as [[mdecl idecl]|] eqn:hl => //.
  move/andP => [] /andP [] /andP [] /andP [] /andP [] e1 e2 e3 e4 e5 e6.
  exists mdecl, idecl.
  split; [exact (lookup_inductive_declared_gen hl)|].
  split; [now apply eqb_eq|].
  split; [exact (ReflectEq.elimP (wf_predicateP mdecl idecl p) e2)|].
  split; [now apply eqb_context_alpha_elim|].
  split; [exact (elimT (wf_branchesP idecl brs) e4)|].
  split.
  - now apply (forallb2_All2_sq _ _ _ _ (fun cdecl br =>
      eqb_context_alpha_elim br.(bcontext)
        (cstr_branch_context ci.(ci_ind) mdecl cdecl))).
  - exact e6.
Qed.

(** The introduction rule: exactly [type_Case]'s syntactic premises. *)
Lemma wf_case_node_intro {Σ ci p brs mdecl idecl} :
  declared_inductive_gen (lookup_env Σ) ci.(ci_ind) mdecl idecl ->
  mdecl.(ind_npars) = ci.(ci_npar) ->
  wf_predicate mdecl idecl p ->
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  wf_branches idecl brs ->
  All2 (fun cdecl br =>
    eq_context_upto_names br.(bcontext) (cstr_branch_context ci.(ci_ind) mdecl cdecl))
    idecl.(ind_ctors) brs ->
  (is_cofinite mdecl.(ind_finite) ==>
   on_free_vars (strengthenP 0 1 xpredT) p.(preturn)) = true ->
  wf_case_node Σ ci p brs.
Proof.
  intros hd e1 e2 e3 e4 e5 e6.
  rewrite /wf_case_node /lookup_inductive (declared_inductive_lookup_gen hd).
  rewrite (eqb_eq_true _ _ e1) (ReflectEq.introP (wf_predicateP mdecl idecl p) e2).
  rewrite (eqb_context_alpha_intro _ _ e3) (introT (wf_branchesP idecl brs) e4).
  rewrite (All2_forallb2_impl _ _ _ _ (fun cdecl br =>
    eqb_context_alpha_intro br.(bcontext)
      (cstr_branch_context ci.(ci_ind) mdecl cdecl)) e5).
  now rewrite e6.
Qed.

Lemma wf_case_nodeP Σ ci p brs :
  reflectProp (wf_case_spec Σ ci p brs) (wf_case_node Σ ci p brs).
Proof.
  destruct (wf_case_node Σ ci p brs) eqn:e; constructor.
  - apply wf_case_node_elim. now rewrite e.
  - intros (mdecl & idecl & hd & e1 & e2 & [e3] & e4 & [e5] & e6).
    rewrite (wf_case_node_intro hd e1 e2 e3 e4 e5 e6) in e. discriminate.
Qed.

Definition wf_proj_node (Σ : global_env) (p : projection) : bool :=
  match lookup_projection Σ p with
  | Some (mdecl, idecl, cdecl, pdecl) => eqb mdecl.(ind_npars) p.(proj_npars)
  | None => false
  end.

Definition wf_proj_spec (Σ : global_env) (p : projection) : Prop :=
  exists mdecl idecl cdecl pdecl,
    declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl.

Lemma wf_proj_node_elim {Σ p} : wf_proj_node Σ p -> wf_proj_spec Σ p.
Proof.
  rewrite /wf_proj_node.
  destruct (lookup_projection Σ p) as [[[[mdecl idecl] cdecl] pdecl]|] eqn:hl => //.
  intros he. apply eqb_eq in he. exists mdecl, idecl, cdecl, pdecl.
  now apply (lookup_projection_declared_gen he hl).
Qed.

Lemma wf_proj_node_intro {Σ p mdecl idecl cdecl pdecl} :
  declared_projection_gen (lookup_env Σ) p mdecl idecl cdecl pdecl ->
  wf_proj_node Σ p.
Proof.
  intros hd.
  rewrite /wf_proj_node /lookup_projection (declared_projection_lookup_gen hd).
  apply eqb_eq_true. apply hd.
Qed.

Lemma wf_proj_nodeP Σ p : reflectProp (wf_proj_spec Σ p) (wf_proj_node Σ p).
Proof.
  destruct (wf_proj_node Σ p) eqn:e; constructor.
  - apply wf_proj_node_elim. now rewrite e.
  - intros (mdecl & idecl & cdecl & pdecl & hd).
    rewrite (wf_proj_node_intro hd) in e. discriminate.
Qed.

(** The generic traversal: [fc] is checked at every [tCase] node and [fp] at
    every [tProj] node.  The predicate and branch *contexts* are not
    traversed: they are pinned to the inductive's own contexts by [fc], so
    any case inside them comes from the global environment, where
    [wf_cases_env] covers it. *)
Section TestCases.
  Context (fc : case_info -> predicate term -> list (branch term) -> bool).
  Context (fp : projection -> bool).

  Fixpoint test_cases (t : term) : bool :=
    match t with
    | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => true
    | tEvar _ args => forallb test_cases args
    | tProd _ A B => test_cases A && test_cases B
    | tLambda _ A b => test_cases A && test_cases b
    | tLetIn _ b B u => test_cases b && test_cases B && test_cases u
    | tApp u v => test_cases u && test_cases v
    | tCase ci p c brs =>
      fc ci p brs && forallb test_cases p.(pparams) && test_cases p.(preturn) &&
      test_cases c && forallb (fun br => test_cases br.(bbody)) brs
    | tProj p c => fp p && test_cases c
    | tFix mfix _ | tCoFix mfix _ => forallb (test_def test_cases test_cases) mfix
    | tPrim p => test_prim test_cases p
    end.
End TestCases.

Lemma test_cases_impl (fc fc' : case_info -> predicate term -> list (branch term) -> bool)
  (fp fp' : projection -> bool) t :
  (forall ci p brs, fc ci p brs -> fc' ci p brs) ->
  (forall p, fp p -> fp' p) ->
  test_cases fc fp t -> test_cases fc' fp' t.
Proof.
  intros hc hp.
  induction t using term_forall_list_ind; cbn in * => //.
  all: try (destruct X as (hpars & hctx & hret)).
  all: try (destruct p as [? []]; cbn in * => //).
  all: try (destruct X as (hty & hdef & hval)).
  all: intros h; rtoProp; repeat split;
       try first [ now apply hc | now apply hp | now auto | solve_all ].
  all: unfold test_def in *; rtoProp; repeat split; intuition auto.
Qed.

Definition wf_cases (Σ : global_env) (t : term) : bool :=
  test_cases (wf_case_node Σ) (wf_proj_node Σ) t.

Definition wf_cases_mfix (Σ : global_env) (m : mfixpoint term) : bool :=
  forallb (test_def (wf_cases Σ) (wf_cases Σ)) m.

Definition wf_cases_ctx (Σ : global_env) (Γ : context) : bool :=
  forallb (test_decl (wf_cases Σ)) Γ.

(** The conditions a declaration must satisfy, taken by name from
    [on_global_env]/[on_inductive]/[on_constructor]:
    - [onNpars] and the closedness of the parameters, indices, constructor
      arguments and constructor indices, which the capture-freedom lemma of
      [PCUICCasesWfTyp] needs;
    - case well-formedness of every type and [let] body in them, and of every
      constant's type and body, which [ι] and [red_rel] in branch and return
      contexts bring into a term. *)
Definition wf_cases_decl (Σ : global_env) (d : global_decl) : bool :=
  match d with
  | ConstantDecl cb =>
    wf_cases Σ cb.(cst_type) && option_default (wf_cases Σ) cb.(cst_body) true
  | InductiveDecl mdecl =>
    closed_inductive_decl mdecl &&
    eqb mdecl.(ind_npars) (context_assumptions mdecl.(ind_params)) &&
    wf_cases_ctx Σ mdecl.(ind_params) &&
    forallb (fun idecl =>
      wf_cases Σ idecl.(ind_type) &&
      wf_cases_ctx Σ idecl.(ind_indices) &&
      forallb (fun cdecl =>
        wf_cases_ctx Σ cdecl.(cstr_args) &&
        forallb (wf_cases Σ) cdecl.(cstr_indices)) idecl.(ind_ctors))
      mdecl.(ind_bodies)
  end.

Definition wf_cases_env (Σ : global_env) : bool :=
  forallb (fun d => wf_cases_decl Σ d.2) Σ.(declarations).

Lemma wf_cases_env_lookup {Σ kn d} :
  wf_cases_env Σ -> lookup_env Σ kn = Some d -> wf_cases_decl Σ d.
Proof.
  rewrite /wf_cases_env /lookup_env.
  induction Σ.(declarations) as [|[kn' d'] decls ih]; cbn => //.
  move/andP => [] hd hdecls.
  destruct (eqb_spec kn kn') as [->|] => //=.
  - now intros [= <-].
  - now apply ih.
Qed.

(** ** The closure *)

Definition check_ok (b : FixCoFix) (Σ : global_env_ext) (Γ : context)
  (m : mfixpoint term) : Prop :=
  wf_cases_mfix Σ.1 m /\
  exists fuel,
    check_guard_gen (lookup_env Σ.1) Σ.1.(retroknowledge) fuel b #|Γ|
      (strip_mfix m) = Accept.

Inductive guard_cl (b : FixCoFix) : global_env_ext -> context -> mfixpoint term -> Prop :=
| gc_check (Σ : global_env_ext) (Γ : context) (m : mfixpoint term) :
    check_ok b Σ Γ m -> guard_cl b Σ Γ m

| gc_red1 (Σ : global_env_ext) (Γ : context) (m m' : mfixpoint term) (i : nat) :
    wf_cases_env Σ.1 -> wf_cases_ctx Σ.1 Γ ->
    ∥ red1 Σ.1 Γ (tFixCoFix b m i) (tFixCoFix b m' i) ∥ ->
    guard_cl b Σ Γ m -> guard_cl b Σ Γ m'

| gc_eq (Σ : global_env_ext) (Γ : context) (m m' : mfixpoint term) (i : nat) :
    ∥ upto_names (tFixCoFix b m i) (tFixCoFix b m' i) ∥ ->
    guard_cl b Σ Γ m -> guard_cl b Σ Γ m'

| gc_ext (Σ Σ' : global_env_ext) (Γ : context) (m : mfixpoint term) :
    extends Σ Σ' -> guard_cl b Σ Γ m -> guard_cl b Σ' Γ m

| gc_ctx (cf : checker_flags) (Σ : global_env_ext) (Γ Γ' : context)
    (m : mfixpoint term) :
    ∥ All2_fold (cumul_decls cumulSpec0 Σ) Γ' Γ ∥ ->
    guard_cl b Σ Γ m -> guard_cl b Σ Γ' m

| gc_univ (Σ : global_env_ext) (Γ : context) (m : mfixpoint term)
    (u : Instance.t) (us : universes_decl) :
    guard_cl b Σ Γ m ->
    guard_cl b (Σ.1, us) (subst_instance u Γ) (subst_instance_mfix m u)

| gc_inst (Σ : global_env_ext) (Γ Δ : context) (m : mfixpoint term) (σ : nat -> term) :
    closedn_mfix #|Δ| m ->
    (forall x, x < #|Δ| -> wf_cases Σ.1 (σ x)) ->
    guard_cl b Σ Δ m -> guard_cl b Σ Γ (inst_mfix m σ)

| gc_ren (Σ : global_env_ext) (Γ Δ : context) (m : mfixpoint term) (f : nat -> nat) :
    guard_cl b Σ Γ m -> guard_cl b Σ Δ (rename_mfix m f).
