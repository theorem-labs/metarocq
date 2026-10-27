(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICUnivSubst
     PCUICCases PCUICReduction PCUICPrimitiveRed.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Default Goal Selector "!".

(** * The kernel's decomposition of an inductive's user arity

  Rocq's kernel computes the arity of an inductive from its user arity with
  [Reduction.dest_arity] (kernel/reduction.ml), that is
  [whd_decompose_prod_decls] followed by a check that the result is a sort.
  At each level of the telescope it reduces with [whd_allnolet] (all
  reductions but zeta; a let-bound variable is still unfolded, under delta),
  keeps an exposed product or let as a declaration, and otherwise falls back to
  [whd_all] once and recurses if that made progress.

  [whd_rel zeta Σ Γ t args h l] is the graph of the weak-head machine of
  [PCUICSafeReduce._reduce_stack] with every flag on except possibly [zeta],
  on the term [t] applied to the arguments [args]: it stops at [h] applied to
  [l].  It is big-step, like the machine, and it keeps the subterms the machine
  keeps: fix unfolding puts the *reduced* recursive argument back, and a stuck
  case, fix or projection keeps its reduced discriminant.  Each contraction
  carries the side condition [red1] needs, so a derivation is a reduction
  ([whd_rel_red]) without any typing.  It describes the kernel without
  call-by-need sharing.

  [arity_red Σ Γ t Δ s] is the graph of [dest_arity]: in context [Γ], [t]
  decomposes into the telescope [Δ] (innermost declaration first, as
  [it_mkProd_or_LetIn] reads it) ending in [tSort s].

  All relations are in [Type], like [red1] and [typing], so that they can be
  quoted. *)

Definition whd_is_construct (t : term) : bool :=
  match t with tConstruct _ _ _ => true | _ => false end.

Definition whd_is_construct0 (t : term) : bool :=
  match t with tConstruct _ 0 _ => true | _ => false end.

Definition whd_is_cofix (t : term) : bool :=
  match t with tCoFix _ _ => true | _ => false end.

(** The machine's [red_discr]: the heads on which it stops at once. *)
Definition whd_stop_head (t : term) (args : list term) : bool :=
  match t with
  | tRel _ | tLetIn _ _ _ _ | tConst _ _ | tApp _ _
  | tFix _ _ | tCase _ _ _ _ | tProj _ _ => false
  | tLambda _ _ _ => match args with [] => true | _ :: _ => false end
  | _ => true
  end.

(** A head that ends one level of [whd_decompose_prod_decls]. *)
Definition whd_arity_head (t : term) (args : list term) : bool :=
  match t, args with
  | tProd _ _ _, [] | tLetIn _ _ _ _, [] | tSort _, [] => true
  | _, _ => false
  end.

Inductive whd_rel (zeta : bool) (Σ : global_env) (Γ : context) :
  term -> list term -> term -> list term -> Type :=
(** A let-bound variable is unfolded whatever [zeta] is: the kernel unfolds a
    [RelKey] under delta (kernel/cClosure.ml, [knr]). *)
| whd_rel_unfold c args d b h l :
    nth_error Γ c = Some d -> d.(decl_body) = Some b ->
    whd_rel zeta Σ Γ (lift0 (S c) b) args h l ->
    whd_rel zeta Σ Γ (tRel c) args h l
| whd_rel_assum c args d :
    nth_error Γ c = Some d -> d.(decl_body) = None ->
    whd_rel zeta Σ Γ (tRel c) args (tRel c) args
| whd_zeta na b B t args h l :
    zeta = true ->
    whd_rel zeta Σ Γ (t {0 := b}) args h l ->
    whd_rel zeta Σ Γ (tLetIn na b B t) args h l
| whd_letin_stop na b B t args :
    zeta = false ->
    whd_rel zeta Σ Γ (tLetIn na b B t) args (tLetIn na b B t) args
(** The machine looks the constant up ([abstract_env_lookup]); [lookup_env]
    finds the first declaration, so the rule is deterministic even on an
    environment with duplicate names. *)
| whd_delta c u decl body args h l :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = Some body ->
    whd_rel zeta Σ Γ (subst_instance u body) args h l ->
    whd_rel zeta Σ Γ (tConst c u) args h l
| whd_axiom c u decl args :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
    prim_op_of Σ c = None ->
    whd_rel zeta Σ Γ (tConst c u) args (tConst c u) args
| whd_app f a args h l :
    whd_rel zeta Σ Γ f (a :: args) h l ->
    whd_rel zeta Σ Γ (tApp f a) args h l
| whd_beta na A t a args h l :
    whd_rel zeta Σ Γ (t {0 := a}) args h l ->
    whd_rel zeta Σ Γ (tLambda na A t) (a :: args) h l
(** [PCUICSafeReduce.v], [_reduce_stack], [red_view_Fix]: the recursive
    argument is reduced, and put back reduced. *)
| whd_fix_iota mfix idx narg fn args c ind n ui cargs h l :
    unfold_fix mfix idx = Some (narg, fn) ->
    nth_error args narg = Some c ->
    whd_rel zeta Σ Γ c [] (tConstruct ind n ui) cargs ->
    whd_rel zeta Σ Γ fn
      (firstn narg args ++ mkApps (tConstruct ind n ui) cargs :: skipn (S narg) args) h l ->
    whd_rel zeta Σ Γ (tFix mfix idx) args h l
| whd_fix_stuck mfix idx narg fn args c t cargs :
    unfold_fix mfix idx = Some (narg, fn) ->
    nth_error args narg = Some c ->
    whd_rel zeta Σ Γ c [] t cargs -> whd_is_construct t = false ->
    whd_rel zeta Σ Γ (tFix mfix idx) args
      (tFix mfix idx) (firstn narg args ++ mkApps t cargs :: skipn (S narg) args)
| whd_fix_noarg mfix idx narg fn args :
    unfold_fix mfix idx = Some (narg, fn) -> nth_error args narg = None ->
    whd_rel zeta Σ Γ (tFix mfix idx) args (tFix mfix idx) args
| whd_fix_nounfold mfix idx args :
    unfold_fix mfix idx = None ->
    whd_rel zeta Σ Γ (tFix mfix idx) args (tFix mfix idx) args
(** [red_view_Case]. *)
| whd_iota ci p c brs args n ui cargs br h l :
    whd_rel zeta Σ Γ c [] (tConstruct ci.(ci_ind) n ui) cargs ->
    nth_error brs n = Some br ->
    #|cargs| = ci.(ci_npar) + context_assumptions br.(bcontext) ->
    whd_rel zeta Σ Γ (iota_red ci.(ci_npar) p cargs br) args h l ->
    whd_rel zeta Σ Γ (tCase ci p c brs) args h l
| whd_case_cofix ci p c brs args mfix idx cargs narg fn h l :
    whd_rel zeta Σ Γ c [] (tCoFix mfix idx) cargs ->
    unfold_cofix mfix idx = Some (narg, fn) ->
    whd_rel zeta Σ Γ (tCase ci p (mkApps fn cargs) brs) args h l ->
    whd_rel zeta Σ Γ (tCase ci p c brs) args h l
| whd_case_stuck ci p c brs args t cargs :
    whd_rel zeta Σ Γ c [] t cargs ->
    whd_is_construct t = false -> whd_is_cofix t = false ->
    whd_rel zeta Σ Γ (tCase ci p c brs) args (tCase ci p (mkApps t cargs) brs) args
(** [red_view_Proj]. *)
| whd_proj p c args u cargs a h l :
    whd_rel zeta Σ Γ c [] (tConstruct p.(proj_ind) 0 u) cargs ->
    nth_error cargs (p.(proj_npars) + p.(proj_arg)) = Some a ->
    whd_rel zeta Σ Γ a args h l ->
    whd_rel zeta Σ Γ (tProj p c) args h l
| whd_proj_cofix p c args mfix idx cargs narg fn h l :
    whd_rel zeta Σ Γ c [] (tCoFix mfix idx) cargs ->
    unfold_cofix mfix idx = Some (narg, fn) ->
    whd_rel zeta Σ Γ (tProj p (mkApps fn cargs)) args h l ->
    whd_rel zeta Σ Γ (tProj p c) args h l
| whd_proj_stuck p c args t cargs :
    whd_rel zeta Σ Γ c [] t cargs ->
    whd_is_construct0 t = false -> whd_is_cofix t = false ->
    whd_rel zeta Σ Γ (tProj p c) args (tProj p (mkApps t cargs)) args
(** [red_view_other]. *)
| whd_stop t args :
    whd_stop_head t args ->
    whd_rel zeta Σ Γ t args t args
(** [PCUICSafeReduce.v], [_reduce_stack], [Prim_app] (design §7.2): a
    registered bodiless operation saturated on the stack evaluates its
    arguments left to right.  [split_lits (firstn (arity op) args)] reads the
    first [arity op] arguments: [inl ls] when all are literals (the operation
    fires), [inr (ls, a, rest)] when [a] is the first that is not (reduce it,
    then re-enter or stop).  Over-application leaves [skipn (arity op) args] on
    the stack, as the machine does. *)
| whd_prim_arg c u decl op args ls a rest t cargs lit h l :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
    prim_op_of Σ c = Some op -> arity op <= #|args| ->
    split_lits (firstn (arity op) args) = inr (ls, a, rest) ->
    whd_rel zeta Σ Γ a [] t cargs ->
    lit_of_term (mkApps t cargs) = Some lit ->
    whd_rel zeta Σ Γ (tConst c u)
      (map term_of_lit ls ++ mkApps t cargs :: rest ++ skipn (arity op) args) h l ->
    whd_rel zeta Σ Γ (tConst c u) args h l
| whd_prim_stuck c u decl op args ls a rest t cargs :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
    prim_op_of Σ c = Some op -> arity op <= #|args| ->
    split_lits (firstn (arity op) args) = inr (ls, a, rest) ->
    whd_rel zeta Σ Γ a [] t cargs ->
    lit_of_term (mkApps t cargs) = None ->
    whd_rel zeta Σ Γ (tConst c u) args
      (tConst c u) (map term_of_lit ls ++ mkApps t cargs :: rest ++ skipn (arity op) args)
| whd_prim_fire c u decl op args ls r v h l :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
    prim_op_of Σ c = Some op -> arity op <= #|args| ->
    split_lits (firstn (arity op) args) = inl ls ->
    prim_op_denote op ls = Some r ->
    readback Σ (po_shape (info op)) r = Some v ->
    whd_rel zeta Σ Γ v (skipn (arity op) args) h l ->
    whd_rel zeta Σ Γ (tConst c u) args h l
| whd_prim_inert c u decl op args ls :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
    prim_op_of Σ c = Some op -> arity op <= #|args| ->
    split_lits (firstn (arity op) args) = inl ls ->
    prim_op_denote op ls = None ->
    whd_rel zeta Σ Γ (tConst c u) args (tConst c u) args
| whd_prim_partial c u decl op args :
    lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None ->
    prim_op_of Σ c = Some op -> #|args| < arity op ->
    whd_rel zeta Σ Γ (tConst c u) args (tConst c u) args.

Derive Signature for whd_rel.

(** [allnolet] and [all] of kernel/redFlags.ml. *)
Abbreviation whd_allnolet_rel := (whd_rel false).
Abbreviation whd_all_rel := (whd_rel true).

(** ** Helpers shared by the primitive cases of the lemmas below *)

(** The arguments before and after the one being evaluated do not move, so a
    reduction of that one argument is a reduction of the whole application. *)
Lemma red_prim_arg_cong Σ Γ c u ls a b rest tail :
  red Σ Γ a b ->
  red Σ Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest ++ tail))
          (mkApps (tConst c u) (map term_of_lit ls ++ b :: rest ++ tail)).
Proof.
  intros r. apply red_mkApps; [reflexivity|].
  apply All2_app; [apply All2_refl; reflexivity|].
  constructor; [exact r|apply All2_refl; reflexivity].
Qed.

(** [split_lits] on the first [n] arguments names the maximal literal prefix
    [ls] and the first non-literal [a]; the whole argument list is then that
    decomposition followed by the over-applied tail. *)
Lemma prim_args_eq {args n ls a rest} :
  split_lits (firstn n args) = inr (ls, a, rest) ->
  args = map term_of_lit ls ++ a :: rest ++ skipn n args.
Proof.
  intros hs.
  rewrite -{1}(firstn_skipn n args) (fst (split_lits_inr hs)) -app_assoc //.
Qed.

Lemma prim_args_eq_inl {args n ls} :
  split_lits (firstn n args) = inl ls ->
  args = map term_of_lit ls ++ skipn n args.
Proof.
  intros hs. rewrite -{1}(firstn_skipn n args) (split_lits_inl hs) //.
Qed.

(** Reducing the stuck argument [a] of a stuck operation application to a
    weak-head form [w] (still not a literal) leaves a term that is its own
    weak-head form: [split_lits] finds [w] at the same place, and the reconstructed
    argument list is the original one.  This is what [whd_rel_idem] needs. *)
Lemma whd_prim_stuck_result {n ls w R} :
  lit_of_term w = None -> #|ls| < n ->
  (split_lits (firstn n (map term_of_lit ls ++ w :: R)) = inr (ls, w, firstn (n - S #|ls|) R)) ×
  (map term_of_lit ls ++ w :: firstn (n - S #|ls|) R
     ++ skipn n (map term_of_lit ls ++ w :: R) = map term_of_lit ls ++ w :: R).
Proof.
  intros hw hlt.
  have hfa : firstn n (map term_of_lit ls ++ w :: R)
           = map term_of_lit ls ++ w :: firstn (n - S #|ls|) R.
  { rewrite firstn_app firstn_all2; [rewrite length_map; lia|].
    rewrite length_map.
    have -> : n - #|ls| = S (n - S #|ls|) by lia.
    reflexivity. }
  have hsk : skipn n (map term_of_lit ls ++ w :: R) = skipn (n - S #|ls|) R.
  { rewrite skipn_app skipn_all2; [rewrite length_map; lia|].
    rewrite length_map.
    have -> : n - #|ls| = S (n - S #|ls|) by lia.
    reflexivity. }
  split.
  - rewrite hfa. apply split_lits_app, hw.
  - rewrite hsk firstn_skipn //.
Qed.

Inductive arity_red (Σ : global_env) : context -> term -> context -> sort -> Type :=
| arity_red_sort Γ t s :
    whd_allnolet_rel Σ Γ t [] (tSort s) [] ->
    arity_red Σ Γ t [] s
| arity_red_prod Γ t na A B Δ s :
    whd_allnolet_rel Σ Γ t [] (tProd na A B) [] ->
    arity_red Σ (Γ ,, vass na A) B Δ s ->
    arity_red Σ Γ t (Δ ++ [vass na A]) s
| arity_red_let Γ t na b A B Δ s :
    whd_allnolet_rel Σ Γ t [] (tLetIn na b A B) [] ->
    arity_red Σ (Γ ,, vdef na b A) B Δ s ->
    arity_red Σ Γ t (Δ ++ [vdef na b A]) s
(** kernel/reduction.ml, [whd_decompose_prod_decls]: [whd_all] once, and
    recurse only if it made progress.  The kernel tests progress with
    [Constr.equal], which ignores binder names; [<>] here sees them.  The
    premise is redundant ([arity_red_fallback_progress] derives it from the
    others), so the difference has no effect. *)
| arity_red_fallback Γ t h l h' l' Δ s :
    whd_allnolet_rel Σ Γ t [] h l ->
    whd_arity_head h l = false ->
    whd_all_rel Σ Γ (mkApps h l) [] h' l' ->
    mkApps h' l' <> mkApps h l ->
    arity_red Σ Γ (mkApps h' l') Δ s ->
    arity_red Σ Γ t Δ s.

Derive Signature for arity_red.

(** The instance of [EnvironmentTyping.KernelRedSig] that [PCUICGlobalMaps]
    (in PCUICTyping) uses: [arity_red] for [on_ind_body]'s [ind_arity_red], and
    [whd_rel] for the reductions of strict positivity ([positive_cstr_arg]). *)
Module PCUICArityRelation <: EnvironmentTyping.KernelRedSig PCUICTerm PCUICEnvironment.
  Definition arity_red := arity_red.
  Definition whd_rel := whd_rel.
End PCUICArityRelation.

(** ** A derivation is a reduction *)

Section WhdRed.
  Context (Σ : global_env) (Γ : context).

  Lemma whd_All2_red_refl l : All2 (red Σ Γ) l l.
  Proof. induction l; constructor; try reflexivity; auto. Qed.

  Lemma whd_red_args args narg c c' :
    nth_error args narg = Some c ->
    red Σ Γ c c' ->
    All2 (red Σ Γ) args (firstn narg args ++ c' :: skipn (S narg) args).
  Proof.
    intros hn r. destruct (nth_error_split_firstn_skipn _ _ _ hn) as [e _].
    rewrite {1}e. apply All2_app; [apply whd_All2_red_refl|].
    constructor; [exact r|apply whd_All2_red_refl].
  Qed.

  Lemma whd_rel_red {zeta t args h l} :
    whd_rel zeta Σ Γ t args h l -> red Σ Γ (mkApps t args) (mkApps h l).
  Proof.
    induction 1 as [c args d b h l hn hb w IH|c args d hn hb
      |na b B t args h l hz w IH|na b B t args hz
      |c u decl body args h l hd hb w IH|c u decl args hd hb hpo
      |f a args h l w IH|na A t a args h l w IH
      |mfix idx narg fn args c ind n ui cargs h l hu hn w1 IH1 w2 IH2
      |mfix idx narg fn args c t cargs hu hn w IH hc
      |mfix idx narg fn args hu hn|mfix idx args hu
      |ci p c brs args n ui cargs br h l w1 IH1 hbr hlen w2 IH2
      |ci p c brs args mfix idx cargs narg fn h l w1 IH1 hu w2 IH2
      |ci p c brs args t cargs w IH hc hcf
      |p c args u cargs a h l w1 IH1 ha w2 IH2
      |p c args mfix idx cargs narg fn h l w1 IH1 hu w2 IH2
      |p c args t cargs w IH hc hcf
      |t args hs
      |c u decl op args ls a rest t cargs lit h l hlook hbod hpo hsat hs wa IHa hnl w IH
      |c u decl op args ls a rest t cargs hlook hbod hpo hsat hs wa IHa hnl
      |c u decl op args ls r v h l hlook hbod hpo hsat hs hden hback w IH
      |c u decl op args ls hlook hbod hpo hsat hs hden
      |c u decl op args hlook hbod hpo hpart].
    - eapply red_trans; [|exact IH].
      apply red_mkApps_f, red1_red, red_rel. now rewrite hn /= hb.
    - reflexivity.
    - eapply red_trans; [|exact IH]. apply red_mkApps_f, red1_red, red_zeta.
    - reflexivity.
    - eapply red_trans; [|exact IH]. apply red_mkApps_f, red1_red.
      eapply red_delta; [exact (lookup_global_Some_if_In _ _ _ hd)|exact hb].
    - reflexivity.
    - exact IH.
    - eapply red_trans; [|exact IH]. cbn. apply red_mkApps_f, red1_red, red_beta.
    - eapply red_trans; [|exact IH2].
      eapply red_trans.
      { apply red_mkApps; [reflexivity|]. eapply whd_red_args; [exact hn|exact IH1]. }
      apply red1_red. eapply red_fix; [exact hu|].
      destruct (nth_error_split_firstn_skipn _ _ _ hn) as [_ len].
      rewrite /is_constructor (nth_error_snoc _ _ _ _ (eq_sym len)) /isConstruct_app.
      now rewrite decompose_app_mkApps.
    - apply red_mkApps; [reflexivity|]. eapply whd_red_args; [exact hn|exact IH].
    - reflexivity.
    - reflexivity.
    - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
      eapply red_trans; [eapply red_case_c; exact IH1|].
      apply red1_red. now apply red_iota.
    - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
      eapply red_trans; [eapply red_case_c; exact IH1|].
      apply red1_red. eapply red_cofix_case; eauto.
    - apply red_mkApps_f. eapply red_case_c; exact IH.
    - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
      eapply red_trans; [eapply red_proj_c; exact IH1|].
      apply red1_red. now apply red_proj.
    - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
      eapply red_trans; [eapply red_proj_c; exact IH1|].
      apply red1_red. eapply red_cofix_proj; eauto.
    - apply red_mkApps_f. eapply red_proj_c; exact IH.
    - reflexivity.
    (* whd_prim_arg *)
    - eapply red_trans; [|exact IH].
      rewrite {1}(prim_args_eq hs). apply red_prim_arg_cong; exact IHa.
    (* whd_prim_stuck *)
    - rewrite {1}(prim_args_eq hs). apply red_prim_arg_cong; exact IHa.
    (* whd_prim_fire *)
    - eapply red_trans; [|exact IH].
      rewrite {1}(prim_args_eq_inl hs) mkApps_app.
      apply red_mkApps_f, red1_red.
      eapply red_prim_op;
        [exact hpo|exact (lookup_global_Some_if_In _ _ _ hlook)|exact hbod|exact hden|exact hback].
    (* whd_prim_inert *)
    - reflexivity.
    (* whd_prim_partial *)
    - reflexivity.
  Qed.
End WhdRed.

(** A derivation reads the context only through [nth_error] and [decl_body], so two
    contexts with pointwise equal bodies have the same derivations. *)
Lemma whd_rel_ctx_bodies {zeta Σ Γ Γ' t args h l} :
  All2 (fun d d' => decl_body d = decl_body d') Γ Γ' ->
  whd_rel zeta Σ Γ t args h l -> whd_rel zeta Σ Γ' t args h l.
Proof.
  intros a.
  induction 1;
    [ | | eapply whd_zeta | eapply whd_letin_stop
    | eapply whd_delta | eapply whd_axiom | eapply whd_app | eapply whd_beta
    | eapply whd_fix_iota | eapply whd_fix_stuck | eapply whd_fix_noarg | eapply whd_fix_nounfold
    | eapply whd_iota | eapply whd_case_cofix | eapply whd_case_stuck
    | eapply whd_proj | eapply whd_proj_cofix | eapply whd_proj_stuck | eapply whd_stop
    | eapply whd_prim_arg | eapply whd_prim_stuck | eapply whd_prim_fire
    | eapply whd_prim_inert | eapply whd_prim_partial ];
    eauto.
  - match goal with hn : nth_error Γ _ = Some _ |- _ =>
      destruct (All2_nth_error_Some _ _ a hn) as [d' [hn' hb']] end.
    eapply whd_rel_unfold; [exact hn'|rewrite -hb'; eassumption|eassumption].
  - match goal with hn : nth_error Γ _ = Some _ |- _ =>
      destruct (All2_nth_error_Some _ _ a hn) as [d' [hn' hb']] end.
    eapply whd_rel_assum; [exact hn'|rewrite -hb'; eassumption].
Qed.

Lemma assumption_context_decl_body {Γ c d} :
  assumption_context Γ -> nth_error Γ c = Some d -> decl_body d = None.
Proof.
  intros a; induction a in c |- *; destruct c; cbn; intros e; try discriminate.
  - injection e as <-. reflexivity.
  - exact (IHa _ e).
Qed.

(** In a context without bodies no variable is unfolded, and every other step of the
    machine reads no context: a derivation is a reduction in every context. *)
Lemma whd_rel_red_nobody {zeta Σ Γ t args h l} :
  assumption_context Γ ->
  whd_rel zeta Σ Γ t args h l -> forall Δ, red Σ Δ (mkApps t args) (mkApps h l).
Proof.
  intros ass w Δ.
  induction w as [c args d b h l hn hb w IH|c args d hn hb
    |na b B t args h l hz w IH|na b B t args hz
    |c u decl body args h l hd hb w IH|c u decl args hd hb hpo
    |f a args h l w IH|na A t a args h l w IH
    |mfix idx narg fn args c ind n ui cargs h l hu hn w1 IH1 w2 IH2
    |mfix idx narg fn args c t cargs hu hn w IH hc
    |mfix idx narg fn args hu hn|mfix idx args hu
    |ci p c brs args n ui cargs br h l w1 IH1 hbr hlen w2 IH2
    |ci p c brs args mfix idx cargs narg fn h l w1 IH1 hu w2 IH2
    |ci p c brs args t cargs w IH hc hcf
    |p c args u cargs a h l w1 IH1 ha w2 IH2
    |p c args mfix idx cargs narg fn h l w1 IH1 hu w2 IH2
    |p c args t cargs w IH hc hcf
    |t args hs
    |c u decl op args ls a rest t cargs lit h l hlook hbod hpo hsat hs wa IHa hnl w IH
    |c u decl op args ls a rest t cargs hlook hbod hpo hsat hs wa IHa hnl
    |c u decl op args ls r v h l hlook hbod hpo hsat hs hden hback w IH
    |c u decl op args ls hlook hbod hpo hsat hs hden
    |c u decl op args hlook hbod hpo hpart].
  - rewrite (assumption_context_decl_body ass hn) in hb. discriminate.
  - reflexivity.
  - eapply red_trans; [|exact IH]. apply red_mkApps_f, red1_red, red_zeta.
  - reflexivity.
  - eapply red_trans; [|exact IH]. apply red_mkApps_f, red1_red.
    eapply red_delta; [exact (lookup_global_Some_if_In _ _ _ hd)|exact hb].
  - reflexivity.
  - exact IH.
  - eapply red_trans; [|exact IH]. cbn. apply red_mkApps_f, red1_red, red_beta.
  - eapply red_trans; [|exact IH2].
    eapply red_trans.
    { apply red_mkApps; [reflexivity|]. eapply whd_red_args; [exact hn|exact IH1]. }
    apply red1_red. eapply red_fix; [exact hu|].
    destruct (nth_error_split_firstn_skipn _ _ _ hn) as [_ len].
    rewrite /is_constructor (nth_error_snoc _ _ _ _ (eq_sym len)) /isConstruct_app.
    now rewrite decompose_app_mkApps.
  - apply red_mkApps; [reflexivity|]. eapply whd_red_args; [exact hn|exact IH].
  - reflexivity.
  - reflexivity.
  - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
    eapply red_trans; [eapply red_case_c; exact IH1|].
    apply red1_red. now apply red_iota.
  - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
    eapply red_trans; [eapply red_case_c; exact IH1|].
    apply red1_red. eapply red_cofix_case; eauto.
  - apply red_mkApps_f. eapply red_case_c; exact IH.
  - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
    eapply red_trans; [eapply red_proj_c; exact IH1|].
    apply red1_red. now apply red_proj.
  - eapply red_trans; [|exact IH2]. apply red_mkApps_f.
    eapply red_trans; [eapply red_proj_c; exact IH1|].
    apply red1_red. eapply red_cofix_proj; eauto.
  - apply red_mkApps_f. eapply red_proj_c; exact IH.
  - reflexivity.
  (* whd_prim_arg *)
  - eapply red_trans; [|exact IH].
    rewrite {1}(prim_args_eq hs). apply red_prim_arg_cong; exact IHa.
  (* whd_prim_stuck *)
  - rewrite {1}(prim_args_eq hs). apply red_prim_arg_cong; exact IHa.
  (* whd_prim_fire *)
  - eapply red_trans; [|exact IH].
    rewrite {1}(prim_args_eq_inl hs) mkApps_app.
    apply red_mkApps_f, red1_red.
    eapply red_prim_op;
      [exact hpo|exact (lookup_global_Some_if_In _ _ _ hlook)|exact hbod|exact hden|exact hback].
  (* whd_prim_inert *)
  - reflexivity.
  (* whd_prim_partial *)
  - reflexivity.
Qed.

Lemma arity_red_red {Σ Γ t Δ s} :
  arity_red Σ Γ t Δ s -> red Σ Γ t (it_mkProd_or_LetIn Δ (tSort s)).
Proof.
  induction 1 as [Γ t s w|Γ t na A B Δ s w ar IH|Γ t na b A B Δ s w ar IH
    |Γ t h l h' l' Δ s w ha w' hne ar IH].
  - exact (whd_rel_red _ _ w).
  - rewrite it_mkProd_or_LetIn_app /=.
    eapply red_trans; [exact (whd_rel_red _ _ w)|].
    now apply red_prod_r.
  - rewrite it_mkProd_or_LetIn_app /=.
    eapply red_trans; [exact (whd_rel_red _ _ w)|].
    apply red_letin; [reflexivity|reflexivity|exact IH].
  - eapply red_trans; [exact (whd_rel_red _ _ w)|].
    eapply red_trans; [exact (whd_rel_red _ _ w')|].
    exact IH.
Qed.

(** The form [on_ind_body] uses: the user arity [U] in the parameter context. *)
Lemma arity_red_red_params {Σ params U Δ s} :
  arity_red Σ params U Δ s ->
  red Σ [] (it_mkProd_or_LetIn params U) (it_mkProd_or_LetIn (params ,,, Δ) (tSort s)).
Proof.
  intros ar. rewrite /app_context it_mkProd_or_LetIn_app.
  apply red_it_mkProd_or_LetIn.
  have e : [] ,,, params = params by rewrite /app_context app_nil_r.
  rewrite e. exact (arity_red_red ar).
Qed.

(** ** Determinism

  The checker computes the relation with the machine; determinism makes every
  comparison it does against the declaration coincide with any derivation. *)

Ltac whd_det_lookup :=
  match goal with
  | H : ?a = Some _, H' : ?a = Some _ |- _ => rewrite H in H'; noconf H'
  | H : ?a = Some _, H' : ?a = None |- _ => rewrite H in H'; discriminate
  | H : ?a = None, H' : ?a = Some _ |- _ => rewrite H in H'; discriminate
  | H : ?a = inl _, H' : ?a = inl _ |- _ => rewrite H in H'; noconf H'
  | H : ?a = inr _, H' : ?a = inr _ |- _ => rewrite H in H'; noconf H'
  | H : ?a = inl _, H' : ?a = inr _ |- _ => rewrite H in H'; discriminate
  | H : ?a = inr _, H' : ?a = inl _ |- _ => rewrite H in H'; discriminate
  | H : true = false |- _ => discriminate
  | H : false = true |- _ => discriminate
  | H : is_true (whd_stop_head _ _) |- _ =>
      unfold is_true in H; cbn in H; discriminate
  | H : whd_is_construct (tConstruct _ _ _) = false |- _ => discriminate
  | H : whd_is_construct0 (tConstruct _ 0 _) = false |- _ => discriminate
  | H : whd_is_cofix (tCoFix _ _) = false |- _ => discriminate
  end.

Ltac whd_det_ih :=
  match goal with
  | IH : forall h' l', whd_rel ?z ?Σ ?Γ ?t ?a h' l' -> (?h = h') × (?l = l'),
    H : whd_rel ?z ?Σ ?Γ ?t ?a _ _ |- _ =>
      let e := fresh "e" in let e' := fresh "e" in
      destruct (IH _ _ H) as [e e']; clear IH H; try noconf e; try subst
  end.

Lemma whd_rel_det {zeta Σ Γ t args h l h' l'} :
  whd_rel zeta Σ Γ t args h l -> whd_rel zeta Σ Γ t args h' l' -> (h = h') × (l = l').
Proof.
  intros d1. induction d1 in h', l' |- *; intros d2.
  (* [induction] keeps the premises next to their induction hypotheses: clear
     them, so that an hypothesis is only ever applied to a premise of [d2]. *)
  all: repeat match goal with
    | IH : forall h' l', whd_rel ?z ?S ?G ?t ?a h' l' -> (?h = h') × (?l = l'),
      H : whd_rel ?z ?S ?G ?t ?a ?h ?l |- _ => clear H
    end.
  all: depelim d2.
  all: repeat (whd_det_lookup || whd_det_ih).
  all: try (split; reflexivity).
  all: cbn in *; try discriminate; try congruence; try lia.
Qed.

Lemma arity_red_det {Σ Γ t Δ s Δ' s'} :
  arity_red Σ Γ t Δ s -> arity_red Σ Γ t Δ' s' -> (Δ = Δ') × (s = s').
Proof.
  intros d1. induction d1 in Δ', s' |- *; intros d2; depelim d2.
  all: repeat match goal with
    | H : whd_rel ?z ?Σ ?Γ ?t ?a _ _, H' : whd_rel ?z ?Σ ?Γ ?t ?a _ _ |- _ =>
        let e := fresh "e" in let e' := fresh "e" in
        destruct (whd_rel_det H H') as [e e']; clear H'; try noconf e; try subst
    end.
  all: cbn in *; try discriminate.
  - split; reflexivity.
  - destruct (IHd1 _ _ d2) as [-> ->]. split; reflexivity.
  - destruct (IHd1 _ _ d2) as [-> ->]. split; reflexivity.
  - destruct (IHd1 _ _ d2) as [-> ->]. split; reflexivity.
Qed.

(** ** Weak-head forms *)

Lemma whd_rel_mkApps {zeta Σ Γ f l args h l'} :
  whd_rel zeta Σ Γ f (l ++ args) h l' -> whd_rel zeta Σ Γ (mkApps f l) args h l'.
Proof.
  induction l as [|a l IHl] in f |- *; cbn; [auto|].
  intros w. apply IHl, whd_app, w.
Qed.

Lemma whd_rel_mkApps0 {zeta Σ Γ f l h l'} :
  whd_rel zeta Σ Γ f l h l' -> whd_rel zeta Σ Γ (mkApps f l) [] h l'.
Proof. intros w. apply whd_rel_mkApps. now rewrite app_nil_r. Qed.

Lemma whd_arity_head_mkApps h l : whd_arity_head h l = whd_arity_head (mkApps h l) [].
Proof.
  induction l as [|y l _] using rev_ind; [reflexivity|].
  rewrite mkApps_app /=. destruct l; cbn; destruct h; reflexivity.
Qed.

(** A weak-head form is its own weak-head form. *)
Lemma whd_rel_idem {zeta Σ Γ t args h l} :
  whd_rel zeta Σ Γ t args h l -> whd_rel zeta Σ Γ h l h l.
Proof.
  induction 1 as [c args d b h l hn hb w IH|c args d hn hb
      |na b B t args h l hz w IH|na b B t args hz
      |c u decl body args h l hd hb w IH|c u decl args hd hb hpo
      |f a args h l w IH|na A t a args h l w IH
      |mfix idx narg fn args c ind n ui cargs h l hu hn w1 IH1 w2 IH2
      |mfix idx narg fn args c t cargs hu hn w IH hc
      |mfix idx narg fn args hu hn|mfix idx args hu
      |ci p c brs args n ui cargs br h l w1 IH1 hbr hlen w2 IH2
      |ci p c brs args mfix idx cargs narg fn h l w1 IH1 hu w2 IH2
      |ci p c brs args t cargs w IH hc hcf
      |p c args u cargs a h l w1 IH1 ha w2 IH2
      |p c args mfix idx cargs narg fn h l w1 IH1 hu w2 IH2
      |p c args t cargs w IH hc hcf
      |t args hs
      |c u decl op args ls a rest t cargs lit h l hlook hbod hpo hsat hs wa IHa hnl w IH
      |c u decl op args ls a rest t cargs hlook hbod hpo hsat hs wa IHa hnl
      |c u decl op args ls r v h l hlook hbod hpo hsat hs hden hback w IH
      |c u decl op args ls hlook hbod hpo hsat hs hden
      |c u decl op args hlook hbod hpo hpart]; try assumption.
  - eapply whd_rel_assum; eassumption.
  - now apply whd_letin_stop.
  - eapply whd_axiom; eassumption.
  - destruct (nth_error_split_firstn_skipn _ _ _ hn) as [_ len].
    have hX := nth_error_snoc (firstn narg args) (mkApps t cargs) (skipn (S narg) args) narg
      (eq_sym len).
    pose proof (whd_fix_stuck zeta Σ Γ mfix idx narg fn _ (mkApps t cargs) t cargs
      hu hX (whd_rel_mkApps0 IH) hc) as X.
    now rewrite -(proj1 (nth_error_split_firstn_skipn _ _ _ hX)) in X.
  - eapply whd_fix_noarg; eassumption.
  - now apply whd_fix_nounfold.
  - eapply whd_case_stuck; [exact (whd_rel_mkApps0 IH)|exact hc|exact hcf].
  - eapply whd_proj_stuck; [exact (whd_rel_mkApps0 IH)|exact hc|exact hcf].
  - now apply whd_stop.
  (* whd_prim_stuck: the reduced stuck argument keeps the application stuck *)
  - have hfl : #|firstn (arity op) args| = arity op by rewrite length_firstn; lia.
    pose proof (split_lits_length_inr hs) as hlen; rewrite hfl in hlen.
    have hlt : #|ls| < arity op by lia.
    destruct (whd_prim_stuck_result (n := arity op) (w := mkApps t cargs)
                (R := rest ++ skipn (arity op) args) hnl hlt) as [hsp heq].
    rewrite -{2}heq.
    eapply whd_prim_stuck;
      [exact hlook|exact hbod|exact hpo| |exact hsp
      |exact (whd_rel_mkApps0 IHa)|exact hnl].
    rewrite length_app length_map /= length_app; lia.
  (* whd_prim_inert *)
  - eapply whd_prim_inert; eassumption.
  (* whd_prim_partial *)
  - eapply whd_prim_partial; eassumption.
Qed.

(** A non-arity weak-head form continues only through the [whd_all] fallback. *)
Lemma arity_red_whd_inv {Σ Γ t Δ s h l} :
  arity_red Σ Γ t Δ s ->
  whd_allnolet_rel Σ Γ t [] h l -> whd_arity_head h l = false ->
  ∑ h' l', whd_all_rel Σ Γ (mkApps h l) [] h' l' × (mkApps h' l' <> mkApps h l).
Proof.
  intros ar; revert h l; destruct ar as [Γ' t' s' w0|Γ' t' na A B Δ' s' w0 _
    |Γ' t' na b A B Δ' s' w0 _|Γ' t' h0 l0 h' l' Δ' s' w0 _ w1 hne _];
    intros h l w ha; destruct (whd_rel_det w w0) as [-> ->]; try (cbn in ha; discriminate).
  exists h', l'. split; assumption.
Qed.

(** The progress premise of [arity_red_fallback] follows from the others: a
    [whd_all] step that changed nothing would leave the same non-arity head,
    from which [arity_red] can only continue by a step that does change it. *)
Lemma arity_red_fallback_progress {Σ Γ t h l h' l' Δ s} :
  whd_allnolet_rel Σ Γ t [] h l -> whd_arity_head h l = false ->
  whd_all_rel Σ Γ (mkApps h l) [] h' l' ->
  arity_red Σ Γ (mkApps h' l') Δ s ->
  mkApps h' l' <> mkApps h l.
Proof.
  intros w ha w' ar e. rewrite e in ar.
  destruct (arity_red_whd_inv ar (whd_rel_mkApps0 (whd_rel_idem w)) ha) as [h2 [l2 [w2 hne2]]].
  destruct (whd_rel_det w2 w') as [e1 e2]; subst h2 l2.
  exact (hne2 e).
Qed.
