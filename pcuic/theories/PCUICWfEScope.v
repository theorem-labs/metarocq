(* Distributed under the terms of the MIT license. *)
(** * The comparisons made by [wfE] are between well-scoped pairs

  [wfE] is [on_global_env cumulSpecE0 (lift_typing typingE)]. Its comparison relation
  [Pcmp := cumulSpecE0] is read in exactly three places of [EnvironmentTyping]:

  - [ind_respects_variance] (field [onIndices] of [on_ind_body]). With [variance_universes]
    giving the doubled universe context [univs'] and the two instances [u], [u'], it is
    [cumul_ctx_rel Pcmp (Σ, univs') Γ Δ Δ'] with
    [Γ := (smash_context [] params)@[u]],
    [Δ := (expand_lets_ctx params (smash_context [] indices))@[u]] and [Δ'] the same at [u'].
    [cumul_ctx_rel] compares, for each position of [Δ], the declaration of [Δ] with the one
    of [Δ'] in the context [Γ ,,, Δ0], [Δ0] the part of [Δ] below that position: [Cumul] on
    the types and [Conv] on the bodies of local definitions.
  - [cstr_respects_variance] (field [on_ctype_variance] of [on_constructor]). The same
    [cumul_ctx_rel] on [(expand_lets_ctx params (smash_context [] args))@[u]] and [@[u']]
    over [(ind_arities mdecl ,,, smash_context [] params)@[u]]; and [Conv] between
    [(expand_lets (params ,,, args) i)@[u]] and the same at [u'], for each index [i] of the
    constructor, in [(ind_arities mdecl ,,, smash_context [] (params ,,, args))@[u]].
  - [prim_op_cst_type] (field of [on_prim_op_constant], read by [on_prim_decl]): [Conv]
    between the declared type [cst_type] and [prim_op_type] in the empty context.

  [cmp_scoped Pcmp] is [Pcmp] on scoped pairs only: the context is closed
  ([is_closed_context]) and both terms are open in it ([is_open_term]).

  - Each site with any [Pcmp] gives the same site with [cmp_scoped Pcmp]:
    [ind_respects_variance_scoped], [cstr_respects_variance_scoped],
    [prim_op_cst_type_scoped] (and [cumul_ctx_rel_scoped], the common step). Their premises
    are the closedness of the declaration parts the site reads, and nothing else (no
    typing, no environment): [closed_ctx (params ,,, indices)]; [closed_ctx params],
    [closed_ctx (arities_context bodies)] and [closed_constructor_body]; [closed cst_type].
    [prim_op_type] is closed whatever the operation ([prim_op_type_closed]).
  - In a [wfE] environment: [ind_respects_varianceE_scoped] (a declared inductive with a
    variance), [cstr_respects_varianceE_scoped] (a declared constructor of one) and
    [prim_op_cst_typeE_scoped] (a declared constant registered as a primitive operation)
    return a [wfE] prefix [Σ'] of [Σ] at which the check holds with
    [cmp_scoped cumulSpecE0]. [Σ'] and the check are the ones [lookup_on_global_env]
    ([lookup_on_global_env_prim]) extracts from [wfE Σ]: the prefix at which [wfE] made the
    check. The closedness comes from [wfE] through
    [declared_inductive_closed_pars_indicesE], [declared_minductive_closedE],
    [declared_constructor_closedE] and [declared_constant_closed_typeE]; [ClosedBodies]
    alone does not give it (it states only the closedness of constant bodies).
  - [wfE_scoped]: [wfE Σ] gives [on_global_env (cmp_scoped cumulSpecE0) (lift_typing typingE) Σ].
    Every field other than the three sites is carried over unchanged, so every comparison
    [wfE] makes is between scoped pairs.

  Satisfying instances (section [Instances]):
  - [ws_env] declares [K@{u} : Type@{u} -> Prop] with one constructor
    [k : forall X : Type@{u}, K X] and the variance [Covariant] for [u]; it is proved [wf]
    ([ws_wf]), hence [wfE] ([ws_wfE]). Its variance checks compare [Type@{u1} ≤ Type@{u0}]
    under the constraint [u1 ≤ u0] that the variance adds, in the empty context
    (indices) and in [K : Type@{u1} -> Prop] (constructor argument), and the index [X] of
    the constructor, [tRel 0], with itself in [K : Type@{u1} -> Prop, X : Type@{u1}].
    [ind_respects_varianceE_scoped_inst] and [cstr_respects_varianceE_scoped_inst] apply
    the lemmas there; [ws_ind_pair_scoped] and [ws_cstr_index_scoped] read the compared
    pairs back out of their conclusions.
  - [Σ_po0] ([PCUICEtaPrimOpInstance]) registers [land : int -> int -> int] as the
    operation [Int63land]; it is proved [wf] here ([po_wf], the unsquashed proof of
    [Σ_po_wf]), hence [wfE] ([po_wfE]). [prim_op_cst_typeE_scoped_inst] applies the lemma
    to [land]. [ws_wfE_scoped_inst] and [po_wfE_scoped_inst] apply [wfE_scoped] to both
    environments. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Kernames Environment EnvironmentTyping
     Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICClosed
     PCUICOnFreeVars PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta
     PCUICArityRed PCUICWfUniverses PCUICClosedTypEta PCUICEtaPrimOpInstance.

Implicit Types (cf : checker_flags).

(** ** Comparisons restricted to scoped pairs *)

Definition cmp_scoped (Pcmp : global_env_ext -> context -> conv_pb -> term -> term -> Type)
  : global_env_ext -> context -> conv_pb -> term -> term -> Type :=
  fun Σ Γ pb t u => [× Pcmp Σ Γ pb t u, is_closed_context Γ, is_open_term Γ t & is_open_term Γ u].

Lemma closedn_is_open_term_app {Γ Δ : context} {t} :
  closedn (#|Γ| + #|Δ|) t -> is_open_term (Γ ,,, Δ) t.
Proof. intros h. by rewrite -is_open_term_closedE app_context_length Nat.add_comm. Qed.

Lemma closedn_is_closed_context_app {Γ Δ : context} :
  closed_ctx Γ -> closedn_ctx #|Γ| Δ -> is_closed_context (Γ ,,, Δ).
Proof.
  intros h h'. rewrite -is_closed_ctx_closedE closedn_ctx_app. apply/andP; split; [exact h|exact h'].
Qed.

(** [cumul_ctx_rel] compares only scoped pairs when its base context is closed and both
    related contexts are closed over it. *)
Lemma cumul_ctx_rel_scoped {Pcmp Σ Γ Δ Δ'} :
  closed_ctx Γ -> closedn_ctx #|Γ| Δ -> closedn_ctx #|Γ| Δ' ->
  cumul_ctx_rel Pcmp Σ Γ Δ Δ' -> cumul_ctx_rel (cmp_scoped Pcmp) Σ Γ Δ Δ'.
Proof.
  intros clΓ clΔ clΔ' h. unfold cumul_ctx_rel, cumul_pb_decls in *.
  induction h as [|d d' Δ0 Δ0' h IH hd] in clΔ, clΔ' |- *; [constructor|].
  move: clΔ clΔ'; rewrite !closedn_ctx_cons => /andP[clΔ0 cld] /andP[clΔ0' cld'].
  have hlen : #|Δ0| = #|Δ0'| := All2_fold_length h.
  have hctx : is_closed_context (Γ ,,, Δ0) := closedn_is_closed_context_app clΓ clΔ0.
  constructor; [exact (IH clΔ0 clΔ0')|].
  destruct hd as [na na' t t' eqna eqt|na na' b t b' t' eqna eqb eqt].
  - rewrite /test_decl /= in cld cld'.
    constructor; [exact eqna|].
    split; [exact eqt|exact hctx|exact (closedn_is_open_term_app cld)|].
    apply closedn_is_open_term_app. rewrite hlen. exact cld'.
  - rewrite /test_decl /= in cld cld'.
    move/andP: cld => [clb clt]. move/andP: cld' => [clb' clt'].
    constructor; [exact eqna| |].
    + split; [exact eqb|exact hctx|exact (closedn_is_open_term_app clb)|].
      apply closedn_is_open_term_app. rewrite hlen. exact clb'.
    + split; [exact eqt|exact hctx|exact (closedn_is_open_term_app clt)|].
      apply closedn_is_open_term_app. rewrite hlen. exact clt'.
Qed.

(** *** The variance check of an inductive *)

Lemma ind_respects_variance_scoped {Pcmp Σ mdecl v indices} :
  closed_ctx (ind_params mdecl ,,, indices) ->
  ind_respects_variance Pcmp Σ mdecl v indices ->
  ind_respects_variance (cmp_scoped Pcmp) Σ mdecl v indices.
Proof.
  rewrite closedn_ctx_app => /andP[clpars clinds].
  rewrite /ind_respects_variance.
  destruct variance_universes as [[[univs u] u']|]; [|easy].
  have clΔ : forall u0,
      closedn_ctx #|(smash_context [] (ind_params mdecl))@[u]|
        (expand_lets_ctx (ind_params mdecl) (smash_context [] indices))@[u0].
  { intros u0. rewrite closedn_subst_instance_context subst_instance_length smash_context_length /=.
    apply (closedn_ctx_expand_lets 0); [exact clpars|].
    apply closedn_smash_context. exact clinds. }
  apply cumul_ctx_rel_scoped; [|exact (clΔ u)|exact (clΔ u')].
  rewrite closedn_subst_instance_context. apply closedn_smash_context. exact clpars.
Qed.

(** *** The variance check of a constructor *)

Lemma closed_inductive_decl_arities {mdecl} :
  closed_inductive_decl mdecl -> closed_ctx (arities_context (ind_bodies mdecl)).
Proof.
  rewrite /closed_inductive_decl => /andP[] _ clbs.
  induction (ind_bodies mdecl) => //.
  rewrite /arities_context /= rev_map_spec /=.
  move: clbs; simpl. move=> /andP[] cla clbs.
  rewrite closedn_ctx_app /=. apply/andP; split; auto.
  rewrite /test_decl /=. now move/andP: cla => [] /andP[] /andP[].
  eapply closedn_ctx_upwards. rewrite -rev_map_spec. eapply IHl => //. lia.
Qed.

Lemma cstr_respects_variance_scoped {Pcmp Σ mdecl v cs} :
  closed_ctx (ind_params mdecl) ->
  closed_ctx (arities_context (ind_bodies mdecl)) ->
  closed_constructor_body mdecl cs ->
  cstr_respects_variance Pcmp Σ mdecl v cs ->
  cstr_respects_variance (cmp_scoped Pcmp) Σ mdecl v cs.
Proof.
  intros clpars clar.
  rewrite /closed_constructor_body => /andP[/andP[clargs clinds] _].
  have clparsB : closedn_ctx #|ind_bodies mdecl| (ind_params mdecl).
  { eapply closedn_ctx_upwards; [exact clpars|lia]. }
  rewrite /cstr_respects_variance.
  destruct variance_universes as [[[univs u] u']|]; [|easy].
  intros [hargs hinds]. split.
  - have e1 : #|(ind_arities mdecl ,,, smash_context [] (ind_params mdecl))@[u]| =
        #|ind_bodies mdecl| + context_assumptions (ind_params mdecl).
    { rewrite subst_instance_length app_context_length smash_context_length /ind_arities
        arities_context_length. cbn [length]. lia. }
    have clΔ : forall u0,
        closedn_ctx #|(ind_arities mdecl ,,, smash_context [] (ind_params mdecl))@[u]|
          (expand_lets_ctx (ind_params mdecl) (smash_context [] (cstr_args cs)))@[u0].
    { intros u0. rewrite closedn_subst_instance_context e1.
      apply closedn_ctx_expand_lets; [exact clparsB|].
      apply closedn_smash_context. exact clargs. }
    apply cumul_ctx_rel_scoped; [|exact (clΔ u)|exact (clΔ u')|exact hargs].
    rewrite closedn_subst_instance_context closedn_ctx_app. apply/andP; split; [exact clar|].
    rewrite /ind_arities arities_context_length.
    apply closedn_smash_context. exact clparsB.
  - set (Γ2 := (ind_arities mdecl ,,, smash_context [] (ind_params mdecl ,,, cstr_args cs))@[u]).
    have clΓ2 : is_closed_context Γ2.
    { rewrite /Γ2 -is_closed_ctx_closedE closedn_subst_instance_context closedn_ctx_app.
      apply/andP; split; [exact clar|].
      rewrite /ind_arities arities_context_length.
      apply closedn_smash_context. rewrite closedn_ctx_app. apply/andP; split; [exact clparsB|].
      exact clargs. }
    have clt : forall u0 t, closedn (#|ind_bodies mdecl| + #|ind_params mdecl| + #|cstr_args cs|) t ->
        is_open_term Γ2 (subst_instance u0 (expand_lets (ind_params mdecl ,,, cstr_args cs) t)).
    { intros u0 t ht.
      have e2 : #|Γ2| = #|ind_bodies mdecl| + 0 + context_assumptions (ind_params mdecl ,,, cstr_args cs).
      { rewrite /Γ2 subst_instance_length app_context_length smash_context_length /ind_arities
          arities_context_length. cbn [length]. lia. }
      have ht' : closedn (#|ind_bodies mdecl| + 0 + context_assumptions (ind_params mdecl ,,, cstr_args cs))
          (expand_lets_k (ind_params mdecl ,,, cstr_args cs) 0 t).
      { have cl2 : closedn_ctx #|ind_bodies mdecl| (ind_params mdecl ,,, cstr_args cs).
        { rewrite closedn_ctx_app. apply/andP; split; [exact clparsB|exact clargs]. }
        rewrite (closedn_expand_lets_eq #|ind_bodies mdecl| (ind_params mdecl ,,, cstr_args cs) 0 t cl2).
        rewrite app_context_length.
        replace (#|ind_bodies mdecl| + 0 + (#|cstr_args cs| + #|ind_params mdecl|))
          with (#|ind_bodies mdecl| + #|ind_params mdecl| + #|cstr_args cs|) by lia.
        exact ht. }
      rewrite -is_open_term_closedE closedn_subst_instance e2. exact ht'. }
    move/forallb_All: clinds => clinds.
    apply All2_map. apply All2_map_inv in hinds.
    eapply All2_impl; [exact (All2_All_mix_right clinds (All2_All_mix_left clinds hinds))|].
    intros t t' [[ht h] ht'].
    split; [exact h|exact clΓ2|exact (clt u t ht)|exact (clt u' t' ht')].
Qed.

(** *** The declared type of a primitive operation *)

Lemma prim_arg_types_closed {r tags res T} :
  PCUICPrimOpType.prim_arg_types r tags res = Some T -> closed res -> closed T.
Proof.
  induction tags as [|t tags ih] in T |- *; cbn; intros h hcl.
  - injection h as <-. exact hcl.
  - destruct (PCUICPrimOpType.prim_tag_type r t) as [a|] eqn:ht => //.
    destruct (PCUICPrimOpType.prim_arg_types r tags res) as [rest|] eqn:hr => //.
    cbn in h. injection h as <-.
    unfold PCUICPrimOpType.prim_tag_type in ht.
    destruct (EnvironmentTyping.retro_type_constant r t) => //. cbn in ht. injection ht as <-.
    rewrite /tImpl /=. now eapply (closedn_lift 1 0 0), ih.
Qed.

(** [prim_op_type] builds only [tImpl], [tConst kn []] and [tInd i []]. *)
Lemma prim_op_type_closed {r op T} :
  PCUICPrimOpType.prim_op_type r op = Some T -> closed T.
Proof.
  rewrite /PCUICPrimOpType.prim_op_type.
  destruct (PCUICPrimOpType.prim_shape_type r (po_shape (info op))) as [res|] eqn:hs => //.
  intros h. apply (prim_arg_types_closed h).
  destruct (po_shape (info op)); cbn in hs.
  - unfold PCUICPrimOpType.prim_tag_type in hs.
    destruct (EnvironmentTyping.retro_type_constant r primInt) => //. cbn in hs. now injection hs as <-.
  - destruct (Retroknowledge.retro_bool r) => //. cbn in hs. now injection hs as <-.
Qed.

Lemma prim_op_cst_type_scoped {Pcmp Σ op cb} :
  closed cb.(cst_type) ->
  on_prim_op_constant Pcmp Σ op cb -> on_prim_op_constant (cmp_scoped Pcmp) Σ op cb.
Proof.
  intros cl [hb hu [T [hT hc]] ha hr]. constructor; [exact hb|exact hu| |exact ha|exact hr].
  exists T. split; [exact hT|].
  split; [exact hc|reflexivity| |].
  - by rewrite -is_open_term_closedE.
  - rewrite -is_open_term_closedE. exact (prim_op_type_closed hT).
Qed.

(** ** In a [wfE] environment *)

Section WfE.
  Context {cf : checker_flags}.

  Lemma ind_respects_varianceE_scoped {Σ : global_env} {wfΣ : wfE Σ} {ind mdecl idecl v} :
    declared_inductive Σ ind mdecl idecl ->
    ind_variance mdecl = Some v ->
    ∑ Σ' : global_env_ext,
      [× wfE Σ'.1, strictly_extends_decls Σ'.1 Σ &
         ind_respects_variance (cmp_scoped cumulSpecE0) Σ'.1 mdecl v (ind_indices idecl)].
  Proof.
    intros hd hv.
    have cl := declared_inductive_closed_pars_indicesE (wfΣ := wfΣ) hd.
    destruct hd as [hm hi].
    have hm' := declared_minductive_to_gen (wfΣ := wfΣ) hm.
    destruct (lookup_on_global_env wfΣ hm') as (Σ' & wfΣ' & ext & ond).
    exists Σ'. split; [exact wfΣ'|exact ext|]. hnf in ond.
    have oib := Alli_nth_error _ _ _ _ _ _ ond.(onInductives) hi.
    have h := oib.(onIndices). rewrite hv in h.
    exact (ind_respects_variance_scoped cl h).
  Qed.

  Lemma cstr_respects_varianceE_scoped {Σ : global_env} {wfΣ : wfE Σ} {c mdecl idecl cdecl v} :
    declared_constructor Σ c mdecl idecl cdecl ->
    ind_variance mdecl = Some v ->
    ∑ Σ' : global_env_ext,
      [× wfE Σ'.1, strictly_extends_decls Σ'.1 Σ &
         cstr_respects_variance (cmp_scoped cumulSpecE0) Σ'.1 mdecl v cdecl].
  Proof.
    intros hc hv.
    have clpars : closed_ctx (ind_params mdecl).
    { move: (declared_inductive_closed_pars_indicesE (wfΣ := wfΣ) (proj1 hc)).
      by rewrite closedn_ctx_app => /andP[]. }
    have clar := closed_inductive_decl_arities (declared_minductive_closedE (wfΣ := wfΣ) (proj1 (proj1 hc))).
    have clcs := declared_constructor_closedE (wfΣ := wfΣ) hc.
    destruct hc as [[hm hi] hn].
    have hm' := declared_minductive_to_gen (wfΣ := wfΣ) hm.
    destruct (lookup_on_global_env wfΣ hm') as (Σ' & wfΣ' & ext & ond).
    exists Σ'. split; [exact wfΣ'|exact ext|]. hnf in ond.
    have oib := Alli_nth_error _ _ _ _ _ _ ond.(onInductives) hi.
    destruct (All2_nth_error_Some _ _ oib.(onConstructors) hn) as (cs & _ & oc).
    exact (cstr_respects_variance_scoped clpars clar clcs (oc.(on_ctype_variance) v hv)).
  Qed.

  Lemma prim_op_cst_typeE_scoped {Σ : global_env} {wfΣ : wfE Σ} {kn cb op} :
    declared_constant Σ kn cb ->
    prim_op_of Σ kn = Some op ->
    ∑ Σ' : global_env_ext,
      [× wfE Σ'.1, strictly_extends_decls Σ'.1 Σ &
         ∑ T, PCUICPrimOpType.prim_op_type Σ'.1.(retroknowledge) op = Some T ×
              cmp_scoped cumulSpecE0 Σ' [] Conv cb.(cst_type) T].
  Proof.
    intros hd hop.
    have cl := declared_constant_closed_typeE (wfΣ := wfΣ) hd.
    have hd' := declared_constant_to_gen (wfΣ := wfΣ) hd.
    destruct (lookup_on_global_env_prim wfΣ hd') as (Σ' & [wfΣ' ext hretro hpd]).
    exists Σ'. split; [exact wfΣ'|exact ext|].
    have hop' : prim_op_of Σ'.1 kn = Some op.
    { rewrite /prim_op_of hretro. exact hop. }
    destruct (prim_op_cst_type_scoped cl (hpd op hop')) as [_ _ hT _ _].
    exact hT.
  Qed.

  (** *** Every comparison of [wfE] *)

  Lemma on_inductive_scoped {Pcmp P Σ kn mdecl} :
    closed_inductive_decl mdecl ->
    on_inductive Pcmp P Σ kn mdecl -> on_inductive (cmp_scoped Pcmp) P Σ kn mdecl.
  Proof.
    intros cl [onI onP onNP onV].
    have clar := closed_inductive_decl_arities cl.
    move: cl; rewrite /closed_inductive_decl => /andP[clpars clbodies].
    constructor; [|exact onP|exact onNP|exact onV].
    eapply Alli_impl; [exact (Alli_All_mix _ _ _ onI (forallb_All _ _ clbodies))|].
    intros i idecl [oib clib].
    move: clib; rewrite /closed_inductive_body => /andP[/andP[/andP[_ clind] clctors] _].
    refine {| ind_arity_red := oib.(ind_arity_red); ind_cunivs := oib.(ind_cunivs) |}.
    - exact oib.(onArity).
    - exact oib.(onArityRed).
    - eapply All2_impl; [exact (All2_All_mix_left (forallb_All _ _ clctors) oib.(onConstructors))|].
      intros cdecl cs [clcs oc].
      destruct oc as [h1 h2 h3 h4 h5 h6 hvar h8].
      constructor; [exact h1|exact h2|exact h3|exact h4|exact h5|exact h6| |exact h8].
      intros v hv. exact (cstr_respects_variance_scoped clpars clar clcs (hvar v hv)).
    - exact oib.(onProjections).
    - exact oib.(ind_sorts).
    - exact oib.(ind_relevance_compat).
    - have h := oib.(onIndices). destruct ind_variance as [v|]; [|exact I].
      apply ind_respects_variance_scoped; [|exact h].
      rewrite closedn_ctx_app. apply/andP; split; [exact clpars|exact clind].
  Qed.

  Lemma on_prim_decl_scoped {Pcmp Σ kn d} :
    (match d with ConstantDecl cb => closed cb.(cst_type) | InductiveDecl _ => true end) ->
    on_prim_decl Pcmp Σ kn d -> on_prim_decl (cmp_scoped Pcmp) Σ kn d.
  Proof.
    destruct d as [cb|mdecl]; cbn; [|intros _ h; exact h].
    intros cl h op hop. exact (prim_op_cst_type_scoped cl (h op hop)).
  Qed.

  Theorem wfE_scoped {Σ : global_env} :
    wfE Σ -> on_global_env (cmp_scoped cumulSpecE0) (lift_typing typingE) Σ.
  Proof.
    destruct Σ as [univs decls retro].
    intros [cu [wfr ond]]; cbn in *.
    split; [exact cu|split; [exact wfr|]]. cbn.
    induction ond as [|decls kn d ond IH data]; [constructor|].
    constructor; [exact IH|].
    set (Σ1 := {| universes := univs; declarations := (kn, d) :: decls; retroknowledge := retro |}).
    have wf1 : wfE Σ1.
    { split; [exact cu|]. split; [exact wfr|]. cbn. apply globenv_decl; [exact ond|exact data]. }
    destruct data as [fresh udecl onud ondecl onprim].
    constructor; [exact fresh|exact onud| |].
    - destruct d as [cb|mdecl]; cbn in ondecl |- *; [exact ondecl|].
      apply on_inductive_scoped; [|exact ondecl].
      apply (declared_minductive_closedE (Σ := Σ1) (wfΣ := wf1) (mind := kn)). now left.
    - apply on_prim_decl_scoped; [|exact onprim].
      destruct d as [cb|mdecl]; [|reflexivity].
      apply (declared_constant_closed_typeE (Σ := Σ1) (wfΣ := wf1) (cst := kn)). now left.
  Qed.

End WfE.

(** ** Satisfying instances *)

Section Instances.

#[local] Existing Instance default_checker_flags.

(** [Inductive K@{u} : Type@{u} -> Prop := k : forall X : Type@{u}, K X], with the
    variance [Covariant] for [u]: one index, one constructor with one argument and one
    index, so both variance checks compare pairs. *)
Definition ws_kn : kername := (MPfile ["PCUICWfEScope"; "PCUIC"; "MetaRocq"], "K").
Definition ws_ind : inductive := {| inductive_mind := ws_kn; inductive_ind := 0 |}.
Definition ws_na : aname := mkBindAnn nAnon Relevant.
Definition ws_u : sort := sType (Universe.make' (Level.lvar 0)).
Definition ws_TU : term := tSort ws_u.
Definition ws_arity : term := tProd ws_na ws_TU (tSort sProp).
Definition ws_cstr_ty : term := tProd ws_na ws_TU (tApp (tRel 1) (tRel 0)).

Definition ws_cdecl : constructor_body :=
  {| cstr_name := "k"; cstr_args := [vass ws_na ws_TU]; cstr_indices := [tRel 0];
     cstr_type := ws_cstr_ty; cstr_arity := 1 |}.

Definition ws_idecl : one_inductive_body :=
  {| ind_name := "K"; ind_indices := [vass ws_na ws_TU]; ind_sort := sProp; ind_type := ws_arity;
     ind_kelim := IntoPropSProp; ind_ctors := [ws_cdecl]; ind_projs := []; ind_relevance := Relevant |}.

Definition ws_univs : universes_decl := Polymorphic_ctx ([nAnon], ConstraintSet.empty).

Definition ws_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 0; ind_params := []; ind_bodies := [ws_idecl];
     ind_universes := ws_univs; ind_variance := Some [Variance.Covariant] |}.

Definition ws_env : global_env :=
  {| universes := ContextSet.empty; declarations := [(ws_kn, InductiveDecl ws_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

(** The declaration is checked in the empty environment, at its own universes. *)
Definition ws_Σ0 : global_env_ext :=
  (mk_global_env ContextSet.empty [] Retroknowledge.empty, ws_univs).

Definition ws_val : valuation := {| valuation_mono := fun _ => 1%positive; valuation_poly := fun n => n |}.

Lemma ws_vass (Γ : context) (na : aname) A s :
  ws_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typing ws_Σ0 Γ (j_vass na A).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

Lemma ws_vass_s (Γ : context) (na : aname) A s :
  ws_Σ0 ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
  lift_typing typing ws_Σ0 Γ (j_vass_s na A s).
Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

Lemma ws_u_wf : wf_sort ws_Σ0 ws_u.
Proof. apply/wf_sort_reflect. reflexivity. Qed.

Lemma ws_TU_typed (Γ : context) : wf_local ws_Σ0 Γ -> ws_Σ0 ;;; Γ |- ws_TU : tSort (Sort.super ws_u).
Proof. intros h. apply type_Sort; [exact h|exact ws_u_wf]. Qed.

Lemma ws_wf_TU (Γ : context) : wf_local ws_Σ0 Γ -> wf_local ws_Σ0 (Γ ,, vass ws_na ws_TU).
Proof.
  intros h. apply localenv_cons_abs; [exact h|].
  exact (ws_vass _ ws_na _ _ (ws_TU_typed Γ h) eq_refl).
Qed.

Lemma ws_arity_typed (Γ : context) : wf_local ws_Σ0 Γ ->
  ws_Σ0 ;;; Γ |- ws_arity : tSort (Sort.sort_of_product (Sort.super ws_u) (Sort.super sProp)).
Proof.
  intros h. apply type_Prod.
  - exact (ws_vass_s _ ws_na _ _ (ws_TU_typed Γ h) eq_refl).
  - apply type_Sort; [exact (ws_wf_TU Γ h)|cbn; trivial].
Qed.

Definition ws_ar : context := arities_context (ind_bodies ws_mdecl).

Lemma ws_ar_eq : ws_ar = [vass (mkBindAnn (nNamed "K") rel_of_Type) ws_arity].
Proof. reflexivity. Qed.

Lemma ws_wf_ar : wf_local ws_Σ0 ws_ar.
Proof.
  rewrite ws_ar_eq. apply localenv_cons_abs; [constructor|].
  exact (ws_vass _ (mkBindAnn (nNamed "K") rel_of_Type) _ _ (ws_arity_typed [] localenv_nil) eq_refl).
Qed.

Lemma ws_concl_typed :
  ws_Σ0 ;;; ws_ar ,, vass ws_na ws_TU |- tApp (tRel 1) (tRel 0) : tSort sProp.
Proof.
  have w := ws_wf_TU _ ws_wf_ar.
  change (tSort sProp) with ((tSort sProp) {0 := tRel 0}).
  eapply type_App with (na := ws_na) (A := ws_TU) (B := tSort sProp).
  - exact (ws_arity_typed _ w).
  - exact (type_Rel _ _ 1 _ w eq_refl).
  - exact (type_Rel _ _ 0 _ w eq_refl).
Qed.

Lemma ws_cstr_typed :
  ws_Σ0 ;;; ws_ar |- ws_cstr_ty : tSort (Sort.sort_of_product (Sort.super ws_u) sProp).
Proof.
  apply type_Prod; [exact (ws_vass_s _ ws_na _ _ (ws_TU_typed _ ws_wf_ar) eq_refl)|exact ws_concl_typed].
Qed.

(** The constraint the variance [Covariant] adds, [lvar 1 ≤ lvar 0], makes
    [Type@{lvar 1} ≤ Type@{lvar 0}] in the doubled universe context. *)
Lemma ws_leq (Γ : context) :
  match variance_universes ws_univs [Variance.Covariant] with
  | Some (univs', u, u') => cumulSpec0 (ws_Σ0.1, univs') Γ Cumul (tSort ws_u@[u]) (tSort ws_u@[u'])
  | None => False
  end.
Proof.
  cbn. apply cumul_Sort. cbn. intros v hv.
  have hin : ConstraintSet.In (Level.lvar 1, ConstraintType.Le 0, Level.lvar 0)
      (global_ext_constraints (ws_Σ0.1, Polymorphic_ctx ([nAnon; nAnon],
         ConstraintSet.union (ConstraintSet.union ConstraintSet.empty (lift_constraints 1 ConstraintSet.empty))
           (variance_cstrs [Variance.Covariant] [Level.lvar 1] [Level.lvar 0])))).
  { apply ConstraintSet.mem_spec. vm_compute. reflexivity. }
  specialize (hv _ hin). inversion hv; subst. cbn in *. lia.
Qed.

Lemma ws_on_constructor :
  on_constructor cumulSpec0 (lift_typing typing) ws_Σ0 ws_mdecl 0 ws_idecl (ind_indices ws_idecl)
    ws_cdecl [Sort.super ws_u].
Proof.
  have w := ws_wf_TU _ ws_wf_ar.
  constructor.
  - reflexivity.
  - reflexivity.
  - exact (ws_vass _ (mkBindAnn nAnon Relevant) _ _ ws_cstr_typed eq_refl).
  - split; [exact tt|]. exact (ws_vass_s _ ws_na _ _ (ws_TU_typed _ ws_wf_ar) eq_refl).
  - cbn. econstructor; [|constructor].
    split; [exact (type_Rel _ _ 0 _ w eq_refl)|].
    exists (Sort.super ws_u). split; [exact (ws_TU_typed _ w)|]. split; exact I.
  - apply pos_ass.
    + apply pos_arg_closed. reflexivity.
    + refine (pos_concl _ _ _ _ [tRel 0] _). constructor; [reflexivity|constructor].
  - intros v [= <-]. cbn. split.
    + constructor; [constructor|]. constructor; [reflexivity|]. exact (ws_leq _).
    + constructor; [apply cumul_Refl|constructor].
  - exact I.
Qed.

Lemma ws_on_ind_body :
  on_ind_body cumulSpec0 (lift_typing typing) ws_Σ0 ws_kn ws_mdecl 0 ws_idecl.
Proof.
  unshelve econstructor.
  - exact [[Sort.super ws_u]].
  - exists ws_arity. split; [reflexivity|].
    apply (arity_red_prod _ _ _ ws_na ws_TU (tSort sProp) []); [apply whd_stop; reflexivity|].
    apply arity_red_sort. apply whd_stop. reflexivity.
  - exact (ws_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (ws_arity_typed [] localenv_nil) eq_refl).
  - exact (ws_vass _ (mkBindAnn nAnon rel_of_Type) _ _ (ws_arity_typed [] localenv_nil) eq_refl).
  - constructor; [exact ws_on_constructor|constructor].
  - exact I.
  - reflexivity.
  - reflexivity.
  - cbn. constructor; [constructor|]. constructor; [reflexivity|]. exact (ws_leq _).
Qed.

Lemma ws_on_inductive : on_inductive cumulSpec0 (lift_typing typing) ws_Σ0 ws_kn ws_mdecl.
Proof.
  constructor.
  - constructor; [exact ws_on_ind_body|constructor].
  - constructor.
  - reflexivity.
  - cbn. eexists; eexists; eexists. split.
    + reflexivity.
    + split; [reflexivity|split; [reflexivity|]].
      unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
      vm_compute in Hc. inversion Hc.
    + split; [reflexivity|split; [reflexivity|]].
      unfold valid_constraints; cbn. intros v _ c Hc. exfalso.
      vm_compute in Hc. inversion Hc.
    + reflexivity.
Qed.

Lemma ws_on_udecl : on_udecl ContextSet.empty ws_univs.
Proof.
  split; [|split; [|split]].
  - intros x Hx H. apply LevelSet.union_spec in H as [H|H].
    + eapply LevelSet.empty_spec. exact H.
    + apply LevelSet.singleton_spec in H. hnf in H. subst x.
      apply LevelSet.mem_spec in Hx. vm_compute in Hx. discriminate Hx.
  - intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - exists ws_val. intros x Hx. exfalso.
    apply ConstraintSet.union_spec in Hx as [Hx|Hx]; eapply ConstraintSet.empty_spec; exact Hx.
  - intros v hv. exists v. split.
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx. reflexivity.
Qed.

Lemma ws_wf : wf ws_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                            (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx].
      * exfalso. eapply LevelSet.empty_spec. exact Hx.
      * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
    + exists ws_val. intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - split.
    { constructor; cbn; [constructor|intros c []|repeat split; intros c h; discriminate h
                        |intros i h; discriminate h]. }
    apply globenv_decl; [constructor|].
    constructor.
    + constructor.
    + exact ws_on_udecl.
    + exact ws_on_inductive.
    + cbn. intros i h; discriminate h.
Qed.

Definition ws_wfE : wfE ws_env := wf_incl_E ws_wf.

Lemma ws_declared_inductive : declared_inductive ws_env ws_ind ws_mdecl ws_idecl.
Proof. split; [now left|reflexivity]. Qed.

Lemma ws_declared_constructor : declared_constructor ws_env (ws_ind, 0) ws_mdecl ws_idecl ws_cdecl.
Proof. split; [exact ws_declared_inductive|reflexivity]. Qed.

Definition ind_respects_varianceE_scoped_inst :=
  ind_respects_varianceE_scoped (wfΣ := ws_wfE) ws_declared_inductive eq_refl.

Definition cstr_respects_varianceE_scoped_inst :=
  cstr_respects_varianceE_scoped (wfΣ := ws_wfE) ws_declared_constructor eq_refl.

Definition ws_wfE_scoped_inst := wfE_scoped ws_wfE.

(** The pair the variance check of [K] compares, read off the conclusion of
    [ind_respects_varianceE_scoped]: [Type@{lvar 1} ≤ Type@{lvar 0}] in the empty context. *)
Lemma ws_ind_pair_scoped :
  ∑ Σ' : global_env_ext, ∑ univs',
    cmp_scoped cumulSpecE0 (Σ'.1, univs') [] Cumul
      (tSort ws_u@[[Level.lvar 1]]) (tSort ws_u@[[Level.lvar 0]]).
Proof.
  destruct ind_respects_varianceE_scoped_inst as (Σ' & [_ _ h]).
  cbn in h. exists Σ'. eexists.
  inversion h as [|? ? ? ? _ hd]; subst. inversion hd; subst. eassumption.
Qed.

(** The index of the constructor [k], [tRel 0], compared with itself in
    [K : Type@{lvar 1} -> Prop, X : Type@{lvar 1}]. *)
Lemma ws_cstr_index_scoped :
  ∑ Σ' : global_env_ext, ∑ univs',
    cmp_scoped cumulSpecE0 (Σ'.1, univs') (ws_ar ,, vass ws_na ws_TU)@[[Level.lvar 1]] Conv
      (tRel 0) (tRel 0).
Proof.
  destruct cstr_respects_varianceE_scoped_inst as (Σ' & [_ _ [_ h]]).
  cbn in h. exists Σ'. eexists.
  inversion h as [|? ? ? ? hx _]; subst. exact hx.
Qed.

(** A primitive operation. [po_wf] is the proof of [Σ_po_wf] without its squash. *)
Lemma po_wf : wf Σ_po0.
Proof.
  split; [exact po_univs_ok|]. split; [exact po_retro_wf|].
  cbn. constructor.
  - constructor; [constructor|].
    econstructor.
    + constructor.
    + exact po_udecl_ok.
    + cbn. split; [exact tt|]. exists (Sort.super Sort.type0). repeat split. apply po_int_type.
    + cbn. intros op hop. discriminate hop.
  - econstructor.
    + constructor; [intros [=]|constructor].
    + exact po_udecl_ok.
    + cbn. split; [exact tt|].
      exists (Sort.sort_of_product Sort.type0 (Sort.sort_of_product Sort.type0 Sort.type0)).
      repeat split. exact po_land_type_typed.
    + cbn. intros op hop. injection hop as <-.
      constructor; cbn; try reflexivity.
      * exists po_land_ty. split; [reflexivity|]. apply cumul_Refl.
      * repeat constructor.
        all: exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
      * exists po_int_kn, po_int_body; split; [reflexivity|now left|split; reflexivity].
Qed.

Definition po_wfE : wfE Σ_po0 := wf_incl_E po_wf.

Definition prim_op_cst_typeE_scoped_inst :=
  prim_op_cst_typeE_scoped (wfΣ := po_wfE) (kn := po_land_kn) (cb := po_land_body)
    (or_introl eq_refl) Σ_po_registers.

Definition po_wfE_scoped_inst := wfE_scoped po_wfE.

End Instances.
