(* Distributed under the terms of the MIT license. *)
(** * [PCUICWfEnv] over the η well-formedness [wfE]/[wf_extE]

  A copy of [PCUICWfEnv] with the SAME names. The intended changes are
  [abstract_env_ext_wf X : abstract_env_ext_rel X Σ -> ∥ wf_extE Σ ∥] and
  [abstract_env_wf X : abstract_env_rel X Σ -> ∥ wfE Σ ∥] ([PCUICTypingEta]), and what
  follows from them:
  - [on_global_decls], the premise of [abstract_env_add_decl], checks the declaration with
    [cumulSpecE0] and [typingE], so that adding it keeps the environment [wfE];
  - [abstract_make_wf_env_ext] takes [∥ wf_extE (Σ, univs) ∥];
  - [abstract_env_ext_sq_wf] gives [∥ wfE Σ ∥];
  - [on_udecl_mono] and [wf_consistent_extension_on_consistent] take [wfE Σ].

  The universe lemmas this file reads take [∥ wf_ext Σ ∥] in [PCUICEqualityDec]
  ([wf_gc_of_uctx], [graph_of_wf], [wf_ext_gc_of_uctx], [wf_ext_gc_of_uctx_irr],
  [graph_of_wf_ext], [uctx'_eq], and the section [EqualityDecGen] up to
  [compare_sortP_gen]). They read only the universe part of the environment, so they are
  restated below with the same names and proofs, for [on_global_env Pcmp P] /
  [on_global_env_ext Pcmp P] with ANY conversion relation [Pcmp]; [PCUICGlobalEnvEta]
  (re-exported here) does the same for the universe lemmas of [PCUICGlobalEnv]. A base use
  at [cumulSpec0] still type-checks against these versions.

  New here: [abstract_env_closed_bodies] and [abstract_env_ext_closed_bodies]
  ([∥ ClosedBodies Σ ∥], the environment premise of the reduction metatheory, from
  [wfE_ClosedBodies]).

  Import this file LAST, after every file that loads base [PCUICWfEnv] or
  [PCUICEqualityDec], so that its names win.

  No hypothesis: every statement is proved. *)
From Stdlib Require Import ssreflect.
From Stdlib Require ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph EnvMap PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses
     PCUICCumulativitySpecEta PCUICTypingEta PCUICClosedBodies PCUICClosedTypEta.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec.
From MetaRocq.PCUIC Require Export PCUICGlobalEnvEta.

(** ** The universe lemmas of [PCUICEqualityDec], for any conversion relation *)

Section UnivGraph.
  Context {cf : checker_flags}.
  Context {Pcmp : global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P : global_env_ext -> context -> judgment -> Type}.

  Lemma wf_gc_of_uctx {Σ : global_env} (HΣ : ∥ on_global_env Pcmp P Σ ∥)
  : ∑ uctx', gc_of_uctx (global_uctx Σ) = Some uctx'.
  Proof.
  assert (consistent (global_uctx Σ).2) as HC.
  { sq; apply (wf_consistent _ HΣ). }
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_constraints Σ)).
  - eexists; reflexivity.
  - contradiction HC.
  Defined.

  Lemma graph_of_wf {Σ : global_env} (HΣ : ∥ on_global_env Pcmp P Σ ∥)
  : ∑ G, is_graph_of_uctx G (global_uctx Σ).
  Proof.
  destruct (wf_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
  Defined.

  Lemma wf_ext_gc_of_uctx {Σ : global_env_ext} (HΣ : ∥ on_global_env_ext Pcmp P Σ ∥)
  : ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
  Proof.
  assert (consistent (global_ext_uctx Σ).2) as HC.
    { sq; apply (global_ext_uctx_consistent _ HΣ). }
  destruct Σ as [Σ φ].
  simpl in HC.
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_ext_constraints (Σ, φ))).
  - eexists; reflexivity.
  - contradiction HC.
  Defined.

  Lemma wf_ext_gc_of_uctx_irr {Σ : global_env_ext} (HΣ HΣ' : ∥ on_global_env_ext Pcmp P Σ ∥) :
    wf_ext_gc_of_uctx HΣ = wf_ext_gc_of_uctx HΣ'.
  Proof.
    unfold wf_ext_gc_of_uctx. Opaque gc_of_constraints.
    destruct Σ; cbn.
    match goal with | |- _ ?X = _ ?Y => set (prf := X) ; set (prf' := Y) end.
    clearbody prf prf'. cbn in *. revert prf prf'.
    set (gc_of_constraints ((g, u):global_env_ext)) in *.
    now destruct o.
  Qed.

  Lemma graph_of_wf_ext {Σ : global_env_ext} (HΣ : ∥ on_global_env_ext Pcmp P Σ ∥)
  : ∑ G, is_graph_of_uctx G (global_ext_uctx Σ).
  Proof.
  destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
  Defined.

  Lemma uctx'_eq {Σ} (wfΣ : ∥ on_global_env_ext Pcmp P Σ ∥) :
    let G := graph_of_wf_ext wfΣ in
    (wf_ext_gc_of_uctx wfΣ).π1 = uctx' G.π1 (global_ext_uctx Σ) G.π2.
  Proof.
    sq. Opaque gc_of_constraints.
    unfold wf_ext_gc_of_uctx, uctx'. destruct Σ. cbn.
    match goal with | |- (_ ?X).π1 = _ ?Y => set (prf := X) ; set (prf' := Y) end.
    clearbody prf prf'. cbn in *. revert prf prf'.
    set (G := graph_of_wf_ext _). destruct G as [G HG].
    unfold is_graph_of_uctx in *. cbn in *.
    Transparent gc_of_constraints.
    set (gc_of_constraints ((g, u):global_env_ext)) in *.
    now destruct o.
  Qed.

End UnivGraph.

(** The reflection lemmas of the section [EqualityDecGen] ([PCUICEqualityDec]) that read
    the environment, for any conversion relation. The boolean functions
    ([check_cmpb_universe_gen], [check_cmpb_sort_gen]) are base's. *)
Section EqualityDecGen.
  Context {cf : checker_flags}.
  Context {Pcmp : global_env_ext -> context -> conv_pb -> term -> term -> Type}.
  Context {P : global_env_ext -> context -> judgment -> Type}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ on_global_env_ext Pcmp P Σ ∥).

  Let uctx := global_ext_uctx Σ.

  Let G := (graph_of_wf_ext hΣ).π1.

  Let HG := (graph_of_wf_ext hΣ).π2.

  Let uctx' : VSet.t × GoodConstraintSet.t.
    fold G uctx in HG. clearbody G HG. cbn in *.
    unfold is_graph_of_uctx, gc_of_uctx in HG.
    destruct (gc_of_constraints uctx.2) as [ctrs|].
    - exact (uctx.1, ctrs).
    - contradiction HG.
  Defined.

  Lemma eq_universeP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
    u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (eq_universe Σ u u') (check_eqb_universe_gen leqb_level_n_gen u u').
  Proof using hΣ.
    intros. destruct Σ as [Σ' φ].
    apply (ssrbool.equivP ssrbool.idP); split; sq.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_eqb_universe_spec_gen'
         with (uctx := global_ext_uctx (Σ', φ)) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_eqb_universe_complete_gen
        with (uctx := global_ext_uctx (Σ', φ)); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma leq_universeP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (leq_universe Σ u u') (check_leqb_universe_gen leqb_level_n_gen u u').
  Proof using hΣ.
    intros.
    apply (ssrbool.equivP ssrbool.idP) ; split.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_leqb_universe_spec_gen'
        with (uctx := global_ext_uctx Σ) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_leqb_universe_complete_gen
        with (uctx := global_ext_uctx Σ); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma compare_universeP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) pb u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    reflect (compare_universe Σ pb u u') (check_cmpb_universe_gen leqb_level_n_gen pb u u').
  Proof.
    destruct pb.
    - now apply eq_universeP_gen.
    - now apply leq_universeP_gen.
  Qed.

  Lemma eq_sortP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen)
    s s' :
    wf_sort Σ s ->
    wf_sort Σ s' ->
    reflect (eq_sort Σ s s') (check_eqb_sort_gen leqb_level_n_gen s s').
  Proof using hΣ.
    intros. destruct Σ as [Σ' φ].
    apply (ssrbool.equivP ssrbool.idP); split; sq.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_eqb_sort_spec_gen'
        with (uctx := global_ext_uctx (Σ', φ)) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_eqb_sort_complete_gen
        with (uctx := global_ext_uctx (Σ', φ)); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma leq_sortP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) s s' :
    wf_sort Σ s ->
    wf_sort Σ s' ->
    reflect (leq_sort Σ s s') (check_leqb_sort_gen leqb_level_n_gen s s').
  Proof using hΣ.
    intros.
    apply (ssrbool.equivP ssrbool.idP) ; split.
    all: pose proof hΣ as hΣ' ; sq.
    - intros e.
      eapply check_leqb_sort_spec_gen'
        with (uctx := global_ext_uctx Σ) in e ; eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
    - intros e.
      eapply check_leqb_sort_complete_gen
        with (uctx := global_ext_uctx Σ); eauto.
      + now eapply wf_ext_global_uctx_invariants.
      + now eapply global_ext_uctx_consistent.
  Qed.

  Lemma compare_sortP_gen leqb_level_n_gen
    (leqb_correct : leqb_level_n_spec_gen uctx' leqb_level_n_gen) pb s s' :
    wf_sort Σ s ->
    wf_sort Σ s' ->
    reflect (compare_sort Σ pb s s') (check_cmpb_sort_gen leqb_level_n_gen pb s s').
  Proof.
    destruct pb.
    - now apply eq_sortP_gen.
    - now apply leq_sortP_gen.
  Qed.

End EqualityDecGen.

(** ** The copy of [PCUICWfEnv] *)

Definition level_mem : global_env_ext -> Level.t -> bool
  := fun X l => LevelSet.mem l (global_ext_levels X).

(** A declaration added to a [wfE] environment is checked with [cumulSpecE0]/[typingE]. *)
Definition on_global_decls {cf:checker_flags} Σ :=
  on_global_decls_data cumulSpecE0 (lift_typing typingE) (cf:=cf) Σ.(universes) Σ.(retroknowledge) Σ.(declarations).

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl : Type) := {
  (* This part of the structure is here to state the correctness properties *)

  abstract_env_rel : abstract_env_impl -> global_env -> Prop;
  abstract_env_ext_rel : abstract_env_ext_impl -> global_env_ext -> Prop;

  (* Operations on the environment *)

  abstract_env_init (cs:ContextSet.t) (retro : Retroknowledge.t) : on_global_univs cs /\ Retroknowledge.wf_retro retro -> abstract_env_impl;
  abstract_env_add_decl X (kn:kername) (d:global_decl) :
   (forall Σ, abstract_env_rel X Σ -> ∥ on_global_decls Σ kn d ∥)
   -> abstract_env_impl;
  abstract_env_add_udecl X udecl :
    (forall Σ, abstract_env_rel X Σ -> ∥ on_udecl Σ.(universes) udecl ∥) ->
    abstract_env_ext_impl ;
  abstract_pop_decls : abstract_env_impl -> abstract_env_impl ;

  (* Queries on the environment *)

  abstract_env_lookup : abstract_env_ext_impl -> kername -> option global_decl;
  abstract_primitive_constant : abstract_env_ext_impl -> Primitive.prim_tag -> option kername;
  abstract_prim_op_of : abstract_env_ext_impl -> kername -> option prim_op;
  abstract_primitive_bool : abstract_env_ext_impl -> option inductive;

  (* Primitive decision procedures *)
  abstract_env_level_mem : abstract_env_ext_impl -> Level.t -> bool;
  abstract_env_leqb_level_n : abstract_env_ext_impl -> Z -> Level.t -> Level.t -> bool;
  abstract_env_guard : abstract_env_ext_impl -> FixCoFix -> context -> mfixpoint term -> bool;
  abstract_env_is_consistent : abstract_env_impl -> LevelSet.t * GoodConstraintSet.t -> bool ;

}.

Definition abstract_env_fixguard  {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) := abstract_env_guard X Fix.

Definition abstract_env_cofixguard  {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) := abstract_env_guard X CoFix.

Definition abstract_env_compare_universe {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : conv_pb -> Universe.t -> Universe.t -> bool :=
  check_cmpb_universe_gen (abstract_env_leqb_level_n X).

Definition abstract_env_compare_sort {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) : conv_pb -> sort -> sort -> bool :=
    check_cmpb_sort_gen (abstract_env_leqb_level_n X).

Definition abstract_env_check_constraints {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
  (X:abstract_env_ext_impl) : ConstraintSet.t -> bool :=
    check_constraints_gen (abstract_env_leqb_level_n X).

Definition abstract_env_ext_wf_universeb {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : Universe.t -> bool :=
    fun (u : Universe.t) => LevelExprSet.for_all (fun l => abstract_env_level_mem X (LevelExpr.get_level l)) u.

Definition abstract_env_ext_wf_sortb {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : sort -> bool :=
    Sort.on_sort (abstract_env_ext_wf_universeb X) true.

Definition abstract_env_level_mem' {cf:checker_flags} {abstract_env_impl abstract_env_ext_impl : Type} `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl}
(X:abstract_env_ext_impl) : LevelSet.t -> Level.t -> bool :=
    fun levels l => LevelSet.mem l levels || abstract_env_level_mem X l.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl: Type)
  `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl} : Prop := {

  abstract_env_ext_exists X : ∥ ∑ Σ , abstract_env_ext_rel X Σ ∥;
  abstract_env_ext_wf X {Σ} : abstract_env_ext_rel X Σ -> ∥ wf_extE Σ ∥ ;
  abstract_env_ext_irr X {Σ Σ'} :
      abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ' ->  Σ = Σ';

  abstract_env_exists X : ∥ ∑ Σ , abstract_env_rel X Σ ∥;
  abstract_env_wf X {Σ} : abstract_env_rel X Σ -> ∥ wfE Σ ∥;
  abstract_env_irr X {Σ Σ'} :
    abstract_env_rel X Σ -> abstract_env_rel X Σ' ->  Σ = Σ';

  abstract_env_init_correct univs retro cuniv :
    abstract_env_rel (abstract_env_init univs retro cuniv)
    {| universes := univs; declarations := []; retroknowledge := retro |} ;
  abstract_env_add_decl_correct X Σ kn d H : abstract_env_rel X Σ ->
    abstract_env_rel (abstract_env_add_decl X kn d H) (add_global_decl Σ (kn,d));
  abstract_env_add_udecl_rel X {Σ} udecl H :
    (abstract_env_rel X Σ.1 /\ Σ.2 = udecl) <->
    abstract_env_ext_rel (abstract_env_add_udecl X udecl H) Σ;
  abstract_pop_decls_correct X decls (prf : forall Σ : global_env, abstract_env_rel X Σ ->
            exists d, Σ.(declarations) = d :: decls) :
    let X' := abstract_pop_decls X in
    forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' ->
                      Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
                      Σ.(retroknowledge) = Σ'.(retroknowledge);

  abstract_env_lookup_correct X {Σ} kn decl : abstract_env_ext_rel X Σ ->
      In (kn, decl) (declarations Σ) <-> abstract_env_lookup X kn = Some decl ;

  abstract_env_leqb_level_n_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ):
    let uctx := (wf_ext_gc_of_uctx (abstract_env_ext_wf X wfΣ)).π1 in
    leqb_level_n_spec_gen uctx (abstract_env_leqb_level_n X);
  abstract_env_level_mem_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) l:
    LevelSet.In l (global_ext_levels Σ) <-> abstract_env_level_mem X l;
  abstract_env_is_consistent_correct X Σ uctx udecl :
    abstract_env_rel X Σ ->
    ConstraintSet.For_all (declared_cstr_levels (LevelSet.union udecl.1 (global_levels Σ))) udecl.2 ->
    gc_of_uctx udecl = Some uctx ->
    consistent_extension_on (global_uctx Σ) udecl.2 <-> abstract_env_is_consistent X uctx ;

  abstract_env_guard_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) fix_cofix Γ mfix :
      abstract_env_guard X fix_cofix Γ mfix -> guard fix_cofix Σ Γ mfix;
  abstract_primitive_constant_correct X tag Σ :
    abstract_env_ext_rel X Σ -> abstract_primitive_constant X tag = PCUICEnvironment.primitive_constant Σ tag ;
  abstract_prim_op_of_correct X c Σ :
    abstract_env_ext_rel X Σ -> abstract_prim_op_of X c = PCUICEnvironment.prim_op_of Σ c ;
  abstract_primitive_bool_correct X Σ :
    abstract_env_ext_rel X Σ -> abstract_primitive_bool X = PCUICEnvironment.primitive_bool Σ
  }.

Definition abstract_env_impl {cf:checker_flags} := ∑ X Y Z, @abstract_env_prop _ X Y Z.

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1 Σ.π2.π1.
  exact (Σ.π2.π2.π1).
Defined.

Global Instance abstract_env_impl_abstract_env_prop {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_prop Σ.π1 Σ.π2.π1.
  exact (Σ.π2.π2.π2).
Defined.

Definition abstract_env_cored {cf:checker_flags} (_X : abstract_env_impl) (X : _X.π2.π1) {Σ Σ' Γ u v} : abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ'
-> cored Σ Γ u v -> cored Σ' Γ u v.
Proof.
  intros HΣ HΣ' Hred. erewrite (abstract_env_ext_irr _ HΣ'); eauto.
Defined.

Definition abstract_env_ext_sq_wf {cf:checker_flags} (X : abstract_env_impl) (x : X.π2.π1)
  Σ (wfΣ : abstract_env_ext_rel x Σ) : ∥ wfE Σ∥.
  destruct (abstract_env_ext_wf _ wfΣ).
  sq. auto.
Qed.

(** New: the environment premise of the reduction metatheory, from [wfE_ClosedBodies]. *)
Definition abstract_env_closed_bodies {cf:checker_flags} (X : abstract_env_impl) (x : X.π1)
  Σ (wfΣ : abstract_env_rel x Σ) : ∥ ClosedBodies Σ ∥.
Proof.
  destruct (abstract_env_wf _ wfΣ) as [wfΣ'].
  sq. exact (@wfE_ClosedBodies _ Σ wfΣ').
Qed.

Definition abstract_env_ext_closed_bodies {cf:checker_flags} (X : abstract_env_impl) (x : X.π2.π1)
  Σ (wfΣ : abstract_env_ext_rel x Σ) : ∥ ClosedBodies Σ ∥.
Proof.
  destruct (abstract_env_ext_wf _ wfΣ) as [wfΣ'].
  sq. exact (@wfE_ClosedBodies _ Σ.1 (wf_extE_wfE Σ wfΣ')).
Qed.

Notation "Σ '∼' X" := (abstract_env_rel X Σ) (at level 40).
Notation "Σ '∼_ext' X" := (abstract_env_ext_rel X Σ) (at level 40).


Program Definition abstract_make_wf_env_ext {cf:checker_flags} {X_type : abstract_env_impl} (X : X_type.π1)
  univs (prf : forall Σ : global_env, abstract_env_rel X Σ -> ∥ wf_extE (Σ, univs) ∥) : X_type.π2.π1
  := abstract_env_add_udecl X univs _.
Next Obligation.
  specialize (prf _ H). sq. now destruct prf.
Defined.

Definition abstract_make_wf_env_ext_correct {cf:checker_flags} {X_type : abstract_env_impl} (X : X_type.π1)  univs prf :
let X' := abstract_make_wf_env_ext X univs prf in
forall Σ Σ', abstract_env_rel X Σ -> abstract_env_ext_rel X' Σ' -> Σ' = (Σ, univs).
Proof.
  unfold abstract_make_wf_env_ext. intros.
  rewrite <- abstract_env_add_udecl_rel in H0. destruct Σ' , H0; cbn in *.
  now rewrite (abstract_env_irr X H H0).
Defined.

From Stdlib Require Import MSetFacts.

From Stdlib Require Import Morphisms.

Global Instance consistent_proper : Proper (CS.Equal ==> iff) consistent.
Proof.
  intros c c' eq. rewrite /consistent.
  now setoid_rewrite eq.
Qed.

Lemma on_udecl_mono {cf:checker_flags} {Σ : global_env} {wfΣ : wfE Σ} : on_udecl Σ Monomorphic_ctx.
Proof.
  repeat split; cbn.
  - intros i; rewrite LevelSetFact.empty_iff //.
  - intros i; rewrite ConstraintSetFact.empty_iff //.
  - red. rewrite /univs_ext_constraints /=.
    rewrite CS_union_empty.
    apply wfΣ.
  - apply consistent_extension_on_empty.
Qed.

Program Definition abstract_env_empty_ext {cf:checker_flags} {X_type : abstract_env_impl}
  (X : X_type.π1) : X_type.π2.π1
  := abstract_env_add_udecl X Monomorphic_ctx _.
Next Obligation.
  pose proof (abstract_env_wf _ H).
  sq. now apply on_udecl_mono.
Defined.

Definition abstract_env_empty_ext_rel {cf:checker_flags} {X_type : abstract_env_impl}
   (X : X_type.π1) {Σ} :
  (abstract_env_rel X Σ.1 /\ Σ.2 = Monomorphic_ctx)  <->
  abstract_env_ext_rel (abstract_env_empty_ext X) Σ.
Proof.
  unfold abstract_env_empty_ext. now rewrite <- abstract_env_add_udecl_rel.
Defined.

Program Definition abstract_env_empty {cf:checker_flags} {X_type : abstract_env_impl} : X_type.π1
  := abstract_env_init (LS.singleton Level.lzero , CS.empty) Retroknowledge.empty _.
Next Obligation.
  split.
  - repeat split.
    + intros x Hx; cbn in *. inversion Hx.
    + intros x Hx; cbn in *. destruct x; eauto. now inversion Hx.
    + red. unshelve eexists.
      * econstructor; eauto. intros; exact 1%positive.
      * red. intros ? ?. cbn in *. inversion H.
  - constructor; cbn.
    + constructor.
    + intros c [].
    + unfold Retroknowledge.types_distinct, Retroknowledge.disjoint_opt;
        repeat split; intros c H1 H2; discriminate H1.
    + intros i [=].
Defined.

Definition abstract_env_is_consistent_empty {cf:checker_flags} {X_type : abstract_env_impl}
  : VSet.t * GoodConstraintSet.t -> bool :=
  fun uctx => abstract_env_is_consistent (@abstract_env_empty cf X_type) uctx.

Lemma abstract_env_compare_universe_correct {cf:checker_flags} {X_type : abstract_env_impl}
  (X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) conv_pb u u' :
        wf_universe Σ u -> wf_universe Σ u' ->
        compare_universe Σ conv_pb u u' <->
        abstract_env_compare_universe X conv_pb u u'.
Proof.
  intros wfu wfu'. pose proof (abstract_env_ext_wf X wfΣ). sq.
  pose (Hleq := abstract_env_leqb_level_n_correct X wfΣ).
  erewrite uctx'_eq in Hleq.
  eapply compare_universeP_gen with (pb := conv_pb) in Hleq.
  apply reflect_reflectT in Hleq.
  split.
  1: now eapply introT.
  1: now eapply elimT.
  all: tea.
Qed.

Lemma abstract_env_compare_sort_correct {cf:checker_flags} {X_type : abstract_env_impl}
  (X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) conv_pb s s' :
        wf_sort Σ s -> wf_sort Σ s' ->
        compare_sort Σ conv_pb s s' <->
        abstract_env_compare_sort X conv_pb s s'.
Proof.
  intros wfu wfu'. pose proof (abstract_env_ext_wf X wfΣ). sq.
  pose (Hleq := abstract_env_leqb_level_n_correct X wfΣ).
  erewrite uctx'_eq in Hleq.
  eapply compare_sortP_gen with (pb := conv_pb) in Hleq.
  apply reflect_reflectT in Hleq.
  split.
  1: now eapply introT.
  1: now eapply elimT.
  all: tea.
Qed.

Lemma check_constraints_spec {cf:checker_flags} {X_type : abstract_env_impl}
     (X:X_type.π2.π1)  {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs :
     uctx_invariants ((global_ext_uctx Σ).1, ctrs) ->
     abstract_env_check_constraints X ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
Proof.
    intros Huctx HH. pose proof (abstract_env_ext_wf X wfΣ). sq.
    pose (Hleq := abstract_env_leqb_level_n_correct X wfΣ).
    erewrite uctx'_eq in Hleq.
    eapply (check_constraints_spec_gen _ (global_ext_uctx Σ)); eauto.
    - now eapply wf_ext_global_uctx_invariants.
    - now eapply global_ext_uctx_consistent.
    - pose proof (wf_ext_global_uctx_invariants Σ H) as [H1 H2].
      split; eauto.
Defined.

Lemma check_constraints_complete {cf:checker_flags} {X_type : abstract_env_impl}
    (X:X_type.π2.π1)  {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs (H : check_univs) :
    uctx_invariants ((global_ext_uctx Σ).1, ctrs) ->
    valid_constraints (global_ext_constraints Σ) ctrs -> abstract_env_check_constraints X ctrs.
Proof.
    intros Huctx HH. pose proof (abstract_env_ext_wf X wfΣ). sq.
    pose (Hleq := abstract_env_leqb_level_n_correct X wfΣ).
    erewrite uctx'_eq in Hleq.
    eapply (check_constraints_complete_gen _ (global_ext_uctx Σ)); eauto.
    - now eapply wf_ext_global_uctx_invariants.
    - now eapply global_ext_uctx_consistent.
    - pose proof (wf_ext_global_uctx_invariants Σ H0) as [H1 H2].
      split; eauto.
Qed.

Lemma abstract_env_check_constraints_correct {cf:checker_flags} {X_type : abstract_env_impl}
    (X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) ctrs :
    check_univs -> uctx_invariants ((global_ext_uctx Σ).1, ctrs) ->
    valid_constraints Σ ctrs <-> abstract_env_check_constraints X ctrs.
Proof.
  split; intros.
  - eapply check_constraints_complete; eauto.
  - eapply check_constraints_spec; eauto.
Qed.

Lemma abstract_env_ext_wf_universeb_correct {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) u :
  wf_universeb Σ u = abstract_env_ext_wf_universeb X u.
Proof.
  destruct u as [ [] ?]; cbn. clear is_ok t_ne.
  induction this => //; cbn. set (b := LevelSet.Raw.mem _ _). set (b' := abstract_env_level_mem _ _).
  assert (Hbb' : b = b').
  { unfold b'. apply eq_true_iff_eq. rewrite <- (abstract_env_level_mem_correct X wfΣ (LevelExpr.get_level a)).
    now erewrite <- (LevelSet.Raw.mem_spec (LevelSet.this (global_ext_levels Σ)) (LevelExpr.get_level a)). }
  destruct Hbb', b => //.
Qed.

Lemma abstract_env_ext_wf_sortb_correct {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) s :
  wf_sortb Σ s = abstract_env_ext_wf_sortb X s.
Proof.
  destruct s as [| |u]; cbnr.
  now apply abstract_env_ext_wf_universeb_correct.
Qed.

Lemma abstract_env_level_mem_correct' {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} (wfΣ : abstract_env_ext_rel X Σ) levels u :
  LevelSet.mem u (LevelSet.union levels (global_ext_levels Σ)) = abstract_env_level_mem' X levels u.
Proof.
  unfold abstract_env_level_mem'. rewrite wGraph.VSetProp.Dec.F.union_b.
  set (b0 := LevelSet.mem _ _). set (b := LevelSet.mem _ _). set (b' := abstract_env_level_mem _ _).
  assert (Hbb' : b = b').
  { unfold b'. apply eq_true_iff_eq. rewrite <- (abstract_env_level_mem_correct X wfΣ u).
    unfold LevelSet.In. now erewrite <- (LevelSet.Raw.mem_spec _ u). }
  destruct Hbb' => //.
Qed.

Lemma wf_consistent_extension_on_consistent {cf:checker_flags} {Σ} udecl :
  wfE Σ -> consistent_extension_on (global_uctx Σ) udecl ->
  consistent (ConstraintSet.union udecl (global_constraints Σ)).
Proof.
  intros s Hext. pose proof (wf_consistent _ s).
  destruct H as [val Hval].
  destruct (Hext val Hval) as [val' [Hval' Hval'']]. exists val'.
  intros [[l ct] l'] [Hl|Hl]%CS.union_spec; eauto.
  destruct (Hval _ Hl); cbn; econstructor.
  - erewrite <- (Hval'' l0). erewrite <- (Hval'' l'0) => //.
    + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
      + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
    - erewrite <- (Hval'' l0). erewrite <- (Hval'' l'0) => //.
      + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
      + destruct s as [[Hs _] _]. now destruct (Hs _ Hl).
Qed.

Lemma abstract_env_lookup_correct' {cf:checker_flags} {X_type : abstract_env_impl}
( X:X_type.π2.π1) {Σ} kn : abstract_env_ext_rel X Σ ->
  lookup_env Σ kn = abstract_env_lookup X kn.
Proof.
  intro wfΣ; pose proof (HΣ := abstract_env_ext_wf X wfΣ); sq.
  set (odecl := lookup_env _ _). case_eq odecl => [decl Hdecl| Hnotin].
  - intros. destruct (abstract_env_lookup_correct X kn decl wfΣ) as [H _].
    rewrite H; eauto. apply lookup_global_Some_iff_In_NoDup => //.
    destruct HΣ as [[] _]. now eapply NoDup_on_global_decls.
  - apply lookup_global_None in Hnotin. case_eq (abstract_env_lookup X kn) => //.
    intros decl Hdecl. eapply abstract_env_lookup_correct in Hdecl; eauto.
    destruct Hnotin. apply in_map_iff. now exists (kn,decl).
Qed.
