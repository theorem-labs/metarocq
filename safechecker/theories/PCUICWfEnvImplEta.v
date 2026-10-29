(* Distributed under the terms of the MIT license. *)
(** * [PCUICWfEnvImpl] over the η well-formedness [wfE]/[wf_extE]

  A copy of [PCUICWfEnvImpl] with the SAME names, implementing the abstract environment of
  [PCUICWfEnvEta]: the records [reference_impl] and [reference_impl_ext] carry
  [∥ wfE Σ ∥] and [∥ wf_extE Σ ∥] where base's carry [∥ wf Σ ∥] and [∥ wf_ext Σ ∥], and
  every function that builds one ([build_reference_impl], [build_reference_impl_ext],
  [ext_graph_of_udecl], [make_reference_impl_ext], [make_wf_env_ext],
  [build_wf_env_ext], [build_wf_env_from_env]) takes the η premise. [wf_fresh_globals],
  [reference_impl_sq_wf] and the section [GraphSpec] take [wfE]. The guard check
  ([abstract_guard_impl], [check_guard_impl], [real_guard_impl]) does not read the
  environment's well-formedness and is copied unchanged, so that this file does not load
  base [PCUICWfEnv].

  Two proof-level differences with base: the hint database is [wf_envE] (base's [wf_env]
  stays untouched when both files are loaded; the tactic [wf_env] keeps its name), and
  the obligation of [abstract_env_is_consistent_correct] passes the [wfE] premise of
  [levels_global_constraint] explicitly, because that lemma ([PCUICGlobalEnvEta]) takes
  any [on_global_env Pcmp P], which typeclass resolution does not fill as it fills base's
  [wf] premise.

  Import this file LAST, after every file that loads base [PCUICWfEnvImpl].

  No hypothesis: every statement is proved. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config uGraph EnvMap.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICReflect PCUICSafeLemmata PCUICTyping PCUICGlobalEnv PCUICWfUniverses
     PCUICGuardChecker PCUICGuardClosure PCUICCumulativitySpecEta PCUICTypingEta.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnvEta.
From Equations Require Import Equations.

(** An executable guard check. Only soundness is required: a [true] answer
    implies the guard condition, a [false] answer is a refusal, not a proof
    that the definition is unguarded. *)
Class abstract_guard_impl :=
  { guard_impl : FixCoFix -> global_env_ext -> context -> mfixpoint term -> bool ;
    guard_correct : forall fix_cofix Σ Γ mfix, guard_impl fix_cofix Σ Γ mfix -> guard fix_cofix Σ Γ mfix
  }.

(** The fuel of the real guard check. The checker doubles its traversal depth
    at each unit of fuel ([gfuel]), so this fixed bound is cheap to state. *)
Definition guard_fuel : nat := 30.

Definition check_guard_impl (fix_cofix : FixCoFix) (Σ : global_env_ext) (Γ : context)
  (mfix : mfixpoint term) : bool :=
  wf_cases_mfix Σ.1 mfix &&
  match check_guard_gen (lookup_env Σ.1) Σ.1.(retroknowledge) guard_fuel fix_cofix #|Γ|
          (strip_mfix mfix) with
  | Accept => true
  | _ => false
  end.

Lemma check_guard_impl_correct fix_cofix Σ Γ mfix :
  check_guard_impl fix_cofix Σ Γ mfix -> guard fix_cofix Σ Γ mfix.
Proof.
  rewrite /check_guard_impl => /andP [hwf hchk].
  change (guard_cl fix_cofix Σ Γ mfix).
  apply gc_check; split => //.
  exists guard_fuel.
  move: hchk; case: check_guard_gen => //.
Qed.

(** The real guard check: the executable checker [check_guard_gen] of
    [PCUICGuardChecker], sound for the closure [guard_cl]. It is not a global
    instance, so that typeclass resolution of the generic environment
    instances is unchanged; users declare it with [Existing Instance]. *)
Definition real_guard_impl : abstract_guard_impl :=
  {| guard_impl := check_guard_impl;
     guard_correct := check_guard_impl_correct |}.

(** The universe graphs are stored fields, computed once when an environment is built.
    As let-fields they were recomputed at every access in the extracted checker, so every
    universe comparison rebuilt the whole graph. Each graph is stored with an index of its
    vertices, so that universe comparisons compare no level names inside Bellman-Ford. *)
Record reference_impl_ext {cf:checker_flags} {guard : abstract_guard_impl} := {
      reference_impl_env_ext :> global_env_ext;
      reference_impl_ext_wf :> ∥ wf_extE reference_impl_env_ext ∥;
      reference_impl_ext_graph : universes_graph;
      reference_impl_ext_graph_wf : is_graph_of_uctx reference_impl_ext_graph (global_ext_uctx reference_impl_env_ext);
      reference_impl_ext_index : wGraph.index;
      reference_impl_ext_index_wf : wGraph.is_index_of reference_impl_ext_graph reference_impl_ext_index
  }.

Record reference_impl {cf:checker_flags} := {
      reference_impl_env :> global_env;
      reference_impl_wf :> ∥ wfE reference_impl_env ∥;
      reference_impl_graph : universes_graph;
      reference_impl_graph_wf : is_graph_of_uctx reference_impl_graph (global_uctx reference_impl_env);
      reference_impl_index : wGraph.index;
      reference_impl_index_wf : wGraph.is_index_of reference_impl_graph reference_impl_index
  }.

Lemma graph_index_of_wf {cf:checker_flags} (Σ : global_env) (wfΣ : ∥ wfE Σ ∥) G :
  is_graph_of_uctx G (global_uctx Σ) -> wGraph.is_index_of G (wGraph.index_of G).
Proof.
  intro HG. destruct wfΣ as [wfΣ].
  assert (HI : wGraph.invariants G).
  { eapply global_uctx_graph_invariants; [exact HG|]. now eapply wf_global_uctx_invariants. }
  exact (wGraph.index_of_correct G).
Qed.

Lemma graph_index_of_wf_ext {cf:checker_flags} (Σ : global_env_ext) (wfΣ : ∥ wf_extE Σ ∥) G :
  is_graph_of_uctx G (global_ext_uctx Σ) -> wGraph.is_index_of G (wGraph.index_of G).
Proof.
  intro HG. destruct wfΣ as [wfΣ].
  assert (HI : wGraph.invariants G).
  { eapply global_uctx_graph_invariants; [exact HG|]. now eapply wf_ext_global_uctx_invariants. }
  exact (wGraph.index_of_correct G).
Qed.

Lemma reference_impl_graph_invariants {cf:checker_flags} (X : reference_impl) :
  wGraph.invariants (reference_impl_graph X).
Proof.
  destruct (reference_impl_wf X) as [wfX].
  eapply global_uctx_graph_invariants; [exact (reference_impl_graph_wf X)|].
  now eapply wf_global_uctx_invariants.
Qed.

Definition build_reference_impl {cf:checker_flags} (Σ : global_env) (wfΣ : ∥ wfE Σ ∥) : reference_impl :=
  let G := graph_of_wf wfΣ in
  {| reference_impl_env := Σ; reference_impl_wf := wfΣ;
     reference_impl_graph := G.π1;
     reference_impl_graph_wf := G.π2;
     reference_impl_index := wGraph.index_of G.π1;
     reference_impl_index_wf := graph_index_of_wf Σ wfΣ G.π1 G.π2 |}.

Definition build_reference_impl_ext {cf:checker_flags} {guard : abstract_guard_impl}
  (Σ : global_env_ext) (wfΣ : ∥ wf_extE Σ ∥) : reference_impl_ext :=
  let G := graph_of_wf_ext wfΣ in
  {| reference_impl_env_ext := Σ; reference_impl_ext_wf := wfΣ;
     reference_impl_ext_graph := G.π1;
     reference_impl_ext_graph_wf := G.π2;
     reference_impl_ext_index := wGraph.index_of G.π1;
     reference_impl_ext_index_wf := graph_index_of_wf_ext Σ wfΣ G.π1 G.π2 |}.

(** The graph of [(X, udecl)] and its index, from the stored graph and index of [X] and the
    universes of [udecl]: adding a declaration's few universes neither rebuilds the global
    graph nor renumbers it. *)
Definition ext_graph_of_udecl {cf:checker_flags} (X : reference_impl) (udecl : universes_decl)
  (wfΣ : ∥ wf_extE (reference_impl_env X, udecl) ∥) :
  ∑ G, ∑ ix, is_graph_of_uctx G (global_ext_uctx (reference_impl_env X, udecl)) /\
             wGraph.is_index_of G ix :=
  match gc_of_uctx (uctx_of_udecl udecl) as o
    return gc_of_uctx (uctx_of_udecl udecl) = o ->
      ∑ G, ∑ ix, is_graph_of_uctx G (global_ext_uctx (reference_impl_env X, udecl)) /\
                 wGraph.is_index_of G ix with
  | Some gctx => fun H =>
    (add_uctx gctx (reference_impl_graph X);
      (add_uctx_ix gctx (reference_impl_index X);
        conj (is_graph_of_uctx_add H (reference_impl_graph_wf X))
             (add_uctx_ix_correct gctx _ _ (reference_impl_graph_invariants X)
                (reference_impl_index_wf X))))
  | None => fun _ =>
    let G := graph_of_wf_ext wfΣ in
    (G.π1; (wGraph.index_of G.π1; conj G.π2 (graph_index_of_wf_ext _ wfΣ G.π1 G.π2)))
  end eq_refl.

Definition make_reference_impl_ext {cf:checker_flags} {guard : abstract_guard_impl}
  (X : reference_impl) (udecl : universes_decl) (wfΣ : ∥ wf_extE (reference_impl_env X, udecl) ∥)
  : reference_impl_ext :=
  let r := ext_graph_of_udecl X udecl wfΣ in
  let r2 := r.π2 in
  {| reference_impl_env_ext := (reference_impl_env X, udecl); reference_impl_ext_wf := wfΣ;
     reference_impl_ext_graph := r.π1;
     reference_impl_ext_graph_wf := proj1 r2.π2;
     reference_impl_ext_index := r2.π1;
     reference_impl_ext_index_wf := proj2 r2.π2 |}.

Program Definition reference_pop {cf:checker_flags} (Σ : reference_impl) : reference_impl :=
match Σ.(declarations) with
 [] => Σ
 | (d::decls) =>
   {| reference_impl_env := {| universes := Σ.(universes); declarations := decls; retroknowledge := Σ.(retroknowledge) |};
      reference_impl_graph := Σ.(reference_impl_graph);
      reference_impl_graph_wf := Σ.(reference_impl_graph_wf);
      reference_impl_index := Σ.(reference_impl_index);
      reference_impl_index_wf := Σ.(reference_impl_index_wf) |}
end.
Next Obligation.
destruct Σ.(reference_impl_wf). sq.
destruct X as [onu [wfr ond]]; split; [exact onu|]; split; [exact wfr|].
rewrite <- Heq_anonymous in ond. now depelim ond.
Qed.

Definition make_wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl}
(Σ : reference_impl) (univs : universes_decl)
(prf : forall Σ0 : global_env, Σ0 = Σ -> ∥ wf_extE (Σ0, univs) ∥) : reference_impl_ext :=
  make_reference_impl_ext Σ univs (prf _ eq_refl).

Program Global Instance canonical_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct reference_impl reference_impl_ext :=
  {|
  abstract_env_lookup := fun Σ => lookup_env (reference_impl_env_ext Σ) ;
  abstract_env_leqb_level_n := fun Σ => leqb_level_n_ix (reference_impl_ext_index Σ) ;
  abstract_env_level_mem := fun Σ l => LevelSet.mem l (global_ext_levels (reference_impl_env_ext Σ));
  abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (reference_impl_env_ext Σ);
  abstract_env_ext_rel := fun X Σ => Σ = reference_impl_env_ext X;
  abstract_env_init := fun cs retro H =>
    build_reference_impl {| universes := cs ;
                            declarations := [];
                            retroknowledge := retro |} _ ;
  abstract_env_add_decl := fun X kn d H =>
    {| reference_impl_env := add_global_decl X.(reference_impl_env) (kn,d);
       reference_impl_graph := X.(reference_impl_graph);
       reference_impl_graph_wf := X.(reference_impl_graph_wf);
       reference_impl_index := X.(reference_impl_index);
       reference_impl_index_wf := X.(reference_impl_index_wf) |};
  abstract_env_is_consistent X uctx :=
   let G := reference_impl_graph X in
   let ix := reference_impl_index X in
   let G' := add_uctx uctx G in
   let ix' := add_uctx_ix uctx ix in
   wGraph.is_acyclic_ix ix' && wGraph.IsFullSubgraph.is_full_extension_ix G ix G' ix' ;
  abstract_env_add_udecl X udecl Hglobal := make_reference_impl_ext X udecl _ ;
  abstract_primitive_constant := fun X tag => primitive_constant X tag;
  abstract_prim_op_of := fun X c => prim_op_of X c;
  abstract_primitive_bool := fun X => primitive_bool X;
  abstract_env_rel := fun X Σ => Σ = reference_impl_env X ;
  abstract_pop_decls := reference_pop ;
 |}.
Next Obligation.
  sq. split; [assumption|]. split; [assumption|]. constructor.
Qed.
Next Obligation.
  pose proof (reference_impl_wf X) as [[Hu [Hr Hd]]].
  destruct (H _ eq_refl) as [Hdata].
  sq. split; [exact Hu|]. split; [exact Hr|].
  constructor; [exact Hd|exact Hdata].
Qed.
Next Obligation.
  pose proof (reference_impl_wf X). destruct (Hglobal _ eq_refl); sq.
  now econstructor.
Qed.

(* We pack up all the information required on the global environment and graph in a
single record. *)

Record wf_env {cf:checker_flags} := {
  wf_env_reference :> reference_impl;
  wf_env_map :> EnvMap.t global_decl;
  wf_env_map_repr :> EnvMap.repr (reference_impl_env wf_env_reference).(declarations) wf_env_map;
}.

Record wf_env_ext {cf:checker_flags} {guard : abstract_guard_impl} := {
  wf_env_ext_reference :> reference_impl_ext;
  wf_env_ext_map :> EnvMap.t global_decl;
  wf_env_ext_map_repr :> EnvMap.repr (reference_impl_env_ext wf_env_ext_reference).(declarations) wf_env_ext_map;
}.

Lemma wf_env_eta {cf : checker_flags} (Σ : wf_env) :
 {| universes := Σ.(universes); declarations := Σ.(declarations); retroknowledge := Σ.(retroknowledge) |} = Σ.
Proof.
  destruct Σ => /= //. destruct reference_impl_env => //.
Qed.

Lemma wf_fresh_globals {cf : checker_flags} Σ : wfE Σ -> EnvMap.fresh_globals Σ.(declarations).
Proof. destruct Σ as [univs Σ]; cbn.
  move=> [] onu [] wfr; cbn. induction 1; constructor; auto. now destruct o.
Qed.


Lemma wf_env_fresh {cf : checker_flags} (Σ : wf_env) : EnvMap.EnvMap.fresh_globals Σ.(declarations).
Proof.
  destruct Σ.(reference_impl_wf).
  now eapply wf_fresh_globals.
Qed.

Lemma of_global_env_cons {cf:checker_flags} d g : EnvMap.fresh_globals (add_global_decl g d).(declarations) ->
  EnvMap.of_global_env (add_global_decl g d).(declarations) = EnvMap.add d.1 d.2 (EnvMap.of_global_env g.(declarations)).
Proof.
  unfold EnvMap.of_global_env. simpl. unfold KernameMapFact.uncurry.
  reflexivity.
Qed.

Program Definition wf_env_init {cf:checker_flags} {guard : abstract_guard_impl} cs retro :
  on_global_univs cs /\ Retroknowledge.wf_retro retro -> wf_env := fun H =>
  {|
  wf_env_reference := abstract_env_init cs retro H;
  wf_env_map := EnvMap.empty;
  |}.

Lemma reference_pop_decls_correct {cf:checker_flags} (X:reference_impl) decls
  (prf : forall Σ : global_env, Σ = X ->
  exists d, Σ.(declarations) = d :: decls) :
  let X' := reference_pop X in
  forall Σ Σ', Σ = X -> Σ' = X' ->
          Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
          Σ.(retroknowledge) = Σ'.(retroknowledge).
Proof.
  cbn; intros; subst. specialize (prf _ eq_refl).
  unfold reference_pop. cbn. set (reference_pop_obligation_1 cf X).
  clearbody s. destruct (X.(declarations)); cbn; inversion prf; now inversion H.
Qed.

Program Definition optim_pop {cf:checker_flags} (Σ : wf_env) : wf_env :=
  match Σ.(reference_impl_env).(declarations) with
    [] => Σ
    | ((kn , d) :: decls) =>
    {| wf_env_reference := reference_pop Σ ;
        wf_env_map := EnvMap.EnvMap.remove kn Σ.(wf_env_map);
    |}
  end.

Next Obligation.
  pose proof Σ.(wf_env_map_repr). red in H.
  rewrite <- Heq_anonymous in H.
  set (Σ0 := EnvMap.of_global_env decls).
  pose proof (EnvMap.remove_add_eq decls kn d Σ0).
  PCUICSR.forward_keep H0.
  { pose proof (Σf := wf_env_fresh Σ). rewrite <- Heq_anonymous in Σf. now depelim Σf. }
  PCUICSR.forward_keep H0.
  { pose proof (Σf := wf_env_fresh Σ). rewrite <- Heq_anonymous in Σf. now depelim Σf. }
  PCUICSR.forward_keep H0.
  { red. unfold EnvMap.equal. reflexivity. }
  unfold EnvMap.repr.
  rewrite H /=. unfold KernameMapFact.uncurry; cbn.
  unfold EnvMap.add in H0.
  unfold reference_pop. cbn. set (reference_pop_obligation_1 cf _).
  clearbody s.
  destruct (declarations Σ); cbn in *; inversion Heq_anonymous; clear Heq_anonymous s.
  subst. unfold KernameMapFact.uncurry in *; cbn in *.
  unfold Σ0 in * ; clear Σ0. unfold EnvMap.equal, KernameMap.Equal in H0.
  specialize (H0 y). cbn in H0. rewrite H0. reflexivity.
Qed.

Program Global Instance optimized_abstract_env_struct {cf:checker_flags} {guard : abstract_guard_impl} :
  abstract_env_struct wf_env wf_env_ext :=
 {|
 abstract_env_lookup := fun Σ k => EnvMap.lookup k (wf_env_ext_map Σ);
 abstract_env_leqb_level_n X := abstract_env_leqb_level_n X.(wf_env_ext_reference);
 abstract_env_level_mem X := abstract_env_level_mem X.(wf_env_ext_reference);
 abstract_env_guard := fun Σ fix_cofix => guard_impl fix_cofix (wf_env_ext_reference Σ);
 abstract_env_ext_rel X := abstract_env_ext_rel X.(wf_env_ext_reference);

 abstract_env_init := wf_env_init;
 abstract_env_add_decl X kn d H :=
  {| wf_env_reference := @abstract_env_add_decl _ _ reference_impl_ext _ X.(wf_env_reference) kn d H ;
     wf_env_map := EnvMap.add kn d X.(wf_env_map) |};
 abstract_env_is_consistent X uctx := abstract_env_is_consistent X.(wf_env_reference) uctx;
 abstract_env_add_udecl X udecl Hdecl :=
 {| wf_env_ext_reference := @abstract_env_add_udecl _ _ reference_impl_ext _ X.(wf_env_reference) udecl Hdecl ;
    wf_env_ext_map := X.(wf_env_map) |};
 abstract_primitive_constant X := abstract_primitive_constant X.(wf_env_ext_reference);
 abstract_prim_op_of X := abstract_prim_op_of X.(wf_env_ext_reference);
 abstract_primitive_bool X := abstract_primitive_bool X.(wf_env_ext_reference);
 abstract_env_rel X := abstract_env_rel X.(wf_env_reference) ;
 abstract_pop_decls := optim_pop ;
 |}.
Next Obligation.
  pose proof (X.(wf_env_reference).(reference_impl_wf)) as [?].
  sq. destruct (H _ eq_refl).
  apply EnvMap.repr_add; eauto; try eapply wf_fresh_globals; eauto.
  destruct X1; eauto.
  apply wf_env_map_repr.
Qed.
Next Obligation. apply wf_env_map_repr. Qed.

Section WfEnv.
  Context {cf : checker_flags} {guard : abstract_guard_impl}.

  Definition reference_impl_sq_wf (Σ : reference_impl_ext) : ∥ wfE Σ ∥.
  Proof using Type.
    destruct (reference_impl_ext_wf Σ).
    sq. apply X.
  Qed.

  Definition lookup (Σ : wf_env_ext) (kn : kername) : option global_decl :=
    EnvMap.lookup kn Σ.(wf_env_ext_map).

  Lemma lookup_lookup_env Σ kn : lookup Σ kn = lookup_env Σ kn.
  Proof using Type.
    rewrite /lookup. destruct Σ as [Σ map repr]. pose (reference_impl_sq_wf Σ).
    sq. apply EnvMap.lookup_spec; auto. now eapply wf_fresh_globals.
  Qed.

End WfEnv.


Create HintDb wf_envE discriminated.
Global Hint Constants Opaque : wf_envE.
Global Hint Variables Opaque : wf_envE.

Global Hint Resolve reference_impl_ext_wf : wf_envE.
Global Hint Resolve reference_impl_wf : wf_envE.

Definition Σudecl_ref {cf : checker_flags} {guard : abstract_guard_impl} (Σ : reference_impl_ext) :
  ∥ on_udecl Σ.(reference_impl_env_ext).1 Σ.(reference_impl_env_ext).2 ∥ :=
    map_squash (fun x => x.2) Σ.

Definition Σudecl {cf : checker_flags} {guard : abstract_guard_impl} (Σ : wf_env_ext) :
  ∥ on_udecl Σ.(reference_impl_env_ext).1 Σ.(reference_impl_env_ext).2 ∥ :=
  map_squash (fun x => x.2) Σ.

  Global Hint Resolve Σudecl : wf_envE.

Ltac wf_env := auto with wf_envE.


(** Build an optimized environment representation for lookups along with the graph associated to a well-formed
  global environment. The graph building is separated, so that [(build_wf_env_ext Σ wfΣ).(wf_env_ext_env)] is
  convertible to [Σ]. *)

Definition build_wf_env_ext {cf : checker_flags} {guard : abstract_guard_impl} (Σ : global_env_ext) (wfΣ : ∥ wf_extE Σ ∥) : wf_env_ext :=
  {| wf_env_ext_reference := build_reference_impl_ext Σ wfΣ ;
     wf_env_ext_map := EnvMap.of_global_env Σ.(declarations);
     wf_env_ext_map_repr := EnvMap.repr_global_env Σ.(declarations);
|}.

Section GraphSpec.
  Context {cf:checker_flags} {guard : abstract_guard_impl} {Σ : global_env_ext} (HΣ : ∥ wfE Σ ∥)
      (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
      (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_extE Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Qed.

  Lemma is_graph_of_uctx_levels (l : Level.t) :
    LevelSet.mem l (uGraph.wGraph.V G) <->
    LevelSet.mem l (global_ext_levels Σ).
  Proof using HG.
    unfold is_graph_of_uctx in HG.
    case_eq (gc_of_uctx (global_ext_uctx Σ)); [intros [lvs cts] XX|intro XX];
      rewrite -> XX in *; simpl in *; [|contradiction].
    unfold gc_of_uctx in XX; simpl in XX.
    destruct (gc_of_constraints Σ); [|discriminate].
    inversion XX; subst.
    unfold is_true. rewrite !LevelSet.mem_spec.
    symmetry. apply HG.
  Qed.

End GraphSpec.

Program Global Instance canonical_abstract_env_prop {cf:checker_flags} {guard : abstract_guard_impl} :
  @abstract_env_prop _ _ _ canonical_abstract_env_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (reference_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Qed.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation.
  apply (reference_pop_decls_correct X decls prf X (reference_pop X) eq_refl eq_refl).
Qed.
Next Obligation.
  epose proof (HΣ := reference_impl_ext_wf X). sq.
  apply lookup_global_Some_iff_In_NoDup => //.
  destruct HΣ as [[] _]. now eapply NoDup_on_global_decls.
Qed.
Next Obligation.
  pose proof (reference_impl_ext_wf X); sq.
  set (uctx := wf_ext_gc_of_uctx _) in *; destruct uctx as [[lc ctrs] Huctx].
  assert (consistent (global_ext_uctx X).2) as HC.
      { sq; apply (global_ext_uctx_consistent _ H). }
  simpl in HC. apply gc_consistent_iff in HC.
  assert (HIx : wGraph.invariants (reference_impl_ext_graph X)).
  { eapply global_uctx_graph_invariants; [exact (reference_impl_ext_graph_wf X)|].
    now eapply wf_ext_global_uctx_invariants. }
  unfold leqb_level_n_ix.
  rewrite (wGraph.leqb_vertices_ix_correct _ _ _ _ _ (reference_impl_ext_index_wf X)).
  eapply leqb_level_n_spec; eauto.
    + eapply gc_of_uctx_invariants; try eapply wf_ext_global_uctx_invariants; eauto.
    + clear Hl Hl'. Opaque gc_of_constraints. cbn in *. Transparent gc_of_constraints.
      destruct (gc_of_constraints X); inversion Huctx. now destruct H2.
    + pose proof (reference_impl_ext_graph_wf X) as HG.
      unfold is_graph_of_uctx in HG. now rewrite Huctx in HG.
Qed.
Next Obligation. pose (reference_impl_ext_wf X). sq. symmetry; apply LevelSet.Raw.mem_spec. typeclasses eauto. Defined.
Next Obligation.
  pose (reference_impl_wf X). sq.
  rename H0 into Hudecl. rename H1 into Hudecl'.
  assert (H0 : global_uctx_invariants (global_uctx X)).
  { eapply wf_global_uctx_invariants; eauto. }
  set (udecl := (t , t0)).
  assert (H1 : global_uctx_invariants (ContextSet.union udecl (global_uctx X))).
  { split => //.
    - apply LevelSet.union_spec; right ; now destruct H0.
    - intros [[l ct] l'] [Hl|Hl]%CS.union_spec.
      + now specialize (Hudecl _ Hl).
      + destruct H0 as [_ H0]. specialize (H0 _ Hl).
        split; apply LevelSet.union_spec; right;
        now cbn in H0.
     }
  pose proof (reference_impl_graph_wf X) as HG.
  pose proof (reference_impl_index_wf X) as Hix.
  set (gph := reference_impl_graph X) in *.
  set (ix := reference_impl_index X) in *. clearbody gph ix. simpl in HG.
  pose proof (HG' := is_graph_of_uctx_add Hudecl' HG).
  assert (Hinv : wGraph.invariants gph).
  { apply (global_uctx_graph_invariants HG H0). }
  assert (Hinv' : wGraph.invariants (add_uctx (t1, t2) gph)).
  { apply (global_uctx_graph_invariants HG' H1). }
  assert (Hsub : wGraph.subgraph gph (add_uctx (t1, t2) gph)).
  { apply add_uctx_subgraph. }
  pose proof (add_uctx_ix_correct (t1, t2) gph ix Hinv Hix) as Hix'.
  rewrite (wGraph.is_acyclic_ix_eq _ _ Hix')
          (wGraph.IsFullSubgraph.is_full_extension_ix_eq gph ix _ _ Hix Hix').
  rewrite (wGraph.IsFullSubgraph.is_acyclic_full_extension'_iff
             gph (add_uctx (t1, t2) gph) Hsub).
  rewrite andb_and.
  pose (global_ext_uctx := ContextSet.union udecl (global_uctx X)).
  pose (wf_consistent_extension_on_consistent udecl.2 s).
  assert (reorder : forall a a' b c : Prop, (b -> a) -> (a /\ b <-> a' /\ c) -> b <-> a' /\ c) by intuition; eapply reorder; try eassumption; clear reorder.
  rewrite - (is_consistent_spec global_ext_uctx) (is_consistent_spec2 HG').
  assert (reorder : forall a b c : Prop, (a -> b <-> c) -> a /\ b <-> a /\ c) by intuition; apply reorder.
  move=> ?; rewrite consistent_extension_on_union.
  1:{ pose proof (reference_impl_wf X) as [hX].
      apply: (levels_global_constraint _ hX). }
  cbn.
  change (CS.union _ _) with global_ext_uctx.2.
  apply: consistent_ext_on_full_ext=> //.
Qed.
Next Obligation. intros; cbn in *; subst; now apply guard_correct. Qed.


Program Global Instance optimized_abstract_env_prop {cf:checker_flags} {guard : abstract_guard_impl} :
  @abstract_env_prop _ _ _ optimized_abstract_env_struct :=
     {| abstract_env_ext_exists := fun Σ => sq (reference_impl_env_ext Σ ; eq_refl); |}.
Next Obligation. wf_env. Qed.
Next Obligation. now sq. Qed.
Next Obligation. wf_env. Qed.
Next Obligation. now split. Qed.
Next Obligation. unfold optim_pop. set (optim_pop_obligation_1 cf X). clearbody r.
  pose proof (reference_pop_decls_correct X decls prf X (reference_pop X) eq_refl eq_refl).
  specialize (prf _ eq_refl).
  destruct (declarations X); cbn; inversion prf; inversion H0. subst.
  now destruct x.
Qed.
Next Obligation.
  epose proof (HΣ := reference_impl_ext_wf X). sq.
  etransitivity; try apply abstract_env_lookup_correct => //.
  assert (lookup_env X kn = EnvMap.lookup kn X).
  { erewrite EnvMap.lookup_spec; try reflexivity.
    1: apply wf_fresh_globals; eauto.
    1: apply wf_env_ext_map_repr. }
  now rewrite <- H.
Qed.
Next Obligation.
    revert n l l' Hl Hl'. erewrite wf_ext_gc_of_uctx_irr.
    exact (abstract_env_leqb_level_n_correct X.(wf_env_ext_reference) eq_refl).
Qed.
Next Obligation.
  now erewrite (abstract_env_level_mem_correct X.(wf_env_ext_reference)).
Qed.
Next Obligation.
  now erewrite (abstract_env_is_consistent_correct X.(wf_env_reference)) with (udecl := (t,t0)); eauto.
Qed.
Next Obligation. intros; cbn in *; subst; now apply guard_correct. Qed.

Definition canonical_abstract_env_impl {cf:checker_flags} {guard : abstract_guard_impl} : abstract_env_impl :=
  (reference_impl ; reference_impl_ext ; canonical_abstract_env_struct ; canonical_abstract_env_prop).

Definition optimized_abstract_env_impl {cf:checker_flags} {guard : abstract_guard_impl} : abstract_env_impl :=
  (wf_env; wf_env_ext ; optimized_abstract_env_struct ; optimized_abstract_env_prop).

Definition build_wf_env_from_env {cf : checker_flags} (Σ : global_env) (wfΣ : ∥ PCUICTypingEta.wfE Σ ∥) : wf_env
  :=
  let Σm := EnvMap.of_global_env Σ.(declarations) in
  {| wf_env_reference := build_reference_impl Σ wfΣ ;
     wf_env_map := Σm;
     wf_env_map_repr := EnvMap.repr_global_env Σ.(declarations);
 |}.
