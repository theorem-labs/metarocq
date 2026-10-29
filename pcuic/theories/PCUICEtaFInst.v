(* Distributed under the terms of the MIT license. *)

(** * [compare_term_eta]: the algorithmic comparison with η (U1', "F-inst")

  [compare_term_eta] is the comparison that ends the canonical joins of the η
  specification ([JoinE], [PCUICEtaI5]). It is a copy of base
  [eq_term_upto_univ_napp] in which the two constructors that read [napp],
  [eq_Ind] and [eq_Construct], compare an under-applied head as the kernel's
  [MustExpand] does: at its full arity, and at [Conv].

  ** Why base's comparison does not fit

  For an inductive [I1] with [Irrelevant] variance, [I1@{u}] and [I1@{v}] are both
  [red1]-normal and [eta1]-normal, so every join of them ends in a comparison at
  [napp 0]. There base [global_variance_gen]'s [arity <=? napp] test fails and the
  result [AllEqual] demands [eq_universe u v]. The η specification relates them,
  by a two-step η detour: [I1@{u} ≤sE[Conv] λx:S. I1@{v} (tRel 0)] by [cumul_eta_r]
  (whose premise is [cumulE_Ind] at [napp 1]), then
  [λx:S. I1@{v} (tRel 0) ≤sE[Conv] I1@{v}] by [cumul_eta_l] on [cumulE_Refl], glued
  by [cumulE_Trans]. The kernel accepts the same pair through [MustExpand].

  ** The comparison at full arity, and why at [Conv]

  An under-applied head is compared at [max napp arity]. Because
  [global_variance_gen]'s only use of [napp] is the [arity <=? napp] test, the
  variance then no longer reads [napp] at all
  ([global_variance_eta_napp_irrelevant]).

  The mode is [Conv] below the arity: every route by which the specification
  relates an under-applied head is an η detour, and every such detour has its
  premise at [Conv] ([cumul_eta_l]'s premise, [cumulE_Sym]'s premise, and
  [cumul_eta_r], which is built from both). [cumulE_Ind]/[cumulE_Construct] at
  the ambient [pb] apply only to a head that carries its arity's arguments. At
  [Conv], [cmp_universe_variance] is [True] at [Irrelevant] and [on_rel (cmp_univ
  Conv)] at [Covariant] and [Invariant], so the per-component relation is an
  equivalence ([cmp_global_instance_eta_trans]).

  ** The constructor rule

  A constructor of a non-cumulative inductive is compared by instance equality,
  as the kernel does. No extra branch is needed for it: compared at its full
  arity, base [global_variance_gen] already returns [AllEqual] there
  ([finst_noncumulative_constructor_AllEqual]). The η specification is
  characterised by the joins of this comparison ([I5_FollowKernel]). *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import RelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
     PCUICInduction PCUICEquality.

Local Open Scope type_scope.

(** ** Full arity of a head

  [IndRef]: the assumptions among parameters and indices, the count
  [global_variance_gen] tests. [ConstructRef]: [cstr_arity + ind_npars], the
  count tested for constructors. An absent declaration keeps arity [0], so F-inst
  then agrees with base on the [AllEqual] fallback. *)

Definition head_arity_gen lookup (gr : global_reference) : nat :=
  match gr with
  | IndRef ind =>
      match lookup_inductive_gen lookup ind with
      | Some (mdecl, idecl) =>
          context_assumptions (mdecl.(ind_params) ,,, idecl.(ind_indices))
      | None => 0
      end
  | ConstructRef ind k =>
      match lookup_constructor_gen lookup ind k with
      | Some (mdecl, _, cdecl) => cdecl.(cstr_arity) + mdecl.(ind_npars)
      | None => 0
      end
  | _ => 0
  end.

Notation head_arity Σ := (head_arity_gen (lookup_env Σ)).

(** Is the head a constructor of a NON-cumulative inductive? Below its full
    arity that is the head whose variance is not base's [AllEqual] fallback. *)
Definition noncumulative_constructor_gen lookup (gr : global_reference) : bool :=
  match gr with
  | ConstructRef ind k =>
      match lookup_constructor_gen lookup ind k with
      | Some (mdecl, _, _) => match mdecl.(ind_variance) with
                              | None => true
                              | Some _ => false
                              end
      | None => false
      end
  | _ => false
  end.

(** The variance lookup F-inst uses: the base one at the head's FULL arity. A
    constructor of a non-cumulative inductive needs no case of its own: at the
    full arity base returns [AllEqual] for it
    ([finst_noncumulative_constructor_AllEqual]), which is the kernel's rule. *)
Definition global_variance_eta_gen lookup gr napp :=
  global_variance_gen lookup gr (max napp (head_arity_gen lookup gr)).

Notation global_variance_eta Σ := (global_variance_eta_gen (lookup_env Σ)).

(** **The napp drop disappears.** It is the whole content of the R3(a) repair. *)
Lemma global_variance_eta_napp_irrelevant lookup gr napp napp' :
  global_variance_eta_gen lookup gr napp = global_variance_eta_gen lookup gr napp'.
Proof.
  unfold global_variance_eta_gen.
  unfold global_variance_gen, head_arity_gen.
  destruct gr as [id|kn|ind|ind k]; cbn; try reflexivity.
  - destruct (lookup_inductive_gen lookup ind) as [[mdecl idecl]|]; [|reflexivity].
    now rewrite !(proj2 (Nat.leb_le _ _) (Nat.le_max_r _ _)).
  - destruct (lookup_constructor_gen lookup ind k) as [[[mdecl idecl] cdecl]|];
      [|reflexivity].
    now rewrite !(proj2 (Nat.leb_le _ _) (Nat.le_max_r _ _)).
Qed.

(** The lookup is base's variance at the full arity, by definition. *)
Lemma global_variance_eta_base lookup gr napp :
  global_variance_eta_gen lookup gr napp
  = global_variance_gen lookup gr (max napp (head_arity_gen lookup gr)).
Proof. reflexivity. Qed.

(** ** The F-inst instance comparison

  Heads applied to at least their arity are compared at [pb], as base
  [eq_Ind]/[eq_Construct] and the specification's [cumulE_Ind]/[cumulE_Construct]
  do; otherwise a fully applied cumulative inductive at [Cumul]
  ([Box@{+u} ≤ Box@{v}], [u < v]) would be related by the specification but
  refused by the join ([finst_cumulative_box_witness]). Heads below their arity
  are compared at [Conv] with the full-arity variance. The step from [(Conv, n)]
  to [(pb, m)] used by the η case is monotone ([finst_Conv_pb]). *)

Definition finst_mode (Σ : global_env) (gr : global_reference) (pb : conv_pb) (napp : nat) :=
  if head_arity Σ gr <=? napp then pb else Conv.

Definition cmp_global_instance_eta Σ cmp_universe pb gr napp :=
  cmp_opt_variance cmp_universe (finst_mode Σ gr pb napp) (global_variance_eta Σ gr napp).

(** ** The instance comparison is an equivalence

  Transitivity has to compose the disjunction in [cmp_opt_variance] at [Variance
  v]. The proof is base's [cmp_global_instance_trans] with
  [cmp_opt_variance_or_impl]: base never inspects where the variance or the mode
  came from. With the mode [pb] or [Conv], every hypothesis base needs is
  required at both, and is discharged at the actual mode by [finst_mode_cases]. *)

Lemma finst_mode_cases (P : conv_pb -> Type) Σ gr pb napp :
  P Conv -> P pb -> P (finst_mode Σ gr pb napp).
Proof. intros hC hp. unfold finst_mode. now destruct (_ <=? _). Qed.

Section FInstInstance.
  Context (Σ : global_env)
          (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop).

  Lemma cmp_global_instance_eta_refl pb gr napp :
    RelationClasses.Reflexive (cmp_universe Conv) ->
    RelationClasses.Reflexive (cmp_universe pb) ->
    RelationClasses.Reflexive (cmp_global_instance_eta Σ cmp_universe pb gr napp).
  Proof.
    intros univ_refl _.
    unfold cmp_global_instance_eta.
    destruct global_variance_eta_gen as [| |v] => //= u.
    - now apply cmp_universe_instance_refl.
    - left. now apply cmp_universe_instance_refl.
  Qed.

  Lemma cmp_global_instance_eta_sym pb gr napp :
    RelationClasses.Symmetric (cmp_universe Conv) ->
    RelationClasses.Symmetric (cmp_universe pb) ->
    RelationClasses.Symmetric (cmp_global_instance_eta Σ cmp_universe pb gr napp).
  Proof.
    intros univ_sym univ_sym'.
    have hm : RelationClasses.Symmetric (cmp_universe (finst_mode Σ gr pb napp))
      := finst_mode_cases (fun m => RelationClasses.Symmetric (cmp_universe m)) _ _ _ _ univ_sym univ_sym'.
    unfold cmp_global_instance_eta.
    destruct global_variance_eta_gen as [| |v] => //= u u'.
    - now symmetry.
    - intros [H | H]; [left|right].
      all: now symmetry.
  Qed.

  (** Transitivity of the instance comparison, by base's combinator. *)
  Lemma cmp_global_instance_eta_trans pb gr napp :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    RelationClasses.Transitive (cmp_universe Conv) ->
    RelationClasses.Transitive (cmp_universe pb) ->
    RelationClasses.Transitive (cmp_global_instance_eta Σ cmp_universe pb gr napp).
  Proof.
    intros univ_sub univ_trans univ_trans'.
    have hsub : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe (finst_mode Σ gr pb napp))
      := finst_mode_cases (fun m => RelationClasses.subrelation (cmp_universe Conv) (cmp_universe m))
           _ _ _ _ (fun x y h => h) univ_sub.
    have htr : RelationClasses.Transitive (cmp_universe (finst_mode Σ gr pb napp))
      := finst_mode_cases (fun m => RelationClasses.Transitive (cmp_universe m)) _ _ _ _ univ_trans univ_trans'.
    unfold cmp_global_instance_eta.
    destruct global_variance_eta_gen as [| |v] => //= u u' u''.
    1,2: now etransitivity.
    apply cmp_opt_variance_or_impl; tas.
    all: now etransitivity.
  Qed.

  (** [AllEqual] input implies F-inst at any mode ([cmp_instance_opt_variance],
      [PCUICEquality.v:102-109]). *)
  Lemma cmp_global_instance_eta_weaken pb gr napp u u' :
    cmp_universe_instance (cmp_universe Conv) u u' ->
    cmp_global_instance_eta Σ cmp_universe pb gr napp u u'.
  Proof.
    intros h. unfold cmp_global_instance_eta.
    now apply (cmp_instance_opt_variance cmp_universe _ _ u u').
  Qed.

  (** A [Conv]-mode comparison implies the same comparison at any [pb'] whose
      universe relation contains [Conv]'s. *)
  Lemma cmp_opt_variance_Conv_sub pb' v u u' :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb') ->
    cmp_opt_variance cmp_universe Conv v u u' -> cmp_opt_variance cmp_universe pb' v u u'.
  Proof.
    intros sub. destruct v as [| |v]; cbn; try (intros h; exact h).
    intros [h|h]; [now left|right].
    eapply Forall3_impl; [exact h|]. intros [] x y; cbn; try (intros; exact I).
    - unfold on_rel. apply sub.
    - intros e; exact e.
  Qed.

  (** The [(Conv, n) → (pb, m)] monotonicity the η case relies on. At [Conv] the
      mode is [Conv] for every [napp]; the variance does not read [napp]
      ([global_variance_eta_napp_irrelevant]); and a [Conv]-mode comparison
      implies the [pb]-mode or [Conv]-mode one at [m]. *)
  Lemma finst_Conv_pb pb gr n m u u' :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    cmp_global_instance_eta Σ cmp_universe Conv gr n u u' ->
    cmp_global_instance_eta Σ cmp_universe pb gr m u u'.
  Proof.
    intros sub. unfold cmp_global_instance_eta.
    have -> : finst_mode Σ gr Conv n = Conv by unfold finst_mode; now destruct (_ <=? _).
    rewrite (global_variance_eta_napp_irrelevant (lookup_env Σ) gr n m).
    apply cmp_opt_variance_Conv_sub.
    exact (finst_mode_cases (fun pm => RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pm))
             _ _ _ _ (fun x y h => h) sub).
  Qed.

End FInstInstance.

(** **The [Box@{+u}] witness holds.** A cumulative inductive with no parameters
    and no indices (arity 0), one [Covariant] universe, compared at [Cumul] with
    [napp 0] and no arguments: [u ≤ v] suffices. Stated for any such declared
    inductive. *)
Lemma finst_cumulative_box_witness (Σ : global_env) cmp_universe i mdecl idecl u v :
  declared_inductive_gen (lookup_env Σ) i mdecl idecl ->
  ind_params mdecl = [] -> ind_indices idecl = [] ->
  ind_variance mdecl = Some [Variance.Covariant] ->
  on_rel (cmp_universe Cumul) Universe.make' u v ->
  cmp_global_instance_eta Σ cmp_universe Cumul (IndRef i) 0 [u] [v].
Proof.
  intros hd hp hi hv huv.
  have hl := declared_inductive_lookup_gen hd.
  unfold cmp_global_instance_eta, finst_mode, global_variance_eta_gen, head_arity_gen.
  rewrite hl hp hi; cbn.
  unfold global_variance_gen. rewrite hl hp hi hv; cbn.
  right. constructor; [exact huv|constructor].
Qed.

(** **The hypotheses are satisfiable.** The three premises of the transitivity
    lemma are met by the real comparison [compare_universe φ], at every [pb], for
    every [φ], with no well-formedness: [compare_universe φ Conv] is
    [eq_universe φ], transitive by [eq_universe_trans]; [compare_universe φ pb] is
    transitive by [compare_universe_trans]; and
    [eq_universe φ ⊆ compare_universe φ pb] is [compare_universe_subrel]. This
    corollary is that statement. *)
Lemma cmp_global_instance_eta_trans_compare {cf : checker_flags} Σ φ pb gr napp :
  RelationClasses.Transitive (cmp_global_instance_eta Σ (compare_universe φ) pb gr napp).
Proof.
  apply cmp_global_instance_eta_trans.
  - exact (compare_universe_subrel φ pb).
  - exact (eq_universe_trans φ).
  - exact (compare_universe_trans φ pb).
Qed.

(** ** U1', the term-level relation

  A copy of base [eq_term_upto_univ_napp] with exactly two constructors changed,
  [eq_Ind] and [eq_Construct], the only two that read [napp]. Every other
  constructor is base's. The copy is needed because [napp] is threaded through
  the inductive, so the variance lookup cannot be swapped from outside. *)

Definition cmp_global_instance_finst Σ cmp_universe pb gr napp :=
  cmp_global_instance_eta Σ cmp_universe pb gr napp.

Section FInstRelation.

Reserved Notation " Σ ⊢ t <==η[ pb , napp ] u" (at level 50, t, u at next level,
  format "Σ  ⊢  t  <==η[ pb , napp ]  u").

Inductive eq_term_upto_univ_eta_napp Σ
  (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop)
  (cmp_sort : conv_pb -> sort -> sort -> Prop)
  (pb : conv_pb) (napp : nat) : term -> term -> Type :=
| eqη_Rel : forall n,
    Σ ⊢ tRel n <==η[ pb , napp ] tRel n

| eqη_Evar : forall e args args',
    All2 (fun arg arg' => (Σ ⊢ arg <==η[ Conv , 0 ] arg')) args args' ->
    Σ ⊢ tEvar e args <==η[ pb , napp ] tEvar e args'

| eqη_Var : forall id,
    Σ ⊢ tVar id <==η[ pb , napp ] tVar id

| eqη_Sort : forall s s',
    cmp_sort pb s s' ->
    Σ ⊢ tSort s <==η[ pb , napp ] tSort s'

| eqη_App : forall t t' u u',
    Σ ⊢ t <==η[ pb , S napp ] t' ->
    Σ ⊢ u <==η[ Conv , 0 ] u' ->
    Σ ⊢ tApp t u <==η[ pb , napp ] tApp t' u'

| eqη_Const : forall c u u',
    cmp_universe_instance (cmp_universe Conv) u u' ->
    Σ ⊢ tConst c u <==η[ pb , napp ] tConst c u'

(* F-INST. The variance is read at the head's FULL ARITY; the comparison mode is
   [pb] at or above the arity and [Conv] below it ([finst_mode]). These two
   constructors are the only change from base. *)
| eqη_Ind : forall i u u',
    cmp_global_instance_finst Σ cmp_universe pb (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==η[ pb , napp ] tInd i u'

| eqη_Construct : forall i k u u',
    cmp_global_instance_finst Σ cmp_universe pb (ConstructRef i k) napp u u' ->
    Σ ⊢ tConstruct i k u <==η[ pb , napp ] tConstruct i k u'

| eqη_Lambda : forall na na' ty ty' t t',
    eq_binder_annot na na' ->
    Σ ⊢ ty <==η[ Conv , 0 ] ty' ->
    Σ ⊢ t <==η[ Conv , 0 ] t' ->
    Σ ⊢ tLambda na ty t <==η[ pb , napp ] tLambda na' ty' t'

| eqη_Prod : forall na na' a a' b b',
    eq_binder_annot na na' ->
    Σ ⊢ a <==η[ Conv , 0 ] a' ->
    Σ ⊢ b <==η[ pb , 0 ] b' ->
    Σ ⊢ tProd na a b <==η[ pb , napp ] tProd na' a' b'

| eqη_LetIn : forall na na' t t' ty ty' u u',
    eq_binder_annot na na' ->
    Σ ⊢ t <==η[ Conv , 0 ] t' ->
    Σ ⊢ ty <==η[ Conv , 0 ] ty' ->
    Σ ⊢ u <==η[ Conv , 0 ] u' ->
    Σ ⊢ tLetIn na t ty u <==η[ pb , napp ] tLetIn na' t' ty' u'

| eqη_Case : forall indn p p' c c' brs brs',
    eq_predicate (fun t t' => Σ ⊢ t <==η[ Conv , 0 ] t') (cmp_universe Conv) p p' ->
    Σ ⊢ c <==η[ Conv , 0 ] c' ->
    eq_branches (fun t t' => Σ ⊢ t <==η[ Conv , 0 ] t') brs brs' ->
    Σ ⊢ tCase indn p c brs <==η[ pb , napp ] tCase indn p' c' brs'

| eqη_Proj : forall p c c',
    Σ ⊢ c <==η[ Conv , 0 ] c' ->
    Σ ⊢ tProj p c <==η[ pb , napp ] tProj p c'

| eqη_Fix : forall mfix mfix' idx,
    eq_mfixpoint (fun t t' => Σ ⊢ t <==η[ Conv , 0 ] t') mfix mfix' ->
    Σ ⊢ tFix mfix idx <==η[ pb , napp ] tFix mfix' idx

| eqη_CoFix : forall mfix mfix' idx,
    eq_mfixpoint (fun t t' => Σ ⊢ t <==η[ Conv , 0 ] t') mfix mfix' ->
    Σ ⊢ tCoFix mfix idx <==η[ pb , napp ] tCoFix mfix' idx

| eqη_Prim i i' :
    onPrims (fun t t' => Σ ⊢ t <==η[ Conv , 0 ] t') (cmp_universe Conv) i i' ->
    Σ ⊢ tPrim i <==η[ pb , napp ] tPrim i'
where " Σ ⊢ t <==η[ pb , napp ] u " :=
  (eq_term_upto_univ_eta_napp Σ _ _ pb napp t u) : type_scope.

Definition compare_term_eta_napp `{checker_flags} Σ φ (pb : conv_pb) napp (t u : term) :=
  eq_term_upto_univ_eta_napp Σ (compare_universe φ) (compare_sort φ) pb napp t u.

(** **U1'.** The comparison that ends the joins of [I5_statement]. *)
Definition compare_term_eta `{checker_flags} Σ φ (pb : conv_pb) (t u : term) :=
  compare_term_eta_napp Σ φ pb 0 t u.

End FInstRelation.

Derive Signature for eq_term_upto_univ_eta_napp.

(** ** Constructors of non-cumulative inductives

  For a constructor of a non-cumulative inductive, F-inst demands instance
  equality, as the kernel and base [global_variance_gen] do. The full-arity
  lookup lands in base's [None] branch of [ind_variance], which is [AllEqual]. *)

Lemma finst_noncumulative_constructor_AllEqual lookup gr napp :
  noncumulative_constructor_gen lookup gr = true ->
  global_variance_eta_gen lookup gr napp = AllEqual.
Proof.
  intros h. unfold noncumulative_constructor_gen in h.
  destruct gr as [id|kn|ind|ind k]; try discriminate.
  unfold global_variance_eta_gen, global_variance_gen, head_arity_gen.
  destruct (lookup_constructor_gen lookup ind k) as [[[mdecl idecl] cdecl]|];
    [|discriminate].
  destruct (ind_variance mdecl); [discriminate|].
  now destruct (_ <=? _).
Qed.

(** The same fact at the comparison: a non-cumulative constructor head is
    compared by instance equality, as the kernel's [convert_constructors_gen]
    does. *)
Lemma finst_noncumulative_constructor_instance_eq Σ cmp_universe pb ind k napp u u' :
  noncumulative_constructor_gen (lookup_env Σ) (ConstructRef ind k) = true ->
  cmp_global_instance_finst Σ cmp_universe pb (ConstructRef ind k) napp u u' ->
  cmp_universe_instance (cmp_universe Conv) u u'.
Proof.
  intros hnc h.
  unfold cmp_global_instance_finst, cmp_global_instance_eta in h.
  now rewrite (finst_noncumulative_constructor_AllEqual _ _ napp hnc) in h.
Qed.
