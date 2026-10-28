(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, U1' / F-inst: [compare_term_eta] — DRAFT, NOT PINNED

  **THE CONSTRUCTOR CLAUSE IS AN EXPLICIT HOLE, WAITING ON R3aProbe.** The stream
  lead has held the pin: one measurement decides how F-inst treats constructors,
  and it has not landed. So this file does NOT choose. It takes the choice as a
  parameter, [finst_construct_rule], and everything below is proved for BOTH
  values. Nothing here commits the lane to either.

  The open question: the non-cumulative constructor pair [p1@{u} A] against
  [p1@{v} A] was refused at TYPING in one posing. Whether ANY well-typed term
  can bring the kernel to compare them is being measured.
  - If no well-typed term reaches it, F-inst follows the SPEC
    ([FInstFollowSpec]): [ConstructRef] yields [AllIrrelevant] when fully
    applied, exactly as base [global_variance_gen] does ([PCUICEquality.v:59-67]).
  - If one does, F-inst follows the KERNEL's constructor rule
    ([FInstFollowKernel]): instance EQUALITY when [ind_variance = None]
    ([conversion.ml] V9.2.0 [:220-222]). A repaired route that is faithful to an
    unfaithful spec buys nothing.

  **The [tInd] half does NOT depend on that measurement and is settled below.**

  ** Why the relation has to change at all

  I5 as obligation 8 wrote it is FALSE. The witness needs no η and no [canon]:
  [I1@{u}] and [I1@{v}] for an inductive with [Irrelevant] variance are both
  [red1]-normal and [eta1]-normal, so every join of them ends in
  [compare_term pb 0]; there [global_variance_gen]'s [arity <=? napp] test fails
  ([PCUICEquality.v:51], [:56]) and the result [AllEqual] demands
  [eq_universe u v]. But the SPEC relates them, by a two-step η detour:

    [I1@{u} ≤sE[Conv] λx:S. I1@{v} (tRel 0)]   ([cumul_eta_r], :746-751,
                                                 premise is [cumulE_Ind] at napp 1)
    [λx:S. I1@{v} (tRel 0) ≤sE[Conv] I1@{v}]   ([cumul_eta_l] on [cumulE_Refl])
    glued by [cumulE_Trans] (:32-38; its scoping premises hold, [S] is closed).

  The kernel ACCEPTS these pairs (R3aProbe, [kernel2.log], [STATUS coqc=0]:
  [(fun A => I1@{u} A) = I1@{v}] and [I1@{u} = I1@{v}] directly at napp 0 through
  MustExpand, under [@{u v|}] with no constraint). So for the INDUCTIVE witness
  the spec is FAITHFUL and this is a statement bug in the algorithmic relation
  only; decision (C) is untouched.

  ** The fix, and why it is at [Conv]

  F-inst: an under-applied head is compared at its FULL ARITY, as the kernel's
  MustExpand does (plan K1). Because [global_variance_gen]'s ONLY use of [napp]
  is the [arity <=? napp] test, taking [max napp arity] makes that test vacuous:
  the relation stops reading [napp] at these heads altogether
  ([global_variance_eta_napp_irrelevant] below). That is the plan's
  "max [#|l|] arity" rule in closed form, and it is why R3(a) does not merely
  shrink but DISAPPEARS — there is no napp drop left to lose.

  **Pinned at [Conv], not at [pb]** (stream lead's correction). Checked, not
  assumed: every route by which the spec relates an UNDER-APPLIED head goes
  through an η detour, and every such detour has its premise at [Conv] —
  [cumul_eta_l]'s premise ([PCUICCumulativitySpecEta.v:168-170]),
  [cumulE_Sym]'s premise ([:40-42]), and [cumul_eta_r], built from both
  ([:746-751]). [cumulE_Ind]/[cumulE_Construct] at the ambient [pb] are reachable
  only when the head carries [#|args|] arguments, i.e. the fully applied case. So
  the spec has no [Cumul]-specific route for an under-applied head, and F-inst at
  [pb] would break A4 (join ⇒ spec).

  The [Conv] pin is also what makes the RISKIEST lemma go through. At [Conv],
  [cmp_universe_variance] is [True] at [Irrelevant] and plain
  [on_rel (cmp_univ Conv)] at both [Covariant] and [Invariant]
  ([PCUICEquality.v:36-41]), so the per-component relation is an equivalence and
  the disjunction in [cmp_opt_variance] composes. At [pb = Cumul] it would not.
  See [cmp_global_instance_eta_trans].

  This file redefines NOTHING that is landed. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import RelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive
     PCUICInduction PCUICEquality.

Local Open Scope type_scope.

(** ** The hole: how F-inst treats constructors *)

Variant finst_construct_rule :=
  | FInstFollowSpec
  (** [ConstructRef] as base does it: [AllIrrelevant] once fully applied. *)
  | FInstFollowKernel.
  (** The kernel's rule: instance EQUALITY when the inductive is not cumulative
      ([ind_variance = None]). *)

(** **THE CONSTRUCTOR CLAUSE IS AN OPEN HOLE, pending FRAC's gate (2026-10-28).**

  **AND THE RULING LEAVES ONE THING OPEN THAT BITES HERE.** The stream lead has
  NOT authorised changing the BASE spec; the spec repair
  ([global_variance_gen]'s [ConstructRef] case → [AllEqual] when not cumulative)
  is being SCOPED as a cost, not built. So once U1' follows the kernel and the
  spec still does not, **I5's spec ⇒ join direction is FALSE** on the witness
  [Q@{u} (p1@{u} unit)] against [Q@{v} (p1@{v} unit)]: the spec relates them
  (through [ConstructRef]'s [AllIrrelevant]) and the join, following the kernel,
  refuses them.

  **So: I5 HOLDS ONLY ONCE THE BASE-SPEC [ConstructRef] REPAIR LANDS.** Do NOT
  attempt the spec ⇒ join direction for constructors before that repair exists —
  it is false today, and no proof effort will change that. See
  [lanes/eta/spec-faithfulness-constructor.md].


  The measurement landed and it went the other way from the first report. The
  non-cumulative constructor pair is NOT unreachable at typing: the direct
  posing [@eq (P1@{u} unit) (p1@{u} unit) (p1@{v} unit)] is refused, but
  wrapping it in a cumulative inductive with an Irrelevant universe in a
  PARAMETER's type, [Q@{*w} (x : P1@{w} unit)], makes
  [Q@{u} (p1@{u} unit) = Q@{v} (p1@{v} unit)] WELL-TYPED. The kernel then
  compares the arguments at [Conv] and REFUSES [p1@{u}] vs [p1@{v}], because
  [P1] is non-cumulative, while MetaRocq's base spec ACCEPTS, since
  [global_variance_gen]'s [ConstructRef] case ([PCUICEquality.v:59-68]) returns
  [AllIrrelevant] without ever reading [ind_variance]. (Evidence
  [lanes/eta/spec-faithfulness-constructor.md], [kernel5.log]:
  [STATUS base1_noncum coqc=1] against the cumulative control [base2_cum] at
  [coqc=0].)

  **That is a PRE-EXISTING defect in the BASE spec, not in this route** — the
  witness has no λ, so η and [canon] are not implicated. Repairing
  [global_variance_gen] itself is the stream lead's call and [PCUICEquality.v]
  is NOT touched here. What IS this lane's obligation is the one line below:
  **U1' must not COPY the defect.** If F-inst followed the spec's present
  [ConstructRef] behaviour, the restated I5 would inherit an over-acceptance the
  kernel refuses, and a repaired route that is faithful to an unfaithful spec
  buys nothing.

  The parameterisation is kept rather than deleted, because it is what makes the
  difference between the two rules checkable, and because it costs nothing: every
  lemma below is proved for both. *)

(** **THE HOLE IS STILL OPEN. [finst_rule] is deliberately NOT defined.**
    Option (b), following the spec's [AllIrrelevant], is RULED OUT: under
    decision (C) an acceptance beyond the kernel is allowed only for ILL-TYPED
    terms, and this witness is WELL-TYPED, so keeping it would knowingly certify
    a defect. Option (a), repairing the base spec's [ConstructRef] case, is the
    stream lead's recommendation, but it changes I1 — the base spec the checker
    and everything downstream rest on — so it goes to FRAC and needs its own
    gate. Whether the SPEC changes decides what this clause must be, so pinning
    it now would bet on a ruling not yet made. Everything below is therefore
    proved for BOTH values of [r]. *)

(** ** Full arity of a head

  [IndRef]: the assumptions among parameters and indices, exactly the count
  [global_variance_gen] tests ([PCUICEquality.v:51]).
  [ConstructRef]: [cstr_arity + ind_npars], exactly the count tested at [:62].
  An absent declaration keeps arity [0], so F-inst then agrees with base on the
  [AllEqual] fallback. *)

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

(** Is the head a constructor of a NON-cumulative inductive? That is the only
    thing [FInstFollowKernel] needs beyond the spec rule. *)
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

(** The variance lookup F-inst uses: the base one at the head's FULL arity,
    except that under [FInstFollowKernel] a non-cumulative constructor keeps
    instance equality. *)
Definition global_variance_eta_gen (r : finst_construct_rule) lookup gr napp :=
  if match r with
     | FInstFollowSpec => false
     | FInstFollowKernel => noncumulative_constructor_gen lookup gr
     end
  then AllEqual
  else global_variance_gen lookup gr (max napp (head_arity_gen lookup gr)).

Notation global_variance_eta r Σ := (global_variance_eta_gen r (lookup_env Σ)).

(** **The napp drop disappears.** This holds for BOTH rules, so it does not wait
    on the measurement. It is the whole content of the R3(a) repair. *)
Lemma global_variance_eta_napp_irrelevant r lookup gr napp napp' :
  global_variance_eta_gen r lookup gr napp = global_variance_eta_gen r lookup gr napp'.
Proof.
  unfold global_variance_eta_gen.
  destruct (match r with FInstFollowSpec => false | _ => _ end); [reflexivity|].
  unfold global_variance_gen, head_arity_gen.
  destruct gr as [id|kn|ind|ind k]; cbn; try reflexivity.
  - destruct (lookup_inductive_gen lookup ind) as [[mdecl idecl]|]; [|reflexivity].
    now rewrite !(proj2 (Nat.leb_le _ _) (Nat.le_max_r _ _)).
  - destruct (lookup_constructor_gen lookup ind k) as [[[mdecl idecl] cdecl]|];
      [|reflexivity].
    now rewrite !(proj2 (Nat.leb_le _ _) (Nat.le_max_r _ _)).
Qed.

(** **After repair (a) the two rules coincide** (8780a014, "Use instance equality
    for fully applied non-cumulative constructors", cherry-picked with [-x]).
    Base [global_variance_gen] now gives [AllEqual] to a fully applied
    constructor of a NON-cumulative inductive — exactly what
    [FInstFollowKernel]'s extra branch returns. So for BOTH values of [r],
    [global_variance_eta_gen] is base's variance at the full arity, and
    [FInstFollowKernel]'s extra branch is redundant. *)
Lemma global_variance_eta_base r lookup gr napp :
  global_variance_eta_gen r lookup gr napp
  = global_variance_gen lookup gr (max napp (head_arity_gen lookup gr)).
Proof.
  unfold global_variance_eta_gen. destruct r; [reflexivity|].
  destruct gr as [id|kn|ind|ind k]; try reflexivity.
  unfold noncumulative_constructor_gen, global_variance_gen, head_arity_gen.
  destruct (lookup_constructor_gen lookup ind k) as [[[mdecl idecl] cdecl]|]; [|reflexivity].
  destruct (ind_variance mdecl); [reflexivity|].
  now destruct (_ <=? _).
Qed.

Lemma global_variance_eta_rule_irrelevant r r' lookup gr napp :
  global_variance_eta_gen r lookup gr napp = global_variance_eta_gen r' lookup gr napp.
Proof. now rewrite !global_variance_eta_base. Qed.

(** ** The F-inst instance comparison — CORRECTION of 5b9cd4ff (2026-10-28)

  5b9cd4ff compared EVERY head at [Conv]. That was WRONG for heads applied to at
  least their arity: base [eq_Ind]/[eq_Construct] ([PCUICEquality.v:427], [:431])
  and the spec's [cumulE_Ind]/[cumulE_Construct]
  ([PCUICCumulativitySpecEta.v:51-59]) compare those at [pb], so a fully applied
  cumulative inductive at [Cumul] ([Box@{+u} ≤ Box@{v}], [u < v]) was
  spec-related but join-refused, and A2 was false
  ([finst_cumulative_box_witness] below now holds). The lane lead's [Conv]
  correction was about UNDER-applied heads — every spec route relating one is an
  η detour at [Conv] — and EtaL2 over-applied it to all heads.

  The comparison MODE is now read from [napp]: [pb] when the head carries at
  least its arity, [Conv] (with the full-arity variance) below it. The variance
  lookup is unchanged. R3(a) stays deleted: the η drop goes from [(Conv, n)] to
  [(pb, m)], and [finst_Conv_pb] shows that is monotone. *)

Definition finst_mode (Σ : global_env) (gr : global_reference) (pb : conv_pb) (napp : nat) :=
  if head_arity Σ gr <=? napp then pb else Conv.

Definition cmp_global_instance_eta r Σ cmp_universe pb gr napp :=
  cmp_opt_variance cmp_universe (finst_mode Σ gr pb napp) (global_variance_eta r Σ gr napp).

(** ** The instance comparison is an equivalence

  Transitivity was flagged as the riskiest step because [cmp_opt_variance] at
  [Variance v] is a disjunction ([PCUICEquality.v:79]). It is base's proof
  ([cmp_global_instance_trans], [:614-628]) with [cmp_opt_variance_or_impl],
  verbatim in structure: base never inspects where the variance or the mode came
  from. With the mode now [pb] or [Conv], every hypothesis base needs is required
  at BOTH, and is discharged at the actual mode by [finst_mode_cases]. All hold
  for BOTH values of the constructor hole [r]. *)

Lemma finst_mode_cases (P : conv_pb -> Type) Σ gr pb napp :
  P Conv -> P pb -> P (finst_mode Σ gr pb napp).
Proof. intros hC hp. unfold finst_mode. now destruct (_ <=? _). Qed.

Section FInstInstance.
  Context (r : finst_construct_rule) (Σ : global_env)
          (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop).

  Lemma cmp_global_instance_eta_refl pb gr napp :
    RelationClasses.Reflexive (cmp_universe Conv) ->
    RelationClasses.Reflexive (cmp_universe pb) ->
    RelationClasses.Reflexive (cmp_global_instance_eta r Σ cmp_universe pb gr napp).
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
    RelationClasses.Symmetric (cmp_global_instance_eta r Σ cmp_universe pb gr napp).
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

  (** The step this lane called riskiest; base's own combinator closes it. *)
  Lemma cmp_global_instance_eta_trans pb gr napp :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    RelationClasses.Transitive (cmp_universe Conv) ->
    RelationClasses.Transitive (cmp_universe pb) ->
    RelationClasses.Transitive (cmp_global_instance_eta r Σ cmp_universe pb gr napp).
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
    cmp_global_instance_eta r Σ cmp_universe pb gr napp u u'.
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

  (** **Item (3) of the lane lead's approval: the [(Conv, n) → (pb, m)]
      monotonicity the η drop relies on.** At [Conv] the mode is [Conv] for
      every [napp]; the variance does not read [napp]
      ([global_variance_eta_napp_irrelevant]); and a [Conv]-mode comparison
      implies the [pb]-mode or [Conv]-mode one at [m]. *)
  Lemma finst_Conv_pb pb gr n m u u' :
    RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pb) ->
    cmp_global_instance_eta r Σ cmp_universe Conv gr n u u' ->
    cmp_global_instance_eta r Σ cmp_universe pb gr m u u'.
  Proof.
    intros sub. unfold cmp_global_instance_eta.
    have -> : finst_mode Σ gr Conv n = Conv by unfold finst_mode; now destruct (_ <=? _).
    rewrite (global_variance_eta_napp_irrelevant r (lookup_env Σ) gr n m).
    apply cmp_opt_variance_Conv_sub.
    exact (finst_mode_cases (fun pm => RelationClasses.subrelation (cmp_universe Conv) (cmp_universe pm))
             _ _ _ _ (fun x y h => h) sub).
  Qed.

End FInstInstance.

(** **Item (1) of the lane lead's approval: the [Box@{+u}] witness now HOLDS.**
    A cumulative inductive with no parameters and no indices (arity 0), one
    [Covariant] universe, compared at [Cumul] with [napp 0] and no arguments:
    [u ≤ v] suffices. Under 5b9cd4ff this demanded [u = v], which is why A2 was
    false. Stated for ANY such declared inductive, at BOTH constructor rules. *)
Lemma finst_cumulative_box_witness r (Σ : global_env) cmp_universe i mdecl idecl u v :
  declared_inductive_gen (lookup_env Σ) i mdecl idecl ->
  ind_params mdecl = [] -> ind_indices idecl = [] ->
  ind_variance mdecl = Some [Variance.Covariant] ->
  on_rel (cmp_universe Cumul) Universe.make' u v ->
  cmp_global_instance_eta r Σ cmp_universe Cumul (IndRef i) 0 [u] [v].
Proof.
  intros hd hp hi hv huv.
  have hl := declared_inductive_lookup_gen hd.
  unfold cmp_global_instance_eta, finst_mode, global_variance_eta_gen, head_arity_gen.
  rewrite hl hp hi; cbn.
  have -> : (match r with FInstFollowSpec => false
             | FInstFollowKernel => noncumulative_constructor_gen (lookup_env Σ) (IndRef i) end) = false
    by now destruct r.
  unfold global_variance_gen. rewrite hl hp hi hv; cbn.
  right. constructor; [exact huv|constructor].
Qed.

(** **Hypotheses satisfiable (FRAC's standing rule).** The corrected
    transitivity's three premises are met by the REAL comparison
    [compare_universe φ], at every [pb], for EVERY [φ] — no well-formedness
    needed: [compare_universe φ Conv] is [eq_universe φ], transitive by
    [eq_universe_trans]; [compare_universe φ pb] is transitive by
    [compare_universe_trans]; and [eq_universe φ ⊆ compare_universe φ pb] is
    [compare_universe_subrel] ([Universes.v:1329], [:1417], [:1407]). This
    corollary is that statement, checked. *)
Lemma cmp_global_instance_eta_trans_compare {cf : checker_flags} r Σ φ pb gr napp :
  RelationClasses.Transitive (cmp_global_instance_eta r Σ (compare_universe φ) pb gr napp).
Proof.
  apply cmp_global_instance_eta_trans.
  - exact (compare_universe_subrel φ pb).
  - exact (eq_universe_trans φ).
  - exact (compare_universe_trans φ pb).
Qed.

(** ** U1', carrying the open constructor clause

  The term-level relation, parameterised by the open clause [r] so that it is
  usable now and pins itself the moment the gate rules.
  It is a faithful copy of [eq_term_upto_univ_napp] ([PCUICEquality.v:399-474])
  with EXACTLY TWO constructors changed, [eq_Ind] and [eq_Construct] — the only
  two that read [napp]. Every other constructor is base's. The copy is
  unavoidable: [napp] is threaded through the inductive, so the variance lookup
  cannot be swapped from outside. *)

Definition cmp_global_instance_finst r Σ cmp_universe pb gr napp :=
  cmp_global_instance_eta r Σ cmp_universe pb gr napp.

(** [r] is a SECTION variable, not an inductive parameter: the recursive
    notation below cannot infer it from a [_]. Discharging the section gives it
    back as the first argument of every definition here. *)
Section FInstRelation.
Context (r : finst_construct_rule).

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
    cmp_global_instance_finst r Σ cmp_universe pb (IndRef i) napp u u' ->
    Σ ⊢ tInd i u <==η[ pb , napp ] tInd i u'

| eqη_Construct : forall i k u u',
    cmp_global_instance_finst r Σ cmp_universe pb (ConstructRef i k) napp u u' ->
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

(** **U1'. The comparison obligation 8's restated I5 ends in — STILL CARRYING
    THE OPEN CONSTRUCTOR CLAUSE [r], which FRAC's gate decides.** *)
Definition compare_term_eta `{checker_flags} Σ φ (pb : conv_pb) (t u : term) :=
  compare_term_eta_napp Σ φ pb 0 t u.

End FInstRelation.

Derive Signature for eq_term_upto_univ_eta_napp.

(** ** U1' does not copy the base spec's constructor defect

  The whole point of pinning the constructor clause at the kernel's rule. For a
  constructor of a NON-cumulative inductive, F-inst demands instance EQUALITY,
  where base's [global_variance_gen] would return [AllIrrelevant] and demand
  only equal lengths. *)

Lemma finst_noncumulative_constructor_AllEqual lookup gr napp :
  noncumulative_constructor_gen lookup gr = true ->
  global_variance_eta_gen FInstFollowKernel lookup gr napp = AllEqual.
Proof.
  intros h. unfold global_variance_eta_gen. now rewrite h.
Qed.

(** The same fact as the lane states it: a non-cumulative constructor head is
    compared by instance equality, exactly as [conversion.ml:221-222] does, and
    NOT by [AllIrrelevant]. *)
Lemma finst_noncumulative_constructor_instance_eq Σ cmp_universe pb ind k napp u u' :
  noncumulative_constructor_gen (lookup_env Σ) (ConstructRef ind k) = true ->
  cmp_global_instance_finst FInstFollowKernel Σ cmp_universe pb (ConstructRef ind k) napp u u' ->
  cmp_universe_instance (cmp_universe Conv) u u'.
Proof.
  intros hnc h.
  unfold cmp_global_instance_finst, cmp_global_instance_eta in h.
  now rewrite (finst_noncumulative_constructor_AllEqual _ _ napp hnc) in h.
Qed.
