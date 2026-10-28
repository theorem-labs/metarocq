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

(** The F-inst instance comparison. Pinned at [Conv]; see the header. *)
Definition cmp_global_instance_eta r Σ cmp_universe gr napp :=
  cmp_opt_variance cmp_universe Conv (global_variance_eta r Σ gr napp).

(** ** The instance comparison is an equivalence

  This lane flagged TRANSITIVITY as the riskiest step of the restatement,
  because [cmp_opt_variance] at [Variance v] is a DISJUNCTION
  ([PCUICEquality.v:79]) and a composition can take different disjuncts on each
  side. **It closed immediately, and it does not move the cost.** Base already
  owns the combinator for exactly this, [cmp_opt_variance_or_impl]
  ([PCUICEquality.v:140-...]), and uses it to prove [cmp_global_instance_trans]
  ([:614-628]). Our relation has the same SHAPE — [cmp_opt_variance] applied to
  a variance VALUE — and base's proofs never inspect where that value came from,
  only that it is one of the three constructors. So the three proofs below are
  base's, verbatim in structure, over [global_variance_eta_gen] instead of
  [global_variance_gen].

  The [Conv] pin pays for itself a second time here. Base's transitivity needs
  [subrelation (cmp_universe Conv) (cmp_universe pb)]; at [pb := Conv] that
  hypothesis is free. At [Cumul] it would have to be carried.

  All three hold for BOTH values of the constructor hole. *)

Section FInstInstance.
  Context (r : finst_construct_rule) (Σ : global_env)
          (cmp_universe : conv_pb -> Universe.t -> Universe.t -> Prop).

  Lemma cmp_global_instance_eta_refl gr napp :
    RelationClasses.Reflexive (cmp_universe Conv) ->
    RelationClasses.Reflexive (cmp_global_instance_eta r Σ cmp_universe gr napp).
  Proof.
    intros univ_refl.
    unfold cmp_global_instance_eta.
    destruct global_variance_eta_gen as [| |v] => //= u.
    - now apply cmp_universe_instance_refl.
    - left. now apply cmp_universe_instance_refl.
  Qed.

  Lemma cmp_global_instance_eta_sym gr napp :
    RelationClasses.Symmetric (cmp_universe Conv) ->
    RelationClasses.Symmetric (cmp_global_instance_eta r Σ cmp_universe gr napp).
  Proof.
    intros univ_sym.
    unfold cmp_global_instance_eta.
    destruct global_variance_eta_gen as [| |v] => //= u u'.
    - now symmetry.
    - intros [H | H]; [left|right].
      all: now symmetry.
  Qed.

  (** The step this lane called riskiest. See the section header: it closed with
      base's own combinator, in the hour it was attacked. *)
  Lemma cmp_global_instance_eta_trans gr napp :
    RelationClasses.Transitive (cmp_universe Conv) ->
    RelationClasses.Transitive (cmp_global_instance_eta r Σ cmp_universe gr napp).
  Proof.
    intros univ_trans.
    assert (univ_sub : RelationClasses.subrelation (cmp_universe Conv) (cmp_universe Conv))
      by (intros x y h; exact h).
    unfold cmp_global_instance_eta.
    destruct global_variance_eta_gen as [| |v] => //= u u' u''.
    1,2: now etransitivity.
    apply cmp_opt_variance_or_impl; tas.
    all: now etransitivity.
  Qed.

  (** Base [compare_term]'s instance comparison implies F-inst's: one
      [cmp_instance_opt_variance] ([PCUICEquality.v:102-109], i.e.
      [AllEqual ⊆ v]). **This is the lemma that keeps [isconv_sound] untouched**:
      the checker keeps base [compare_term] (SC3, K2), and base ⊆ F-inst, so
      "checker accepts ⊆ algorithmic ⊆ spec" survives the widening. *)
  Lemma cmp_global_instance_eta_weaken gr napp u u' :
    cmp_universe_instance (cmp_universe Conv) u u' ->
    cmp_global_instance_eta r Σ cmp_universe gr napp u u'.
  Proof.
    intros h. unfold cmp_global_instance_eta.
    now apply (cmp_instance_opt_variance cmp_universe Conv _ u u').
  Qed.

End FInstInstance.
