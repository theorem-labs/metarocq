(* Distributed under the terms of the MIT license. *)
(** * The premise of the confluence spine: closed constant bodies and fresh names

  Base confluence ([PCUICParallelReduction], [PCUICParallelReductionConfluence],
  [PCUICConfluence]) used to assume [wf Σ]. The compiler shows it needs only two
  facts about the environment, which [ClosedBodies Σ] states:
  - [closed_bodies]: the body of a declared constant is closed (the δ cases:
    [PCUICParallelReduction.v] [pred1_rename] and [strong_substitutivity],
    [PCUICParallelReductionConfluence.v] [rho_rename] and [pred1_rho]'s δ case);
  - [fresh_names]: declaration names are pairwise distinct, so a constant in the
    declaration list is the one [lookup_env] returns ([declared_constant_to_gen],
    used by the primitive-operation cases of [PCUICParallelReductionConfluence.v]).

  Both are consequences of [on_global_env Pcmp P] for ANY [Pcmp]/[P]: the instance
  from [wf] is [wf_ClosedBodies]; an environment checked with another
  conversion relation (BET-315's [wfE]) gives its own instance the same way.
  The instance from [wf] is in [Typing/PCUICClosedTyp.v], after
  [declared_constant_closed_body]; this file comes before it, because
  [PCUICClosedTyp]'s own reduction lemmas are stated under the class. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping.
From Stdlib Require Import ssreflect.

(** The class is ABSTRACT: a module sealed by a signature exports the type, its
    constructor and its two projections, and nothing else. Statements over
    [ClosedBodies Σ] then behave as the [wf Σ] statements they generalise: the same
    [Type] sort, the same section-variable structure and automatic hypothesis names,
    and no tactic ([firstorder], [eauto]) can unfold it into its fields (a
    transparent record would be decomposed by [firstorder], which then applies the
    closed-bodies field and leaves an unsolvable [kername] goal). The
    [checker_flags] parameter is unused by the property; it keeps the dependency on
    [cf] that the [wf] statements had. *)
Module Type ClosedBodiesSig.
  Parameter ClosedBodies : forall {cf : checker_flags}, global_env -> Type.
  Parameter closed_bodies : forall {cf : checker_flags} {Σ : global_env} {cb : ClosedBodies Σ}
    cst decl body,
    declared_constant Σ cst decl -> decl.(cst_body) = Some body -> closed body.
  Parameter fresh_names : forall {cf : checker_flags} {Σ : global_env} {cb : ClosedBodies Σ},
    NoDup (List.map fst (declarations Σ)).
  Parameter Build_ClosedBodies : forall {cf : checker_flags} (Σ : global_env)
    (h : forall cst decl body,
      declared_constant Σ cst decl -> decl.(cst_body) = Some body -> closed body)
    (f : NoDup (List.map fst (declarations Σ))), ClosedBodies Σ.
End ClosedBodiesSig.

Module ClosedBodiesImpl : ClosedBodiesSig.
  Record ClosedBodies_ {cf : checker_flags} (Σ : global_env) : Type := {
    cbd_closed : forall cst decl body,
      declared_constant Σ cst decl -> decl.(cst_body) = Some body -> closed body;
    cbd_fresh : NoDup (List.map fst (declarations Σ))
  }.
  Definition ClosedBodies {cf : checker_flags} (Σ : global_env) := ClosedBodies_ Σ.
  Definition closed_bodies {cf : checker_flags} {Σ : global_env} {cb : ClosedBodies Σ} :=
    @cbd_closed cf Σ cb.
  Definition fresh_names {cf : checker_flags} {Σ : global_env} {cb : ClosedBodies Σ} :=
    @cbd_fresh cf Σ cb.
  Definition Build_ClosedBodies {cf : checker_flags} (Σ : global_env) h f : ClosedBodies Σ :=
    @Build_ClosedBodies_ cf Σ h f.
End ClosedBodiesImpl.
Export ClosedBodiesImpl.
Existing Class ClosedBodies.

Section ToGen.
  Context {cf : checker_flags} {Σ : global_env} {cb : ClosedBodies Σ}.

  (** [declared_constant_to_gen] under [ClosedBodies]. *)
  Lemma cb_declared_constant_to_gen {kn cdecl} :
    declared_constant Σ kn cdecl -> declared_constant_gen (lookup_env Σ) kn cdecl.
  Proof using cb.
    intro H; eapply lookup_global_Some_iff_In_NoDup in H; [|exact fresh_names].
    apply lookup_constant_declared_gen => //.
    unfold lookup_constant_gen, lookup_env.
    destruct (lookup_global _ _) => //.
    destruct g => //. now inversion H.
  Qed.

  Lemma cb_declared_minductive_to_gen {ind mdecl} :
    declared_minductive Σ ind mdecl -> declared_minductive_gen (lookup_env Σ) ind mdecl.
  Proof using cb.
    intro H; eapply lookup_global_Some_iff_In_NoDup in H; [|exact fresh_names].
    apply lookup_minductive_declared_gen => //.
    unfold lookup_minductive_gen, lookup_env.
    destruct (lookup_global _ _) => //.
    destruct g => //. now inversion H.
  Qed.

  Lemma cb_declared_inductive_to_gen {ind mdecl idecl} :
    declared_inductive Σ ind mdecl idecl -> declared_inductive_gen (lookup_env Σ) ind mdecl idecl.
  Proof using cb. intros []; split => //. now eapply cb_declared_minductive_to_gen. Qed.

  Lemma cb_declared_constructor_to_gen {id mdecl idecl cdecl} :
    declared_constructor Σ id mdecl idecl cdecl ->
    declared_constructor_gen (lookup_env Σ) id mdecl idecl cdecl.
  Proof using cb. intros []; split => //. now eapply cb_declared_inductive_to_gen. Qed.
End ToGen.
