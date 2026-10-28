(* Distributed under the terms of the MIT license. *)
(** * Closed constant bodies and fresh names, the premise of the reduction metatheory

  Parallel reduction, confluence and the reduction/conversion lemmas built on them
  used to assume [wf Σ]. They need only two facts about the environment, which
  [ClosedBodies Σ] states:
  - [closed_bodies]: the body of a declared constant is closed. It serves the δ cases
    of [pred1_rename] and [strong_substitutivity] ([PCUICParallelReduction]), of
    [rho_rename] and [pred1_on_free_vars_gen] ([PCUICParallelReductionConfluence]), of
    [red1_rename] ([PCUICRenameConv]), [red1_inst] ([PCUICInstConv]) and
    [red1_on_free_vars] ([PCUICClosedTyp]).
  - [fresh_names]: declaration names are pairwise distinct, so a constant in the
    declaration list is the one [lookup_env] returns ([cb_declared_constant_to_gen]).
    It serves the primitive-operation cases and the δ case of [triangle_gen]
    ([PCUICParallelReductionConfluence]) and [invert_red_axiom] ([PCUICConversion]).

  [fresh_names] holds for any [on_global_env Pcmp P] ([NoDup_on_global_decls]).
  [closed_bodies] comes from typing: the instance from [wf] is [wf_ClosedBodies], in
  [Typing/PCUICClosedTyp.v] after [declared_constant_closed_body]; a typing judgement
  that implies closed constant bodies gives its own instance the same way. This file
  comes before [PCUICClosedTyp], because that file's own reduction lemmas are stated
  under the class. *)
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

End ToGen.
