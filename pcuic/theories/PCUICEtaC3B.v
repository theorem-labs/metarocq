(* Distributed under the terms of the MIT license. *)

(** * C3 (strong commutation modulo [upto_domain]) via a parallel η relation.

  Prover B's route (plan.md §6 rank-1 fallback: parallel η). We build a parallel
  η-reduction [peta] (one step contracts any set of η-redexes + full reflexive
  congruence) against the SHARED [eta1]/[upto_domain] of [PCUICEtaDefs], prove a
  clean local commutation of [peta] with single-step [red1], and derive C3.

  NO [Admitted], NO new [Axiom]. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICPrimitive
     PCUICInduction PCUICLiftSubst PCUICEquality PCUICReduction PCUICEtaDefs.

Import ListNotations.

Set Default Goal Selector "!".

Derive Signature for eta1.
Derive Signature for upto_domain.

(** ** [upto_domain] is reflexive *)

#[local] Instance upto_domain_refl : Reflexive upto_domain.
Proof.
  intros t.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. now apply All_All2 with (1 := X).
  - (* tCase *)
    destruct X as (Hpars & _ & Hret).
    constructor.
    + now apply All_All2 with (1 := Hpars).
    + reflexivity.
    + reflexivity.
    + exact Hret.
    + assumption.
    + apply All_All2 with (1 := X0). intros x [_ Hb].
      split; [reflexivity|exact Hb].
  - (* tFix *)
    constructor. apply All_All2 with (1 := X).
    intros d [Ht Hb]. repeat split; auto.
  - (* tCoFix *)
    constructor. apply All_All2 with (1 := X).
    intros d [Ht Hb]. repeat split; auto.
  - (* tPrim *)
    constructor.
    destruct p as [? []]; cbn in X |- *.
    1-3: constructor.
    destruct X as (Ht & Hd & Hv).
    constructor.
    + reflexivity.
    + exact Hd.
    + exact Ht.
    + now apply All_All2 with (1 := Hv).
Qed.

(** ** Parallel η-reduction [peta]

  One step reduces any set of η-redexes at once, with full reflexive congruence.
  [peta_eta] is the only non-structural rule: it η-contracts a [tLambda]-headed
  η-redex while reducing its body in parallel. *)

Inductive peta : term -> term -> Type :=
| peta_eta na A M M' :
    peta M M' ->
    peta (tLambda na A (tApp (lift0 1 M) (tRel 0))) M'

| peta_Rel n : peta (tRel n) (tRel n)
| peta_Var i : peta (tVar i) (tVar i)
| peta_Sort s : peta (tSort s) (tSort s)
| peta_Const c u : peta (tConst c u) (tConst c u)
| peta_Ind ind u : peta (tInd ind u) (tInd ind u)
| peta_Construct ind n u : peta (tConstruct ind n u) (tConstruct ind n u)

| peta_Evar ev l l' :
    All2 peta l l' ->
    peta (tEvar ev l) (tEvar ev l')

| peta_Lambda na A A' M M' :
    peta A A' -> peta M M' ->
    peta (tLambda na A M) (tLambda na A' M')

| peta_App t t' u u' :
    peta t t' -> peta u u' ->
    peta (tApp t u) (tApp t' u')

| peta_Prod na a a' b b' :
    peta a a' -> peta b b' ->
    peta (tProd na a b) (tProd na a' b')

| peta_LetIn na b b' ty ty' u u' :
    peta b b' -> peta ty ty' -> peta u u' ->
    peta (tLetIn na b ty u) (tLetIn na b' ty' u')

| peta_Case ci p p' c c' brs brs' :
    All2 peta p.(pparams) p'.(pparams) ->
    p.(puinst) = p'.(puinst) ->
    p.(pcontext) = p'.(pcontext) ->
    peta p.(preturn) p'.(preturn) ->
    peta c c' ->
    All2 (fun x y => x.(bcontext) = y.(bcontext) × peta x.(bbody) y.(bbody)) brs brs' ->
    peta (tCase ci p c brs) (tCase ci p' c' brs')

| peta_Proj pr c c' :
    peta c c' ->
    peta (tProj pr c) (tProj pr c')

| peta_Fix mfix mfix' idx :
    All2 (fun d d' => peta d.(dtype) d'.(dtype) × peta d.(dbody) d'.(dbody)
                      × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
    peta (tFix mfix idx) (tFix mfix' idx)

| peta_CoFix mfix mfix' idx :
    All2 (fun d d' => peta d.(dtype) d'.(dtype) × peta d.(dbody) d'.(dbody)
                      × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
    peta (tCoFix mfix idx) (tCoFix mfix' idx)

| peta_Prim p p' :
    onPrims peta eq p p' ->
    peta (tPrim p) (tPrim p').

Derive Signature for peta.

(** ** Reflexivity of [peta] *)

#[local] Instance peta_refl : Reflexive peta.
Proof.
  intros t.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. now apply All_All2 with (1 := X).
  - (* tCase *)
    destruct X as (Hpars & _ & Hret).
    constructor.
    + now apply All_All2 with (1 := Hpars).
    + reflexivity.
    + reflexivity.
    + exact Hret.
    + assumption.
    + apply All_All2 with (1 := X0). intros x [_ Hb]. split; auto.
  - (* tFix *)
    constructor. apply All_All2 with (1 := X).
    intros d [Ht Hb]. repeat split; auto.
  - (* tCoFix *)
    constructor. apply All_All2 with (1 := X).
    intros d [Ht Hb]. repeat split; auto.
  - (* tPrim *)
    constructor.
    destruct p as [? []]; cbn in X |- *.
    1-3: constructor.
    destruct X as (Ht & Hd & Hv).
    constructor.
    + reflexivity.
    + exact Hd.
    + exact Ht.
    + now apply All_All2 with (1 := Hv).
Qed.
