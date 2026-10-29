(* Distributed under the terms of the MIT license. *)

(** * The two shared η relations

  - [eta1]: one η-contraction step plus congruences, ported to the 9.2 AST from
    upstream MetaRocq branch [eta_postpo], [pcuic/theories/PCUICConversionDef.v];
  - [upto_domain]: syntactic equality that ignores λ domains, λ binder
    annotations, [tProd]/[tLetIn] binder names and fix/cofix [dname], ported from
    that branch's [pcuic/theories/PCUICEquality.v].

  Neither upstream file is in this tree. The 9.2 reconciliation adds exactly what
  the newer AST carries and the 2020 AST lacked: the [tCase] predicate is now a
  record (so the single 2020 case-predicate congruence splits into
  [case_eta_param] on [pparams] and [case_eta_return] on [preturn], mirroring base
  [red1]'s [case_red_param]/[case_red_return]); branches and case/branch contexts
  are records ([bbody]/[bcontext], compared with [eq_context_upto_names] exactly as
  base [eq_predicate]/[eq_branch]); and primitive arrays appear ([array_eta_*]
  congruences for [eta1], an [onPrims] case for [upto_domain], mirroring base
  [red1]'s [array_red_*] and base [eq_Prim]). [eta1] is context-free, as upstream. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICPrimitive
     PCUICLiftSubst PCUICEquality PCUICReduction.

Import ListNotations.

Set Default Goal Selector "!".

(** ** η-contraction redex

  [eta_redex na A t = λ (x : A). (lift0 1 t) x] — the η-long form of [t] under a
  binder of (irrelevant) domain [A]. *)

Notation " 'eta_redex' na A t " :=
  (tLambda na A (tApp (lift0 1 t) (tRel 0)))
  (at level 30, na at level 0, A at level 0, t at level 0).

(** ** One η-contraction step (+ congruences), 9.2 AST *)

Local Unset Elimination Schemes.

Inductive eta1 : term -> term -> Type :=
(* η-contraction at the head *)
| eta_red na t A :
    eta1 (eta_redex na A t) t

(* congruence: λ *)
| abs_eta_l na M M' N : eta1 M M' -> eta1 (tLambda na M N) (tLambda na M' N)
| abs_eta_r na M M' N : eta1 M M' -> eta1 (tLambda na N M) (tLambda na N M')

(* congruence: let *)
| letin_eta_def na b t b' r : eta1 b r -> eta1 (tLetIn na b t b') (tLetIn na r t b')
| letin_eta_ty na b t b' r : eta1 t r -> eta1 (tLetIn na b t b') (tLetIn na b r b')
| letin_eta_body na b t b' r : eta1 b' r -> eta1 (tLetIn na b t b') (tLetIn na b t r)

(* congruence: case (predicate params / return / discriminee / branch bodies) *)
| case_eta_param ci p params' c brs :
    OnOne2 eta1 p.(pparams) params' ->
    eta1 (tCase ci p c brs) (tCase ci (set_pparams p params') c brs)
| case_eta_return ci p preturn' c brs :
    eta1 p.(preturn) preturn' ->
    eta1 (tCase ci p c brs) (tCase ci (set_preturn p preturn') c brs)
| case_eta_discr ci p c c' brs :
    eta1 c c' -> eta1 (tCase ci p c brs) (tCase ci p c' brs)
| case_eta_brs ci p c brs brs' :
    OnOne2 (on_Trel_eq eta1 bbody bcontext) brs brs' ->
    eta1 (tCase ci p c brs) (tCase ci p c brs')

(* congruence: projection *)
| proj_eta pr c c' : eta1 c c' -> eta1 (tProj pr c) (tProj pr c')

(* congruence: application *)
| app_eta_l M1 N1 M2 : eta1 M1 N1 -> eta1 (tApp M1 M2) (tApp N1 M2)
| app_eta_r M2 N2 M1 : eta1 M2 N2 -> eta1 (tApp M1 M2) (tApp M1 N2)

(* congruence: product *)
| prod_eta_l na M1 M2 N1 : eta1 M1 N1 -> eta1 (tProd na M1 M2) (tProd na N1 M2)
| prod_eta_r na M2 N2 M1 : eta1 M2 N2 -> eta1 (tProd na M1 M2) (tProd na M1 N2)

(* congruence: evar *)
| evar_eta ev l l' : OnOne2 eta1 l l' -> eta1 (tEvar ev l) (tEvar ev l')

(* congruence: fix / cofix *)
| fix_eta_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    eta1 (tFix mfix0 idx) (tFix mfix1 idx)
| fix_eta_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    eta1 (tFix mfix0 idx) (tFix mfix1 idx)
| cofix_eta_ty mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
    eta1 (tCoFix mfix0 idx) (tCoFix mfix1 idx)
| cofix_eta_body mfix0 mfix1 idx :
    OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
    eta1 (tCoFix mfix0 idx) (tCoFix mfix1 idx)

(* congruence: primitive arrays *)
| array_eta_val arr value :
    OnOne2 eta1 arr.(array_value) value ->
    eta1 (tPrim (primArray; primArrayModel arr))
         (tPrim (primArray; primArrayModel (set_array_value arr value)))
| array_eta_def arr d :
    eta1 arr.(array_default) d ->
    eta1 (tPrim (primArray; primArrayModel arr))
         (tPrim (primArray; primArrayModel (set_array_default arr d)))
| array_eta_type arr ty :
    eta1 arr.(array_type) ty ->
    eta1 (tPrim (primArray; primArrayModel arr))
         (tPrim (primArray; primArrayModel (set_array_type arr ty))).

(** Strong induction principle for [eta1] (nested [OnOne2]-aware), ported from
    [origin/eta_postpo]'s [eta1_ind_all] and modelled on base [red1_ind_all]. *)
Lemma eta1_ind_all (P : term -> term -> Type) :

  (forall na (t A : term), P (eta_redex na A t) t) ->

  (forall na (M M' N : term),
   eta1 M M' -> P M M' -> P (tLambda na M N) (tLambda na M' N)) ->
  (forall na (M M' N : term),
   eta1 M M' -> P M M' -> P (tLambda na N M) (tLambda na N M')) ->

  (forall na (b t b' r : term),
   eta1 b r -> P b r -> P (tLetIn na b t b') (tLetIn na r t b')) ->
  (forall na (b t b' r : term),
   eta1 t r -> P t r -> P (tLetIn na b t b') (tLetIn na b r b')) ->
  (forall na (b t b' r : term),
   eta1 b' r -> P b' r -> P (tLetIn na b t b') (tLetIn na b t r)) ->

  (forall ci p params' c brs,
   OnOne2 (Trel_conj eta1 P) p.(pparams) params' ->
   P (tCase ci p c brs) (tCase ci (set_pparams p params') c brs)) ->
  (forall ci p preturn' c brs,
   eta1 p.(preturn) preturn' -> P p.(preturn) preturn' ->
   P (tCase ci p c brs) (tCase ci (set_preturn p preturn') c brs)) ->
  (forall ci p c c' brs,
   eta1 c c' -> P c c' -> P (tCase ci p c brs) (tCase ci p c' brs)) ->
  (forall ci p c brs brs',
   OnOne2 (on_Trel_eq (Trel_conj eta1 P) bbody bcontext) brs brs' ->
   P (tCase ci p c brs) (tCase ci p c brs')) ->

  (forall pr (c c' : term), eta1 c c' -> P c c' -> P (tProj pr c) (tProj pr c')) ->

  (forall (M1 N1 M2 : term), eta1 M1 N1 -> P M1 N1 -> P (tApp M1 M2) (tApp N1 M2)) ->
  (forall (M2 N2 M1 : term), eta1 M2 N2 -> P M2 N2 -> P (tApp M1 M2) (tApp M1 N2)) ->

  (forall na (M1 M2 N1 : term),
   eta1 M1 N1 -> P M1 N1 -> P (tProd na M1 M2) (tProd na N1 M2)) ->
  (forall na (M2 N2 M1 : term),
   eta1 M2 N2 -> P M2 N2 -> P (tProd na M1 M2) (tProd na M1 N2)) ->

  (forall ev (l l' : list term),
   OnOne2 (Trel_conj eta1 P) l l' -> P (tEvar ev l) (tEvar ev l')) ->

  (forall (mfix0 mfix1 : list (def term)) idx,
   OnOne2 (on_Trel_eq (Trel_conj eta1 P) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
   P (tFix mfix0 idx) (tFix mfix1 idx)) ->
  (forall (mfix0 mfix1 : list (def term)) idx,
   OnOne2 (on_Trel_eq (Trel_conj eta1 P) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
   P (tFix mfix0 idx) (tFix mfix1 idx)) ->
  (forall (mfix0 mfix1 : list (def term)) idx,
   OnOne2 (on_Trel_eq (Trel_conj eta1 P) dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix1 ->
   P (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->
  (forall (mfix0 mfix1 : list (def term)) idx,
   OnOne2 (on_Trel_eq (Trel_conj eta1 P) dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix1 ->
   P (tCoFix mfix0 idx) (tCoFix mfix1 idx)) ->

  (forall (arr : array_model term) value,
   OnOne2 (Trel_conj eta1 P) arr.(array_value) value ->
   P (tPrim (primArray; primArrayModel arr))
     (tPrim (primArray; primArrayModel (set_array_value arr value)))) ->
  (forall (arr : array_model term) d,
   eta1 arr.(array_default) d -> P arr.(array_default) d ->
   P (tPrim (primArray; primArrayModel arr))
     (tPrim (primArray; primArrayModel (set_array_default arr d)))) ->
  (forall (arr : array_model term) ty,
   eta1 arr.(array_type) ty -> P arr.(array_type) ty ->
   P (tPrim (primArray; primArrayModel arr))
     (tPrim (primArray; primArrayModel (set_array_type arr ty)))) ->

  forall t t0, eta1 t t0 -> P t t0.
Proof.
  intros Hredex Habsl Habsr Hletd Hletty Hletb Hparam Hreturn Hdiscr Hbrs
         Hproj Happl Happr Hprodl Hprodr Hevar Hfixty Hfixbody Hcofixty Hcofixbody
         Haval Hadef Haty.
  fix aux 3. intros t T.
  move aux at top.
  destruct 1;
    match goal with
    | |- P (tCase _ _ _ _) (tCase _ (set_pparams _ _) _ _) => idtac
    | |- P (tCase _ _ _ _) (tCase _ _ _ _) => idtac
    | |- P (tEvar _ _) (tEvar _ _) => idtac
    | |- P (tFix _ _) (tFix _ _) => idtac
    | |- P (tCoFix _ _) (tCoFix _ _) => idtac
    | |- P (tPrim _) (tPrim (primArray; primArrayModel (set_array_value _ _))) => idtac
    | H : _ |- _ => eapply H; eauto
    end.
  - (* case_eta_param *)
    eapply Hparam.
    revert params' o. generalize (pparams p).
    fix auxl 3. intros l l' Hl; destruct Hl.
    + constructor. split; auto.
    + constructor. auto.
  - (* case_eta_return *)
    eapply Hreturn; eauto.
  - (* case_eta_discr *)
    eapply Hdiscr; eauto.
  - (* case_eta_brs *)
    eapply Hbrs.
    revert brs' o. revert brs.
    fix auxl 3. intros l l' Hl; destruct Hl.
    + simpl in *. constructor; intros; intuition auto.
    + constructor. eapply auxl. apply Hl.
  - (* evar_eta *)
    eapply Hevar.
    revert l' o. generalize l.
    fix auxl 3. intros ll ll' Hl; destruct Hl.
    + constructor. split; auto.
    + constructor. auto.
  - (* fix_eta_ty *)
    eapply Hfixty.
    revert mfix1 o. generalize mfix0.
    fix auxl 3. intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
  - (* fix_eta_body *)
    eapply Hfixbody.
    revert mfix1 o. generalize mfix0.
    fix auxl 3. intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
  - (* cofix_eta_ty *)
    eapply Hcofixty.
    revert mfix1 o. generalize mfix0.
    fix auxl 3. intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
  - (* cofix_eta_body *)
    eapply Hcofixbody.
    revert mfix1 o. generalize mfix0.
    fix auxl 3. intros l l' Hl; destruct Hl;
      constructor; try split; auto; intuition.
  - (* array_eta_val *)
    eapply Haval.
    revert value o. generalize (array_value arr).
    fix auxl 3. intros l l' Hl; destruct Hl.
    + constructor. split; auto.
    + constructor. auto.
Defined.

(** [eta] : the reflexive-transitive closure of [eta1]. *)
Definition eta := clos_refl_trans eta1.

(** ** Syntactic equality up to λ domains

  Ignores λ domains, λ/Prod/LetIn binder annotations and fix/cofix [dname].
  Universe instances are compared by [eq]. *)

Inductive upto_domain : term -> term -> Type :=
(* Rel/Evar/Var/Sort/App/Const/Ind/Construct/Lambda/Prod/LetIn/Proj/Fix/CoFix below
   are the byte-for-byte 9.2 ports of the 2020 utd_* constructors
   (origin/eta_postpo:PCUICEquality.v:1439-1498); only utd_Case is reshaped for the
   9.2 predicate/branch records and utd_Prim is new (arrays), each noted inline. *)
| utd_Rel n : upto_domain (tRel n) (tRel n)                           (* = 2020 utd_Rel *)

| utd_Evar e args args' :                                            (* = 2020 utd_Evar *)
    All2 upto_domain args args' ->
    upto_domain (tEvar e args) (tEvar e args')

| utd_Var id : upto_domain (tVar id) (tVar id)                        (* = 2020 utd_Var *)

| utd_Sort s : upto_domain (tSort s) (tSort s)                        (* = 2020 utd_Sort *)

| utd_App t t' u u' :                                                 (* = 2020 utd_App *)
    upto_domain t t' ->
    upto_domain u u' ->
    upto_domain (tApp t u) (tApp t' u')

| utd_Const c u : upto_domain (tConst c u) (tConst c u)               (* = 2020 utd_Const *)

| utd_Ind i u : upto_domain (tInd i u) (tInd i u)                     (* = 2020 utd_Ind *)

| utd_Construct i k u : upto_domain (tConstruct i k u) (tConstruct i k u) (* = 2020 utd_Construct *)

| utd_Lambda na na' ty ty' t t' :                                     (* = 2020 utd_Lambda: ty,ty' ignored *)
    upto_domain t t' ->
    upto_domain (tLambda na ty t) (tLambda na' ty' t')

| utd_Prod na na' a a' b b' :                                         (* = 2020 utd_Prod: na,na' ignored *)
    upto_domain a a' ->
    upto_domain b b' ->
    upto_domain (tProd na a b) (tProd na' a' b')

| utd_LetIn na na' t t' ty ty' u u' :                                 (* = 2020 utd_LetIn: na,na' ignored *)
    upto_domain t t' ->
    upto_domain ty ty' ->
    upto_domain u u' ->
    upto_domain (tLetIn na t ty u) (tLetIn na' t' ty' u')

(* RESHAPED for 9.2: 2020 utd_Case related a single return-term p and
   `All2 (x.1=y.1 x upto_domain x.2 y.2)` branches. 9.2 predicate is a record, so we
   mirror base eq_predicate/eq_branch (PCUICEquality.v:368-378): params/return by
   upto_domain, puinst by eq, pcontext/bcontext by eq_context_upto_names. [risk-5] *)
| utd_Case ci p p' c c' brs brs' :
    All2 upto_domain p.(pparams) p'.(pparams) ->
    p.(puinst) = p'.(puinst) ->
    eq_context_upto_names p.(pcontext) p'.(pcontext) ->
    upto_domain p.(preturn) p'.(preturn) ->
    upto_domain c c' ->
    All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                     × upto_domain x.(bbody) y.(bbody)) brs brs' ->
    upto_domain (tCase ci p c brs) (tCase ci p' c' brs')

| utd_Proj pr c c' :                                                  (* = 2020 utd_Proj *)
    upto_domain c c' ->
    upto_domain (tProj pr c) (tProj pr c')

| utd_Fix mfix mfix' idx :                                            (* = 2020 utd_Fix: dname ignored *)
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) ×
                     upto_domain x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain (tFix mfix idx) (tFix mfix' idx)

| utd_CoFix mfix mfix' idx :                                          (* = 2020 utd_CoFix: dname ignored *)
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) ×
                     upto_domain x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain (tCoFix mfix idx) (tCoFix mfix' idx)

(* NEW for 9.2 (no 2020 analogue): primitive arrays, mirrors base eq_Prim
   (PCUICEquality.v:471-473); levels by eq, components by upto_domain. *)
| utd_Prim p p' :
    onPrims upto_domain eq p p' ->
    upto_domain (tPrim p) (tPrim p').
