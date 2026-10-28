(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 1: the canonical-domain map [canon]

  The modulo-[upto_domain] form of C4 is REFUTED (plan.md risk row 4, §6.1;
  [C4_false] at `wip/c4-C4C1b-2026-10-28` @ `73bbb2d1`). The repair is the
  canonical-domain route of plan.md §6.2: the joins run on terms whose λ domains
  have been ERASED BEFORE any reduction step, because comparing domain-blind only
  at the end of a join is too late — an η-expansion upstream can block ι/fix/
  cofix/proj, and a variable in an inner domain can block η.

  This file is §6.2's obligation 1, the first lemma of the route:

    [upto_domain_r a b <~> canon a = canon b]      ([upto_domain_r_canon_iff])

  **AC1 / R1 / SC1 (binding).** [canon] erases exactly what [upto_domain_r]
  ignores, no more and no less. In particular it KEEPS the binder RELEVANCE on
  [tProd], [tLetIn] and fix/cofix [dname], and it does NOT recurse into the
  [pcontext]/[bcontext] declarations' types or bodies:

  | node          | [canon]                                          | why                                                      |
  |---------------|--------------------------------------------------|----------------------------------------------------------|
  | [tLambda]     | domain := [canon_dom]; annotation fully erased   | [cumulSpecE_lambda_domain] has no annotation premise      |
  | [tProd]/[tLetIn] | NAME erased, RELEVANCE kept; recurse         | [cumulE_Prod]/[cumulE_LetIn] need [eq_binder_annot], which IS relevance equality ([BasicAst.v:18-22]) |
  | [tFix]/[tCoFix] | [dname] NAME erased, relevance kept; recurse  | [cumul_mfixpoint] compares [dname] relevance              |
  | [tCase]       | [pcontext]/[bcontext] NAMES only; NO recursion into their types or bodies | [eq_decl_upto_names] ([PCUICEquality.v:205-209]) compares relevance and compares declaration types and bodies by [=] |

  Erasing the Prod/LetIn/fix relevance too — the pre-R1 wording "every binder
  annotation set to one fixed value" — is UNSOUND for this route: [tProd {anon,
  Relevant} S S] and [tProd {anon, Irrelevant} S S] would get the same [canon]
  form and I5 would join them, while no [≤sE] rule relates them, so I5's
  join ⇒ spec direction (A4) would be false and the relevance conjuncts the
  typing metatheory reads out of Prod inversion would go dead.

  [upto_domain] itself is LANDED ([PCUICEtaDefs.v]) and is NOT edited here;
  [upto_domain_r] is a new, strictly stronger relation defined below, and C3/C1a
  are re-pinned to it separately.

  Dependencies: base syntax, [PCUICEquality] (for [eq_binder_annot] and
  [eq_decl_upto_names]) and [PCUICEtaDefs]. NO confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICPrimitive
     PCUICLiftSubst PCUICInduction PCUICEquality PCUICReduction PCUICSigmaCalculus
     PCUICOnFreeVars PCUICEtaDefs.

Local Open Scope type_scope.

(** ** Generic list plumbing

   Written as combinators rather than inline inductions so that the case solvers
   below stay uniform: re-pinning C3 and C1a over [upto_domain_r] ADDS
   constructors to their induction principles and reorders cases by
   construction, so nothing here may depend on goal order. *)

Lemma All_All2_map_eq {A B} (P : A -> Type) (R : A -> A -> Type) (f : A -> B) l l' :
  All P l -> All2 R l l' ->
  (forall x y, P x -> R x y -> f x = f y) ->
  map f l = map f l'.
Proof.
  intros hP hR H. induction hR in hP |- *; cbn; [reflexivity|].
  depelim hP. f_equal; [now apply H|now apply IHhR].
Qed.

Lemma All2_map_eq {A B} (f : A -> B) l l' :
  All2 (fun x y => f x = f y) l l' -> map f l = map f l'.
Proof. induction 1; cbn; congruence. Qed.

Lemma map_eq_All2 {A B} (f : A -> B) l l' :
  map f l = map f l' -> All2 (fun x y => f x = f y) l l'.
Proof.
  induction l in l' |- *; destruct l' as [|b l']; cbn; intros [=]; constructor; auto.
Qed.

Lemma All2_sym_mix {A} (P : A -> Type) (R : A -> A -> Type) l l' :
  All P l -> All2 R l l' -> (forall x y, P x -> R x y -> R y x) -> All2 R l' l.
Proof.
  intros hP hR H. induction hR in hP |- *; [constructor|].
  depelim hP. constructor; [now apply H|now apply IHhR].
Qed.

Lemma All2_trans_mix {A} (P : A -> Type) (R : A -> A -> Type) l1 l2 l3 :
  All P l1 -> All2 R l1 l2 -> All2 R l2 l3 ->
  (forall x, P x -> forall y z, R x y -> R y z -> R x z) ->
  All2 R l1 l3.
Proof.
  intros hP h1. induction h1 in l3, hP |- *; intros h2 H; depelim h2; [constructor|].
  depelim hP. constructor; [eapply H; eassumption|eapply IHh1; eassumption].
Qed.


Lemma All_All2_impl {A} (P : A -> Type) (R R' : A -> A -> Type) l l' :
  All P l -> All2 R l l' -> (forall x y, P x -> R x y -> R' x y) -> All2 R' l l'.
Proof.
  intros hP hR H. induction hR in hP |- *; [constructor|].
  depelim hP. constructor; [now apply H|now apply IHhR].
Qed.

Lemma All2_map_refl {A B} (P : A -> Type) (R : A -> B -> Type) (f : A -> B) l :
  All P l -> (forall x, P x -> R x (f x)) -> All2 R l (map f l).
Proof.
  intros h H. induction h; cbn; constructor; auto.
Qed.

(** ** [eq_binder_annot] is relevance equality, hence an equivalence *)

Lemma eq_binder_annot_refl' {A} (x : binder_annot A) : eq_binder_annot x x.
Proof. reflexivity. Qed.

Lemma eq_binder_annot_sym' {A B} (x : binder_annot A) (y : binder_annot B) :
  eq_binder_annot x y -> eq_binder_annot y x.
Proof. unfold eq_binder_annot. intros e. now symmetry. Qed.

Lemma eq_binder_annot_trans' {A B C}
  (x : binder_annot A) (y : binder_annot B) (z : binder_annot C) :
  eq_binder_annot x y -> eq_binder_annot y z -> eq_binder_annot x z.
Proof. unfold eq_binder_annot. intros e1 e2. now etransitivity. Qed.

(** ** [upto_domain_r] (plan.md §6.2, R1)

  [upto_domain] PLUS an [eq_binder_annot] premise at [utd_Prod], [utd_LetIn],
  [utd_Fix] and [utd_CoFix]. Everything else is byte-for-byte the landed
  relation ([PCUICEtaDefs.v:264-339]). *)

Inductive upto_domain_r : term -> term -> Type :=
| utdr_Rel n : upto_domain_r (tRel n) (tRel n)

| utdr_Evar e args args' :
    All2 upto_domain_r args args' ->
    upto_domain_r (tEvar e args) (tEvar e args')

| utdr_Var id : upto_domain_r (tVar id) (tVar id)

| utdr_Sort s : upto_domain_r (tSort s) (tSort s)

| utdr_App t t' u u' :
    upto_domain_r t t' ->
    upto_domain_r u u' ->
    upto_domain_r (tApp t u) (tApp t' u')

| utdr_Const c u : upto_domain_r (tConst c u) (tConst c u)

| utdr_Ind i u : upto_domain_r (tInd i u) (tInd i u)

| utdr_Construct i k u : upto_domain_r (tConstruct i k u) (tConstruct i k u)

(* λ: the domain AND the whole annotation are ignored, exactly as [utd_Lambda]. *)
| utdr_Lambda na na' ty ty' t t' :
    upto_domain_r t t' ->
    upto_domain_r (tLambda na ty t) (tLambda na' ty' t')

(* Prod/LetIn/Fix/CoFix: the binder NAME is ignored, the RELEVANCE is NOT (R1). *)
| utdr_Prod na na' a a' b b' :
    eq_binder_annot na na' ->
    upto_domain_r a a' ->
    upto_domain_r b b' ->
    upto_domain_r (tProd na a b) (tProd na' a' b')

| utdr_LetIn na na' t t' ty ty' u u' :
    eq_binder_annot na na' ->
    upto_domain_r t t' ->
    upto_domain_r ty ty' ->
    upto_domain_r u u' ->
    upto_domain_r (tLetIn na t ty u) (tLetIn na' t' ty' u')

| utdr_Case ci p p' c c' brs brs' :
    All2 upto_domain_r p.(pparams) p'.(pparams) ->
    p.(puinst) = p'.(puinst) ->
    eq_context_upto_names p.(pcontext) p'.(pcontext) ->
    upto_domain_r p.(preturn) p'.(preturn) ->
    upto_domain_r c c' ->
    All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                     × upto_domain_r x.(bbody) y.(bbody)) brs brs' ->
    upto_domain_r (tCase ci p c brs) (tCase ci p' c' brs')

| utdr_Proj pr c c' :
    upto_domain_r c c' ->
    upto_domain_r (tProj pr c) (tProj pr c')

| utdr_Fix mfix mfix' idx :
    All2 (fun x y => eq_binder_annot x.(dname) y.(dname) ×
                     upto_domain_r x.(dtype) y.(dtype) ×
                     upto_domain_r x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain_r (tFix mfix idx) (tFix mfix' idx)

| utdr_CoFix mfix mfix' idx :
    All2 (fun x y => eq_binder_annot x.(dname) y.(dname) ×
                     upto_domain_r x.(dtype) y.(dtype) ×
                     upto_domain_r x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix' ->
    upto_domain_r (tCoFix mfix idx) (tCoFix mfix' idx)

| utdr_Prim p p' :
    onPrims upto_domain_r eq p p' ->
    upto_domain_r (tPrim p) (tPrim p').

Derive Signature for upto_domain_r.

(** [upto_domain_r] is strictly stronger than the landed [upto_domain]: it is the
   same relation with extra premises, so it embeds. (The converse is false: the
   two [tProd {anon,·} S S] of the AC1 note are [upto_domain]-related and not
   [upto_domain_r]-related.) *)
Lemma upto_domain_r_upto_domain t u : upto_domain_r t u -> upto_domain t u.
Proof.
  intros e. induction t in u, e |- * using term_forall_list_ind; depelim e.
  all: try solve [constructor; eauto].
  - (* Evar *) constructor. eapply All_All2_impl; [exact X|exact a|]. cbn. eauto.
  - (* Case *) destruct X as (Hpar & _ & Hret). constructor; eauto.
    + eapply All_All2_impl; [exact Hpar|exact a|]. cbn. eauto.
    + clear -X0 a1. induction a1 in X0 |- *; depelim X0; constructor.
      * destruct r as [Hc Hb], p as [_ HP]. split; [exact Hc|now apply HP].
      * now apply IHa1.
  - (* Fix *) constructor. clear -X a.
    induction a in X |- *; depelim X; constructor.
    * destruct r as (_ & Ht & Hb & Hr), p as [HPt HPb].
      repeat split; [now apply HPt|now apply HPb|exact Hr].
    * now apply IHa.
  - (* CoFix *) constructor. clear -X a.
    induction a in X |- *; depelim X; constructor.
    * destruct r as (_ & Ht & Hb & Hr), p as [HPt HPb].
      repeat split; [now apply HPt|now apply HPb|exact Hr].
    * now apply IHa.
  - (* Prim *) constructor. depelim o; try solve [constructor].
    destruct X as (HPt & HPd & HPv). constructor.
    + assumption.
    + now apply HPd.
    + now apply HPt.
    + eapply All_All2_impl; [exact HPv|eassumption|]. cbn. eauto.
Qed.


Lemma eq_context_upto_names_refl' ctx : eq_context_upto_names ctx ctx.
Proof.
  induction ctx as [|d ctx IH]; cbn; constructor; [|exact IH].
  destruct d as [na [b|] ty]; [apply compare_vdef|apply compare_vass]; reflexivity.
Qed.

(** ** [upto_domain_r] is an equivalence *)

(** The three proofs below dispatch on the SHAPE OF THE GOAL
   ([lazymatch goal with | |- upto_domain_r (tFix _ _) _ => … ]), not on bullet
   position. [upto_domain_r] has four more premises than [upto_domain], so any
   prelude that silently closes one case shifts every later positional bullet and
   the failure then surfaces several cases away. Shape dispatch also keeps the
   error message on the case that actually failed. (C4C1b's carry-forward,
   recorded in [impl/HELPERS.md].) *)

#[global] Instance upto_domain_r_refl : CRelationClasses.Reflexive upto_domain_r.
Proof.
  intros t.
  induction t using term_forall_list_ind;
  lazymatch goal with
  | |- upto_domain_r (tEvar _ _) _ =>
      apply utdr_Evar; eapply All_All2; [exact X|]; cbn; intros ? h; exact h
  | |- upto_domain_r (tProd _ _ _) _ =>
      apply utdr_Prod; [apply eq_binder_annot_refl'|assumption|assumption]
  | |- upto_domain_r (tLetIn _ _ _ _) _ =>
      apply utdr_LetIn;
      [apply eq_binder_annot_refl'|assumption|assumption|assumption]
  | |- upto_domain_r (tCase _ _ _ _) _ =>
      destruct X as (Hpars & _ & Hret); apply utdr_Case;
      [ eapply All_All2; [exact Hpars|]; cbn; intros ? h; exact h
      | reflexivity
      | apply eq_context_upto_names_refl'
      | exact Hret
      | assumption
      | eapply All_All2; [eassumption|]; cbn; intros br [_ Hb];
        split; [apply eq_context_upto_names_refl'|exact Hb] ]
  | |- upto_domain_r (tFix _ _) _ =>
      apply utdr_Fix; eapply All_All2; [eassumption|]; cbn; intros d [Hty Hbo];
      repeat split;
      first [apply eq_binder_annot_refl'|exact Hty|exact Hbo|reflexivity]
  | |- upto_domain_r (tCoFix _ _) _ =>
      apply utdr_CoFix; eapply All_All2; [eassumption|]; cbn; intros d [Hty Hbo];
      repeat split;
      first [apply eq_binder_annot_refl'|exact Hty|exact Hbo|reflexivity]
  | |- upto_domain_r (tPrim _) _ =>
      apply utdr_Prim; destruct p as [? m]; destruct m; cbn in X;
      lazymatch goal with
      | |- onPrims _ _ (primArray; _) _ =>
          destruct X as (Hty & Hdef & Hval); apply onPrimsArray;
          [ reflexivity
          | exact Hdef
          | exact Hty
          | eapply All_All2; [exact Hval|]; cbn; intros ? h; exact h ]
      | |- _ => constructor
      end
  | |- upto_domain_r (tRel _) _ => apply utdr_Rel
  | |- upto_domain_r (tVar _) _ => apply utdr_Var
  | |- upto_domain_r (tSort _) _ => apply utdr_Sort
  | |- upto_domain_r (tConst _ _) _ => apply utdr_Const
  | |- upto_domain_r (tInd _ _) _ => apply utdr_Ind
  | |- upto_domain_r (tConstruct _ _ _) _ => apply utdr_Construct
  | |- upto_domain_r (tLambda _ _ _) _ => apply utdr_Lambda; assumption
  | |- upto_domain_r (tApp _ _) _ => apply utdr_App; assumption
  | |- upto_domain_r (tProj _ _) _ => apply utdr_Proj; assumption
  end.
Qed.

#[global] Instance upto_domain_r_sym : CRelationClasses.Symmetric upto_domain_r.
Proof.
  intros u v e.
  induction u in v, e |- * using term_forall_list_ind; depelim e;
  lazymatch goal with
  | |- upto_domain_r _ (tEvar _ _) =>
      constructor; eapply All2_sym_mix; [eassumption|eassumption|];
      cbn; intros x y HP h; now apply HP
  | |- upto_domain_r _ (tProd _ _ _) =>
      constructor; [now apply eq_binder_annot_sym'|eauto|eauto]
  | |- upto_domain_r _ (tLetIn _ _ _ _) =>
      constructor; [now apply eq_binder_annot_sym'|eauto|eauto|eauto]
  | |- upto_domain_r _ (tCase _ _ _ _) =>
      destruct X as (Hpar & _ & Hret); constructor;
      [ eapply All2_sym_mix; [exact Hpar|eassumption|];
        cbn; intros x y HP h; now apply HP
      | now symmetry
      | now symmetry
      | now apply Hret
      | eauto
      | eapply All2_sym_mix; [eassumption|eassumption|];
        cbn; intros x y [_ HP] [Hc Hb]; split; [now symmetry|now apply HP] ]
  | |- upto_domain_r _ (tFix _ _) =>
      constructor; eapply All2_sym_mix; [eassumption|eassumption|];
      cbn; intros x y [HPt HPb] (Hn & Ht & Hb & Hr); repeat split;
      [now apply eq_binder_annot_sym'|now apply HPt|now apply HPb|now symmetry]
  | |- upto_domain_r _ (tCoFix _ _) =>
      constructor; eapply All2_sym_mix; [eassumption|eassumption|];
      cbn; intros x y [HPt HPb] (Hn & Ht & Hb & Hr); repeat split;
      [now apply eq_binder_annot_sym'|now apply HPt|now apply HPb|now symmetry]
  | |- upto_domain_r _ (tPrim _) =>
      constructor; depelim o;
      lazymatch goal with
      | |- onPrims _ _ (primArray; _) _ =>
          destruct X as (HPt & HPd & HPv); constructor;
          [ now symmetry
          | now apply HPd
          | now apply HPt
          | eapply All2_sym_mix; [exact HPv|eassumption|];
            cbn; intros x y HP h; now apply HP ]
      | |- _ => constructor
      end
  | |- _ => constructor; eauto
  end.
Qed.

#[global] Instance upto_domain_r_trans : CRelationClasses.Transitive upto_domain_r.
Proof.
  intros u v w e1 e2.
  induction u in v, w, e1, e2 |- * using term_forall_list_ind;
    depelim e1; depelim e2;
  lazymatch goal with
  | |- upto_domain_r (tEvar _ _) _ =>
      constructor; eapply All2_trans_mix; [eassumption|eassumption|eassumption|];
      cbn; intros x HP y z h1 h2; eapply HP; eassumption
  | |- upto_domain_r (tProd _ _ _) _ =>
      constructor; [eapply eq_binder_annot_trans'; eassumption|eauto|eauto]
  | |- upto_domain_r (tLetIn _ _ _ _) _ =>
      constructor; [eapply eq_binder_annot_trans'; eassumption|eauto|eauto|eauto]
  | |- upto_domain_r (tCase _ _ _ _) _ =>
      destruct X as (Hpar & _ & Hret); constructor;
      [ eapply All2_trans_mix; [exact Hpar|eassumption|eassumption|];
        cbn; intros x HP y z h1 h2; eapply HP; eassumption
      | etransitivity; eassumption
      | etransitivity; eassumption
      | eapply Hret; eassumption
      | eauto
      | eapply All2_trans_mix; [eassumption|eassumption|eassumption|];
        cbn; intros x [_ HP] y z [Hc1 Hb1] [Hc2 Hb2];
        split; [etransitivity; eassumption|eapply HP; eassumption] ]
  | |- upto_domain_r (tFix _ _) _ =>
      constructor; eapply All2_trans_mix; [eassumption|eassumption|eassumption|];
      cbn; intros x [HPt HPb] y z (Hn1 & Ht1 & Hb1 & Hr1) (Hn2 & Ht2 & Hb2 & Hr2);
      repeat split;
      [ eapply eq_binder_annot_trans'; eassumption
      | eapply HPt; eassumption
      | eapply HPb; eassumption
      | etransitivity; eassumption ]
  | |- upto_domain_r (tCoFix _ _) _ =>
      constructor; eapply All2_trans_mix; [eassumption|eassumption|eassumption|];
      cbn; intros x [HPt HPb] y z (Hn1 & Ht1 & Hb1 & Hr1) (Hn2 & Ht2 & Hb2 & Hr2);
      repeat split;
      [ eapply eq_binder_annot_trans'; eassumption
      | eapply HPt; eassumption
      | eapply HPb; eassumption
      | etransitivity; eassumption ]
  | |- upto_domain_r (tPrim _) _ =>
      constructor; depelim o; depelim o0;
      lazymatch goal with
      | |- onPrims _ _ (primArray; _) _ =>
          destruct X as (HPt & HPd & HPv); constructor;
          [ etransitivity; eassumption
          | eapply HPd; eassumption
          | eapply HPt; eassumption
          | eapply All2_trans_mix; [exact HPv|eassumption|eassumption|];
            cbn; intros x HP y z h1 h2; eapply HP; eassumption ]
      | |- _ => constructor
      end
  | |- _ => constructor; eauto
  end.
Qed.

(** ** [canon] (plan.md §6.2, AC1 / R1 / SC1)

  [canon_dom] is CLOSED, which is what makes [canon] preserve scoping
  (obligation 2) and makes substitution unable to put a variable into a
  canonical domain. *)

Definition canon_dom : term := tSort sProp.

(** Binder annotation with the NAME erased and the RELEVANCE KEPT. *)
Definition canon_na (na : aname) : aname :=
  {| binder_name := nAnon; binder_relevance := na.(binder_relevance) |}.

(** Binder annotation with name AND relevance erased: λ only. *)
Definition canon_la : aname :=
  {| binder_name := nAnon; binder_relevance := Relevant |}.

(** Case/branch context declaration: the NAME only. The type and the body are
   left ALONE — [eq_decl_upto_names] compares them by [=], so recursing here
   would make [canon] identify strictly more than [upto_domain_r] does and
   obligation 1 would be false. It would also be pointless: [lift]/[subst] never
   touch [pcontext] ([map_predicate_k], [PCUICAst.v:83-87]). *)
Definition canon_decl (d : context_decl) : context_decl :=
  {| decl_name := canon_na d.(decl_name);
     decl_body := d.(decl_body);
     decl_type := d.(decl_type) |}.

Definition canon_def (f : term -> term) (d : def term) : def term :=
  {| dname := canon_na d.(dname);
     dtype := f d.(dtype);
     dbody := f d.(dbody);
     rarg := d.(rarg) |}.

Definition canon_predicate (f : term -> term) (p : predicate term) : predicate term :=
  {| pparams := map f p.(pparams);
     puinst := p.(puinst);
     pcontext := map canon_decl p.(pcontext);
     preturn := f p.(preturn) |}.

Definition canon_branch (f : term -> term) (b : branch term) : branch term :=
  {| bcontext := map canon_decl b.(bcontext);
     bbody := f b.(bbody) |}.

Fixpoint canon (t : term) : term :=
  match t with
  | tRel n => tRel n
  | tVar i => tVar i
  | tEvar ev l => tEvar ev (map canon l)
  | tSort s => tSort s
  | tProd na A B => tProd (canon_na na) (canon A) (canon B)
  | tLambda na A b => tLambda canon_la canon_dom (canon b)
  | tLetIn na b B u => tLetIn (canon_na na) (canon b) (canon B) (canon u)
  | tApp u v => tApp (canon u) (canon v)
  | tConst c u => tConst c u
  | tInd i u => tInd i u
  | tConstruct i n u => tConstruct i n u
  | tCase ci p c brs =>
      tCase ci (canon_predicate canon p) (canon c) (map (canon_branch canon) brs)
  | tProj pr c => tProj pr (canon c)
  | tFix mfix idx => tFix (map (canon_def canon) mfix) idx
  | tCoFix mfix idx => tCoFix (map (canon_def canon) mfix) idx
  | tPrim p => tPrim (map_prim canon p)
  end.

(** ** Binder and declaration arms of obligation 1 *)

Lemma canon_na_eq na na' : eq_binder_annot na na' -> canon_na na = canon_na na'.
Proof. unfold eq_binder_annot, canon_na. intros e. now rewrite e. Qed.

(** [canon_na] KEEPS the relevance, so a binder is [eq_binder_annot] to its own
   canonical form. This is the whole content of R1/SC1 in one line. *)
Lemma eq_binder_annot_canon_na na : eq_binder_annot na (canon_na na).
Proof. reflexivity. Qed.

Lemma canon_na_inv na na' : canon_na na = canon_na na' -> eq_binder_annot na na'.
Proof.
  unfold canon_na, eq_binder_annot. intros e.
  exact (f_equal binder_relevance e).
Qed.

Lemma canon_decl_eq d d' : eq_decl_upto_names d d' -> canon_decl d = canon_decl d'.
Proof.
  intros e. depelim e; unfold canon_decl; cbn; now rewrite (canon_na_eq _ _ e).
Qed.

Lemma canon_decl_inv d d' : canon_decl d = canon_decl d' -> eq_decl_upto_names d d'.
Proof.
  destruct d as [na bo ty], d' as [na' bo' ty']. unfold canon_decl; cbn.
  intros [= e1 e2 e3]. subst bo' ty'.
  (* [injection] already reduces [canon_na na = canon_na na'] to the relevance
     equation, which IS [eq_binder_annot] by definition. *)
  destruct bo as [b|]; [apply compare_vdef|apply compare_vass]; exact e1.
Qed.

Lemma canon_ctx_eq ctx ctx' :
  eq_context_upto_names ctx ctx' -> map canon_decl ctx = map canon_decl ctx'.
Proof.
  induction 1; cbn; [reflexivity|]. f_equal; [now apply canon_decl_eq|assumption].
Qed.

Lemma canon_ctx_inv ctx ctx' :
  map canon_decl ctx = map canon_decl ctx' -> eq_context_upto_names ctx ctx'.
Proof.
  intros e. apply map_eq_All2 in e.
  eapply All2_impl; [exact e|]. cbn. intros x y. apply canon_decl_inv.
Qed.

Lemma eq_context_upto_names_canon_decl ctx :
  eq_context_upto_names ctx (map canon_decl ctx).
Proof.
  induction ctx as [|d ctx IH]; cbn; constructor; [|exact IH].
  destruct d as [na [b|] ty]; unfold canon_decl; cbn;
    [apply compare_vdef|apply compare_vass]; reflexivity.
Qed.

(** ** Obligation 1, forward: [upto_domain_r] implies [canon]-equality *)

Lemma upto_domain_r_canon t u : upto_domain_r t u -> canon t = canon u.
Proof.
  intros e. induction t in u, e |- * using term_forall_list_ind; depelim e; cbn.
  all: try solve [reflexivity | f_equal; eauto].
  - (* Evar *) f_equal. eapply All_All2_map_eq; [exact X|exact a|]. cbn. eauto.
  - (* Prod *) f_equal; [now apply canon_na_eq|eauto|eauto].
  - (* LetIn *) f_equal; [now apply canon_na_eq|eauto|eauto|eauto].
  - (* Case *) destruct X as (Hpar & _ & Hret).
    f_equal.
    + unfold canon_predicate; cbn. f_equal.
      * eapply All_All2_map_eq; [exact Hpar|exact a|]. cbn. eauto.
      * assumption.
      * now apply canon_ctx_eq.
      * now apply Hret.
    + eauto.
    + eapply All_All2_map_eq; [exact X0|exact a1|].
      cbn. intros x y [_ Hb] [Hc Hu]. unfold canon_branch; cbn.
      f_equal; [now apply canon_ctx_eq|now apply Hb].
  - (* Fix *) f_equal.
    eapply All_All2_map_eq; [exact X|exact a|].
    cbn. intros x y [Hty Hbo] (Hn & Ht & Hb & Hr). unfold canon_def; cbn.
    f_equal; [now apply canon_na_eq|now apply Hty|now apply Hbo|exact Hr].
  - (* CoFix *) f_equal.
    eapply All_All2_map_eq; [exact X|exact a|].
    cbn. intros x y [Hty Hbo] (Hn & Ht & Hb & Hr). unfold canon_def; cbn.
    f_equal; [now apply canon_na_eq|now apply Hty|now apply Hbo|exact Hr].
  - (* Prim *) f_equal. depelim o; cbn; [reflexivity|reflexivity|reflexivity|].
    destruct X as (HPt & HPd & HPv).
    (* [canon] KEEPS [array_level], while [onPrims] only relates the levels'
       [Universe.make']. [Universe.make'_inj] (Universes.v:613) closes the gap. *)
    match goal with
    | H : Universe.make' _ = Universe.make' _ |- _ =>
        apply Universe.make'_inj in H
    end.
    assert (hv : map canon (array_value a) = map canon (array_value a'))
      by (eapply All_All2_map_eq; [exact HPv|eassumption|]; cbn; eauto).
    assert (hd : canon (array_default a) = canon (array_default a'))
      by (now apply HPd).
    assert (ht : canon (array_type a) = canon (array_type a'))
      by (now apply HPt).
    unfold mapu_array_model; cbn.
    now rewrite hv hd ht; f_equal.
Qed.

(** ** Obligation 1, backward, through [canon]'s own fixed point

   [upto_domain_r t (canon t)] plus symmetry and transitivity gives the backward
   direction without a 15x15 shape analysis. *)

Lemma upto_domain_r_canon_self t : upto_domain_r t (canon t).
Proof.
  induction t using term_forall_list_ind; cbn;
  lazymatch goal with
  | |- upto_domain_r (tEvar _ _) _ =>
      apply utdr_Evar; eapply All2_map_refl; [exact X|]; cbn; intros ? h; exact h
  | |- upto_domain_r (tProd _ _ _) _ =>
      apply utdr_Prod; [apply eq_binder_annot_canon_na|assumption|assumption]
  | |- upto_domain_r (tLetIn _ _ _ _) _ =>
      apply utdr_LetIn;
      [apply eq_binder_annot_canon_na|assumption|assumption|assumption]
  | |- upto_domain_r (tCase _ _ _ _) _ =>
      destruct X as (Hpar & _ & Hret); unfold canon_predicate; cbn;
      apply utdr_Case; cbn;
      [ eapply All2_map_refl; [exact Hpar|]; cbn; intros ? h; exact h
      | reflexivity
      | apply eq_context_upto_names_canon_decl
      | exact Hret
      | assumption
      | clear -X0; induction X0; cbn; constructor; [|assumption];
        destruct p as [_ Hb]; unfold canon_branch; cbn;
        split; [apply eq_context_upto_names_canon_decl|exact Hb] ]
  | |- upto_domain_r (tFix _ _) _ =>
      apply utdr_Fix; clear -X;
      induction X; cbn; constructor; [|assumption];
      destruct p as [Hty Hbo]; unfold canon_def; cbn; repeat split;
      first [apply eq_binder_annot_canon_na|exact Hty|exact Hbo|reflexivity]
  | |- upto_domain_r (tCoFix _ _) _ =>
      apply utdr_CoFix; clear -X;
      induction X; cbn; constructor; [|assumption];
      destruct p as [Hty Hbo]; unfold canon_def; cbn; repeat split;
      first [apply eq_binder_annot_canon_na|exact Hty|exact Hbo|reflexivity]
  | |- upto_domain_r (tPrim _) _ =>
      apply utdr_Prim; destruct p as [? m]; destruct m; cbn in X; cbn;
      lazymatch goal with
      | |- onPrims _ _ (primArray; _) _ =>
          destruct X as (Hty & Hdef & Hval); unfold mapu_array_model; cbn;
          apply onPrimsArray; cbn;
          [ reflexivity
          | exact Hdef
          | exact Hty
          | eapply All2_map_refl; [exact Hval|]; cbn; intros ? h; exact h ]
      | |- _ => constructor
      end
  | |- upto_domain_r (tRel _) _ => apply utdr_Rel
  | |- upto_domain_r (tVar _) _ => apply utdr_Var
  | |- upto_domain_r (tSort _) _ => apply utdr_Sort
  | |- upto_domain_r (tConst _ _) _ => apply utdr_Const
  | |- upto_domain_r (tInd _ _) _ => apply utdr_Ind
  | |- upto_domain_r (tConstruct _ _ _) _ => apply utdr_Construct
  | |- upto_domain_r (tLambda _ _ _) _ => apply utdr_Lambda; assumption
  | |- upto_domain_r (tApp _ _) _ => apply utdr_App; assumption
  | |- upto_domain_r (tProj _ _) _ => apply utdr_Proj; assumption
  end.
Qed.

(** ** Obligation 1 *)

Theorem upto_domain_r_canon_iff t u : upto_domain_r t u <~> canon t = canon u.
Proof.
  split.
  - apply upto_domain_r_canon.
  - intros e.
    transitivity (canon t); [apply upto_domain_r_canon_self|].
    rewrite e. symmetry. apply upto_domain_r_canon_self.
Qed.

(** [canon] is idempotent: canonical terms are exactly its fixed points, which is
   the [canon t = t] conjunct of §6.2's invariant [Q]. *)
Lemma canon_idem t : canon (canon t) = canon t.
Proof.
  apply upto_domain_r_canon. symmetry. apply upto_domain_r_canon_self.
Qed.

(** * §6.2 obligation 2: [canon] commutes with the substitution calculus,
      and preserves scoping (R2)

  Why it goes through at all: [canon_dom] is CLOSED, so it is fixed by every
  operation here, and substitution can never put a variable into a canonical
  λ domain. The only arithmetic obligations are length equations, and [canon]
  is a [map] everywhere it matters, so all of them are [length_map]. *)

Lemma All_map_eq' {A B} (f g : A -> B) l :
  All (fun x => f x = g x) l -> map f l = map g l.
Proof. induction 1; cbn; congruence. Qed.

Lemma canon_ctx_length ctx : #|map canon_decl ctx| = #|ctx|.
Proof. apply length_map. Qed.

(** One congruence solver for every node whose [canon] image is built from the
   IHs alone. Positional dispatch after [f_equal] is wrong here: [f_equal]
   discharges the arguments that are already syntactically equal (the preserved
   binder annotation, and [canon_dom] for a λ), so the number of goals it leaves
   varies by node. *)
Local Ltac canon_cong := f_equal; first [reflexivity|eauto].

(** ** [lift] *)

Lemma canon_lift n k t : canon (lift n k t) = lift n k (canon t).
Proof.
  induction t in k |- * using term_forall_list_ind; cbn.
  - (* tRel *) reflexivity.
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite !map_map. apply All_map_eq'.
    eapply All_impl; [exact X|]. cbn. intros ? h. apply h.
  - (* tSort *) reflexivity.
  - (* tProd *) canon_cong.
  - (* tLambda *) canon_cong.
  - (* tLetIn *) canon_cong.
  - (* tApp *) canon_cong.
  - (* tConst *) reflexivity.
  - (* tInd *) reflexivity.
  - (* tConstruct *) reflexivity.
  - (* tCase *) destruct X as (Hpar & _ & Hret).
    unfold canon_predicate, map_predicate_k; cbn.
    f_equal; [f_equal|apply IHt|].
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact Hpar|]. cbn. intros ? h. apply h.
    + rewrite canon_ctx_length. apply Hret.
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact X0|]. cbn. intros br [_ Hb].
      unfold canon_branch, map_branch_k; cbn.
      rewrite canon_ctx_length. f_equal. apply Hb.
  - (* tProj *) canon_cong.
  - (* tFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tCoFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tPrim *) f_equal. destruct p as [? m]; destruct m; cbn in X; cbn;
      try reflexivity.
    destruct X as (Hty & Hdef & Hval).
    unfold mapu_array_model; cbn. rewrite ?map_map.
    assert (hv : map (fun x : term => canon (lift n k x)) (array_value a)
               = map (fun x : term => lift n k (canon x)) (array_value a)).
    { apply All_map_eq'. eapply All_impl; [exact Hval|]. cbn. intros ? h. apply h. }
    now rewrite hv (Hty k) (Hdef k).
Qed.

(** ** [rename] *)

Lemma canon_rename f t : canon (rename f t) = rename f (canon t).
Proof.
  induction t in f |- * using term_forall_list_ind; cbn.
  - (* tRel *) reflexivity.
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite !map_map. apply All_map_eq'.
    eapply All_impl; [exact X|]. cbn. intros ? h. apply h.
  - (* tSort *) reflexivity.
  - (* tProd *) canon_cong.
  - (* tLambda *) canon_cong.
  - (* tLetIn *) canon_cong.
  - (* tApp *) canon_cong.
  - (* tConst *) reflexivity.
  - (* tInd *) reflexivity.
  - (* tConstruct *) reflexivity.
  - (* tCase *) destruct X as (Hpar & _ & Hret).
    unfold canon_predicate, map_predicate_shift; cbn.
    f_equal; [f_equal|apply IHt|].
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact Hpar|]. cbn. intros ? h. apply h.
    + rewrite canon_ctx_length. apply Hret.
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact X0|]. cbn. intros br [_ Hb].
      unfold canon_branch, map_branch_shift; cbn.
      rewrite canon_ctx_length. f_equal. apply Hb.
  - (* tProj *) canon_cong.
  - (* tFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tCoFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tPrim *) f_equal. destruct p as [? m]; destruct m; cbn in X; cbn;
      try reflexivity.
    destruct X as (Hty & Hdef & Hval).
    unfold mapu_array_model; cbn. rewrite ?map_map.
    assert (hv : map (fun x : term => canon (rename f x)) (array_value a)
               = map (fun x : term => rename f (canon x)) (array_value a)).
    { apply All_map_eq'. eapply All_impl; [exact Hval|]. cbn. intros ? h. apply h. }
    now rewrite hv (Hty f) (Hdef f).
Qed.

(** ** [subst]

  The [tRel] case is where the closedness of [canon_dom] is invisible but the
  [canon_lift] commutation is not: a substituted body arrives under [lift0 k]. *)

Lemma canon_subst s k t :
  canon (subst s k t) = subst (map canon s) k (canon t).
Proof.
  induction t in k |- * using term_forall_list_ind; cbn.
  - (* tRel *) destruct (Nat.leb k n); cbn; [|reflexivity].
    rewrite nth_error_map. destruct (nth_error s (n - k)) as [b|]; cbn.
    + apply canon_lift.
    + now rewrite length_map.
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite !map_map. apply All_map_eq'.
    eapply All_impl; [exact X|]. cbn. intros ? h. apply h.
  - (* tSort *) reflexivity.
  - (* tProd *) canon_cong.
  - (* tLambda *) canon_cong.
  - (* tLetIn *) canon_cong.
  - (* tApp *) canon_cong.
  - (* tConst *) reflexivity.
  - (* tInd *) reflexivity.
  - (* tConstruct *) reflexivity.
  - (* tCase *) destruct X as (Hpar & _ & Hret).
    unfold canon_predicate, map_predicate_k; cbn.
    f_equal; [f_equal|apply IHt|].
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact Hpar|]. cbn. intros ? h. apply h.
    + rewrite canon_ctx_length. apply Hret.
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact X0|]. cbn. intros br [_ Hb].
      unfold canon_branch, map_branch_k; cbn.
      rewrite canon_ctx_length. f_equal. apply Hb.
  - (* tProj *) canon_cong.
  - (* tFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tCoFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tPrim *) f_equal. destruct p as [? m]; destruct m; cbn in X; cbn;
      try reflexivity.
    destruct X as (Hty & Hdef & Hval).
    unfold mapu_array_model; cbn. rewrite ?map_map.
    assert (hv : map (fun x : term => canon (subst s k x)) (array_value a)
               = map (fun x : term => subst (map canon s) k (canon x)) (array_value a)).
    { apply All_map_eq'. eapply All_impl; [exact Hval|]. cbn. intros ? h. apply h. }
    now rewrite hv (Hty k) (Hdef k).
Qed.

Lemma canon_subst1 a k t :
  canon (subst1 a k t) = subst1 (canon a) k (canon t).
Proof. unfold subst1. apply (canon_subst [a]). Qed.

(** ** [subst_instance] (needed by δ: a constant body arrives instantiated)

  [subst_instance_constr] leaves [pcontext]/[bcontext] alone ([id],
  [PCUICAst.v:419-420]) and rewrites only [array_level] inside a primitive
  array, which is exactly the field [canon] keeps. So the two commute because
  they touch disjoint fields. *)

Lemma canon_subst_instance u t :
  canon (subst_instance u t) = subst_instance u (canon t).
Proof.
  induction t using term_forall_list_ind; cbn.
  - (* tRel *) reflexivity.
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite !map_map. apply All_map_eq'.
    eapply All_impl; [exact X|]. cbn. intros ? h. apply h.
  - (* tSort *) reflexivity.
  - (* tProd *) canon_cong.
  - (* tLambda *) canon_cong.
  - (* tLetIn *) canon_cong.
  - (* tApp *) canon_cong.
  - (* tConst *) reflexivity.
  - (* tInd *) reflexivity.
  - (* tConstruct *) reflexivity.
  - (* tCase *) destruct X as (Hpar & _ & Hret).
    unfold canon_predicate, map_predicate; cbn.
    f_equal; [f_equal|apply IHt|].
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact Hpar|]. cbn. intros ? h. apply h.
    + apply Hret.
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact X0|]. cbn. intros br [_ Hb].
      unfold canon_branch, map_branch; cbn. f_equal. apply Hb.
  - (* tProj *) canon_cong.
  - (* tFix *) f_equal. rewrite !map_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tCoFix *) f_equal. rewrite !map_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|apply Hbo].
  - (* tPrim *) f_equal. destruct p as [? m]; destruct m; cbn in X; cbn;
      try reflexivity.
    destruct X as (Hty & Hdef & Hval).
    unfold mapu_array_model; cbn. rewrite ?map_map.
    assert (hv : map (fun x : term => canon (subst_instance u x)) (array_value a)
               = map (fun x : term => subst_instance u (canon x)) (array_value a)).
    { apply All_map_eq'. eapply All_impl; [exact Hval|]. cbn. intros ? h. apply h. }
    now rewrite hv Hty Hdef.
Qed.

(** ** [inst] (A7's sigma-calculus route)

  The only new content over [canon_rename] is that [canon] commutes with [up]:
  below the cut [up] produces [tRel i], which [canon] fixes, and above it a
  [rename], which [canon_rename] handles. *)

Lemma canon_up k s i : canon (up k s i) = up k (fun j => canon (s j)) i.
Proof.
  unfold up. destruct (k <=? i); [apply canon_rename|reflexivity].
Qed.

Lemma canon_inst s t : canon (inst s t) = inst (fun j => canon (s j)) (canon t).
Proof.
  induction t in s |- * using term_forall_list_ind; cbn.
  - (* tRel *) reflexivity.
  - (* tVar *) reflexivity.
  - (* tEvar *) f_equal. rewrite !map_map. apply All_map_eq'.
    eapply All_impl; [exact X|]. cbn. intros ? h. apply h.
  - (* tSort *) reflexivity.
  - (* tProd *) f_equal; [apply IHt1|].
    rewrite IHt2. apply inst_ext. intros i. apply canon_up.
  - (* tLambda *) f_equal.
    rewrite IHt2. apply inst_ext. intros i. apply canon_up.
  - (* tLetIn *) f_equal; [apply IHt1|apply IHt2|].
    rewrite IHt3. apply inst_ext. intros i. apply canon_up.
  - (* tApp *) f_equal; [apply IHt1|apply IHt2].
  - (* tConst *) reflexivity.
  - (* tInd *) reflexivity.
  - (* tConstruct *) reflexivity.
  - (* tCase *) destruct X as (Hpar & _ & Hret).
    unfold canon_predicate, map_predicate_shift; cbn.
    f_equal; [f_equal|apply IHt|].
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact Hpar|]. cbn. intros ? h. apply h.
    + rewrite canon_ctx_length Hret. apply inst_ext. intros i.
      apply canon_up.
    + rewrite !map_map. apply All_map_eq'.
      eapply All_impl; [exact X0|]. cbn. intros br [_ Hb].
      unfold canon_branch, map_branch_shift; cbn.
      rewrite canon_ctx_length Hb. f_equal. apply inst_ext. intros i.
      apply canon_up.
  - (* tProj *) f_equal. apply IHt.
  - (* tFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|].
    rewrite Hbo. apply inst_ext. intros i. apply canon_up.
  - (* tCoFix *) f_equal. rewrite !map_map. rewrite length_map.
    apply All_map_eq'. eapply All_impl; [exact X|]. cbn. intros d [Hty Hbo].
    unfold canon_def, map_def; cbn. f_equal; [apply Hty|].
    rewrite Hbo. apply inst_ext. intros i. apply canon_up.
  - (* tPrim *) f_equal. destruct p as [? m]; destruct m; cbn in X; cbn;
      try reflexivity.
    destruct X as (Hty & Hdef & Hval).
    unfold mapu_array_model; cbn. rewrite ?map_map.
    assert (hv : map (fun x : term => canon (inst s x)) (array_value a)
               = map (fun x : term => inst (fun j => canon (s j)) (canon x))
                     (array_value a)).
    { apply All_map_eq'. eapply All_impl; [exact Hval|]. cbn. intros ? h. apply h. }
    now rewrite hv (Hty s) (Hdef s).
Qed.

(** ** Scoping

  [canon] only ever WEAKENS a scoping obligation: at a λ it replaces the domain
  by the closed [canon_dom], and everywhere else it either recurses or rewrites
  a binder name, which [on_free_vars] does not read. The [tCase] contexts are
  the one place worth stating separately, because [on_free_vars] tests them with
  [test_context_k] and [canon_decl] leaves every field that test reads. *)

Lemma test_context_k_canon f n ctx :
  test_context_k f n (map canon_decl ctx) = test_context_k f n ctx.
Proof.
  induction ctx as [|d ctx IH]; cbn; [reflexivity|].
  rewrite IH canon_ctx_length. reflexivity.
Qed.

(** List helpers, so the main induction needs no [solve_all] (whose behaviour
    after a partial [cbn] is what made the first draft of this proof fail). *)

Lemma forallb_canon_ofv P l :
  All (fun t => forall P, on_free_vars P t -> on_free_vars P (canon t)) l ->
  forallb (on_free_vars P) l -> forallb (on_free_vars P) (map canon l).
Proof.
  induction 1; cbn; [reflexivity|]. move/andP => [h1 h2]. apply/andP. split; auto.
Qed.

Lemma forallb_canon_def_ofv P Q mfix :
  All (fun d => (forall P, on_free_vars P d.(dtype) -> on_free_vars P (canon d.(dtype))) ×
                (forall P, on_free_vars P d.(dbody) -> on_free_vars P (canon d.(dbody)))) mfix ->
  forallb (test_def (on_free_vars P) (on_free_vars Q)) mfix ->
  forallb (test_def (on_free_vars P) (on_free_vars Q)) (map (canon_def canon) mfix).
Proof.
  induction 1 as [|d mfix [Hty Hbo] _ IH]; cbn; [reflexivity|].
  unfold test_def at 1 3; cbn.
  move/andP => [/andP [h1 h2] h3]. apply/andP. split; [apply/andP; split; auto|auto].
Qed.

Lemma forallb_canon_branch_ofv P f n brs :
  All (fun br => onctx (fun t => forall P, on_free_vars P t -> on_free_vars P (canon t))
                       br.(bcontext) ×
                 (forall P, on_free_vars P br.(bbody) -> on_free_vars P (canon br.(bbody)))) brs ->
  forallb (fun br => test_context_k f n br.(bcontext) &&
                     on_free_vars (shiftnP #|br.(bcontext)| P) br.(bbody)) brs ->
  forallb (fun br => test_context_k f n br.(bcontext) &&
                     on_free_vars (shiftnP #|br.(bcontext)| P) br.(bbody))
          (map (canon_branch canon) brs).
Proof.
  induction 1 as [|br brs [_ Hb] _ IH]; cbn; [reflexivity|].
  move/andP => [/andP [h1 h2] h3]. apply/andP. split; [|auto].
  unfold canon_branch; cbn. rewrite canon_ctx_length test_context_k_canon.
  apply/andP. split; [exact h1|auto].
Qed.

(** The proof dispatches EXPLICITLY, one bullet per term constructor, with no
    [auto] prelude: an [auto] prelude closes [tProj] as well as the leaf cases,
    which silently shifts every later bullet. And it unfolds with
    [cbn [on_free_vars canon]], never a bare [cbn], which would also unfold
    [andb] into an [if] and leave the ssreflect views nothing to apply to. *)
Lemma canon_on_free_vars P t : on_free_vars P t -> on_free_vars P (canon t).
Proof.
  induction t in P |- * using term_forall_list_ind; cbn [on_free_vars canon].
  - (* tRel *) auto.
  - (* tVar *) auto.
  - (* tEvar *) apply forallb_canon_ofv. exact X.
  - (* tSort *) auto.
  - (* tProd *) move/andP => [h1 h2]. apply/andP. split; auto.
  - (* tLambda *) move/andP => [_ h2]. apply/andP. split; [reflexivity|auto].
  - (* tLetIn *) move/and3P => [h1 h2 h3]. apply/and3P. split; auto.
  - (* tApp *) move/andP => [h1 h2]. apply/andP. split; auto.
  - (* tConst *) auto.
  - (* tInd *) auto.
  - (* tConstruct *) auto.
  - (* tCase *) destruct X as (Hpar & _ & Hret).
    unfold canon_predicate; cbn [pparams pcontext preturn].
    move/and5P => [hp hr hc hd hbrs]. apply/and5P. split.
    + now apply forallb_canon_ofv.
    + rewrite canon_ctx_length. now apply Hret.
    + rewrite length_map test_context_k_canon. exact hc.
    + now apply IHt.
    + rewrite length_map. now apply forallb_canon_branch_ofv.
  - (* tProj *) auto.
  - (* tFix *) rewrite length_map. now apply forallb_canon_def_ofv.
  - (* tCoFix *) rewrite length_map. now apply forallb_canon_def_ofv.
  - (* tPrim *) destruct p as [? m]; destruct m; cbn in X |- *; auto.
    destruct X as (Hty & Hdef & Hval). simp test_prim; cbn.
    move/andP => [/andP [hv hd] ht]. apply/andP. split; [apply/andP; split|].
    + now apply forallb_canon_ofv.
    + now apply Hdef.
    + now apply Hty.
Qed.

(** The [Q]-facing corollary: [canon] preserves [is_open_term]. *)
Lemma canon_is_open_term (Γ : context) t : is_open_term Γ t -> is_open_term Γ (canon t).
Proof. apply canon_on_free_vars. Qed.
