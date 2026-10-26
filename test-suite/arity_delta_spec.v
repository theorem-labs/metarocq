(* Distributed under the terms of the MIT license. *)
(** Spec-level controls for [ind_arity_red] (BET-64, ArityLane row O).

    [arity_delta.v] tests the verified checker.  This file tests the
    specification it is proved against: the relation [PCUICArityRed.arity_red]
    that [on_ind_body]'s field [ind_arity_red] uses.

    - Positive: [arity_red] derives the index context that Rocq's kernel stores
      for B1's alias [ad_right], for A10's [ad_relar] (a let-bound variable is
      unfolded without zeta) and for A11's [ad_fbar] (the [whd_all] fallback).
    - Negative: no [arity_red] derivation exists, for any sort, for the
      contexts of B8, B9, B11 and B12.  Each proof uses the positive
      derivation of the real shape and [arity_red_det].  So the specification
      itself refuses these declarations, not only the checker.

    The PCUIC environment is written by hand.  Its constants copy the bodies of
    the Rocq definitions of the same name in [arity_delta.v].  The sorts that
    annotate let-bound types and [fun X : Type] stand for the universes that
    Rocq infers.  [arity_red] only copies them into the context, so their value
    does not change any result here. *)

From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICArityRed.
Local Open Scope bs_scope.

(** * The environment *)

Definition ad_mp : modpath := MPfile ["arity_delta"; "TestSuite"; "MetaRocq"].
Definition ad_kn (s : ident) : kername := (ad_mp, s).

Definition ad_natI : inductive :=
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
Definition tnat : term := tInd ad_natI [].
Definition tProp : term := tSort sProp.
Definition tSet : term := tSort Sort.type0.
Definition tTy : term := tSort Sort.type1.

Definition anon : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nm (s : ident) : aname := {| binder_name := nNamed s; binder_relevance := Relevant |}.

(** [ad_right : Type := nat -> Prop] (B1). *)
Definition right_body : term := tProd anon tnat tProp.
(** [ad_zero : Type := Prop] (B6, B8). *)
Definition zero_body : term := tProp.
(** [ad_letar : Type := let X := nat in X -> Prop] (A7, B9). *)
Definition letar_body : term := tLetIn (nm "X") tnat tSet (tProd anon (tRel 0) tProp).
(** [ad_relar : Type := let Z := (let W := nat in W -> Prop) in Z] (A10, B11). *)
Definition relar_inner : term := tLetIn (nm "W") tnat tSet (tProd anon (tRel 0) tProp).
Definition relar_body : term := tLetIn (nm "Z") relar_inner tTy (tRel 0).
(** [ad_relbad : Type := let Z := (let W := nat in W -> Prop) in nat -> Prop],
    the source of B11's context. *)
Definition relbad_body : term := tLetIn (nm "Z") relar_inner tTy (tProd anon tnat tProp).
(** [ad_fbar : Type := (let F := fun X : Type => X -> Prop in F) nat] (A11, B12). *)
Definition fbar_fun : term := tLambda (nm "X") tTy (tProd anon (tRel 0) tProp).
Definition fbar_fty : term := tProd (nm "X") tTy tTy.
Definition fbar_body : term := tApp (tLetIn (nm "F") fbar_fun fbar_fty (tRel 0)) tnat.
(** [ad_keepf : Type := let F := fun X : Type => X -> Prop in F nat], the
    source of B12's context. *)
Definition keepf_body : term := tLetIn (nm "F") fbar_fun fbar_fty (tApp (tRel 0) tnat).

Definition ad_cb (b : term) : constant_body :=
  {| cst_type := tTy; cst_body := Some b; cst_universes := Monomorphic_ctx;
     cst_relevance := Relevant |}.

Definition ad_Σ : global_env :=
  {| universes := ContextSet.empty;
     declarations :=
       [(ad_kn "ad_right", ConstantDecl (ad_cb right_body));
        (ad_kn "ad_zero", ConstantDecl (ad_cb zero_body));
        (ad_kn "ad_letar", ConstantDecl (ad_cb letar_body));
        (ad_kn "ad_relar", ConstantDecl (ad_cb relar_body));
        (ad_kn "ad_relbad", ConstantDecl (ad_cb relbad_body));
        (ad_kn "ad_fbar", ConstantDecl (ad_cb fbar_body));
        (ad_kn "ad_keepf", ConstantDecl (ad_cb keepf_body))];
     retroknowledge := Retroknowledge.empty |}.

Definition ad_const (s : ident) : term := tConst (ad_kn s) [].

(** * Index contexts (innermost declaration first)

    These are the contexts the kernel stores ([mind_arity_ctxt] minus the
    parameters; none of these blocks has parameters), see the comments of
    [arity_delta.v]. *)

(** [_ : nat]: [ad_src], [ad_empty], [ad_fempty]. *)
Definition nat_idx : context := [vass anon tnat].
(** [X := nat; _ : X]: [ad_letind]. *)
Definition letar_idx : context := [vass anon (tRel 0); vdef (nm "X") tnat tSet].
(** [Z := (let W := nat in W -> Prop); W := nat; _ : W]: [ad_relind]. *)
Definition relar_idx : context :=
  [vass anon (tRel 0); vdef (nm "W") tnat tSet; vdef (nm "Z") relar_inner tTy].
(** [Z := (let W := nat in W -> Prop); _ : nat]: [ad_relbadind] (B11). *)
Definition relbad_idx : context := [vass anon tnat; vdef (nm "Z") relar_inner tTy].
(** [F := fun X : Type => X -> Prop; _ : nat]: [ad_keepfind] (B12). *)
Definition keepf_idx : context := [vass anon tnat; vdef (nm "F") fbar_fun fbar_fty].
(** [x := 0 : nat]: B8's fabricated let index ([ad_let_idx]). *)
Definition let_idx : context := [vdef (nm "x") (tConstruct ad_natI 0 []) tnat].

(** * Positive derivations *)

Ltac ad_delta :=
  eapply whd_delta; [first [reflexivity | cbv; reflexivity] | reflexivity | cbn].
Ltac ad_stop := apply whd_stop; reflexivity.

(** B1: the alias [ad_right] against [_ : nat], sort [Prop]. *)
Lemma ad_B1_arity : arity_red ad_Σ [] (ad_const "ad_right") nat_idx sProp.
Proof.
  refine (arity_red_prod ad_Σ [] _ anon tnat tProp [] sProp _ _).
  - ad_delta. ad_stop.
  - apply arity_red_sort. ad_stop.
Qed.

(** A10: [whd_allnolet] keeps the let [Z], then unfolds the let-bound variable
    [Z] without zeta ([whd_rel_unfold]) and keeps the second let [W]. *)
Lemma ad_A10_arity : arity_red ad_Σ [] (ad_const "ad_relar") relar_idx sProp.
Proof.
  refine (arity_red_let ad_Σ [] _ (nm "Z") relar_inner tTy (tRel 0)
            [vass anon (tRel 0); vdef (nm "W") tnat tSet] sProp _ _).
  { ad_delta. apply whd_letin_stop. reflexivity. }
  refine (arity_red_let ad_Σ _ (tRel 0) (nm "W") tnat tSet (tProd anon (tRel 0) tProp)
            [vass anon (tRel 0)] sProp _ _).
  { eapply whd_rel_unfold; [reflexivity | reflexivity |]. cbn.
    apply whd_letin_stop. reflexivity. }
  refine (arity_red_prod ad_Σ _ _ anon (tRel 0) tProp [] sProp _ _).
  - ad_stop.
  - apply arity_red_sort. ad_stop.
Qed.

(** A11: [whd_allnolet] stops at [App (LetIn ...)], so the derivation takes the
    [whd_all] fallback, which zeta- and beta-reduces to [nat -> Prop]. *)
Lemma ad_A11_arity : arity_red ad_Σ [] (ad_const "ad_fbar") nat_idx sProp.
Proof.
  eapply (arity_red_fallback ad_Σ [] _ (tLetIn (nm "F") fbar_fun fbar_fty (tRel 0)) [tnat]
            (tProd anon tnat tProp) []).
  - ad_delta. apply whd_app. apply whd_letin_stop. reflexivity.
  - reflexivity.
  - cbn. apply whd_app. apply whd_zeta; [reflexivity |]. cbn.
    apply whd_beta. cbn. ad_stop.
  - cbn. discriminate.
  - refine (arity_red_prod ad_Σ [] _ anon tnat tProp [] sProp _ _).
    + ad_stop.
    + apply arity_red_sort. ad_stop.
Qed.

(** The real shapes of the terms that B8 and B9 doctor, and the derivations of
    the contexts that B11 and B12 fabricate, from the terms that produce them:
    each fabricated context is a genuine [arity_red] result, only of another
    term. *)

Lemma ad_zero_arity : arity_red ad_Σ [] (ad_const "ad_zero") [] sProp.
Proof. apply arity_red_sort. ad_delta. ad_stop. Qed.

Lemma ad_letar_arity : arity_red ad_Σ [] (ad_const "ad_letar") letar_idx sProp.
Proof.
  refine (arity_red_let ad_Σ [] _ (nm "X") tnat tSet (tProd anon (tRel 0) tProp)
            [vass anon (tRel 0)] sProp _ _).
  { ad_delta. apply whd_letin_stop. reflexivity. }
  refine (arity_red_prod ad_Σ _ _ anon (tRel 0) tProp [] sProp _ _).
  - ad_stop.
  - apply arity_red_sort. ad_stop.
Qed.

Lemma ad_relbad_arity : arity_red ad_Σ [] (ad_const "ad_relbad") relbad_idx sProp.
Proof.
  refine (arity_red_let ad_Σ [] _ (nm "Z") relar_inner tTy (tProd anon tnat tProp)
            [vass anon tnat] sProp _ _).
  { ad_delta. apply whd_letin_stop. reflexivity. }
  refine (arity_red_prod ad_Σ _ _ anon tnat tProp [] sProp _ _).
  - ad_stop.
  - apply arity_red_sort. ad_stop.
Qed.

Lemma ad_keepf_arity : arity_red ad_Σ [] (ad_const "ad_keepf") keepf_idx sProp.
Proof.
  refine (arity_red_let ad_Σ [] _ (nm "F") fbar_fun fbar_fty (tApp (tRel 0) tnat)
            [vass anon tnat] sProp _ _).
  { ad_delta. apply whd_letin_stop. reflexivity. }
  refine (arity_red_prod ad_Σ _ _ anon tnat tProp [] sProp _ _).
  - apply whd_app. eapply whd_rel_unfold; [reflexivity | reflexivity |]. cbn.
    apply whd_beta. cbn. ad_stop.
  - apply arity_red_sort. ad_stop.
Qed.

(** * Negative controls: no derivation, for any sort *)

Ltac ad_refute pos :=
  let d := fresh "d" in let e := fresh "e" in
  intros d; destruct (arity_red_det pos d) as [e _]; cbv in e; discriminate e.

(** B8: [ad_zero] reduces to [Prop]; the fabricated let index is refused. *)
Lemma ad_B8_no_arity s : arity_red ad_Σ [] (ad_const "ad_zero") let_idx s -> False.
Proof. ad_refute ad_zero_arity. Qed.

(** B9: [ad_letar] keeps its let; [_ : nat] alone is refused. *)
Lemma ad_B9_no_arity s : arity_red ad_Σ [] (ad_const "ad_letar") nat_idx s -> False.
Proof. ad_refute ad_letar_arity. Qed.

(** B11: [ad_relar] against [ad_relbadind]'s context
    [Z := (let W := nat in W -> Prop); _ : nat]: refused, because the
    let-bound [Z] is unfolded without zeta and exposes the let [W]. *)
Lemma ad_B11_no_arity s : arity_red ad_Σ [] (ad_const "ad_relar") relbad_idx s -> False.
Proof. ad_refute ad_A10_arity. Qed.

(** B12: [ad_fbar] against [ad_keepfind]'s kept-let context: refused, because
    the [whd_all] fallback contracts the internal let. *)
Lemma ad_B12_no_arity s : arity_red ad_Σ [] (ad_const "ad_fbar") keepf_idx s -> False.
Proof. ad_refute ad_A11_arity. Qed.

(** * Assumptions

    Compare with the base library's own [arity_red_det] and [whd_rel_det]. *)
Print Assumptions whd_rel_det.
Print Assumptions arity_red_det.
Print Assumptions ad_B1_arity.
Print Assumptions ad_A10_arity.
Print Assumptions ad_A11_arity.
Print Assumptions ad_B8_no_arity.
Print Assumptions ad_B9_no_arity.
Print Assumptions ad_B11_no_arity.
Print Assumptions ad_B12_no_arity.
