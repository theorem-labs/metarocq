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

(** ** Strong (nested [All2]-aware) induction principle for [peta] *)

Lemma peta_ind_all (P : term -> term -> Type) :
  (forall na A M M', peta M M' -> P M M' ->
     P (tLambda na A (tApp (lift0 1 M) (tRel 0))) M') ->
  (forall n, P (tRel n) (tRel n)) ->
  (forall i, P (tVar i) (tVar i)) ->
  (forall s, P (tSort s) (tSort s)) ->
  (forall c u, P (tConst c u) (tConst c u)) ->
  (forall ind u, P (tInd ind u) (tInd ind u)) ->
  (forall ind n u, P (tConstruct ind n u) (tConstruct ind n u)) ->
  (forall ev l l', All2 (Trel_conj peta P) l l' -> P (tEvar ev l) (tEvar ev l')) ->
  (forall na A A' M M', peta A A' -> P A A' -> peta M M' -> P M M' ->
     P (tLambda na A M) (tLambda na A' M')) ->
  (forall t t' u u', peta t t' -> P t t' -> peta u u' -> P u u' ->
     P (tApp t u) (tApp t' u')) ->
  (forall na a a' b b', peta a a' -> P a a' -> peta b b' -> P b b' ->
     P (tProd na a b) (tProd na a' b')) ->
  (forall na b b' ty ty' u u', peta b b' -> P b b' -> peta ty ty' -> P ty ty' ->
     peta u u' -> P u u' -> P (tLetIn na b ty u) (tLetIn na b' ty' u')) ->
  (forall ci p p' c c' brs brs',
     All2 (Trel_conj peta P) p.(pparams) p'.(pparams) ->
     p.(puinst) = p'.(puinst) ->
     p.(pcontext) = p'.(pcontext) ->
     peta p.(preturn) p'.(preturn) -> P p.(preturn) p'.(preturn) ->
     peta c c' -> P c c' ->
     All2 (fun x y => (x.(bcontext) = y.(bcontext))
                      × Trel_conj peta P x.(bbody) y.(bbody)) brs brs' ->
     P (tCase ci p c brs) (tCase ci p' c' brs')) ->
  (forall pr c c', peta c c' -> P c c' -> P (tProj pr c) (tProj pr c')) ->
  (forall mfix mfix' idx,
     All2 (fun d d' => Trel_conj peta P d.(dtype) d'.(dtype)
                       × Trel_conj peta P d.(dbody) d'.(dbody)
                       × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
     P (tFix mfix idx) (tFix mfix' idx)) ->
  (forall mfix mfix' idx,
     All2 (fun d d' => Trel_conj peta P d.(dtype) d'.(dtype)
                       × Trel_conj peta P d.(dbody) d'.(dbody)
                       × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
     P (tCoFix mfix idx) (tCoFix mfix' idx)) ->
  (forall p p', onPrims (Trel_conj peta P) eq p p' -> P (tPrim p) (tPrim p')) ->
  forall t t', peta t t' -> P t t'.
Proof.
  intros Heta HRel HVar HSort HConst HInd HCtor HEvar HLam HApp HProd HLet
         HCase HProj HFix HCoFix HPrim.
  fix aux 3. intros t t' H. move aux at top.
  destruct H as
    [ na A M M' pM
    | n | i | s | cst u | ind u | ind k u
    | ev l l' al
    | na A A' M M' pA pM
    | f f' u u' pf pu
    | na a a' b b' pa pb
    | na b b' ty ty' u u' pb pty pu
    | ci p p' c c' brs brs' apar eu ectx pret pc abrs
    | pr c c' pc
    | mfix mfix' idx am
    | mfix mfix' idx am
    | pp pp' op ].
  - (* peta_eta *) eapply Heta; [exact pM|apply aux; exact pM].
  - apply HRel.
  - apply HVar.
  - apply HSort.
  - apply HConst.
  - apply HInd.
  - apply HCtor.
  - (* tEvar *)
    eapply HEvar. revert l l' al.
    fix auxl 3. intros l l' Hl; destruct Hl.
    + constructor.
    + constructor; [split; [assumption|apply aux; assumption]|apply auxl; assumption].
  - (* tLambda *) eapply HLam; [exact pA|apply aux; exact pA|exact pM|apply aux; exact pM].
  - (* tApp *) eapply HApp; [exact pf|apply aux; exact pf|exact pu|apply aux; exact pu].
  - (* tProd *) eapply HProd; [exact pa|apply aux; exact pa|exact pb|apply aux; exact pb].
  - (* tLetIn *)
    eapply HLet; [exact pb|apply aux; exact pb|exact pty|apply aux; exact pty
                 |exact pu|apply aux; exact pu].
  - (* tCase *)
    eapply HCase; [| exact eu | exact ectx | exact pret | apply aux; exact pret
                  | exact pc | apply aux; exact pc |].
    + revert apar. generalize (pparams p) (pparams p').
      fix auxl 3. intros l l' Hl; destruct Hl.
      * constructor.
      * constructor; [split; [assumption|apply aux; assumption]|apply auxl; assumption].
    + revert abrs. generalize brs brs'.
      fix auxl 3. intros l l' Hl; destruct Hl as [|x y ll ll' rh rt].
      * constructor.
      * constructor; [|apply auxl; exact rt].
        destruct rh as [Hc Hb]. split; [exact Hc|].
        split; [exact Hb|apply aux; exact Hb].
  - (* tProj *) eapply HProj; [exact pc|apply aux; exact pc].
  - (* tFix *)
    eapply HFix. revert am. generalize mfix mfix'.
    fix auxl 3. intros l l' Hl; destruct Hl as [|x y ll ll' rh rt].
    + constructor.
    + constructor; [|apply auxl; exact rt].
      destruct rh as [Hty [Hbo [Hn Hr]]].
      split; [split; [exact Hty|apply aux; exact Hty]|].
      split; [split; [exact Hbo|apply aux; exact Hbo]|].
      split; assumption.
  - (* tCoFix *)
    eapply HCoFix. revert am. generalize mfix mfix'.
    fix auxl 3. intros l l' Hl; destruct Hl as [|x y ll ll' rh rt].
    + constructor.
    + constructor; [|apply auxl; exact rt].
      destruct rh as [Hty [Hbo [Hn Hr]]].
      split; [split; [exact Hty|apply aux; exact Hty]|].
      split; [split; [exact Hbo|apply aux; exact Hbo]|].
      split; assumption.
  - (* tPrim *)
    eapply HPrim. destruct op; try solve [constructor].
    constructor;
      [ assumption
      | split; [assumption|apply aux; assumption]
      | split; [assumption|apply aux; assumption]
      | ].
    match goal with H : All2 peta _ _ |- _ => revert H end.
    generalize (array_value a) (array_value a').
    fix auxl 3. intros l l' Hl; destruct Hl.
    + constructor.
    + constructor; [split; [assumption|apply aux; assumption]|apply auxl; assumption].
Qed.

(** ** [eta1] refines to a single parallel step *)

Lemma OnOne2_All2_refl {A} (R S : A -> A -> Type) l l' :
  OnOne2 R l l' -> (forall x, S x x) -> (forall x y, R x y -> S x y) ->
  All2 S l l'.
Proof.
  intros H Hrefl Himpl. induction H.
  - constructor; [now apply Himpl|].
    clear -Hrefl. induction tl; constructor; auto.
  - constructor; [apply Hrefl|assumption].
Qed.

Lemma eta1_peta t u : eta1 t u -> peta t u.
Proof.
  induction 1 using eta1_ind_all.
  - (* eta_red *) apply peta_eta, peta_refl.
  - (* abs_eta_l : domain *) apply peta_Lambda; [assumption|apply peta_refl].
  - (* abs_eta_r : body *) apply peta_Lambda; [apply peta_refl|assumption].
  - (* letin def *) apply peta_LetIn; [assumption|apply peta_refl|apply peta_refl].
  - (* letin ty *) apply peta_LetIn; [apply peta_refl|assumption|apply peta_refl].
  - (* letin body *) apply peta_LetIn; [apply peta_refl|apply peta_refl|assumption].
  - (* case param *)
    apply peta_Case; try reflexivity; try apply peta_refl.
    + eapply OnOne2_All2_refl;
        [eassumption | intros ?; apply peta_refl | intros x y [? ?]; assumption].
    + apply All2_same. intros; split; [reflexivity|apply peta_refl].
  - (* case return *)
    apply peta_Case; try reflexivity; try apply peta_refl.
    + apply All2_same. intros; apply peta_refl.
    + assumption.
    + apply All2_same. intros; split; [reflexivity|apply peta_refl].
  - (* case discr *)
    apply peta_Case; try reflexivity; try apply peta_refl.
    + apply All2_same. intros; apply peta_refl.
    + assumption.
    + apply All2_same. intros; split; [reflexivity|apply peta_refl].
  - (* case brs *)
    apply peta_Case; try reflexivity; try apply peta_refl.
    + apply All2_same. intros; apply peta_refl.
    + eapply OnOne2_All2_refl;
        [ eassumption
        | intros ?; split; [reflexivity|apply peta_refl]
        | intros x y [[? Hp] Hc]; split; [exact Hc|exact Hp] ].
  - (* proj *) apply peta_Proj; assumption.
  - (* app l *) apply peta_App; [assumption|apply peta_refl].
  - (* app r *) apply peta_App; [apply peta_refl|assumption].
  - (* prod l *) apply peta_Prod; [assumption|apply peta_refl].
  - (* prod r *) apply peta_Prod; [apply peta_refl|assumption].
  - (* evar *)
    apply peta_Evar.
    eapply OnOne2_All2_refl;
      [eassumption | intros ?; apply peta_refl | intros x y [? ?]; assumption].
  - (* fix ty *)
    apply peta_Fix.
    eapply OnOne2_All2_refl;
      [ eassumption
      | intros ?; repeat split; try apply peta_refl; reflexivity
      | ].
    intros x y [[He Hp] Heq].
    assert (Hdn : dname x = dname y) by (now inversion Heq).
    assert (Hdb : dbody x = dbody y) by (now inversion Heq).
    assert (Hrr : rarg x = rarg y) by (now inversion Heq).
    split; [exact Hp|split; [rewrite Hdb; apply peta_refl|split; [exact Hdn|exact Hrr]]].
  - (* fix body *)
    apply peta_Fix.
    eapply OnOne2_All2_refl;
      [ eassumption
      | intros ?; repeat split; try apply peta_refl; reflexivity
      | ].
    intros x y [[He Hp] Heq].
    assert (Hdn : dname x = dname y) by (now inversion Heq).
    assert (Hdt : dtype x = dtype y) by (now inversion Heq).
    assert (Hrr : rarg x = rarg y) by (now inversion Heq).
    split; [rewrite Hdt; apply peta_refl|split; [exact Hp|split; [exact Hdn|exact Hrr]]].
  - (* cofix ty *)
    apply peta_CoFix.
    eapply OnOne2_All2_refl;
      [ eassumption
      | intros ?; repeat split; try apply peta_refl; reflexivity
      | ].
    intros x y [[He Hp] Heq].
    assert (Hdn : dname x = dname y) by (now inversion Heq).
    assert (Hdb : dbody x = dbody y) by (now inversion Heq).
    assert (Hrr : rarg x = rarg y) by (now inversion Heq).
    split; [exact Hp|split; [rewrite Hdb; apply peta_refl|split; [exact Hdn|exact Hrr]]].
  - (* cofix body *)
    apply peta_CoFix.
    eapply OnOne2_All2_refl;
      [ eassumption
      | intros ?; repeat split; try apply peta_refl; reflexivity
      | ].
    intros x y [[He Hp] Heq].
    assert (Hdn : dname x = dname y) by (now inversion Heq).
    assert (Hdt : dtype x = dtype y) by (now inversion Heq).
    assert (Hrr : rarg x = rarg y) by (now inversion Heq).
    split; [rewrite Hdt; apply peta_refl|split; [exact Hp|split; [exact Hdn|exact Hrr]]].
  - (* array val *)
    apply peta_Prim. constructor; try reflexivity; try apply peta_refl.
    eapply OnOne2_All2_refl;
      [eassumption | intros ?; apply peta_refl | intros x y [? ?]; assumption].
  - (* array def *)
    apply peta_Prim. constructor.
    + reflexivity.
    + assumption.
    + apply peta_refl.
    + apply All2_same; intros; apply peta_refl.
  - (* array type *)
    apply peta_Prim. constructor.
    + reflexivity.
    + apply peta_refl.
    + assumption.
    + apply All2_same; intros; apply peta_refl.
Qed.

(** ** [peta] commutes with lifting and (single) substitution *)

Lemma peta_lift np t t' (H : peta t t') :
  forall k, peta (lift np k t) (lift np k t').
Proof.
  induction H using peta_ind_all; intros k; cbn;
    try solve [econstructor; eauto].
  - (* eta *)
    replace (S k) with (k + 1) by lia.
    rewrite <- (permute_lift M np k 1 0) by lia.
    change (lift 1 0 ?x) with (lift0 1 x).
    apply peta_eta. apply IHpeta.
  - (* tEvar *)
    constructor. apply All2_map.
    eapply All2_impl; [eassumption|]. intros x y [_ Hk]. apply Hk.
  - (* tCase *)
    apply peta_Case; cbn.
    + apply All2_map. eapply All2_impl; [eassumption|].
      intros x y [_ Hk]. apply Hk.
    + assumption.
    + assumption.
    + match goal with H : pcontext _ = pcontext _ |- _ => rewrite H end.
      eauto.
    + eauto.
    + apply All2_map. eapply All2_impl; [eassumption|].
      intros x y [Hc [_ Hk]]. cbn. split; [exact Hc|].
      rewrite Hc. apply Hk.
  - (* tFix *)
    constructor.
    match goal with H : All2 _ ?m ?m' |- _ => pose proof (All2_length H) as Hlen end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht|]. split; [rewrite Hlen; apply Hb|]. split; [exact Hn|exact Hr].
  - (* tCoFix *)
    constructor.
    match goal with H : All2 _ ?m ?m' |- _ => pose proof (All2_length H) as Hlen end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht|]. split; [rewrite Hlen; apply Hb|]. split; [exact Hn|exact Hr].
  - (* tPrim *)
    constructor.
    match goal with
    | H : onPrims _ _ _ _ |- _ =>
        destruct H as [i|fl|st|arr arr' Hlvl Hdef Hty Hval]
    end; cbn; try solve [constructor].
    constructor; cbn.
    + exact Hlvl.
    + destruct Hdef as [_ Hd]. apply Hd.
    + destruct Hty as [_ Ht]. apply Ht.
    + apply All2_map. eapply All2_impl; [exact Hval|]. intros x y [_ Hk]. apply Hk.
Qed.

Lemma peta_subst1 M M' (H : peta M M') :
  forall N N' k, peta N N' -> peta (subst [N] k M) (subst [N'] k M').
Proof.
  induction H using peta_ind_all; intros N N' k HN; cbn;
    try solve [econstructor; eauto].
  - (* eta *)
    rewrite !commut_lift_subst.
    apply peta_eta. apply IHpeta; assumption.
  - (* tRel *)
    destruct (le_lt_dec k n) as [Hle|Hlt].
    + assert (Hb : Nat.leb k n = true) by (apply Nat.leb_le; exact Hle).
      rewrite Hb.
      destruct (Nat.eq_dec n k) as [->|Hne].
      * rewrite Nat.sub_diag. cbn. now apply peta_lift.
      * destruct (n - k) as [|m] eqn:Hnk; [lia|]. destruct m; cbn; apply peta_Rel.
    + assert (Hb : Nat.leb k n = false) by (apply Nat.leb_gt; exact Hlt).
      rewrite Hb. apply peta_Rel.
  - (* tEvar *)
    constructor. apply All2_map.
    eapply All2_impl; [eassumption|]. intros x y [_ Hk]. apply Hk; assumption.
  - (* tCase *)
    apply peta_Case; cbn.
    + apply All2_map. eapply All2_impl; [eassumption|].
      intros x y [_ Hk]. apply Hk; assumption.
    + assumption.
    + assumption.
    + match goal with He : pcontext _ = pcontext _ |- _ => rewrite He end.
      eauto.
    + eauto.
    + apply All2_map. eapply All2_impl; [eassumption|].
      intros x y [Hc [_ Hk]]. cbn. split; [exact Hc|].
      rewrite Hc. apply Hk; assumption.
  - (* tFix *)
    constructor.
    match goal with He : All2 _ ?m ?m' |- _ => pose proof (All2_length He) as Hlen end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht; assumption|].
    split; [rewrite Hlen; apply Hb; assumption|]. split; [exact Hn|exact Hr].
  - (* tCoFix *)
    constructor.
    match goal with He : All2 _ ?m ?m' |- _ => pose proof (All2_length He) as Hlen end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht; assumption|].
    split; [rewrite Hlen; apply Hb; assumption|]. split; [exact Hn|exact Hr].
  - (* tPrim *)
    constructor.
    match goal with
    | He : onPrims _ _ _ _ |- _ =>
        destruct He as [i|fl|st|arr arr' Hlvl Hdef Hty Hval]
    end; cbn; try solve [constructor].
    constructor; cbn.
    + exact Hlvl.
    + destruct Hdef as [_ Hd]. apply Hd; assumption.
    + destruct Hty as [_ Ht]. apply Ht; assumption.
    + apply All2_map. eapply All2_impl; [exact Hval|].
      intros x y [_ Hk]. apply Hk; assumption.
Qed.
