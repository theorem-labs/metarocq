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
     PCUICInduction PCUICLiftSubst PCUICSigmaCalculus PCUICEquality PCUICCases
     PCUICOnFreeVars PCUICTyping PCUICReduction PCUICEtaDefs.

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

(** ** [peta] on application spines *)

Lemma peta_mkApps f f' args args' :
  peta f f' -> All2 peta args args' -> peta (mkApps f args) (mkApps f' args').
Proof.
  intros Hf Ha. induction Ha in f, f', Hf |- *; cbn; [assumption|].
  apply IHHa. now apply peta_App.
Qed.

(** Only [peta_App] produces [peta (tApp _ _) _] (the η-rule's left side is a
    [tLambda]), so a [peta] step on a spine distributes over head and arguments. *)
Lemma peta_mkApps_inv f args u :
  peta (mkApps f args) u ->
  ∑ f' args', (u = mkApps f' args') × peta f f' × All2 peta args args'.
Proof.
  induction args in f, u |- *; cbn; intros H.
  - exists u, []. repeat split; auto.
  - destruct (IHargs _ _ H) as (g & args'' & -> & Hg & Ha).
    depelim Hg.
    exists t', (u' :: args''). repeat split; cbn; auto.
Qed.

(** General (list) substitution. *)
Lemma peta_subst M M' (H : peta M M') :
  forall ss ss' k, All2 peta ss ss' -> peta (subst ss k M) (subst ss' k M').
Proof.
  induction H using peta_ind_all; intros ss ss' k HS; cbn;
    try solve [econstructor; eauto].
  - (* eta *)
    rewrite !commut_lift_subst.
    apply peta_eta. apply IHpeta; assumption.
  - (* tRel *)
    destruct (le_lt_dec k n) as [Hle|Hlt].
    + assert (Hb : Nat.leb k n = true) by (apply Nat.leb_le; exact Hle).
      rewrite Hb.
      destruct (nth_error ss (n - k)) as [b|] eqn:Hs.
      * destruct (All2_nth_error_Some _ _ HS Hs) as (b' & Hs' & Hbb).
        rewrite Hs'. now apply peta_lift.
      * rewrite (All2_nth_error_None _ HS Hs).
        rewrite (All2_length HS). apply peta_Rel.
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
    match goal with
    | |- All2 _ (map _ ?m) (map _ ?m') =>
        match goal with He : All2 _ m m' |- _ => pose proof (All2_length He) as Hlen end
    end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht; assumption|].
    split; [rewrite Hlen; apply Hb; assumption|]. split; [exact Hn|exact Hr].
  - (* tCoFix *)
    constructor.
    match goal with
    | |- All2 _ (map _ ?m) (map _ ?m') =>
        match goal with He : All2 _ m m' |- _ => pose proof (All2_length He) as Hlen end
    end.
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

(** ** [peta] preserves constructor heads, guards and (co)fix unfolding

  This is why the four "unlocking" [red1] rules — [red_fix], [red_cofix_case],
  [red_cofix_proj], [red_proj] — are harmless for the COMMUTATION: a [peta] step
  can only η-contract a [tLambda], so it never turns a constructor/(co)fix head
  into something else, and the guard [is_constructor] survives. (The η-postponement
  form died on the converse direction: η CREATES a constructor head. C3 never has
  to match a redex that appears only on the η side.) *)

Lemma peta_isConstruct_app a b :
  peta a b -> isConstruct_app a = true -> isConstruct_app b = true.
Proof.
  unfold isConstruct_app. intros Hp.
  destruct (decompose_app a) as [hd args] eqn:Ha. cbn.
  destruct hd; try discriminate. intros _.
  apply decompose_app_inv in Ha. subst a.
  apply peta_mkApps_inv in Hp as (f' & args' & -> & Hf & Ha').
  depelim Hf. now rewrite decompose_app_mkApps.
Qed.

Lemma peta_is_constructor n args args' :
  All2 peta args args' -> is_constructor n args = true -> is_constructor n args' = true.
Proof.
  unfold is_constructor. intros Ha.
  destruct (nth_error args n) as [a|] eqn:Hn; [|discriminate].
  destruct (All2_nth_error_Some _ _ Ha Hn) as (a' & Hn' & Haa).
  rewrite Hn'. now apply peta_isConstruct_app.
Qed.

Notation peta_def :=
  (fun d d' => peta d.(dtype) d'.(dtype) × peta d.(dbody) d'.(dbody)
               × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)).

Lemma peta_fix_subst mfix mfix' :
  All2 peta_def mfix mfix' -> All2 peta (fix_subst mfix) (fix_subst mfix').
Proof.
  intros H. pose proof (All2_length H) as Hl.
  unfold fix_subst. rewrite Hl.
  generalize #|mfix'|. intros n. induction n; cbn; constructor; auto.
  now apply peta_Fix.
Qed.

Lemma peta_cofix_subst mfix mfix' :
  All2 peta_def mfix mfix' -> All2 peta (cofix_subst mfix) (cofix_subst mfix').
Proof.
  intros H. pose proof (All2_length H) as Hl.
  unfold cofix_subst. rewrite Hl.
  generalize #|mfix'|. intros n. induction n; cbn; constructor; auto.
  now apply peta_CoFix.
Qed.

Lemma peta_unfold_fix mfix mfix' idx narg fn :
  All2 peta_def mfix mfix' ->
  unfold_fix mfix idx = Some (narg, fn) ->
  ∑ fn', unfold_fix mfix' idx = Some (narg, fn') × peta fn fn'.
Proof.
  unfold unfold_fix. intros H Hu.
  destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate].
  destruct (All2_nth_error_Some _ _ H Hd) as (d' & Hd' & (_ & Hbo & _ & Hr)).
  rewrite Hd'. noconf Hu.
  eexists. split; [now rewrite Hr|].
  eapply peta_subst; [exact Hbo|now apply peta_fix_subst].
Qed.

Lemma peta_unfold_cofix mfix mfix' idx narg fn :
  All2 peta_def mfix mfix' ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ fn', unfold_cofix mfix' idx = Some (narg, fn') × peta fn fn'.
Proof.
  unfold unfold_cofix. intros H Hu.
  destruct (nth_error mfix idx) as [d|] eqn:Hd; [|discriminate].
  destruct (All2_nth_error_Some _ _ H Hd) as (d' & Hd' & (_ & Hbo & _ & Hr)).
  rewrite Hd'. noconf Hu.
  eexists. split; [now rewrite Hr|].
  eapply peta_subst; [exact Hbo|now apply peta_cofix_subst].
Qed.
(** ** The real collision: [red_fix] against a parallel η step

  η-POSTPONEMENT died here because η can CREATE a constructor head and so unlock a
  fixpoint that no reduct of the original unfolds. The COMMUTATION is a different
  claim: [red1 Σ Γ t v] is a hypothesis, so the [tFix] head and the
  [is_constructor] guard already hold in [t]; a [peta] step can only η-contract a
  [tLambda], hence it preserves both ([peta_is_constructor]) and the fix re-fires
  on the η side in exactly ONE [red1] step. The redex η creates is only ever on the
  η side, and C3 never has to match it. *)

Lemma peta_commut_red_fix Σ Γ mfix idx args narg fn u :
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args = true ->
  peta (mkApps (tFix mfix idx) args) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w
        × peta (mkApps fn args) w'
        × upto_domain w w'.
Proof.
  intros Hunf Hic Hp.
  apply peta_mkApps_inv in Hp as (f' & args' & -> & Hf & Ha).
  depelim Hf.
  match goal with Hm : All2 _ mfix ?m |- _ =>
    destruct (peta_unfold_fix _ m _ _ _ Hm Hunf) as (fn' & Hunf' & Hfn) end.
  exists (mkApps fn' args'), (mkApps fn' args').
  repeat split.
  - apply r_step. eapply red_fix; [exact Hunf'|].
    eapply peta_is_constructor; eassumption.
  - apply peta_mkApps; assumption.
  - reflexivity.
Qed.

(** ** Bridge half 2: [peta ⊆ eta := clos_refl_trans eta1]

  [eta] congruence closures, then [peta_eta]. The η rule contracts FIRST
  ([rt_step (eta_red …)]) and then applies the IH, so no [eta1_lift] is needed. *)

Lemma clos_rt_map {A B} (R : A -> A -> Type) (S : B -> B -> Type) (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) ->
  forall x y, clos_refl_trans R x y -> clos_refl_trans S (f x) (f y).
Proof.
  intros Hf x y D. induction D.
  - apply rt_step; now apply Hf.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma OnOne2_rt_hd {A} (R : A -> A -> Type) l x y :
  clos_refl_trans R x y -> clos_refl_trans (OnOne2 R) (x :: l) (y :: l).
Proof.
  intros D. induction D.
  - apply rt_step. now apply OnOne2_hd.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma OnOne2_rt_tl {A} (R : A -> A -> Type) a l l' :
  clos_refl_trans (OnOne2 R) l l' -> clos_refl_trans (OnOne2 R) (a :: l) (a :: l').
Proof.
  intros D. induction D.
  - apply rt_step. now apply OnOne2_tl.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma All2_rt_OnOne2 {A} (R : A -> A -> Type) l l' :
  All2 (clos_refl_trans R) l l' -> clos_refl_trans (OnOne2 R) l l'.
Proof.
  induction 1.
  - apply rt_refl.
  - eapply rt_trans; [apply OnOne2_rt_hd; eassumption|apply OnOne2_rt_tl; assumption].
Qed.

(** Single-position η congruences, each a [clos_rt_map] of an [eta1] congruence. *)
Definition eta_absl na N : forall x y, eta x y -> eta (tLambda na x N) (tLambda na y N) :=
  clos_rt_map _ _ _ (fun x y h => abs_eta_l na x y N h).
Definition eta_absr na A : forall x y, eta x y -> eta (tLambda na A x) (tLambda na A y) :=
  clos_rt_map _ _ _ (fun x y h => abs_eta_r na x y A h).
Definition eta_appl M2 : forall x y, eta x y -> eta (tApp x M2) (tApp y M2) :=
  clos_rt_map _ _ _ (fun x y h => app_eta_l x y M2 h).
Definition eta_appr M1 : forall x y, eta x y -> eta (tApp M1 x) (tApp M1 y) :=
  clos_rt_map _ _ _ (fun x y h => app_eta_r x y M1 h).
Definition eta_prodl M2 na : forall x y, eta x y -> eta (tProd na x M2) (tProd na y M2) :=
  clos_rt_map _ _ _ (fun x y h => prod_eta_l na x M2 y h).
Definition eta_prodr M1 na : forall x y, eta x y -> eta (tProd na M1 x) (tProd na M1 y) :=
  clos_rt_map _ _ _ (fun x y h => prod_eta_r na x y M1 h).
Definition eta_letd na t b' : forall x y, eta x y -> eta (tLetIn na x t b') (tLetIn na y t b') :=
  clos_rt_map _ _ _ (fun x y h => letin_eta_def na x t b' y h).
Definition eta_lett na b b' : forall x y, eta x y -> eta (tLetIn na b x b') (tLetIn na b y b') :=
  clos_rt_map _ _ _ (fun x y h => letin_eta_ty na b x b' y h).
Definition eta_letb na b t : forall x y, eta x y -> eta (tLetIn na b t x) (tLetIn na b t y) :=
  clos_rt_map _ _ _ (fun x y h => letin_eta_body na b t x y h).
Definition eta_proj pr : forall x y, eta x y -> eta (tProj pr x) (tProj pr y) :=
  clos_rt_map _ _ _ (fun x y h => proj_eta pr x y h).
Definition eta_casediscr ci p brs : forall x y, eta x y -> eta (tCase ci p x brs) (tCase ci p y brs) :=
  clos_rt_map _ _ _ (fun x y h => case_eta_discr ci p x y brs h).

Lemma eta_tEvar ev l l' : All2 eta l l' -> eta (tEvar ev l) (tEvar ev l').
Proof.
  intros H. apply (clos_rt_map _ _ (tEvar ev) (fun x y h => evar_eta ev x y h)).
  now apply All2_rt_OnOne2.
Qed.

(** branch list: change bbody via eta* keeping bcontext *)
Lemma eta_brs_hd bc tl x y :
  clos_refl_trans eta1 x y ->
  clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext))
    (mk_branch bc x :: tl) (mk_branch bc y :: tl).
Proof.
  induction 1.
  - apply rt_step. constructor. cbn. split; [assumption|reflexivity].
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma eta_brs brs brs' :
  All2 (fun x y => bcontext x = bcontext y × eta (bbody x) (bbody y)) brs brs' ->
  clos_refl_trans (OnOne2 (on_Trel_eq eta1 bbody bcontext)) brs brs'.
Proof.
  induction 1 as [|x y l l' [Hc Hb] Hl IH].
  - apply rt_refl.
  - destruct x as [bcx bbx], y as [bcy bby]; cbn in *. subst bcy.
    eapply rt_trans.
    + apply (eta_brs_hd bcx l bbx bby Hb).
    + now apply OnOne2_rt_tl.
Qed.

Lemma eta_tCase ci p p' c c' brs brs' :
  All2 eta (pparams p) (pparams p') ->
  puinst p = puinst p' -> pcontext p = pcontext p' ->
  eta (preturn p) (preturn p') -> eta c c' ->
  All2 (fun x y => bcontext x = bcontext y × eta (bbody x) (bbody y)) brs brs' ->
  eta (tCase ci p c brs) (tCase ci p' c' brs').
Proof.
  destruct p as [pp pu pc pr], p' as [pp' pu' pc' pr']; cbn.
  intros Hpar Hu Hpc Hret Hdiscr Hbrs. subst pu' pc'.
  eapply rt_trans.
  { apply (clos_rt_map (OnOne2 eta1) _
             (fun q => tCase ci (mk_predicate q pu pc pr) c brs))
    with (x := pp) (y := pp').
    - intros a b h.
      exact (case_eta_param ci (mk_predicate a pu pc pr) b c brs h).
    - now apply All2_rt_OnOne2. }
  eapply rt_trans.
  { apply (clos_rt_map eta1 _
             (fun q => tCase ci (mk_predicate pp' pu pc q) c brs))
    with (x := pr) (y := pr').
    - intros a b h.
      exact (case_eta_return ci (mk_predicate pp' pu pc a) b c brs h).
    - exact Hret. }
  eapply rt_trans.
  { exact (eta_casediscr ci (mk_predicate pp' pu pc pr') brs _ _ Hdiscr). }
  apply (clos_rt_map (OnOne2 (on_Trel_eq eta1 bbody bcontext)) _
           (fun l => tCase ci (mk_predicate pp' pu pc pr') c' l)
           (fun l l' h => case_eta_brs ci _ c' l l' h)).
  now apply eta_brs.
Qed.

Lemma eta_tPrim_arr arr arr' :
  array_level arr = array_level arr' ->
  eta (array_default arr) (array_default arr') ->
  eta (array_type arr) (array_type arr') ->
  All2 eta (array_value arr) (array_value arr') ->
  eta (tPrim (primArray; primArrayModel arr)) (tPrim (primArray; primArrayModel arr')).
Proof.
  destruct arr as [lvl ty def vals], arr' as [lvl' ty' def' vals']; cbn.
  intros Hl Hdef Hty Hval. subst lvl'.
  eapply rt_trans.
  { apply (clos_rt_map eta1 _
             (fun t => tPrim (primArray; primArrayModel
               {| array_level := lvl; array_type := ty; array_default := t; array_value := vals |})))
    with (x := def) (y := def').
    - intros a b h.
      exact (array_eta_def {| array_level := lvl; array_type := ty; array_default := a; array_value := vals |} b h).
    - exact Hdef. }
  eapply rt_trans.
  { apply (clos_rt_map eta1 _
             (fun t => tPrim (primArray; primArrayModel
               {| array_level := lvl; array_type := t; array_default := def'; array_value := vals |})))
    with (x := ty) (y := ty').
    - intros a b h.
      exact (array_eta_type {| array_level := lvl; array_type := a; array_default := def'; array_value := vals |} b h).
    - exact Hty. }
  apply (clos_rt_map (OnOne2 eta1) _
           (fun l => tPrim (primArray; primArrayModel
             {| array_level := lvl; array_type := ty'; array_default := def'; array_value := l |}))
           (fun l l' h => array_eta_val
             {| array_level := lvl; array_type := ty'; array_default := def'; array_value := l |} l' h)).
  now apply All2_rt_OnOne2.
Qed.

(** mfix: change dtype, then dbody, each via one [eta1] field rule keeping the rest *)
Lemma eta_mfix_ty_hd dn db ra tl x y :
  clos_refl_trans eta1 x y ->
  clos_refl_trans (OnOne2 (on_Trel_eq eta1 dtype (fun d => (dname d, dbody d, rarg d))))
    (mkdef _ dn x db ra :: tl) (mkdef _ dn y db ra :: tl).
Proof.
  induction 1.
  - apply rt_step. constructor. cbn. split; [assumption|reflexivity].
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma eta_mfix_body_hd dn dt ra tl x y :
  clos_refl_trans eta1 x y ->
  clos_refl_trans (OnOne2 (on_Trel_eq eta1 dbody (fun d => (dname d, dtype d, rarg d))))
    (mkdef _ dn dt x ra :: tl) (mkdef _ dn dt y ra :: tl).
Proof.
  induction 1.
  - apply rt_step. constructor. cbn. split; [assumption|reflexivity].
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma eta_mfix_ty mfix mfix' :
  All2 (fun d d' => eta (dtype d) (dtype d') × dname d = dname d'
                    × dbody d = dbody d' × rarg d = rarg d') mfix mfix' ->
  clos_refl_trans (OnOne2 (on_Trel_eq eta1 dtype (fun d => (dname d, dbody d, rarg d))))
    mfix mfix'.
Proof.
  induction 1 as [|x y l l' (Ht & Hn & Hb & Hr) Hl IH].
  - apply rt_refl.
  - destruct x as [dnx dtx dbx rax], y as [dny dty dby ray]; cbn in *.
    subst dny dbx rax.
    eapply rt_trans.
    + apply (eta_mfix_ty_hd dnx dby ray l dtx dty Ht).
    + now apply OnOne2_rt_tl.
Qed.

Lemma eta_mfix_body mfix mfix' :
  All2 (fun d d' => eta (dbody d) (dbody d') × dname d = dname d'
                    × dtype d = dtype d' × rarg d = rarg d') mfix mfix' ->
  clos_refl_trans (OnOne2 (on_Trel_eq eta1 dbody (fun d => (dname d, dtype d, rarg d))))
    mfix mfix'.
Proof.
  induction 1 as [|x y l l' (Hb & Hn & Ht & Hr) Hl IH].
  - apply rt_refl.
  - destruct x as [dnx dtx dbx rax], y as [dny dty dby ray]; cbn in *.
    subst dny dtx rax.
    eapply rt_trans.
    + apply (eta_mfix_body_hd dnx dty ray l dbx dby Hb).
    + now apply OnOne2_rt_tl.
Qed.

Lemma mfix_split mfix mfix' :
  All2 (fun d d' => eta (dtype d) (dtype d') × eta (dbody d) (dbody d')
                    × dname d = dname d' × rarg d = rarg d') mfix mfix' ->
  ∑ mid,
    All2 (fun d d' => eta (dtype d) (dtype d') × dname d = dname d'
                      × dbody d = dbody d' × rarg d = rarg d') mfix mid ×
    All2 (fun d d' => eta (dbody d) (dbody d') × dname d = dname d'
                      × dtype d = dtype d' × rarg d = rarg d') mid mfix'.
Proof.
  induction 1 as [|x y l l' (Ht & Hb & Hn & Hr) Hl (mid & H1 & H2)].
  - exists []. split; constructor.
  - exists (mkdef _ (dname y) (dtype y) (dbody x) (rarg x) :: mid).
    split; constructor; cbn; auto; repeat split; auto.
Qed.

Lemma eta_tFix mfix mfix' idx :
  All2 (fun d d' => eta (dtype d) (dtype d') × eta (dbody d) (dbody d')
                    × dname d = dname d' × rarg d = rarg d') mfix mfix' ->
  eta (tFix mfix idx) (tFix mfix' idx).
Proof.
  intros H. destruct (mfix_split _ _ H) as (mid & H1 & H2).
  eapply rt_trans.
  - apply (clos_rt_map (OnOne2 (on_Trel_eq eta1 dtype (fun d => (dname d, dbody d, rarg d))))
             eta1 (fun m => tFix m idx) (fun a b h => fix_eta_ty a b idx h)).
    now apply eta_mfix_ty.
  - apply (clos_rt_map (OnOne2 (on_Trel_eq eta1 dbody (fun d => (dname d, dtype d, rarg d))))
             eta1 (fun m => tFix m idx) (fun a b h => fix_eta_body a b idx h)).
    now apply eta_mfix_body.
Qed.

Lemma eta_tCoFix mfix mfix' idx :
  All2 (fun d d' => eta (dtype d) (dtype d') × eta (dbody d) (dbody d')
                    × dname d = dname d' × rarg d = rarg d') mfix mfix' ->
  eta (tCoFix mfix idx) (tCoFix mfix' idx).
Proof.
  intros H. destruct (mfix_split _ _ H) as (mid & H1 & H2).
  eapply rt_trans.
  - apply (clos_rt_map (OnOne2 (on_Trel_eq eta1 dtype (fun d => (dname d, dbody d, rarg d))))
             eta1 (fun m => tCoFix m idx) (fun a b h => cofix_eta_ty a b idx h)).
    now apply eta_mfix_ty.
  - apply (clos_rt_map (OnOne2 (on_Trel_eq eta1 dbody (fun d => (dname d, dtype d, rarg d))))
             eta1 (fun m => tCoFix m idx) (fun a b h => cofix_eta_body a b idx h)).
    now apply eta_mfix_body.
Qed.

(** Bridge half 2. *)
Lemma peta_to_eta t u : peta t u -> eta t u.
Proof.
  induction 1 using peta_ind_all.
  - (* eta rule: contract FIRST, then IH; no lift needed *)
    eapply rt_trans; [apply rt_step; apply eta_red|assumption].
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - (* tEvar *) apply eta_tEvar. eapply All2_impl; [eassumption|]. now intros x y [_ ?].
  - (* tLambda *) eapply rt_trans; [apply eta_absl; eassumption|apply eta_absr; eassumption].
  - (* tApp *) eapply rt_trans; [apply eta_appl; eassumption|apply eta_appr; eassumption].
  - (* tProd *) eapply rt_trans; [apply eta_prodl; eassumption|apply eta_prodr; eassumption].
  - (* tLetIn *)
    eapply rt_trans; [apply eta_letd; eassumption|].
    eapply rt_trans; [apply eta_lett; eassumption|apply eta_letb; eassumption].
  - (* tCase *)
    apply eta_tCase; auto.
    + eapply All2_impl; [eassumption|]. now intros x y [_ ?].
    + eapply All2_impl; [eassumption|]. now intros x y [? [_ ?]].
  - (* tProj *) apply eta_proj; assumption.
  - (* tFix *) apply eta_tFix. eapply All2_impl; [eassumption|].
    now intros x y [[_ ?] [[_ ?] [? ?]]].
  - (* tCoFix *) apply eta_tCoFix. eapply All2_impl; [eassumption|].
    now intros x y [[_ ?] [[_ ?] [? ?]]].
  - (* tPrim *)
    match goal with H : onPrims _ _ _ _ |- _ =>
      destruct H as [i|fl|st|arr arr' Hlvl Hdef Hty Hval] end;
      try apply rt_refl.
    apply eta_tPrim_arr; cbn.
    + now apply Universe.make'_inj.
    + destruct Hdef as [_ ?]; assumption.
    + destruct Hty as [_ ?]; assumption.
    + eapply All2_impl; [exact Hval|]. now intros x y [_ ?].
Qed.

(** ** More commutation cases, standalone and green (no eta_subst)

  The remaining "unlocking" rows ([red_cofix_case], [red_cofix_proj], [red_proj])
  copy [peta_commut_red_fix]. The δ/ρ rows ([red_delta], [red_rel]) are forced
  reflexive on the η side (peta on [tConst]/[tRel] is reflexive), so the same red1
  step re-fires. None needs [wf Σ] or scoping: those bite only when a red1 fires
  INSIDE an η-redex peta contracts (the [abs_red_r] kernel, see EtaC3B.md). *)

Lemma peta_commut_red_rel Σ Γ i body u :
  option_map decl_body (nth_error Γ i) = Some (Some body) ->
  peta (tRel i) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta (lift0 (S i) body) w' × upto_domain w w'.
Proof.
  intros H Hp. depelim Hp.
  exists (lift0 (S i) body), (lift0 (S i) body). repeat split.
  - apply r_step. now apply red_rel.
  - apply peta_refl.
  - reflexivity.
Qed.

Lemma peta_commut_red_delta Σ Γ c decl body uu u :
  declared_constant Σ c decl -> cst_body decl = Some body ->
  peta (tConst c uu) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta (subst_instance uu body) w' × upto_domain w w'.
Proof.
  intros Hdecl Hbody Hp. depelim Hp.
  exists (subst_instance uu body), (subst_instance uu body). repeat split.
  - apply r_step. eapply red_delta; eassumption.
  - apply peta_refl.
  - reflexivity.
Qed.

Lemma peta_commut_red_proj Σ Γ pr args uu arg u :
  nth_error args (pr.(proj_npars) + pr.(proj_arg)) = Some arg ->
  peta (tProj pr (mkApps (tConstruct pr.(proj_ind) 0 uu) args)) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta arg w' × upto_domain w w'.
Proof.
  intros Hnth Hp. depelim Hp.
  apply peta_mkApps_inv in Hp as (f' & args' & -> & Hf & Ha). depelim Hf.
  destruct (All2_nth_error_Some _ _ Ha Hnth) as (arg' & Hnth' & Harg).
  exists arg', arg'. repeat split.
  - apply r_step. eapply red_proj; exact Hnth'.
  - exact Harg.
  - reflexivity.
Qed.

Lemma peta_commut_red_cofix_proj Σ Γ pr mfix idx args narg fn u :
  unfold_cofix mfix idx = Some (narg, fn) ->
  peta (tProj pr (mkApps (tCoFix mfix idx) args)) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta (tProj pr (mkApps fn args)) w' × upto_domain w w'.
Proof.
  intros Hunf Hp. depelim Hp.
  apply peta_mkApps_inv in Hp as (f' & args' & -> & Hf & Ha). depelim Hf.
  match goal with Hm : All2 _ mfix ?m |- _ =>
    destruct (peta_unfold_cofix _ m _ _ _ Hm Hunf) as (fn' & Hunf' & Hfn) end.
  exists (tProj pr (mkApps fn' args')), (tProj pr (mkApps fn' args')). repeat split.
  - apply r_step. eapply red_cofix_proj; exact Hunf'.
  - apply peta_Proj, peta_mkApps; assumption.
  - reflexivity.
Qed.

Lemma peta_commut_red_cofix_case Σ Γ ip p mfix idx args narg fn brs u :
  unfold_cofix mfix idx = Some (narg, fn) ->
  peta (tCase ip p (mkApps (tCoFix mfix idx) args) brs) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w
        × peta (tCase ip p (mkApps fn args) brs) w' × upto_domain w w'.
Proof.
  intros Hunf Hp. depelim Hp.
  match goal with Hd : peta (mkApps (tCoFix _ _) _) _ |- _ =>
    apply peta_mkApps_inv in Hd as (f' & args' & Hc & Hf & Ha) end. depelim Hf.
  match goal with Hm : All2 _ mfix ?m |- _ =>
    destruct (peta_unfold_cofix _ m _ _ _ Hm Hunf) as (fn' & Hunf' & Hfn) end.
  eexists _, _. repeat split.
  - apply r_step. rewrite Hc. eapply red_cofix_case; exact Hunf'.
  - eapply peta_Case; try eassumption. apply peta_mkApps; eassumption.
  - reflexivity.
Qed.

(** [red_beta]: the η/β OVERLAP (peta_eta on the function) closes with ZERO β on the
    η side and NO size-induction / wf — it is handled by [simpl_subst], unlike the
    [abs_red_r] kernel. The ordinary (peta_Lambda) subcase is one β via [peta_subst1]. *)
Lemma peta_commut_red_beta Σ Γ na A b a u :
  peta (tApp (tLambda na A b) a) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta (b {0 := a}) w' × upto_domain w w'.
Proof.
  intros Hp. depelim Hp.
  rename Hp1 into Hfun. rename Hp2 into Harg.
  depelim Hfun.
  - (* peta_eta: b = tApp (lift0 1 M) (tRel 0), function contracts to M' *)
    eexists _, _. repeat split.
    + apply r_refl.
    + assert (He : (tApp (lift0 1 M) (tRel 0)) {0 := a} = tApp M a).
      { change ((tApp (lift0 1 M) (tRel 0)) {0 := a})
          with (tApp (subst [a] 0 (lift0 1 M)) (subst [a] 0 (tRel 0))).
        rewrite (simpl_subst_k [a] M 0 1 eq_refl).
        rewrite (subst_rel_eq [a] 0 0 a 0 eq_refl eq_refl).
        now rewrite lift0_p. }
      rewrite He.
      match goal with H : peta M _ |- _ => apply peta_App; [exact H|exact Harg] end.
    + reflexivity.
  - (* peta_Lambda: ordinary beta, one step *)
    eexists _, _. repeat split.
    + apply r_step. apply red_beta.
    + match goal with H : peta b _ |- _ => apply peta_subst1; [exact H|exact Harg] end.
    + reflexivity.
Qed.

Lemma peta_commut_red_zeta Σ Γ na b ty b' u :
  peta (tLetIn na b ty b') u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta (b' {0 := b}) w' × upto_domain w w'.
Proof.
  intros Hp. depelim Hp.
  eexists _, _. repeat split.
  - apply r_step. apply red_zeta.
  - apply peta_subst1; eassumption.
  - reflexivity.
Qed.

(** * The commutation kernel: infrastructure *)

(** ** Contexts related on declaration BODIES only.
    [red1] reads its context only through [red_rel], i.e. only through let-bodies;
    declaration types are irrelevant to it. *)
Definition peta_decl (d d' : context_decl) : Type :=
  match decl_body d, decl_body d' with
  | Some b, Some b' => peta b b'
  | None, None => unit
  | _, _ => Empty_set
  end.

Definition peta_ctx := All2 peta_decl.

Lemma peta_decl_refl d : peta_decl d d.
Proof. unfold peta_decl. destruct (decl_body d); [apply peta_refl|exact tt]. Qed.

Lemma peta_ctx_refl Γ : peta_ctx Γ Γ.
Proof. apply All2_same, peta_decl_refl. Qed.

Lemma peta_ctx_vass Γ Δ na A na' A' :
  peta_ctx Γ Δ -> peta_ctx (Γ ,, vass na A) (Δ ,, vass na' A').
Proof. intros H. constructor; [exact tt|exact H]. Qed.

Lemma peta_ctx_vdef Γ Δ na b t na' b' t' :
  peta_ctx Γ Δ -> peta b b' -> peta_ctx (Γ ,, vdef na b t) (Δ ,, vdef na' b' t').
Proof. intros H Hb. constructor; [exact Hb|exact H]. Qed.

Lemma peta_ctx_app Γ Δ Γ' Δ' :
  peta_ctx Γ Δ -> peta_ctx Γ' Δ' -> peta_ctx (Γ ,,, Γ') (Δ ,,, Δ').
Proof. intros H H'. unfold app_context. now apply All2_app. Qed.

Lemma peta_ctx_assumptions Γ Δ :
  peta_ctx Γ Δ -> context_assumptions Γ = context_assumptions Δ.
Proof.
  induction 1 as [|d d' Γ Δ Hd H IH]; [reflexivity|].
  destruct d as [na [b|] ty], d' as [na' [b'|] ty']; cbn in *;
    try destruct Hd; congruence.
Qed.

Lemma peta_subst_context ss ss' k ctx :
  All2 peta ss ss' -> peta_ctx (subst_context ss k ctx) (subst_context ss' k ctx).
Proof.
  intros Hs. induction ctx as [|d ctx IH]; [constructor|].
  rewrite !subst_context_snoc. constructor; [|exact IH].
  destruct d as [na [b|] ty]; cbn; [|exact tt].
  apply peta_subst; [apply peta_refl|exact Hs].
Qed.

Lemma peta_inst_case_context params params' puinst ctx :
  All2 peta params params' ->
  peta_ctx (inst_case_context params puinst ctx) (inst_case_context params' puinst ctx).
Proof. intros H. unfold inst_case_context. apply peta_subst_context. now apply All2_rev. Qed.

Lemma peta_ctx_mapi_vass (f g : nat -> def term -> term) m m' k :
  #|m| = #|m'| ->
  All2 peta_decl (mapi_rec (fun i d => vass (dname d) (f i d)) m k)
                 (mapi_rec (fun i d => vass (dname d) (g i d)) m' k).
Proof.
  induction m in m', k |- *; destruct m'; cbn; intros Hl; try discriminate.
  - constructor.
  - constructor; [exact tt|]. apply IHm. lia.
Qed.

Lemma peta_ctx_fix_context m m' : #|m| = #|m'| -> peta_ctx (fix_context m) (fix_context m').
Proof.
  intros Hl. unfold fix_context, mapi. apply All2_rev. now apply peta_ctx_mapi_vass.
Qed.

Lemma peta_extended_subst Γ Γ' n :
  peta_ctx Γ Γ' -> All2 peta (extended_subst Γ n) (extended_subst Γ' n).
Proof.
  intros H. induction H as [|d d' Γ Γ' Hd H IH] in n |- *; [constructor|].
  destruct d as [na [b|] ty], d' as [na' [b'|] ty']; cbn in Hd |- *.
  - constructor; [|apply IH].
    rewrite (peta_ctx_assumptions _ _ H) !extended_subst_length (All2_length H).
    apply peta_subst; [exact (peta_lift _ _ _ Hd _)|apply IH].
  - destruct Hd.
  - destruct Hd.
  - constructor; [apply peta_Rel|apply IH].
Qed.

Lemma peta_expand_lets Γ Γ' t t' :
  peta_ctx Γ Γ' -> peta t t' -> peta (expand_lets Γ t) (expand_lets Γ' t').
Proof.
  intros H Ht. unfold expand_lets, expand_lets_k.
  rewrite (peta_ctx_assumptions _ _ H) (All2_length H).
  apply peta_subst; [now apply peta_lift|now apply peta_extended_subst].
Qed.

Lemma peta_iota_red npar p p' args args' br br' :
  All2 peta args args' -> All2 peta (pparams p) (pparams p') ->
  puinst p = puinst p' -> bcontext br = bcontext br' -> peta (bbody br) (bbody br') ->
  peta (iota_red npar p args br) (iota_red npar p' args' br').
Proof.
  intros Ha Hp Hu Hc Hb. unfold iota_red.
  apply peta_subst; [|now apply All2_rev, All2_skipn].
  apply peta_expand_lets; [|exact Hb].
  unfold inst_case_branch_context. rewrite Hu Hc.
  now apply peta_inst_case_context.
Qed.

Lemma peta_commut_red_iota Σ Γ ci c uu args p brs br u :
  nth_error brs c = Some br ->
  #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
  peta (tCase ci p (mkApps (tConstruct ci.(ci_ind) c uu) args) brs) u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × peta (iota_red ci.(ci_npar) p args br) w'
        × upto_domain w w'.
Proof.
  intros Hnth Hlen Hp. depelim Hp.
  match goal with Hd : peta (mkApps (tConstruct _ _ _) _) _ |- _ =>
    apply peta_mkApps_inv in Hd as (f' & args' & -> & Hf & Ha) end.
  depelim Hf.
  match goal with Hb : All2 _ brs ?bs |- _ =>
    destruct (All2_nth_error_Some _ _ Hb Hnth) as (br' & Hnth' & (Hc & Hbb)) end.
  eexists _, _. repeat split.
  - apply r_step. eapply red_iota; [exact Hnth'|].
    rewrite <- (All2_length Ha), <- Hc. exact Hlen.
  - apply peta_iota_red; [exact Ha|eassumption|eassumption|exact Hc|exact Hbb].
  - reflexivity.
Qed.

(** ** Spine helpers *)
Lemma mkApps_Fix_eq mfix idx args t :
  mkApps (tFix mfix idx) args = t ->
  ((args = []) × (t = tFix mfix idx)) + (∑ f a, t = tApp f a).
Proof.
  induction args using rev_ind; cbn; intros H.
  - left. split; [reflexivity|now symmetry].
  - right. rewrite mkApps_app in H. cbn in H. subst t. eexists _, _. reflexivity.
Qed.

Lemma is_constructor_nil n : is_constructor n [] = false.
Proof. unfold is_constructor. now destruct n. Qed.

(** ** The kernel's scoping premise, and why it SURVIVES the induction

  [red1_strengthening] (staged below) needs [on_free_vars xpredT t]. That is NOT
  vacuous on the 9.2 AST: [on_free_vars]'s [tCase] branch
  (Syntax/PCUICOnFreeVars.v:82,:85) tests
  [test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams|] on
  [pcontext] and on every [bcontext], and that conjunct never mentions [p], so it
  demands those contexts be CLOSED however permissive [p] is. (The lemmas that would
  discharge it — [on_free_vars_true], [on_free_vars_xpredT], [test_context_k_true] —
  are commented out at :139-163.) Base's own [weakening_red1] carries it for the
  same reason.

  DO NOT TRY TO DROP THIS PREMISE. It is carried, not re-established at each step,
  and that is exactly why the induction goes through:
  - under binders it propagates UNCHANGED, because [shiftnP_xpredT] (:129) gives
    [shiftnP n xpredT =1 xpredT];
  - across the [lift0 1] of the η-redex it is INVARIANT ([ofvT_lift] below), because
    [lift] leaves [pcontext]/[bcontext] untouched ([map_branch_k] uses [id] on
    [bcontext]), so the p-independent conjunct is literally identical for [M] and
    [lift0 1 M], while every p-dependent conjunct is trivial at [xpredT].
  It costs the ROUTE nothing: the authoritative C3 already carries [is_open_term Γ t],
  and [shiftnP n xpred0 ≤ xpredT] pointwise, so [on_free_vars_impl] (:168) discharges
  it at assembly. Likewise [wf Σ] is already a C3 premise. *)

Notation ofvT := (on_free_vars xpredT).

Lemma ofvT_shiftnP n t : on_free_vars (shiftnP n xpredT) t = ofvT t.
Proof. apply on_free_vars_ext, shiftnP_xpredT. Qed.

(** Proved locally (purity): no base lemma gives this direction. [on_free_vars_lift]
    and friends all yield [t -> lift t], since [strengthenP k n xpredT <= xpredT] makes
    [on_free_vars_impl] run outward; the converse needs the window-emptiness of lifting,
    for which base has no [noccur_between]/[lift] bridge. *)
Lemma ofvT_lift n k t : ofvT (lift n k t) = ofvT t.
Proof.
  induction t in n, k |- * using term_forall_list_ind; cbn; auto.
  - rewrite forallb_map. apply All_forallb_eq_forallb with (1 := X). auto.
  - now rewrite IHt1 !ofvT_shiftnP IHt2.
  - now rewrite IHt1 !ofvT_shiftnP IHt2.
  - now rewrite IHt1 IHt2 !ofvT_shiftnP IHt3.
  - now rewrite IHt1 IHt2.
  - destruct X as (Hpar & _ & Hret).
    rewrite length_map.
    f_equal.
    { rewrite forallb_map. apply All_forallb_eq_forallb with (1 := Hpar). auto. }
    f_equal.
    { now rewrite !ofvT_shiftnP Hret. }
    f_equal.
    f_equal.
    { eauto. }
    rewrite forallb_map. apply All_forallb_eq_forallb with (1 := X0).
    intros br [_ Hb]. cbn. now rewrite !ofvT_shiftnP Hb.
  - rewrite forallb_map. apply All_forallb_eq_forallb with (1 := X).
    intros d [Ht Hb]. unfold test_def. cbn.
    now rewrite Ht !ofvT_shiftnP Hb.
  - rewrite forallb_map. apply All_forallb_eq_forallb with (1 := X).
    intros d [Ht Hb]. unfold test_def. cbn.
    now rewrite Ht !ofvT_shiftnP Hb.
  - destruct p as [? []]; cbn in X |- *; auto.
    destruct X as (Ht & Hd & Hv).
    rewrite Ht Hd forallb_map. f_equal. f_equal.
    apply All_forallb_eq_forallb with (1 := Hv). auto.
Qed.

(** * Kernel inversions *)

(** Clean [red1] inversion for [tLambda]: only [abs_red_l] and [abs_red_r] apply.
    [depelim] on [red1] leaves impossible [mkApps]-headed cases due to opacity;
    this inversion avoids that by matching the [tLambda] head directly. *)
Lemma red1_tLambda_inv {Σ Γ na A b v} :
  red1 Σ Γ (tLambda na A b) v ->
  (∑ A', v = tLambda na A' b × red1 Σ Γ A A') +
  (∑ b', v = tLambda na A b' × red1 Σ (Γ ,, vass na A) b b').
Proof.
  intro H. remember (tLambda na A b) as t eqn:Heq.
  destruct H; try discriminate Heq;
    try solve [exfalso; destruct args using rev_ind;
               [cbn in Heq; discriminate Heq|
                rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq]].
  - injection Heq as -> -> ->. left. eexists; split; [reflexivity|assumption].
  - injection Heq as -> -> ->. right. eexists; split; [reflexivity|assumption].
Qed.

(** [tRel 0] has no [red1] reduct under an assumption: [vass] has no body. *)
Lemma red1_tRel0_vass_absurd {Σ Γ na A v} :
  red1 Σ (Γ ,, vass na A) (tRel 0) v -> False.
Proof.
  intro H. remember (tRel 0) as t eqn:Heq.
  destruct H; try discriminate Heq;
    try solve [destruct args using rev_ind;
               [cbn in Heq; discriminate Heq|
                rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq]].
  injection Heq as ->.
  match goal with He : option_map _ _ = _ |- _ => cbn in He; discriminate He end.
Qed.

(** The red1 reducts of an η-redex BODY [tApp (lift0 1 M) (tRel 0)] under its binder.
    Three live cases; [app_red_r] is absurd ([red1_tRel0_vass_absurd]). *)
Lemma red1_eta_body_inv {Σ Γ na A M v} :
  red1 Σ (Γ ,, vass na A) (tApp (lift0 1 M) (tRel 0)) v ->
  (∑ N1, (v = tApp N1 (tRel 0)) × red1 Σ (Γ ,, vass na A) (lift0 1 M) N1)
  + (∑ nb B b, (lift0 1 M = tLambda nb B b) × (v = b {0 := tRel 0}))
  + (∑ mfix idx args narg fn,
       (mkApps (tFix mfix idx) args = tApp (lift0 1 M) (tRel 0))
       × (unfold_fix mfix idx = Some (narg, fn))
       × (is_constructor narg args = true) × (v = mkApps fn args)).
Proof.
  intro H. remember (tApp (lift0 1 M) (tRel 0)) as t eqn:Heq.
  destruct H; try discriminate Heq.
  - (* red_beta *)
    injection Heq as Hf Ha. subst a.
    left; right. eexists _, _, _. split; [symmetry; exact Hf|reflexivity].
  - (* red_fix *)
    right. eexists _, _, _, _, _. repeat split; eassumption.
  - (* app_red_l *)
    injection Heq as -> ->.
    left; left. eexists. split; [reflexivity|assumption].
  - (* app_red_r *)
    injection Heq as -> ->.
    exfalso. eapply red1_tRel0_vass_absurd. eassumption.
Qed.

Lemma lift_tLambda_inv n k M nb B b :
  lift n k M = tLambda nb B b ->
  ∑ B0 b0, (M = tLambda nb B0 b0) × (B = lift n k B0) × (b = lift n (S k) b0).
Proof.
  destruct M; cbn; intros H; try discriminate H.
  injection H as Hna HB Hb. subst.
  exists M1, M2. repeat split; reflexivity.
Qed.

(** [PCUICConversion]'s [subst_rel0_lift_id] is behind conversion; derive the instance
    we need from [PCUICSigmaCalculus] (which imports nothing we do not already). *)
Lemma subst_rel0_lift_id0 t : (lift 1 1 t) {0 := tRel 0} = t.
Proof. exact (eq_trans (subst_reli_lift_id 0 0 t (le_n 0)) (lift0_id t 0)). Qed.
(** ** Created-redex sub-case 1: [red_beta] created inside the η body.

  [t = eta_redex na A M] with [lift0 1 M = tLambda], i.e. [M] is itself a λ. The inner
  application β-reduces and [v = tLambda na A b0] where [b0] is [M]'s body — so [v] and
  [M] differ ONLY in the λ domain ([A] vs [M]'s domain). [peta] cannot absorb that
  (its λ congruence relates domains), which is exactly why C3's conclusion is modulo
  [upto_domain]: the mismatch is discharged by [utd_Lambda], which ignores domains and
  binder names. Both [peta] sub-cases close with ZERO β-steps on the η side. *)
Lemma peta_commut_eta_red_beta Σ Γ na A M M' nb B b :
  peta M M' ->
  lift0 1 M = tLambda nb B b ->
  ∑ w w', clos_refl (red1 Σ Γ) M' w
        × peta (tLambda na A (b {0 := tRel 0})) w' × upto_domain w w'.
Proof.
  intros Hp Hl.
  destruct (lift_tLambda_inv _ _ _ _ _ _ Hl) as (B0 & b0 & -> & _ & ->).
  rewrite (subst_rel0_lift_id0 b0).
  depelim Hp.
  - (* peta_eta : b0 is itself an η-redex, M' is its contraction *)
    eexists _, _. repeat split.
    + apply r_refl.
    + apply peta_eta. eassumption.
    + reflexivity.
  - (* peta_Lambda : M' = tLambda nb B0' b0' *)
    eexists _, (tLambda na A _). repeat split.
    + apply r_refl.
    + apply peta_Lambda; [apply peta_refl|eassumption].
    + apply utd_Lambda. reflexivity.
Qed.

(** ** Created-redex sub-case 2: [red_fix] created inside the η body — helpers.

  NB base HAS [decompose_app_lift] and [lift_is_constructor], but both are inside the
  commented-out block at Conversion/PCUICWeakeningConv.v:175-208 (same nested-comment
  trap as [on_free_vars_true] at Syntax/PCUICOnFreeVars.v:139-163). So they are proved
  locally here — which also keeps the closure clean, since PCUICWeakeningConv is
  Conversion-level. *)

Lemma decompose_app_rec_lift n k t l :
  decompose_app_rec (lift n k t) (map (lift n k) l) =
  (lift n k (decompose_app_rec t l).1, map (lift n k) (decompose_app_rec t l).2).
Proof.
  induction t in l |- *; cbn; try reflexivity.
  now rewrite -(IHt1 (t2 :: l)).
Qed.

Lemma isConstruct_app_lift n k t : isConstruct_app (lift n k t) = isConstruct_app t.
Proof.
  unfold isConstruct_app, decompose_app.
  replace (@nil term) with (map (lift n k) (@nil term)) at 1 by reflexivity.
  rewrite decompose_app_rec_lift. cbn.
  now destruct (decompose_app_rec t []).1.
Qed.

Lemma is_constructor_lift n k narg args :
  is_constructor narg (map (lift n k) args) = is_constructor narg args.
Proof.
  unfold is_constructor. rewrite nth_error_map.
  destruct (nth_error args narg); cbn; [apply isConstruct_app_lift|reflexivity].
Qed.

(** The guard's recursive argument can NEVER be the trailing [tRel 0] of an η-body:
    [isConstruct_app (tRel 0) = false]. So an η-created fix always has its recursive
    argument inside the REAL spine — which is why this case is benign. *)
Lemma is_constructor_app_tRel0 narg args :
  is_constructor narg (args ++ [tRel 0]) = true -> narg < #|args|.
Proof.
  unfold is_constructor. intro H.
  destruct (Nat.ltb_spec narg #|args|) as [Hlt|Hge]; [exact Hlt|].
  exfalso. rewrite nth_error_app_ge in H; [exact Hge|].
  destruct (narg - #|args|) as [|m] eqn:Hd; cbn in H; [discriminate H|].
  destruct m; cbn in H; discriminate H.
Qed.

Lemma fix_subst_lift n k mfix :
  fix_subst (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix)
  = map (lift n k) (fix_subst mfix).
Proof.
  unfold fix_subst. rewrite !length_map.
  generalize #|mfix| at 2 3. intro m.
  induction m; cbn; auto. f_equal. apply IHm.
Qed.

Lemma lift_unfold_fix n k mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = Some (narg, lift n k fn).
Proof.
  unfold unfold_fix. rewrite nth_error_map.
  destruct (nth_error mfix idx) as [d|] eqn:Hd; cbn; [|discriminate].
  intro H. injection H as <- <-.
  rewrite fix_subst_lift.
  f_equal. f_equal. rewrite distr_lift_subst. f_equal.
  now rewrite fix_subst_length.
Qed.

Lemma lift_mkApps_tFix_inv n k M mfix idx args :
  lift n k M = mkApps (tFix mfix idx) args ->
  ∑ mfix0 args0, (M = mkApps (tFix mfix0 idx) args0)
    × (mfix = map (map_def (lift n k) (lift n (#|mfix0| + k))) mfix0)
    × (args = map (lift n k) args0).
Proof.
  revert M. induction args using rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate H.
    injection H as <- <-. exists mfix0, []. repeat split.
  - rewrite mkApps_app in H. cbn in H.
    destruct M; cbn in H; try discriminate H.
    injection H as H1 H2.
    destruct (IHargs _ H1) as (mfix0 & args0 & -> & -> & ->).
    exists mfix0, (args0 ++ [M2]). repeat split.
    + now rewrite mkApps_app.
    + rewrite map_app. cbn. now rewrite H2.
Qed.

Lemma mkApps_tApp_inv f args g a :
  ~~ isApp f -> mkApps f args = tApp g a ->
  ∑ args', (args = args' ++ [a]) × (mkApps f args' = g).
Proof.
  intros Hf H. destruct args using rev_ind.
  - cbn in H. subst f. cbn in Hf. discriminate.
  - rewrite mkApps_app in H. cbn in H. injection H as <- <-.
    exists args. split; reflexivity.
Qed.

Lemma lift_unfold_fix_inv n k mfix0 idx narg fn :
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix0| + k))) mfix0) idx = Some (narg, fn) ->
  ∑ fn0, (unfold_fix mfix0 idx = Some (narg, fn0)) × (fn = lift n k fn0).
Proof.
  intro H. destruct (unfold_fix mfix0 idx) as [[narg0 fn0]|] eqn:E.
  - rewrite (lift_unfold_fix n k _ _ _ _ E) in H. injection H as <- <-.
    exists fn0. split; reflexivity.
  - exfalso. unfold unfold_fix in *. rewrite nth_error_map in H.
    destruct (nth_error mfix0 idx); cbn in *; discriminate.
Qed.

Lemma is_constructor_app_lt narg args l :
  narg < #|args| -> is_constructor narg (args ++ l) = is_constructor narg args.
Proof. intro H. unfold is_constructor. now rewrite nth_error_app_lt. Qed.

(** ** Created-redex sub-case 2: [red_fix] created inside the η body.

  η turns the λ-bound spine into [args' ++ [tRel 0]] and so can UNLOCK a fixpoint.
  This is where η-POSTPONEMENT died. For the COMMUTATION it is benign, and
  [is_constructor_app_tRel0] is why: the guard's recursive argument can never be the
  trailing [tRel 0], so it lies in the REAL spine, transfers down through the lift
  ([is_constructor_lift]) to [M]'s own spine, and the fix fires on the η side in ONE
  step. The β side stays an η-redex ([eta_redex na A (mkApps fn0 args0)]), so [peta_eta]
  closes it and [upto_domain] is REFLEXIVE here — unlike [red_beta]-created. *)
Lemma peta_commut_eta_red_fix Σ Γ na A M M' mfix idx args narg fn :
  peta M M' ->
  mkApps (tFix mfix idx) args = tApp (lift0 1 M) (tRel 0) ->
  unfold_fix mfix idx = Some (narg, fn) ->
  is_constructor narg args = true ->
  ∑ w w', clos_refl (red1 Σ Γ) M' w
        × peta (tLambda na A (mkApps fn args)) w' × upto_domain w w'.
Proof.
  intros Hp Heq Hunf Hic.
  destruct (mkApps_tApp_inv (tFix mfix idx) args (lift0 1 M) (tRel 0) eq_refl Heq)
    as (args' & -> & Hsp).
  pose proof (is_constructor_app_tRel0 _ _ Hic) as Hlt.
  rewrite (is_constructor_app_lt _ _ _ Hlt) in Hic.
  destruct (lift_mkApps_tFix_inv _ _ _ _ _ _ (eq_sym Hsp))
    as (mfix0 & args0 & -> & -> & ->).
  destruct (lift_unfold_fix_inv _ _ _ _ _ _ Hunf) as (fn0 & Hunf0 & ->).
  rewrite is_constructor_lift in Hic.
  apply peta_mkApps_inv in Hp as (f' & args0' & -> & Hf & Ha).
  depelim Hf.
  match goal with Hm : All2 _ mfix0 ?m |- _ =>
    destruct (peta_unfold_fix _ m _ _ _ Hm Hunf0) as (fn0' & Hunf0' & Hfn) end.
  exists (mkApps fn0' args0'), (mkApps fn0' args0'). repeat split.
  - apply r_step. eapply red_fix; [exact Hunf0'|].
    eapply peta_is_constructor; eassumption.
  - rewrite mkApps_app. cbn. rewrite <- lift_mkApps.
    apply peta_eta. apply peta_mkApps; assumption.
  - reflexivity.
Qed.

(** * Congruence infrastructure: one clean [red1] inversion per head shape.
    Pattern ([red1_tLambda_inv]): [remember] the head, [destruct] the derivation,
    [discriminate] head clashes. [depelim] would leave [mkApps]-headed impossible cases. *)

Lemma red1_tApp_inv {Σ Γ f a v} :
  red1 Σ Γ (tApp f a) v ->
  (∑ na A b, (f = tLambda na A b) × (v = b {0 := a}))
  + (∑ mfix idx args narg fn,
       (mkApps (tFix mfix idx) args = tApp f a) × (unfold_fix mfix idx = Some (narg, fn))
       × (is_constructor narg args = true) × (v = mkApps fn args))
  + (∑ f', (v = tApp f' a) × red1 Σ Γ f f')
  + (∑ a', (v = tApp f a') × red1 Σ Γ a a').
Proof.
  intro H. remember (tApp f a) as t eqn:Heq.
  destruct H; try discriminate Heq.
  - injection Heq as Hf Ha. subst. left; left; left.
    eexists _, _, _. split; reflexivity.
  - left; left; right. eexists _, _, _, _, _. repeat split; eassumption.
  - injection Heq as Hf Ha. subst. left; right.
    eexists. split; [reflexivity|assumption].
  - injection Heq as Hf Ha. subst. right.
    eexists. split; [reflexivity|assumption].
Qed.

Lemma red1_tProj_inv {Σ Γ pr c v} :
  red1 Σ Γ (tProj pr c) v ->
  (∑ mfix idx args narg fn, (c = mkApps (tCoFix mfix idx) args)
     × (unfold_cofix mfix idx = Some (narg, fn)) × (v = tProj pr (mkApps fn args)))
  + (∑ args uu arg, (c = mkApps (tConstruct pr.(proj_ind) 0 uu) args)
     × (nth_error args (pr.(proj_npars) + pr.(proj_arg)) = Some arg) × (v = arg))
  + (∑ c', (v = tProj pr c') × red1 Σ Γ c c').
Proof.
  intro H. remember (tProj pr c) as t eqn:Heq.
  destruct H; try discriminate Heq;
    try solve [exfalso; destruct args using rev_ind;
               [cbn in Heq; discriminate Heq|
                rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq]].
  - injection Heq as Hp Hc. subst. left; left.
    eexists _, _, _, _, _. repeat split; eassumption.
  - injection Heq as Hp Hc. subst. left; right.
    eexists _, _, _. repeat split; eassumption.
  - injection Heq as Hp Hc. subst. right.
    eexists. split; [reflexivity|assumption].
Qed.

(** Leaves with no [red1] reduct. *)
Lemma red1_tVar_absurd {Σ Γ i v} : red1 Σ Γ (tVar i) v -> False.
Proof.
  intro H. remember (tVar i) as t eqn:Heq. destruct H; try discriminate Heq.
  destruct args using rev_ind;
    [cbn in Heq; discriminate Heq|rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq].
Qed.

Lemma red1_tSort_absurd {Σ Γ s v} : red1 Σ Γ (tSort s) v -> False.
Proof.
  intro H. remember (tSort s) as t eqn:Heq. destruct H; try discriminate Heq.
  destruct args using rev_ind;
    [cbn in Heq; discriminate Heq|rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq].
Qed.

Lemma red1_tInd_absurd {Σ Γ ind uu v} : red1 Σ Γ (tInd ind uu) v -> False.
Proof.
  intro H. remember (tInd ind uu) as t eqn:Heq. destruct H; try discriminate Heq.
  destruct args using rev_ind;
    [cbn in Heq; discriminate Heq|rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq].
Qed.

Lemma red1_tConstruct_absurd {Σ Γ ind k uu v} : red1 Σ Γ (tConstruct ind k uu) v -> False.
Proof.
  intro H. remember (tConstruct ind k uu) as t eqn:Heq. destruct H; try discriminate Heq.
  destruct args using rev_ind;
    [cbn in Heq; discriminate Heq|rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq].
Qed.

Ltac red1_dismiss_mkApps Heq :=
  exfalso; match type of Heq with
  | mkApps _ ?l = _ =>
      destruct l using rev_ind;
      [cbn in Heq; discriminate Heq|rewrite mkApps_app in Heq; cbn in Heq; discriminate Heq]
  end.

Lemma red1_tProd_inv {Σ Γ na A B v} :
  red1 Σ Γ (tProd na A B) v ->
  (∑ A', v = tProd na A' B × red1 Σ Γ A A') +
  (∑ B', v = tProd na A B' × red1 Σ (Γ ,, vass na A) B B').
Proof.
  intro H. remember (tProd na A B) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  - injection Heq as -> -> ->. left. eexists; split; [reflexivity|assumption].
  - injection Heq as -> -> ->. right. eexists; split; [reflexivity|assumption].
Qed.

Lemma red1_tLetIn_inv {Σ Γ na b ty B v} :
  red1 Σ Γ (tLetIn na b ty B) v ->
  (v = B {0 := b})
  + (∑ b', v = tLetIn na b' ty B × red1 Σ Γ b b')
  + (∑ ty', v = tLetIn na b ty' B × red1 Σ Γ ty ty')
  + (∑ B', v = tLetIn na b ty B' × red1 Σ (Γ ,, vdef na b ty) B B').
Proof.
  intro H. remember (tLetIn na b ty B) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  - injection Heq as -> -> -> ->. left; left; left. reflexivity.
  - injection Heq as -> -> -> ->. left; left; right. eexists; split; [reflexivity|assumption].
  - injection Heq as -> -> -> ->. left; right. eexists; split; [reflexivity|assumption].
  - injection Heq as -> -> -> ->. right. eexists; split; [reflexivity|assumption].
Qed.

Lemma red1_tRel_inv {Σ Γ n v} :
  red1 Σ Γ (tRel n) v ->
  ∑ body, (option_map decl_body (nth_error Γ n) = Some (Some body)) × (v = lift0 (S n) body).
Proof.
  intro H. remember (tRel n) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  injection Heq as ->. eexists; split; [eassumption|reflexivity].
Qed.

Lemma red1_tConst_inv {Σ Γ c uu v} :
  red1 Σ Γ (tConst c uu) v ->
  ∑ decl body, declared_constant Σ c decl × (cst_body decl = Some body)
             × (v = subst_instance uu body).
Proof.
  intro H. remember (tConst c uu) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  injection Heq as -> ->. eexists _, _. repeat split; eassumption.
Qed.

(** * The commutation kernel, one lemma per [peta] constructor.

  [commutes Σ t u] is the induction motive. The η side lives in a context [Δ] related
  to the β side's [Γ] by [peta_ctx] (bodies only), because case and fixpoint contexts
  are computed from terms that [peta] may change. Each constructor's case is its own
  lemma taking the subterms' motives as premises, so every case is committed green on
  its own; the final induction only dispatches to them. *)

Definition commutes Σ t u : Type :=
  forall Γ Δ v, peta_ctx Γ Δ -> on_ctx_free_vars xpredT Γ -> ofvT t -> red1 Σ Γ t v ->
  ∑ w w', clos_refl (red1 Σ Δ) u w × peta v w' × upto_domain w w'.

Lemma clos_refl_map {A B} (R : A -> A -> Type) (S : B -> B -> Type) (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) ->
  forall x y, clos_refl R x y -> clos_refl S (f x) (f y).
Proof. intros Hf x y []; [apply r_step; now apply Hf|apply r_refl]. Qed.

Lemma octx_shiftnP n Γ :
  on_ctx_free_vars (shiftnP n xpredT) Γ = on_ctx_free_vars xpredT Γ.
Proof. exact (on_ctx_free_vars_proper _ _ (shiftnP_xpredT n) Γ Γ eq_refl). Qed.

Lemma octx_vass Γ na A :
  on_ctx_free_vars xpredT Γ -> ofvT A -> on_ctx_free_vars xpredT (Γ ,, vass na A).
Proof.
  intros HΓ HA. rewrite -(octx_shiftnP 1). now apply on_ctx_free_vars_snoc_ass.
Qed.

Lemma octx_vdef Γ na b ty :
  on_ctx_free_vars xpredT Γ -> ofvT ty -> ofvT b ->
  on_ctx_free_vars xpredT (Γ ,, vdef na b ty).
Proof.
  intros HΓ Hty Hb. rewrite -(octx_shiftnP 1). now apply on_ctx_free_vars_snoc_def.
Qed.

(** Leaves: no [red1] reduct, so nothing to commute. *)
Lemma commut_Var Σ i : commutes Σ (tVar i) (tVar i).
Proof. intros Γ Δ v _ _ _ Hr. destruct (red1_tVar_absurd Hr). Qed.
Lemma commut_Sort Σ s : commutes Σ (tSort s) (tSort s).
Proof. intros Γ Δ v _ _ _ Hr. destruct (red1_tSort_absurd Hr). Qed.
Lemma commut_Ind Σ ind uu : commutes Σ (tInd ind uu) (tInd ind uu).
Proof. intros Γ Δ v _ _ _ Hr. destruct (red1_tInd_absurd Hr). Qed.
Lemma commut_Construct Σ ind k uu : commutes Σ (tConstruct ind k uu) (tConstruct ind k uu).
Proof. intros Γ Δ v _ _ _ Hr. destruct (red1_tConstruct_absurd Hr). Qed.

(** [tRel]: the only place [red1] reads its context. The η side reads the
    [peta]-related body from [Δ]; [peta_lift] relates the two reducts. *)
Lemma commut_Rel Σ n : commutes Σ (tRel n) (tRel n).
Proof.
  intros Γ Δ v HΔ _ _ Hr.
  destruct (red1_tRel_inv Hr) as (body & Hb & ->).
  destruct (nth_error Γ n) as [d|] eqn:Hd; cbn in Hb; [|discriminate].
  destruct (All2_nth_error_Some _ _ HΔ Hd) as (d' & Hd' & Hdd).
  injection Hb as Hb. unfold peta_decl in Hdd. rewrite Hb in Hdd.
  destruct (decl_body d') as [body'|] eqn:Hb'; [|destruct Hdd].
  exists (lift0 (S n) body'), (lift0 (S n) body'). repeat split.
  - apply r_step. apply red_rel. now rewrite Hd' /= Hb'.
  - now apply peta_lift.
  - reflexivity.
Qed.

Lemma commut_Const Σ c uu : commutes Σ (tConst c uu) (tConst c uu).
Proof.
  intros Γ Δ v _ _ _ Hr.
  destruct (red1_tConst_inv Hr) as (decl & body & Hdecl & Hbody & ->).
  exact (peta_commut_red_delta Σ Δ c decl body uu _ Hdecl Hbody (peta_refl _)).
Qed.

Lemma commut_Lambda Σ na A A' M M' :
  peta A A' -> commutes Σ A A' -> peta M M' -> commutes Σ M M' ->
  commutes Σ (tLambda na A M) (tLambda na A' M').
Proof.
  intros pA IA pM IM Γ Δ v HΔ HΓ Ht Hr.
  cbn in Ht. move/andP: Ht => [HA HM]. rewrite ofvT_shiftnP in HM.
  destruct (red1_tLambda_inv Hr) as [(A1 & -> & HrA)|(M1 & -> & HrM)].
  - destruct (IA Γ Δ A1 HΔ HΓ HA HrA) as (w & w' & Hw & Hw' & Hu).
    exists (tLambda na w M'), (tLambda na w' M'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tLambda na x M')); [|exact Hw].
      intros x y H. now apply abs_red_l.
    + now apply peta_Lambda.
    + apply utd_Lambda. reflexivity.
  - destruct (IM (Γ ,, vass na A) (Δ ,, vass na A') M1 (peta_ctx_vass _ _ _ _ _ _ HΔ)
                 (octx_vass _ _ _ HΓ HA) HM HrM) as (w & w' & Hw & Hw' & Hu).
    exists (tLambda na A' w), (tLambda na A' w'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tLambda na A' x)); [|exact Hw].
      intros x y H. now apply abs_red_r.
    + now apply peta_Lambda.
    + now apply utd_Lambda.
Qed.

Lemma commut_Prod Σ na A A' B B' :
  peta A A' -> commutes Σ A A' -> peta B B' -> commutes Σ B B' ->
  commutes Σ (tProd na A B) (tProd na A' B').
Proof.
  intros pA IA pB IB Γ Δ v HΔ HΓ Ht Hr.
  cbn in Ht. move/andP: Ht => [HA HB]. rewrite ofvT_shiftnP in HB.
  destruct (red1_tProd_inv Hr) as [(A1 & -> & HrA)|(B1 & -> & HrB)].
  - destruct (IA Γ Δ A1 HΔ HΓ HA HrA) as (w & w' & Hw & Hw' & Hu).
    exists (tProd na w B'), (tProd na w' B'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tProd na x B')); [|exact Hw].
      intros x y H. now apply prod_red_l.
    + now apply peta_Prod.
    + apply utd_Prod; [exact Hu|reflexivity].
  - destruct (IB (Γ ,, vass na A) (Δ ,, vass na A') B1 (peta_ctx_vass _ _ _ _ _ _ HΔ)
                 (octx_vass _ _ _ HΓ HA) HB HrB) as (w & w' & Hw & Hw' & Hu).
    exists (tProd na A' w), (tProd na A' w'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tProd na A' x)); [|exact Hw].
      intros x y H. now apply prod_red_r.
    + now apply peta_Prod.
    + apply utd_Prod; [reflexivity|exact Hu].
Qed.

Lemma commut_LetIn Σ na b b' ty ty' B B' :
  peta b b' -> commutes Σ b b' -> peta ty ty' -> commutes Σ ty ty' ->
  peta B B' -> commutes Σ B B' ->
  commutes Σ (tLetIn na b ty B) (tLetIn na b' ty' B').
Proof.
  intros pb Ib pty Ity pB IB Γ Δ v HΔ HΓ Ht Hr.
  cbn in Ht. move/and3P: Ht => [Hb Hty HB]. rewrite ofvT_shiftnP in HB.
  destruct (red1_tLetIn_inv Hr) as [[[->|(b1 & -> & Hrb)]|(ty1 & -> & Hrty)]|(B1 & -> & HrB)].
  - exact (peta_commut_red_zeta Σ Δ na b ty B _ (peta_LetIn _ _ _ _ _ _ _ pb pty pB)).
  - destruct (Ib Γ Δ b1 HΔ HΓ Hb Hrb) as (w & w' & Hw & Hw' & Hu).
    exists (tLetIn na w ty' B'), (tLetIn na w' ty' B'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tLetIn na x ty' B')); [|exact Hw].
      intros x y H. now apply letin_red_def.
    + now apply peta_LetIn.
    + apply utd_LetIn; [exact Hu|reflexivity|reflexivity].
  - destruct (Ity Γ Δ ty1 HΔ HΓ Hty Hrty) as (w & w' & Hw & Hw' & Hu).
    exists (tLetIn na b' w B'), (tLetIn na b' w' B'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tLetIn na b' x B')); [|exact Hw].
      intros x y H. now apply letin_red_ty.
    + now apply peta_LetIn.
    + apply utd_LetIn; [reflexivity|exact Hu|reflexivity].
  - destruct (IB (Γ ,, vdef na b ty) (Δ ,, vdef na b' ty') B1
                 (peta_ctx_vdef _ _ _ _ _ _ _ _ HΔ pb)
                 (octx_vdef _ _ _ _ HΓ Hty Hb) HB HrB) as (w & w' & Hw & Hw' & Hu).
    exists (tLetIn na b' ty' w), (tLetIn na b' ty' w'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tLetIn na b' ty' x)); [|exact Hw].
      intros x y H. now apply letin_red_body.
    + now apply peta_LetIn.
    + apply utd_LetIn; [reflexivity|reflexivity|exact Hu].
Qed.

Lemma commut_App Σ f f' a a' :
  peta f f' -> commutes Σ f f' -> peta a a' -> commutes Σ a a' ->
  commutes Σ (tApp f a) (tApp f' a').
Proof.
  intros pf If pa Ia Γ Δ v HΔ HΓ Ht Hr.
  cbn in Ht. move/andP: Ht => [Hf Ha].
  destruct (red1_tApp_inv Hr)
    as [[[(na & A & b & -> & ->)|(mfix & idx & args & narg & fn & Heq & Hunf & Hic & ->)]
        |(f1 & -> & Hrf)]|(a1 & -> & Hra)].
  - exact (peta_commut_red_beta Σ Δ na A b a _ (peta_App _ _ _ _ pf pa)).
  - apply (peta_commut_red_fix Σ Δ mfix idx args narg fn _ Hunf Hic).
    rewrite Heq. now apply peta_App.
  - destruct (If Γ Δ f1 HΔ HΓ Hf Hrf) as (w & w' & Hw & Hw' & Hu).
    exists (tApp w a'), (tApp w' a'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tApp x a')); [|exact Hw].
      intros x y H. now apply app_red_l.
    + now apply peta_App.
    + apply utd_App; [exact Hu|reflexivity].
  - destruct (Ia Γ Δ a1 HΔ HΓ Ha Hra) as (w & w' & Hw & Hw' & Hu).
    exists (tApp f' w), (tApp f' w'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tApp f' x)); [|exact Hw].
      intros x y H. now apply app_red_r.
    + now apply peta_App.
    + apply utd_App; [reflexivity|exact Hu].
Qed.

Lemma commut_Proj Σ pr c c' :
  peta c c' -> commutes Σ c c' -> commutes Σ (tProj pr c) (tProj pr c').
Proof.
  intros pc Ic Γ Δ v HΔ HΓ Ht Hr. cbn in Ht.
  destruct (red1_tProj_inv Hr)
    as [[(mfix & idx & args & narg & fn & -> & Hunf & ->)|(args & uu & arg & -> & Hnth & ->)]
       |(c1 & -> & Hrc)].
  - exact (peta_commut_red_cofix_proj Σ Δ pr mfix idx args narg fn _ Hunf (peta_Proj _ _ _ pc)).
  - exact (peta_commut_red_proj Σ Δ pr args uu arg _ Hnth (peta_Proj _ _ _ pc)).
  - destruct (Ic Γ Δ c1 HΔ HΓ Ht Hrc) as (w & w' & Hw & Hw' & Hu).
    exists (tProj pr w), (tProj pr w'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tProj pr x)); [|exact Hw].
      intros x y H. now apply proj_red.
    + now apply peta_Proj.
    + now apply utd_Proj.
Qed.

(** The η constructor: the only case that consumes the staged [red1_strengthening],
    and hence the only consumer of the two scoping premises and of [wf Σ]. *)
Lemma ofvT_eta_redex na A M :
  ofvT (tLambda na A (tApp (lift0 1 M) (tRel 0))) -> ofvT A × ofvT M.
Proof.
  cbn. rewrite !ofvT_shiftnP ofvT_lift. move/andP => [HA /andP [HM _]]. now split.
Qed.

Section Kernel.
Context {cf : checker_flags}.
(** Staged VERBATIM from EtaL2's [PCUICEtaStrengthening.v:209] (frac/eta-c3-c @
    6d04f604). NOT Required: Main's ruling keeps this file's closure empty; the
    discharge is an assembly-time decision of the lane lead. *)
Context (red1_strengthening : forall {Σ : global_env} {wfΣ : wf Σ} Γ d t u,
  on_ctx_free_vars xpredT Γ ->
  on_free_vars xpredT t ->
  red1 Σ (Γ ,, d) (lift0 1 t) u -> ∑ u', (u = lift0 1 u') × red1 Σ Γ t u').

Lemma commut_eta (Σ : global_env) (wfΣ : wf Σ) na A M M' :
  peta M M' -> commutes Σ M M' ->
  commutes Σ (tLambda na A (tApp (lift0 1 M) (tRel 0))) M'.
Proof.
  intros pM IM Γ Δ v HΔ HΓ Ht Hr.
  destruct (ofvT_eta_redex _ _ _ Ht) as [HA HM].
  destruct (red1_tLambda_inv Hr) as [(A1 & -> & _)|(b1 & -> & Hb)].
  - (* abs_red_l: still an η-redex; close with zero steps *)
    exists M', M'. repeat split; [apply r_refl|now apply peta_eta|reflexivity].
  - destruct (red1_eta_body_inv Hb)
      as [[(N1 & -> & HN)|(nb & B & b & Hl & ->)]
         |(mfix & idx & args & narg & fn & Heq & Hunf & Hic & ->)].
    + (* app_red_l: the clean case, through strengthening and the IH on M *)
      destruct (@red1_strengthening Σ wfΣ Γ (vass na A) M N1 HΓ HM HN) as (M'' & -> & HrM).
      destruct (IM Γ Δ M'' HΔ HΓ HM HrM) as (w & w' & Hw & Hw' & Hu).
      exists w, w'. repeat split; [exact Hw|now apply peta_eta|exact Hu].
    + exact (peta_commut_eta_red_beta Σ Δ na A M M' nb B b pM Hl).
    + exact (peta_commut_eta_red_fix Σ Δ na A M M' mfix idx args narg fn pM Heq Hunf Hic).
Qed.

End Kernel.

(** ** List congruences: one generic [OnOne2] commutation, instantiated per list.
    The reduced position commutes by its own motive; every other position keeps its
    [peta] step, and [upto_domain] is reflexive there. *)
Lemma OnOne2_commut {A} (R1 R2 Pe U : A -> A -> Type) (Q : A -> Type) l l' l1 :
  (forall x, U x x) ->
  All2 (fun x y => Pe x y × (Q x -> forall z, R1 x z ->
          ∑ w w', clos_refl R2 y w × Pe z w' × U w w')) l l' ->
  All Q l -> OnOne2 R1 l l1 ->
  ∑ lw lw', clos_refl (OnOne2 R2) l' lw × All2 Pe l1 lw' × All2 U lw lw'.
Proof.
  intros HU Ha HQ Ho.
  induction Ho as [hd hd' tl Hr|hd tl tl1 Ho IHo] in l', Ha, HQ |- *.
  - depelim Ha. depelim HQ.
    match goal with H : Pe hd ?y × _ |- _ => destruct H as [Pxy IH] end.
    match goal with Hq : Q hd |- _ => destruct (IH Hq hd' Hr) as (w & w' & Hw & Hw' & Hu) end.
    match goal with Ht : All2 _ tl ?tl' |- _ =>
      exists (w :: tl'), (w' :: tl'); repeat split end.
    + destruct Hw; [apply r_step; now constructor|apply r_refl].
    + constructor; [exact Hw'|]. eapply All2_impl; [eassumption|]. now intros ? ? [? _].
    + constructor; [exact Hu|]. now apply All2_same.
  - depelim Ha. depelim HQ.
    match goal with H : Pe hd ?y × _ |- _ => destruct H as [Pxy _] end.
    match goal with Ht : All2 _ tl ?tl' |- _ =>
      destruct (IHo tl' Ht HQ) as (lw & lw' & Hl & Hl' & Hu) end.
    exists (y :: lw), (y :: lw'). repeat split.
    + destruct Hl; [apply r_step; now apply OnOne2_tl|apply r_refl].
    + now constructor.
    + constructor; [apply HU|exact Hu].
Qed.

Lemma red1_tEvar_inv {Σ Γ ev l v} :
  red1 Σ Γ (tEvar ev l) v -> ∑ l1, (v = tEvar ev l1) × OnOne2 (red1 Σ Γ) l l1.
Proof.
  intro H. remember (tEvar ev l) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  injection Heq as -> ->. eexists; split; [reflexivity|assumption].
Qed.

Lemma red1_tFix_inv {Σ Γ mfix idx v} :
  red1 Σ Γ (tFix mfix idx) v ->
  (∑ m1, (v = tFix m1 idx)
     × OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix m1)
  + (∑ m1, (v = tFix m1 idx)
     × OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody
                (fun x => (dname x, dtype x, rarg x))) mfix m1).
Proof.
  intro H. remember (tFix mfix idx) as t eqn:Heq.
  destruct H; try discriminate Heq.
  - (* red_fix with an empty spine is blocked: [is_constructor _ []] is false *)
    exfalso. destruct args using rev_ind.
    + match goal with Hc : is_constructor _ [] = true |- _ =>
        rewrite is_constructor_nil in Hc; discriminate Hc end.
    + rewrite mkApps_app in Heq. cbn in Heq. discriminate Heq.
  - injection Heq as -> ->. left. eexists; split; [reflexivity|assumption].
  - injection Heq as -> ->. right. eexists; split; [reflexivity|assumption].
Qed.

Lemma red1_tCoFix_inv {Σ Γ mfix idx v} :
  red1 Σ Γ (tCoFix mfix idx) v ->
  (∑ m1, (v = tCoFix m1 idx)
     × OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix m1)
  + (∑ m1, (v = tCoFix m1 idx)
     × OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody
                (fun x => (dname x, dtype x, rarg x))) mfix m1).
Proof.
  intro H. remember (tCoFix mfix idx) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  - injection Heq as -> ->. left. eexists; split; [reflexivity|assumption].
  - injection Heq as -> ->. right. eexists; split; [reflexivity|assumption].
Qed.

Lemma commut_Evar Σ ev l l' :
  All2 (fun x y => peta x y × commutes Σ x y) l l' ->
  commutes Σ (tEvar ev l) (tEvar ev l').
Proof.
  intros Hl Γ Δ v HΔ HΓ Ht Hr. cbn in Ht.
  destruct (red1_tEvar_inv Hr) as (l1 & -> & Ho).
  destruct (OnOne2_commut (red1 Σ Γ) (red1 Σ Δ) peta upto_domain (fun x => is_true (ofvT x))
              l l' l1 (fun x => upto_domain_refl x)) as (lw & lw' & Hw & Hw' & Hu).
  - eapply All2_impl; [exact Hl|]. intros x y [pxy cxy]. split; [exact pxy|].
    intros Hq z Hz. exact (cxy Γ Δ z HΔ HΓ Hq Hz).
  - now apply forallb_All.
  - exact Ho.
  - exists (tEvar ev lw), (tEvar ev lw'). repeat split.
    + eapply (clos_refl_map _ _ (tEvar ev)); [|exact Hw]. intros x y H. now apply evar_red.
    + now apply peta_Evar.
    + now apply utd_Evar.
Qed.

Notation upto_def :=
  (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody)
              × x.(rarg) = y.(rarg)).

Notation commut_mfix Σ mfix mfix' :=
  (All2 (fun d d' => (peta d.(dtype) d'.(dtype) × commutes Σ d.(dtype) d'.(dtype))
                     × (peta d.(dbody) d'.(dbody) × commutes Σ d.(dbody) d'.(dbody))
                     × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix').

Lemma upto_def_refl d : upto_def d d.
Proof. repeat split; reflexivity. Qed.

(** The [dtype] step of a (co)fixpoint, in the β context [Γ], commuted. *)
Lemma commut_mfix_ty Σ Γ Δ mfix mfix' m1 :
  peta_ctx Γ Δ -> on_ctx_free_vars xpredT Γ ->
  commut_mfix Σ mfix mfix' ->
  forallb (test_def ofvT (on_free_vars (shiftnP #|mfix| xpredT))) mfix ->
  OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) mfix m1 ->
  ∑ lw lw', clos_refl (OnOne2 (on_Trel_eq (red1 Σ Δ) dtype
                                 (fun x => (dname x, dbody x, rarg x)))) mfix' lw
          × All2 peta_def m1 lw' × All2 upto_def lw lw'.
Proof.
  intros HΔ HΓ Hm Ht Ho.
  eapply (OnOne2_commut _ _ peta_def upto_def (fun d => is_true (ofvT (dtype d))));
    [exact upto_def_refl| |  |exact Ho].
  - eapply All2_impl; [exact Hm|].
    intros x [yn yt yb yr] [[pt ct] [[pb cb] [hn hr]]]. cbn in *.
    split; [repeat split; assumption|].
    intros Hq z [Hz Hk]. injection Hk as kn kb kr.
    destruct (ct Γ Δ (dtype z) HΔ HΓ Hq Hz) as (w & w' & Hw & Hw' & Hu).
    exists (mkdef _ yn w yb yr), (mkdef _ (dname z) w' yb (rarg z)). cbn. repeat split.
    + destruct Hw; [apply r_step; split; [assumption|reflexivity]|apply r_refl].
    + exact Hw'.
    + rewrite <- kb. exact pb.
    + exact Hu.
    + reflexivity.
    + congruence.
  - apply forallb_All in Ht. eapply All_impl; [exact Ht|].
    intros d Hd. now move/andP: Hd => [? _].
Qed.

(** The [dbody] step of a (co)fixpoint, under [fix_context]: both sides extend their
    context by the [fix_context] of their own list, related by [peta_ctx_fix_context]. *)
Lemma commut_mfix_body Σ Γ Δ mfix mfix' m1 :
  peta_ctx Γ Δ -> on_ctx_free_vars xpredT Γ ->
  commut_mfix Σ mfix mfix' ->
  forallb (test_def ofvT (on_free_vars (shiftnP #|mfix| xpredT))) mfix ->
  OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody
            (fun x => (dname x, dtype x, rarg x))) mfix m1 ->
  ∑ lw lw', clos_refl (OnOne2 (on_Trel_eq (red1 Σ (Δ ,,, fix_context mfix')) dbody
                                 (fun x => (dname x, dtype x, rarg x)))) mfix' lw
          × All2 peta_def m1 lw' × All2 upto_def lw lw'.
Proof.
  intros HΔ HΓ Hm Ht Ho.
  have HΔ' : peta_ctx (Γ ,,, fix_context mfix) (Δ ,,, fix_context mfix').
  { apply peta_ctx_app; [exact HΔ|]. apply peta_ctx_fix_context. exact (All2_length Hm). }
  have HΓ' : on_ctx_free_vars xpredT (Γ ,,, fix_context mfix).
  { rewrite -(octx_shiftnP #|mfix|). apply on_ctx_free_vars_fix_context; [|exact HΓ].
    now apply forallb_All. }
  eapply (OnOne2_commut _ _ peta_def upto_def (fun d => is_true (ofvT (dbody d))));
    [exact upto_def_refl| |  |exact Ho].
  - eapply All2_impl; [exact Hm|].
    intros x [yn yt yb yr] [[pt ct] [[pb cb] [hn hr]]]. cbn in *.
    split; [repeat split; assumption|].
    intros Hq z [Hz Hk]. injection Hk as kn kt kr.
    destruct (cb _ _ (dbody z) HΔ' HΓ' Hq Hz) as (w & w' & Hw & Hw' & Hu).
    exists (mkdef _ yn yt w yr), (mkdef _ (dname z) yt w' (rarg z)). cbn. repeat split.
    + destruct Hw; [apply r_step; split; [assumption|reflexivity]|apply r_refl].
    + rewrite <- kt. exact pt.
    + exact Hw'.
    + reflexivity.
    + exact Hu.
    + congruence.
  - apply forallb_All in Ht. eapply All_impl; [exact Ht|].
    intros d Hd. move/andP: Hd => [_ Hb]. now rewrite ofvT_shiftnP in Hb.
Qed.

Lemma commut_Fix Σ mfix mfix' idx :
  commut_mfix Σ mfix mfix' -> commutes Σ (tFix mfix idx) (tFix mfix' idx).
Proof.
  intros Hm Γ Δ v HΔ HΓ Ht Hr. cbn in Ht.
  destruct (red1_tFix_inv Hr) as [(m1 & -> & Ho)|(m1 & -> & Ho)].
  - destruct (commut_mfix_ty Σ Γ Δ mfix mfix' m1 HΔ HΓ Hm Ht Ho) as (lw & lw' & Hw & Hw' & Hu).
    exists (tFix lw idx), (tFix lw' idx). repeat split.
    + eapply (clos_refl_map _ _ (fun m => tFix m idx)); [|exact Hw].
      intros x y H. now apply fix_red_ty.
    + now apply peta_Fix.
    + now apply utd_Fix.
  - destruct (commut_mfix_body Σ Γ Δ mfix mfix' m1 HΔ HΓ Hm Ht Ho) as (lw & lw' & Hw & Hw' & Hu).
    exists (tFix lw idx), (tFix lw' idx). repeat split.
    + destruct Hw; [apply r_step; now apply fix_red_body|apply r_refl].
    + now apply peta_Fix.
    + now apply utd_Fix.
Qed.

Lemma commut_CoFix Σ mfix mfix' idx :
  commut_mfix Σ mfix mfix' -> commutes Σ (tCoFix mfix idx) (tCoFix mfix' idx).
Proof.
  intros Hm Γ Δ v HΔ HΓ Ht Hr. cbn in Ht.
  destruct (red1_tCoFix_inv Hr) as [(m1 & -> & Ho)|(m1 & -> & Ho)].
  - destruct (commut_mfix_ty Σ Γ Δ mfix mfix' m1 HΔ HΓ Hm Ht Ho) as (lw & lw' & Hw & Hw' & Hu).
    exists (tCoFix lw idx), (tCoFix lw' idx). repeat split.
    + eapply (clos_refl_map _ _ (fun m => tCoFix m idx)); [|exact Hw].
      intros x y H. now apply cofix_red_ty.
    + now apply peta_CoFix.
    + now apply utd_CoFix.
  - destruct (commut_mfix_body Σ Γ Δ mfix mfix' m1 HΔ HΓ Hm Ht Ho) as (lw & lw' & Hw & Hw' & Hu).
    exists (tCoFix lw idx), (tCoFix lw' idx). repeat split.
    + destruct Hw; [apply r_step; now apply cofix_red_body|apply r_refl].
    + now apply peta_CoFix.
    + now apply utd_CoFix.
Qed.

(** ** [tCase]: six [red1] rules. [red_iota] and [red_cofix_case] are the standalone
    root lemmas; the four congruences reduce the parameters, the return type (under
    [inst_case_predicate_context]), the discriminee, or one branch (under
    [inst_case_branch_context]). Both case contexts are computed from [pparams], which
    [peta] may change, so the η side reads its own — [peta_inst_case_context] relates
    them, and [on_ctx_free_vars_inst_case_context] (base) supplies the scoping premise. *)
Lemma red1_tCase_inv {Σ Γ ci p c brs v} :
  red1 Σ Γ (tCase ci p c brs) v ->
  (∑ k uu args br, (c = mkApps (tConstruct ci.(ci_ind) k uu) args)
     × (nth_error brs k = Some br)
     × (#|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat)
     × (v = iota_red ci.(ci_npar) p args br))
  + (∑ mfix idx args narg fn, (c = mkApps (tCoFix mfix idx) args)
     × (unfold_cofix mfix idx = Some (narg, fn)) × (v = tCase ci p (mkApps fn args) brs))
  + (∑ par1, (v = tCase ci (set_pparams p par1) c brs) × OnOne2 (red1 Σ Γ) p.(pparams) par1)
  + (∑ r, (v = tCase ci (set_preturn p r) c brs)
     × red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) r)
  + (∑ c1, (v = tCase ci p c1 brs) × red1 Σ Γ c c1)
  + (∑ brs1, (v = tCase ci p c brs1)
     × OnOne2 (fun br br' => on_Trel_eq (red1 Σ (Γ ,,, inst_case_branch_context p br))
                               bbody bcontext br br') brs brs1).
Proof.
  intro H. remember (tCase ci p c brs) as t eqn:Heq.
  destruct H; try discriminate Heq; try solve [red1_dismiss_mkApps Heq].
  all: injection Heq as e1 e2 e3 e4; subst.
  - left; left; left; left; left. eexists _, _, _, _. repeat split; eassumption.
  - left; left; left; left; right. eexists _, _, _, _, _. repeat split; eassumption.
  - left; left; left; right. eexists; split; [reflexivity|assumption].
  - left; left; right. eexists; split; [reflexivity|assumption].
  - left; right. eexists; split; [reflexivity|assumption].
  - right. eexists; split; [reflexivity|assumption].
Qed.

Lemma set_pparams_id p : set_pparams p (pparams p) = p.
Proof. now destruct p. Qed.

Lemma set_preturn_id p : set_preturn p (preturn p) = p.
Proof. now destruct p. Qed.

Lemma All2_upto_branch_refl brs :
  All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                   × upto_domain x.(bbody) y.(bbody)) brs brs.
Proof. apply All2_same. intros; split; reflexivity. Qed.

Lemma commut_Case Σ ci p p' c c' brs brs' :
  All2 (fun x y => peta x y × commutes Σ x y) p.(pparams) p'.(pparams) ->
  p.(puinst) = p'.(puinst) -> p.(pcontext) = p'.(pcontext) ->
  peta p.(preturn) p'.(preturn) -> commutes Σ p.(preturn) p'.(preturn) ->
  peta c c' -> commutes Σ c c' ->
  All2 (fun x y => (x.(bcontext) = y.(bcontext))
                   × (peta x.(bbody) y.(bbody) × commutes Σ x.(bbody) y.(bbody))) brs brs' ->
  commutes Σ (tCase ci p c brs) (tCase ci p' c' brs').
Proof.
  intros Hpar Hu Hpc pr Ir pc Ic Hbrs Γ Δ v HΔ HΓ Ht Hr.
  cbn in Ht. move/and5P: Ht => [Hpars Hret Hpctx Hc Hbrsf].
  have hpar : All2 peta (pparams p) (pparams p').
  { eapply All2_impl; [exact Hpar|]. now intros ? ? [? _]. }
  have hbr : All2 (fun x y => (x.(bcontext) = y.(bcontext)) × peta x.(bbody) y.(bbody)) brs brs'.
  { eapply All2_impl; [exact Hbrs|]. now intros ? ? [? [? _]]. }
  have HP : peta (tCase ci p c brs) (tCase ci p' c' brs').
  { now apply peta_Case. }
  destruct (red1_tCase_inv Hr)
    as [[[[[(k & uu & args & br & -> & Hnth & Hlen & ->)
           |(mfix & idx & args & narg & fn & -> & Hunf & ->)]
          |(par1 & -> & Ho)]|(r & -> & Hrr)]|(c1 & -> & Hrc)]|(brs1 & -> & Ho)].
  - exact (peta_commut_red_iota Σ Δ ci k uu args p brs br _ Hnth Hlen HP).
  - exact (peta_commut_red_cofix_case Σ Δ ci p mfix idx args narg fn brs _ Hunf HP).
  - (* parameters *)
    destruct (OnOne2_commut (red1 Σ Γ) (red1 Σ Δ) peta upto_domain (fun x => is_true (ofvT x))
                (pparams p) (pparams p') par1 (fun x => upto_domain_refl x))
      as (lw & lw' & Hw & Hw' & Hu').
    + eapply All2_impl; [exact Hpar|]. intros x y [pxy cxy]. split; [exact pxy|].
      intros Hq z Hz. exact (cxy Γ Δ z HΔ HΓ Hq Hz).
    + now apply forallb_All.
    + exact Ho.
    + exists (tCase ci (set_pparams p' lw) c' brs'), (tCase ci (set_pparams p' lw') c' brs').
      repeat split.
      * destruct Hw; [apply r_step; now apply case_red_param|].
        rewrite set_pparams_id. apply r_refl.
      * apply peta_Case; cbn; assumption.
      * apply utd_Case; cbn; try reflexivity; [exact Hu'|apply All2_upto_branch_refl].
  - (* return type, under the predicate context *)
    have HΔ' : peta_ctx (Γ ,,, inst_case_predicate_context p) (Δ ,,, inst_case_predicate_context p').
    { apply peta_ctx_app; [exact HΔ|]. unfold inst_case_predicate_context.
      rewrite -Hu -Hpc. exact (peta_inst_case_context _ _ _ _ hpar). }
    have HΓ' : on_ctx_free_vars xpredT (Γ ,,, inst_case_predicate_context p).
    { unfold inst_case_predicate_context. rewrite -(octx_shiftnP #|pcontext p|).
      now apply on_ctx_free_vars_inst_case_context. }
    rewrite ofvT_shiftnP in Hret.
    destruct (Ir _ _ r HΔ' HΓ' Hret Hrr) as (w & w' & Hw & Hw' & Hu').
    exists (tCase ci (set_preturn p' w) c' brs'), (tCase ci (set_preturn p' w') c' brs').
    repeat split.
    + destruct Hw; [apply r_step; now apply case_red_return|].
      rewrite set_preturn_id. apply r_refl.
    + apply peta_Case; cbn; assumption.
    + apply utd_Case; cbn; try reflexivity;
        [now apply All2_same|exact Hu'|apply All2_upto_branch_refl].
  - (* discriminee *)
    destruct (Ic Γ Δ c1 HΔ HΓ Hc Hrc) as (w & w' & Hw & Hw' & Hu').
    exists (tCase ci p' w brs'), (tCase ci p' w' brs'). repeat split.
    + eapply (clos_refl_map _ _ (fun x => tCase ci p' x brs')); [|exact Hw].
      intros x y H. now apply case_red_discr.
    + now apply peta_Case.
    + apply utd_Case; try reflexivity;
        [now apply All2_same|exact Hu'|apply All2_upto_branch_refl].
  - (* one branch, under its branch context *)
    destruct (OnOne2_commut
                (fun br br' => on_Trel_eq (red1 Σ (Γ ,,, inst_case_branch_context p br))
                                 bbody bcontext br br')
                (fun br br' => on_Trel_eq (red1 Σ (Δ ,,, inst_case_branch_context p' br))
                                 bbody bcontext br br')
                (fun x y => (x.(bcontext) = y.(bcontext)) × peta x.(bbody) y.(bbody))
                (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                            × upto_domain x.(bbody) y.(bbody))
                (fun br => is_true (test_context_k (fun k => on_free_vars (closedP k xpredT))
                                      #|pparams p| br.(bcontext)
                                    && on_free_vars (shiftnP #|br.(bcontext)| xpredT) br.(bbody)))
                brs brs' brs1)
      as (lw & lw' & Hw & Hw' & Hu').
    + intros x. split; reflexivity.
    + eapply All2_impl; [exact Hbrs|].
      intros x [yc yb] [hc [pb cb]]. cbn in *.
      split; [split; assumption|].
      intros Hq z [Hz Hk]. move/andP: Hq => [Hq1 Hq2]. rewrite ofvT_shiftnP in Hq2.
      have HΔ' : peta_ctx (Γ ,,, inst_case_branch_context p x)
                          (Δ ,,, inst_case_branch_context p' {| bcontext := yc; bbody := yb |}).
      { apply peta_ctx_app; [exact HΔ|]. unfold inst_case_branch_context. cbn.
        rewrite -Hu -hc. exact (peta_inst_case_context _ _ _ _ hpar). }
      have HΓ' : on_ctx_free_vars xpredT (Γ ,,, inst_case_branch_context p x).
      { unfold inst_case_branch_context. rewrite -(octx_shiftnP #|bcontext x|).
        now apply on_ctx_free_vars_inst_case_context. }
      destruct (cb _ _ (bbody z) HΔ' HΓ' Hq2 Hz) as (w & w' & Hw & Hw' & Hu').
      exists {| bcontext := yc; bbody := w |}, {| bcontext := bcontext z; bbody := w' |}.
      cbn. repeat split.
      * destruct Hw; [apply r_step; split; [assumption|reflexivity]|apply r_refl].
      * exact Hw'.
      * rewrite -Hk hc. reflexivity.
      * exact Hu'.
    + now apply forallb_All.
    + exact Ho.
    + exists (tCase ci p' c' lw), (tCase ci p' c' lw'). repeat split.
      * destruct Hw; [apply r_step; now apply case_red_brs|apply r_refl].
      * now apply peta_Case.
      * apply utd_Case; try reflexivity; [now apply All2_same|exact Hu'].
Qed.

