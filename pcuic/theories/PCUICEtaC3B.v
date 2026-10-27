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

