From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICReduction PCUICCases PCUICEquality PCUICPrimitive
     PCUICEtaDefs PCUICEtaParallel.
From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
Set Default Goal Selector "!".

Ltac cong1 := induction 1;
  [ apply eta_step; solve [econstructor; eauto]
  | apply eta_refl | eapply eta_trans; eauto ].

Lemma eta_Lambda_dom na A A' b : eta A A' -> eta (tLambda na A b) (tLambda na A' b).
Proof. cong1. Qed.
Lemma eta_Lambda_body na A b b' : eta b b' -> eta (tLambda na A b) (tLambda na A b').
Proof. cong1. Qed.
Lemma eta_Lambda na A A' b b' : eta A A' -> eta b b' -> eta (tLambda na A b) (tLambda na A' b').
Proof. intros. apply (eta_trans (u := tLambda na A' b)); [now apply eta_Lambda_dom|now apply eta_Lambda_body]. Qed.
Lemma eta_Prod_dom na A A' b : eta A A' -> eta (tProd na A b) (tProd na A' b).
Proof. cong1. Qed.
Lemma eta_Prod_cod na A b b' : eta b b' -> eta (tProd na A b) (tProd na A b').
Proof. cong1. Qed.
Lemma eta_Prod na A A' b b' : eta A A' -> eta b b' -> eta (tProd na A b) (tProd na A' b').
Proof. intros. apply (eta_trans (u := tProd na A' b)); [now apply eta_Prod_dom|now apply eta_Prod_cod]. Qed.
Lemma eta_LetIn_def na d d' t b : eta d d' -> eta (tLetIn na d t b) (tLetIn na d' t b).
Proof. cong1. Qed.
Lemma eta_LetIn_ty na d t t' b : eta t t' -> eta (tLetIn na d t b) (tLetIn na d t' b).
Proof. cong1. Qed.
Lemma eta_LetIn_body na d t b b' : eta b b' -> eta (tLetIn na d t b) (tLetIn na d t b').
Proof. cong1. Qed.
Lemma eta_LetIn na d d' t t' b b' :
  eta d d' -> eta t t' -> eta b b' -> eta (tLetIn na d t b) (tLetIn na d' t' b').
Proof.
  intros. apply (eta_trans (u := tLetIn na d' t b)); [now apply eta_LetIn_def|].
  apply (eta_trans (u := tLetIn na d' t' b)); [now apply eta_LetIn_ty|now apply eta_LetIn_body].
Qed.
Lemma eta_App a a' b b' : eta a a' -> eta b b' -> eta (tApp a b) (tApp a' b').
Proof. intros. apply (eta_trans (u := tApp a' b)); [now apply eta_App_l|now apply eta_App_r]. Qed.

Lemma eta_Evar_step ev pre a a' l :
  eta a a' -> eta (tEvar ev (pre ++ a :: l)) (tEvar ev (pre ++ a' :: l)).
Proof.
  induction 1; [|apply eta_refl|eapply eta_trans; eauto].
  apply eta_step. apply evar_eta. apply OnOne2_app. now constructor.
Qed.
Lemma eta_Evar ev l l' : All2 eta l l' -> eta (tEvar ev l) (tEvar ev l').
Proof.
  intros a. enough (H : forall pre, eta (tEvar ev (pre ++ l)) (tEvar ev (pre ++ l'))) by apply (H []).
  induction a; intros pre.
  - rewrite !app_nil_r; apply eta_refl.
  - eapply eta_trans; [exact (eta_Evar_step ev pre _ _ _ r)|].
    specialize (IHa (pre ++ [y])). rewrite -!app_assoc in IHa. exact IHa.
Qed.

Lemma eta_Case_param_step ci p pre a a' l c brs :
  eta a a' ->
  eta (tCase ci (set_pparams p (pre ++ a :: l)) c brs)
      (tCase ci (set_pparams p (pre ++ a' :: l)) c brs).
Proof.
  induction 1; [|apply eta_refl|eapply eta_trans; eauto].
  apply eta_step.
  replace (tCase ci (set_pparams p (pre ++ y :: l)) c brs)
    with (tCase ci (set_pparams (set_pparams p (pre ++ x :: l)) (pre ++ y :: l)) c brs)
    by reflexivity.
  apply case_eta_param. apply OnOne2_app. now constructor.
Qed.
Lemma eta_Case_params ci p params' c brs :
  All2 eta p.(pparams) params' ->
  eta (tCase ci p c brs) (tCase ci (set_pparams p params') c brs).
Proof.
  intros a.
  enough (H : forall pre, eta (tCase ci (set_pparams p (pre ++ pparams p)) c brs)
                              (tCase ci (set_pparams p (pre ++ params')) c brs)).
  { specialize (H []); cbn in H.
    replace (set_pparams p (pparams p)) with p in H by (destruct p; reflexivity). exact H. }
  induction a; intros pre.
  - apply eta_refl.
  - eapply eta_trans; [exact (eta_Case_param_step ci p pre _ _ _ c brs r)|].
    specialize (IHa (pre ++ [y])). rewrite -!app_assoc in IHa. exact IHa.
Qed.
Lemma eta_Case_return ci p r' c brs :
  eta p.(preturn) r' -> eta (tCase ci p c brs) (tCase ci (set_preturn p r') c brs).
Proof.
  intros h. remember (preturn p) as r eqn:Hr. revert p Hr.
  induction h; intros p Hr; subst.
  - apply eta_step. apply (case_eta_return ci p y). eassumption.
  - destruct p; apply eta_refl.
  - eapply eta_trans.
    + apply (IHh1 p); reflexivity.
    + specialize (IHh2 (set_preturn p y)). cbn in IHh2. apply IHh2; reflexivity.
Qed.
Lemma eta_Case_brs_step ci p c pre a a' l :
  eta a.(bbody) a'.(bbody) -> a.(bcontext) = a'.(bcontext) ->
  eta (tCase ci p c (pre ++ a :: l)) (tCase ci p c (pre ++ a' :: l)).
Proof.
  intros hb hc. remember (bbody a) as x eqn:Hx. remember (bbody a') as y eqn:Hy.
  revert a a' Hx Hy hc. induction hb; intros a0 a1 Hx Hy hc; subst.
  - apply eta_step. apply case_eta_brs. apply OnOne2_app. constructor.
    unfold on_Trel; cbn. split; auto.
  - destruct a0, a1; cbn in *; subst; apply eta_refl.
  - eapply eta_trans.
    + apply (IHhb1 a0 {| bcontext := bcontext a0; bbody := y |}); cbn; auto.
    + apply (IHhb2 {| bcontext := bcontext a0; bbody := y |} a1); cbn; auto.
Qed.
Lemma eta_Case_brs ci p c brs brs' :
  All2 (fun x y => eta x.(bbody) y.(bbody) × x.(bcontext) = y.(bcontext)) brs brs' ->
  eta (tCase ci p c brs) (tCase ci p c brs').
Proof.
  intros a.
  enough (H : forall pre, eta (tCase ci p c (pre ++ brs)) (tCase ci p c (pre ++ brs'))) by apply (H []).
  induction a as [|x y l l' [hb hc] a IH]; intros pre.
  - rewrite !app_nil_r; apply eta_refl.
  - eapply eta_trans; [exact (eta_Case_brs_step ci p c pre x y l hb hc)|].
    specialize (IH (pre ++ [y])). rewrite -!app_assoc in IH. exact IH.
Qed.
Lemma eta_Case ci p p' c c' brs brs' :
  All2 eta p.(pparams) p'.(pparams) ->
  p.(puinst) = p'.(puinst) -> p.(pcontext) = p'.(pcontext) ->
  eta p.(preturn) p'.(preturn) -> eta c c' ->
  All2 (fun x y => eta x.(bbody) y.(bbody) × x.(bcontext) = y.(bcontext)) brs brs' ->
  eta (tCase ci p c brs) (tCase ci p' c' brs').
Proof.
  intros hp hu hc hr hd hb.
  eapply eta_trans; [apply (eta_Case_params ci p p'.(pparams) c brs hp)|].
  eapply eta_trans; [apply (eta_Case_return ci (set_pparams p p'.(pparams)) p'.(preturn) c brs); cbn; exact hr|].
  eapply eta_trans; [apply (eta_Case_discr ci _ c c' brs hd)|].
  eapply eta_trans; [apply (eta_Case_brs ci _ c' brs brs' hb)|].
  replace (set_preturn (set_pparams p p'.(pparams)) p'.(preturn)) with p'.
  { apply eta_refl. }
  destruct p, p'; cbn in *; subst; reflexivity.
Qed.

Lemma eta_Fix_ty_step pre a a' l idx :
  eta a.(dtype) a'.(dtype) -> dname a = dname a' -> dbody a = dbody a' -> rarg a = rarg a' ->
  eta (tFix (pre ++ a :: l) idx) (tFix (pre ++ a' :: l) idx).
Proof.
  intros he hn hb hr. remember (dtype a) as x eqn:Hx. remember (dtype a') as y eqn:Hy.
  revert a a' Hx Hy hn hb hr. induction he; intros a0 a1 Hx Hy hn hb hr; subst.
  - apply eta_step. apply fix_eta_ty. apply OnOne2_app. constructor.
    unfold on_Trel; cbn. split; [auto|]. rewrite hn hb hr; reflexivity.
  - destruct a0, a1; cbn in *; subst; apply eta_refl.
  - eapply eta_trans.
    + apply (IHhe1 a0 {| dname := dname a0; dtype := y; dbody := dbody a0; rarg := rarg a0 |}); cbn; auto.
    + apply (IHhe2 {| dname := dname a0; dtype := y; dbody := dbody a0; rarg := rarg a0 |} a1); cbn; auto;
        rewrite -?hn -?hb -?hr //.
Qed.
Lemma eta_Fix_body_step pre a a' l idx :
  eta a.(dbody) a'.(dbody) -> dname a = dname a' -> dtype a = dtype a' -> rarg a = rarg a' ->
  eta (tFix (pre ++ a :: l) idx) (tFix (pre ++ a' :: l) idx).
Proof.
  intros he hn ht hr. remember (dbody a) as x eqn:Hx. remember (dbody a') as y eqn:Hy.
  revert a a' Hx Hy hn ht hr. induction he; intros a0 a1 Hx Hy hn ht hr; subst.
  - apply eta_step. apply fix_eta_body. apply OnOne2_app. constructor.
    unfold on_Trel; cbn. split; [auto|]. rewrite hn ht hr; reflexivity.
  - destruct a0, a1; cbn in *; subst; apply eta_refl.
  - eapply eta_trans.
    + apply (IHhe1 a0 {| dname := dname a0; dtype := dtype a0; dbody := y; rarg := rarg a0 |}); cbn; auto.
    + apply (IHhe2 {| dname := dname a0; dtype := dtype a0; dbody := y; rarg := rarg a0 |} a1); cbn; auto;
        rewrite -?hn -?ht -?hr //.
Qed.
Lemma eta_Fix mfix mfix' idx :
  All2 (fun d d' => eta (dtype d) (dtype d') × eta (dbody d) (dbody d')
                    × dname d = dname d' × rarg d = rarg d') mfix mfix' ->
  eta (tFix mfix idx) (tFix mfix' idx).
Proof.
  intros a.
  enough (H : forall pre, eta (tFix (pre ++ mfix) idx) (tFix (pre ++ mfix') idx)) by apply (H []).
  induction a as [|x y l l' [ht [hb [hn hr]]] a IH]; intros pre.
  - rewrite !app_nil_r; apply eta_refl.
  - eapply eta_trans.
    + exact (eta_Fix_ty_step pre x {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |} l idx ht eq_refl eq_refl eq_refl).
    + eapply eta_trans.
      * refine (eta_Fix_body_step pre {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |} y l idx _ _ _ _); cbn; auto.
      * specialize (IH (pre ++ [y])). rewrite -!app_assoc in IH. exact IH.
Qed.
Lemma eta_CoFix_ty_step pre a a' l idx :
  eta a.(dtype) a'.(dtype) -> dname a = dname a' -> dbody a = dbody a' -> rarg a = rarg a' ->
  eta (tCoFix (pre ++ a :: l) idx) (tCoFix (pre ++ a' :: l) idx).
Proof.
  intros he hn hb hr. remember (dtype a) as x eqn:Hx. remember (dtype a') as y eqn:Hy.
  revert a a' Hx Hy hn hb hr. induction he; intros a0 a1 Hx Hy hn hb hr; subst.
  - apply eta_step. apply cofix_eta_ty. apply OnOne2_app. constructor.
    unfold on_Trel; cbn. split; [auto|]. rewrite hn hb hr; reflexivity.
  - destruct a0, a1; cbn in *; subst; apply eta_refl.
  - eapply eta_trans.
    + apply (IHhe1 a0 {| dname := dname a0; dtype := y; dbody := dbody a0; rarg := rarg a0 |}); cbn; auto.
    + apply (IHhe2 {| dname := dname a0; dtype := y; dbody := dbody a0; rarg := rarg a0 |} a1); cbn; auto;
        rewrite -?hn -?hb -?hr //.
Qed.
Lemma eta_CoFix_body_step pre a a' l idx :
  eta a.(dbody) a'.(dbody) -> dname a = dname a' -> dtype a = dtype a' -> rarg a = rarg a' ->
  eta (tCoFix (pre ++ a :: l) idx) (tCoFix (pre ++ a' :: l) idx).
Proof.
  intros he hn ht hr. remember (dbody a) as x eqn:Hx. remember (dbody a') as y eqn:Hy.
  revert a a' Hx Hy hn ht hr. induction he; intros a0 a1 Hx Hy hn ht hr; subst.
  - apply eta_step. apply cofix_eta_body. apply OnOne2_app. constructor.
    unfold on_Trel; cbn. split; [auto|]. rewrite hn ht hr; reflexivity.
  - destruct a0, a1; cbn in *; subst; apply eta_refl.
  - eapply eta_trans.
    + apply (IHhe1 a0 {| dname := dname a0; dtype := dtype a0; dbody := y; rarg := rarg a0 |}); cbn; auto.
    + apply (IHhe2 {| dname := dname a0; dtype := dtype a0; dbody := y; rarg := rarg a0 |} a1); cbn; auto;
        rewrite -?hn -?ht -?hr //.
Qed.
Lemma eta_CoFix mfix mfix' idx :
  All2 (fun d d' => eta (dtype d) (dtype d') × eta (dbody d) (dbody d')
                    × dname d = dname d' × rarg d = rarg d') mfix mfix' ->
  eta (tCoFix mfix idx) (tCoFix mfix' idx).
Proof.
  intros a.
  enough (H : forall pre, eta (tCoFix (pre ++ mfix) idx) (tCoFix (pre ++ mfix') idx)) by apply (H []).
  induction a as [|x y l l' [ht [hb [hn hr]]] a IH]; intros pre.
  - rewrite !app_nil_r; apply eta_refl.
  - eapply eta_trans.
    + exact (eta_CoFix_ty_step pre x {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |} l idx ht eq_refl eq_refl eq_refl).
    + eapply eta_trans.
      * refine (eta_CoFix_body_step pre {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |} y l idx _ _ _ _); cbn; auto.
      * specialize (IH (pre ++ [y])). rewrite -!app_assoc in IH. exact IH.
Qed.

Lemma eta_Prim_type arr t' :
  eta arr.(array_type) t' ->
  eta (tPrim (primArray; primArrayModel arr))
      (tPrim (primArray; primArrayModel (set_array_type arr t'))).
Proof.
  intros h. remember (array_type arr) as x eqn:Hx. revert arr Hx.
  induction h; intros arr Hx; subst.
  - apply eta_step. apply (array_eta_type arr y). eassumption.
  - destruct arr; apply eta_refl.
  - eapply eta_trans; [apply (IHh1 arr); reflexivity|].
    specialize (IHh2 (set_array_type arr y)); cbn in IHh2. apply IHh2; reflexivity.
Qed.
Lemma eta_Prim_default arr d' :
  eta arr.(array_default) d' ->
  eta (tPrim (primArray; primArrayModel arr))
      (tPrim (primArray; primArrayModel (set_array_default arr d'))).
Proof.
  intros h. remember (array_default arr) as x eqn:Hx. revert arr Hx.
  induction h; intros arr Hx; subst.
  - apply eta_step. apply (array_eta_def arr y). eassumption.
  - destruct arr; apply eta_refl.
  - eapply eta_trans; [apply (IHh1 arr); reflexivity|].
    specialize (IHh2 (set_array_default arr y)); cbn in IHh2. apply IHh2; reflexivity.
Qed.
Lemma eta_Prim_val_step arr pre a a' l :
  eta a a' ->
  eta (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ a :: l))))
      (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ a' :: l)))).
Proof.
  induction 1; [|apply eta_refl|eapply eta_trans; eauto].
  apply eta_step.
  replace (set_array_value arr (pre ++ y :: l))
    with (set_array_value (set_array_value arr (pre ++ x :: l)) (pre ++ y :: l))
    by reflexivity.
  apply array_eta_val. apply OnOne2_app. now constructor.
Qed.
Lemma eta_Prim_value arr value' :
  All2 eta arr.(array_value) value' ->
  eta (tPrim (primArray; primArrayModel arr))
      (tPrim (primArray; primArrayModel (set_array_value arr value'))).
Proof.
  intros a.
  enough (H : forall pre, eta (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ arr.(array_value)))))
                              (tPrim (primArray; primArrayModel (set_array_value arr (pre ++ value'))))).
  { specialize (H []); cbn in H.
    replace (set_array_value arr (array_value arr)) with arr in H by (destruct arr; reflexivity). exact H. }
  induction a; intros pre.
  - apply eta_refl.
  - eapply eta_trans; [exact (eta_Prim_val_step arr pre _ _ _ r)|].
    specialize (IHa (pre ++ [y])). rewrite -!app_assoc in IHa. exact IHa.
Qed.
Lemma eta_Prim_array arr arr' :
  arr.(array_level) = arr'.(array_level) ->
  eta arr.(array_type) arr'.(array_type) ->
  eta arr.(array_default) arr'.(array_default) ->
  All2 eta arr.(array_value) arr'.(array_value) ->
  eta (tPrim (primArray; primArrayModel arr)) (tPrim (primArray; primArrayModel arr')).
Proof.
  intros hl ht hd hv.
  eapply eta_trans; [apply (eta_Prim_type arr arr'.(array_type) ht)|].
  eapply eta_trans; [apply (eta_Prim_default (set_array_type arr arr'.(array_type)) arr'.(array_default)); cbn; exact hd|].
  eapply eta_trans; [apply (eta_Prim_value (set_array_default (set_array_type arr arr'.(array_type)) arr'.(array_default)) arr'.(array_value)); cbn; exact hv|].
  replace (set_array_value (set_array_default (set_array_type arr arr'.(array_type)) arr'.(array_default)) arr'.(array_value)) with arr'.
  { apply eta_refl. }
  destruct arr, arr'; cbn in *; subst; reflexivity.
Qed.

Lemma subst_eta σ σ' k b :
  All2 eta σ σ' -> eta (subst σ k b) (subst σ' k b).
Proof.
  revert σ σ' k. induction b using term_forall_list_ind; intros σ σ' k XX; cbn.
  all: try solve [apply eta_refl].
  - destruct (k <=? n) eqn:Hle; [|apply eta_refl].
    destruct (nth_error σ (n - k)) as [a|] eqn:E.
    + eapply All2_nth_error_Some in E as [a' [E1 E2]]; [|exact XX]. rewrite E1.
      now apply weakening_eta.
    + eapply All2_nth_error_None in E as E1; [|exact XX].
      rewrite E1. rewrite (All2_length XX). apply eta_refl.
  - apply eta_Evar. eapply All2_map. eapply All_All2; tea; cbn. eauto.
  - apply eta_Prod; eauto.
  - apply eta_Lambda; eauto.
  - apply eta_LetIn; eauto.
  - apply eta_App; eauto.
  - destruct X as [hpar [_ hret]].
    apply eta_Case; cbn; eauto.
    + eapply All2_map. eapply All_All2; tea; cbn. eauto.
    + eapply All2_map. eapply All_All2; tea; cbn. intros x [_ hbb]. split; [eauto|reflexivity].
  - apply eta_Proj; eauto.
  - apply eta_Fix. eapply All2_map. eapply All_All2; tea; cbn.
    intros x [ht hb]. repeat split; eauto.
  - apply eta_CoFix. eapply All2_map. eapply All_All2; tea; cbn.
    intros x [ht hb]. repeat split; eauto.
  - destruct p as [tag pm]; destruct pm; cbn in *; try apply eta_refl.
    destruct X as [ht [hd hv]].
    apply eta_Prim_array; cbn; [reflexivity|eauto|eauto|].
    eapply All2_map. eapply All_All2; tea; cbn. eauto.
Qed.

Lemma eta_subst_body s k b b' :
  eta b b' -> eta (subst s k b) (subst s k b').
Proof.
  induction 1.
  - apply eta_step. now apply eta1_subst.
  - apply eta_refl.
  - eapply eta_trans; eauto.
Qed.

Lemma eta_subst s s' b b' :
  All2 eta s s' -> eta b b' -> eta (subst0 s b) (subst0 s' b').
Proof.
  intros hs hb. apply (eta_trans (u := subst0 s b')).
  - apply (eta_subst_body s 0 b b' hb).
  - apply (subst_eta s s' 0 b' hs).
Qed.

(** ** Corollaries at level 0 (the shapes the C3 four-cases hypotheses carried)

    These are NOT exported as the authoritative shared names: the final C3 assembly Requires
    EtaL2's [eta_subst] from [PCUICEtaConfluence.v] (frac/eta-l2 @ 7b4491f0). This file is the
    INDEPENDENT second proof (corroboration) of that critical lemma, on its own route. *)

Corollary eta_subst_terms σ σ' M : All2 eta σ σ' -> eta (subst0 σ M) (subst0 σ' M).
Proof. intros. now apply subst_eta. Qed.

Corollary eta1_subst0 σ M M' : eta1 M M' -> eta1 (subst0 σ M) (subst0 σ M').
Proof. intros. now apply eta1_subst. Qed.
