(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, C1a: [upto_domain] commutes with [red1].

   The pinned statement is [C1a_fixed_statement] ([PCUICEtaBetaEta]):
     [upto_domain t t' -> red1 Σ Γ t u ->
        ∑ u', clos_refl (red1 Σ Γ) t' u' × upto_domain u u'].
   The one-step form is FALSE (plan B3(b)): a step inside a λ domain has no
   counterpart on the related side, whose domain is arbitrary. That is the
   [abs_red_l] case below, closed by [r_refl].

   WHY THE INDUCTION RUNS OVER A RELATED CONTEXT. Under a λ the two sides
   reduce in [Γ ,, vass na ty] and [Γ' ,, vass na' ty'] with UNRELATED [ty]
   and [ty']. [red1] reads a context only through [decl_body] (rule
   [red_rel]), so the induction carries [upto_domain_bodies Γ Γ']: bodies
   related by [upto_domain], types and names free. The plan's
   [upto_domain_ctx] (PCUICEtaConfluence) also relates the TYPES, so it is not
   preserved under a λ and cannot be the induction invariant; it implies
   [upto_domain_bodies], which gives the plan's general form
   [red1_upto_domain_ctx] as a corollary.

   The [tCase] predicate/branch contexts (plan §6 rank 5) are no obstacle:
   [upto_domain] relates them by [eq_context_upto_names] (equal bodies and
   types), so the instantiated contexts have bodies related by [upto_domain]
   through the related parameters.

   Dependencies: base syntax and [red1] only, plus [PCUICEtaDefs],
   [PCUICEtaConfluence] (the [upto_domain] equivalence) and [PCUICEtaBetaEta]
   (the pinned statement). No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICLiftSubst
     PCUICPrimitive PCUICInduction PCUICReduction PCUICEquality PCUICCases
     PCUICEtaDefs PCUICEtaConfluence PCUICEtaBetaEta.

Local Open Scope type_scope.
Set Default Goal Selector "!".

(** ** Generic list and closure helpers *)

Lemma All2_map2_All {A B C D} (P : A -> Type) (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (g : B -> D) l l' :
  All P l -> All2 R l l' -> (forall x y, P x -> R x y -> R' (f x) (g y)) ->
  All2 R' (map f l) (map g l').
Proof.
  intros hP hR H. induction hR in hP |- *; cbn; constructor; depelim hP; eauto.
Qed.

Lemma onPrims_map2 {R R' : term -> term -> Type} {Re} {P : term -> Type}
  (f g : term -> term) p p' :
  tPrimProp P p -> onPrims R Re p p' ->
  (forall x y, P x -> R x y -> R' (f x) (g y)) ->
  onPrims R' Re (map_prim f p) (map_prim g p').
Proof.
  intros h e hf. depelim e; cbn in h |- *; constructor; cbn.
  all: try destruct h as (hty & hdef & hval).
  all: try solve [eauto].
  eapply All2_map2_All; eassumption.
Qed.

(** One [OnOne2] step against an [All2]-related list: either one step on the
    related list, or none. *)
Lemma OnOne2_All2_sim {A B} (E : A -> B -> Type) (R : A -> A -> Type) (R' : B -> B -> Type)
  l l1 l' :
  OnOne2 R l l1 -> All2 E l l' ->
  (forall x y x', R x y -> E x x' -> ∑ y', clos_refl R' x' y' × E y y') ->
  ∑ l1', clos_refl (OnOne2 R') l' l1' × All2 E l1 l1'.
Proof.
  intros hR. induction hR as [hd hd' tl r|hd tl tl' hR IH] in l' |- *; intros hE H.
  - destruct l' as [|x' l'']; [solve [depelim hE]|].
    assert (ex : E hd x') by (now depelim hE).
    assert (hl : All2 E tl l'') by (now depelim hE).
    destruct (H _ _ _ r ex) as (y' & hy & ey).
    exists (y' :: l''). split; [|now constructor].
    destruct hy as [? hy|]; [apply r_step; now constructor|apply r_refl].
  - destruct l' as [|x' l'']; [solve [depelim hE]|].
    assert (ex : E hd x') by (now depelim hE).
    assert (hl : All2 E tl l'') by (now depelim hE).
    destruct (IH l'' hl H) as (l1' & hy & ey).
    exists (x' :: l1'). split; [|now constructor].
    destruct hy as [? hy|]; [apply r_step; now constructor|apply r_refl].
Qed.

Lemma eq_context_upto_names_assumptions Γ Γ' :
  eq_context_upto_names Γ Γ' -> context_assumptions Γ = context_assumptions Γ'.
Proof.
  induction 1 as [|x y l l' r h IH]; [reflexivity|]. destruct r; cbn; congruence.
Qed.

(** ** [upto_domain] under lifting and substitution *)

Lemma upto_domain_lift t t' n k :
  upto_domain t t' -> upto_domain (lift n k t) (lift n k t').
Proof.
  intros e. induction t in t', e, k |- * using term_forall_list_ind; depelim e; cbn.
  all: try solve [constructor; eauto].
  - (* Evar *) constructor. eapply All2_map2_All; [exact X|eassumption|]. cbn; eauto.
  - (* Case *) destruct X as (Hpar & _ & Hret). constructor; cbn.
    + eapply All2_map2_All; [exact Hpar|eassumption|]. cbn; eauto.
    + assumption.
    + assumption.
    + match goal with H : eq_context_upto_names (pcontext p) _ |- _ =>
        rewrite -(All2_length H) end. eauto.
    + eauto.
    + eapply All2_map2_All; [exact X0|eassumption|]. cbn.
      intros x y [_ Hb] [Hc Hxy]. split; [assumption|].
      rewrite -(All2_length Hc). eauto.
  - (* Fix *) constructor.
    match goal with H : All2 _ m mfix' |- _ => rewrite -(All2_length H) end.
    eapply All2_map2_All; [exact X|eassumption|]. cbn.
    intros x y [Ht Hb] (Ht' & Hb' & Hr). repeat split; eauto.
  - (* CoFix *) constructor.
    match goal with H : All2 _ m mfix' |- _ => rewrite -(All2_length H) end.
    eapply All2_map2_All; [exact X|eassumption|]. cbn.
    intros x y [Ht Hb] (Ht' & Hb' & Hr). repeat split; eauto.
  - (* Prim *) constructor. eapply onPrims_map2; [exact X|eassumption|]. cbn; eauto.
Qed.

Lemma upto_domain_subst s s' t t' k :
  All2 upto_domain s s' -> upto_domain t t' ->
  upto_domain (subst s k t) (subst s' k t').
Proof.
  intros hs e. induction t in t', e, k |- * using term_forall_list_ind; depelim e; cbn.
  all: try solve [constructor; eauto].
  - (* Rel *) destruct (Nat.leb k n); [|constructor].
    destruct (nth_error s (n - k)) as [b|] eqn:E.
    + destruct (All2_nth_error_Some _ _ hs E) as [b' [-> hb]].
      now apply upto_domain_lift.
    + rewrite (All2_nth_error_None _ hs E) (All2_length hs). constructor.
  - (* Evar *) constructor. eapply All2_map2_All; [exact X|eassumption|]. cbn; eauto.
  - (* Case *) destruct X as (Hpar & _ & Hret). constructor; cbn.
    + eapply All2_map2_All; [exact Hpar|eassumption|]. cbn; eauto.
    + assumption.
    + assumption.
    + match goal with H : eq_context_upto_names (pcontext p) _ |- _ =>
        rewrite -(All2_length H) end. eauto.
    + eauto.
    + eapply All2_map2_All; [exact X0|eassumption|]. cbn.
      intros x y [_ Hb] [Hc Hxy]. split; [assumption|].
      rewrite -(All2_length Hc). eauto.
  - (* Fix *) constructor.
    match goal with H : All2 _ m mfix' |- _ => rewrite -(All2_length H) end.
    eapply All2_map2_All; [exact X|eassumption|]. cbn.
    intros x y [Ht Hb] (Ht' & Hb' & Hr). repeat split; eauto.
  - (* CoFix *) constructor.
    match goal with H : All2 _ m mfix' |- _ => rewrite -(All2_length H) end.
    eapply All2_map2_All; [exact X|eassumption|]. cbn.
    intros x y [Ht Hb] (Ht' & Hb' & Hr). repeat split; eauto.
  - (* Prim *) constructor. eapply onPrims_map2; [exact X|eassumption|]. cbn; eauto.
Qed.

(** ** Inversions *)

Lemma upto_domain_tRel_inv n t' : upto_domain (tRel n) t' -> t' = tRel n.
Proof. intros e; now depelim e. Qed.

Lemma upto_domain_tConst_inv c u t' : upto_domain (tConst c u) t' -> t' = tConst c u.
Proof. intros e; now depelim e. Qed.

Lemma upto_domain_tConstruct_inv i c u t' :
  upto_domain (tConstruct i c u) t' -> t' = tConstruct i c u.
Proof. intros e; now depelim e. Qed.

Lemma upto_domain_tApp_inv f a t' :
  upto_domain (tApp f a) t' ->
  ∑ f' a', (t' = tApp f' a') × upto_domain f f' × upto_domain a a'.
Proof. intros e; depelim e. do 2 eexists; split; [reflexivity|split; assumption]. Qed.

Lemma upto_domain_tLambda_inv na ty b t' :
  upto_domain (tLambda na ty b) t' ->
  ∑ na' ty' b', (t' = tLambda na' ty' b') × upto_domain b b'.
Proof. intros e; depelim e. do 3 eexists; split; [reflexivity|assumption]. Qed.

Lemma upto_domain_tProd_inv na a b t' :
  upto_domain (tProd na a b) t' ->
  ∑ na' a' b', (t' = tProd na' a' b') × upto_domain a a' × upto_domain b b'.
Proof. intros e; depelim e. do 3 eexists; split; [reflexivity|split; assumption]. Qed.

Lemma upto_domain_tLetIn_inv na b ty c t' :
  upto_domain (tLetIn na b ty c) t' ->
  ∑ na' b' ty' c', (t' = tLetIn na' b' ty' c') ×
    upto_domain b b' × upto_domain ty ty' × upto_domain c c'.
Proof.
  intros e; depelim e. do 4 eexists; split; [reflexivity|repeat split; assumption].
Qed.

Lemma upto_domain_tProj_inv pr c t' :
  upto_domain (tProj pr c) t' -> ∑ c', (t' = tProj pr c') × upto_domain c c'.
Proof. intros e; depelim e. eexists; split; [reflexivity|assumption]. Qed.

Lemma upto_domain_tEvar_inv ev l t' :
  upto_domain (tEvar ev l) t' -> ∑ l', (t' = tEvar ev l') × All2 upto_domain l l'.
Proof. intros e; depelim e. eexists; split; [reflexivity|assumption]. Qed.

Lemma upto_domain_tCase_inv ci p c brs t' :
  upto_domain (tCase ci p c brs) t' ->
  ∑ p' c' brs', (t' = tCase ci p' c' brs') ×
    All2 upto_domain p.(pparams) p'.(pparams) × p.(puinst) = p'.(puinst) ×
    eq_context_upto_names p.(pcontext) p'.(pcontext) ×
    upto_domain p.(preturn) p'.(preturn) × upto_domain c c' ×
    All2 (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext)
                     × upto_domain x.(bbody) y.(bbody)) brs brs'.
Proof.
  intros e; depelim e. do 3 eexists; split; [reflexivity|repeat split; assumption].
Qed.

Lemma upto_domain_tFix_inv mfix idx t' :
  upto_domain (tFix mfix idx) t' ->
  ∑ mfix', (t' = tFix mfix' idx) ×
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix'.
Proof. intros e; depelim e. eexists; split; [reflexivity|assumption]. Qed.

Lemma upto_domain_tCoFix_inv mfix idx t' :
  upto_domain (tCoFix mfix idx) t' ->
  ∑ mfix', (t' = tCoFix mfix' idx) ×
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) ×
                     x.(rarg) = y.(rarg)) mfix mfix'.
Proof. intros e; depelim e. eexists; split; [reflexivity|assumption]. Qed.

Lemma upto_domain_tPrim_array_inv arr t' :
  upto_domain (tPrim (primArray; primArrayModel arr)) t' ->
  ∑ arr', (t' = tPrim (primArray; primArrayModel arr')) ×
    (Universe.make' arr.(array_level) = Universe.make' arr'.(array_level)) ×
    upto_domain arr.(array_default) arr'.(array_default) ×
    upto_domain arr.(array_type) arr'.(array_type) ×
    All2 upto_domain arr.(array_value) arr'.(array_value).
Proof.
  intros e; depelim e.
  match goal with H : onPrims _ _ _ _ |- _ => depelim H end.
  eexists; split; [reflexivity|repeat split; assumption].
Qed.

(** ** Applications *)

Lemma upto_domain_mkApps f f' args args' :
  upto_domain f f' -> All2 upto_domain args args' ->
  upto_domain (mkApps f args) (mkApps f' args').
Proof.
  intros hf ha. induction ha in f, f', hf |- *; cbn; [assumption|].
  apply IHha. now constructor.
Qed.

Lemma upto_domain_mkApps_inv f args t' :
  upto_domain (mkApps f args) t' ->
  ∑ f' args', (t' = mkApps f' args') × upto_domain f f' × All2 upto_domain args args'.
Proof.
  induction args as [|a args IH] in f, t' |- *; cbn; intros e.
  - exists t', []. split; [reflexivity|split; [assumption|constructor]].
  - destruct (IH _ _ e) as (f'' & args' & -> & ef & ea).
    destruct (upto_domain_tApp_inv _ _ _ ef) as (f' & a' & -> & ef' & ea').
    exists f', (a' :: args'). split; [reflexivity|split; [assumption|now constructor]].
Qed.

Lemma upto_domain_head_construct t t' l l' :
  upto_domain t t' ->
  (match fst (decompose_app_rec t l) with tConstruct _ _ _ => true | _ => false end) =
  (match fst (decompose_app_rec t' l') with tConstruct _ _ _ => true | _ => false end).
Proof.
  induction t in t', l, l' |- * using term_forall_list_ind; intros e; depelim e; cbn;
    try reflexivity.
  now apply IHt1.
Qed.

Lemma upto_domain_isConstruct_app t t' :
  upto_domain t t' -> isConstruct_app t = isConstruct_app t'.
Proof. intros e. unfold isConstruct_app, decompose_app. now apply upto_domain_head_construct. Qed.

Lemma is_constructor_upto n args args' :
  All2 upto_domain args args' -> is_constructor n args = is_constructor n args'.
Proof.
  intros h. unfold is_constructor.
  destruct (nth_error args n) as [a|] eqn:E.
  - destruct (All2_nth_error_Some _ _ h E) as [a' [-> ha]].
    now apply upto_domain_isConstruct_app.
  - now rewrite (All2_nth_error_None _ h E).
Qed.

(** ** Fixpoints *)

Lemma upto_domain_fix_subst mfix mfix' :
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) ×
                   x.(rarg) = y.(rarg)) mfix mfix' ->
  All2 upto_domain (fix_subst mfix) (fix_subst mfix').
Proof.
  intros h. unfold fix_subst. rewrite -(All2_length h).
  generalize #|mfix| as n. induction n; cbn; constructor; [now constructor|exact IHn].
Qed.

Lemma upto_domain_cofix_subst mfix mfix' :
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) ×
                   x.(rarg) = y.(rarg)) mfix mfix' ->
  All2 upto_domain (cofix_subst mfix) (cofix_subst mfix').
Proof.
  intros h. unfold cofix_subst. rewrite -(All2_length h).
  generalize #|mfix| as n. induction n; cbn; constructor; [now constructor|exact IHn].
Qed.

Lemma upto_domain_unfold_fix mfix mfix' idx narg fn :
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) ×
                   x.(rarg) = y.(rarg)) mfix mfix' ->
  unfold_fix mfix idx = Some (narg, fn) ->
  ∑ fn', unfold_fix mfix' idx = Some (narg, fn') × upto_domain fn fn'.
Proof.
  intros h. unfold unfold_fix.
  destruct (nth_error mfix idx) as [d|] eqn:E; [|discriminate].
  intros [= <- <-].
  destruct (All2_nth_error_Some _ _ h E) as [d' [-> (_ & hb & hr)]].
  exists (subst0 (fix_subst mfix') (dbody d')). split; [now rewrite hr|].
  apply upto_domain_subst; [now apply upto_domain_fix_subst|exact hb].
Qed.

Lemma upto_domain_unfold_cofix mfix mfix' idx narg fn :
  All2 (fun x y => upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) ×
                   x.(rarg) = y.(rarg)) mfix mfix' ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ fn', unfold_cofix mfix' idx = Some (narg, fn') × upto_domain fn fn'.
Proof.
  intros h. unfold unfold_cofix.
  destruct (nth_error mfix idx) as [d|] eqn:E; [|discriminate].
  intros [= <- <-].
  destruct (All2_nth_error_Some _ _ h E) as [d' [-> (_ & hb & hr)]].
  exists (subst0 (cofix_subst mfix') (dbody d')). split; [now rewrite hr|].
  apply upto_domain_subst; [now apply upto_domain_cofix_subst|exact hb].
Qed.

(** ** Contexts related on their bodies *)

Definition upto_domain_bodies : context -> context -> Type :=
  All2 (fun d d' => rel_option upto_domain (decl_body d) (decl_body d')).

Lemma upto_domain_bodies_refl Γ : upto_domain_bodies Γ Γ.
Proof.
  induction Γ as [|d Γ IH]; constructor; [|exact IH].
  destruct (decl_body d); constructor. reflexivity.
Qed.

Lemma upto_domain_bodies_vass Γ Γ' na na' ty ty' :
  upto_domain_bodies Γ Γ' -> upto_domain_bodies (Γ ,, vass na ty) (Γ' ,, vass na' ty').
Proof. intros h. constructor; [constructor|exact h]. Qed.

Lemma upto_domain_bodies_vdef Γ Γ' na na' b b' ty ty' :
  upto_domain b b' -> upto_domain_bodies Γ Γ' ->
  upto_domain_bodies (Γ ,, vdef na b ty) (Γ' ,, vdef na' b' ty').
Proof. intros hb h. constructor; [now constructor|exact h]. Qed.

Lemma upto_domain_bodies_app Γ Γ' Δ Δ' :
  upto_domain_bodies Δ Δ' -> upto_domain_bodies Γ Γ' ->
  upto_domain_bodies (Γ ,,, Δ) (Γ' ,,, Δ').
Proof. intros hΔ hΓ. now apply All2_app. Qed.

Lemma upto_domain_bodies_nth Γ Γ' i body :
  upto_domain_bodies Γ Γ' ->
  option_map decl_body (nth_error Γ i) = Some (Some body) ->
  ∑ body', option_map decl_body (nth_error Γ' i) = Some (Some body') × upto_domain body body'.
Proof.
  intros h. destruct (nth_error Γ i) as [d|] eqn:E; cbn; [|discriminate].
  intros [= hb].
  destruct (All2_nth_error_Some _ _ h E) as [d' [-> hd]]. cbn.
  rewrite hb in hd. revert hd. destruct (decl_body d') as [b'|]; intros hd; depelim hd.
  exists b'. split; [reflexivity|assumption].
Qed.

Lemma upto_domain_bodies_assumptions Γ Γ' :
  upto_domain_bodies Γ Γ' -> context_assumptions Γ = context_assumptions Γ'.
Proof.
  induction 1 as [|x y l l' r h IH]; cbn; [reflexivity|].
  revert r. destruct (decl_body x), (decl_body y); intros r; depelim r; cbn; congruence.
Qed.

Lemma upto_domain_extended_subst Γ Γ' n :
  upto_domain_bodies Γ Γ' -> All2 upto_domain (extended_subst Γ n) (extended_subst Γ' n).
Proof.
  intros h. induction h as [|x y l l' r h IH] in n |- *; cbn; [constructor|].
  revert r. destruct (decl_body x) as [b|], (decl_body y) as [b'|]; intros r; depelim r; cbn.
  - constructor; [|apply IH].
    rewrite (upto_domain_bodies_assumptions _ _ h) !extended_subst_length (All2_length h).
    apply upto_domain_subst; [apply IH|now apply upto_domain_lift].
  - constructor; [constructor|apply IH].
Qed.

Lemma upto_domain_expand_lets Γ Γ' t t' :
  upto_domain_bodies Γ Γ' -> upto_domain t t' ->
  upto_domain (expand_lets Γ t) (expand_lets Γ' t').
Proof.
  intros h e. unfold expand_lets, expand_lets_k.
  rewrite (upto_domain_bodies_assumptions _ _ h) (All2_length h).
  apply upto_domain_subst; [now apply upto_domain_extended_subst|now apply upto_domain_lift].
Qed.

Lemma upto_domain_bodies_subst_context s s' k Γ Γ' :
  All2 upto_domain s s' -> upto_domain_bodies Γ Γ' ->
  upto_domain_bodies (subst_context s k Γ) (subst_context s' k Γ').
Proof.
  intros hs h. induction h as [|x y l l' r h IH]; [constructor|].
  rewrite !subst_context_snoc. constructor; [|exact IH].
  rewrite (All2_length h). cbn.
  revert r. destruct (decl_body x), (decl_body y); intros r; depelim r; cbn; constructor.
  now apply upto_domain_subst.
Qed.

Lemma upto_domain_bodies_subst_instance u Γ Γ' :
  eq_context_upto_names Γ Γ' -> upto_domain_bodies (subst_instance u Γ) (subst_instance u Γ').
Proof.
  induction 1 as [|x y l l' r h IH]; [constructor|].
  cbn. constructor; [|exact IH].
  destruct r; cbn; constructor. reflexivity.
Qed.

Lemma upto_domain_bodies_inst_case_context params params' u ctx ctx' :
  All2 upto_domain params params' -> eq_context_upto_names ctx ctx' ->
  upto_domain_bodies (inst_case_context params u ctx) (inst_case_context params' u ctx').
Proof.
  intros hp hc. unfold inst_case_context.
  apply upto_domain_bodies_subst_context; [now apply All2_rev|].
  now apply upto_domain_bodies_subst_instance.
Qed.

Lemma upto_domain_bodies_mapi_vass {A B} (P : A -> B -> Type)
  (f : nat -> A -> context_decl) (g : nat -> B -> context_decl) l l' n :
  All2 P l l' -> (forall i x, decl_body (f i x) = None) -> (forall i y, decl_body (g i y) = None) ->
  upto_domain_bodies (mapi_rec f l n) (mapi_rec g l' n).
Proof.
  intros h hf hg. induction h in n |- *; cbn; constructor; [|apply IHh].
  rewrite hf hg. constructor.
Qed.

Lemma upto_domain_bodies_fix_context {P} (mfix mfix' : mfixpoint term) :
  All2 P mfix mfix' -> upto_domain_bodies (fix_context mfix) (fix_context mfix').
Proof.
  intros h. unfold fix_context, mapi. apply All2_rev.
  eapply upto_domain_bodies_mapi_vass; [exact h|intros; reflexivity|intros; reflexivity].
Qed.

Lemma upto_domain_ctx_bodies Γ Γ' : upto_domain_ctx Γ Γ' -> upto_domain_bodies Γ Γ'.
Proof.
  induction 1; constructor; [|assumption].
  match goal with H : upto_domain_decl _ _ |- _ => destruct H end; cbn; constructor.
  assumption.
Qed.

(** ** C1a *)

Lemma red1_upto_domain_bodies {Σ Γ t u} : red1 Σ Γ t u ->
  forall Γ' t', upto_domain_bodies Γ Γ' -> upto_domain t t' ->
  ∑ u', clos_refl (red1 Σ Γ') t' u' × upto_domain u u'.
Proof.
  revert Γ t u.
  apply (red1_ind_all Σ (fun Γ t u => forall Γ' t', upto_domain_bodies Γ Γ' -> upto_domain t t' ->
            ∑ u', clos_refl (red1 Σ Γ') t' u' × upto_domain u u')).
  - (* red_beta *)
    intros Γ na ty b a Γ' t' hΓ e.
    destruct (upto_domain_tApp_inv _ _ _ e) as (f' & a' & -> & ef & ea).
    destruct (upto_domain_tLambda_inv _ _ _ _ ef) as (na' & ty' & b' & -> & eb).
    exists (b' {0 := a'}). split; [apply r_step; apply red_beta|].
    unfold subst1. apply upto_domain_subst; [constructor; [exact ea|constructor]|exact eb].
  - (* red_zeta *)
    intros Γ na b ty c Γ' t' hΓ e.
    destruct (upto_domain_tLetIn_inv _ _ _ _ _ e) as (na' & b' & ty' & c' & -> & eb & ety & ec).
    exists (c' {0 := b'}). split; [apply r_step; apply red_zeta|].
    unfold subst1. apply upto_domain_subst; [constructor; [exact eb|constructor]|exact ec].
  - (* red_rel *)
    intros Γ i body hb Γ' t' hΓ e.
    apply upto_domain_tRel_inv in e; subst t'.
    destruct (upto_domain_bodies_nth _ _ _ _ hΓ hb) as (body' & hb' & eb).
    exists (lift0 (S i) body'). split; [apply r_step; now apply red_rel|].
    now apply upto_domain_lift.
  - (* red_iota *)
    intros Γ ci c u args p brs br hnth hlen Γ' t' hΓ e.
    destruct (upto_domain_tCase_inv _ _ _ _ _ e)
      as (p' & c' & brs' & -> & hpar & hinst & hctx & hret & hc & hbrs).
    destruct (upto_domain_mkApps_inv _ _ _ hc) as (f' & args' & -> & ef & eargs).
    apply upto_domain_tConstruct_inv in ef; subst f'.
    destruct (All2_nth_error_Some _ _ hbrs hnth) as [br' [hnth' [hbctx hbody]]].
    exists (iota_red ci.(ci_npar) p' args' br'). split.
    + apply r_step. apply red_iota; [exact hnth'|].
      rewrite -(All2_length eargs) hlen. f_equal.
      now apply eq_context_upto_names_assumptions.
    + unfold iota_red. apply upto_domain_subst.
      * now apply All2_rev, All2_skipn.
      * apply upto_domain_expand_lets; [|exact hbody].
        unfold inst_case_branch_context. rewrite -hinst.
        now apply upto_domain_bodies_inst_case_context.
  - (* red_fix *)
    intros Γ mfix idx args narg fn hunf hisc Γ' t' hΓ e.
    destruct (upto_domain_mkApps_inv _ _ _ e) as (f' & args' & -> & ef & eargs).
    destruct (upto_domain_tFix_inv _ _ _ ef) as (mfix' & -> & hm).
    destruct (upto_domain_unfold_fix _ _ _ _ _ hm hunf) as (fn' & hunf' & efn).
    exists (mkApps fn' args'). split.
    + apply r_step. eapply red_fix; [exact hunf'|].
      now rewrite -(is_constructor_upto narg _ _ eargs).
    + now apply upto_domain_mkApps.
  - (* red_cofix_case *)
    intros Γ ci p mfix idx args narg fn brs hunf Γ' t' hΓ e.
    destruct (upto_domain_tCase_inv _ _ _ _ _ e)
      as (p' & c' & brs' & -> & hpar & hinst & hctx & hret & hc & hbrs).
    destruct (upto_domain_mkApps_inv _ _ _ hc) as (f' & args' & -> & ef & eargs).
    destruct (upto_domain_tCoFix_inv _ _ _ ef) as (mfix' & -> & hm).
    destruct (upto_domain_unfold_cofix _ _ _ _ _ hm hunf) as (fn' & hunf' & efn).
    exists (tCase ci p' (mkApps fn' args') brs'). split.
    + apply r_step. eapply red_cofix_case; exact hunf'.
    + constructor; try assumption. now apply upto_domain_mkApps.
  - (* red_cofix_proj *)
    intros Γ pr mfix idx args narg fn hunf Γ' t' hΓ e.
    destruct (upto_domain_tProj_inv _ _ _ e) as (c' & -> & hc).
    destruct (upto_domain_mkApps_inv _ _ _ hc) as (f' & args' & -> & ef & eargs).
    destruct (upto_domain_tCoFix_inv _ _ _ ef) as (mfix' & -> & hm).
    destruct (upto_domain_unfold_cofix _ _ _ _ _ hm hunf) as (fn' & hunf' & efn).
    exists (tProj pr (mkApps fn' args')). split.
    + apply r_step. eapply red_cofix_proj; exact hunf'.
    + constructor. now apply upto_domain_mkApps.
  - (* red_delta *)
    intros Γ c decl body hdecl u hbody Γ' t' hΓ e.
    apply upto_domain_tConst_inv in e; subst t'.
    exists (subst_instance u body).
    split; [apply r_step; eapply red_delta; eassumption|reflexivity].
  - (* red_proj *)
    intros Γ pr args u arg hnth Γ' t' hΓ e.
    destruct (upto_domain_tProj_inv _ _ _ e) as (c' & -> & hc).
    destruct (upto_domain_mkApps_inv _ _ _ hc) as (f' & args' & -> & ef & eargs).
    apply upto_domain_tConstruct_inv in ef; subst f'.
    destruct (All2_nth_error_Some _ _ eargs hnth) as [arg' [hnth' harg]].
    exists arg'. split; [apply r_step; apply red_proj; exact hnth'|exact harg].
  - (* abs_red_l: a step inside the λ DOMAIN, which upto_domain ignores *)
    intros Γ na M M' N _ _ Γ' t' hΓ e.
    destruct (upto_domain_tLambda_inv _ _ _ _ e) as (na' & ty' & b' & -> & eb).
    exists (tLambda na' ty' b'). split; [apply r_refl|now constructor].
  - (* abs_red_r: under the binder, the two domains are unrelated *)
    intros Γ na M M' N _ IH Γ' t' hΓ e.
    destruct (upto_domain_tLambda_inv _ _ _ _ e) as (na' & ty' & b' & -> & eb).
    destruct (IH (Γ' ,, vass na' ty') b' (upto_domain_bodies_vass _ _ _ _ _ _ hΓ) eb)
      as (r' & hr & er).
    exists (tLambda na' ty' r'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply abs_red_r|apply r_refl].
  - (* letin_red_def *)
    intros Γ na b ty c r _ IH Γ' t' hΓ e.
    destruct (upto_domain_tLetIn_inv _ _ _ _ _ e) as (na' & b' & ty' & c' & -> & eb & ety & ec).
    destruct (IH Γ' b' hΓ eb) as (r' & hr & er).
    exists (tLetIn na' r' ty' c'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply letin_red_def|apply r_refl].
  - (* letin_red_ty *)
    intros Γ na b ty c r _ IH Γ' t' hΓ e.
    destruct (upto_domain_tLetIn_inv _ _ _ _ _ e) as (na' & b' & ty' & c' & -> & eb & ety & ec).
    destruct (IH Γ' ty' hΓ ety) as (r' & hr & er).
    exists (tLetIn na' b' r' c'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply letin_red_ty|apply r_refl].
  - (* letin_red_body *)
    intros Γ na b ty c r _ IH Γ' t' hΓ e.
    destruct (upto_domain_tLetIn_inv _ _ _ _ _ e) as (na' & b' & ty' & c' & -> & eb & ety & ec).
    destruct (IH (Γ' ,, vdef na' b' ty') c' (upto_domain_bodies_vdef _ _ _ _ _ _ _ _ eb hΓ) ec)
      as (r' & hr & er).
    exists (tLetIn na' b' ty' r'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply letin_red_body|apply r_refl].
  - (* case_red_param *)
    intros Γ ci p params' c brs hon Γ' t' hΓ e.
    destruct (upto_domain_tCase_inv _ _ _ _ _ e)
      as (p' & c' & brs' & -> & hpar & hinst & hctx & hret & hc & hbrs).
    destruct (OnOne2_All2_sim upto_domain _ (red1 Σ Γ') _ _ _ hon hpar) as (l1' & hl & el).
    { intros x y x' [_ IH] ex. exact (IH Γ' x' hΓ ex). }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tCase ci (set_pparams p' l2) c' brs').
      split; [apply r_step; now apply case_red_param|].
      constructor; cbn; assumption.
    + exists (tCase ci p' c' brs'). split; [apply r_refl|]. constructor; cbn; assumption.
  - (* case_red_return *)
    intros Γ ci p preturn' c brs _ IH Γ' t' hΓ e.
    destruct (upto_domain_tCase_inv _ _ _ _ _ e)
      as (p' & c' & brs' & -> & hpar & hinst & hctx & hret & hc & hbrs).
    assert (hΓ2 : upto_domain_bodies (Γ ,,, inst_case_predicate_context p)
                                     (Γ' ,,, inst_case_predicate_context p')).
    { apply upto_domain_bodies_app; [|exact hΓ].
      unfold inst_case_predicate_context. rewrite -hinst.
      now apply upto_domain_bodies_inst_case_context. }
    destruct (IH _ _ hΓ2 hret) as (r' & hr & er).
    revert er. destruct hr as [r'' hr|]; intros er.
    + exists (tCase ci (set_preturn p' r'') c' brs').
      split; [apply r_step; now apply case_red_return|].
      constructor; cbn; assumption.
    + exists (tCase ci p' c' brs'). split; [apply r_refl|]. constructor; cbn; assumption.
  - (* case_red_discr *)
    intros Γ ci p c c1 brs _ IH Γ' t' hΓ e.
    destruct (upto_domain_tCase_inv _ _ _ _ _ e)
      as (p' & c' & brs' & -> & hpar & hinst & hctx & hret & hc & hbrs).
    destruct (IH Γ' c' hΓ hc) as (r' & hr & er).
    exists (tCase ci p' r' brs'). split; [|constructor; assumption].
    destruct hr as [? hr|]; [apply r_step; now apply case_red_discr|apply r_refl].
  - (* case_red_brs *)
    intros Γ ci p c brs brs1 hon Γ' t' hΓ e.
    destruct (upto_domain_tCase_inv _ _ _ _ _ e)
      as (p' & c' & brs' & -> & hpar & hinst & hctx & hret & hc & hbrs).
    destruct (OnOne2_All2_sim
      (fun x y => eq_context_upto_names x.(bcontext) y.(bcontext) × upto_domain x.(bbody) y.(bbody))
      _ (fun x' y' => on_Trel_eq (red1 Σ (Γ' ,,, inst_case_branch_context p' x')) bbody bcontext x' y')
      _ _ _ hon hbrs) as (l1' & hl & el).
    { intros x y x' [[_ IH] hceq] [hxc hxb].
      assert (hΓx : upto_domain_bodies (Γ ,,, inst_case_branch_context p x)
                                       (Γ' ,,, inst_case_branch_context p' x')).
      { apply upto_domain_bodies_app; [|exact hΓ].
        unfold inst_case_branch_context. rewrite -hinst.
        now apply upto_domain_bodies_inst_case_context. }
      destruct (IH _ _ hΓx hxb) as (b'' & hb & eb).
      revert eb. destruct hb as [b3 hb|]; intros eb.
      - exists {| bcontext := bcontext x'; bbody := b3 |}.
        split; [apply r_step; split; [exact hb|reflexivity]|].
        split; cbn; [rewrite -hceq; exact hxc|exact eb].
      - exists x'. split; [apply r_refl|]. split; [rewrite -hceq; exact hxc|exact eb]. }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tCase ci p' c' l2). split; [apply r_step; now apply case_red_brs|].
      constructor; assumption.
    + exists (tCase ci p' c' brs'). split; [apply r_refl|]. constructor; assumption.
  - (* proj_red *)
    intros Γ pr c c1 _ IH Γ' t' hΓ e.
    destruct (upto_domain_tProj_inv _ _ _ e) as (c' & -> & hc).
    destruct (IH Γ' c' hΓ hc) as (r' & hr & er).
    exists (tProj pr r'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply proj_red|apply r_refl].
  - (* app_red_l *)
    intros Γ M1 N1 M2 _ IH Γ' t' hΓ e.
    destruct (upto_domain_tApp_inv _ _ _ e) as (f' & a' & -> & ef & ea).
    destruct (IH Γ' f' hΓ ef) as (r' & hr & er).
    exists (tApp r' a'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply app_red_l|apply r_refl].
  - (* app_red_r *)
    intros Γ M2 N2 M1 _ IH Γ' t' hΓ e.
    destruct (upto_domain_tApp_inv _ _ _ e) as (f' & a' & -> & ef & ea).
    destruct (IH Γ' a' hΓ ea) as (r' & hr & er).
    exists (tApp f' r'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply app_red_r|apply r_refl].
  - (* prod_red_l *)
    intros Γ na M1 M2 N1 _ IH Γ' t' hΓ e.
    destruct (upto_domain_tProd_inv _ _ _ _ e) as (na' & a' & b' & -> & ea & eb).
    destruct (IH Γ' a' hΓ ea) as (r' & hr & er).
    exists (tProd na' r' b'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply prod_red_l|apply r_refl].
  - (* prod_red_r *)
    intros Γ na M2 N2 M1 _ IH Γ' t' hΓ e.
    destruct (upto_domain_tProd_inv _ _ _ _ e) as (na' & a' & b' & -> & ea & eb).
    destruct (IH (Γ' ,, vass na' a') b' (upto_domain_bodies_vass _ _ _ _ _ _ hΓ) eb)
      as (r' & hr & er).
    exists (tProd na' a' r'). split; [|now constructor].
    destruct hr as [? hr|]; [apply r_step; now apply prod_red_r|apply r_refl].
  - (* evar_red *)
    intros Γ ev l l1 hon Γ' t' hΓ e.
    destruct (upto_domain_tEvar_inv _ _ _ e) as (l' & -> & hl').
    destruct (OnOne2_All2_sim upto_domain _ (red1 Σ Γ') _ _ _ hon hl') as (l1' & hl & el).
    { intros x y x' [_ IH] ex. exact (IH Γ' x' hΓ ex). }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tEvar ev l2). split; [apply r_step; now apply evar_red|now constructor].
    + exists (tEvar ev l'). split; [apply r_refl|now constructor].
  - (* fix_red_ty *)
    intros Γ mfix0 mfix1 idx hon Γ' t' hΓ e.
    destruct (upto_domain_tFix_inv _ _ _ e) as (mfix' & -> & hm).
    destruct (OnOne2_All2_sim _ _
      (on_Trel_eq (red1 Σ Γ') dtype (fun x => (dname x, dbody x, rarg x))) _ _ _ hon hm)
      as (l1' & hl & el).
    { intros x y x' [[_ IH] heq] (hty & hbo & hra).
      assert (hb : dbody y = dbody x) by congruence.
      assert (hr : rarg y = rarg x) by congruence.
      destruct (IH Γ' (dtype x') hΓ hty) as (ty'' & hr' & ety).
      revert ety. destruct hr' as [ty3 hr'|]; intros ety.
      - exists {| dname := dname x'; dtype := ty3; dbody := dbody x'; rarg := rarg x' |}.
        split; [apply r_step; split; [exact hr'|reflexivity]|].
        cbn. split; [exact ety|split; [rewrite hb; exact hbo|rewrite hr; exact hra]].
      - exists x'. split; [apply r_refl|].
        split; [exact ety|split; [rewrite hb; exact hbo|rewrite hr; exact hra]]. }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tFix l2 idx). split; [apply r_step; now apply fix_red_ty|now constructor].
    + exists (tFix mfix' idx). split; [apply r_refl|now constructor].
  - (* fix_red_body *)
    intros Γ mfix0 mfix1 idx hon Γ' t' hΓ e.
    destruct (upto_domain_tFix_inv _ _ _ e) as (mfix' & -> & hm).
    assert (hΓ2 : upto_domain_bodies (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix')).
    { apply upto_domain_bodies_app; [|exact hΓ]. now eapply upto_domain_bodies_fix_context. }
    destruct (OnOne2_All2_sim _ _
      (on_Trel_eq (red1 Σ (Γ' ,,, fix_context mfix')) dbody (fun x => (dname x, dtype x, rarg x)))
      _ _ _ hon hm) as (l1' & hl & el).
    { intros x y x' [[_ IH] heq] (hty & hbo & hra).
      assert (ht : dtype y = dtype x) by congruence.
      assert (hr : rarg y = rarg x) by congruence.
      destruct (IH _ (dbody x') hΓ2 hbo) as (bo'' & hr' & ebo).
      revert ebo. destruct hr' as [bo3 hr'|]; intros ebo.
      - exists {| dname := dname x'; dtype := dtype x'; dbody := bo3; rarg := rarg x' |}.
        split; [apply r_step; split; [exact hr'|reflexivity]|].
        cbn. split; [rewrite ht; exact hty|split; [exact ebo|rewrite hr; exact hra]].
      - exists x'. split; [apply r_refl|].
        split; [rewrite ht; exact hty|split; [exact ebo|rewrite hr; exact hra]]. }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tFix l2 idx). split; [apply r_step; now apply fix_red_body|now constructor].
    + exists (tFix mfix' idx). split; [apply r_refl|now constructor].
  - (* cofix_red_ty *)
    intros Γ mfix0 mfix1 idx hon Γ' t' hΓ e.
    destruct (upto_domain_tCoFix_inv _ _ _ e) as (mfix' & -> & hm).
    destruct (OnOne2_All2_sim _ _
      (on_Trel_eq (red1 Σ Γ') dtype (fun x => (dname x, dbody x, rarg x))) _ _ _ hon hm)
      as (l1' & hl & el).
    { intros x y x' [[_ IH] heq] (hty & hbo & hra).
      assert (hb : dbody y = dbody x) by congruence.
      assert (hr : rarg y = rarg x) by congruence.
      destruct (IH Γ' (dtype x') hΓ hty) as (ty'' & hr' & ety).
      revert ety. destruct hr' as [ty3 hr'|]; intros ety.
      - exists {| dname := dname x'; dtype := ty3; dbody := dbody x'; rarg := rarg x' |}.
        split; [apply r_step; split; [exact hr'|reflexivity]|].
        cbn. split; [exact ety|split; [rewrite hb; exact hbo|rewrite hr; exact hra]].
      - exists x'. split; [apply r_refl|].
        split; [exact ety|split; [rewrite hb; exact hbo|rewrite hr; exact hra]]. }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tCoFix l2 idx). split; [apply r_step; now apply cofix_red_ty|now constructor].
    + exists (tCoFix mfix' idx). split; [apply r_refl|now constructor].
  - (* cofix_red_body *)
    intros Γ mfix0 mfix1 idx hon Γ' t' hΓ e.
    destruct (upto_domain_tCoFix_inv _ _ _ e) as (mfix' & -> & hm).
    assert (hΓ2 : upto_domain_bodies (Γ ,,, fix_context mfix0) (Γ' ,,, fix_context mfix')).
    { apply upto_domain_bodies_app; [|exact hΓ]. now eapply upto_domain_bodies_fix_context. }
    destruct (OnOne2_All2_sim _ _
      (on_Trel_eq (red1 Σ (Γ' ,,, fix_context mfix')) dbody (fun x => (dname x, dtype x, rarg x)))
      _ _ _ hon hm) as (l1' & hl & el).
    { intros x y x' [[_ IH] heq] (hty & hbo & hra).
      assert (ht : dtype y = dtype x) by congruence.
      assert (hr : rarg y = rarg x) by congruence.
      destruct (IH _ (dbody x') hΓ2 hbo) as (bo'' & hr' & ebo).
      revert ebo. destruct hr' as [bo3 hr'|]; intros ebo.
      - exists {| dname := dname x'; dtype := dtype x'; dbody := bo3; rarg := rarg x' |}.
        split; [apply r_step; split; [exact hr'|reflexivity]|].
        cbn. split; [rewrite ht; exact hty|split; [exact ebo|rewrite hr; exact hra]].
      - exists x'. split; [apply r_refl|].
        split; [rewrite ht; exact hty|split; [exact ebo|rewrite hr; exact hra]]. }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tCoFix l2 idx). split; [apply r_step; now apply cofix_red_body|now constructor].
    + exists (tCoFix mfix' idx). split; [apply r_refl|now constructor].
  - (* array_red_val *)
    intros Γ arr value hon Γ' t' hΓ e.
    destruct (upto_domain_tPrim_array_inv _ _ e)
      as (arr' & -> & hlev & hdef & hty & hval).
    destruct (OnOne2_All2_sim upto_domain _ (red1 Σ Γ') _ _ _ hon hval) as (l1' & hl & el).
    { intros x y x' [_ IH] ex. exact (IH Γ' x' hΓ ex). }
    revert el. destruct hl as [l2 hl|]; intros el.
    + exists (tPrim (primArray; primArrayModel (set_array_value arr' l2))).
      split; [apply r_step; now apply array_red_val|].
      constructor; constructor; assumption.
    + exists (tPrim (primArray; primArrayModel arr')). split; [apply r_refl|].
      constructor; constructor; assumption.
  - (* array_red_def *)
    intros Γ arr d _ IH Γ' t' hΓ e.
    destruct (upto_domain_tPrim_array_inv _ _ e)
      as (arr' & -> & hlev & hdef & hty & hval).
    destruct (IH Γ' _ hΓ hdef) as (r' & hr & er).
    revert er. destruct hr as [r'' hr|]; intros er.
    + exists (tPrim (primArray; primArrayModel (set_array_default arr' r''))).
      split; [apply r_step; now apply array_red_def|].
      constructor; constructor; assumption.
    + exists (tPrim (primArray; primArrayModel arr')). split; [apply r_refl|].
      constructor; constructor; assumption.
  - (* array_red_type *)
    intros Γ arr ty _ IH Γ' t' hΓ e.
    destruct (upto_domain_tPrim_array_inv _ _ e)
      as (arr' & -> & hlev & hdef & hty & hval).
    destruct (IH Γ' _ hΓ hty) as (r' & hr & er).
    revert er. destruct hr as [r'' hr|]; intros er.
    + exists (tPrim (primArray; primArrayModel (set_array_type arr' r''))).
      split; [apply r_step; now apply array_red_type|].
      constructor; constructor; assumption.
    + exists (tPrim (primArray; primArrayModel arr')). split; [apply r_refl|].
      constructor; constructor; assumption.
Qed.

(** The plan's general form (row C1a), over [upto_domain_ctx]. *)
Theorem red1_upto_domain_ctx {Σ Γ Γ' t t' u} :
  upto_domain_ctx Γ Γ' -> upto_domain t t' -> red1 Σ Γ t u ->
  ∑ u', clos_refl (red1 Σ Γ') t' u' × upto_domain u u'.
Proof.
  intros hΓ e r. exact (red1_upto_domain_bodies r Γ' t' (upto_domain_ctx_bodies _ _ hΓ) e).
Qed.

(** The pinned statement: C1a at a fixed context, as [HR_A_instantiable] consumes it. *)
Theorem C1a_fixed : C1a_fixed_statement.
Proof.
  intros Σ Γ t t' u e r. exact (red1_upto_domain_bodies r Γ t' (upto_domain_bodies_refl Γ) e).
Qed.
