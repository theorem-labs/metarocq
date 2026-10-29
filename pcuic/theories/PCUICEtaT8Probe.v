(* Distributed under the terms of the MIT license. *)

(** * T8 (typed postponement): pinned statements, route, and one-step η-postponement

  ** What T8 claims
  A well-typed type that is E-convertible to a head form (sort, product, applied
  inductive) reduces to that head form by base [red] alone. The pinned forms are
  the [Definition]s [T8_*_statement] below; none is proved here. Without typing the
  claim is false ([A6_F_raw_false]; and [tProj p (λx. C ps X x)] η-reduces then
  projects, while it is β-stuck).

  ** Route
  1. A6 already gives, untyped, that the canonical form [canon T] reaches the head by
     [(R_c ∪ eta1)*] ([ws_cumul_pbE_Sort_r_inv], [ws_cumul_pbE_Prod_r_inv],
     [ws_cumul_pbE_Ind_r_inv]).
  2. Postpone η in that chain: [(R_c ∪ eta1)* ⊆ R_c* · eta1*] on the canonical forms of
     the reducts of a typed [T]. The relation η is postponed over is base [red1] on
     the actual term (lemma [eta_postpone1] below); the [R_c] form follows from it by
     [red1_R_c] and [eta1_star_canon], because [canon] keeps every λ, every scrutinee
     position and every fixpoint [rarg].
  3. Lift [R_c*] from [canon T] back to [red] on [T] (backward simulation of [red1]
     through [canon]: a reduction of [canon T] is the canonical image of a reduction
     of [T], because [canon_dom] is a normal sort and every redex of [canon T] is the
     image of a redex of [T]).
  4. The end of the η* tail is the head form; its source [canon T'] is not a λ,
     because [T'] (a reduct of [T]) is typed by subject reduction at a sort, and a
     λ has a product type ([ws_cumul_pbE_Prod_Sort_inv], [invert_cumul_prod_indE]).
     A non-λ term η-reduces only inside, keeping its head, so [canon T'] is already
     the head form.

  ** The invariant ([eta_safe], syntactic, closed under subterms)
  η creates a redex in exactly four places: a λ as the scrutinee of [tCase] (ι and
  cofix-case), as the argument of [tProj] (projection and cofix-proj), as the
  [rarg]-th argument of an applied fixpoint, and as an argument of an applied
  primitive operation. [eta_safe Σ t] says that no subterm of [t] has a λ there.
  Every other created redex (β with an η-expanded head, a spine whose head is an
  η-redex) is reached from [t] by extra β steps, so needs nothing.

  Typing gives the invariant (a λ has a product type, the four positions an
  inductive, primitive or, for a fixpoint, its [rarg] type, which [wf_fixpointE]
  makes inductive). The invariant is NOT preserved by β or by fixpoint unfolding as
  a syntactic property: [(λx. tCase x _) (λy. M y)] β-reduces to a λ scrutinee, and
  unfolding a fixpoint turns a recursive call [f (λy. C y)] into a fixpoint spine with
  a λ [rarg]. Both reducts come from ill-typed terms, so the invariant survives
  [red] on typed terms through E subject reduction (the forecast row T1), and only
  there. It is also not preserved by η: η at a spine head [(λx. F x) a] merges the
  spine into a fixpoint spine.

  ** Why the one-step lemma does not iterate by itself
  [eta_postpone1] commutes one η step past one [red1] step. Iterating it over
  [eta1* · red1] needs the invariant on η-reducts of a typed term, which subject
  reduction does not give (η-reducts need not be typed: [λx:A. f x] with [f : Π x:A'. B]
  and [A ≤ A'], [A ≠ A'], is typed at [Π x:A. B]; [f] is not, and in [g (λx:A. f x)]
  with [g : (Π x:A. B) → C] the η-reduct [g f] is ill-typed). The iteration needs the
  same lemma for a development-style parallel η ([pe], with the η rule
  [pe b ((lift0 1 M') (tRel 0)) → pe (λ. b) M'], which is closed under
  post-composition with [eta1], so [eta1* = pe]); its β-head case recurses on the
  [pe] derivation of the η-expanded head, which is structurally smaller. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Stdlib Require Import Lia.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICPrimitive
     PCUICLiftSubst PCUICCases PCUICOnFreeVars PCUICReduction PCUICPrimitiveRed
     PCUICTyping PCUICWellScopedCumulativity PCUICClosedBodies PCUICWeakeningConv
     PCUICEtaDefs PCUICEtaReduction PCUICEtaConfluence PCUICEtaFInst
     PCUICTypingEta PCUICWellScopedCumulativityEta PCUICConversionEtaCongr
     PCUICEtaC3BR.

Import ListNotations.

Set Default Goal Selector "!".

(** ** The pinned target statements (not proved here) *)

Section Statements.
  Context {cf : checker_flags}.

  Definition T8_Sort_r_statement (Σ : global_env_ext) : Type :=
    forall Γ pb T s s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ T (tSort s) ->
      ∑ s'', Σ ;;; Γ ⊢ T ⇝ tSort s'' × compare_sort Σ pb s'' s.

  Definition T8_Sort_l_statement (Σ : global_env_ext) : Type :=
    forall Γ pb T s s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ (tSort s) T ->
      ∑ s'', Σ ;;; Γ ⊢ T ⇝ tSort s'' × compare_sort Σ pb s s''.

  Definition T8_Prod_r_statement (Σ : global_env_ext) : Type :=
    forall Γ pb T na dom codom s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ T (tProd na dom codom) ->
      ∑ na' dom' codom',
        [× Σ ;;; Γ ⊢ T ⇝ tProd na' dom' codom', eq_binder_annot na' na,
           ws_cumul_pbE Conv Σ Γ dom' dom &
           ws_cumul_pbE pb Σ (Γ ,, vass na dom) codom' codom].

  Definition T8_Prod_l_statement (Σ : global_env_ext) : Type :=
    forall Γ pb T na dom codom s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ (tProd na dom codom) T ->
      ∑ na' dom' codom',
        [× Σ ;;; Γ ⊢ T ⇝ tProd na' dom' codom', eq_binder_annot na na',
           ws_cumul_pbE Conv Σ Γ dom dom' &
           ws_cumul_pbE pb Σ (Γ ,, vass na dom) codom codom'].

  Definition T8_Ind_r_statement (Σ : global_env_ext) : Type :=
    forall Γ pb T ind ui l s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ T (mkApps (tInd ind ui) l) ->
      ∑ ui' l',
        [× Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind ui') l',
           cmp_global_instance_finst Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| ui' ui &
           ws_cumul_pbE_terms Σ Γ l' l].

  Definition T8_Ind_l_statement (Σ : global_env_ext) : Type :=
    forall Γ pb T ind ui l s',
      wfE Σ -> Σ ;;; Γ |-E T : tSort s' ->
      ws_cumul_pbE pb Σ Γ (mkApps (tInd ind ui) l) T ->
      ∑ ui' l',
        [× Σ ;;; Γ ⊢ T ⇝ mkApps (tInd ind ui') l',
           cmp_global_instance_finst Σ.1 (compare_universe Σ) pb (IndRef ind) #|l| ui ui' &
           All2 (ws_cumul_pbE Conv Σ Γ) l l'].

End Statements.

(** ** The invariant *)

Definition notLam (t : term) : bool := ~~ isLambda t.

Definition spine_safe (Σ : global_env) (t : term) : bool :=
  match decompose_app t with
  | (tFix mfix idx, args) =>
      match unfold_fix mfix idx with
      | Some (narg, _) =>
          match nth_error args narg with Some a => notLam a | None => true end
      | None => true
      end
  | (tConst c _, args) =>
      match prim_op_of Σ c with Some _ => forallb notLam args | None => true end
  | _ => true
  end.

Fixpoint eta_safe (Σ : global_env) (t : term) : bool :=
  match t with
  | tEvar _ l => forallb (eta_safe Σ) l
  | tProd _ A B => eta_safe Σ A && eta_safe Σ B
  | tLambda _ A b => eta_safe Σ A && eta_safe Σ b
  | tLetIn _ b B c => eta_safe Σ b && eta_safe Σ B && eta_safe Σ c
  | tApp f a => spine_safe Σ t && eta_safe Σ f && eta_safe Σ a
  | tCase _ p c brs =>
      notLam c && eta_safe Σ c && forallb (eta_safe Σ) p.(pparams) && eta_safe Σ p.(preturn)
      && forallb (fun br => eta_safe Σ br.(bbody)) brs
  | tProj _ c => notLam c && eta_safe Σ c
  | tFix mfix _ => forallb (fun d => eta_safe Σ d.(dtype) && eta_safe Σ d.(dbody)) mfix
  | tCoFix mfix _ => forallb (fun d => eta_safe Σ d.(dtype) && eta_safe Σ d.(dbody)) mfix
  | tPrim p => test_prim (eta_safe Σ) p
  | _ => true
  end.

Lemma eta_safe_case_scrut Σ ci p c brs : eta_safe Σ (tCase ci p c brs) -> notLam c.
Proof. cbn. intros h. rtoProp. assumption. Qed.

Lemma eta_safe_proj_arg Σ pr c : eta_safe Σ (tProj pr c) -> notLam c.
Proof. cbn. intros h. rtoProp. assumption. Qed.

Lemma eta_safe_spine Σ h args :
  args <> [] -> eta_safe Σ (mkApps h args) -> spine_safe Σ (mkApps h args).
Proof.
  induction args as [|a l _] using MRList.rev_ind; [congruence|].
  intros _. rewrite mkApps_app. cbn [mkApps eta_safe]. intros hs. rtoProp. assumption.
Qed.

Lemma spine_safe_fix Σ mfix idx args narg fn a :
  unfold_fix mfix idx = Some (narg, fn) -> nth_error args narg = Some a ->
  spine_safe Σ (mkApps (tFix mfix idx) args) -> notLam a.
Proof.
  intros hu hn. unfold spine_safe. rewrite decompose_app_mkApps //. cbv beta iota.
  rewrite hu. cbv beta iota. rewrite hn. exact id.
Qed.

Lemma spine_safe_prim Σ c u args op :
  prim_op_of Σ c = Some op -> spine_safe Σ (mkApps (tConst c u) args) -> forallb notLam args.
Proof.
  intros hop. unfold spine_safe. rewrite decompose_app_mkApps //. cbv beta iota.
  rewrite hop. exact id.
Qed.

Lemma forallb_app_cons_mid {A} (f : A -> bool) pre a post : forallb f (pre ++ a :: post) -> f a.
Proof. rewrite forallb_app. move/andP => [_ /= /andP [h _]]. exact h. Qed.

(** ** One-step postponement: the conclusion *)

Definition PP (Σ : global_env) Γ t v := ∑ w, trans_clos (red1 Σ Γ) t w × eta w v.

(** ** Generic pieces *)

Lemma subst1_lift0 X a : (lift0 1 X) {0 := a} = X.
Proof. now apply simpl_subst_k. Qed.

Lemma red1_eta_head Σ Γ na A X a : red1 Σ Γ (tApp (eta_redex na A X) a) (tApp X a).
Proof.
  replace (tApp X a) with ((tApp (lift0 1 X) (tRel 0)) {0 := a}).
  - apply red_beta.
  - unfold subst1. cbn. rewrite simpl_subst_k //. now rewrite lift0_id.
Qed.

Lemma red1_eta_head_mkApps Σ Γ na A X a l :
  red1 Σ Γ (mkApps (eta_redex na A X) (a :: l)) (mkApps X (a :: l)).
Proof. cbn. apply red1_mkApps_f. apply red1_eta_head. Qed.

Lemma head_eta_split Σ Γ na A X l :
  (l = []) + red1 Σ Γ (mkApps (eta_redex na A X) l) (mkApps X l).
Proof. destruct l as [|a l]; [now left|right; apply red1_eta_head_mkApps]. Qed.

Section Generic.
  Context {cf : checker_flags} {Σ : global_env} (cb : ClosedBodies Σ).

  Lemma red1_lift1 Γ na A u v :
    on_free_vars xpredT u -> red1 Σ Γ u v -> red1 Σ (Γ ,, vass na A) (lift0 1 u) (lift0 1 v).
  Proof. intros hu h. exact (weakening_red1_cb Γ [] [vass na A] u v cb hu h). Qed.

  (** η at the root of [t], any [red1] step below it: CLOSED, one step each. *)
  Lemma pp_root Γ na A u v :
    on_free_vars xpredT (eta_redex na A u) -> red1 Σ Γ u v -> PP Σ Γ (eta_redex na A u) v.
  Proof.
    intros ho h. destruct (C3R.ofvT_eta_redex na A u ho) as [_ hu].
    exists (eta_redex na A v). split.
    - apply t_step. apply abs_red_r. apply app_red_l. now apply red1_lift1.
    - apply rt_step. apply eta_red.
  Qed.

  (** A spine whose head is an η-redex: β first. CLOSED. *)
  Lemma pp_head_eta Γ na A X l v :
    on_free_vars xpredT (mkApps (eta_redex na A X) l) ->
    red1 Σ Γ (mkApps X l) v -> PP Σ Γ (mkApps (eta_redex na A X) l) v.
  Proof.
    destruct l as [|a l]; intros ho hr.
    - cbn in ho, hr. now apply pp_root.
    - exists v. split; [|apply rt_refl].
      eapply t_trans; [apply t_step; apply red1_eta_head_mkApps|apply t_step; exact hr].
  Qed.

End Generic.

(** ** η inversion with an application spine as target *)

Lemma eta1_mkApps_tgt t h args : eta1 t (mkApps h args) ->
  (∑ h0, eta1 h0 h × t = mkApps h0 args) +
  (∑ args0, OnOne2 eta1 args0 args × t = mkApps h args0) +
  (∑ na A args1 args2, (args = args1 ++ args2) × t = mkApps (eta_redex na A (mkApps h args1)) args2).
Proof.
  revert t. induction args as [|a args IH] using MRList.rev_ind; intros t he.
  - left; left. exists t. split; [exact he|reflexivity].
  - rewrite mkApps_app in he. cbn in he. depelim he.
    + right. do 2 eexists. exists (args ++ [a]), []. split; [now rewrite app_nil_r|].
      now rewrite mkApps_app.
    + match goal with H : eta1 _ (mkApps h args) |- _ =>
        destruct (IH _ H) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & -> & ->)]
      end.
      * left; left. exists h0. split; [exact hh|]. now rewrite mkApps_app.
      * left; right. exists (args0 ++ [a]). split; [now apply OnOne2_app_r|now rewrite mkApps_app].
      * right. exists na, A, args1, (args2 ++ [a]). split; [now rewrite app_assoc|now rewrite mkApps_app].
    + match goal with H : eta1 ?x a |- _ =>
        left; right; exists (args ++ [x]); split;
          [apply OnOne2_app; now constructor|now rewrite mkApps_app]
      end.
Qed.

(** ** η vs. the (co)fixpoint bodies, read backwards through [peta] *)

Definition pdef (d d' : def term) : Type :=
  C3R.peta d.(dtype) d'.(dtype) × C3R.peta d.(dbody) d'.(dbody) × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg).

Lemma pdef_refl d : pdef d d.
Proof. repeat split; apply C3R.peta_refl. Qed.

Lemma mfix_ty_pdef mfix0 mfix :
  OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix0 mfix ->
  All2 pdef mfix0 mfix.
Proof.
  intros h. eapply C3R.OnOne2_All2_refl; [exact h|exact pdef_refl|].
  intros d d' [he e]. injection e as e1 e2 e3.
  repeat split; [now apply C3R.eta1_peta|rewrite e2; apply C3R.peta_refl|exact e1|exact e3].
Qed.

Lemma mfix_body_pdef mfix0 mfix :
  OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix0 mfix ->
  All2 pdef mfix0 mfix.
Proof.
  intros h. eapply C3R.OnOne2_All2_refl; [exact h|exact pdef_refl|].
  intros d d' [he e]. injection e as e1 e2 e3.
  repeat split; [rewrite e2; apply C3R.peta_refl|now apply C3R.eta1_peta|exact e1|exact e3].
Qed.

Lemma unfold_fix_back mfix0 mfix idx narg fn :
  All2 pdef mfix0 mfix -> unfold_fix mfix idx = Some (narg, fn) ->
  ∑ fn0, unfold_fix mfix0 idx = Some (narg, fn0) × C3R.peta fn0 fn.
Proof.
  intros ha. unfold unfold_fix.
  destruct (nth_error mfix idx) as [d|] eqn:hd; [|discriminate].
  intros [= <- <-].
  destruct (All2_nth_error_Some_r idx d ha hd) as (d0 & hd0 & (_ & hb & _ & hr)).
  rewrite hd0. eexists; split; [now rewrite hr|].
  apply (C3R.peta_subst _ _ hb). now apply C3R.peta_fix_subst.
Qed.

Lemma unfold_cofix_back mfix0 mfix idx narg fn :
  All2 pdef mfix0 mfix -> unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ fn0, unfold_cofix mfix0 idx = Some (narg, fn0) × C3R.peta fn0 fn.
Proof.
  intros ha. unfold unfold_cofix.
  destruct (nth_error mfix idx) as [d|] eqn:hd; [|discriminate].
  intros [= <- <-].
  destruct (All2_nth_error_Some_r idx d ha hd) as (d0 & hd0 & (_ & hb & _ & hr)).
  rewrite hd0. eexists; split; [now rewrite hr|].
  apply (C3R.peta_subst _ _ hb). now apply C3R.peta_cofix_subst.
Qed.

Lemma OnOne2_eta1_peta l l' : OnOne2 eta1 l l' -> All2 C3R.peta l l'.
Proof. intros h. eapply C3R.OnOne2_All2_refl; [exact h|exact C3R.peta_refl|exact C3R.eta1_peta]. Qed.

Lemma OnOne2_eta1_eta l l' : OnOne2 eta1 l l' -> All2 eta l l'.
Proof.
  intros h. eapply C3R.OnOne2_All2_refl; [exact h|intros x; apply rt_refl|intros x y e; now apply rt_step].
Qed.

(** η inversion with a (co)fixpoint as target: the root η-expansion of it, or an η
    step inside its bodies/types (read as [All2 pdef]). *)
Lemma eta1_tFix_tgt h0 mfix idx : eta1 h0 (tFix mfix idx) ->
  (∑ na A, h0 = eta_redex na A (tFix mfix idx)) +
  (∑ mfix0, (h0 = tFix mfix0 idx) × All2 pdef mfix0 mfix).
Proof.
  intros h. remember (tFix mfix idx) as x eqn:E. revert E.
  destruct h; intros E; try discriminate E.
  - left. subst. now do 2 eexists.
  - right. injection E as -> ->. eexists; split; [reflexivity|]. now apply mfix_ty_pdef.
  - right. injection E as -> ->. eexists; split; [reflexivity|]. now apply mfix_body_pdef.
Qed.

Lemma eta1_tCoFix_tgt h0 mfix idx : eta1 h0 (tCoFix mfix idx) ->
  (∑ na A, h0 = eta_redex na A (tCoFix mfix idx)) +
  (∑ mfix0, (h0 = tCoFix mfix0 idx) × All2 pdef mfix0 mfix).
Proof.
  intros h. remember (tCoFix mfix idx) as x eqn:E. revert E.
  destruct h; intros E; try discriminate E.
  - left. subst. now do 2 eexists.
  - right. injection E as -> ->. eexists; split; [reflexivity|]. now apply mfix_ty_pdef.
  - right. injection E as -> ->. eexists; split; [reflexivity|]. now apply mfix_body_pdef.
Qed.

(** Split on the arguments of a spine whose head is an η-redex: none (so the term
    is that λ) or some (so one β step removes the η-redex). *)
Ltac split_head Σ Γ :=
  match goal with
  | |- context [mkApps (tLambda ?na ?A (tApp (lift 1 0 ?X) (tRel 0))) ?l] =>
      destruct (head_eta_split Σ Γ na A X l) as [->|hr]
  end.

(** A target that is a constructor application: its η-source is a λ (excluded by
    the invariant), already a constructor application, or β-reduces to the target. *)
Lemma eta1_construct_tgt Σ Γ a0 ind k uu bs :
  eta1 a0 (mkApps (tConstruct ind k uu) bs) ->
  (isLambda a0 = true) + (isConstruct_app a0 = true) + red1 Σ Γ a0 (mkApps (tConstruct ind k uu) bs).
Proof.
  intros he.
  destruct (eta1_mkApps_tgt _ _ _ he) as [[[h0 [hh ->]]|[bs0 [hb ->]]]|(na & A & bs1 & bs2 & -> & ->)].
  - depelim hh. split_head Σ Γ.
    + left; left. reflexivity.
    + right. exact hr.
  - left; right. unfold isConstruct_app. now rewrite decompose_app_mkApps.
  - split_head Σ Γ.
    + left; left. reflexivity.
    + right. rewrite mkApps_app. exact hr.
Qed.

Lemma eta1_lit_isLambda a l : eta1 a (term_of_lit l) -> isLambda a = true.
Proof.
  intros h. remember (term_of_lit l) as x eqn:E. revert E.
  destruct h; intros E; try reflexivity; destruct l; discriminate E.
Qed.

Lemma nth_error_at_pre {A} (pre post : list A) a : nth_error (pre ++ a :: post) #|pre| = Some a.
Proof. rewrite (nth_error_app_ge pre (a :: post) #|pre| (le_n _)) Nat.sub_diag. reflexivity. Qed.

Lemma app_cons_not_nil {A} (pre post : list A) a : pre ++ a :: post <> [].
Proof. intros e. apply app_eq_nil in e as [_ e]. discriminate e. Qed.

(** ** The root cases, one lemma per [red1] rule *)

Section Roots.
  Context {cf : checker_flags} {Σ : global_env} (cb : ClosedBodies Σ).

  (** β. CLOSED, no invariant: the η-expanded head costs one extra β step. *)
  Lemma pp_beta Γ t na A b a :
    on_free_vars xpredT t -> eta1 t (tApp (tLambda na A b) a) -> PP Σ Γ t (b {0 := a}).
  Proof.
    intros ho he. depelim he.
    - apply (pp_root cb); [exact ho|apply red_beta].
    - match goal with H : eta1 _ (tLambda _ _ _) |- _ => depelim H end.
      + eexists. split; [|apply rt_refl].
        eapply t_trans; [apply t_step; apply red1_eta_head|apply t_step; apply red_beta].
      + eexists. split; [apply t_step; apply red_beta|apply rt_refl].
      + eexists. split; [apply t_step; apply red_beta|]. now apply eta1_subst.
    - eexists. split; [apply t_step; apply red_beta|].
      apply subst_eta. constructor; [now apply rt_step|constructor].
  Qed.

  (** ζ. CLOSED, no invariant. *)
  Lemma pp_zeta Γ t na d T b :
    on_free_vars xpredT t -> eta1 t (tLetIn na d T b) -> PP Σ Γ t (b {0 := d}).
  Proof.
    intros ho he. depelim he.
    - apply (pp_root cb); [exact ho|apply red_zeta].
    - eexists. split; [apply t_step; apply red_zeta|].
      apply subst_eta. constructor; [now apply rt_step|constructor].
    - eexists. split; [apply t_step; apply red_zeta|apply rt_refl].
    - eexists. split; [apply t_step; apply red_zeta|]. now apply eta1_subst.
  Qed.

  (** Variable unfolding. CLOSED: only the root η can produce a [tRel]. *)
  Lemma pp_rel Γ t i body :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    on_free_vars xpredT t -> eta1 t (tRel i) -> PP Σ Γ t (lift0 (S i) body).
  Proof.
    intros hb ho he. depelim he. apply (pp_root cb); [exact ho|now apply red_rel].
  Qed.

  (** δ. CLOSED: only the root η can produce a [tConst]. *)
  Lemma pp_delta Γ t c decl body u :
    declared_constant Σ c decl -> cst_body decl = Some body ->
    on_free_vars xpredT t -> eta1 t (tConst c u) -> PP Σ Γ t (subst_instance u body).
  Proof.
    intros hd hb ho he. depelim he. apply (pp_root cb); [exact ho|now eapply red_delta].
  Qed.

  (** ι. NEEDS-INVARIANT for exactly one sub-case: the scrutinee is a λ that
      η-contracts to the constructor application. Every other sub-case CLOSED. *)
  Lemma pp_iota Γ t ci c uu args p brs br :
    nth_error brs c = Some br ->
    #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (tCase ci p (mkApps (tConstruct ci.(ci_ind) c uu) args) brs) ->
    PP Σ Γ t (iota_red ci.(ci_npar) p args br).
  Proof.
    intros hnth hlen ho hs he.
    have hc := hs. depelim he.
    - apply (pp_root cb); [exact ho|now apply red_iota].
    - (* η in a parameter *)
      eexists. split; [apply t_step; eapply red_iota; eassumption|].
      apply C3R.peta_to_eta. apply C3R.peta_iota_red.
      + apply All2_refl. exact C3R.peta_refl.
      + cbn. apply OnOne2_eta1_peta. assumption.
      + reflexivity.
      + reflexivity.
      + apply C3R.peta_refl.
    - (* η in the return type: ι ignores it *)
      eexists. split; [apply t_step; eapply red_iota; eassumption|].
      apply C3R.peta_to_eta. apply C3R.peta_iota_red.
      + apply All2_refl. exact C3R.peta_refl.
      + apply All2_refl. exact C3R.peta_refl.
      + reflexivity.
      + reflexivity.
      + apply C3R.peta_refl.
    - (* η in the scrutinee *)
      apply eta_safe_case_scrut in hc.
      match goal with H : eta1 _ (mkApps _ args) |- _ =>
        destruct (eta1_mkApps_tgt _ _ _ H) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & -> & ->)]
      end.
      + depelim hh. split_head Σ Γ.
        * cbn in hc. discriminate hc.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step; apply case_red_discr; exact hr|].
          apply t_step. now apply red_iota.
      + eexists. split.
        * apply t_step. eapply red_iota; [exact hnth|]. now rewrite (OnOne2_length ha).
        * apply C3R.peta_to_eta. apply C3R.peta_iota_red.
          -- now apply OnOne2_eta1_peta.
          -- apply All2_refl. exact C3R.peta_refl.
          -- reflexivity.
          -- reflexivity.
          -- apply C3R.peta_refl.
      + split_head Σ Γ.
        * cbn in hc. discriminate hc.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step; apply case_red_discr; exact hr|].
          apply t_step. rewrite -mkApps_app. now apply red_iota.
    - (* η in a branch *)
      match goal with H : OnOne2 (on_Trel_eq eta1 bbody bcontext) ?b0 ?b1 |- _ =>
        have hb : All2 (fun x y => bcontext x = bcontext y × C3R.peta (bbody x) (bbody y)) b0 b1
          by (eapply C3R.OnOne2_All2_refl;
              [exact H
              |intros x; split; [reflexivity|apply C3R.peta_refl]
              |intros x y [h1 h2]; split; [exact h2|now apply C3R.eta1_peta]])
      end.
      destruct (All2_nth_error_Some_r c br hb hnth) as (br0 & hnth0 & (hctx & hbody)).
      eexists. split.
      + apply t_step. eapply red_iota; [exact hnth0|]. now rewrite hctx.
      + apply C3R.peta_to_eta. apply C3R.peta_iota_red.
        * apply All2_refl. exact C3R.peta_refl.
        * apply All2_refl. exact C3R.peta_refl.
        * reflexivity.
        * exact hctx.
        * exact hbody.
  Qed.

  (** Projection. NEEDS-INVARIANT for the λ argument only; other sub-cases CLOSED. *)
  Lemma pp_proj Γ t pr args uu arg :
    nth_error args (pr.(proj_npars) + pr.(proj_arg)) = Some arg ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (tProj pr (mkApps (tConstruct pr.(proj_ind) 0 uu) args)) -> PP Σ Γ t arg.
  Proof.
    intros hnth ho hs he.
    have hc := hs. depelim he.
    - apply (pp_root cb); [exact ho|now apply red_proj].
    - apply eta_safe_proj_arg in hc.
      match goal with H : eta1 _ (mkApps _ args) |- _ =>
        destruct (eta1_mkApps_tgt _ _ _ H) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & -> & ->)]
      end.
      + depelim hh. split_head Σ Γ.
        * cbn in hc. discriminate hc.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step; apply proj_red; exact hr|].
          apply t_step. now apply red_proj.
      + have hall := OnOne2_eta1_eta _ _ ha.
        destruct (All2_nth_error_Some_r _ arg hall hnth) as (arg0 & hnth0 & he0).
        exists arg0. split; [apply t_step; now apply red_proj|exact he0].
      + split_head Σ Γ.
        * cbn in hc. discriminate hc.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step; apply proj_red; exact hr|].
          apply t_step. rewrite -mkApps_app. now apply red_proj.
  Qed.

  (** Cofix-case. NEEDS-INVARIANT for the λ scrutinee only; other sub-cases CLOSED
      (η in the cofixpoint bodies is read back through [unfold_cofix_back]). *)
  Lemma pp_cofix_case Γ t ip p mfix idx args narg fn brs :
    unfold_cofix mfix idx = Some (narg, fn) ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (tCase ip p (mkApps (tCoFix mfix idx) args) brs) ->
    PP Σ Γ t (tCase ip p (mkApps fn args) brs).
  Proof.
    intros hu ho hs he.
    have hc := hs. depelim he.
    - apply (pp_root cb); [exact ho|now eapply red_cofix_case].
    - eexists. split; [apply t_step; eapply red_cofix_case; exact hu|].
      apply rt_step. now apply case_eta_param.
    - eexists. split; [apply t_step; eapply red_cofix_case; exact hu|].
      apply rt_step. now apply case_eta_return.
    - apply eta_safe_case_scrut in hc.
      match goal with H : eta1 _ (mkApps _ args) |- _ =>
        destruct (eta1_mkApps_tgt _ _ _ H) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & -> & ->)]
      end.
      + destruct (eta1_tCoFix_tgt _ _ _ hh) as [(na & A & ->)|(mfix0 & -> & hm)].
        * split_head Σ Γ.
          -- cbn in hc. discriminate hc.
          -- eexists. split; [|apply rt_refl].
             eapply t_trans; [apply t_step; apply case_red_discr; exact hr|].
             apply t_step. now eapply red_cofix_case.
        * destruct (unfold_cofix_back _ _ _ _ _ hm hu) as (fn0 & hu0 & hp).
          eexists. split; [apply t_step; eapply red_cofix_case; exact hu0|].
          apply eta_Case_discr. apply eta_mkApps_head. now apply C3R.peta_to_eta.
      + eexists. split; [apply t_step; eapply red_cofix_case; exact hu|].
        apply rt_step. apply case_eta_discr. now apply eta1_mkApps_args.
      + split_head Σ Γ.
        * cbn in hc. discriminate hc.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step; apply case_red_discr; exact hr|].
          apply t_step. rewrite -mkApps_app. now eapply red_cofix_case.
    - eexists. split; [apply t_step; eapply red_cofix_case; exact hu|].
      apply rt_step. now apply case_eta_brs.
  Qed.

  (** Cofix-proj. NEEDS-INVARIANT for the λ argument only; other sub-cases CLOSED. *)
  Lemma pp_cofix_proj Γ t pr mfix idx args narg fn :
    unfold_cofix mfix idx = Some (narg, fn) ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (tProj pr (mkApps (tCoFix mfix idx) args)) ->
    PP Σ Γ t (tProj pr (mkApps fn args)).
  Proof.
    intros hu ho hs he.
    have hc := hs. depelim he.
    - apply (pp_root cb); [exact ho|now eapply red_cofix_proj].
    - apply eta_safe_proj_arg in hc.
      match goal with H : eta1 _ (mkApps _ args) |- _ =>
        destruct (eta1_mkApps_tgt _ _ _ H) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & -> & ->)]
      end.
      + destruct (eta1_tCoFix_tgt _ _ _ hh) as [(na & A & ->)|(mfix0 & -> & hm)].
        * split_head Σ Γ.
          -- cbn in hc. discriminate hc.
          -- eexists. split; [|apply rt_refl].
             eapply t_trans; [apply t_step; apply proj_red; exact hr|].
             apply t_step. now eapply red_cofix_proj.
        * destruct (unfold_cofix_back _ _ _ _ _ hm hu) as (fn0 & hu0 & hp).
          eexists. split; [apply t_step; eapply red_cofix_proj; exact hu0|].
          apply eta_Proj. apply eta_mkApps_head. now apply C3R.peta_to_eta.
      + eexists. split; [apply t_step; eapply red_cofix_proj; exact hu|].
        apply rt_step. apply proj_eta. now apply eta1_mkApps_args.
      + split_head Σ Γ.
        * cbn in hc. discriminate hc.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step; apply proj_red; exact hr|].
          apply t_step. rewrite -mkApps_app. now eapply red_cofix_proj.
  Qed.

  (** Fixpoint unfolding. NEEDS-INVARIANT for one sub-case: the [rarg]-th argument
      is a λ that η-contracts to a constructor application. CLOSED otherwise:
      η in the bodies (read back), η in another argument, η inside the [rarg]-th
      argument (it is already a constructor application, or β-reduces to it), and
      an η-redex as spine head (β first). *)
  Lemma pp_fix Γ t mfix idx args narg fn :
    unfold_fix mfix idx = Some (narg, fn) ->
    is_constructor narg args = true ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (mkApps (tFix mfix idx) args) -> PP Σ Γ t (mkApps fn args).
  Proof.
    intros hu hc ho hs he.
    have hred : red1 Σ Γ (mkApps (tFix mfix idx) args) (mkApps fn args) by (eapply red_fix; eassumption).
    destruct (eta1_mkApps_tgt _ _ _ he) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & -> & ->)].
    - destruct (eta1_tFix_tgt _ _ _ hh) as [(na & A & ->)|(mfix0 & -> & hm)].
      + now apply (pp_head_eta cb).
      + destruct (unfold_fix_back _ _ _ _ _ hm hu) as (fn0 & hu0 & hp).
        eexists. split; [apply t_step; eapply red_fix; [exact hu0|exact hc]|].
        apply eta_mkApps_head. now apply C3R.peta_to_eta.
    - destruct (OnOne2_split _ _ _ _ ha) as (a0 & a & pre & post & ha0 & -> & ->).
      destruct (Nat.eq_dec narg #|pre|) as [en|ne].
      + (* the η step is in the [rarg]-th argument *)
        subst narg.
        have hca : isConstruct_app a = true.
        { move: hc. rewrite /is_constructor nth_error_at_pre. exact id. }
        unfold isConstruct_app in hca.
        destruct (decompose_app a) as [hd bs] eqn:ea. cbn in hca.
        destruct hd; try discriminate hca.
        apply decompose_app_inv in ea. subst a.
        destruct (eta1_construct_tgt Σ Γ _ _ _ _ _ ha0) as [[hl|hca0]|hr].
        * exfalso.
          have hsp := eta_safe_spine _ _ _ (app_cons_not_nil pre post a0) hs.
          have hn := spine_safe_fix _ _ _ _ _ _ _ hu (nth_error_at_pre pre post a0) hsp.
          unfold notLam in hn. rewrite hl in hn. discriminate hn.
        * eexists. split.
          -- apply t_step. eapply red_fix; [exact hu|].
             rewrite /is_constructor nth_error_at_pre. exact hca0.
          -- apply rt_step. apply eta1_mkApps_args. apply OnOne2_app. now constructor.
        * eexists. split; [|apply rt_refl].
          eapply t_trans; [apply t_step|apply t_step; exact hred].
          apply red1_mkApps_r. apply OnOne2_app. now constructor.
      + (* the η step is in another argument *)
        have hc' : is_constructor narg (pre ++ a0 :: post) = true.
        { move: hc. rewrite /is_constructor.
          destruct (Nat.lt_ge_cases narg #|pre|) as [lt|ge].
          - rewrite (nth_error_app_lt pre (a :: post) narg lt) (nth_error_app_lt pre (a0 :: post) narg lt).
            exact id.
          - rewrite (nth_error_app_ge pre (a :: post) narg ge) (nth_error_app_ge pre (a0 :: post) narg ge).
            destruct (narg - #|pre|) as [|k] eqn:ek; [lia|]. cbn. exact id. }
        eexists. split; [apply t_step; eapply red_fix; [exact hu|exact hc']|].
        apply rt_step. apply eta1_mkApps_args. apply OnOne2_app. now constructor.
    - rewrite mkApps_app in hred. now apply (pp_head_eta cb).
  Qed.

  (** Primitive operation. NEEDS-INVARIANT for one sub-case: an argument is a λ
      that η-contracts to a literal. CLOSED otherwise. *)
  Lemma pp_prim Γ t c uu op ls v :
    prim_op_of Σ c = Some op ->
    red1 Σ Γ (mkApps (tConst c uu) (map term_of_lit ls)) v ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (mkApps (tConst c uu) (map term_of_lit ls)) -> PP Σ Γ t v.
  Proof.
    intros hop hred ho hs he.
    destruct (eta1_mkApps_tgt _ _ _ he) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & e & ->)].
    - depelim hh. now apply (pp_head_eta cb).
    - exfalso.
      destruct (OnOne2_split _ _ _ _ ha) as (a0 & a & pre & post & ha0 & -> & hm).
      have hin : In a (map term_of_lit ls).
      { rewrite hm. apply in_or_app. right. now left. }
      apply in_map_iff in hin as [lit [<- _]].
      have hl := eta1_lit_isLambda _ _ ha0.
      have hsp := eta_safe_spine _ _ _ (app_cons_not_nil pre post a0) hs.
      have hn := forallb_app_cons_mid _ _ _ _ (spine_safe_prim _ _ _ _ _ hop hsp).
      unfold notLam in hn. rewrite hl in hn. discriminate hn.
    - rewrite e mkApps_app in hred. now apply (pp_head_eta cb).
  Qed.

End Roots.
