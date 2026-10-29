(* Distributed under the terms of the MIT license. *)

(** * T8 (typed postponement): pinned statements, route, and the root cases of
    one-step η-postponement

  ** What T8 claims
  A well-typed type that is E-convertible to a head form (sort, product, applied
  inductive) reduces to that head form by base [red] alone. The pinned forms are
  the [Definition]s [T8_*_statement] below; none is proved here. Without typing the
  claim is false ([A6_F_raw_false]; and [tProj p (λx. C ps X x)] η-reduces then
  projects, while it is β-stuck).

  ** Route
  1. A6 gives, untyped, that the canonical form [canon T] reaches the head by
     [(R_c ∪ eta1)*] ([ws_cumul_pbE_Sort_r_inv], [ws_cumul_pbE_Prod_r_inv],
     [ws_cumul_pbE_Ind_r_inv]).
  2. Postpone η in that chain: [(R_c ∪ eta1)* ⊆ R_c* · eta1*] on the canonical forms of
     the reducts of a typed [T]. η is postponed over base [red1] on the actual term;
     the [R_c] form follows by [red1_R_c] and [eta1_star_canon], because [canon] keeps
     every λ, every scrutinee position and every fixpoint [rarg]. The one-step
     commutation is [eta1 t u → red1 Σ Γ u v → ∑ w, red1⁺ t w × eta1* w v]. This
     file proves it when the [red1] step is a rule applied at the root of [u]
     ([pp_beta] ... [pp_prim]), and for η at the root of [t] ([pp_root]) or at the
     head of an application spine ([pp_head_eta]), under any [red1] step. It does
     not prove the congruence cases (η and the [red1] step in different
     subterms), which need the [red1] context transport for η-related let bodies
     and case/fixpoint contexts.
     Statement change: [pp_prim] no longer has the premise [prim_op_of Σ c = Some op]
     (dropped when the primitive clause of [eta_safe] became "no applied primitive
     value"); the lemma without it is stronger, and its callers lose nothing.
  3. Lift [R_c*] from [canon T] back to [red] on [T] (backward simulation of [red1]
     through [canon]: [canon_dom] is a normal sort and every redex of [canon T] is
     the image of a redex of [T]).
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

  That typing gives the invariant is not proved here: a λ has a product type, and
  the four positions have an inductive or primitive type (for a fixpoint, its
  [rarg] type, which [wf_fixpointE] makes convertible to an inductive). The
  invariant is NOT preserved by β or by fixpoint unfolding as a syntactic
  property: [(λx. tCase x _) (λy. M y)] β-reduces to a λ scrutinee, and unfolding a
  fixpoint turns a recursive call [f (λy. C y)] into a fixpoint spine with a λ
  [rarg]. Both reducts come from ill-typed terms, so the invariant survives [red]
  on typed terms through E subject reduction (the forecast row T1), and only
  there. It is also not preserved by η: η at a spine head [(λx. F x) a] merges the
  spine into a fixpoint spine.

  ** Why the one-step commutation does not iterate by itself
  Iterating it over [eta1* · red1] needs the invariant on η-reducts of a typed
  term, which subject reduction does not give (η-reducts need not be typed:
  [λx:A. f x] with [f : Π x:A'. B] and [A ≤ A'], [A ≠ A'], is typed at [Π x:A. B], and
  in [g (λx:A. f x)] with [g : (Π x:A. B) → C] the η-reduct [g f] is ill-typed). The
  iteration needs the same commutation for a development-style parallel η ([pe],
  with the η rule [pe b ((lift0 1 M') (tRel 0)) → pe (λ. b) M'], which is closed
  under post-composition with [eta1], so [eta1* = pe]); its β-head case recurses on
  the [pe] derivation of the η-expanded head, which is structurally smaller. *)

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
     PCUICEtaC3BR PCUICTypingEtaInd PCUICClosedTypEta PCUICInversionEta PCUICEtaA6 PCUICEtaA6Ind
     PCUICInduction PCUICWfUniverses
     PCUICCumulativitySpecEtaClosureInstances PCUICInversionEtaInstances.
From MetaRocq.PCUIC Require PCUICSize PCUICClosedTyp PCUICEtaScope.
From MetaRocq.PCUIC Require Import PCUICEtaCanon PCUICEtaI5EtaL PCUICEtaC1b.

Import ListNotations.

Set Default Goal Selector "!".

(** ** The pinned target statements (not proved here)

  Satisfying instances: [T8_*_instance] below. [wf_localE Σ Γ] is not a premise:
  the typing premise gives it ([T8_typing_wf_localE]).

  Falsity check, no counterexample found. A counterexample is a typed [T : tSort s'],
  E-convertible to the head form, whose base reducts never reach a head form. E adds
  only function η to base conversion, so the head form must appear through η. The
  candidates and why each fails:
  - [T] a λ (for example [λz:D. (tProd na (λy:z.y) B) z], the witness of
    [A6_F_raw_false]): a typed λ has a product type, which is not E-convertible to
    a sort ([ws_cumul_pbE_Prod_Sort_inv]), so [T : tSort s'] excludes it;
  - [T] the η-expansion [λx:A. I x] of an under-applied inductive: a λ again. Under
    [welltypedE] alone, instead of [T : tSort s'], it is a typable counterexample
    to the [Ind] forms;
  - [T] a stuck elimination (a [match], projection or fixpoint on a neutral term):
    [canon] keeps it, the [(R_c ∪ eta1)*] chains from it keep the elimination, and
    the chains from a head form keep the head, so no [JoinE] relates them. *)

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

(** A primitive value is never a function, so it is never applied in a typed term.
    The η-expansion [λx. lit x] of a literal contains such an application. *)
Definition notPrimHead (t : term) : bool := match t with tPrim _ => false | _ => true end.

Definition spine_safe (Σ : global_env) (t : term) : bool :=
  match decompose_app t with
  | (tFix mfix idx, args) =>
      match unfold_fix mfix idx with
      | Some (narg, _) =>
          match nth_error args narg with Some a => notLam a | None => true end
      | None => true
      end
  | _ => true
  end.

Fixpoint eta_safe (Σ : global_env) (t : term) : bool :=
  match t with
  | tEvar _ l => forallb (eta_safe Σ) l
  | tProd _ A B => eta_safe Σ A && eta_safe Σ B
  | tLambda _ A b => eta_safe Σ A && eta_safe Σ b
  | tLetIn _ b B c => eta_safe Σ b && eta_safe Σ B && eta_safe Σ c
  | tApp f a => notPrimHead f && spine_safe Σ t && eta_safe Σ f && eta_safe Σ a
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

Lemma eta_safe_mkApps_args Σ h args : eta_safe Σ (mkApps h args) -> forallb (eta_safe Σ) args.
Proof.
  induction args as [|a l IH] using MRList.rev_ind; [reflexivity|].
  rewrite mkApps_app forallb_app. cbn [mkApps eta_safe forallb]. move/andP => [/andP [_ h1] h2].
  by rewrite (IH h1) h2.
Qed.

(** The η-expansion of a literal is never [eta_safe]. *)
Lemma eta_safe_lit_eta Σ na A l : eta_safe Σ (eta_redex na A (term_of_lit l)) = false.
Proof. destruct l; cbn; now rewrite andb_false_r. Qed.

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

Lemma eta1_lit_inv a l : eta1 a (term_of_lit l) -> ∑ na A, a = eta_redex na A (term_of_lit l).
Proof.
  intros h. remember (term_of_lit l) as x eqn:E. revert E.
  destruct h; intros E; try (destruct l; discriminate E).
  subst. now do 2 eexists.
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
      that η-contracts to a literal, i.e. [λx. lit x], which applies a primitive
      value. CLOSED otherwise. *)
  Lemma pp_prim Γ t c uu ls v :
    red1 Σ Γ (mkApps (tConst c uu) (map term_of_lit ls)) v ->
    on_free_vars xpredT t -> eta_safe Σ t ->
    eta1 t (mkApps (tConst c uu) (map term_of_lit ls)) -> PP Σ Γ t v.
  Proof.
    intros hred ho hs he.
    destruct (eta1_mkApps_tgt _ _ _ he) as [[[h0 [hh ->]]|[args0 [ha ->]]]|(na & A & args1 & args2 & e & ->)].
    - depelim hh. now apply (pp_head_eta cb).
    - exfalso.
      destruct (OnOne2_split _ _ _ _ ha) as (a0 & a & pre & post & ha0 & -> & hm).
      have hin : In a (map term_of_lit ls).
      { rewrite hm. apply in_or_app. right. now left. }
      apply in_map_iff in hin as [lit [<- _]].
      destruct (eta1_lit_inv _ _ ha0) as (na & A & ->).
      have hn := forallb_app_cons_mid _ _ _ _ (eta_safe_mkApps_args _ _ _ hs).
      cbn beta in hn. rewrite eta_safe_lit_eta in hn. discriminate hn.
    - rewrite e mkApps_app in hred. now apply (pp_head_eta cb).
  Qed.

End Roots.

(** ** The context premise of the pinned statements

  [wf_localE Σ Γ] is not a premise of [T8_*_statement]: the typing premise gives it. *)
Lemma T8_typing_wf_localE {cf : checker_flags} {Σ : global_env_ext} Γ T s :
  Σ ;;; Γ |-E T : tSort s -> wf_localE Σ Γ.
Proof. exact typingE_wf_local. Qed.

(** ** Typing gives the invariant *)

Lemma ctx_inst_typed {cf : checker_flags} {Σ : global_env_ext} Γ l Δ :
  ctx_inst (typingE Σ) Γ l Δ -> All (fun t => ∑ T, Σ ;;; Γ |-E t : T) l.
Proof.
  induction 1.
  - constructor.
  - constructor; [eexists; eassumption|assumption].
  - assumption.
Qed.

Section TypedSafe.
  Context {cf : checker_flags} {Σ : global_env_ext} (wfΣ : wfE Σ).

  Let cbΣ : ClosedBodies Σ := wfE_ClosedBodies Σ (wfΣ := wfΣ).

  (** An inversion lemma of [PCUICInversionEta], with or without its [wfE] argument. *)
  Ltac invE lem h hi := first [pose proof (lem Σ wfΣ _ _ _ _ _ _ h) as hi
                              | pose proof (lem Σ wfΣ _ _ _ _ _ h) as hi
                              | pose proof (lem Σ wfΣ _ _ _ _ h) as hi
                              | pose proof (lem Σ wfΣ _ _ _ h) as hi
                              | pose proof (lem Σ wfΣ h) as hi
                              | pose proof (lem Σ h) as hi].

  (** A λ never has an inductive type: its type is a product. *)
  Lemma typed_lambda_not_ind_ty Γ na A b ind u l :
    Σ ;;; Γ |-E tLambda na A b : mkApps (tInd ind u) l -> False.
  Proof.
    intros h. invE inversion_LambdaE h hi. destruct hi as (B & _ & _ & hc).
    exact (invert_cumul_prod_indE (Σ := Σ) (wfΣ := cbΣ) hc).
  Qed.

  Lemma typed_lambda_not_ind Γ na A b T ind u l :
    Σ ;;; Γ |-E tLambda na A b : T -> ws_cumul_pbE Cumul Σ Γ T (mkApps (tInd ind u) l) -> False.
  Proof.
    intros h hT. invE inversion_LambdaE h hi. destruct hi as (B & _ & _ & hc).
    exact (invert_cumul_prod_indE (Σ := Σ) (wfΣ := cbΣ)
             (ws_cumul_pbE_trans (Σ := Σ) (wfΣ := cbΣ) _ _ _ hc hT)).
  Qed.

  Lemma typed_notLam_ind Γ c ind u l : Σ ;;; Γ |-E c : mkApps (tInd ind u) l -> notLam c.
  Proof.
    intros h. destruct c; try reflexivity. exfalso. exact (typed_lambda_not_ind_ty _ _ _ _ _ _ _ h).
  Qed.

  (** A primitive value never has a product type: its type is an axiom (applied, for
      arrays), which is not a primitive operation. *)
  Lemma typed_prim_not_prod Γ p na A B : Σ ;;; Γ |-E tPrim p : tProd na A B -> False.
  Proof.
    intros h. invE inversion_PrimE h hi.
    destruct hi as [prim_ty [cdecl [_ hpc hdecl hinv _ hcum]]].
    have hop : prim_op_of Σ prim_ty = None.
    { pose proof wfΣ as [_ [wfr _]]. exact (prim_op_of_primitive_constant _ _ _ wfr hpc). }
    destruct p as [? []]; cbn in hinv; destruct hinv as [_ hb _]; simp prim_type in hcum.
    1-3: exact (invert_cumul_axiom_prodE (Σ := Σ) (wfΣ := cbΣ) (args := []) hdecl hb hop hcum).
    exact (invert_cumul_axiom_prodE (Σ := Σ) (wfΣ := cbΣ) (args := [_]) hdecl hb hop hcum).
  Qed.

  Lemma typed_notPrimHead Γ u na A B : Σ ;;; Γ |-E u : tProd na A B -> notPrimHead u.
  Proof.
    intros h. destruct u; try reflexivity. exfalso. exact (typed_prim_not_prod _ _ _ _ _ h).
  Qed.

  (** The one statement used here that the tree does not give: the [rarg]-th argument of
      a typed applied fixpoint has a type that is E-convertible to an applied inductive.
      Its proof needs the E typing spine: the spine's domains are E-convertible to the
      products of a type that [wf_fixpointE] relates to a telescope whose [rarg]-th
      assumption is an applied inductive.

      It is not the known-false neighbour ("[welltypedE T] and [T] E-convertible to an
      inductive head give a REDUCTION of [T] to that head", refuted by [λx:A. I x]):
      its premise is a typing of the whole applied fixpoint, not a [welltypedE]-only
      premise on an inductive-head term, and its conclusion is only an E-CONVERSION of
      the argument's type with an applied inductive, which the η-expansion [λx:A. I x]
      would satisfy too; it claims no reduction. Satisfying instance:
      [fix_rarg_inductive_instance] below. *)
  Definition fix_rarg_inductive_statement : Type :=
    forall Γ mfix idx args narg fn a T,
      Σ ;;; Γ |-E mkApps (tFix mfix idx) args : T ->
      unfold_fix mfix idx = Some (narg, fn) ->
      nth_error args narg = Some a ->
      ∑ A ind u l, (Σ ;;; Γ |-E a : A) × ws_cumul_pbE Cumul Σ Γ A (mkApps (tInd ind u) l).

  (* FORECAST-ONLY: provable from the E copies of PCUICArities.typing_spine / PCUICSpine (copies 14/15) *)
  Context (fix_rarg_inductive : fix_rarg_inductive_statement).

  Lemma typed_spine_safe Γ t T : Σ ;;; Γ |-E t : T -> spine_safe Σ t.
  Proof.
    intros ht. unfold spine_safe.
    destruct (decompose_app t) as [h args] eqn:ed.
    destruct h; cbv beta iota; try reflexivity.
    destruct (unfold_fix mfix idx) as [[narg fn]|] eqn:hu; cbv beta iota; [|reflexivity].
    destruct (nth_error args narg) as [a|] eqn:hn; cbv beta iota; [|reflexivity].
    apply decompose_app_inv in ed. subst t.
    destruct (fix_rarg_inductive _ _ _ _ _ _ _ _ ht hu hn) as (A & ind & u & l & ha & hA).
    destruct a; try reflexivity.
    exfalso. exact (typed_lambda_not_ind _ _ _ _ _ _ _ _ ha hA).
  Qed.

  Ltac apply_ih := match goal with
    | IH : forall _ _, _ -> is_true (eta_safe ?S ?x) |- is_true (eta_safe ?S ?x) =>
        eapply IH; eassumption
    end.

  (** Every typed term satisfies the invariant (given [fix_rarg_inductive]). *)
  Theorem typed_eta_safe Γ t T : Σ ;;; Γ |-E t : T -> eta_safe Σ t.
  Proof.
    induction t in Γ, T |- * using term_forall_list_ind; intros ht; cbn [eta_safe]; try reflexivity.
    - (* tEvar *) exfalso. exact (inversion_EvarE Σ ht).
    - (* tProd *) invE inversion_ProdE ht hi. destruct hi as (s1 & s2 & hA & hB & _).
      destruct hA as (_ & s & hA & _). hnf in hA.
      apply/andP; split; apply_ih.
    - (* tLambda *) invE inversion_LambdaE ht hi. destruct hi as (B & hA & hb & _).
      destruct hA as (_ & s & hA & _). hnf in hA.
      apply/andP; split; apply_ih.
    - (* tLetIn *) invE inversion_LetInE ht hi. destruct hi as (A & hbB & hc & _).
      destruct hbB as (hb & s & hB & _). hnf in hb. hnf in hB.
      rtoProp; repeat split; apply_ih.
    - (* tApp *) invE inversion_AppE ht hi. destruct hi as (na & A & B & hu & hv & _).
      rtoProp; repeat split.
      + eapply typed_notPrimHead; exact hu.
      + eapply typed_spine_safe; exact ht.
      + apply_ih.
      + apply_ih.
    - (* tCase *)
      destruct X as (Hpars & _ & Hret).
      invE inversion_CaseE ht hi.
      destruct hi as (mdecl & idecl & isdecl & indices & hdata & _).
      destruct hdata.
      rtoProp; repeat split.
      + eapply typed_notLam_ind; eassumption.
      + apply_ih.
      + match goal with H : ctx_inst _ _ _ _ |- _ =>
          pose proof (fst (All_app (ctx_inst_typed _ _ _ H))) as hp end.
        eapply All_forallb'; [exact (All_mix Hpars hp)|]. intros x [ih [Tx hx]]. exact (ih _ _ hx).
      + eapply Hret; eassumption.
      + match goal with
        | |- is_true (forallb _ ?brs) =>
          match goal with H : All2i _ _ _ brs |- _ =>
            have hb : All (fun br => ∑ Γ' T', Σ ;;; Γ' |-E bbody br : T') brs
              by (eapply All2i_All_right; [exact H|];
                  intros i x y (_ & _ & hbd & _); eexists _, _; exact hbd)
          end
        end.
        eapply All_forallb'; [exact (All_mix X0 hb)|]. intros x [[_ ih] (Γ' & T' & hx)].
        exact (ih _ _ hx).
    - (* tProj *) invE inversion_ProjE ht hi.
      destruct hi as (u & mdecl & idecl & cdecl & pdecl & args & _ & hc & _).
      apply/andP; split; [eapply typed_notLam_ind; exact hc|apply_ih].
    - (* tFix *) invE inversion_FixE ht hi.
      destruct hi as (decl & _ & _ & htys & hbodies & _).
      eapply All_forallb'; [exact (All_mix X (All_mix htys hbodies))|].
      intros d [[iht ihb] [hty hbd]]. apply/andP; split.
      + destruct hty as (_ & s & hs & _). hnf in hs. exact (iht _ _ hs).
      + destruct hbd as (hb & _). hnf in hb. exact (ihb _ _ hb).
    - (* tCoFix *) invE inversion_CoFixE ht hi.
      destruct hi as (decl & _ & _ & htys & hbodies & _).
      eapply All_forallb'; [exact (All_mix X (All_mix htys hbodies))|].
      intros d [[iht ihb] [hty hbd]]. apply/andP; split.
      + destruct hty as (_ & s & hs & _). hnf in hs. exact (iht _ _ hs).
      + destruct hbd as (hb & _). hnf in hb. exact (ihb _ _ hb).
    - (* tPrim *)
      destruct p as [? []]; cbn in X |- *; try reflexivity.
      invE inversion_PrimE ht hi. destruct hi as [prim_ty [cdecl [_ _ _ _ hhyps _]]].
      depelim hhyps. destruct X as (Ht & Hd & Hv).
      rtoProp; repeat split.
      + eapply All_forallb'; [exact (All_mix Hv hvalue)|]. intros y [ih hy]. exact (ih _ _ hy).
      + exact (Hd _ _ hdef).
      + exact (Ht _ _ hty).
  Qed.

End TypedSafe.

(** ** Concrete satisfying instances of the pinned statements

  In [si_Σ] ([Inductive I (A : Prop) : Prop := c : I A], well formed for the η typing
  by [si_wfE]). Each [T] is typed at a sort, is E-convertible to the head form, and
  reaches it by one β step; each lemma proves the premises of the statement for
  that [T] and its conclusion. The six statements share three terms:
  - [t8_sortT := (λx:Prop. Prop) (∀P:Prop. P)], reaching [Prop];
  - [t8_prodT := (λx:Prop. x) (∀P:Prop. P)], reaching the product [∀P:Prop. P];
  - [t8_indT := (λz:I x. I x) (c x)] in [x : Prop], reaching [I x]. *)

Section Instances.

#[local] Existing Instance default_checker_flags.

Definition t8_sortT : term := tApp (tLambda si_na si_P si_P) iv_False.
Definition t8_prodT : term := tApp iv_id iv_False.
Definition t8_indT : term := tApp (tLambda iv_zna (iv_Ix 0) (iv_Ix 1)) iv_disc.
Definition t8_indH : term := mkApps (tInd si_ind []) [tRel 0].

Lemma t8_sortT_typed : si_Σ ;;; [] |-E t8_sortT : tSort (Sort.super sProp).
Proof.
  assert (w1 : wf_localE si_Σ ([] ,, vass si_na si_P)) by exact (iv_wf_P si_Σ [] localenv_nil).
  assert (hSS : si_Σ ;;; [] ,, vass si_na si_P |-E tSort (Sort.super sProp)
               : tSort (Sort.super (Sort.super sProp))).
  { apply typeE_Sort; [exact w1|]. apply wf_sort_super. exact I. }
  refine (typeE_App _ _ (tLambda si_na si_P si_P) si_na si_P (tSort (Sort.super sProp)) _ iv_False
            _ _ (iv_False_typed si_Σ [] localenv_nil)).
  - apply typeE_Prod; [|exact hSS].
    exact (iv_vass_s si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl).
  - apply typeE_Lambda; [|exact (iv_P_typed si_Σ _ w1)].
    exact (iv_vass si_Σ [] si_na si_P _ (iv_P_typed si_Σ [] localenv_nil) eq_refl).
Qed.

Lemma t8_sortT_red : si_Σ ;;; [] ⊢ t8_sortT ⇝ tSort sProp.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ [] si_na si_P si_P iv_False).
Qed.

Lemma t8_prodT_red : si_Σ ;;; [] ⊢ t8_prodT ⇝ iv_False.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step. exact (red_beta si_Σ [] si_na si_P (tRel 0) iv_False).
Qed.

Lemma t8_indT_red : si_Σ ;;; iv_Γ1 ⊢ t8_indT ⇝ t8_indH.
Proof.
  split; [reflexivity|reflexivity|]. apply rt_step.
  exact (red_beta si_Σ iv_Γ1 iv_zna (iv_Ix 0) (iv_Ix 1) iv_disc).
Qed.

Lemma t8_cmp_refl pb : cmp_global_instance_finst si_Σ.1 (compare_universe si_Σ) pb (IndRef si_ind) 1 [] [].
Proof. unfold cmp_global_instance_finst. apply cmp_global_instance_eta_refl; tc. Qed.

Lemma t8_sort_cmp pb : compare_sort si_Σ pb sProp sProp.
Proof. destruct pb; cbn; first [reflexivity | exact I | trivial]. Qed.

Lemma T8_Sort_r_instance pb :
  [× wfE si_Σ, si_Σ ;;; [] |-E t8_sortT : tSort (Sort.super sProp),
     ws_cumul_pbE pb si_Σ [] t8_sortT (tSort sProp) &
     ∑ s'', si_Σ ;;; [] ⊢ t8_sortT ⇝ tSort s'' × compare_sort si_Σ pb s'' sProp].
Proof.
  split; [exact si_wfE|exact t8_sortT_typed|exact (red_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_cb) t8_sortT_red)|].
  exists sProp. split; [exact t8_sortT_red|apply t8_sort_cmp].
Qed.

Lemma T8_Sort_l_instance pb :
  [× wfE si_Σ, si_Σ ;;; [] |-E t8_sortT : tSort (Sort.super sProp),
     ws_cumul_pbE pb si_Σ [] (tSort sProp) t8_sortT &
     ∑ s'', si_Σ ;;; [] ⊢ t8_sortT ⇝ tSort s'' × compare_sort si_Σ pb sProp s''].
Proof.
  split; [exact si_wfE|exact t8_sortT_typed|exact (red_ws_cumul_pbE_inv (Σ := si_Σ) (wfΣ := si_cb) t8_sortT_red)|].
  exists sProp. split; [exact t8_sortT_red|apply t8_sort_cmp].
Qed.

Lemma T8_Prod_r_instance pb :
  [× wfE si_Σ, si_Σ ;;; [] |-E t8_prodT : tSort sProp,
     ws_cumul_pbE pb si_Σ [] t8_prodT (tProd si_na si_P (tRel 0)) &
     ∑ na' dom' codom',
       [× si_Σ ;;; [] ⊢ t8_prodT ⇝ tProd na' dom' codom', eq_binder_annot na' si_na,
          ws_cumul_pbE Conv si_Σ [] dom' si_P &
          ws_cumul_pbE pb si_Σ ([] ,, vass si_na si_P) codom' (tRel 0)]].
Proof.
  split; [exact si_wfE|exact (iv_app_typed si_Σ [] localenv_nil)
         |exact (red_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_cb) t8_prodT_red)|].
  exists si_na, si_P, (tRel 0).
  split; [exact t8_prodT_red|reflexivity|apply ws_cumul_pbE_refl; reflexivity|apply ws_cumul_pbE_refl; reflexivity].
Qed.

Lemma T8_Prod_l_instance pb :
  [× wfE si_Σ, si_Σ ;;; [] |-E t8_prodT : tSort sProp,
     ws_cumul_pbE pb si_Σ [] (tProd si_na si_P (tRel 0)) t8_prodT &
     ∑ na' dom' codom',
       [× si_Σ ;;; [] ⊢ t8_prodT ⇝ tProd na' dom' codom', eq_binder_annot si_na na',
          ws_cumul_pbE Conv si_Σ [] si_P dom' &
          ws_cumul_pbE pb si_Σ ([] ,, vass si_na si_P) (tRel 0) codom']].
Proof.
  split; [exact si_wfE|exact (iv_app_typed si_Σ [] localenv_nil)
         |exact (red_ws_cumul_pbE_inv (Σ := si_Σ) (wfΣ := si_cb) t8_prodT_red)|].
  exists si_na, si_P, (tRel 0).
  split; [exact t8_prodT_red|reflexivity|apply ws_cumul_pbE_refl; reflexivity|apply ws_cumul_pbE_refl; reflexivity].
Qed.

Lemma T8_Ind_r_instance pb :
  [× wfE si_Σ, si_Σ ;;; iv_Γ1 |-E t8_indT : tSort sProp,
     ws_cumul_pbE pb si_Σ iv_Γ1 t8_indT (mkApps (tInd si_ind []) [tRel 0]) &
     ∑ ui' l',
       [× si_Σ ;;; iv_Γ1 ⊢ t8_indT ⇝ mkApps (tInd si_ind ui') l',
          cmp_global_instance_finst si_Σ.1 (compare_universe si_Σ) pb (IndRef si_ind) #|[tRel 0]| ui' [] &
          ws_cumul_pbE_terms si_Σ iv_Γ1 l' [tRel 0]]].
Proof.
  split; [exact si_wfE|exact iv_bty_typed|exact (red_ws_cumul_pbE (Σ := si_Σ) (wfΣ := si_cb) t8_indT_red)|].
  exists [], [tRel 0]. split; [exact t8_indT_red|apply t8_cmp_refl|].
  constructor; [apply ws_cumul_pbE_refl; reflexivity|constructor].
Qed.

Lemma T8_Ind_l_instance pb :
  [× wfE si_Σ, si_Σ ;;; iv_Γ1 |-E t8_indT : tSort sProp,
     ws_cumul_pbE pb si_Σ iv_Γ1 (mkApps (tInd si_ind []) [tRel 0]) t8_indT &
     ∑ ui' l',
       [× si_Σ ;;; iv_Γ1 ⊢ t8_indT ⇝ mkApps (tInd si_ind ui') l',
          cmp_global_instance_finst si_Σ.1 (compare_universe si_Σ) pb (IndRef si_ind) #|[tRel 0]| [] ui' &
          All2 (ws_cumul_pbE Conv si_Σ iv_Γ1) [tRel 0] l']].
Proof.
  split; [exact si_wfE|exact iv_bty_typed|exact (red_ws_cumul_pbE_inv (Σ := si_Σ) (wfΣ := si_cb) t8_indT_red)|].
  exists [], [tRel 0]. split; [exact t8_indT_red|apply t8_cmp_refl|].
  constructor; [apply ws_cumul_pbE_refl; reflexivity|constructor].
Qed.

(** A satisfying instance of [fix_rarg_inductive_statement] (the hypothesis of
    [typed_eta_safe]): in [si_Σ], [fix f (x : I (∀P:Prop. P)) : I (∀P:Prop. P) := x]
    applied to [c (∀P:Prop. P)]; the [rarg]-th argument [c (∀P:Prop. P)] has the
    type [I (∀P:Prop. P)], an applied inductive. *)
Definition t8_ca : term := tApp (tConstruct si_ind 0 []) iv_False.

Lemma t8_ca_typed : si_Σ ;;; [] |-E t8_ca : iv_IF.
Proof.
  exact (typeE_App _ _ (tConstruct si_ind 0 []) si_na si_P (tApp (tInd si_ind []) (tRel 0)) _ iv_False
           (iv_cstr_prod_typed [] localenv_nil) (iv_cstr_typed [] localenv_nil)
           (iv_False_typed si_Σ [] localenv_nil)).
Qed.

Lemma t8_fixapp_typed : si_Σ ;;; [] |-E mkApps (tFix iv_mfix 0) [t8_ca] : iv_IF.
Proof.
  exact (typeE_App _ _ (tFix iv_mfix 0) si_na iv_IF iv_IF _ t8_ca (iv_fix_ty_typed [] localenv_nil)
           iv_fix_typed t8_ca_typed).
Qed.

Lemma fix_rarg_inductive_instance :
  [× wfE si_Σ,
     si_Σ ;;; [] |-E mkApps (tFix iv_mfix 0) [t8_ca] : iv_IF,
     unfold_fix iv_mfix 0 = Some (0, tLambda si_na iv_IF (tRel 0)),
     nth_error [t8_ca] 0 = Some t8_ca &
     ∑ A ind u l, (si_Σ ;;; [] |-E t8_ca : A) × ws_cumul_pbE Cumul si_Σ [] A (mkApps (tInd ind u) l)].
Proof.
  split; [exact si_wfE|exact t8_fixapp_typed|reflexivity|reflexivity|].
  exists iv_IF, si_ind, [], [iv_False].
  split; [exact t8_ca_typed|apply ws_cumul_pbE_refl; reflexivity].
Qed.

End Instances.

(** ** Development-style parallel η ([pe])

  [pe] is [C3R.peta] with one change: the η rule contracts a λ whose body REDUCES (in
  parallel) to an η-redex body, [pe b ((lift0 1 M') (tRel 0)) → pe (λ. b) M'], instead
  of one whose body syntactically is one. So [pe] absorbs η-redexes created by inner
  η steps, which is what makes it closed under a following [eta1] step and lets the
  parallel one-step postponement iterate with the invariant needed only on [red]
  reducts of a typed term. *)

Inductive pe : term -> term -> Type :=
| pe_eta na A b M' :
    pe b (tApp (lift0 1 M') (tRel 0)) ->
    pe (tLambda na A b) M'
| pe_Rel n : pe (tRel n) (tRel n)
| pe_Var i : pe (tVar i) (tVar i)
| pe_Sort s : pe (tSort s) (tSort s)
| pe_Const c u : pe (tConst c u) (tConst c u)
| pe_Ind ind u : pe (tInd ind u) (tInd ind u)
| pe_Construct ind n u : pe (tConstruct ind n u) (tConstruct ind n u)
| pe_Evar ev l l' : All2 pe l l' -> pe (tEvar ev l) (tEvar ev l')
| pe_Lambda na A A' M M' : pe A A' -> pe M M' -> pe (tLambda na A M) (tLambda na A' M')
| pe_App t t' u u' : pe t t' -> pe u u' -> pe (tApp t u) (tApp t' u')
| pe_Prod na a a' b b' : pe a a' -> pe b b' -> pe (tProd na a b) (tProd na a' b')
| pe_LetIn na b b' ty ty' u u' :
    pe b b' -> pe ty ty' -> pe u u' -> pe (tLetIn na b ty u) (tLetIn na b' ty' u')
| pe_Case ci p p' c c' brs brs' :
    All2 pe p.(pparams) p'.(pparams) ->
    p.(puinst) = p'.(puinst) ->
    p.(pcontext) = p'.(pcontext) ->
    pe p.(preturn) p'.(preturn) ->
    pe c c' ->
    All2 (fun x y => x.(bcontext) = y.(bcontext) × pe x.(bbody) y.(bbody)) brs brs' ->
    pe (tCase ci p c brs) (tCase ci p' c' brs')
| pe_Proj pr c c' : pe c c' -> pe (tProj pr c) (tProj pr c')
| pe_Fix mfix mfix' idx :
    All2 (fun d d' => pe d.(dtype) d'.(dtype) × pe d.(dbody) d'.(dbody)
                      × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
    pe (tFix mfix idx) (tFix mfix' idx)
| pe_CoFix mfix mfix' idx :
    All2 (fun d d' => pe d.(dtype) d'.(dtype) × pe d.(dbody) d'.(dbody)
                      × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
    pe (tCoFix mfix idx) (tCoFix mfix' idx)
| pe_Prim p p' : onPrims pe eq p p' -> pe (tPrim p) (tPrim p').

Derive Signature for pe.

Lemma pe_refl t : pe t t.
Proof.
  induction t using term_forall_list_ind; try solve [constructor; auto].
  - constructor. now apply All_All2 with (1 := X).
  - destruct X as (Hpars & _ & Hret).
    constructor.
    + now apply All_All2 with (1 := Hpars).
    + reflexivity.
    + reflexivity.
    + exact Hret.
    + assumption.
    + apply All_All2 with (1 := X0). intros x [_ Hb]. split; auto.
  - constructor. apply All_All2 with (1 := X). intros d [Ht Hb]. repeat split; auto.
  - constructor. apply All_All2 with (1 := X). intros d [Ht Hb]. repeat split; auto.
  - constructor. destruct p as [? []]; cbn in X |- *.
    1-3: constructor.
    destruct X as (Ht & Hd & Hv).
    constructor.
    + reflexivity.
    + exact Hd.
    + exact Ht.
    + now apply All_All2 with (1 := Hv).
Qed.

Lemma pe_ind_all (P : term -> term -> Type) :
  (forall na A b M', pe b (tApp (lift0 1 M') (tRel 0)) -> P b (tApp (lift0 1 M') (tRel 0)) ->
     P (tLambda na A b) M') ->
  (forall n, P (tRel n) (tRel n)) ->
  (forall i, P (tVar i) (tVar i)) ->
  (forall s, P (tSort s) (tSort s)) ->
  (forall c u, P (tConst c u) (tConst c u)) ->
  (forall ind u, P (tInd ind u) (tInd ind u)) ->
  (forall ind n u, P (tConstruct ind n u) (tConstruct ind n u)) ->
  (forall ev l l', All2 (Trel_conj pe P) l l' -> P (tEvar ev l) (tEvar ev l')) ->
  (forall na A A' M M', pe A A' -> P A A' -> pe M M' -> P M M' ->
     P (tLambda na A M) (tLambda na A' M')) ->
  (forall t t' u u', pe t t' -> P t t' -> pe u u' -> P u u' ->
     P (tApp t u) (tApp t' u')) ->
  (forall na a a' b b', pe a a' -> P a a' -> pe b b' -> P b b' ->
     P (tProd na a b) (tProd na a' b')) ->
  (forall na b b' ty ty' u u', pe b b' -> P b b' -> pe ty ty' -> P ty ty' ->
     pe u u' -> P u u' -> P (tLetIn na b ty u) (tLetIn na b' ty' u')) ->
  (forall ci p p' c c' brs brs',
     All2 (Trel_conj pe P) p.(pparams) p'.(pparams) ->
     p.(puinst) = p'.(puinst) ->
     p.(pcontext) = p'.(pcontext) ->
     pe p.(preturn) p'.(preturn) -> P p.(preturn) p'.(preturn) ->
     pe c c' -> P c c' ->
     All2 (fun x y => (x.(bcontext) = y.(bcontext))
                      × Trel_conj pe P x.(bbody) y.(bbody)) brs brs' ->
     P (tCase ci p c brs) (tCase ci p' c' brs')) ->
  (forall pr c c', pe c c' -> P c c' -> P (tProj pr c) (tProj pr c')) ->
  (forall mfix mfix' idx,
     All2 (fun d d' => Trel_conj pe P d.(dtype) d'.(dtype)
                       × Trel_conj pe P d.(dbody) d'.(dbody)
                       × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
     P (tFix mfix idx) (tFix mfix' idx)) ->
  (forall mfix mfix' idx,
     All2 (fun d d' => Trel_conj pe P d.(dtype) d'.(dtype)
                       × Trel_conj pe P d.(dbody) d'.(dbody)
                       × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg)) mfix mfix' ->
     P (tCoFix mfix idx) (tCoFix mfix' idx)) ->
  (forall p p', onPrims (Trel_conj pe P) eq p p' -> P (tPrim p) (tPrim p')) ->
  forall t t', pe t t' -> P t t'.
Proof.
  intros Heta HRel HVar HSort HConst HInd HCtor HEvar HLam HApp HProd HLet
         HCase HProj HFix HCoFix HPrim.
  fix aux 3. intros t t' H. move aux at top.
  destruct H as
    [ na A b M' pM
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
  - eapply Heta; [exact pM|apply aux; exact pM].
  - apply HRel.
  - apply HVar.
  - apply HSort.
  - apply HConst.
  - apply HInd.
  - apply HCtor.
  - eapply HEvar. revert l l' al.
    fix auxl 3. intros l l' Hl; destruct Hl.
    + constructor.
    + constructor; [split; [assumption|apply aux; assumption]|apply auxl; assumption].
  - eapply HLam; [exact pA|apply aux; exact pA|exact pM|apply aux; exact pM].
  - eapply HApp; [exact pf|apply aux; exact pf|exact pu|apply aux; exact pu].
  - eapply HProd; [exact pa|apply aux; exact pa|exact pb|apply aux; exact pb].
  - eapply HLet; [exact pb|apply aux; exact pb|exact pty|apply aux; exact pty
               |exact pu|apply aux; exact pu].
  - eapply HCase; [| exact eu | exact ectx | exact pret | apply aux; exact pret
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
  - eapply HProj; [exact pc|apply aux; exact pc].
  - eapply HFix. revert am. generalize mfix mfix'.
    fix auxl 3. intros l l' Hl; destruct Hl as [|x y ll ll' rh rt].
    + constructor.
    + constructor; [|apply auxl; exact rt].
      destruct rh as [Hty [Hbo [Hn Hr]]].
      split; [split; [exact Hty|apply aux; exact Hty]|].
      split; [split; [exact Hbo|apply aux; exact Hbo]|].
      split; assumption.
  - eapply HCoFix. revert am. generalize mfix mfix'.
    fix auxl 3. intros l l' Hl; destruct Hl as [|x y ll ll' rh rt].
    + constructor.
    + constructor; [|apply auxl; exact rt].
      destruct rh as [Hty [Hbo [Hn Hr]]].
      split; [split; [exact Hty|apply aux; exact Hty]|].
      split; [split; [exact Hbo|apply aux; exact Hbo]|].
      split; assumption.
  - eapply HPrim. destruct op; try solve [constructor].
    constructor;
      [ assumption
      | split; [assumption|apply aux; assumption]
      | split; [assumption|apply aux; assumption]
      | ].
    match goal with H : All2 pe _ _ |- _ => revert H end.
    generalize (array_value a) (array_value a').
    fix auxl 3. intros l l' Hl; destruct Hl.
    + constructor.
    + constructor; [split; [assumption|apply aux; assumption]|apply auxl; assumption].
Qed.

Lemma pe_lift np t t' (H : pe t t') : forall k, pe (lift np k t) (lift np k t').
Proof.
  induction H using pe_ind_all; intros k; cbn; try solve [econstructor; eauto].
  - (* eta *)
    apply pe_eta.
    have e : lift np (S k) (lift0 1 M') = lift0 1 (lift np k M').
    { rewrite (permute_lift M' np k 1 0 (Nat.le_0_l k)). now rewrite Nat.add_1_r. }
    rewrite -e. match goal with IH : forall k, pe (lift np k _) (lift np k _) |- _ => exact (IH (S k)) end.
  - constructor. apply All2_map.
    eapply All2_impl; [eassumption|]. intros x y [_ Hk]. apply Hk.
  - apply pe_Case; cbn.
    + apply All2_map. eapply All2_impl; [eassumption|]. intros x y [_ Hk]. apply Hk.
    + assumption.
    + assumption.
    + match goal with H : pcontext _ = pcontext _ |- _ => rewrite H end. eauto.
    + eauto.
    + apply All2_map. eapply All2_impl; [eassumption|].
      intros x y [Hc [_ Hk]]. cbn. split; [exact Hc|]. rewrite Hc. apply Hk.
  - constructor.
    match goal with H : All2 _ ?m ?m' |- _ => pose proof (All2_length H) as Hlen end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht|]. split; [rewrite Hlen; apply Hb|]. split; [exact Hn|exact Hr].
  - constructor.
    match goal with H : All2 _ ?m ?m' |- _ => pose proof (All2_length H) as Hlen end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht|]. split; [rewrite Hlen; apply Hb|]. split; [exact Hn|exact Hr].
  - constructor.
    match goal with
    | H : onPrims _ _ _ _ |- _ => destruct H as [i|fl|st|arr arr' Hlvl Hdef Hty Hval]
    end; cbn; try solve [constructor].
    constructor; cbn.
    + exact Hlvl.
    + destruct Hdef as [_ Hd]. apply Hd.
    + destruct Hty as [_ Ht]. apply Ht.
    + apply All2_map. eapply All2_impl; [exact Hval|]. intros x y [_ Hk]. apply Hk.
Qed.

Lemma pe_subst M M' (H : pe M M') :
  forall ss ss' k, All2 pe ss ss' -> pe (subst ss k M) (subst ss' k M').
Proof.
  induction H using pe_ind_all; intros ss ss' k HS; cbn; try solve [econstructor; eauto].
  - (* eta *)
    apply pe_eta. rewrite -commut_lift_subst.
    match goal with IH : forall ss ss' k, All2 pe ss ss' -> _ |- _ => exact (IH ss ss' (S k) HS) end.
  - destruct (le_lt_dec k n) as [Hle|Hlt].
    + assert (Hb : Nat.leb k n = true) by (apply Nat.leb_le; exact Hle).
      rewrite Hb.
      destruct (nth_error ss (n - k)) as [b|] eqn:Hs.
      * destruct (All2_nth_error_Some _ _ HS Hs) as (b' & Hs' & Hbb).
        rewrite Hs'. now apply pe_lift.
      * rewrite (All2_nth_error_None _ HS Hs). rewrite (All2_length HS). apply pe_Rel.
    + assert (Hb : Nat.leb k n = false) by (apply Nat.leb_gt; exact Hlt).
      rewrite Hb. apply pe_Rel.
  - constructor. apply All2_map.
    eapply All2_impl; [eassumption|]. intros x y [_ Hk]. apply Hk; assumption.
  - apply pe_Case; cbn.
    + apply All2_map. eapply All2_impl; [eassumption|]. intros x y [_ Hk]. apply Hk; assumption.
    + assumption.
    + assumption.
    + match goal with He : pcontext _ = pcontext _ |- _ => rewrite He end. eauto.
    + eauto.
    + apply All2_map. eapply All2_impl; [eassumption|].
      intros x y [Hc [_ Hk]]. cbn. split; [exact Hc|]. rewrite Hc. apply Hk; assumption.
  - constructor.
    match goal with
    | |- All2 _ (map _ ?m) (map _ ?m') =>
        match goal with He : All2 _ m m' |- _ => pose proof (All2_length He) as Hlen end
    end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht; assumption|].
    split; [rewrite Hlen; apply Hb; assumption|]. split; [exact Hn|exact Hr].
  - constructor.
    match goal with
    | |- All2 _ (map _ ?m) (map _ ?m') =>
        match goal with He : All2 _ m m' |- _ => pose proof (All2_length He) as Hlen end
    end.
    apply All2_map. eapply All2_impl; [eassumption|].
    intros x y [[_ Ht] [[_ Hb] [Hn Hr]]]. cbn.
    split; [apply Ht; assumption|].
    split; [rewrite Hlen; apply Hb; assumption|]. split; [exact Hn|exact Hr].
  - constructor.
    match goal with
    | He : onPrims _ _ _ _ |- _ => destruct He as [i|fl|st|arr arr' Hlvl Hdef Hty Hval]
    end; cbn; try solve [constructor].
    constructor; cbn.
    + exact Hlvl.
    + destruct Hdef as [_ Hd]. apply Hd; assumption.
    + destruct Hty as [_ Ht]. apply Ht; assumption.
    + apply All2_map. eapply All2_impl; [exact Hval|]. intros x y [_ Hk]. apply Hk; assumption.
Qed.

(** ** The parallel one-step postponement: statement, and its β-head case

  The statement the iteration needs ([Good] is [eta_safe] of every [red] reduct of
  [t], which typing gives through [typed_eta_safe] and E subject reduction):

    [pe t u -> red1 Σ Γ u v -> ∑ w, red1⁺ t w × pe w v].

  Its β-head case: [u] is a β-redex, possibly at the head of an application spine,
  and [t] is an η-expansion of it at any depth (the head λ itself η-expanded, the
  whole redex η-expanded, or both). It needs no invariant and closes by induction on
  the [pe] derivation of [t], jointly with the fact that a [pe]-source of a λ reduces
  to a λ (the η-expanded head λ is unfolded by β steps inside it). *)

Definition pe_postpone_statement (Σ : global_env) (Good : context -> term -> Type) : Type :=
  forall Γ t u v, Good Γ t -> on_free_vars xpredT u -> pe t u -> red1 Σ Γ u v ->
  ∑ w, trans_clos (red1 Σ Γ) t w × pe w v.

Lemma mkApps_tApp_is_tApp f a rest : ∑ g b, mkApps (tApp f a) rest = tApp g b.
Proof.
  induction rest as [|r rest _] using MRList.rev_ind; [now exists f, a|].
  rewrite mkApps_app. cbn. now do 2 eexists.
Qed.

Lemma trans_clos_map {A B} (R : A -> A -> Type) (S : B -> B -> Type) (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) -> forall x y, trans_clos R x y -> trans_clos S (f x) (f y).
Proof.
  intros hf x y h. induction h; [apply t_step; now apply hf|eapply t_trans; eassumption].
Qed.

Lemma rt_map {A B} (R : A -> A -> Type) (S : B -> B -> Type) (f : A -> B) :
  (forall x y, R x y -> S (f x) (f y)) -> forall x y, clos_refl_trans R x y -> clos_refl_trans S (f x) (f y).
Proof.
  intros hf x y h. induction h as [x y r|x|x y w _ IH1 _ IH2].
  - apply rt_step. now apply hf.
  - apply rt_refl.
  - eapply rt_trans; eassumption.
Qed.

Lemma rt_trans_clos {A} (R : A -> A -> Type) x y z :
  clos_refl_trans R x y -> trans_clos R y z -> trans_clos R x z.
Proof.
  intros h. induction h as [x y r|x|x y w _ IH1 _ IH2] in z |- *; intros h'.
  - eapply t_trans; [apply t_step; exact r|exact h'].
  - exact h'.
  - apply IH1. apply IH2. exact h'.
Qed.

Ltac pe_impossible :=
  split; intros * E;
  [ match type of E with
    | _ = mkApps (tApp ?f ?a) ?rest =>
        let g := fresh "g" in let b := fresh "b" in let e := fresh "e" in
        destruct (mkApps_tApp_is_tApp f a rest) as (g & b & e); rewrite e in E; discriminate E
    end
  | discriminate E ].

Section BetaHead.
  Context (Σ : global_env).

  Lemma pe_beta_head_and_lambda t u (h : pe t u) :
    (forall Γ na A' b' a' rest, u = mkApps (tApp (tLambda na A' b') a') rest ->
       ∑ w, trans_clos (red1 Σ Γ) t w × pe w (mkApps (b' {0 := a'}) rest)) ×
    (forall Γ na A' b', u = tLambda na A' b' ->
       ∑ nb B b0, clos_refl_trans (red1 Σ Γ) t (tLambda nb B b0) × pe b0 b').
  Proof.
    induction h as
      [ na A b M' hb IH
      | n | i | s | cst uu | ind uu | ind k uu
      | ev l l' al
      | na A A' M M' hA IHA hM IHM
      | f f' x x' hf IHf hx IHx
      | na a a' b b' ha IHa hb IHb
      | na b b' ty ty' x x' hb IHb hty IHty hx IHx
      | ci p p' c c' brs brs' apar eu ectx pret IHret pc IHc abrs
      | pr c c' pc IHc
      | mfix mfix' idx am
      | mfix mfix' idx am
      | pp pp' op ].
    all: try solve [pe_impossible].
    - (* pe_eta: the redex (or the λ) is η-expanded as a whole *)
      destruct IH as [IH1 _]. split.
      + intros Γ na' A' b' a' rest ->.
        destruct (IH1 (Γ ,, vass na A) na' (lift0 1 A') (lift 1 1 b') (lift0 1 a')
                    (map (lift0 1) rest ++ [tRel 0])) as (w & hr & hp).
        { rewrite mkApps_app lift_mkApps. reflexivity. }
        exists (tLambda na A w). split.
        * eapply (trans_clos_map _ _ (fun y => tLambda na A y)); [|exact hr].
          intros y z r. now apply abs_red_r.
        * apply pe_eta.
          have e : tApp (lift0 1 (mkApps (b' {0 := a'}) rest)) (tRel 0)
                   = mkApps ((lift 1 1 b') {0 := lift0 1 a'}) (map (lift0 1) rest ++ [tRel 0]).
          { rewrite mkApps_app lift_mkApps. cbn. f_equal. f_equal. apply distr_lift_subst10. }
          rewrite e. exact hp.
      + intros Γ na' A' b' ->.
        destruct (IH1 (Γ ,, vass na A) na' (lift0 1 A') (lift 1 1 b') (tRel 0) []) as (w & hr & hp).
        { reflexivity. }
        cbn in hp. rewrite C3R.subst_rel0_lift_id0 in hp.
        exists na, A, w. split; [|exact hp].
        apply clos_t_rt. eapply (trans_clos_map _ _ (fun y => tLambda na A y)); [|exact hr].
        intros y z r. now apply abs_red_r.
    - (* pe_Lambda: the λ itself *)
      split.
      + intros * E. match type of E with _ = mkApps (tApp ?f ?a) ?r =>
          destruct (mkApps_tApp_is_tApp f a r) as (g & b0 & e) end.
        rewrite e in E. discriminate E.
      + intros Γ na' A'' b'' E. injection E as _ _ ->.
        do 3 eexists. split; [apply rt_refl|exact hM].
    - (* pe_App: the redex, or a spine around it *)
      destruct IHf as [IHf1 IHf2]. split; [|intros * E; discriminate E].
      intros Γ na A' b' a' rest E.
      destruct rest as [|r rest _] using MRList.rev_ind.
      + cbn in E. injection E as -> ->.
        destruct (IHf2 Γ na A' b' eq_refl) as (nb & B & b0 & hr & hp).
        exists (b0 {0 := x}). split.
        * eapply rt_trans_clos.
          -- eapply (rt_map _ _ (fun y => tApp y x)); [|exact hr]. intros y z r. now apply app_red_l.
          -- apply t_step. apply red_beta.
        * exact (pe_subst _ _ hp [x] [a'] 0 (All2_cons hx All2_nil)).
      + rewrite mkApps_app in E. cbn in E. injection E as -> ->.
        destruct (IHf1 Γ na A' b' a' rest eq_refl) as (w & hr & hp).
        exists (tApp w x). split.
        * eapply (trans_clos_map _ _ (fun y => tApp y x)); [|exact hr].
          intros y z r0. now apply app_red_l.
        * rewrite mkApps_app. cbn. now apply pe_App.
  Qed.

  (** **The β-head case of the parallel one-step postponement: CLOSED.** *)
  Lemma pe_postpone_beta Γ t na A' b' a' :
    pe t (tApp (tLambda na A' b') a') -> ∑ w, trans_clos (red1 Σ Γ) t w × pe w (b' {0 := a'}).
  Proof. intros h. exact (fst (pe_beta_head_and_lambda _ _ h) Γ na A' b' a' [] eq_refl). Qed.

End BetaHead.

(** ** [eta1* = pe]

  [eta1_pe] and [pe_to_eta] give [eta1 ⊆ pe ⊆ eta1*]; [pe_eta1_closed] closes [pe]
  under one more [eta1] step at its target, so [eta_to_pe] gives [eta1* ⊆ pe]. *)

Lemma All2_OnOne2_compose {A} (Q S Q' : A -> A -> Type) l l' l'' :
  All2 Q l l' -> OnOne2 S l' l'' ->
  (forall x y z, Q x y -> S y z -> Q' x z) -> (forall x y, Q x y -> Q' x y) -> All2 Q' l l''.
Proof.
  intros ha ho hc hi. induction ho as [hd hd' tl hs|hd tl tl' ho IH] in l, ha |- *.
  - depelim ha. constructor; [eapply hc; eassumption|]. eapply All2_impl; [eassumption|exact hi].
  - depelim ha. constructor; [now apply hi|]. now apply IH.
Qed.

Lemma eta1_tPrim_inv pv v :
  eta1 (tPrim pv) v ->
  ∑ arr, (pv = (primArray; primArrayModel arr)) ×
    ((∑ value, (v = tPrim (primArray; primArrayModel (set_array_value arr value)))
                 × OnOne2 eta1 arr.(array_value) value)
     + (∑ d, (v = tPrim (primArray; primArrayModel (set_array_default arr d)))
                 × eta1 arr.(array_default) d)
     + (∑ ty, (v = tPrim (primArray; primArrayModel (set_array_type arr ty)))
                 × eta1 arr.(array_type) ty)).
Proof.
  intro H. remember (tPrim pv) as t eqn:Heq.
  destruct H; try discriminate Heq.
  all: injection Heq as e; subst; eexists; split; [reflexivity|].
  - left; left. eexists; split; [reflexivity|assumption].
  - left; right. eexists; split; [reflexivity|assumption].
  - right. eexists; split; [reflexivity|assumption].
Qed.

Lemma eta1_pe t u : eta1 t u -> pe t u.
Proof.
  induction 1 using eta1_ind_all.
  - (* eta_red *) apply pe_eta, pe_refl.
  - apply pe_Lambda; [assumption|apply pe_refl].
  - apply pe_Lambda; [apply pe_refl|assumption].
  - apply pe_LetIn; [assumption|apply pe_refl|apply pe_refl].
  - apply pe_LetIn; [apply pe_refl|assumption|apply pe_refl].
  - apply pe_LetIn; [apply pe_refl|apply pe_refl|assumption].
  - (* case param *)
    apply pe_Case; try reflexivity; try apply pe_refl.
    + eapply C3R.OnOne2_All2_refl;
        [eassumption | intros ?; apply pe_refl | intros x y [? ?]; assumption].
    + apply All2_same. intros; split; [reflexivity|apply pe_refl].
  - (* case return *)
    apply pe_Case; try reflexivity; try apply pe_refl.
    + apply All2_same. intros; apply pe_refl.
    + assumption.
    + apply All2_same. intros; split; [reflexivity|apply pe_refl].
  - (* case discr *)
    apply pe_Case; try reflexivity; try apply pe_refl.
    + apply All2_same. intros; apply pe_refl.
    + assumption.
    + apply All2_same. intros; split; [reflexivity|apply pe_refl].
  - (* case brs *)
    apply pe_Case; try reflexivity; try apply pe_refl.
    + apply All2_same. intros; apply pe_refl.
    + eapply C3R.OnOne2_All2_refl;
        [ eassumption
        | intros ?; split; [reflexivity|apply pe_refl]
        | intros x y [[? Hp] Hc]; split; [exact Hc|exact Hp] ].
  - apply pe_Proj; assumption.
  - apply pe_App; [assumption|apply pe_refl].
  - apply pe_App; [apply pe_refl|assumption].
  - apply pe_Prod; [assumption|apply pe_refl].
  - apply pe_Prod; [apply pe_refl|assumption].
  - apply pe_Evar.
    eapply C3R.OnOne2_All2_refl;
      [eassumption | intros ?; apply pe_refl | intros x y [? ?]; assumption].
  - apply pe_Fix.
    eapply C3R.OnOne2_All2_refl;
      [ eassumption | intros ?; repeat split; try apply pe_refl; reflexivity | ].
    intros x y [[He Hp] Heq]. injection Heq as Hdn Hdb Hrr.
    split; [exact Hp|split; [rewrite Hdb; apply pe_refl|split; [exact Hdn|exact Hrr]]].
  - apply pe_Fix.
    eapply C3R.OnOne2_All2_refl;
      [ eassumption | intros ?; repeat split; try apply pe_refl; reflexivity | ].
    intros x y [[He Hp] Heq]. injection Heq as Hdn Hdt Hrr.
    split; [rewrite Hdt; apply pe_refl|split; [exact Hp|split; [exact Hdn|exact Hrr]]].
  - apply pe_CoFix.
    eapply C3R.OnOne2_All2_refl;
      [ eassumption | intros ?; repeat split; try apply pe_refl; reflexivity | ].
    intros x y [[He Hp] Heq]. injection Heq as Hdn Hdb Hrr.
    split; [exact Hp|split; [rewrite Hdb; apply pe_refl|split; [exact Hdn|exact Hrr]]].
  - apply pe_CoFix.
    eapply C3R.OnOne2_All2_refl;
      [ eassumption | intros ?; repeat split; try apply pe_refl; reflexivity | ].
    intros x y [[He Hp] Heq]. injection Heq as Hdn Hdt Hrr.
    split; [rewrite Hdt; apply pe_refl|split; [exact Hp|split; [exact Hdn|exact Hrr]]].
  - apply pe_Prim. constructor; try reflexivity; try apply pe_refl.
    eapply C3R.OnOne2_All2_refl;
      [eassumption | intros ?; apply pe_refl | intros x y [? ?]; assumption].
  - apply pe_Prim. constructor.
    + reflexivity.
    + assumption.
    + apply pe_refl.
    + apply All2_same; intros; apply pe_refl.
  - apply pe_Prim. constructor.
    + reflexivity.
    + apply pe_refl.
    + assumption.
    + apply All2_same; intros; apply pe_refl.
Qed.

Lemma pe_to_eta t u : pe t u -> eta t u.
Proof.
  induction 1 using pe_ind_all.
  - (* η rule: the IH below the λ, then contract *)
    eapply rt_trans; [apply C3R.eta_absr; eassumption|apply rt_step; apply eta_red].
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply rt_refl.
  - apply C3R.eta_tEvar. eapply All2_impl; [eassumption|]. now intros x y [_ ?].
  - eapply rt_trans; [apply C3R.eta_absl; eassumption|apply C3R.eta_absr; eassumption].
  - eapply rt_trans; [apply C3R.eta_appl; eassumption|apply C3R.eta_appr; eassumption].
  - eapply rt_trans; [apply C3R.eta_prodl; eassumption|apply C3R.eta_prodr; eassumption].
  - eapply rt_trans; [apply C3R.eta_letd; eassumption|].
    eapply rt_trans; [apply C3R.eta_lett; eassumption|apply C3R.eta_letb; eassumption].
  - apply C3R.eta_tCase; auto.
    + eapply All2_impl; [eassumption|]. now intros x y [_ ?].
    + eapply All2_impl; [eassumption|]. now intros x y [? [_ ?]].
  - apply C3R.eta_proj; assumption.
  - apply C3R.eta_tFix. eapply All2_impl; [eassumption|].
    now intros x y [[_ ?] [[_ ?] [? ?]]].
  - apply C3R.eta_tCoFix. eapply All2_impl; [eassumption|].
    now intros x y [[_ ?] [[_ ?] [? ?]]].
  - match goal with H : onPrims _ _ _ _ |- _ =>
      destruct H as [i|fl|st|arr arr' Hlvl Hdef Hty Hval] end;
      try apply rt_refl.
    apply C3R.eta_tPrim_arr; cbn.
    + now apply Universe.make'_inj.
    + destruct Hdef as [_ ?]; assumption.
    + destruct Hty as [_ ?]; assumption.
    + eapply All2_impl; [exact Hval|]. now intros x y [_ ?].
Qed.

Lemma All2_Tconj_fst {A} (R P : A -> A -> Type) l l' : All2 (Trel_conj R P) l l' -> All2 R l l'.
Proof. intros h. eapply All2_impl; [exact h|]. intros x y [r _]. exact r. Qed.

Lemma All2_Tconj_step {A} (R S : A -> A -> Type) l l' l'' :
  All2 (Trel_conj R (fun x y => forall z, S y z -> R x z)) l l' -> OnOne2 S l' l'' -> All2 R l l''.
Proof.
  intros ha ho. eapply All2_OnOne2_compose; [exact ha|exact ho| |].
  - intros x y z [_ h] e. exact (h _ e).
  - intros x y [r _]. exact r.
Qed.

Definition prim_arr_of (p : prim_val term) : option (array_model term) :=
  match prim_val_model p with primArrayModel a => Some a | _ => None end.

(** [pe] is closed under one more [eta1] step at its target. *)
Lemma pe_eta1_closed t u : pe t u -> forall v, eta1 u v -> pe t v.
Proof.
  revert t u. apply (pe_ind_all (fun t u => forall v, eta1 u v -> pe t v)).
  - (* η rule: the step goes under the η-redex body *)
    intros na A b M' hb IH v he. apply pe_eta. apply IH. apply app_eta_l.
    exact (eta1_lift 1 _ _ he 0).
  - intros n v he. depelim he.
  - intros i v he. depelim he.
  - intros s v he. depelim he.
  - intros c uu v he. depelim he.
  - intros ind uu v he. depelim he.
  - intros ind n uu v he. depelim he.
  - intros ev l l' al v he. depelim he. apply pe_Evar. eapply All2_Tconj_step; eassumption.
  - intros na A A' M M' hA IHA hM IHM v he. depelim he.
    + (* the η-redex is the λ itself: absorbed by the η rule *)
      apply pe_eta. exact hM.
    + apply pe_Lambda; [now apply IHA|exact hM].
    + apply pe_Lambda; [exact hA|now apply IHM].
  - intros f f' x x' hf IHf hx IHx v he. depelim he.
    + apply pe_App; [now apply IHf|exact hx].
    + apply pe_App; [exact hf|now apply IHx].
  - intros na a a' b b' ha IHa hb IHb v he. depelim he.
    + apply pe_Prod; [now apply IHa|exact hb].
    + apply pe_Prod; [exact ha|now apply IHb].
  - intros na b b' ty ty' x x' hb IHb hty IHty hx IHx v he. depelim he.
    + apply pe_LetIn; [now apply IHb|exact hty|exact hx].
    + apply pe_LetIn; [exact hb|now apply IHty|exact hx].
    + apply pe_LetIn; [exact hb|exact hty|now apply IHx].
  - intros ci p p' c c' brs brs' apar eu ectx pret IHret pc IHc abrs v he.
    have hbrs : All2 (fun x y => bcontext x = bcontext y × pe (bbody x) (bbody y)) brs brs'.
    { eapply All2_impl; [exact abrs|]. intros x y [hc [q _]]. split; assumption. }
    depelim he.
    + apply pe_Case; cbn; [eapply All2_Tconj_step; eassumption|exact eu|exact ectx|exact pret|exact pc|exact hbrs].
    + apply pe_Case; cbn; [exact (All2_Tconj_fst _ _ _ _ apar)|exact eu|exact ectx|now apply IHret|exact pc|exact hbrs].
    + apply pe_Case; cbn; [exact (All2_Tconj_fst _ _ _ _ apar)|exact eu|exact ectx|exact pret|now apply IHc|exact hbrs].
    + apply pe_Case; cbn; [exact (All2_Tconj_fst _ _ _ _ apar)|exact eu|exact ectx|exact pret|exact pc|].
      eapply All2_OnOne2_compose; [exact abrs|eassumption| |].
      * intros x y z [hc [_ h]] [e hc']. split; [etransitivity; [exact hc|exact hc']|exact (h _ e)].
      * intros x y [hc [q _]]. split; assumption.
  - intros pr c c' pc IHc v he. depelim he. apply pe_Proj. now apply IHc.
  - intros mfix mfix' idx am v he. depelim he.
    + apply pe_Fix. eapply All2_OnOne2_compose; [exact am|eassumption| |].
      * intros x y z [[ht hPt] [[hb hPb] [hn hr]]] [e heq]. injection heq as e1 e2 e3.
        split; [exact (hPt _ e)|]. split; [rewrite -e2; exact hb|]. split; congruence.
      * intros x y [[ht _] [[hb _] [hn hr]]]. exact (ht, (hb, (hn, hr))).
    + apply pe_Fix. eapply All2_OnOne2_compose; [exact am|eassumption| |].
      * intros x y z [[ht hPt] [[hb hPb] [hn hr]]] [e heq]. injection heq as e1 e2 e3.
        split; [rewrite -e2; exact ht|]. split; [exact (hPb _ e)|]. split; congruence.
      * intros x y [[ht _] [[hb _] [hn hr]]]. exact (ht, (hb, (hn, hr))).
  - intros mfix mfix' idx am v he. depelim he.
    + apply pe_CoFix. eapply All2_OnOne2_compose; [exact am|eassumption| |].
      * intros x y z [[ht hPt] [[hb hPb] [hn hr]]] [e heq]. injection heq as e1 e2 e3.
        split; [exact (hPt _ e)|]. split; [rewrite -e2; exact hb|]. split; congruence.
      * intros x y [[ht _] [[hb _] [hn hr]]]. exact (ht, (hb, (hn, hr))).
    + apply pe_CoFix. eapply All2_OnOne2_compose; [exact am|eassumption| |].
      * intros x y z [[ht hPt] [[hb hPb] [hn hr]]] [e heq]. injection heq as e1 e2 e3.
        split; [rewrite -e2; exact ht|]. split; [exact (hPb _ e)|]. split; congruence.
      * intros x y [[ht _] [[hb _] [hn hr]]]. exact (ht, (hb, (hn, hr))).
  - intros p p' op v he.
    destruct op as [i|fl|st|a a' hl hd hty hval].
    1-3: destruct (eta1_tPrim_inv _ _ he) as (arr & e & _); discriminate e.
    destruct (eta1_tPrim_inv _ _ he) as (arr & e & hc).
    apply (f_equal prim_arr_of) in e. cbn in e. injection e as <-.
    destruct hd as [pd cd]; destruct hty as [pty cty].
    destruct hc as [[(value & -> & ho)|(d & -> & hd)]|(ty & -> & ht)];
      apply pe_Prim; constructor; cbn; try assumption.
    + eapply All2_Tconj_step; eassumption.
    + now apply cd.
    + exact (All2_Tconj_fst _ _ _ _ hval).
    + now apply cty.
    + exact (All2_Tconj_fst _ _ _ _ hval).
Qed.

Lemma eta_pe_step x y : eta x y -> forall t, pe t x -> pe t y.
Proof.
  intros h. induction h as [x y r|x|x y z _ IH1 _ IH2]; intros t hp.
  - exact (pe_eta1_closed _ _ hp _ r).
  - exact hp.
  - apply IH2, IH1, hp.
Qed.

(** **[eta1* = pe]: CLOSED.** *)
Theorem eta_iff_pe t u : (eta t u -> pe t u) × (pe t u -> eta t u).
Proof. split; [intros h; exact (eta_pe_step _ _ h t (pe_refl t))|exact (pe_to_eta t u)]. Qed.

(** ** The parallel root cases: a [pe]-source of a rigid spine

  The ι, projection, fixpoint and cofixpoint root cases of the parallel
  postponement need: a [pe]-source [c0] of a spine with a rigid head (constructor,
  fixpoint, cofixpoint, constant) reduces to a spine with a [pe]-related head and
  [pe]-related arguments. η-expanded heads, nested at any depth, are removed by β
  steps; a λ can appear only as a REDUCT of [c0], which the hypothesis [hnl]
  excludes (it holds of a typed scrutinee, a projection argument or a [rarg]-th
  fixpoint argument, by [typed_eta_safe] on the typed reducts of the term).

  The induction is on the [pe] derivation of the spine head, carrying the pending
  substitution [s] that the β steps build ([subst_cons_beta]); [head_unbound] says
  the target's spine head is not one of the substituted variables. *)

Definition rigid (h : term) : bool :=
  match h with tConstruct _ _ _ | tFix _ _ | tCoFix _ _ | tConst _ _ | tPrim _ => true | _ => false end.

Lemma rigid_notApp h : rigid h -> ~~ isApp h.
Proof. destruct h; cbn; auto. Qed.

Definition head_unbound (n : nat) (u : term) : bool :=
  match fst (decompose_app u) with tRel k => Nat.leb n k | _ => true end.

Lemma head_lift n k t : fst (decompose_app (lift n k t)) = lift n k (fst (decompose_app t)).
Proof.
  induction t; try reflexivity.
  change (fst (decompose_app_rec (lift n k t1) [lift n k t2]) = lift n k (fst (decompose_app_rec t1 [t2]))).
  rewrite !fst_decompose_app_rec. exact IHt1.
Qed.

Lemma head_unbound_lift n M : head_unbound n M -> head_unbound (S n) (lift0 1 M).
Proof. rewrite /head_unbound head_lift. destruct (fst (decompose_app M)); cbn; auto. Qed.

Lemma head_unbound_app n f x : head_unbound n (tApp f x) = head_unbound n f.
Proof.
  rewrite /head_unbound. change (decompose_app (tApp f x)) with (decompose_app_rec f [x]).
  now rewrite fst_decompose_app_rec.
Qed.

Lemma subst_cons_lift1 r s M : subst (r :: s) 0 (lift0 1 M) = subst s 0 M.
Proof.
  rewrite (subst_app_simpl [r] s 0 (lift0 1 M)).
  have e := commut_lift_subst_rec M s 1 0 0 (le_n 0). cbn in e |- *. rewrite -e.
  exact (subst1_lift0 _ _).
Qed.

Lemma subst_cons_beta r s b : (subst s 1 b) {0 := r} = subst (r :: s) 0 b.
Proof. symmetry. exact (subst_app_simpl [r] s 0 b). Qed.

Ltac rigid_contra :=
  match goal with
  | E : mkApps _ _ = mkApps ?hd _, hrig : is_true (rigid ?hd) |- _ =>
      exfalso; destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 _];
      subst hd; cbn in hrig; discriminate hrig
  end.

(** ** Occurrence counts and the domain-free size

  [occ_gen dom k t] counts the occurrences of [tRel k] in [t] (binder contexts of
  [tCase] are not terms that substitution touches, and are not counted); with
  [dom = true] it counts every occurrence, with [dom = false] it skips λ DOMAINS.
  [size'] is the term size with λ domains not counted.

  Why [size'] is principled: η-contraction [λx:A. M x ↦ M] drops only a λ domain [A]
  and the λ/application/variable nodes of the redex; it never drops or duplicates
  anything else. So the count of a variable OUTSIDE λ domains is invariant under η
  ([pe_occ]), and a measure that does not count domains cannot be inflated by
  substituting for a variable whose extra occurrences sit in domains, which is
  exactly what broke plain size ([literal_linearity_false]: the second occurrence of
  the bound variable is in the domain [P z]). If a third measure is ever needed, its
  invariance under whatever broke [size'] must be stated first. *)

Fixpoint lsum {A} (f : A -> nat) (l : list A) : nat :=
  match l with [] => 0 | a :: l => f a + lsum f l end.

Definition prim_lsum (f : term -> nat) (p : prim_val term) : nat :=
  match p.π2 return nat with
  | primIntModel _ => 0
  | primFloatModel _ => 0
  | primStringModel _ => 0
  | primArrayModel a => f a.(array_type) + f a.(array_default) + lsum f a.(array_value)
  end.

Fixpoint occ_gen (dom : bool) (k : nat) (t : term) {struct t} : nat :=
  match t with
  | tRel n => if Nat.eqb n k then 1 else 0
  | tEvar _ l => lsum (occ_gen dom k) l
  | tProd _ A B => occ_gen dom k A + occ_gen dom (S k) B
  | tLambda _ A b => (if dom then occ_gen dom k A else 0) + occ_gen dom (S k) b
  | tLetIn _ b B c => occ_gen dom k b + occ_gen dom k B + occ_gen dom (S k) c
  | tApp f a => occ_gen dom k f + occ_gen dom k a
  | tCase _ p c brs =>
      lsum (occ_gen dom k) p.(pparams) + occ_gen dom (#|p.(pcontext)| + k) p.(preturn)
      + occ_gen dom k c + lsum (fun br => occ_gen dom (#|br.(bcontext)| + k) br.(bbody)) brs
  | tProj _ c => occ_gen dom k c
  | tFix mfix _ => lsum (fun d => occ_gen dom k d.(dtype) + occ_gen dom (#|mfix| + k) d.(dbody)) mfix
  | tCoFix mfix _ => lsum (fun d => occ_gen dom k d.(dtype) + occ_gen dom (#|mfix| + k) d.(dbody)) mfix
  | tPrim p => prim_lsum (occ_gen dom k) p
  | _ => 0
  end.

Fixpoint size' (t : term) : nat :=
  match t with
  | tEvar _ l => S (lsum size' l)
  | tProd _ A B => S (size' A + size' B)
  | tLambda _ _ b => S (size' b)
  | tLetIn _ b B c => S (size' b + size' B + size' c)
  | tApp f a => S (size' f + size' a)
  | tCase _ p c brs =>
      S (lsum size' p.(pparams) + size' p.(preturn) + size' c + lsum (fun br => size' br.(bbody)) brs)
  | tProj _ c => S (size' c)
  | tFix mfix _ => S (lsum (fun d => size' d.(dtype) + size' d.(dbody)) mfix)
  | tCoFix mfix _ => S (lsum (fun d => size' d.(dtype) + size' d.(dbody)) mfix)
  | tPrim p => S (prim_lsum size' p)
  | _ => 1
  end.

(** ** The literal linearity claim is FALSE (building refutation, typable witness)

  The claim first stated for the size route: every [pe]-η body contains its bound
  variable exactly once, counting ALL occurrences. Witness: in
  [Γ = A : Prop, P : A → Prop, C : Prop, M' : Π z:A. P z → C], the term
  [W := λz:A. λy:P z. M' z y] [pe]-reduces to [M'] by two η steps, and the outer body
  [λy:P z. M' z y] contains [z] twice: in the domain [P z] and in [M' z y]. *)

Definition literal_linearity : Prop :=
  forall b M', pe b (tApp (lift0 1 M') (tRel 0)) -> occ_gen true 0 b = 1.

Definition lw_PA : term := tProd si_na (tRel 0) si_P.
Definition lw_TM : term := tProd si_na (tRel 2) (tProd si_na (tApp (tRel 2) (tRel 0)) (tRel 2)).
Definition lw_Γ : context := [vass si_na lw_TM; vass si_na si_P; vass si_na lw_PA; vass si_na si_P].
Definition lw_body : term := tLambda si_na (tApp (tRel 3) (tRel 0)) (tApp (tApp (tRel 2) (tRel 1)) (tRel 0)).
Definition lw_W : term := tLambda si_na (tRel 3) lw_body.

Lemma lw_body_pe : pe lw_body (tApp (lift0 1 (tRel 0)) (tRel 0)).
Proof. unfold lw_body. apply pe_eta. cbn. apply pe_refl. Qed.

Lemma lw_W_pe : pe lw_W (tRel 0).
Proof. unfold lw_W. apply pe_eta. exact lw_body_pe. Qed.

Lemma lw_body_occ : (occ_gen true 0 lw_body = 2) * (occ_gen false 0 lw_body = 1).
Proof. split; reflexivity. Qed.

Theorem literal_linearity_false : literal_linearity -> False.
Proof. intros H. have e := H _ _ lw_body_pe. rewrite (fst lw_body_occ) in e. discriminate e. Qed.

Section LinearityWitnessTyping.
  #[local] Existing Instance default_checker_flags.
  Context (Σ : global_env_ext).

  Lemma lw_ProdA Δ iA : wf_localE Σ Δ -> nth_error Δ iA = Some (vass si_na si_P) ->
    Σ ;;; Δ |-E tProd si_na (tRel iA) si_P : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
  Proof.
    intros hw hA.
    have hR : Σ ;;; Δ |-E tRel iA : tSort sProp by exact (typeE_Rel _ _ iA _ hw hA).
    apply typeE_Prod.
    - exact (iv_vass_s Σ Δ si_na (tRel iA) sProp hR eq_refl).
    - exact (iv_P_typed Σ _ (iv_wf_vass Σ Δ si_na (tRel iA) sProp hw hR eq_refl)).
  Qed.

  Lemma lw_Papp Δ iP x : wf_localE Σ Δ -> nth_error Δ iP = Some (vass si_na lw_PA) ->
    nth_error Δ (S iP) = Some (vass si_na si_P) -> Σ ;;; Δ |-E x : tRel (S iP) ->
    Σ ;;; Δ |-E tApp (tRel iP) x : si_P.
  Proof.
    intros hw hP hA hx.
    have hR := typeE_Rel _ _ iP _ hw hP. cbn in hR. rewrite Nat.add_0_r in hR.
    exact (typeE_App _ _ (tRel iP) si_na (tRel (S iP)) si_P _ x (lw_ProdA Δ (S iP) hw hA) hR hx).
  Qed.

  (** [Π z:A. Π y:P z. C] with [C], [P], [A] at indices [d], [d+1], [d+2]. *)
  Lemma lw_TM_at Δ d : wf_localE Σ Δ ->
    nth_error Δ d = Some (vass si_na si_P) -> nth_error Δ (S d) = Some (vass si_na lw_PA) ->
    nth_error Δ (S (S d)) = Some (vass si_na si_P) ->
    Σ ;;; Δ |-E tProd si_na (tRel (S (S d))) (tProd si_na (tApp (tRel (S (S d))) (tRel 0)) (tRel (S (S d))))
      : tSort (Sort.sort_of_product sProp (Sort.sort_of_product sProp sProp)).
  Proof.
    intros hw hC hP hA.
    have hR : Σ ;;; Δ |-E tRel (S (S d)) : tSort sProp by exact (typeE_Rel _ _ _ _ hw hA).
    have hwz := iv_wf_vass Σ Δ si_na (tRel (S (S d))) sProp hw hR eq_refl.
    have hz : Σ ;;; Δ ,, vass si_na (tRel (S (S d))) |-E tRel 0 : tRel (S (S (S d)))
      by exact (typeE_Rel _ _ 0 _ hwz eq_refl).
    have hPz := lw_Papp _ (S (S d)) (tRel 0) hwz hP hA hz.
    have hwzy := iv_wf_vass Σ _ si_na _ sProp hwz hPz eq_refl.
    apply typeE_Prod; [exact (iv_vass_s Σ Δ si_na _ sProp hR eq_refl)|].
    apply typeE_Prod; [exact (iv_vass_s Σ _ si_na _ sProp hPz eq_refl)|].
    exact (typeE_Rel _ _ (S (S d)) _ hwzy hC).
  Qed.

  Lemma lw_Γ_wf : wf_localE Σ lw_Γ.
  Proof.
    have hwA := iv_wf_P Σ [] localenv_nil.
    have hwP := iv_wf_vass Σ _ si_na lw_PA _ hwA (lw_ProdA _ 0 hwA eq_refl) eq_refl.
    have hwC := iv_wf_P Σ _ hwP.
    exact (iv_wf_vass Σ _ si_na lw_TM _ hwC (lw_TM_at _ 0 hwC eq_refl eq_refl eq_refl) eq_refl).
  Qed.

  (** **The witness is typable:** [W : Π z:A. Π y:P z. C] in [lw_Γ]. *)
  Theorem lw_W_typed :
    Σ ;;; lw_Γ |-E lw_W : tProd si_na (tRel 3) (tProd si_na (tApp (tRel 3) (tRel 0)) (tRel 3)).
  Proof.
    have hw := lw_Γ_wf.
    have hA : Σ ;;; lw_Γ |-E tRel 3 : tSort sProp by exact (typeE_Rel _ _ 3 _ hw eq_refl).
    have hwz := iv_wf_vass Σ _ si_na (tRel 3) sProp hw hA eq_refl.
    have hz : Σ ;;; lw_Γ ,, vass si_na (tRel 3) |-E tRel 0 : tRel 4 by exact (typeE_Rel _ _ 0 _ hwz eq_refl).
    have hPz := lw_Papp _ 3 (tRel 0) hwz eq_refl eq_refl hz.
    have hwzy := iv_wf_vass Σ _ si_na _ sProp hwz hPz eq_refl.
    set Γzy := (lw_Γ ,, vass si_na (tRel 3)) ,, vass si_na (tApp (tRel 3) (tRel 0)) in hwzy |- *.
    have hM : Σ ;;; Γzy |-E tRel 2 : tProd si_na (tRel 5) (tProd si_na (tApp (tRel 5) (tRel 0)) (tRel 5))
      by exact (typeE_Rel _ _ 2 _ hwzy eq_refl).
    have hz' : Σ ;;; Γzy |-E tRel 1 : tRel 5 by exact (typeE_Rel _ _ 1 _ hwzy eq_refl).
    have hMz : Σ ;;; Γzy |-E tApp (tRel 2) (tRel 1) : tProd si_na (tApp (tRel 4) (tRel 1)) (tRel 4)
      by exact (typeE_App _ _ _ si_na _ _ _ _ (lw_TM_at Γzy 3 hwzy eq_refl eq_refl eq_refl) hM hz').
    have hPz' := lw_Papp Γzy 4 (tRel 1) hwzy eq_refl eq_refl hz'.
    have hwzy' := iv_wf_vass Σ Γzy si_na _ sProp hwzy hPz' eq_refl.
    have hprod : Σ ;;; Γzy |-E tProd si_na (tApp (tRel 4) (tRel 1)) (tRel 4)
                   : tSort (Sort.sort_of_product sProp sProp).
    { apply typeE_Prod; [exact (iv_vass_s Σ _ si_na _ sProp hPz' eq_refl)|].
      exact (typeE_Rel _ _ 4 _ hwzy' eq_refl). }
    have hy : Σ ;;; Γzy |-E tRel 0 : tApp (tRel 4) (tRel 1) by exact (typeE_Rel _ _ 0 _ hwzy eq_refl).
    have hbody : Σ ;;; Γzy |-E tApp (tApp (tRel 2) (tRel 1)) (tRel 0) : tRel 3
      by exact (typeE_App _ _ _ si_na _ _ _ _ hprod hMz hy).
    unfold lw_W, lw_body. apply typeE_Lambda; [exact (iv_vass Σ _ si_na _ sProp hA eq_refl)|].
    apply typeE_Lambda; [exact (iv_vass Σ _ si_na _ sProp hPz eq_refl)|].
    exact hbody.
  Qed.

End LinearityWitnessTyping.

(** In a well-formed environment: [si_Σ]. *)
Lemma lw_W_typed_si :
  @wfE default_checker_flags si_Σ ×
  @typingE default_checker_flags si_Σ lw_Γ lw_W
    (tProd si_na (tRel 3) (tProd si_na (tApp (tRel 3) (tRel 0)) (tRel 3))).
Proof. split; [exact si_wfE|exact (lw_W_typed si_Σ)]. Qed.

(** **Plain [size] grows under the head β step of the witness** (22 → 27, with an
    argument [x] of size 10), while [size'] shrinks (18 → 15). The argument [x] is
    a closed-form term chosen only for its size; it is not typed. *)
Definition lw_x10 : term :=
  tLetIn si_na (tRel 0) (tRel 0) (tApp (tApp (tApp (tRel 0) (tRel 0)) (tRel 0)) (tRel 0)).

Theorem plain_size_grows_head_beta {cf : checker_flags} (Σ : global_env) :
  [× red1 Σ lw_Γ (tApp lw_W lw_x10) (lw_body {0 := lw_x10}),
     PCUICSize.size (tApp lw_W lw_x10) = 22, PCUICSize.size (lw_body {0 := lw_x10}) = 27,
     size' (tApp lw_W lw_x10) = 18 & size' (lw_body {0 := lw_x10}) = 15].
Proof. split; [unfold lw_W; apply red_beta|reflexivity|reflexivity|reflexivity|reflexivity]. Qed.

(** ** (a) [pe] preserves out-of-domain occurrence counts; a [pe]-η body has its
    bound variable exactly once outside domains *)

Lemma lsum_map {A B} (f : B -> nat) (g : A -> B) l : lsum f (map g l) = lsum (fun x => f (g x)) l.
Proof. induction l; cbn; congruence. Qed.

Lemma lsum_All_eq {A} (f g : A -> nat) l : All (fun x => f x = g x) l -> lsum f l = lsum g l.
Proof. induction 1; cbn; congruence. Qed.

Lemma lsum_All2_eq {A B} (f : A -> nat) (g : B -> nat) l l' :
  All2 (fun x y => f x = g y) l l' -> lsum f l = lsum g l'.
Proof. induction 1; cbn; congruence. Qed.

Lemma lsum_All_zero {A} (f : A -> nat) l : All (fun x => f x = 0) l -> lsum f l = 0.
Proof. induction 1; cbn; lia. Qed.

Lemma lsum_lin {A} (F G H : A -> nat) R l :
  All (fun x => F x + G x = H x + G x * R) l -> lsum F l + lsum G l = lsum H l + lsum G l * R.
Proof. induction 1; cbn; lia. Qed.

Ltac split4 := f_equal; [f_equal; [f_equal|]|].

Lemma occ_lift_ge d t : forall j i, j <= i -> occ_gen d (S i) (lift 1 j t) = occ_gen d i t.
Proof.
  induction t using term_forall_list_ind; intros jj ii hji; cbn; try reflexivity.
  - destruct (Nat.leb_spec0 jj n) as [h|h]; cbn; [reflexivity|].
    destruct (Nat.eqb_spec n (S ii)), (Nat.eqb_spec n ii); cbn; lia.
  - rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [eassumption|]. intros x h. now apply h.
  - rewrite IHt1 // IHt2 //; lia.
  - rewrite IHt1 // IHt2 //; lia.
  - rewrite IHt1 // IHt2 // IHt3 //; lia.
  - rewrite IHt1 // IHt2 //.
  - match goal with H : tCasePredProp _ _ _ |- _ => destruct H as (Hpars & _ & Hret) end.
    try unfold map_branches_k. split4.
    + rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [exact Hpars|]. intros x h. now apply h.
    + rewrite Nat.add_succ_r. apply Hret. lia.
    + match goal with H : forall j i, _ -> occ_gen d (S i) (lift 1 j ?c) = _ |- context [lift 1 jj ?c] =>
        now apply H end.
    + rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [eassumption|].
      intros x [_ h]. cbn. rewrite Nat.add_succ_r. apply h. lia.
  - rewrite IHt //.
  - rewrite lsum_map length_map. apply lsum_All_eq. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn. rewrite h1 // Nat.add_succ_r h2 //. lia.
  - rewrite lsum_map length_map. apply lsum_All_eq. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn. rewrite h1 // Nat.add_succ_r h2 //. lia.
  - destruct p as [? [i0|f0|s0|arr]]; cbn in *; try reflexivity.
    match goal with H : _ × _ × All _ _ |- _ => destruct H as (Ht & Hd & Hv) end.
    rewrite Ht // Hd // lsum_map.
    rewrite (lsum_All_eq _ (occ_gen d ii) _ (All_impl Hv (fun x h => h jj ii hji))). reflexivity.
Qed.

Lemma occ_lift_eq d t : forall j, occ_gen d j (lift 1 j t) = 0.
Proof.
  induction t using term_forall_list_ind; intros j; cbn; try reflexivity.
  - destruct (Nat.leb_spec0 j n) as [h|h]; cbn.
    + destruct (Nat.eqb_spec (S n) j); [lia|reflexivity].
    + destruct (Nat.eqb_spec n j); [lia|reflexivity].
  - rewrite lsum_map. apply lsum_All_zero. eapply All_impl; [eassumption|]. intros x h. apply h.
  - rewrite IHt1 IHt2. reflexivity.
  - rewrite IHt1 IHt2. now destruct d.
  - rewrite IHt1 IHt2 IHt3. reflexivity.
  - rewrite IHt1 IHt2. reflexivity.
  - match goal with H : tCasePredProp _ _ _ |- _ => destruct H as (Hpars & _ & Hret) end.
    try unfold map_branches_k.
    match goal with |- ?A + ?B + ?C + ?D = 0 =>
      enough (A = 0 /\ B = 0 /\ C = 0 /\ D = 0) by lia; split; [|split; [|split]] end.
    + rewrite lsum_map. apply lsum_All_zero. eapply All_impl; [exact Hpars|]. intros x h. apply h.
    + apply Hret.
    + match goal with H : forall j, occ_gen d j (lift 1 j _) = 0 |- _ => apply H end.
    + rewrite lsum_map. apply lsum_All_zero. eapply All_impl; [eassumption|]. intros x [_ h]. cbn. apply h.
  - rewrite IHt. reflexivity.
  - rewrite lsum_map length_map. apply lsum_All_zero. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn. rewrite h1 h2. reflexivity.
  - rewrite lsum_map length_map. apply lsum_All_zero. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn. rewrite h1 h2. reflexivity.
  - destruct p as [? [i0|f0|s0|arr]]; cbn in *; try reflexivity.
    match goal with H : _ × _ × All _ _ |- _ => destruct H as (Ht & Hd & Hv) end.
    rewrite Ht Hd lsum_map.
    rewrite (lsum_All_zero _ _ (All_impl Hv (fun x h => h j))). reflexivity.
Qed.

(** **(a), first half: [pe] preserves every variable's out-of-domain count.** *)
Lemma pe_occ t u : pe t u -> forall k, occ_gen false k t = occ_gen false k u.
Proof.
  revert t u. apply (pe_ind_all (fun t u => forall k, occ_gen false k t = occ_gen false k u)).
  - (* η: the dropped domain is not counted; the dropped variable is [tRel 0] *)
    intros na A b M' hb IH k. cbn. rewrite (IH (S k)). cbn.
    rewrite occ_lift_ge; [lia|]. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros ev l l' al k. cbn. apply lsum_All2_eq. eapply All2_impl; [exact al|]. intros x y [_ h]. apply h.
  - intros na A A' M M' hA IHA hM IHM k. cbn. now rewrite IHM.
  - intros f f' x x' hf IHf hx IHx k. cbn. now rewrite IHf IHx.
  - intros na a a' b b' ha IHa hb IHb k. cbn. now rewrite IHa IHb.
  - intros na b b' ty ty' x x' hb IHb hty IHty hx IHx k. cbn. now rewrite IHb IHty IHx.
  - intros ci p p' c c' brs brs' apar eu ectx pret IHret pc IHc abrs k. cbn.
    have e1 : lsum (occ_gen false k) (pparams p) = lsum (occ_gen false k) (pparams p').
    { apply lsum_All2_eq. eapply All2_impl; [exact apar|]. intros x y [_ h]. apply h. }
    have e2 : lsum (fun br => occ_gen false (#|bcontext br| + k) (bbody br)) brs
              = lsum (fun br => occ_gen false (#|bcontext br| + k) (bbody br)) brs'.
    { apply lsum_All2_eq. eapply All2_impl; [exact abrs|]. intros x y [hc [_ h]]. rewrite hc. apply h. }
    rewrite e1 e2 ectx IHret IHc. reflexivity.
  - intros pr c c' pc IHc k. cbn. now rewrite IHc.
  - intros mfix mfix' idx am k. cbn. rewrite (All2_length am).
    apply lsum_All2_eq. eapply All2_impl; [exact am|]. intros x y [[_ h1] [[_ h2] _]]. now rewrite h1 h2.
  - intros mfix mfix' idx am k. cbn. rewrite (All2_length am).
    apply lsum_All2_eq. eapply All2_impl; [exact am|]. intros x y [[_ h1] [[_ h2] _]]. now rewrite h1 h2.
  - intros p p' op k. destruct op as [i|f|s|a a' hl hd hty hval]; cbn; try reflexivity.
    destruct hd as [_ hd], hty as [_ hty]. rewrite hd hty.
    rewrite (lsum_All2_eq (occ_gen false k) (occ_gen false k) _ _ (All2_impl hval (fun x y h => snd h k))).
    reflexivity.
Qed.

(** **(a), second half: a [pe]-η body has its bound variable exactly once outside
    λ domains** (with every occurrence counted it can be twice:
    [literal_linearity_false]). *)
Corollary pe_eta_body_once b M' : pe b (tApp (lift0 1 M') (tRel 0)) -> occ_gen false 0 b = 1.
Proof. intros h. rewrite (pe_occ _ _ h 0). cbn. rewrite occ_lift_eq. reflexivity. Qed.

(** ** (b) [size'] strictly decreases at every head β step of a [pe]-η node *)

Lemma size'_lift t : forall n k, size' (lift n k t) = size' t.
Proof.
  induction t using term_forall_list_ind; intros n' k'; cbn; try reflexivity.
  - f_equal. rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [eassumption|]. intros x h. apply h.
  - now rewrite IHt1 IHt2.
  - now rewrite IHt2.
  - now rewrite IHt1 IHt2 IHt3.
  - now rewrite IHt1 IHt2.
  - match goal with H : tCasePredProp _ _ _ |- _ => destruct H as (Hpars & _ & Hret) end.
    try unfold map_branches_k. f_equal. split4.
    + rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [exact Hpars|]. intros x h. apply h.
    + apply Hret.
    + match goal with H : forall n k, size' (lift n k ?c) = size' ?c |- context [lift _ _ ?c] => apply H end.
    + rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [eassumption|]. intros x [_ h]. cbn. apply h.
  - now rewrite IHt.
  - f_equal. rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn. now rewrite h1 h2.
  - f_equal. rewrite lsum_map. apply lsum_All_eq. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn. now rewrite h1 h2.
  - destruct p as [? [i0|f0|s0|arr]]; cbn in *; try reflexivity.
    match goal with H : _ × _ × All _ _ |- _ => destruct H as (Ht & Hd & Hv) end.
    rewrite Ht Hd lsum_map.
    rewrite (lsum_All_eq _ size' _ (All_impl Hv (fun x h => h n' k'))). reflexivity.
Qed.

(** Substituting [r] for [tRel k] changes [size'] by [size' r - 1] per out-of-domain
    occurrence; occurrences in λ domains are not counted on either side. *)
Lemma size'_subst1 t : forall r k,
  size' (subst [r] k t) + occ_gen false k t = size' t + occ_gen false k t * size' r.
Proof.
  induction t using term_forall_list_ind; intros r k; cbn -[map].
  - destruct (Nat.leb_spec0 k n) as [h|h].
    + destruct (n - k) as [|m] eqn:e; cbn.
      * rewrite size'_lift. destruct (Nat.eqb_spec n k); cbn; lia.
      * rewrite ?nth_error_nil. cbn. destruct (Nat.eqb_spec n k); cbn; lia.
    + destruct (Nat.eqb_spec n k); cbn; lia.
  - reflexivity.
  - rewrite lsum_map.
    have := lsum_lin (fun x => size' (subst [r] k x)) (occ_gen false k) size' (size' r) l
              (All_impl X (fun x h => h r k)).
    lia.
  - reflexivity.
  - have h1 := IHt1 r k. have h2 := IHt2 r (S k). lia.
  - have h2 := IHt2 r (S k). lia.
  - have h1 := IHt1 r k. have h2 := IHt2 r k. have h3 := IHt3 r (S k). lia.
  - have h1 := IHt1 r k. have h2 := IHt2 r k. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - match goal with H : tCasePredProp _ _ _ |- _ => destruct H as (Hpars & _ & Hret) end.
    try unfold map_branches_k.
    match goal with
    |- S (?A' + ?B' + ?C' + ?D' + (?oA + ?oB + ?oC + ?oD)) = S (?sA + ?sB + ?sC + ?sD + _ * _) =>
      assert (hA : A' + oA = sA + oA * size' r);
      [|assert (hB : B' + oB = sB + oB * size' r);
        [|assert (hC : C' + oC = sC + oC * size' r);
          [|assert (hD : D' + oD = sD + oD * size' r)]]]
    end.
    + rewrite lsum_map. apply lsum_lin. eapply All_impl; [exact Hpars|]. intros x h. apply h.
    + apply Hret.
    + match goal with H : forall (r : term) (k : nat), _ |- _ => apply H end.
    + rewrite lsum_map. apply lsum_lin. eapply All_impl; [eassumption|]. intros x [_ h]. cbn. apply h.
    + lia.
  - have h := IHt r k. lia.
  - f_equal. rewrite lsum_map. apply lsum_lin. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn.
    match goal with |- context [subst [r] ?K' (dbody x)] => have e2 := h2 r K' end.
    have e1 := h1 r k. lia.
  - f_equal. rewrite lsum_map. apply lsum_lin. eapply All_impl; [eassumption|].
    intros x [h1 h2]. cbn.
    match goal with |- context [subst [r] ?K' (dbody x)] => have e2 := h2 r K' end.
    have e1 := h1 r k. lia.
  - destruct p as [? [i0|f0|s0|arr]]; cbn -[map] in *; try reflexivity.
    match goal with H : _ × _ × All _ _ |- _ => destruct H as (Ht & Hd & Hv) end.
    rewrite lsum_map.
    have hv := lsum_lin (fun x => size' (subst [r] k x)) (occ_gen false k) size' (size' r) _
                 (All_impl Hv (fun x h => h r k)).
    have ht := Ht r k. have hd := Hd r k. lia.
Qed.

(** **(b): at a head β step of a [pe]-η node, [size'] strictly decreases** (by 3). *)
Lemma head_beta_size'_decrease na A b M' r :
  pe b (tApp (lift0 1 M') (tRel 0)) -> size' (b {0 := r}) < size' (tApp (tLambda na A b) r).
Proof.
  intros h. have e := size'_subst1 b r 0. rewrite (pe_eta_body_once _ _ h) in e.
  unfold subst1. cbn [size']. lia.
Qed.

Lemma size'_mkApps_lt f g l : size' f < size' g -> size' (mkApps f l) < size' (mkApps g l).
Proof. induction l in f, g |- *; cbn; intros h; [exact h|]. apply IHl. cbn. lia. Qed.

Lemma subst_shift_eta_target s M :
  subst s 1 (tApp (lift0 1 M) (tRel 0)) = tApp (lift0 1 (subst s 0 M)) (tRel 0).
Proof. have e := commut_lift_subst_rec M s 1 0 0 (le_n 0). cbn in e |- *. now rewrite e. Qed.

Section RigidInv.
  Context (Σ : global_env) (Γ : context) (c0 : term).

  Definition rigid_inv_concl hd args :=
    ∑ h0 args0, red Σ Γ c0 (mkApps h0 args0) × notLam h0 × pe h0 hd × All2 pe args0 args.

  (** The λ alternative: [c0] reduces, by head β steps that never increase [size'],
      to a λ whose body is a [pe]-source of the η-expansion of the spine. *)
  Definition rigid_lam_concl hd args :=
    ∑ na A B, red Σ Γ c0 (tLambda na A B) × (size' (tLambda na A B) <= size' c0)
      × pe B (tApp (lift0 1 (mkApps hd args)) (tRel 0)).

  (** A [pe]-source of a rigid spine reduces either to a spine with a [pe]-related
      head and arguments, or to a λ (the η-expansion case). Every reduction step it
      takes is a head β step at a [pe]-η node, which strictly decreases [size']
      ([head_beta_size'_decrease]); the invariant [size' … <= size' c0] records it. *)
  Lemma pe_spine_or_lam t u : pe t u ->
    forall s s' rest rest', All2 pe s s' -> All2 pe rest rest' -> head_unbound #|s'| u ->
    red Σ Γ c0 (mkApps (subst s 0 t) rest) -> size' (mkApps (subst s 0 t) rest) <= size' c0 ->
    forall hd args, rigid hd -> mkApps (subst s' 0 u) rest' = mkApps hd args ->
    rigid_inv_concl hd args + rigid_lam_concl hd args.
  Proof.
    revert t u.
    apply (pe_ind_all (fun t u =>
      forall s s' rest rest', All2 pe s s' -> All2 pe rest rest' -> head_unbound #|s'| u ->
      red Σ Γ c0 (mkApps (subst s 0 t) rest) -> size' (mkApps (subst s 0 t) rest) <= size' c0 ->
      forall hd args, rigid hd -> mkApps (subst s' 0 u) rest' = mkApps hd args ->
      rigid_inv_concl hd args + rigid_lam_concl hd args)).
    - (* η-expanded head *)
      intros na A b M' hb IH s s' rest rest' hs hr hu hred hsz hd args hrig E.
      destruct rest as [|r rest0].
      + (* no argument: the term is the λ itself *)
        depelim hr. right. exists na, (subst s 0 A), (subst s 1 b).
        split; [exact hred|split; [exact hsz|]].
        cbn in E. rewrite -E -subst_shift_eta_target. exact (pe_subst _ _ hb s s' 1 hs).
      + (* an argument: one β step, then the body with the argument pushed on [s] *)
        destruct rest' as [|r' rest0']; [depelim hr|].
        depelim hr.
        have hs' : All2 pe (r :: s) (r' :: s') by (constructor; assumption).
        have hu' : head_unbound #|r' :: s'| (tApp (lift0 1 M') (tRel 0)).
        { rewrite head_unbound_app. now apply head_unbound_lift. }
        have hred' : red Σ Γ c0 (mkApps (subst (r :: s) 0 b) rest0).
        { eapply rt_trans; [exact hred|]. apply rt_step.
          rewrite -subst_cons_beta.
          change (mkApps (subst s 0 (tLambda na A b)) (r :: rest0))
            with (mkApps (tApp (tLambda na (subst s 0 A) (subst s 1 b)) r) rest0).
          apply red1_mkApps_f. apply red_beta. }
        have hlt : size' (mkApps (subst (r :: s) 0 b) rest0)
                   < size' (mkApps (subst s 0 (tLambda na A b)) (r :: rest0)).
        { rewrite -subst_cons_beta.
          change (mkApps (subst s 0 (tLambda na A b)) (r :: rest0))
            with (mkApps (tApp (tLambda na (subst s 0 A) (subst s 1 b)) r) rest0).
          apply size'_mkApps_lt. apply (head_beta_size'_decrease _ _ _ (subst s' 0 M')).
          rewrite -subst_shift_eta_target. exact (pe_subst _ _ hb s s' 1 hs). }
        have e : subst (r' :: s') 0 (tApp (lift0 1 M') (tRel 0)) = tApp (subst s' 0 M') r'.
        { cbn [subst]. rewrite subst_cons_lift1. cbn. now rewrite lift0_id. }
        apply (IH (r :: s) (r' :: s') rest0 rest0' hs' ltac:(assumption) hu' hred' ltac:(lia) hd args hrig).
        rewrite e. exact E.
    - (* a variable head: not substituted ([head_unbound]), so not rigid *)
      intros n s s' rest rest' hs hr hu hred hsz hd args hrig E. exfalso.
      rewrite /head_unbound /= in hu.
      have hn : nth_error s' n = None by (apply nth_error_None; apply Nat.leb_le; exact hu).
      have e : subst s' 0 (tRel n) = tRel (n - #|s'|) by (cbn; rewrite Nat.sub_0_r hn; reflexivity).
      rewrite e in E.
      destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 _]. subst hd. discriminate hrig.
    - intros; rigid_contra.
    - intros; rigid_contra.
    - (* constant *)
      intros c uu s s' rest rest' hs hr hu hred hsz hd args hrig E.
      destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 E2]. subst hd args.
      left. exists (tConst c uu), rest.
      split; [exact hred|split; [reflexivity|split; [apply pe_Const|exact hr]]].
    - intros; rigid_contra.
    - (* constructor *)
      intros ind k uu s s' rest rest' hs hr hu hred hsz hd args hrig E.
      destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 E2]. subst hd args.
      left. exists (tConstruct ind k uu), rest.
      split; [exact hred|split; [reflexivity|split; [apply pe_Construct|exact hr]]].
    - intros; rigid_contra.
    - intros; rigid_contra.
    - (* application: push the argument on the stack *)
      intros f f' x x' hf IHf hx IHx s s' rest rest' hs hr hu hred hsz hd args hrig E.
      rewrite head_unbound_app in hu.
      exact (IHf s s' (subst s 0 x :: rest) (subst s' 0 x' :: rest') hs
               (All2_cons (pe_subst _ _ hx s s' 0 hs) hr) hu hred hsz hd args hrig E).
    - intros; rigid_contra.
    - intros; rigid_contra.
    - intros; rigid_contra.
    - intros; rigid_contra.
    - (* fixpoint *)
      intros mfix mfix' idx am s s' rest rest' hs hr hu hred hsz hd args hrig E.
      destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 E2]. subst hd args.
      left. exists (subst s 0 (tFix mfix idx)), rest.
      split; [exact hred|split; [reflexivity|split; [|exact hr]]].
      apply pe_subst; [|exact hs]. apply pe_Fix.
      eapply All2_impl; [exact am|]. intros d d' [[ht _] [[hb _] [hn hrr]]]. exact (ht, (hb, (hn, hrr))).
    - (* cofixpoint *)
      intros mfix mfix' idx am s s' rest rest' hs hr hu hred hsz hd args hrig E.
      destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 E2]. subst hd args.
      left. exists (subst s 0 (tCoFix mfix idx)), rest.
      split; [exact hred|split; [reflexivity|split; [|exact hr]]].
      apply pe_subst; [|exact hs]. apply pe_CoFix.
      eapply All2_impl; [exact am|]. intros d d' [[ht _] [[hb _] [hn hrr]]]. exact (ht, (hb, (hn, hrr))).
    - (* primitive value *)
      intros pp pp' op s s' rest rest' hs hr hu hred hsz hd args hrig E.
      destruct (mkApps_eq_inj E eq_refl (rigid_notApp _ hrig)) as [E1 E2]. subst hd args.
      left. exists (subst s 0 (tPrim pp)), rest.
      split; [exact hred|split; [reflexivity|split; [|exact hr]]].
      apply pe_subst; [|exact hs]. apply pe_Prim.
      destruct op as [i|f|st|a a' hl hd' hty hval]; constructor; try assumption.
      + exact (fst hd').
      + exact (fst hty).
      + eapply All2_impl; [exact hval|]. intros x y [h _]. exact h.
  Qed.

  Lemma pe_spine_or_lam_top u hd args :
    pe c0 u -> rigid hd -> u = mkApps hd args -> rigid_inv_concl hd args + rigid_lam_concl hd args.
  Proof.
    intros h hrig ->.
    have hu : head_unbound #|@nil term| (mkApps hd args).
    { rewrite /head_unbound decompose_app_mkApps; [exact (rigid_notApp _ hrig)|].
      destruct hd; cbn; reflexivity. }
    have hred : red Σ Γ c0 (mkApps (subst [] 0 c0) []) by (cbn; rewrite subst_empty; apply rt_refl).
    have hsz : size' (mkApps (subst [] 0 c0) []) <= size' c0 by (cbn; rewrite subst_empty; lia).
    exact (pe_spine_or_lam _ _ h [] [] [] [] All2_nil All2_nil hu hred hsz hd args hrig
             ltac:(cbn; now rewrite subst_empty)).
  Qed.

  (** **The spine inversion the parallel ι / projection / cofixpoint root cases
      need: CLOSED** (given [hnl], which excludes the λ alternative). *)
  Corollary pe_rigid_spine (hnl : forall c', red Σ Γ c0 c' -> notLam c') u hd args :
    pe c0 u -> rigid hd -> u = mkApps hd args -> rigid_inv_concl hd args.
  Proof.
    intros h hrig hE.
    destruct (pe_spine_or_lam_top u hd args h hrig hE) as [hs|(na & A & B & hr & _ & _)]; [exact hs|].
    exfalso. specialize (hnl _ hr). cbn in hnl. discriminate hnl.
  Qed.

End RigidInv.

(** ** [pe] on contexts, [expand_lets] and [iota_red] (copied from the [C3R.peta_*]
    lemmas, with [pe] for [peta]) *)

Definition pe_decl (d d' : context_decl) : Type :=
  match decl_body d, decl_body d' with
  | Some b, Some b' => pe b b'
  | None, None => unit
  | _, _ => Empty_set
  end.

Definition pe_ctx := All2 pe_decl.

Lemma pe_ctx_assumptions Γ Δ : pe_ctx Γ Δ -> context_assumptions Γ = context_assumptions Δ.
Proof.
  induction 1 as [|d d' Γ Δ Hd H IH]; [reflexivity|].
  destruct d as [na [b|] ty], d' as [na' [b'|] ty']; cbn in *; try destruct Hd; congruence.
Qed.

Lemma pe_subst_context ss ss' k ctx :
  All2 pe ss ss' -> pe_ctx (subst_context ss k ctx) (subst_context ss' k ctx).
Proof.
  intros Hs. induction ctx as [|d ctx IH]; [constructor|].
  rewrite !subst_context_snoc. constructor; [|exact IH].
  destruct d as [na [b|] ty]; cbn; [|exact tt].
  apply pe_subst; [apply pe_refl|exact Hs].
Qed.

Lemma pe_inst_case_context params params' puinst ctx :
  All2 pe params params' ->
  pe_ctx (inst_case_context params puinst ctx) (inst_case_context params' puinst ctx).
Proof. intros H. unfold inst_case_context. apply pe_subst_context. now apply All2_rev. Qed.

Lemma pe_extended_subst Γ Γ' n : pe_ctx Γ Γ' -> All2 pe (extended_subst Γ n) (extended_subst Γ' n).
Proof.
  intros H. induction H as [|d d' Γ Γ' Hd H IH] in n |- *; [constructor|].
  destruct d as [na [b|] ty], d' as [na' [b'|] ty']; cbn in Hd |- *.
  - constructor; [|apply IH].
    rewrite (pe_ctx_assumptions _ _ H) !extended_subst_length (All2_length H).
    apply pe_subst; [exact (pe_lift _ _ _ Hd _)|apply IH].
  - destruct Hd.
  - destruct Hd.
  - constructor; [apply pe_Rel|apply IH].
Qed.

Lemma pe_expand_lets Γ Γ' t t' : pe_ctx Γ Γ' -> pe t t' -> pe (expand_lets Γ t) (expand_lets Γ' t').
Proof.
  intros H Ht. unfold expand_lets, expand_lets_k.
  rewrite (pe_ctx_assumptions _ _ H) (All2_length H).
  apply pe_subst; [now apply pe_lift|now apply pe_extended_subst].
Qed.

Lemma pe_iota_red npar p p' args args' br br' :
  All2 pe args args' -> All2 pe (pparams p) (pparams p') ->
  puinst p = puinst p' -> bcontext br = bcontext br' -> pe (bbody br) (bbody br') ->
  pe (iota_red npar p args br) (iota_red npar p' args' br').
Proof.
  intros Ha Hp Hu Hc Hb. unfold iota_red.
  apply pe_subst; [|now apply All2_rev, All2_skipn].
  apply pe_expand_lets; [|exact Hb].
  unfold inst_case_branch_context. rewrite Hu Hc.
  now apply pe_inst_case_context.
Qed.

(** *** The premise [hnl] of the ι, projection, cofix-case and cofix-proj roots

  Each of these roots assumes [hnl]: NO REDUCT of the scrutinee (or projection
  argument) [c0] is a λ. These roots are NOT unconditional. For a typed source,
  [hnl] follows from two halves, and only the first is proved here:
  - (i) TYPING ⇒ INVARIANT: [typed_eta_safe] (this file, given the FORECAST-ONLY
    hypothesis [fix_rarg_inductive]) says that a typed term is [eta_safe], and so
    has no λ in scrutinee or projection-argument position. This half needs no
    subject reduction.
  - (ii) PRESERVATION: every reduct of the typed source is still typed. That is E
    subject reduction, forecast row T1. It is neither proved nor used in this
    file. Only with (ii) does (i) apply to each reduct of [c0] and give [hnl].

  Measured time per root group (wall clock, from commit times; build cycles of about
  1 min each included):
  - β-head and the [pe] definition: 11 min (11:36–11:47Z);
  - [eta1* = pe]: 8 min (12:02–12:10Z);
  - rigid-spine inversion: 7 min (12:10–12:17Z);
  - ι and projection roots, with the [pe_ctx] copies: 7 min (12:18–12:25Z);
  - cofix-case and cofix-proj roots, with their helpers: 6 min (12:31–12:37Z);
  - measure lemmas (literal-linearity refutation with the typed witness, plain-size
    growth, [pe_occ], [pe_eta_body_once], [size'_subst1],
    [head_beta_size'_decrease]): 26 min (12:38–13:04Z);
  - λ alternative of the inversion ([pe_spine_or_lam]): 5 min (13:04–13:09Z);
  - fixpoint root: 7 min (13:09–13:16Z);
  - primitive-operation root: 5 min (13:17–13:22Z);
  - assembly infrastructure ([pe_ctx] helpers, [Good] transport per position,
    [OnOne2_postpone]): 15 min (13:26–13:41Z);
  - the assembled postponement ([pe_postpone], η-at-root and every congruence case):
    6 min (13:41–13:47Z);
  - scoping transfer along [pe] ([pe_on_free_vars]) and the iteration
    ([pe_red_postpone]): 5 min (13:47–13:52Z).

  Mirror screening, measured 2026-10-29: of 3 named landed mirrors tried for B1
  ([eta1_on_free_vars] → transfer: paid; [red1_upto_domain_r_fixed] → backsim: paid;
  [HR_strong_commutation_modulo] → iteration: did NOT instantiate, reasons above,
  cost ~5 min), 2 paid. A named mirror is a hypothesis to try first, not a guarantee.

  Induction principles, one per lemma. No lemma calls another lemma recursively,
  and calls between lemmas follow a fixed acyclic order:
  - [pe_beta_head_and_lambda] and [pe_spine_or_lam]: induction on the [pe] derivation;
  - [pe_eta1_closed], [eta1_pe], [pe_to_eta], [pe_occ]: induction on the [pe] or
    [eta1] derivation;
  - [occ_lift_ge], [occ_lift_eq], [size'_lift], [size'_subst1]: induction on the term;
  - [eta_pe_step]: induction on [clos_refl_trans];
  - [pe_fix_root_n], [pe_prim_root_n], [no_pe_source_app_prim_n]: induction on a
    bound [n >= size' t], whose only recursive call is on the body of a λ-reduct
    with its decrease proved at the call.
  The ι, projection and cofix roots do no induction of their own: they call
  [pe_rigid_spine]. *)

(** **The parallel ι root case: CLOSED, under [hnl].** The source is a [pe_Case]
    whose scrutinee [c0] is a [pe]-source of the constructor application. The
    [pe_eta] source, an η-expansion of the whole redex, is the generic
    η-at-the-root case, as in [pp_root]. *)
Lemma pe_iota_root Σ Γ ci p0 c0 brs0 p c uu args brs br :
  (* PREMISE hnl, NOT unconditional: (i) typed_eta_safe, typing ⇒ invariant, proved here
     with no SR; (ii) preservation of typing along red, E subject reduction, forecast T1,
     not proved here. *)
  (forall c', red Σ Γ c0 c' -> notLam c') ->
  All2 pe p0.(pparams) p.(pparams) -> p0.(puinst) = p.(puinst) ->
  pe c0 (mkApps (tConstruct ci.(ci_ind) c uu) args) ->
  All2 (fun x y => bcontext x = bcontext y × pe (bbody x) (bbody y)) brs0 brs ->
  nth_error brs c = Some br -> #|args| = (ci.(ci_npar) + context_assumptions br.(bcontext))%nat ->
  ∑ w, trans_clos (red1 Σ Γ) (tCase ci p0 c0 brs0) w × pe w (iota_red ci.(ci_npar) p args br).
Proof.
  intros hnl hpar hu hc hbrs hnth hlen.
  destruct (pe_rigid_spine Σ Γ c0 hnl _ (tConstruct ci.(ci_ind) c uu) args hc eq_refl eq_refl)
    as (h0 & args0 & hred & hnlh & hph & hargs).
  depelim hph; [cbn in hnlh; discriminate hnlh|].
  destruct (All2_nth_error_Some_r c br hbrs hnth) as (br0 & hnth0 & (hctx & hbody)).
  exists (iota_red ci.(ci_npar) p0 args0 br0). split.
  - eapply rt_trans_clos; [apply red_case_c; exact hred|].
    apply t_step. eapply red_iota; [exact hnth0|].
    rewrite (All2_length hargs) hctx. exact hlen.
  - now apply pe_iota_red.
Qed.

(** **The parallel projection root case: CLOSED, under [hnl]** (same shape as
    [pe_iota_root]). *)
Lemma pe_proj_root Σ Γ pr c0 uu args arg :
  (* PREMISE hnl: (i) typed_eta_safe (proved, no SR) + (ii) E subject reduction (forecast T1). *)
  (forall c', red Σ Γ c0 c' -> notLam c') ->
  pe c0 (mkApps (tConstruct pr.(proj_ind) 0 uu) args) ->
  nth_error args (pr.(proj_npars) + pr.(proj_arg)) = Some arg ->
  ∑ w, trans_clos (red1 Σ Γ) (tProj pr c0) w × pe w arg.
Proof.
  intros hnl hc hnth.
  destruct (pe_rigid_spine Σ Γ c0 hnl _ (tConstruct pr.(proj_ind) 0 uu) args hc eq_refl eq_refl)
    as (h0 & args0 & hred & hnlh & hph & hargs).
  depelim hph; [cbn in hnlh; discriminate hnlh|].
  destruct (All2_nth_error_Some_r _ arg hargs hnth) as (arg0 & hnth0 & hp).
  exists arg0. split; [|exact hp].
  eapply rt_trans_clos; [apply red_proj_c; exact hred|].
  apply t_step. now apply red_proj.
Qed.

Lemma pe_mkApps f f' args args' : pe f f' -> All2 pe args args' -> pe (mkApps f args) (mkApps f' args').
Proof.
  intros Hf Ha. induction Ha in f, f', Hf |- *; cbn; [assumption|].
  apply IHHa. now apply pe_App.
Qed.

Definition pe_def (d d' : def term) : Type :=
  pe d.(dtype) d'.(dtype) × pe d.(dbody) d'.(dbody) × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg).

Lemma pe_fix_subst mfix mfix' : All2 pe_def mfix mfix' -> All2 pe (fix_subst mfix) (fix_subst mfix').
Proof.
  intros H. pose proof (All2_length H) as Hl.
  unfold fix_subst. rewrite Hl.
  generalize #|mfix'|. intros n. induction n; cbn; constructor; auto.
  now apply pe_Fix.
Qed.

Lemma pe_cofix_subst mfix mfix' : All2 pe_def mfix mfix' -> All2 pe (cofix_subst mfix) (cofix_subst mfix').
Proof.
  intros H. pose proof (All2_length H) as Hl.
  unfold cofix_subst. rewrite Hl.
  generalize #|mfix'|. intros n. induction n; cbn; constructor; auto.
  now apply pe_CoFix.
Qed.

(** Unfolding read backwards: the [pe]-source of an unfoldable (co)fixpoint unfolds
    to a [pe]-source of the unfolding. *)
Lemma pe_unfold_fix_back mfix0 mfix idx narg fn :
  All2 pe_def mfix0 mfix -> unfold_fix mfix idx = Some (narg, fn) ->
  ∑ fn0, unfold_fix mfix0 idx = Some (narg, fn0) × pe fn0 fn.
Proof.
  intros ha. unfold unfold_fix.
  destruct (nth_error mfix idx) as [d|] eqn:hd; [|discriminate].
  intros [= <- <-].
  destruct (All2_nth_error_Some_r idx d ha hd) as (d0 & hd0 & (_ & hb & _ & hr)).
  rewrite hd0. eexists; split; [now rewrite hr|].
  apply (pe_subst _ _ hb). now apply pe_fix_subst.
Qed.

Lemma pe_unfold_cofix_back mfix0 mfix idx narg fn :
  All2 pe_def mfix0 mfix -> unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ fn0, unfold_cofix mfix0 idx = Some (narg, fn0) × pe fn0 fn.
Proof.
  intros ha. unfold unfold_cofix.
  destruct (nth_error mfix idx) as [d|] eqn:hd; [|discriminate].
  intros [= <- <-].
  destruct (All2_nth_error_Some_r idx d ha hd) as (d0 & hd0 & (_ & hb & _ & hr)).
  rewrite hd0. eexists; split; [now rewrite hr|].
  apply (pe_subst _ _ hb). now apply pe_cofix_subst.
Qed.

(** **The parallel cofix-case root case: CLOSED, under [hnl]** (same shape as
    [pe_iota_root]; the scrutinee's cofixpoint is unfolded through
    [pe_unfold_cofix_back]). *)
Lemma pe_cofix_case_root Σ Γ ip p0 c0 brs0 p mfix idx args narg fn brs :
  (* PREMISE hnl: (i) typed_eta_safe (proved, no SR) + (ii) E subject reduction (forecast T1). *)
  (forall c', red Σ Γ c0 c' -> notLam c') ->
  All2 pe p0.(pparams) p.(pparams) -> p0.(puinst) = p.(puinst) -> p0.(pcontext) = p.(pcontext) ->
  pe p0.(preturn) p.(preturn) ->
  pe c0 (mkApps (tCoFix mfix idx) args) ->
  All2 (fun x y => bcontext x = bcontext y × pe (bbody x) (bbody y)) brs0 brs ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ w, trans_clos (red1 Σ Γ) (tCase ip p0 c0 brs0) w × pe w (tCase ip p (mkApps fn args) brs).
Proof.
  intros hnl hpar hu hctx hret hc hbrs hunf.
  destruct (pe_rigid_spine Σ Γ c0 hnl _ (tCoFix mfix idx) args hc eq_refl eq_refl)
    as (h0 & args0 & hred & hnlh & hph & hargs).
  depelim hph; [cbn in hnlh; discriminate hnlh|].
  match goal with H : All2 _ ?m mfix |- _ =>
    destruct (pe_unfold_cofix_back m mfix idx narg fn H hunf) as (fn0 & hu0 & hfn) end.
  exists (tCase ip p0 (mkApps fn0 args0) brs0). split.
  - eapply rt_trans_clos; [apply red_case_c; exact hred|].
    apply t_step. eapply red_cofix_case. exact hu0.
  - apply pe_Case; [exact hpar|exact hu|exact hctx|exact hret|apply pe_mkApps; [exact hfn|exact hargs]|exact hbrs].
Qed.

(** **The parallel cofix-proj root case: CLOSED, under [hnl].** *)
Lemma pe_cofix_proj_root Σ Γ pr c0 mfix idx args narg fn :
  (* PREMISE hnl: (i) typed_eta_safe (proved, no SR) + (ii) E subject reduction (forecast T1). *)
  (forall c', red Σ Γ c0 c' -> notLam c') ->
  pe c0 (mkApps (tCoFix mfix idx) args) ->
  unfold_cofix mfix idx = Some (narg, fn) ->
  ∑ w, trans_clos (red1 Σ Γ) (tProj pr c0) w × pe w (tProj pr (mkApps fn args)).
Proof.
  intros hnl hc hunf.
  destruct (pe_rigid_spine Σ Γ c0 hnl _ (tCoFix mfix idx) args hc eq_refl eq_refl)
    as (h0 & args0 & hred & hnlh & hph & hargs).
  depelim hph; [cbn in hnlh; discriminate hnlh|].
  match goal with H : All2 _ ?m mfix |- _ =>
    destruct (pe_unfold_cofix_back m mfix idx narg fn H hunf) as (fn0 & hu0 & hfn) end.
  exists (tProj pr (mkApps fn0 args0)). split.
  - eapply rt_trans_clos; [apply red_proj_c; exact hred|].
    apply t_step. eapply red_cofix_proj. exact hu0.
  - apply pe_Proj. apply pe_mkApps; [exact hfn|exact hargs].
Qed.

(** ** Status of the parallel one-step postponement ([pe_postpone_statement])

  Closed above and below: the β-head case ([pe_postpone_beta], no invariant), the
  ι, projection, cofix-case and cofix-proj root cases (under [hnl]), their shared
  spine inversion ([pe_rigid_spine]), and the fixpoint and primitive-operation
  roots ([pe_fix_root], [pe_prim_root], under [Good], by induction on [size']).

  Why the fixpoint and primitive roots need [size']: the redex spine may have a
  PRODUCT type, so [hnl] does not hold of its source, and a source such as
  [(λz. λy. G z y) x] (with [G = mkApps (tFix mfix idx) args']) β-reduces to the
  η-expansion [λy. G x y] of the redex, never to the redex spine. The reduct's [pe]
  derivation is not a subderivation of the source's. Plain [size] does NOT work
  ([literal_linearity_false], [plain_size_grows_head_beta]).

  Open (not started, on hold):
  - the generic η-at-the-root case ([pe_eta] source, any [red1] step): [pp_root] with
    the IH on the body;
  - the congruence cases, with [red1] transported along [pe_ctx] (above): [red_rel]
    in a let body unfolds a [pe]-related body ([pe_lift]); case branches use
    [pe_inst_case_context], fixpoint bodies the [fix_context] analogue. *)

(** ** The parallel fixpoint root, by well-founded induction on [size']

  [Good Σ Γ t]: every reduct of [t] is [eta_safe]. For a typed [t] it is the same
  two halves as [hnl]: [typed_eta_safe] (typing ⇒ invariant, no SR) and E subject
  reduction (forecast row T1, preservation; not used here).

  Recursion structure of [pe_fix_root_n] (induction on a bound [n] with
  [size' t <= n]): the ONLY recursive call is on [B], the BODY of a λ that [t]
  reduces to by head β steps ([pe_spine_or_lam]), against the lifted fixpoint redex
  with one more argument [tRel 0]. Its decrease is proved at the call:
  [size' B < S (size' B) = size' (λ A. B) <= size' t] ([hszB]). It never recurses into
  a λ domain, a spine argument, or any other root lemma. *)

Definition Good (Σ : global_env) (Γ : context) (t : term) : Type :=
  forall t', red Σ Γ t t' -> eta_safe Σ t'.

Lemma nth_split {A} (l : list A) n a : nth_error l n = Some a -> ∑ pre post, (l = pre ++ a :: post) × #|pre| = n.
Proof.
  induction l as [|x l IH] in n |- *; destruct n; cbn; intros h; try discriminate.
  - injection h as ->. exists [], l. split; reflexivity.
  - destruct (IH _ h) as (pre & post & -> & e). exists (x :: pre), post. split; [reflexivity|cbn; now rewrite e].
Qed.

Lemma isConstruct_app_inv a : isConstruct_app a = true -> ∑ ind k uu bs, a = mkApps (tConstruct ind k uu) bs.
Proof.
  unfold isConstruct_app. destruct (decompose_app a) as [hd bs] eqn:ea. cbn. intros h.
  destruct hd; try discriminate h. apply decompose_app_inv in ea. subst a. now do 4 eexists.
Qed.

Lemma All2_replace_mid {A B} (R : A -> B -> Type) pre0 x post0 pre y post x' :
  #|pre0| = #|pre| -> All2 R (pre0 ++ x :: post0) (pre ++ y :: post) -> R x' y ->
  All2 R (pre0 ++ x' :: post0) (pre ++ y :: post).
Proof.
  induction pre0 as [|z pre0 IH] in pre |- *; destruct pre as [|w pre]; cbn; intros hl ha hr; try discriminate.
  - depelim ha. constructor; assumption.
  - depelim ha. constructor; [assumption|]. apply IH; [lia|assumption|assumption].
Qed.

Lemma size'_pos t : 0 < size' t.
Proof. destruct t; cbn; lia. Qed.

Lemma lift_fix_eta_target mfix idx args :
  tApp (lift0 1 (mkApps (tFix mfix idx) args)) (tRel 0)
  = mkApps (tFix (map (map_def (lift 1 0) (lift 1 (#|mfix| + 0))) mfix) idx) (map (lift0 1) args ++ [tRel 0]).
Proof. rewrite lift_mkApps mkApps_app. reflexivity. Qed.

Lemma lift_mkApps_eta_target f args :
  tApp (lift0 1 (mkApps f args)) (tRel 0) = mkApps (lift0 1 f) (map (lift0 1) args ++ [tRel 0]).
Proof. rewrite lift_mkApps mkApps_app. reflexivity. Qed.

Lemma is_constructor_lift_snoc narg args :
  is_constructor narg args = true -> is_constructor narg (map (lift0 1) args ++ [tRel 0]) = true.
Proof.
  rewrite /is_constructor. destruct (nth_error args narg) as [a|] eqn:ha; [|discriminate]. intros hca.
  have hlt := nth_error_Some_length ha.
  rewrite (nth_error_app_lt (map (lift0 1) args) [tRel 0] narg (ltac:(rewrite length_map; exact hlt))).
  rewrite nth_error_map ha /=.
  now rewrite C3R.isConstruct_app_lift.
Qed.

Section FixRoot.
  Context (Σ : global_env).

  Lemma pe_fix_root_n n : forall Γ t mfix idx args narg fn,
    (* PREMISE Good, NOT unconditional: (i) typed_eta_safe, typing ⇒ invariant, proved here
       with no SR; (ii) preservation of typing along red, E subject reduction, forecast T1,
       not proved here. *)
    size' t <= n -> Good Σ Γ t -> pe t (mkApps (tFix mfix idx) args) ->
    unfold_fix mfix idx = Some (narg, fn) -> is_constructor narg args = true ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w (mkApps fn args).
  Proof.
    induction n as [|n IH]; intros Γ t mfix idx args narg fn hsz hgood hpe hunf hc.
    { exfalso. have := size'_pos t. lia. }
    destruct (pe_spine_or_lam_top Σ Γ t _ (tFix mfix idx) args hpe eq_refl eq_refl) as [hs|hl].
    - (* the source reduces to a fixpoint spine: unfold it *)
      destruct hs as (h0 & args0 & hred & hnlh & hph & hargs).
      depelim hph; [cbn in hnlh; discriminate hnlh|].
      match goal with H : All2 _ ?m mfix |- _ =>
        destruct (pe_unfold_fix_back m mfix idx narg fn H hunf) as (fn0 & hu0 & hfn); rename m into mfix0 end.
      move: hc. rewrite /is_constructor. destruct (nth_error args narg) as [ra|] eqn:ha; [|discriminate].
      intros hca.
      destruct (All2_nth_error_Some_r _ ra hargs ha) as (a0 & ha0 & hpa).
      destruct (nth_split args narg ra ha) as (pre & post & -> & hlen).
      destruct (nth_split args0 narg a0 ha0) as (pre0 & post0 & -> & hlen0).
      destruct (isConstruct_app_inv _ hca) as (ind & k & uu & bs & ->).
      (* the [rarg]-th argument: no reduct of it is a λ (from [Good] on the spine) *)
      have hnl : forall a', red Σ Γ a0 a' -> notLam a'.
      { intros a' hra.
        have hred2 : red Σ Γ t (mkApps (tFix mfix0 idx) (pre0 ++ a' :: post0)).
        { eapply rt_trans; [exact hred|]. apply red_mkApps; [apply rt_refl|].
          apply All2_app; [apply All2_refl; intros; apply rt_refl|].
          constructor; [exact hra|apply All2_refl; intros; apply rt_refl]. }
        have hsp := eta_safe_spine _ _ _ (app_cons_not_nil pre0 post0 a') (hgood _ hred2).
        apply (spine_safe_fix _ _ _ _ _ _ _ hu0 ltac:(rewrite -hlen0; apply nth_error_at_pre) hsp). }
      destruct (pe_rigid_spine Σ Γ a0 hnl _ (tConstruct ind k uu) bs hpa eq_refl eq_refl)
        as (h1 & bs0 & hred1 & hnlh1 & hph1 & hbs).
      depelim hph1; [cbn in hnlh1; discriminate hnlh1|].
      exists (mkApps fn0 (pre0 ++ mkApps (tConstruct ind k uu) bs0 :: post0)). split.
      + eapply rt_trans_clos.
        * eapply rt_trans; [exact hred|]. apply red_mkApps; [apply rt_refl|].
          apply All2_app; [apply All2_refl; intros; apply rt_refl|].
          constructor; [exact hred1|apply All2_refl; intros; apply rt_refl].
        * apply t_step. eapply red_fix; [exact hu0|].
          rewrite /is_constructor -hlen0 nth_error_at_pre /isConstruct_app decompose_app_mkApps //.
      + apply pe_mkApps; [exact hfn|].
        eapply (All2_replace_mid _ pre0 a0 post0); [congruence|exact hargs|].
        apply pe_mkApps; [apply pe_Construct|exact hbs].
    - (* the source reduces to a λ: recurse on its BODY, with [size'] decreasing *)
      destruct hl as (na & A & B & hred & hszl & hpB).
      have hszB : size' B <= n by (cbn in hszl; lia).
      rewrite lift_fix_eta_target in hpB.
      have hgoodB : Good Σ (Γ ,, vass na A) B.
      { intros B' hB.
        have hr : red Σ Γ t (tLambda na A B') by (eapply rt_trans; [exact hred|]; apply red_abs; [apply rt_refl|exact hB]).
        have hs := hgood _ hr. cbn in hs. move/andP: hs => [_ hs]. exact hs. }
      destruct (IH (Γ ,, vass na A) B _ idx _ narg (lift0 1 fn) hszB hgoodB hpB
                  (C3R.lift_unfold_fix 1 0 mfix idx narg fn hunf) (is_constructor_lift_snoc _ _ hc))
        as (w' & hw' & hpw').
      exists (tLambda na A w'). split.
      + eapply rt_trans_clos; [exact hred|].
        eapply (trans_clos_map _ _ (fun y => tLambda na A y)); [|exact hw'].
        intros y z r. now apply abs_red_r.
      + apply pe_eta. rewrite lift_mkApps_eta_target. exact hpw'.
  Qed.

  (** **The parallel fixpoint root: CLOSED, under [Good].** *)
  Theorem pe_fix_root Γ t mfix idx args narg fn :
    Good Σ Γ t -> pe t (mkApps (tFix mfix idx) args) ->
    unfold_fix mfix idx = Some (narg, fn) -> is_constructor narg args = true ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w (mkApps fn args).
  Proof. exact (pe_fix_root_n (size' t) Γ t mfix idx args narg fn (le_n _)). Qed.

End FixRoot.

(** ** The parallel primitive-operation root, by well-founded induction on [size']

  Same structure as the fixpoint root. Two differences: the target is a primitive
  redex followed by EXTRA arguments (under a λ the spine gains [tRel 0], which is not
  a literal, so the redex is the prefix); and the argument positions of the redex
  must be literals, so a [pe]-source of a literal must reduce to it ([pe_lit_red]).
  That uses [no_pe_source_app_prim_n]: a [Good] term never [pe]-reduces to an
  APPLIED primitive value, by the same induction on [size'], whose only recursive
  call is on the body of a λ-reduct. *)

Section PrimRoot.
  Context {cf : checker_flags} {Σ : global_env} (cb : ClosedBodies Σ).

  Lemma Good_red Γ t t' : Good Σ Γ t -> red Σ Γ t t' -> Good Σ Γ t'.
  Proof. intros hg hr t'' h. apply hg. eapply rt_trans; eassumption. Qed.

  Lemma Good_lam_body Γ na A B : Good Σ Γ (tLambda na A B) -> Good Σ (Γ ,, vass na A) B.
  Proof.
    intros hg B' hB.
    have hr : red Σ Γ (tLambda na A B) (tLambda na A B') by (apply red_abs; [apply rt_refl|exact hB]).
    have hs := hg _ hr. cbn in hs. move/andP: hs => [_ hs]. exact hs.
  Qed.

  Lemma Good_arg Γ h pre a post : Good Σ Γ (mkApps h (pre ++ a :: post)) -> Good Σ Γ a.
  Proof.
    intros hg a' hr.
    have hred : red Σ Γ (mkApps h (pre ++ a :: post)) (mkApps h (pre ++ a' :: post)).
    { apply red_mkApps; [apply rt_refl|].
      apply All2_app; [apply All2_refl; intros; apply rt_refl|].
      constructor; [exact hr|apply All2_refl; intros; apply rt_refl]. }
    have hs := eta_safe_mkApps_args _ _ _ (hg _ hred). rewrite forallb_app /= in hs.
    move/andP: hs => [_ /andP [hs _]]. exact hs.
  Qed.

  Lemma eta_safe_mkApps_prim p args : args <> [] -> eta_safe Σ (mkApps (tPrim p) args) = false.
  Proof.
    induction args as [|x l IH] using MRList.rev_ind; [congruence|]. intros _.
    rewrite mkApps_app. cbn [mkApps eta_safe].
    destruct l as [|y l'].
    - reflexivity.
    - rewrite IH; [discriminate|]. now rewrite andb_false_r.
  Qed.

  Lemma snoc_not_nil {A} (l : list A) x : l ++ [x] <> [].
  Proof. intros e. apply app_eq_nil in e as [_ e]. discriminate e. Qed.

  (** A [Good] term is never a [pe]-source of an applied primitive value. Only
      recursive call: on the body [B] of a λ-reduct, with [size' B < size' a]. *)
  Lemma no_pe_source_app_prim_n n : forall Γ a p xs,
    size' a <= n -> Good Σ Γ a -> pe a (mkApps (tPrim p) xs) -> xs <> [] -> False.
  Proof.
    induction n as [|n IH]; intros Γ a p xs hsz hg hpe hne.
    { have := size'_pos a. lia. }
    destruct (pe_spine_or_lam_top Σ Γ a _ (tPrim p) xs hpe eq_refl eq_refl) as [hs|hl].
    - destruct hs as (h0 & args0 & hred & hnlh & hph & hargs).
      depelim hph; [cbn in hnlh; discriminate hnlh|].
      have hne0 : args0 <> [] by (intros ->; depelim hargs; congruence).
      have hs := hg _ hred. rewrite (eta_safe_mkApps_prim _ _ hne0) in hs. discriminate hs.
    - destruct hl as (na & A & B & hred & hszl & hpB).
      rewrite lift_mkApps_eta_target in hpB. cbn [lift] in hpB.
      exact (IH (Γ ,, vass na A) B _ _ ltac:(cbn in hszl; lia)
               (Good_lam_body _ _ _ _ (Good_red _ _ _ hg hred)) hpB (snoc_not_nil _ _)).
  Qed.

  (** A [Good] [pe]-source of a literal reduces to that literal. *)
  Lemma pe_lit_red Γ a l : Good Σ Γ a -> pe a (term_of_lit l) -> red Σ Γ a (term_of_lit l).
  Proof.
    intros hg hpe.
    destruct (pe_spine_or_lam_top Σ Γ a _ (term_of_lit l) [] hpe eq_refl eq_refl) as [hs|hl].
    - destruct hs as (h0 & args0 & hred & hnlh & hph & hargs). depelim hargs. cbn in hred.
      destruct l as [i|s0]; cbn in hph |- *; depelim hph; try (cbn in hnlh; discriminate hnlh);
        match goal with H : onPrims _ _ _ _ |- _ => depelim H end; exact hred.
    - destruct hl as (na & A & B & hred & hszl & hpB). exfalso.
      have hgB := Good_lam_body _ _ _ _ (Good_red _ _ _ hg hred).
      destruct l as [i|s0]; cbn in hpB;
        exact (no_pe_source_app_prim_n (size' B) _ B _ [tRel 0] (le_n _) hgB hpB ltac:(discriminate)).
  Qed.

  Lemma pe_lits_red Γ h pre a0s post ls :
    Good Σ Γ (mkApps h (pre ++ a0s ++ post)) -> All2 pe a0s (map term_of_lit ls) ->
    All2 (red Σ Γ) a0s (map term_of_lit ls).
  Proof.
    induction a0s as [|a a0s IH] in pre, ls |- *; intros hg ha; destruct ls as [|l ls]; cbn in ha |- *;
      depelim ha.
    - constructor.
    - constructor.
      + apply pe_lit_red; [|assumption]. exact (Good_arg _ h pre a (a0s ++ post) hg).
      + apply (IH (pre ++ [a]) ls); [|assumption]. rewrite -app_assoc. exact hg.
  Qed.

  Lemma lift_prim_spine n k c uu ls :
    lift n k (mkApps (tConst c uu) (map term_of_lit ls)) = mkApps (tConst c uu) (map term_of_lit ls).
  Proof.
    rewrite lift_mkApps map_map. cbn. f_equal. apply map_ext. intros []; reflexivity.
  Qed.

  Lemma ofv_prim_spine c uu ls : on_free_vars xpredT (mkApps (tConst c uu) (map term_of_lit ls)).
  Proof.
    rewrite on_free_vars_mkApps. cbn. induction ls as [|l ls IH]; [reflexivity|].
    destruct l; cbn; exact IH.
  Qed.

  Lemma pe_prim_root_n n : forall Γ t c uu ls extra v,
    (* PREMISE Good, NOT unconditional: (i) typed_eta_safe, typing ⇒ invariant, proved here
       with no SR; (ii) preservation of typing along red, E subject reduction, forecast T1,
       not proved here. *)
    size' t <= n -> Good Σ Γ t ->
    pe t (mkApps (mkApps (tConst c uu) (map term_of_lit ls)) extra) ->
    red1 Σ Γ (mkApps (tConst c uu) (map term_of_lit ls)) v ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w (mkApps v extra).
  Proof.
    induction n as [|n IH]; intros Γ t c uu ls extra v hsz hgood hpe hstep.
    { exfalso. have := size'_pos t. lia. }
    rewrite -mkApps_app in hpe.
    destruct (pe_spine_or_lam_top Σ Γ t _ (tConst c uu) _ hpe eq_refl eq_refl) as [hs|hl].
    - (* the source reduces to the primitive spine: reduce its literal arguments, fire *)
      destruct hs as (h0 & args0 & hred & hnlh & hph & hargs).
      depelim hph; [cbn in hnlh; discriminate hnlh|].
      destruct (All2_app_inv_r _ _ _ _ _ _ hargs) as (a0s & b0s & -> & hlits & hext).
      have hlr := pe_lits_red Γ (tConst c uu) [] a0s b0s ls (Good_red _ _ _ hgood hred) hlits.
      exists (mkApps v b0s). split.
      + eapply rt_trans_clos.
        * eapply rt_trans; [exact hred|]. apply red_mkApps; [apply rt_refl|].
          apply All2_app; [exact hlr|apply All2_refl; intros; apply rt_refl].
        * apply t_step. rewrite mkApps_app. now apply red1_mkApps_f.
      + apply pe_mkApps; [apply pe_refl|exact hext].
    - (* the source reduces to a λ: recurse on its BODY, with [size'] decreasing *)
      destruct hl as (na & A & B & hred & hszl & hpB).
      have hszB : size' B <= n by (cbn in hszl; lia).
      rewrite mkApps_app lift_mkApps_eta_target lift_prim_spine in hpB.
      have hstep' : red1 Σ (Γ ,, vass na A) (mkApps (tConst c uu) (map term_of_lit ls)) (lift0 1 v).
      { rewrite -{1}(lift_prim_spine 1 0 c uu ls).
        exact (red1_lift1 cb Γ na A _ _ (ofv_prim_spine c uu ls) hstep). }
      destruct (IH (Γ ,, vass na A) B c uu ls _ _ hszB (Good_lam_body _ _ _ _ (Good_red _ _ _ hgood hred))
                  hpB hstep') as (w' & hw' & hpw').
      exists (tLambda na A w'). split.
      + eapply rt_trans_clos; [exact hred|].
        eapply (trans_clos_map _ _ (fun y => tLambda na A y)); [|exact hw'].
        intros y z r. now apply abs_red_r.
      + apply pe_eta. rewrite lift_mkApps_eta_target. exact hpw'.
  Qed.

  (** **The parallel primitive-operation root: CLOSED, under [Good].** *)
  Theorem pe_prim_root Γ t c uu ls v :
    Good Σ Γ t -> pe t (mkApps (tConst c uu) (map term_of_lit ls)) ->
    red1 Σ Γ (mkApps (tConst c uu) (map term_of_lit ls)) v ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w v.
  Proof. intros hg hpe hstep. exact (pe_prim_root_n (size' t) Γ t c uu ls [] v (le_n _) hg hpe hstep). Qed.

End PrimRoot.

(** ** Assembly of the parallel one-step postponement: infrastructure

  The assembled statement ([pe_postpone]) relates a source [t] in [Γ] to a target [u]
  in [Γ'] with [pe_ctx Γ Γ'] (let bodies related by [pe]); its premises are
  [Good Σ Γ t] (source side; same two halves as before) and
  [on_free_vars xpredT u] (target side, for weakening the target step under a λ). *)

Lemma ofvT_shift k t : on_free_vars (shiftnP k xpredT) t = on_free_vars xpredT t.
Proof. apply on_free_vars_ext. apply shiftnP_xpredT. Qed.

Lemma ofvT_lift0 t : on_free_vars xpredT t -> on_free_vars xpredT (lift0 1 t).
Proof.
  intros h. rewrite -(ofvT_shift 1). apply (on_free_vars_lift_impl xpredT 1 0). now rewrite ofvT_shift.
Qed.

Lemma pe_decl_refl d : pe_decl d d.
Proof. unfold pe_decl. destruct (decl_body d); [apply pe_refl|exact tt]. Qed.

Lemma pe_ctx_refl Γ : pe_ctx Γ Γ.
Proof. apply All2_same, pe_decl_refl. Qed.

Lemma pe_ctx_vass Γ Γ' na A na' A' : pe_ctx Γ Γ' -> pe_ctx (Γ ,, vass na A) (Γ' ,, vass na' A').
Proof. intros h. constructor; [exact tt|exact h]. Qed.

Lemma pe_ctx_vdef Γ Γ' na b t na' b' t' :
  pe_ctx Γ Γ' -> pe b b' -> pe_ctx (Γ ,, vdef na b t) (Γ' ,, vdef na' b' t').
Proof. intros h hb. constructor; [exact hb|exact h]. Qed.

Lemma pe_ctx_app Γ Γ' Δ Δ' : pe_ctx Γ Γ' -> pe_ctx Δ Δ' -> pe_ctx (Γ ,,, Δ) (Γ' ,,, Δ').
Proof. intros h h'. unfold app_context. now apply All2_app. Qed.

Lemma pe_ctx_mapi_vass (f g : nat -> def term -> term) m m' k :
  #|m| = #|m'| ->
  All2 pe_decl (mapi_rec (fun i d => vass (dname d) (f i d)) m k)
               (mapi_rec (fun i d => vass (dname d) (g i d)) m' k).
Proof.
  induction m as [|d m IH] in m', k |- *; destruct m' as [|d' m']; cbn; intros hl; try discriminate.
  - constructor.
  - constructor; [exact tt|]. apply IH. lia.
Qed.

Lemma pe_ctx_fix_context m m' : #|m| = #|m'| -> pe_ctx (fix_context m) (fix_context m').
Proof. intros hl. unfold fix_context, mapi. apply All2_rev. now apply pe_ctx_mapi_vass. Qed.

Lemma pe_ctx_nth Γ Γ' n b' : pe_ctx Γ Γ' -> option_map decl_body (nth_error Γ' n) = Some (Some b') ->
  ∑ b, (option_map decl_body (nth_error Γ n) = Some (Some b)) × pe b b'.
Proof.
  intros h. induction h as [|d d' Γ Γ' hd h IH] in n |- *; destruct n; cbn; intros e; try discriminate.
  - unfold pe_decl in hd. destruct (decl_body d') as [b0|]; [|discriminate].
    injection e as ->. destruct (decl_body d) as [b|]; [|destruct hd]. exists b. split; [reflexivity|exact hd].
  - exact (IH n e).
Qed.

Lemma set_pparams_twice p l l' : set_pparams (set_pparams p l) l' = set_pparams p l'.
Proof. now destruct p. Qed.

Lemma set_array_value_twice a l l' : set_array_value (set_array_value a l) l' = set_array_value a l'.
Proof. now destruct a. Qed.

(** One position of a list reduces under a congruence [C]: [Good] of the list term
    gives [Good] of each element. *)
Lemma Good_list_terms Σ Γ (C : list term -> term) l :
  (forall l l0, All2 (red Σ Γ) l l0 -> red Σ Γ (C l) (C l0)) ->
  (forall l0, eta_safe Σ (C l0) -> forallb (eta_safe Σ) l0) ->
  Good Σ Γ (C l) -> All (Good Σ Γ) l.
Proof.
  induction l as [|a l IH] in C |- *; intros hC hE hg; constructor.
  - intros a' hr.
    have hr' : red Σ Γ (C (a :: l)) (C (a' :: l))
      by (apply hC; constructor; [exact hr|apply All2_refl; intros; apply rt_refl]).
    have := hE _ (hg _ hr'). cbn. move/andP => [h _]. exact h.
  - apply (IH (fun l0 => C (a :: l0))).
    + intros l1 l2 h. apply hC. constructor; [apply rt_refl|exact h].
    + intros l0 h. have := hE _ h. cbn. move/andP => [_ h']. exact h'.
    + exact hg.
Qed.

Section GoodTransport.
  Context (Σ : global_env) (Γ : context).

  Ltac good_proj hg hr := let hs := fresh in have hs := hg _ hr; cbn in hs; rtoProp; assumption.

  Lemma Good_app_l f x : Good Σ Γ (tApp f x) -> Good Σ Γ f.
  Proof.
    intros hg f' hr. have hr' : red Σ Γ (tApp f x) (tApp f' x) by (apply red_app; [exact hr|apply rt_refl]).
    good_proj hg hr'.
  Qed.

  Lemma Good_app_r f x : Good Σ Γ (tApp f x) -> Good Σ Γ x.
  Proof.
    intros hg x' hr. have hr' : red Σ Γ (tApp f x) (tApp f x') by (apply red_app; [apply rt_refl|exact hr]).
    good_proj hg hr'.
  Qed.

  Lemma Good_lam_dom na A M : Good Σ Γ (tLambda na A M) -> Good Σ Γ A.
  Proof.
    intros hg A' hr. have hr' : red Σ Γ (tLambda na A M) (tLambda na A' M) by (apply red_abs; [exact hr|apply rt_refl]).
    good_proj hg hr'.
  Qed.

  Lemma Good_prod_dom na A B : Good Σ Γ (tProd na A B) -> Good Σ Γ A.
  Proof.
    intros hg A' hr. have hr' : red Σ Γ (tProd na A B) (tProd na A' B) by (apply red_prod; [exact hr|apply rt_refl]).
    good_proj hg hr'.
  Qed.

  Lemma Good_prod_cod na A B : Good Σ Γ (tProd na A B) -> Good Σ (Γ ,, vass na A) B.
  Proof.
    intros hg B' hr. have hr' : red Σ Γ (tProd na A B) (tProd na A B') by (apply red_prod; [apply rt_refl|exact hr]).
    good_proj hg hr'.
  Qed.

  Lemma Good_letin_def na b ty x : Good Σ Γ (tLetIn na b ty x) -> Good Σ Γ b.
  Proof.
    intros hg b' hr.
    have hr' : red Σ Γ (tLetIn na b ty x) (tLetIn na b' ty x) by (apply red_letin; [exact hr|apply rt_refl|apply rt_refl]).
    good_proj hg hr'.
  Qed.

  Lemma Good_letin_ty na b ty x : Good Σ Γ (tLetIn na b ty x) -> Good Σ Γ ty.
  Proof.
    intros hg t' hr.
    have hr' : red Σ Γ (tLetIn na b ty x) (tLetIn na b t' x) by (apply red_letin; [apply rt_refl|exact hr|apply rt_refl]).
    good_proj hg hr'.
  Qed.

  Lemma Good_letin_body na b ty x : Good Σ Γ (tLetIn na b ty x) -> Good Σ (Γ ,, vdef na b ty) x.
  Proof.
    intros hg x' hr.
    have hr' : red Σ Γ (tLetIn na b ty x) (tLetIn na b ty x') by (apply red_letin; [apply rt_refl|apply rt_refl|exact hr]).
    good_proj hg hr'.
  Qed.

  Lemma Good_proj pr c : Good Σ Γ (tProj pr c) -> Good Σ Γ c.
  Proof. intros hg c' hr. have hr' := red_proj_c pr _ _ hr. good_proj hg hr'. Qed.

  Lemma Good_proj_hnl pr c : Good Σ Γ (tProj pr c) -> forall c', red Σ Γ c c' -> notLam c'.
  Proof. intros hg c' hr. exact (eta_safe_proj_arg _ _ _ (hg _ (red_proj_c pr _ _ hr))). Qed.

  Lemma Good_case_discr ci p c brs : Good Σ Γ (tCase ci p c brs) -> Good Σ Γ c.
  Proof. intros hg c' hr. have hr' := red_case_c ci p c brs c' hr. good_proj hg hr'. Qed.

  Lemma Good_case_hnl ci p c brs : Good Σ Γ (tCase ci p c brs) -> forall c', red Σ Γ c c' -> notLam c'.
  Proof. intros hg c' hr. exact (eta_safe_case_scrut _ _ _ _ _ (hg _ (red_case_c ci p c brs c' hr))). Qed.

  Lemma Good_case_ret ci p c brs :
    Good Σ Γ (tCase ci p c brs) -> Good Σ (Γ ,,, inst_case_predicate_context p) (preturn p).
  Proof. intros hg r hr. have hr' := red_case_p ci p c brs r hr. good_proj hg hr'. Qed.

  Lemma Good_case_params ci p c brs : Good Σ Γ (tCase ci p c brs) -> All (Good Σ Γ) (pparams p).
  Proof.
    intros hg. apply (Good_list_terms Σ Γ (fun l => tCase ci (set_pparams p l) c brs)).
    - intros l l0 h. rewrite -(set_pparams_twice p l l0). now apply red_case_pars.
    - intros l0 h. cbn in h. rtoProp. assumption.
    - now rewrite C3R.set_pparams_id.
  Qed.

  Lemma Good_evar ev l : Good Σ Γ (tEvar ev l) -> All (Good Σ Γ) l.
  Proof.
    intros hg. apply (Good_list_terms Σ Γ (tEvar ev)); [|intros l0 h; exact h|exact hg].
    intros l1 l2 h. now apply red_evar.
  Qed.

  Lemma Good_case_brs ci p c brs :
    Good Σ Γ (tCase ci p c brs) -> All (fun br => Good Σ (Γ ,,, inst_case_branch_context p br) (bbody br)) brs.
  Proof.
    intros hg.
    enough (H : forall pre, Good Σ Γ (tCase ci p c (pre ++ brs)) ->
                 All (fun br => Good Σ (Γ ,,, inst_case_branch_context p br) (bbody br)) brs)
      by exact (H [] hg).
    clear hg. induction brs as [|br brs IH]; intros pre hg'; constructor.
    - intros b' hr.
      have hr' : red Σ Γ (tCase ci p c (pre ++ br :: brs))
                   (tCase ci p c (pre ++ {| bcontext := bcontext br; bbody := b' |} :: brs)).
      { apply red_case_one_brs. apply OnOne2_app. constructor. split; [exact hr|reflexivity]. }
      have hs := hg' _ hr'. cbn in hs. rtoProp.
      match goal with H : is_true (forallb _ (pre ++ _)) |- _ => rewrite forallb_app /= in H end.
      rtoProp. assumption.
    - apply (IH (pre ++ [br])). rewrite -app_assoc. exact hg'.
  Qed.

  Lemma Good_fix_gen (isfix : bool) mfix idx :
    let T := if isfix then tFix else tCoFix in
    Good Σ Γ (T mfix idx) ->
    All (fun d => Good Σ Γ (dtype d) × Good Σ (Γ ,,, fix_context mfix) (dbody d)) mfix.
  Proof.
    intros T hg.
    enough (H : forall pre rest, mfix = pre ++ rest ->
                 All (fun d => Good Σ Γ (dtype d) × Good Σ (Γ ,,, fix_context mfix) (dbody d)) rest)
      by exact (H [] mfix eq_refl).
    intros pre rest. induction rest as [|d rest IH] in pre |- *; intros e; constructor.
    - split.
      + intros ty' hr.
        set d' := {| dname := dname d; dtype := ty'; dbody := dbody d; rarg := rarg d |}.
        have hr' : red Σ Γ (T mfix idx) (T (pre ++ d' :: rest) idx).
        { rewrite {1}e. destruct isfix; [apply red_fix_ty|apply red_cofix_ty];
          (apply All2_app;
           [ apply All2_refl; intros; split; [apply rt_refl|reflexivity]
           | constructor; [split; [exact hr|reflexivity]
                          |apply All2_refl; intros; split; [apply rt_refl|reflexivity]]]). }
        have hs := hg _ hr'. destruct isfix; cbn in hs; rewrite forallb_app /= in hs; rtoProp; assumption.
      + intros b' hr.
        set d' := {| dname := dname d; dtype := dtype d; dbody := b'; rarg := rarg d |}.
        have hr' : red Σ Γ (T mfix idx) (T (pre ++ d' :: rest) idx).
        { destruct isfix; [apply red_fix_body|apply red_cofix_body]; rewrite {2}e;
          (apply All2_app;
           [ apply All2_refl; intros; split; [apply rt_refl|reflexivity]
           | constructor; [split; [exact hr|reflexivity]
                          |apply All2_refl; intros; split; [apply rt_refl|reflexivity]]]). }
        have hs := hg _ hr'. destruct isfix; cbn in hs; rewrite forallb_app /= in hs; rtoProp; assumption.
    - apply (IH (pre ++ [d])). rewrite e -app_assoc. reflexivity.
  Qed.

  Lemma Good_prim_arr a :
    Good Σ Γ (tPrim (primArray; primArrayModel a)) ->
    Good Σ Γ (array_default a) × Good Σ Γ (array_type a) × All (Good Σ Γ) (array_value a).
  Proof.
    intros hg. split; [|split].
    - intros d' hr. have hr' := red_primArray_default a d' hr. good_proj hg hr'.
    - intros t' hr. have hr' := red_primArray_type a t' hr. good_proj hg hr'.
    - apply (Good_list_terms Σ Γ (fun l => tPrim (primArray; primArrayModel (set_array_value a l)))).
      + intros l l0 h. rewrite -(set_array_value_twice a l l0). now apply red_primArray_value.
      + intros l0 h. cbn in h. rtoProp. assumption.
      + now rewrite C3R.set_array_value_id.
  Qed.

End GoodTransport.

Lemma All2_cons_inv' {A B} (R : A -> B -> Type) x l y l' : All2 R (x :: l) (y :: l') -> R x y × All2 R l l'.
Proof. intros h. now depelim h. Qed.

Lemma All_cons_inv' {A} (P : A -> Type) x l : All P (x :: l) -> P x × All P l.
Proof. intros h. now depelim h. Qed.

(** A list in which one position steps by [R] on the target side: postpone that one
    step through [pe] (with per-element hypotheses [G] on sources and [T] on targets). *)
Lemma OnOne2_postpone {A} (Pe R S : A -> A -> Type) (G T : A -> Type) l l' l'' :
  All2 (fun x y => Pe x y × (G x -> T y -> forall z, R y z -> ∑ w, trans_clos S x w × Pe w z)) l l' ->
  All G l -> All T l' -> OnOne2 R l' l'' ->
  ∑ l0, OnOne2 (trans_clos S) l l0 × All2 Pe l0 l''.
Proof.
  intros ha hG hT ho. induction ho as [y z tl hr|y tl tl' ho IH] in l, ha, hG, hT |- *;
    (destruct l as [|x l]; [depelim ha|]);
    destruct (All2_cons_inv' _ _ _ _ _ ha) as [[hp ih] ha'];
    destruct (All_cons_inv' _ _ _ hG) as [gx hG'];
    destruct (All_cons_inv' _ _ _ hT) as [ty hT'].
  - destruct (ih gx ty _ hr) as (w & hw & hpw).
    exists (w :: l). split; [now constructor|].
    constructor; [exact hpw|]. eapply All2_impl; [exact ha'|]. intros x0 y0 [h _]. exact h.
  - destruct (IH _ ha' hG' hT') as (l0 & ho0 & hp0).
    exists (x :: l0). split; [now constructor|]. now constructor.
Qed.

Lemma OnOne2_tc {A} (R : A -> A -> Type) l l0 : OnOne2 (trans_clos R) l l0 -> trans_clos (OnOne2 R) l l0.
Proof.
  induction 1 as [x y tl h|x tl tl' h IH].
  - eapply (trans_clos_map _ _ (fun z => z :: tl)); [|exact h]. intros a b r. now constructor.
  - eapply (trans_clos_map _ _ (fun z => x :: z)); [|exact IH]. intros a b r. now constructor.
Qed.

Lemma set_array_default_twice a d d' : set_array_default (set_array_default a d) d' = set_array_default a d'.
Proof. now destruct a. Qed.

Lemma set_array_type_twice a t t' : set_array_type (set_array_type a t) t' = set_array_type a t'.
Proof. now destruct a. Qed.

Lemma set_preturn_twice p r r' : set_preturn (set_preturn p r) r' = set_preturn p r'.
Proof. now destruct p. Qed.

Lemma fix_context_body_irr pre post n t b b' r r' :
  fix_context (pre ++ {| dname := n; dtype := t; dbody := b; rarg := r |} :: post)
  = fix_context (pre ++ {| dname := n; dtype := t; dbody := b'; rarg := r' |} :: post).
Proof. unfold fix_context. rewrite !mapi_app. reflexivity. Qed.

Section RecordSteps.
  Context (Σ : global_env).

  Lemma tc_branch_body Γ p (x : branch term) w :
    trans_clos (red1 Σ (Γ ,,, inst_case_branch_context p x)) (bbody x) w ->
    trans_clos (fun br br' => on_Trel_eq (red1 Σ (Γ ,,, inst_case_branch_context p br)) bbody bcontext br br')
      x {| bcontext := bcontext x; bbody := w |}.
  Proof.
    destruct x as [cx bx]; cbn. intros h.
    eapply (trans_clos_map _ _ (fun b => {| bcontext := cx; bbody := b |})); [|exact h].
    intros a b r. split; [exact r|reflexivity].
  Qed.

  Lemma tc_def_type Γ (d : def term) w :
    trans_clos (red1 Σ Γ) (dtype d) w ->
    trans_clos (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x)))
      d {| dname := dname d; dtype := w; dbody := dbody d; rarg := rarg d |}.
  Proof.
    destruct d as [dn dt db dr]; cbn. intros h.
    eapply (trans_clos_map _ _ (fun t => {| dname := dn; dtype := t; dbody := db; rarg := dr |})); [|exact h].
    intros a b r. split; [exact r|reflexivity].
  Qed.

  Lemma tc_def_body Δ (d : def term) w :
    trans_clos (red1 Σ Δ) (dbody d) w ->
    trans_clos (on_Trel_eq (red1 Σ Δ) dbody (fun x => (dname x, dtype x, rarg x)))
      d {| dname := dname d; dtype := dtype d; dbody := w; rarg := rarg d |}.
  Proof.
    destruct d as [dn dt db dr]; cbn. intros h.
    eapply (trans_clos_map _ _ (fun b => {| dname := dn; dtype := dt; dbody := b; rarg := dr |})); [|exact h].
    intros a b r. split; [exact r|reflexivity].
  Qed.

  Lemma tc_def_body_inv Δ d d0 :
    trans_clos (on_Trel_eq (red1 Σ Δ) dbody (fun x => (dname x, dtype x, rarg x))) d d0 ->
    trans_clos (red1 Σ Δ) (dbody d) (dbody d0) × ((dname d, dtype d, rarg d) = (dname d0, dtype d0, rarg d0)).
  Proof.
    induction 1 as [x y [r e]|x y z _ [h1 e1] _ [h2 e2]].
    - split; [now apply t_step|exact e].
    - split; [eapply t_trans; eassumption|congruence].
  Qed.

  (** One body of a (co)fixpoint steps by [red1⁺] in [Γ ,,, fix_context M]: the
      (co)fixpoint steps by [red1⁺] (each intermediate keeps names and types, so
      the same [fix_context]). *)
  Lemma fix_body_steps (isfix : bool) Γ M M0 idx :
    let T := if isfix then tFix else tCoFix in
    OnOne2 (fun d d0 => trans_clos (red1 Σ (Γ ,,, fix_context M)) (dbody d) (dbody d0)
                        × ((dname d, dtype d, rarg d) = (dname d0, dtype d0, rarg d0))) M M0 ->
    trans_clos (red1 Σ Γ) (T M idx) (T M0 idx).
  Proof.
    intros T ho. destruct (OnOne2_split _ _ _ _ ho) as (d & d0 & pre & post & [hb e] & -> & ->).
    destruct d as [dn dt db dr], d0 as [n0 t0 b0 r0]; cbn in hb, e.
    injection e as <- <- <-.
    eapply (trans_clos_map _ _ (fun b => T (pre ++ {| dname := dn; dtype := dt; dbody := b; rarg := dr |} :: post) idx));
      [|exact hb].
    intros a b r. destruct isfix; [apply fix_red_body|apply cofix_red_body]; apply OnOne2_app; constructor;
      (split; [|reflexivity]); cbn; rewrite (fix_context_body_irr pre post dn dt a db dr dr); exact r.
  Qed.

End RecordSteps.

(** ** The parallel one-step postponement, assembled

  INDUCTION PRINCIPLE: structural on the [pe] derivation of the source ([pe_ind_all]),
  one case per [pe] constructor. The root cases call the root lemmas as black boxes
  ([pe_postpone_beta], [pe_iota_root], [pe_proj_root], [pe_cofix_case_root],
  [pe_cofix_proj_root], [pe_fix_root], [pe_prim_root]); the [pe_eta] case pushes the
  target step under the λ ([red1_lift1]); the other cases are congruences, with the
  target step transported along [pe_ctx].

  POSITIVITY: the source side is [red1⁺] ([trans_clos]), NEVER zero steps. The
  β-head case already needs two steps, on [(λx. (λy. M) x) a]. The iteration below
  ([pe_red_postpone]) weakens it to [red] only at the end, where the target's
  reflexive step needs a reflexive source step. Nothing here needs a strict
  decrease: the [size'] measure is confined to the fixpoint and primitive roots. *)

Section Assembly.
  Context {cf : checker_flags} {Σ : global_env} (cb : ClosedBodies Σ).

  Definition PPg (t u : term) : Type :=
    forall Γ Γ' v, pe_ctx Γ Γ' ->
    (* PREMISE Good, NOT unconditional: (i) typed_eta_safe, proved here with no SR;
       (ii) preservation of typing along red, E subject reduction, forecast T1. *)
    Good Σ Γ t ->
    on_free_vars xpredT u -> red1 Σ Γ' u v ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w v.

  Definition pe_defrel (d d' : def term) : Type :=
    pe d.(dtype) d'.(dtype) × pe d.(dbody) d'.(dbody) × d.(dname) = d'.(dname) × d.(rarg) = d'.(rarg).

  Theorem pe_postpone_gen t u : pe t u -> PPg t u.
  Proof.
    revert t u. apply pe_ind_all; unfold PPg.
    - (* η at the root of the source: push the target step under the λ *)
      intros na A b M' hb IH Γ Γ' v hctx hg hofv hr.
      have hr' : red1 Σ (Γ' ,, vass na A) (tApp (lift0 1 M') (tRel 0)) (tApp (lift0 1 v) (tRel 0))
        by (apply app_red_l; exact (red1_lift1 cb Γ' na A _ _ hofv hr)).
      have hofv' : on_free_vars xpredT (tApp (lift0 1 M') (tRel 0)) by (cbn; now rewrite (ofvT_lift0 _ hofv)).
      destruct (IH (Γ ,, vass na A) (Γ' ,, vass na A) _ (pe_ctx_vass _ _ _ _ _ _ hctx)
                  (Good_lam_body _ _ _ _ hg) hofv' hr') as (w' & hw' & hpw').
      exists (tLambda na A w'). split.
      + eapply (trans_clos_map _ _ (fun y => tLambda na A y)); [|exact hw']. intros y z r. now apply abs_red_r.
      + now apply pe_eta.
    - (* variable: unfold the [pe]-related let body *)
      intros n Γ Γ' v hctx hg hofv hr. destruct (C3R.red1_tRel_inv hr) as (b' & hb' & ->).
      destruct (pe_ctx_nth _ _ _ _ hctx hb') as (b & hb & hpb).
      exists (lift0 (S n) b). split; [apply t_step; now apply red_rel|now apply pe_lift].
    - intros i Γ Γ' v _ _ _ hr. exfalso. exact (C3R.red1_tVar_absurd hr).
    - intros s Γ Γ' v _ _ _ hr. exfalso. exact (C3R.red1_tSort_absurd hr).
    - intros c uu Γ Γ' v _ _ _ hr. destruct (C3R.red1_tConst_inv hr) as (decl & body & hd & hb & ->).
      exists (subst_instance uu body). split; [apply t_step; eapply red_delta; eassumption|apply pe_refl].
    - intros ind uu Γ Γ' v _ _ _ hr. exfalso. exact (C3R.red1_tInd_absurd hr).
    - intros ind k uu Γ Γ' v _ _ _ hr. exfalso. exact (C3R.red1_tConstruct_absurd hr).
    - (* evar *)
      intros ev l l' al Γ Γ' v hctx hg hofv hr. destruct (C3R.red1_tEvar_inv hr) as (l1 & -> & ho).
      have hT : All (fun y => is_true (on_free_vars xpredT y)) l' by (cbn in hofv; now apply forallb_All).
      destruct (OnOne2_postpone pe (red1 Σ Γ') (red1 Σ Γ) (Good Σ Γ) (fun y => is_true (on_free_vars xpredT y))
                  l l' l1 (All2_impl al (fun x y '(hp, ih) => (hp, fun gx ty z hz => ih Γ Γ' z hctx gx ty hz)))
                  (Good_evar Σ Γ ev l hg) hT ho) as (l0 & ho0 & hp0).
      exists (tEvar ev l0). split.
      + eapply (trans_clos_map _ _ (tEvar ev)); [|exact (OnOne2_tc _ _ _ ho0)]. intros a b r. now apply evar_red.
      + now apply pe_Evar.
    - (* λ *)
      intros na A A' M M' hA IHA hM IHM Γ Γ' v hctx hg hofv hr.
      cbn in hofv. move/andP: hofv => [hoA hoM]. rewrite ofvT_shift in hoM.
      destruct (C3R.red1_tLambda_inv hr) as [(A'' & -> & hrA)|(M'' & -> & hrM)].
      + destruct (IHA Γ Γ' A'' hctx (Good_lam_dom Σ Γ _ _ _ hg) hoA hrA) as (w & hw & hpw).
        exists (tLambda na w M). split; [|now apply pe_Lambda].
        eapply (trans_clos_map _ _ (fun y => tLambda na y M)); [|exact hw]. intros y z r. now apply abs_red_l.
      + destruct (IHM (Γ ,, vass na A) (Γ' ,, vass na A') M'' (pe_ctx_vass _ _ _ _ _ _ hctx)
                    (Good_lam_body _ _ _ _ hg) hoM hrM) as (w & hw & hpw).
        exists (tLambda na A w). split; [|now apply pe_Lambda].
        eapply (trans_clos_map _ _ (fun y => tLambda na A y)); [|exact hw]. intros y z r. now apply abs_red_r.
    - (* application: β, fixpoint and primitive roots, or a congruence *)
      intros f f' x x' hf IHf hx IHx Γ Γ' v hctx hg hofv hr.
      destruct (C3R.red1_tApp_inv hr) as
        [[[[(na & A' & b' & -> & ->)|(mfix & idx & args & narg & fn & E & hu & hc & ->)]
          |(f'' & -> & hrf)]|(x'' & -> & hrx)]
        |(c & decl & uu & op & ls & r & E & hop & hd & hb & hden & hrb)].
      + exact (pe_postpone_beta Σ Γ (tApp f x) na A' b' x' (pe_App _ _ _ _ hf hx)).
      + have hpe : pe (tApp f x) (mkApps (tFix mfix idx) args) by (rewrite E; now apply pe_App).
        exact (pe_fix_root Σ Γ (tApp f x) mfix idx args narg fn hg hpe hu hc).
      + cbn in hofv. move/andP: hofv => [hof hox].
        destruct (IHf Γ Γ' f'' hctx (Good_app_l Σ Γ _ _ hg) hof hrf) as (w & hw & hpw).
        exists (tApp w x). split; [|now apply pe_App].
        eapply (trans_clos_map _ _ (fun y => tApp y x)); [|exact hw]. intros y z r0. now apply app_red_l.
      + cbn in hofv. move/andP: hofv => [hof hox].
        destruct (IHx Γ Γ' x'' hctx (Good_app_r Σ Γ _ _ hg) hox hrx) as (w & hw & hpw).
        exists (tApp f w). split; [|now apply pe_App].
        eapply (trans_clos_map _ _ (fun y => tApp f y)); [|exact hw]. intros y z r0. now apply app_red_r.
      + have hpe : pe (tApp f x) (mkApps (tConst c uu) (map term_of_lit ls)) by (rewrite E; now apply pe_App).
        have hstep : red1 Σ Γ (mkApps (tConst c uu) (map term_of_lit ls)) v by (eapply red_prim_op; eassumption).
        exact (pe_prim_root cb Γ (tApp f x) c uu ls v hg hpe hstep).
    - (* product *)
      intros na a a' b b' ha IHa hb IHb Γ Γ' v hctx hg hofv hr.
      cbn in hofv. move/andP: hofv => [hoa hob]. rewrite ofvT_shift in hob.
      destruct (C3R.red1_tProd_inv hr) as [(a'' & -> & hra)|(b'' & -> & hrb)].
      + destruct (IHa Γ Γ' a'' hctx (Good_prod_dom Σ Γ _ _ _ hg) hoa hra) as (w & hw & hpw).
        exists (tProd na w b). split; [|now apply pe_Prod].
        eapply (trans_clos_map _ _ (fun y => tProd na y b)); [|exact hw]. intros y z r. now apply prod_red_l.
      + destruct (IHb (Γ ,, vass na a) (Γ' ,, vass na a') b'' (pe_ctx_vass _ _ _ _ _ _ hctx)
                    (Good_prod_cod Σ Γ _ _ _ hg) hob hrb) as (w & hw & hpw).
        exists (tProd na a w). split; [|now apply pe_Prod].
        eapply (trans_clos_map _ _ (fun y => tProd na a y)); [|exact hw]. intros y z r. now apply prod_red_r.
    - (* let: ζ, or a congruence *)
      intros na b b' ty ty' x x' hb IHb hty IHty hx IHx Γ Γ' v hctx hg hofv hr.
      cbn in hofv. move/and3P: hofv => [hob hoty hox]. rewrite ofvT_shift in hox.
      destruct (C3R.red1_tLetIn_inv hr) as [[[->|(b'' & -> & hrb)]|(ty'' & -> & hrty)]|(x'' & -> & hrx)].
      + exists (x {0 := b}). split; [apply t_step; apply red_zeta|].
        exact (pe_subst _ _ hx [b] [b'] 0 (All2_cons hb All2_nil)).
      + destruct (IHb Γ Γ' b'' hctx (Good_letin_def Σ Γ _ _ _ _ hg) hob hrb) as (w & hw & hpw).
        exists (tLetIn na w ty x). split; [|now apply pe_LetIn].
        eapply (trans_clos_map _ _ (fun y => tLetIn na y ty x)); [|exact hw]. intros y z r. now apply letin_red_def.
      + destruct (IHty Γ Γ' ty'' hctx (Good_letin_ty Σ Γ _ _ _ _ hg) hoty hrty) as (w & hw & hpw).
        exists (tLetIn na b w x). split; [|now apply pe_LetIn].
        eapply (trans_clos_map _ _ (fun y => tLetIn na b y x)); [|exact hw]. intros y z r. now apply letin_red_ty.
      + destruct (IHx (Γ ,, vdef na b ty) (Γ' ,, vdef na b' ty') x'' (pe_ctx_vdef _ _ _ _ _ _ _ _ hctx hb)
                    (Good_letin_body Σ Γ _ _ _ _ hg) hox hrx) as (w & hw & hpw).
        exists (tLetIn na b ty w). split; [|now apply pe_LetIn].
        eapply (trans_clos_map _ _ (fun y => tLetIn na b ty y)); [|exact hw]. intros y z r. now apply letin_red_body.
    - (* case: ι and cofix roots, or a congruence *)
      intros ci p p' c c' brs brs' apar eu ectx pret IHret pc IHc abrs Γ Γ' v hctx hg hofv hr.
      have apar0 : All2 pe (pparams p) (pparams p') := All2_impl apar (fun x y h => fst h).
      have abrs0 : All2 (fun x y => bcontext x = bcontext y × pe (bbody x) (bbody y)) brs brs'
        := All2_impl abrs (fun x y h => (fst h, fst (snd h))).
      have hnl := Good_case_hnl Σ Γ ci p c brs hg.
      cbn in hofv. move/and5P: hofv => [hopar horet _ hoc hobrs].
      destruct (C3R.red1_tCase_inv hr) as
        [[[[[(k & uu & args & br & -> & hnth & hlen & ->)|(mfix & idx & args & narg & fn & -> & hu & ->)]
           |(par1 & -> & hop)]|(r & -> & hrr)]|(c1 & -> & hrc)]|(brs1 & -> & hob)].
      + exact (pe_iota_root Σ Γ ci p c brs p' k uu args brs' br hnl apar0 eu pc abrs0 hnth hlen).
      + exact (pe_cofix_case_root Σ Γ ci p c brs p' mfix idx args narg fn brs' hnl apar0 eu ectx pret pc abrs0 hu).
      + (* a parameter *)
        have hT : All (fun y => is_true (on_free_vars xpredT y)) (pparams p') by now apply forallb_All.
        destruct (OnOne2_postpone pe (red1 Σ Γ') (red1 Σ Γ) (Good Σ Γ) (fun y => is_true (on_free_vars xpredT y))
                    _ _ par1 (All2_impl apar (fun x y '(hp, ih) => (hp, fun gx ty z hz => ih Γ Γ' z hctx gx ty hz)))
                    (Good_case_params Σ Γ ci p c brs hg) hT hop) as (l0 & ho0 & hp0).
        exists (tCase ci (set_pparams p l0) c brs). split.
        * rewrite -{1}(C3R.set_pparams_id p).
          eapply (trans_clos_map _ _ (fun l => tCase ci (set_pparams p l) c brs)); [|exact (OnOne2_tc _ _ _ ho0)].
          intros a b0 r0. rewrite -(set_pparams_twice p a b0). now apply case_red_param.
        * apply pe_Case; cbn; [exact hp0|exact eu|exact ectx|exact pret|exact pc|exact abrs0].
      + (* the return type *)
        rewrite ofvT_shift in horet.
        have hctx' : pe_ctx (Γ ,,, inst_case_predicate_context p) (Γ' ,,, inst_case_predicate_context p').
        { apply pe_ctx_app; [exact hctx|]. unfold inst_case_predicate_context. rewrite -eu -ectx.
          now apply pe_inst_case_context. }
        destruct (IHret _ _ r hctx' (Good_case_ret Σ Γ ci p c brs hg) horet hrr) as (w & hw & hpw).
        exists (tCase ci (set_preturn p w) c brs). split.
        * rewrite -{1}(C3R.set_preturn_id p).
          eapply (trans_clos_map _ _ (fun y => tCase ci (set_preturn p y) c brs)); [|exact hw].
          intros a b0 r0. rewrite -(set_preturn_twice p a b0). now apply case_red_return.
        * apply pe_Case; cbn; [exact apar0|exact eu|exact ectx|exact hpw|exact pc|exact abrs0].
      + (* the scrutinee *)
        destruct (IHc Γ Γ' c1 hctx (Good_case_discr Σ Γ ci p c brs hg) hoc hrc) as (w & hw & hpw).
        exists (tCase ci p w brs). split; [|apply pe_Case; [exact apar0|exact eu|exact ectx|exact pret|exact hpw|exact abrs0]].
        eapply (trans_clos_map _ _ (fun y => tCase ci p y brs)); [|exact hw]. intros y z r0. now apply case_red_discr.
      + (* a branch *)
        have hT : All (fun br => is_true (on_free_vars xpredT (bbody br))) brs'.
        { apply forallb_All in hobrs. eapply All_impl; [exact hobrs|]. intros br h.
          move/andP: h => [_ h]. now rewrite ofvT_shift in h. }
        destruct (OnOne2_postpone (fun x y => bcontext x = bcontext y × pe (bbody x) (bbody y))
                    (fun br br' => on_Trel_eq (red1 Σ (Γ' ,,, inst_case_branch_context p' br)) bbody bcontext br br')
                    (fun br br' => on_Trel_eq (red1 Σ (Γ ,,, inst_case_branch_context p br)) bbody bcontext br br')
                    (fun br => Good Σ (Γ ,,, inst_case_branch_context p br) (bbody br))
                    (fun br => is_true (on_free_vars xpredT (bbody br))) brs brs' brs1) as (brs0 & ho0 & hp0).
        { eapply All2_impl; [exact abrs|]. intros x y [hc [hp ih]]. split; [split; [exact hc|exact hp]|].
          intros gx ty z [hz hcz].
          have hctxb : pe_ctx (Γ ,,, inst_case_branch_context p x) (Γ' ,,, inst_case_branch_context p' y).
          { apply pe_ctx_app; [exact hctx|]. unfold inst_case_branch_context. rewrite -eu -hc.
            now apply pe_inst_case_context. }
          destruct (ih _ _ _ hctxb gx ty hz) as (w & hw & hpw).
          exists {| bcontext := bcontext x; bbody := w |}. split; [exact (tc_branch_body Σ Γ p x w hw)|].
          split; [cbn; congruence|exact hpw]. }
        { exact (Good_case_brs Σ Γ ci p c brs hg). }
        { exact hT. }
        { exact hob. }
        exists (tCase ci p c brs0). split.
        * eapply (trans_clos_map _ _ (fun l => tCase ci p c l)); [|exact (OnOne2_tc _ _ _ ho0)].
          intros a b0 r0. now apply case_red_brs.
        * apply pe_Case; [exact apar0|exact eu|exact ectx|exact pret|exact pc|exact hp0].
    - (* projection: projection and cofix-proj roots, or a congruence *)
      intros pr c c' pc IHc Γ Γ' v hctx hg hofv hr.
      have hnl := Good_proj_hnl Σ Γ pr c hg.
      destruct (C3R.red1_tProj_inv hr) as
        [[(mfix & idx & args & narg & fn & -> & hu & ->)|(args & uu & arg & -> & hnth & ->)]|(c1 & -> & hrc)].
      + exact (pe_cofix_proj_root Σ Γ pr c mfix idx args narg fn hnl pc hu).
      + exact (pe_proj_root Σ Γ pr c uu args arg hnl pc hnth).
      + cbn in hofv. destruct (IHc Γ Γ' c1 hctx (Good_proj Σ Γ _ _ hg) hofv hrc) as (w & hw & hpw).
        exists (tProj pr w). split; [|now apply pe_Proj].
        eapply (trans_clos_map _ _ (fun y => tProj pr y)); [|exact hw]. intros y z r. now apply proj_red.
    - (* fixpoint: a type or a body steps *)
      intros mfix mfix' idx am Γ Γ' v hctx hg hofv hr.
      have am0 : All2 pe_defrel mfix mfix'.
      { eapply All2_impl; [exact am|]. intros x y [[h1 _] [[h2 _] [h3 h4]]]. exact (h1, (h2, (h3, h4))). }
      have hG := Good_fix_gen Σ Γ true mfix idx hg.
      cbn in hofv. apply forallb_All in hofv.
      destruct (C3R.red1_tFix_inv hr) as [(m1 & -> & ho)|(m1 & -> & ho)].
      + destruct (OnOne2_postpone pe_defrel (on_Trel_eq (red1 Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))
                    (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x)))
                    (fun d => Good Σ Γ (dtype d)) (fun d => is_true (on_free_vars xpredT (dtype d)))
                    mfix mfix' m1) as (m0 & ho0 & hp0).
        { eapply All2_impl; [exact am|]. intros x y [[h1 ih] [[h2 _] [h3 h4]]].
          split; [exact (h1, (h2, (h3, h4)))|]. intros gx ty z [hz e]. injection e as e1 e2 e3.
          destruct (ih _ _ _ hctx gx ty hz) as (w & hw & hpw).
          eexists; split; [exact (tc_def_type Σ Γ x w hw)|].
          cbn. split; [exact hpw|]. split; [rewrite -e2; exact h2|].
          cbn [dname rarg dtype dbody]. split; congruence. }
        { eapply All_impl; [exact hG|]. intros d [h _]. exact h. }
        { eapply All_impl; [exact hofv|]. intros d h. move/andP: h => [h _]. exact h. }
        { exact ho. }
        exists (tFix m0 idx). split; [|now apply pe_Fix].
        eapply (trans_clos_map _ _ (fun m => tFix m idx)); [|exact (OnOne2_tc _ _ _ ho0)].
        intros a b r. now apply fix_red_ty.
      + have hctxf : pe_ctx (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix')
          by (apply pe_ctx_app; [exact hctx|apply pe_ctx_fix_context; exact (All2_length am)]).
        destruct (OnOne2_postpone pe_defrel
                    (on_Trel_eq (red1 Σ (Γ' ,,, fix_context mfix')) dbody (fun x => (dname x, dtype x, rarg x)))
                    (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
                    (fun d => Good Σ (Γ ,,, fix_context mfix) (dbody d)) (fun d => is_true (on_free_vars xpredT (dbody d)))
                    mfix mfix' m1) as (m0 & ho0 & hp0).
        { eapply All2_impl; [exact am|]. intros x y [[h1 _] [[h2 ih] [h3 h4]]].
          split; [exact (h1, (h2, (h3, h4)))|]. intros gx ty z [hz e]. injection e as e1 e2 e3.
          destruct (ih _ _ _ hctxf gx ty hz) as (w & hw & hpw).
          eexists; split; [exact (tc_def_body Σ _ x w hw)|].
          cbn. split; [rewrite -e2; exact h1|]. split; [exact hpw|]. cbn [dname rarg dtype dbody]. split; congruence. }
        { eapply All_impl; [exact hG|]. intros d [_ h]. exact h. }
        { eapply All_impl; [exact hofv|]. intros d h. move/andP: h => [_ h]. now rewrite ofvT_shift in h. }
        { exact ho. }
        exists (tFix m0 idx). split; [|now apply pe_Fix].
        apply (fix_body_steps Σ true Γ mfix m0 idx).
        eapply OnOne2_impl; [exact ho0|]. intros d d0 h. exact (tc_def_body_inv Σ _ d d0 h).
    - (* cofixpoint: a type or a body steps *)
      intros mfix mfix' idx am Γ Γ' v hctx hg hofv hr.
      have hG := Good_fix_gen Σ Γ false mfix idx hg.
      cbn in hofv. apply forallb_All in hofv.
      destruct (C3R.red1_tCoFix_inv hr) as [(m1 & -> & ho)|(m1 & -> & ho)].
      + destruct (OnOne2_postpone pe_defrel (on_Trel_eq (red1 Σ Γ') dtype (fun x => (dname x, dbody x, rarg x)))
                    (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x)))
                    (fun d => Good Σ Γ (dtype d)) (fun d => is_true (on_free_vars xpredT (dtype d)))
                    mfix mfix' m1) as (m0 & ho0 & hp0).
        { eapply All2_impl; [exact am|]. intros x y [[h1 ih] [[h2 _] [h3 h4]]].
          split; [exact (h1, (h2, (h3, h4)))|]. intros gx ty z [hz e]. injection e as e1 e2 e3.
          destruct (ih _ _ _ hctx gx ty hz) as (w & hw & hpw).
          eexists; split; [exact (tc_def_type Σ Γ x w hw)|].
          cbn. split; [exact hpw|]. split; [rewrite -e2; exact h2|]. cbn [dname rarg dtype dbody]. split; congruence. }
        { eapply All_impl; [exact hG|]. intros d [h _]. exact h. }
        { eapply All_impl; [exact hofv|]. intros d h. move/andP: h => [h _]. exact h. }
        { exact ho. }
        exists (tCoFix m0 idx). split; [|now apply pe_CoFix].
        eapply (trans_clos_map _ _ (fun m => tCoFix m idx)); [|exact (OnOne2_tc _ _ _ ho0)].
        intros a b r. now apply cofix_red_ty.
      + have hctxf : pe_ctx (Γ ,,, fix_context mfix) (Γ' ,,, fix_context mfix')
          by (apply pe_ctx_app; [exact hctx|apply pe_ctx_fix_context; exact (All2_length am)]).
        destruct (OnOne2_postpone pe_defrel
                    (on_Trel_eq (red1 Σ (Γ' ,,, fix_context mfix')) dbody (fun x => (dname x, dtype x, rarg x)))
                    (on_Trel_eq (red1 Σ (Γ ,,, fix_context mfix)) dbody (fun x => (dname x, dtype x, rarg x)))
                    (fun d => Good Σ (Γ ,,, fix_context mfix) (dbody d)) (fun d => is_true (on_free_vars xpredT (dbody d)))
                    mfix mfix' m1) as (m0 & ho0 & hp0).
        { eapply All2_impl; [exact am|]. intros x y [[h1 _] [[h2 ih] [h3 h4]]].
          split; [exact (h1, (h2, (h3, h4)))|]. intros gx ty z [hz e]. injection e as e1 e2 e3.
          destruct (ih _ _ _ hctxf gx ty hz) as (w & hw & hpw).
          eexists; split; [exact (tc_def_body Σ _ x w hw)|].
          cbn. split; [rewrite -e2; exact h1|]. split; [exact hpw|]. cbn [dname rarg dtype dbody]. split; congruence. }
        { eapply All_impl; [exact hG|]. intros d [_ h]. exact h. }
        { eapply All_impl; [exact hofv|]. intros d h. move/andP: h => [_ h]. now rewrite ofvT_shift in h. }
        { exact ho. }
        exists (tCoFix m0 idx). split; [|now apply pe_CoFix].
        apply (fix_body_steps Σ false Γ mfix m0 idx).
        eapply OnOne2_impl; [exact ho0|]. intros d d0 h. exact (tc_def_body_inv Σ _ d d0 h).
    - (* primitive array: the default, the type, or a value steps *)
      intros pp pp' op Γ Γ' v hctx hg hofv hr.
      destruct op as [i|f|st|a a' hl hd hty hval].
      1-3: destruct (C3R.red1_tPrim_inv hr) as (arr & e & _); discriminate e.
      destruct (C3R.red1_tPrim_inv hr) as (arr & e & hc).
      apply (f_equal prim_arr_of) in e. cbn in e. injection e as <-.
      destruct (Good_prim_arr Σ Γ a hg) as (gd & gt & gv).
      cbn in hofv. rtoProp.
      destruct hc as [[(value & -> & ho)|(d & -> & hrd)]|(ty & -> & hrt)].
      + destruct (OnOne2_postpone pe (red1 Σ Γ') (red1 Σ Γ) (Good Σ Γ) (fun y => is_true (on_free_vars xpredT y))
                    _ _ value (All2_impl hval (fun x y '(hp, ih) => (hp, fun gx ty z hz => ih Γ Γ' z hctx gx ty hz)))
                    gv ltac:(now apply forallb_All) ho) as (l0 & ho0 & hp0).
        exists (tPrim (primArray; primArrayModel (set_array_value a l0))). split.
        * rewrite -{1}(C3R.set_array_value_id a).
          eapply (trans_clos_map _ _ (fun l => tPrim (primArray; primArrayModel (set_array_value a l))));
            [|exact (OnOne2_tc _ _ _ ho0)].
          intros l1 l2 r0. rewrite -(set_array_value_twice a l1 l2). now apply array_red_val.
        * apply pe_Prim. constructor; cbn; [exact hl|exact (fst hd)|exact (fst hty)|exact hp0].
      + destruct (snd hd Γ Γ' d hctx gd ltac:(assumption) hrd) as (w & hw & hpw).
        exists (tPrim (primArray; primArrayModel (set_array_default a w))). split.
        * rewrite -{1}(C3R.set_array_default_id a).
          eapply (trans_clos_map _ _ (fun x => tPrim (primArray; primArrayModel (set_array_default a x)))); [|exact hw].
          intros x1 x2 r0. rewrite -(set_array_default_twice a x1 x2). now apply array_red_def.
        * apply pe_Prim. constructor; cbn; [exact hl|exact hpw|exact (fst hty)|exact (All2_impl hval (fun x y h => fst h))].
      + destruct (snd hty Γ Γ' ty hctx gt ltac:(assumption) hrt) as (w & hw & hpw).
        exists (tPrim (primArray; primArrayModel (set_array_type a w))). split.
        * rewrite -{1}(C3R.set_array_type_id a).
          eapply (trans_clos_map _ _ (fun x => tPrim (primArray; primArrayModel (set_array_type a x)))); [|exact hw].
          intros x1 x2 r0. rewrite -(set_array_type_twice a x1 x2). now apply array_red_type.
        * apply pe_Prim. constructor; cbn; [exact hl|exact (fst hd)|exact hpw|exact (All2_impl hval (fun x y h => fst h))].
  Qed.

  (** **The parallel one-step postponement: CLOSED**, under the VISIBLE premises
      [Good Σ Γ t] (two halves: [typed_eta_safe], proved with no SR; preservation by
      E subject reduction, forecast T1) and [on_free_vars xpredT u] (target scoping). *)
  Theorem pe_postpone Γ t u v :
    Good Σ Γ t -> on_free_vars xpredT u -> pe t u -> red1 Σ Γ u v ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w v.
  Proof. intros hg ho h hr. exact (pe_postpone_gen t u h Γ Γ v (pe_ctx_refl Γ) hg ho hr). Qed.

  Corollary pe_postpone_statement_holds : pe_postpone_statement Σ (Good Σ).
  Proof. intros Γ t u v. exact (pe_postpone Γ t u v). Qed.

  (** **Transfer of scoping along [pe]: CLOSED.** A short corollary of [pe_to_eta]
      ([pe ⊆ eta1*]) and the landed [eta1_on_free_vars] (PCUICEtaScope.v), by
      induction on the closure. So the target premise [on_free_vars xpredT u] of
      [pe_postpone] follows from the same premise on the source. *)
  Lemma pe_on_free_vars P t u : pe t u -> on_free_vars P t -> on_free_vars P u.
  Proof.
    intros h. apply pe_to_eta in h.
    induction h as [x y r|x|x y z _ IH1 _ IH2]; intros hx.
    - exact (PCUICEtaScope.eta1_on_free_vars x y r P hx).
    - exact hx.
    - exact (IH2 (IH1 hx)).
  Qed.

  Corollary pe_postpone_src Γ t u v :
    Good Σ Γ t -> on_free_vars xpredT t -> pe t u -> red1 Σ Γ u v ->
    ∑ w, trans_clos (red1 Σ Γ) t w × pe w v.
  Proof. intros hg ho h hr. exact (pe_postpone Γ t u v hg (pe_on_free_vars _ _ _ h ho) h hr). Qed.

  (** The ZERO-step pullback, as its own named case: when the target takes no step,
      the source takes none either and the [pe] relation is unchanged. This is the
      only place where the source side is reflexive; [pe_postpone] itself always
      gives [red1⁺]. *)
  Lemma pe_postpone_zero Γ t u : pe t u -> ∑ w, red Σ Γ t w × pe w u.
  Proof. intros hp. exists t. split; [apply rt_refl|exact hp]. Qed.

  (** **(4) The iteration: [pe] followed by [red] is [red] followed by [pe]: CLOSED**,
      under the VISIBLE premises [Good Σ Γ t] (carried along the source reduction by
      [Good_red]), [on_free_vars xpredT u] (carried along the target reduction by
      [red_on_free_vars_cb]) and [on_ctx_free_vars xpredT Γ] (needed for the latter).

      INDUCTION PRINCIPLE: structural on the [clos_refl_trans] derivation of the
      target reduction, generalised over the source [t] and its premises. Three
      cases: [rt_step] calls [pe_postpone] (source side [red1⁺], weakened to [red]
      by [clos_t_rt]); [rt_refl] is the zero-step pullback [pe_postpone_zero];
      [rt_trans] composes, re-establishing [Good] on the new source by [Good_red]
      and the target scoping by [red_on_free_vars_cb]. No step needs a strict
      decrease: the derivation shrinks structurally.

      Proved by this new induction, not by instantiating a landed mirror.
      [HR_strong_commutation_modulo] (PCUICEtaHRCommutationA1.v) cannot be
      instantiated, for two reasons: its tile allows at most ONE [R] step
      ([clos_refl R]) where [pe_postpone] needs [red1⁺] (the β-head case takes two
      steps on [(λx. (λy. M) x) a]), and its invariant [Q] sits on the common source
      (here the η-REDUCT [u]) while [Good] is a property of the η-EXPANSION [t], which
      no invariance of [Q] under [S] steps can supply. The C3R [commutes] machinery
      (PCUICEtaC3BR.v) is the forward direction (the [peta] SOURCE reduces), so it
      does not fit this backward postponement either. *)
  Theorem pe_red_postpone Γ t u v :
    on_ctx_free_vars xpredT Γ ->
    Good Σ Γ t -> on_free_vars xpredT u -> pe t u -> red Σ Γ u v ->
    ∑ w, red Σ Γ t w × pe w v.
  Proof.
    intros hctx hg ho hp hr. induction hr as [u v r|u|u u1 v h1 IH1 h2 IH2] in t, hg, ho, hp |- *.
    - destruct (pe_postpone Γ t u v hg ho hp r) as (w & hw & hpw).
      exists w. split; [now apply clos_t_rt|exact hpw].
    - exact (pe_postpone_zero Γ t u hp).
    - destruct (IH1 t hg ho hp) as (w1 & hw1 & hp1).
      have ho1 : on_free_vars xpredT u1
        := @PCUICClosedTyp.red_on_free_vars_cb cf xpredT (Σ, Monomorphic_ctx) Γ u u1 cb h1 ho hctx.
      destruct (IH2 w1 (Good_red _ _ _ hg hw1) ho1 hp1) as (w & hw & hpw).
      exists w. split; [eapply rt_trans; eassumption|exact hpw].
  Qed.

End Assembly.

(** ** The η half of the backward simulation is FALSE (building refutation)

  The "convert first, postpone second" route needs the mirror of [R_c_back1] for η:
  an [eta1] step on [canon t] read back as [eta1] steps on [t].

  STEP FORM, as pinned: the lemma fails in EVERY form — not only "exactly one step",
  but also [clos_refl eta1] and [eta1*] ([eta1_canon_backsim_false] refutes the
  [eta1*] form, and the witness has NO η step at all, so the weaker forms fail with
  the same witness).

  Why the expectation ("[canon] rewrites only λ DOMAINS, so it cannot create or
  remove an η-redex outside a domain") does not hold: a λ domain is PART of the η
  pattern. The η rule's left side is [λ _:A. (lift0 1 f) (tRel 0)], and the side
  condition is that the body is a [lift0 1], i.e. that the bound variable does NOT
  occur in [f] — including inside [f]'s own λ domains. Erasing those domains can
  delete the only occurrence, turning a non-redex into a redex. Base [red1] has no
  such side condition, which is why [PCUICEtaT8BackSim] goes through.

  Witness, TYPABLE (typing proved below, [lb_t_typed]): in [Γ = P : Prop],
    [lb_t := λ _:Prop. ((λ _:Prop. λ _:x. P) x)],
  where [x] is the outer variable. The inner λ's DOMAIN is [x], so the middle λ is
  not a [lift0 1] of anything ([lift 1 1] never yields [tRel 1]) and [lb_t] has no η
  step at all ([lb_t_eta_normal]). After [canon] that domain becomes [canon_dom],
  the middle λ becomes [lift0 1 lb_u], and [canon lb_t] η-contracts
  ([lb_canon_eta]). *)

Definition lb_inner : term := tLambda si_na (tRel 1) (tRel 3).
Definition lb_f : term := tLambda si_na si_P lb_inner.
Definition lb_b : term := tApp lb_f (tRel 0).
Definition lb_t : term := tLambda si_na si_P lb_b.
Definition lb_u : term := tLambda canon_la canon_dom (tLambda canon_la canon_dom (tRel 2)).
Definition lb_Γ : context := [vass si_na si_P].

Lemma lb_canon_t : canon lb_t = eta_redex canon_la canon_dom lb_u.
Proof. reflexivity. Qed.

(** [canon lb_t] η-contracts to [lb_u]. *)
Lemma lb_canon_eta : eta1 (canon lb_t) lb_u.
Proof. rewrite lb_canon_t. apply eta_red. Qed.

(** [lb_t] itself has no η step: the root rule is blocked by the domain [tRel 1]
    (no term lifts to it at level 1), and every subterm is η-normal. *)
Lemma lb_inner_eta_normal y : eta1 lb_inner y -> False.
Proof.
  intros h. remember lb_inner as z eqn:E. revert E.
  destruct h; intros E; unfold lb_inner in E; try discriminate E;
    injection E as E1 E2 E3; subst;
    first [ congruence | exact (eta1_tRel_absurd _ _ ltac:(eassumption)) ].
Qed.

Lemma lb_f_eta_normal y : eta1 lb_f y -> False.
Proof.
  intros h. remember lb_f as z eqn:E. revert E.
  destruct h; intros E; unfold lb_f in E; try discriminate E;
    injection E as E1 E2 E3; subst;
    first [ congruence
          | exact (eta_normal_Sort _ _ ltac:(eassumption))
          | exact (lb_inner_eta_normal _ ltac:(eassumption)) ].
Qed.

Lemma lb_b_eta_normal y : eta1 lb_b y -> False.
Proof.
  intros h. remember lb_b as z eqn:E. revert E.
  destruct h; intros E; unfold lb_b in E; try discriminate E;
    injection E as E1 E2; subst;
    first [ exact (lb_f_eta_normal _ ltac:(eassumption))
          | exact (eta1_tRel_absurd _ _ ltac:(eassumption)) ].
Qed.

(** The decisive step: the root η rule is blocked on [lb_t], because the inner λ has
    the outer variable in its DOMAIN, and [lift 1 1] never produces [tRel 1]. *)
Lemma lb_t_eta_normal y : eta1 lb_t y -> False.
Proof.
  intros h. remember lb_t as z eqn:E. revert E.
  destruct h; intros E; unfold lb_t in E; try discriminate E.
  - (* eta_red *)
    injection E as E1 E2 E3. unfold lb_f in E3.
    match type of E3 with context [lift 1 0 ?x] => destruct x end; cbn in E3; try discriminate E3.
    injection E3 as _ _ E4. unfold lb_inner in E4.
    match type of E4 with context [lift 1 1 ?x] => destruct x end; cbn in E4; try discriminate E4.
    injection E4 as _ E5 _.
    match type of E5 with context [lift 1 1 ?x] => destruct x end; cbn in E5; try discriminate E5.
    injection E5 as E5. match goal with n : nat |- _ => destruct (Nat.leb_spec0 1 n) end; lia.
  - (* abs_eta_l: a step in the domain [si_P], a sort *)
    injection E as _ E _. subst. exact (eta_normal_Sort _ _ ltac:(eassumption)).
  - (* abs_eta_r: a step in the body [lb_b] *)
    injection E as _ _ E. subst. exact (lb_b_eta_normal _ ltac:(eassumption)).
Qed.

Lemma lb_u_ne : lb_u <> canon lb_t.
Proof. rewrite lb_canon_t. intros e. unfold lb_u in e. congruence. Qed.

(** **The η backward simulation is FALSE**, in its [eta1*] form (hence also in the
    one-step and [clos_refl] forms). *)
Definition eta1_canon_backsim_statement : Type :=
  forall t w, eta1 (canon t) w -> ∑ t', clos_refl_trans eta1 t t' × canon t' = w.

Theorem eta1_canon_backsim_false : eta1_canon_backsim_statement -> False.
Proof.
  intros H. destruct (H lb_t lb_u lb_canon_eta) as (t' & hr & e).
  rewrite (rt_from_normal eta1 lb_t t' lb_t_eta_normal hr) in e.
  exact (lb_u_ne (eq_sym e)).
Qed.

(** The witness is TYPABLE: [lb_t : Π _:Prop. Π _:x. Prop] in [Γ = P : Prop]. No
    conversion step is needed: the application [lb_f x] matches its domain [Prop]
    syntactically, and the blocking occurrence of [x] sits in the domain of the
    INNER λ. *)
Section LambdaBlockTyping.
  #[local] Existing Instance default_checker_flags.

  Theorem lb_t_typed : wfE si_Σ × ∑ T, si_Σ ;;; lb_Γ |-E lb_t : T.
  Proof.
    split; [exact si_wfE|].
    have hw0 : wf_localE si_Σ lb_Γ := iv_wf_P si_Σ [] localenv_nil.
    have hw1 := iv_wf_P si_Σ _ hw0.
    have hw2 := iv_wf_P si_Σ _ hw1.
    have hR1 : si_Σ ;;; (lb_Γ ,, vass si_na si_P) ,, vass si_na si_P |-E tRel 1 : tSort sProp
      := typeE_Rel _ _ 1 (vass si_na si_P) hw2 eq_refl.
    have hw3 := iv_wf_vass si_Σ _ si_na (tRel 1) sProp hw2 hR1 eq_refl.
    have hR3 : si_Σ ;;; ((lb_Γ ,, vass si_na si_P) ,, vass si_na si_P) ,, vass si_na (tRel 1)
                 |-E tRel 3 : tSort sProp
      := typeE_Rel _ _ 3 (vass si_na si_P) hw3 eq_refl.
    have hinner : si_Σ ;;; (lb_Γ ,, vass si_na si_P) ,, vass si_na si_P
                    |-E lb_inner : tProd si_na (tRel 1) si_P.
    { apply typeE_Lambda; [exact (iv_vass si_Σ _ si_na (tRel 1) sProp hR1 eq_refl)|exact hR3]. }
    have hf : si_Σ ;;; lb_Γ ,, vass si_na si_P
                |-E lb_f : tProd si_na si_P (tProd si_na (tRel 1) si_P).
    { apply typeE_Lambda; [exact (iv_vass si_Σ _ si_na si_P _ (iv_P_typed si_Σ _ hw1) eq_refl)|exact hinner]. }
    have hcod : si_Σ ;;; (lb_Γ ,, vass si_na si_P) ,, vass si_na si_P
                  |-E tProd si_na (tRel 1) si_P : tSort (Sort.sort_of_product sProp (Sort.super sProp)).
    { apply typeE_Prod; [exact (iv_vass_s si_Σ _ si_na (tRel 1) sProp hR1 eq_refl)|].
      exact (iv_P_typed si_Σ _ hw3). }
    have hprod : si_Σ ;;; lb_Γ ,, vass si_na si_P
                   |-E tProd si_na si_P (tProd si_na (tRel 1) si_P)
                   : tSort (Sort.sort_of_product (Sort.super sProp)
                              (Sort.sort_of_product sProp (Sort.super sProp))).
    { apply typeE_Prod; [|exact hcod].
      exact (iv_vass_s si_Σ _ si_na si_P _ (iv_P_typed si_Σ _ hw1) eq_refl). }
    have hx : si_Σ ;;; lb_Γ ,, vass si_na si_P |-E tRel 0 : si_P
      := typeE_Rel _ _ 0 (vass si_na si_P) hw1 eq_refl.
    have happ := typeE_App _ _ lb_f si_na si_P (tProd si_na (tRel 1) si_P) _ (tRel 0) hprod hf hx.
    eexists. unfold lb_t, lb_b.
    apply typeE_Lambda; [exact (iv_vass si_Σ _ si_na si_P _ (iv_P_typed si_Σ _ hw0) eq_refl)|exact happ].
  Qed.

End LambdaBlockTyping.

(** ** History of the [eta_safe] invariant (every change so far)

  Change 1: the primitive POSITION was added.
  - ADDED: a clause for the arguments of an applied primitive operation.
  - Bought: the primitive-operation root [pp_prim]; an η-expansion [λx. lit x] of a
    literal argument is excluded, so the redex's arguments stay literals.
  - Still excludes: a λ as the scrutinee of [tCase], as the argument of [tProj], as
    the [rarg]-th argument of an applied fixpoint, and the new primitive position.

  Change 2: the primitive CLAUSE was restated as "no applied primitive value".
  - DROPPED: the dependence on [prim_op_of Σ c = Some op], so [pp_prim] lost that
    premise and became a STRONGER lemma. ADDED: [notPrimHead] on every application
    head.
  - Bought: the clause follows from typing with no extra hypothesis
    ([typed_prim_not_prod]), because a primitive value never has a product type.
  - Still excludes: the same four positions; the primitive clause now excludes EVERY
    applied primitive value, not only an argument of a registered operation.

  Both changes moved only the primitive clause. The λ clause has never changed: it
  still inspects the DOMAIN ([tLambda _ A b => eta_safe Σ A && eta_safe Σ b]), which
  is what makes [Good] fail to transfer from [T] to [canon T]. Any further change to
  [eta_safe] is reported before it is made.

  Induction principle for the mixed-chain sketch: NOT APPLICABLE. The sketch was to
  induct on the CANONICAL chain's length, fixed before lifting (never on the lifted
  chain, which can be longer), but the lifting step it rests on is false
  ([eta1_canon_backsim_false]), so no such induction is written. *)

