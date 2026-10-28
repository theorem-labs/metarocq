(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 8: A2 (spec ⇒ join), and obligation 8
      at [FInstFollowKernel]

    [I5_spec_to_join] : I5_eta_l_case r Σ -> closed Γ -> open t -> open u ->
                        Σ ;;; Γ ⊢ t ≤sE[pb] u -> JoinE r Σ Γ pb t u
    [I5_obligation8_FollowKernel] :
      I5_eta_l_case FInstFollowKernel Σ -> I5_statement FInstFollowKernel Σ

  Induction on [cumulSpecE0] ([cumulSpecE0_rect]), every rule a lemma below:
  the nine reduction rules by one [red1] step; [cumulE_Trans] by A3
  ([I5_join_trans]); [cumulE_Sym] by U1' symmetry at [Conv] and
  [(Conv,0) ⊆ (pb,0)]; the congruences by [BE] chains; the constructor spine by
  site K3 ([cumul_construct_finst], true at both rules after repair (a));
  [cumul_eta_l] by the premise [I5_eta_l_case] (obligation 9).

  **Hypotheses satisfiable (FRAC's rule):** [wf Σ] by any well-formed
  environment; the scoping premises by any scoped context and terms;
  [I5_eta_l_case] is obligation 9's statement. C4-side (through A3).

  ** The step relation [BE]

  [JoinE] runs on canonical terms under [R_c ∪ eta1]. Congruences are easier on
  raw terms, so the proof works with

    [BE Γ := (red1 Σ Γ ∪ eta1 ∪ "same canon")*]

  on raw terms, and moves between the two:
  - [BE_RE] : [BE Γ x y -> (R_c ∪ eta1)* (canon x) (canon y)] (obligation 3's
    [red1_R_c], obligation 5's [eta1_canon]);
  - [RE_BE] : [(R_c ∪ eta1)* x y -> BE Γ x y] (an [R_c] step is a [red1] step
    followed by a "same canon" step, [canon_idem]).
  Every position of every node lifts a [BE] chain by its [red1] and [eta1]
  congruence constructors ([BE_map], [BE_list]), because [canon] is a
  homomorphism on every position.

  ** Binders whose context differs between the two sides

  The spec compares the bodies of [LetIn] and [Case] in the LEFT term's context.
  The right term's body lives in a different context (different let-bodies,
  different parameters). Each such congruence is split by A3 ([I5_join_trans])
  into two joins through a middle term:
  1. change the bodies, keeping the left term's context fields — both chains
     then run in exactly the context the induction hypothesis gives;
  2. change the context fields, keeping the (now equal) bodies — no body
     chain is needed, and the bodies are compared by reflexivity.
  So no context-reduction lemma is needed. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations Require Import Equations.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICInduction
     PCUICEquality PCUICReduction PCUICOnFreeVars PCUICTyping PCUICUnivSubstitutionConv
     PCUICCumulativitySpec PCUICCumulativitySpecEta
     PCUICEtaDefs PCUICEtaScope PCUICEtaCanon PCUICEtaCanonRed PCUICEtaCanonEta
     PCUICEtaFInst PCUICEtaFInstEquiv PCUICEtaFInstC1c PCUICEtaFInstGlue
     PCUICEtaReduction PCUICEtaC1aR PCUICEtaI5 PCUICEtaI5Trans PCUICClosedBodies.
From MetaRocq.PCUIC Require PCUICOnFreeVarsConv.

(** ** Witness lists from pointwise joins *)

Lemma All2_ex3 {A B C D : Type} (P : A -> C -> Type) (Q : B -> D -> Type) (S : C -> D -> Type) l l' :
  All2 (fun a b => ∑ c d, P a c × Q b d × S c d) l l' ->
  ∑ lc ld, All2 P l lc × All2 Q l' ld × All2 S lc ld.
Proof.
  induction 1 as [|a b l l' (c & d & hp & hq & hs) _ (lc & ld & h1 & h2 & h3)].
  - exists [], []. repeat split; constructor.
  - exists (c :: lc), (d :: ld). repeat split; constructor; assumption.
Qed.

Lemma All2_mid {A B : Type} (P1 : A -> B -> Type) (P2 : B -> A -> Type) (R : A -> A -> Type)
  (f : A -> A -> B) l l' :
  All2 R l l' -> (forall x y, R x y -> P1 x (f x y) × P2 (f x y) y) ->
  ∑ lm, All2 P1 l lm × All2 P2 lm l'.
Proof.
  intros h hf. induction h as [|x y l l' hxy _ (lm & h1 & h2)].
  - exists []. split; constructor.
  - destruct (hf x y hxy) as [p1 p2]. exists (f x y :: lm). split; constructor; assumption.
Qed.

(** [fix_context] reads only the names and the types. *)
Lemma mapi_rec_nt (f : nat -> def term -> context_decl)
  (hf : forall i d d', dname d = dname d' -> dtype d = dtype d' -> f i d = f i d') l l' n :
  map (fun d => (dname d, dtype d)) l = map (fun d => (dname d, dtype d)) l' ->
  mapi_rec f l n = mapi_rec f l' n.
Proof.
  induction l as [|d l IH] in l', n |- *; destruct l' as [|d' l']; intros e; cbn in e |- *;
    try discriminate; [reflexivity|].
  injection e as e1 e2 e3. rewrite (hf n d d' e1 e2) (IH l' (S n) e3). reflexivity.
Qed.

Lemma fix_context_nt (l l' : mfixpoint term) :
  map (fun d => (dname d, dtype d)) l = map (fun d => (dname d, dtype d)) l' ->
  fix_context l = fix_context l'.
Proof.
  intros e. unfold fix_context, mapi. f_equal. apply mapi_rec_nt; [|exact e].
  intros i d d' e1 e2. now rewrite e1 e2.
Qed.

Lemma canon_mkApps f l : canon (mkApps f l) = mkApps (canon f) (map canon l).
Proof. induction l as [|a l IH] in f |- *; cbn; [reflexivity|]. now rewrite IH. Qed.

(** F-inst comparisons are monotone in [napp]: the variance does not read
    [napp], and the mode only moves from [Conv] to [pb]. *)
Lemma finst_inst_napp_mono r Σ cu pb gr n m u u' :
  RelationClasses.subrelation (cu Conv) (cu pb) -> n <= m ->
  cmp_global_instance_eta r Σ cu pb gr n u u' -> cmp_global_instance_eta r Σ cu pb gr m u u'.
Proof.
  intros sub hle. unfold cmp_global_instance_eta.
  rewrite (global_variance_eta_napp_irrelevant r (lookup_env Σ) gr n m).
  unfold finst_mode. destruct (Nat.leb_spec (head_arity Σ gr) n) as [h|h].
  - rewrite (proj2 (Nat.leb_le _ _) (Nat.le_trans _ _ _ h hle)). intros x; exact x.
  - apply (cmp_opt_variance_Conv_sub cu). destruct (_ <=? m); [exact sub|intros x y e; exact e].
Qed.

Lemma finst_napp_mono r Σ cu cs pb n m t u :
  RelationClasses.subrelation (cu Conv) (cu pb) ->
  eq_term_upto_univ_eta_napp r Σ cu cs pb n t u -> n <= m ->
  eq_term_upto_univ_eta_napp r Σ cu cs pb m t u.
Proof.
  intros sub e. revert sub. induction e in m |- *; intros sub hle.
  all: try solve [constructor; assumption].
  - constructor; [apply IHe1; [exact sub|lia]|assumption].
  - constructor. eapply finst_inst_napp_mono; [exact sub|exact hle|eassumption].
  - constructor. eapply finst_inst_napp_mono; [exact sub|exact hle|eassumption].
Qed.

Lemma open_app (Γ Δ : context) t :
  on_free_vars (shiftnP #|Δ| (shiftnP #|Γ| xpred0)) t -> is_open_term (Γ ,,, Δ) t.
Proof.
  intros h.
  have e : shiftnP (#|Δ| + #|Γ|) xpred0 =1 shiftnP #|Δ| (shiftnP #|Γ| xpred0)
    by intros i; symmetry; apply shiftnP_add.
  rewrite app_context_length (on_free_vars_ext _ _ t e). exact h.
Qed.

Lemma open_snoc (Γ : context) (d : context_decl) t :
  on_free_vars (shiftnP 1 (shiftnP #|Γ| xpred0)) t -> is_open_term (Γ ,, d) t.
Proof. intros h. exact (open_app Γ [d] t h). Qed.

Lemma closed_snoc_vass (Γ : context) na A :
  is_closed_context Γ -> is_open_term Γ A -> is_closed_context (Γ ,, vass na A).
Proof. intros h1 h2. rewrite on_free_vars_ctx_snoc h1 /=. exact h2. Qed.

Lemma closed_snoc_vdef (Γ : context) na b A :
  is_closed_context Γ -> is_open_term Γ b -> is_open_term Γ A -> is_closed_context (Γ ,, vdef na b A).
Proof.
  intros h1 h2 h3. rewrite on_free_vars_ctx_snoc h1 /=.
  change (on_free_vars (shiftnP #|Γ| xpred0) b && on_free_vars (shiftnP #|Γ| xpred0) A).
  now rewrite h2 h3.
Qed.

Lemma canon_array lvl l d t :
  canon (tPrim (primArray; primArrayModel {| array_level := lvl; array_value := l; array_default := d; array_type := t |}))
  = tPrim (primArray; primArrayModel
      {| array_level := lvl; array_value := map canon l; array_default := canon d; array_type := canon t |}).
Proof. reflexivity.
Qed.

Section A2.

  Context {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ) (r : finst_construct_rule).

  Local Notation cu := (compare_universe Σ).
  Local Notation cs := (compare_sort Σ).
  Local Notation RF pb n := (eq_term_upto_univ_eta_napp r Σ.1 cu cs pb n).
  Local Notation RE Γ := (union (R_c Σ Γ) eta1).
  Local Notation J Γ pb := (JoinE r Σ Γ pb).

  Definition be_step Γ (x y : term) : Type := ((red1 Σ Γ x y + eta1 x y) + (canon x = canon y))%type.
  Local Notation BE Γ := (clos_refl_trans (be_step Γ)).

  (** ** Between [BE] and the canonical join steps *)

  Lemma BE_RE Γ x y : BE Γ x y -> clos_refl_trans (RE Γ) (canon x) (canon y).
  Proof.
    induction 1 as [x y [[s|s]|s]|x|x y z _ IH1 _ IH2].
    - destruct (red1_R_c Σ Γ x y s) as [? h|]; [apply rt_step; left; exact h|apply rt_refl].
    - destruct (eta1_canon x y s) as [? h|]; [apply rt_step; right; exact h|apply rt_refl].
    - rewrite s. apply rt_refl.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma RE_BE Γ x y : clos_refl_trans (RE Γ) x y -> BE Γ x y.
  Proof.
    induction 1 as [x y [[y0 [hr ->]]|he]|x|x y z _ IH1 _ IH2].
    - eapply rt_trans; [apply rt_step; left; left; exact hr|].
      apply rt_step; right. symmetry. apply canon_idem.
    - apply rt_step; left; right; exact he.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma BE_canon Γ t : BE Γ t (canon t).
  Proof. apply rt_step; right. symmetry. apply canon_idem. Qed.

  Lemma JoinE_BE Γ pb t u : J Γ pb t u -> ∑ v v', BE Γ t v × BE Γ u v' × RF pb 0 v v'.
  Proof.
    intros (v & v' & hv & hv' & e). exists v, v'. repeat split.
    - eapply rt_trans; [apply BE_canon|exact (RE_BE _ _ _ hv)].
    - eapply rt_trans; [apply BE_canon|exact (RE_BE _ _ _ hv')].
    - exact e.
  Qed.

  Lemma BE_JoinE Γ pb t u v v' :
    BE Γ t v -> BE Γ u v' -> RF pb 0 (canon v) (canon v') -> J Γ pb t u.
  Proof.
    intros hv hv' e. exists (canon v), (canon v').
    repeat split; [exact (BE_RE _ _ _ hv)|exact (BE_RE _ _ _ hv')|exact e].
  Qed.

  (** A comparison at the end of a join, moved onto the canonical forms. *)
  Lemma RF_canon pb n x y : RF pb n x y -> RF pb n (canon x) (canon y).
  Proof. exact (finst_canon r Σ.1 cu cs (a3_refl_s Σ) pb n x y). Qed.

  Lemma RF_refl pb n x : RF pb n x x.
  Proof. apply compare_term_eta_refl. Qed.

  (** ** Lifting [BE] chains through positions *)

  Lemma BE_map Γ Γ' (f : term -> term) :
    (forall x y, red1 Σ Γ x y -> red1 Σ Γ' (f x) (f y)) ->
    (forall x y, eta1 x y -> eta1 (f x) (f y)) ->
    (forall x y, canon x = canon y -> canon (f x) = canon (f y)) ->
    forall x y, BE Γ x y -> BE Γ' (f x) (f y).
  Proof.
    intros hr he hc x y h.
    induction h as [x y [[s|s]|s]|x|x y z _ IH1 _ IH2].
    - apply rt_step; left; left; exact (hr _ _ s).
    - apply rt_step; left; right; exact (he _ _ s).
    - apply rt_step; right; exact (hc _ _ s).
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma BE_list Γ Γ' (F : list term -> term) :
    (forall l l', OnOne2 (red1 Σ Γ) l l' -> red1 Σ Γ' (F l) (F l')) ->
    (forall l l', OnOne2 eta1 l l' -> eta1 (F l) (F l')) ->
    (forall l l', map canon l = map canon l' -> canon (F l) = canon (F l')) ->
    forall l l', All2 (fun x y => BE Γ x y) l l' -> BE Γ' (F l) (F l').
  Proof.
    intros hr he hc l l' h.
    enough (H : forall pre, BE Γ' (F (pre ++ l)) (F (pre ++ l'))) by exact (H []).
    induction h as [|x x' l l' hx _ IH]; intros pre; [apply rt_refl|].
    eapply rt_trans.
    - eapply (BE_map Γ Γ' (fun y => F (pre ++ y :: l))); [| | |exact hx].
      + intros a b s. apply hr. apply OnOne2_app. constructor. exact s.
      + intros a b s. apply he. apply OnOne2_app. constructor. exact s.
      + intros a b e. apply hc. rewrite !map_app /=. now rewrite e.
    - specialize (IH (pre ++ [x'])). rewrite <- !app_assoc in IH. exact IH.
  Qed.

  (** The trivial joins. *)
  Lemma JoinE_canon_eq Γ pb t u : canon t = canon u -> J Γ pb t u.
  Proof.
    intros e. exists (canon t), (canon u). repeat split; [apply rt_refl|apply rt_refl|].
    rewrite e. apply RF_refl.
  Qed.

  Lemma JoinE_red1 Γ pb t u : red1 Σ Γ t u -> J Γ pb t u.
  Proof.
    intros h. apply (BE_JoinE Γ pb t u u u); [apply rt_step; left; left; exact h|apply rt_refl|apply RF_refl].
  Qed.

  (** ** Case *)

  (** Branch bodies, each in its own branch context. *)
  Lemma BE_case_brs Γ ci p c brs brs' :
    All2 (fun br br' => (bcontext br' = bcontext br) ×
            BE (Γ ,,, inst_case_branch_context p br) (bbody br) (bbody br')) brs brs' ->
    BE Γ (tCase ci p c brs) (tCase ci p c brs').
  Proof.
    intros h.
    enough (H : forall pre, BE Γ (tCase ci p c (pre ++ brs)) (tCase ci p c (pre ++ brs'))) by exact (H []).
    induction h as [|br br' l l' [hc hb] _ IH]; intros pre; [apply rt_refl|].
    destruct br as [bc bb], br' as [bc' bb']; cbn in hc, hb; subst bc'.
    eapply rt_trans.
    - eapply (BE_map (Γ ,,, inst_case_branch_context p {| bcontext := bc; bbody := bb |}) Γ
                (fun y => tCase ci p c (pre ++ {| bcontext := bc; bbody := y |} :: l)));
        [| | |exact hb].
      + intros a b s. apply case_red_brs. apply OnOne2_app. constructor. split; [exact s|reflexivity].
      + intros a b s. apply case_eta_brs. apply OnOne2_app. constructor. split; [exact s|reflexivity].
      + intros a b e. cbn [canon]. rewrite !map_app. cbn [map]. unfold canon_branch; cbn.
        now rewrite e.
    - specialize (IH (pre ++ [{| bcontext := bc; bbody := bb' |}])).
      rewrite <- !app_assoc in IH. exact IH.
  Qed.

  (** Step 1 of the split: change the return type and the branch bodies, keeping
      the left term's parameters, instance, predicate context and branch
      contexts. Both chains run in the induction hypothesis's own contexts. *)
  Lemma JoinE_Case_bodies Γ pb ci pars u ctx ret ret' c brs brs1 :
    J (Γ ,,, inst_case_predicate_context (mk_predicate pars u ctx ret)) Conv ret ret' ->
    All2 (fun br b1 => (bcontext br = bcontext b1) ×
            J (Γ ,,, inst_case_branch_context (mk_predicate pars u ctx ret) br) Conv (bbody br) (bbody b1))
      brs brs1 ->
    J Γ pb (tCase ci (mk_predicate pars u ctx ret) c brs) (tCase ci (mk_predicate pars u ctx ret') c brs1).
  Proof.
    intros hret hbrs.
    destruct (JoinE_BE _ _ _ _ hret) as (vr & vr' & hvr & hvr' & er).
    assert (hw : All2 (fun br b1 => ∑ bl b1',
               (bcontext bl = bcontext br ×
                BE (Γ ,,, inst_case_branch_context (mk_predicate pars u ctx ret) br) (bbody br) (bbody bl)) ×
               (bcontext b1' = bcontext b1 ×
                BE (Γ ,,, inst_case_branch_context (mk_predicate pars u ctx ret) b1) (bbody b1) (bbody b1')) ×
               (bcontext bl = bcontext b1' × RF Conv 0 (canon (bbody bl)) (canon (bbody b1')))) brs brs1).
    { eapply All2_impl; [exact hbrs|]. intros br b1 [hc hj].
      destruct (JoinE_BE _ _ _ _ hj) as (v & v' & hv & hv' & e).
      exists {| bcontext := bcontext br; bbody := v |}, {| bcontext := bcontext b1; bbody := v' |}; cbn.
      refine ((eq_refl, hv), ((eq_refl, _), (hc, RF_canon _ _ _ _ e))).
      rewrite /inst_case_branch_context -hc. exact hv'. }
    destruct (All2_ex3 _ _ _ _ _ hw) as (lbl & lbr & hl & hr & hlr).
    apply (BE_JoinE Γ pb _ _ (tCase ci (mk_predicate pars u ctx vr) c lbl)
                              (tCase ci (mk_predicate pars u ctx vr') c lbr)).
    - eapply rt_trans.
      + eapply (BE_map (Γ ,,, inst_case_predicate_context (mk_predicate pars u ctx ret)) Γ
                  (fun x => tCase ci (mk_predicate pars u ctx x) c brs)); [| | |exact hvr].
        * intros a b s. exact (case_red_return _ _ ci (mk_predicate pars u ctx a) b c brs s).
        * intros a b s. exact (case_eta_return ci (mk_predicate pars u ctx a) b c brs s).
        * intros a b e. cbn [canon]. unfold canon_predicate; cbn. now rewrite e.
      + apply BE_case_brs. exact hl.
    - eapply rt_trans.
      + eapply (BE_map (Γ ,,, inst_case_predicate_context (mk_predicate pars u ctx ret)) Γ
                  (fun x => tCase ci (mk_predicate pars u ctx x) c brs1)); [| | |exact hvr'].
        * intros a b s. exact (case_red_return _ _ ci (mk_predicate pars u ctx a) b c brs1 s).
        * intros a b s. exact (case_eta_return ci (mk_predicate pars u ctx a) b c brs1 s).
        * intros a b e. cbn [canon]. unfold canon_predicate; cbn. now rewrite e.
      + apply BE_case_brs. exact hr.
    - cbn [canon]. constructor.
      + unfold eq_predicate, canon_predicate; cbn. split; [|split; [|split]].
        * apply All2_map. apply All2_refl. intros x. apply RF_refl.
        * reflexivity.
        * apply eq_context_upto_names_refl'.
        * exact (RF_canon _ _ _ _ er).
      + apply RF_refl.
      + unfold eq_branches, eq_branch. apply All2_map. eapply All2_impl; [exact hlr|].
        intros x y [hc e]. unfold canon_branch; cbn. split; [|exact e].
        rewrite hc. apply eq_context_upto_names_refl'.
  Qed.

  (** Step 2 of the split: change the parameters, the discriminee, the instance
      and the binder names, with the bodies already equal. *)
  Lemma JoinE_Case_heads Γ pb ci pars u ctx pars' u' ctx' ret c c' brs brs' :
    All2 (J Γ Conv) pars pars' ->
    cmp_universe_instance (cu Conv) u u' ->
    eq_context_upto_names ctx ctx' ->
    J Γ Conv c c' ->
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') × (bbody br = bbody br')) brs brs' ->
    J Γ pb (tCase ci (mk_predicate pars u ctx ret) c brs) (tCase ci (mk_predicate pars' u' ctx' ret) c' brs').
  Proof.
    intros hpars hu hctx hc hbrs.
    destruct (JoinE_BE _ _ _ _ hc) as (vc & vc' & hvc & hvc' & ec).
    assert (hw : All2 (fun a b => ∑ x y, BE Γ a x × BE Γ b y × RF Conv 0 (canon x) (canon y)) pars pars').
    { eapply All2_impl; [exact hpars|]. intros a b hj.
      destruct (JoinE_BE _ _ _ _ hj) as (x & y & hx & hy & e).
      exists x, y. exact (hx, (hy, RF_canon _ _ _ _ e)). }
    destruct (All2_ex3 _ _ _ _ _ hw) as (lx & ly & hlx & hly & hxy).
    apply (BE_JoinE Γ pb _ _ (tCase ci (mk_predicate lx u ctx ret) vc brs)
                              (tCase ci (mk_predicate ly u' ctx' ret) vc' brs')).
    - eapply rt_trans.
      + eapply (BE_list Γ Γ (fun l => tCase ci (mk_predicate l u ctx ret) c brs)); [| | |exact hlx].
        * intros l l' s. exact (case_red_param _ _ ci (mk_predicate l u ctx ret) l' c brs s).
        * intros l l' s. exact (case_eta_param ci (mk_predicate l u ctx ret) l' c brs s).
        * intros l l' e. cbn [canon]. unfold canon_predicate; cbn. now rewrite e.
      + eapply (BE_map Γ Γ (fun x => tCase ci (mk_predicate lx u ctx ret) x brs)); [| | |exact hvc].
        * intros a b s. exact (case_red_discr _ _ ci _ a b brs s).
        * intros a b s. exact (case_eta_discr ci _ a b brs s).
        * intros a b e. cbn [canon]. now rewrite e.
    - eapply rt_trans.
      + eapply (BE_list Γ Γ (fun l => tCase ci (mk_predicate l u' ctx' ret) c' brs')); [| | |exact hly].
        * intros l l' s. exact (case_red_param _ _ ci (mk_predicate l u' ctx' ret) l' c' brs' s).
        * intros l l' s. exact (case_eta_param ci (mk_predicate l u' ctx' ret) l' c' brs' s).
        * intros l l' e. cbn [canon]. unfold canon_predicate; cbn. now rewrite e.
      + eapply (BE_map Γ Γ (fun x => tCase ci (mk_predicate ly u' ctx' ret) x brs')); [| | |exact hvc'].
        * intros a b s. exact (case_red_discr _ _ ci _ a b brs' s).
        * intros a b s. exact (case_eta_discr ci _ a b brs' s).
        * intros a b e. cbn [canon]. now rewrite e.
    - cbn [canon]. constructor.
      + unfold eq_predicate, canon_predicate; cbn. split; [|split; [|split]].
        * apply All2_map. exact hxy.
        * exact hu.
        * rewrite (canon_ctx_eq _ _ hctx). apply eq_context_upto_names_refl'.
        * apply RF_refl.
      + exact (RF_canon _ _ _ _ ec).
      + unfold eq_branches, eq_branch. apply All2_map. eapply All2_impl; [exact hbrs|].
        intros b b' [hcx hb]. unfold canon_branch; cbn. split.
        * rewrite (canon_ctx_eq _ _ hcx). apply eq_context_upto_names_refl'.
        * rewrite hb. apply RF_refl.
  Qed.

  (** The middle branches of the split: left contexts, right bodies. *)
  Lemma case_mid_branches Γ (p : predicate term) (n : nat) (P : nat -> bool) brs brs' :
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
            J (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br')) brs brs' ->
    All (fun br => test_context_k (fun k => on_free_vars (closedP k xpredT)) n (bcontext br)) brs ->
    All (fun br => on_free_vars (shiftnP #|bcontext br| P) (bbody br)) brs' ->
    ∑ brs1, All2 (fun br b1 => (bcontext br = bcontext b1) ×
                   J (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody b1)) brs brs1 ×
            All2 (fun b1 br' => eq_context_upto_names (bcontext b1) (bcontext br') ×
                   (bbody b1 = bbody br')) brs1 brs' ×
            All (fun b1 => test_context_k (fun k => on_free_vars (closedP k xpredT)) n (bcontext b1) &&
                           on_free_vars (shiftnP #|bcontext b1| P) (bbody b1)) brs1.
  Proof.
    induction 1 as [|br br' l l' [hc hj] _ IH]; intros hl hr.
    - exists []. repeat split; constructor.
    - inversion hl as [|? ? hl0 hl1]; subst. inversion hr as [|? ? hr0 hr1]; subst.
      destruct (IH hl1 hr1) as (l1 & h1 & h2 & h3).
      exists ({| bcontext := bcontext br; bbody := bbody br' |} :: l1).
      split; [|split].
      + constructor; [split; [reflexivity|exact hj]|exact h1].
      + constructor; [split; [exact hc|reflexivity]|exact h2].
      + constructor; [|exact h3]. cbn. rewrite hl0 /=. rewrite (All2_length hc). exact hr0.
  Qed.

  (** **The Case congruence.** *)
  Lemma JoinE_Case Γ pb ci p p' c c' brs brs' :
    is_closed_context Γ ->
    is_open_term Γ (tCase ci p c brs) -> is_open_term Γ (tCase ci p' c' brs') ->
    All2 (J Γ Conv) (pparams p) (pparams p') ->
    cmp_universe_instance (cu Conv) (puinst p) (puinst p') ->
    eq_context_upto_names (pcontext p) (pcontext p') ->
    J (Γ ,,, inst_case_predicate_context p) Conv (preturn p) (preturn p') ->
    J Γ Conv c c' ->
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
            J (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br')) brs brs' ->
    J Γ pb (tCase ci p c brs) (tCase ci p' c' brs').
  Proof.
    destruct p as [pars u ctx ret], p' as [pars' u' ctx' ret'].
    intros hΓ hl hr hpars hu hctx hret hc hbrs.
    move: hl hr. cbn [on_free_vars pparams pcontext preturn puinst].
    move/and5P => [hpl hrl hcl hcc hbl]. move/and5P => [_ hrr _ _ hbr].
    destruct (case_mid_branches Γ (mk_predicate pars u ctx ret) #|pars| (shiftnP #|Γ| xpred0) brs brs' hbrs)
      as (brs1 & h1 & h2 & hs).
    { eapply All_impl; [exact (forallb_All _ _ hbl)|]. intros br h. exact (proj1 (andP h)). }
    { eapply All_impl; [exact (forallb_All _ _ hbr)|]. intros br h. exact (proj2 (andP h)). }
    apply (I5_join_trans Σ wfΣ r Γ pb _ (tCase ci (mk_predicate pars u ctx ret') c brs1) _ hΓ).
    - cbn [on_free_vars pparams pcontext preturn puinst].
      apply/and5P; split; [exact hpl| |exact hcl|exact hcc|exact (All_forallb _ _ hs)].
      rewrite (All2_length hctx). exact hrr.
    - exact (JoinE_Case_bodies Γ pb ci pars u ctx ret ret' c brs brs1 hret h1).
    - exact (JoinE_Case_heads Γ pb ci pars u ctx pars' u' ctx' ret' c c' brs1 brs' hpars hu hctx hc h2).
  Qed.

  (** ** Contexts that differ only in assumption types, or in let-bodies up to
      [canon], carry the same chains (C1a re-pinned, [red1_upto_domain_r_bodies]). *)
  Lemma BE_ctx Γ Γ' x y : upto_domain_r_bodies Γ Γ' -> BE Γ x y -> BE Γ' x y.
  Proof.
    intros hc h. induction h as [x y [[s|s]|s]|x|x y z _ IH1 _ IH2].
    - destruct (red1_upto_domain_r_bodies s Γ' x hc (upto_domain_r_refl x)) as (y' & hy' & ey).
      eapply rt_trans; cycle 1.
      + apply rt_step; right. symmetry. exact (canon_eq_of_upto_domain_r _ _ ey).
      + destruct hy' as [? h|]; [apply rt_step; left; left; exact h|apply rt_refl].
    - apply rt_step; left; right; exact s.
    - apply rt_step; right; exact s.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  Qed.

  Lemma bodies_vass Γ na na' A A' : upto_domain_r_bodies (Γ ,, vass na A) (Γ ,, vass na' A').
  Proof. apply upto_domain_r_bodies_vass, upto_domain_r_bodies_refl. Qed.

  Lemma All2_JoinE_ex Γ l l' : All2 (J Γ Conv) l l' ->
    ∑ lx ly, All2 (fun a x => BE Γ a x) l lx × All2 (fun b y => BE Γ b y) l' ly ×
             All2 (fun x y => RF Conv 0 (canon x) (canon y)) lx ly.
  Proof.
    intros h. apply All2_ex3. eapply All2_impl; [exact h|]. intros a b hj.
    destruct (JoinE_BE _ _ _ _ hj) as (x & y & hx & hy & e). exists x, y. exact (hx, (hy, RF_canon _ _ _ _ e)).
  Qed.

  (** ** The remaining congruences *)

  Lemma JoinE_sym Γ pb t u : J Γ Conv u t -> J Γ pb t u.
  Proof.
    intros (v & v' & hv & hv' & e). exists v', v. repeat split; [exact hv'|exact hv|].
    exact (finst_term_Conv_pb r Σ.1 cu cs Conv 0 v' v (compare_term_eta_sym r Σ.1 Σ 0 v v' e) eq_refl
             pb 0 (a3_sub_u Σ pb) (a3_sub_s Σ pb)).
  Qed.

  Lemma JoinE_Evar Γ pb ev l l' : All2 (J Γ Conv) l l' -> J Γ pb (tEvar ev l) (tEvar ev l').
  Proof.
    intros h. destruct (All2_JoinE_ex Γ l l' h) as (lx & ly & hlx & hly & hxy).
    apply (BE_JoinE Γ pb _ _ (tEvar ev lx) (tEvar ev ly)).
    - eapply (BE_list Γ Γ (tEvar ev)); [| | |exact hlx].
      + intros a b s. exact (evar_red _ _ ev a b s).
      + intros a b s. exact (evar_eta ev a b s).
      + intros a b e. cbn [canon]. now rewrite e.
    - eapply (BE_list Γ Γ (tEvar ev)); [| | |exact hly].
      + intros a b s. exact (evar_red _ _ ev a b s).
      + intros a b s. exact (evar_eta ev a b s).
      + intros a b e. cbn [canon]. now rewrite e.
    - cbn [canon]. constructor. apply All2_map. exact hxy.
  Qed.

  Lemma JoinE_App Γ pb t t' u u' : J Γ pb t t' -> J Γ Conv u u' -> J Γ pb (tApp t u) (tApp t' u').
  Proof.
    intros ht hu.
    destruct (JoinE_BE _ _ _ _ ht) as (vt & vt' & hvt & hvt' & et).
    destruct (JoinE_BE _ _ _ _ hu) as (vu & vu' & hvu & hvu' & eu).
    apply (BE_JoinE Γ pb _ _ (tApp vt vu) (tApp vt' vu')).
    - eapply rt_trans.
      + eapply (BE_map Γ Γ (fun x => tApp x u)); [| | |exact hvt].
        * intros a b s; exact (app_red_l _ _ a b u s).
        * intros a b s; exact (app_eta_l a b u s).
        * intros a b e; cbn [canon]; now rewrite e.
      + eapply (BE_map Γ Γ (tApp vt)); [| | |exact hvu].
        * intros a b s; exact (app_red_r _ _ a b vt s).
        * intros a b s; exact (app_eta_r a b vt s).
        * intros a b e; cbn [canon]; now rewrite e.
    - eapply rt_trans.
      + eapply (BE_map Γ Γ (fun x => tApp x u')); [| | |exact hvt'].
        * intros a b s; exact (app_red_l _ _ a b u' s).
        * intros a b s; exact (app_eta_l a b u' s).
        * intros a b e; cbn [canon]; now rewrite e.
      + eapply (BE_map Γ Γ (tApp vt')); [| | |exact hvu'].
        * intros a b s; exact (app_red_r _ _ a b vt' s).
        * intros a b s; exact (app_eta_r a b vt' s).
        * intros a b e; cbn [canon]; now rewrite e.
    - cbn [canon]. constructor.
      + apply (finst_napp_mono r Σ.1 cu cs pb 0 1); [exact (a3_sub_u Σ pb)|exact (RF_canon _ _ _ _ et)|lia].
      + exact (RF_canon _ _ _ _ eu).
  Qed.

  (** The λ domain is erased by [canon], so only the body is joined; the right
      body's chain moves from [vass na ty] to [vass na' ty'] ([BE_ctx]). *)
  Lemma JoinE_Lambda Γ pb na na' ty ty' t t' :
    J (Γ ,, vass na ty) Conv t t' -> J Γ pb (tLambda na ty t) (tLambda na' ty' t').
  Proof.
    intros h. destruct (JoinE_BE _ _ _ _ h) as (v & v' & hv & hv' & e).
    apply (BE_JoinE Γ pb _ _ (tLambda na ty v) (tLambda na' ty' v')).
    - eapply (BE_map (Γ ,, vass na ty) Γ (tLambda na ty)); [| | |exact hv].
      + intros a b s; exact (abs_red_r _ _ na a b ty s).
      + intros a b s; exact (abs_eta_r na a b ty s).
      + intros a b ec; cbn [canon]; now rewrite ec.
    - eapply (BE_map (Γ ,, vass na' ty') Γ (tLambda na' ty'));
        [| | |exact (BE_ctx _ _ _ _ (bodies_vass Γ na na' ty ty') hv')].
      + intros a b s; exact (abs_red_r _ _ na' a b ty' s).
      + intros a b s; exact (abs_eta_r na' a b ty' s).
      + intros a b ec; cbn [canon]; now rewrite ec.
    - cbn [canon]. constructor; [apply eq_binder_annot_refl'|apply RF_refl|exact (RF_canon _ _ _ _ e)].
  Qed.

  Lemma JoinE_Prod Γ pb na na' a a' b b' :
    eq_binder_annot na na' -> J Γ Conv a a' -> J (Γ ,, vass na a) pb b b' ->
    J Γ pb (tProd na a b) (tProd na' a' b').
  Proof.
    intros hna ha hb.
    destruct (JoinE_BE _ _ _ _ ha) as (va & va' & hva & hva' & ea).
    destruct (JoinE_BE _ _ _ _ hb) as (vb & vb' & hvb & hvb' & eb).
    apply (BE_JoinE Γ pb _ _ (tProd na va vb) (tProd na' va' vb')).
    - eapply rt_trans.
      + eapply (BE_map (Γ ,, vass na a) Γ (tProd na a)); [| | |exact hvb].
        * intros x y s; exact (prod_red_r _ _ na x y a s).
        * intros x y s; exact (prod_eta_r na x y a s).
        * intros x y e; cbn [canon]; now rewrite e.
      + eapply (BE_map Γ Γ (fun x => tProd na x vb)); [| | |exact hva].
        * intros x y s; exact (prod_red_l _ _ na x vb y s).
        * intros x y s; exact (prod_eta_l na x vb y s).
        * intros x y e; cbn [canon]; now rewrite e.
    - eapply rt_trans.
      + eapply (BE_map (Γ ,, vass na' a') Γ (tProd na' a'));
          [| | |exact (BE_ctx _ _ _ _ (bodies_vass Γ na na' a a') hvb')].
        * intros x y s; exact (prod_red_r _ _ na' x y a' s).
        * intros x y s; exact (prod_eta_r na' x y a' s).
        * intros x y e; cbn [canon]; now rewrite e.
      + eapply (BE_map Γ Γ (fun x => tProd na' x vb')); [| | |exact hva'].
        * intros x y s; exact (prod_red_l _ _ na' x vb' y s).
        * intros x y s; exact (prod_eta_l na' x vb' y s).
        * intros x y e; cbn [canon]; now rewrite e.
    - cbn [canon]. constructor; [exact hna|exact (RF_canon _ _ _ _ ea)|exact (RF_canon _ _ _ _ eb)].
  Qed.

  (** LetIn, split by A3 like Case: the body is joined in the left term's
      [vdef] context, then the definition and type with the body fixed. *)
  Lemma JoinE_LetIn_body Γ pb na t ty u u' :
    J (Γ ,, vdef na t ty) Conv u u' -> J Γ pb (tLetIn na t ty u) (tLetIn na t ty u').
  Proof.
    intros h. destruct (JoinE_BE _ _ _ _ h) as (v & v' & hv & hv' & e).
    apply (BE_JoinE Γ pb _ _ (tLetIn na t ty v) (tLetIn na t ty v')).
    - eapply (BE_map (Γ ,, vdef na t ty) Γ (tLetIn na t ty)); [| | |exact hv].
      + intros a b s; exact (letin_red_body _ _ na t ty a b s).
      + intros a b s; exact (letin_eta_body na t ty a b s).
      + intros a b ec; cbn [canon]; now rewrite ec.
    - eapply (BE_map (Γ ,, vdef na t ty) Γ (tLetIn na t ty)); [| | |exact hv'].
      + intros a b s; exact (letin_red_body _ _ na t ty a b s).
      + intros a b s; exact (letin_eta_body na t ty a b s).
      + intros a b ec; cbn [canon]; now rewrite ec.
    - cbn [canon]. constructor; [apply eq_binder_annot_refl'|apply RF_refl|apply RF_refl|exact (RF_canon _ _ _ _ e)].
  Qed.

  Lemma JoinE_LetIn_heads Γ pb na na' t t' ty ty' u :
    eq_binder_annot na na' -> J Γ Conv t t' -> J Γ Conv ty ty' ->
    J Γ pb (tLetIn na t ty u) (tLetIn na' t' ty' u).
  Proof.
    intros hna ht hty.
    destruct (JoinE_BE _ _ _ _ ht) as (vt & vt' & hvt & hvt' & et).
    destruct (JoinE_BE _ _ _ _ hty) as (vy & vy' & hvy & hvy' & ey).
    apply (BE_JoinE Γ pb _ _ (tLetIn na vt vy u) (tLetIn na' vt' vy' u)).
    - eapply rt_trans.
      + eapply (BE_map Γ Γ (fun x => tLetIn na x ty u)); [| | |exact hvt].
        * intros a b s; exact (letin_red_def _ _ na a ty u b s).
        * intros a b s; exact (letin_eta_def na a ty u b s).
        * intros a b ec; cbn [canon]; now rewrite ec.
      + eapply (BE_map Γ Γ (fun x => tLetIn na vt x u)); [| | |exact hvy].
        * intros a b s; exact (letin_red_ty _ _ na vt a u b s).
        * intros a b s; exact (letin_eta_ty na vt a u b s).
        * intros a b ec; cbn [canon]; now rewrite ec.
    - eapply rt_trans.
      + eapply (BE_map Γ Γ (fun x => tLetIn na' x ty' u)); [| | |exact hvt'].
        * intros a b s; exact (letin_red_def _ _ na' a ty' u b s).
        * intros a b s; exact (letin_eta_def na' a ty' u b s).
        * intros a b ec; cbn [canon]; now rewrite ec.
      + eapply (BE_map Γ Γ (fun x => tLetIn na' vt' x u)); [| | |exact hvy'].
        * intros a b s; exact (letin_red_ty _ _ na' vt' a u b s).
        * intros a b s; exact (letin_eta_ty na' vt' a u b s).
        * intros a b ec; cbn [canon]; now rewrite ec.
    - cbn [canon]. constructor; [exact hna|exact (RF_canon _ _ _ _ et)|exact (RF_canon _ _ _ _ ey)|apply RF_refl].
  Qed.

  Lemma JoinE_LetIn Γ pb na na' t t' ty ty' u u' :
    is_closed_context Γ -> is_open_term Γ (tLetIn na t ty u) -> is_open_term Γ (tLetIn na' t' ty' u') ->
    eq_binder_annot na na' -> J Γ Conv t t' -> J Γ Conv ty ty' -> J (Γ ,, vdef na t ty) Conv u u' ->
    J Γ pb (tLetIn na t ty u) (tLetIn na' t' ty' u').
  Proof.
    intros hΓ hl hr hna ht hty hu.
    apply (I5_join_trans Σ wfΣ r Γ pb _ (tLetIn na t ty u') _ hΓ).
    - move: hl hr. cbn [on_free_vars]. move/and3P => [h1 h2 _]. move/and3P => [_ _ h3].
      apply/and3P; split; assumption.
    - exact (JoinE_LetIn_body Γ pb na t ty u u' hu).
    - exact (JoinE_LetIn_heads Γ pb na na' t t' ty ty' u' hna ht hty).
  Qed.

  Lemma JoinE_Proj Γ pb p c c' : J Γ Conv c c' -> J Γ pb (tProj p c) (tProj p c').
  Proof.
    intros h. destruct (JoinE_BE _ _ _ _ h) as (v & v' & hv & hv' & e).
    apply (BE_JoinE Γ pb _ _ (tProj p v) (tProj p v')).
    - eapply (BE_map Γ Γ (tProj p)); [| | |exact hv].
      + intros a b s; exact (proj_red _ _ p a b s).
      + intros a b s; exact (proj_eta p a b s).
      + intros a b ec; cbn [canon]; now rewrite ec.
    - eapply (BE_map Γ Γ (tProj p)); [| | |exact hv'].
      + intros a b s; exact (proj_red _ _ p a b s).
      + intros a b s; exact (proj_eta p a b s).
      + intros a b ec; cbn [canon]; now rewrite ec.
    - cbn [canon]. constructor. exact (RF_canon _ _ _ _ e).
  Qed.

  Lemma JoinE_Sort Γ pb s s' : compare_sort Σ pb s s' -> J Γ pb (tSort s) (tSort s').
  Proof.
    intros h. apply (BE_JoinE Γ pb _ _ (tSort s) (tSort s')); [apply rt_refl|apply rt_refl|].
    cbn [canon]. constructor. exact h.
  Qed.

  Lemma JoinE_Const Γ pb c u u' : cmp_universe_instance (cu Conv) u u' -> J Γ pb (tConst c u) (tConst c u').
  Proof.
    intros h. apply (BE_JoinE Γ pb _ _ (tConst c u) (tConst c u')); [apply rt_refl|apply rt_refl|].
    cbn [canon]. constructor. exact h.
  Qed.

  Lemma RF_mkApps pb n f f' l l' :
    RF pb (n + #|l|) f f' -> All2 (RF Conv 0) l l' -> RF pb n (mkApps f l) (mkApps f' l').
  Proof.
    intros hf hl. induction hl as [|x y l l' hxy _ IH] in n, f, f', hf |- *.
    - cbn in hf |- *. rewrite Nat.add_0_r in hf. exact hf.
    - cbn. apply IH. constructor; [|exact hxy]. rewrite -Nat.add_succ_r. exact hf.
  Qed.

  Lemma BE_mkApps_args Γ f l l' : All2 (fun x y => BE Γ x y) l l' -> BE Γ (mkApps f l) (mkApps f l').
  Proof.
    apply (BE_list Γ Γ (mkApps f)).
    - intros a b s. apply red1_mkApps_r. exact s.
    - intros a b s. exact (eta1_mkApps_args a b s f).
    - intros a b e. rewrite !canon_mkApps. now rewrite e.
  Qed.

  (** The spine heads: the spec's base instance comparison is F-inst
      ([cumul_ind_finst]; SITE K3 [cumul_construct_finst]). *)
  Lemma JoinE_Ind Γ pb i u u' args args' :
    cumul_Ind_univ Σ pb i #|args| u u' -> All2 (J Γ Conv) args args' ->
    J Γ pb (mkApps (tInd i u) args) (mkApps (tInd i u') args').
  Proof.
    intros hu h. destruct (All2_JoinE_ex Γ args args' h) as (lx & ly & hlx & hly & hxy).
    apply (BE_JoinE Γ pb _ _ (mkApps (tInd i u) lx) (mkApps (tInd i u') ly)).
    - exact (BE_mkApps_args Γ _ _ _ hlx).
    - exact (BE_mkApps_args Γ _ _ _ hly).
    - rewrite !canon_mkApps. cbn [canon]. apply RF_mkApps; [|apply All2_map; exact hxy].
      rewrite Nat.add_0_l length_map. constructor.
      rewrite -(All2_length hlx). exact (cumul_ind_finst r Σ.1 cu pb i #|args| u u' hu).
  Qed.

  Lemma JoinE_Construct Γ pb i k u u' args args' :
    cumul_Construct_univ Σ pb i k #|args| u u' -> All2 (J Γ Conv) args args' ->
    J Γ pb (mkApps (tConstruct i k u) args) (mkApps (tConstruct i k u') args').
  Proof.
    intros hu h. destruct (All2_JoinE_ex Γ args args' h) as (lx & ly & hlx & hly & hxy).
    apply (BE_JoinE Γ pb _ _ (mkApps (tConstruct i k u) lx) (mkApps (tConstruct i k u') ly)).
    - exact (BE_mkApps_args Γ _ _ _ hlx).
    - exact (BE_mkApps_args Γ _ _ _ hly).
    - rewrite !canon_mkApps. cbn [canon]. apply RF_mkApps; [|apply All2_map; exact hxy].
      rewrite Nat.add_0_l length_map. constructor.
      rewrite -(All2_length hlx). exact (cumul_construct_finst r Σ.1 cu pb i k #|args| u u' hu).
  Qed.

  Lemma JoinE_Prim Γ pb p p' : onPrims (J Γ Conv) (eq_universe Σ) p p' -> J Γ pb (tPrim p) (tPrim p').
  Proof.
    intros h. destruct h as [i|f|s|a a' hl hd ht hv].
    1-3: now apply JoinE_canon_eq.
    destruct (JoinE_BE _ _ _ _ hd) as (vd & vd' & hvd & hvd' & ed).
    destruct (JoinE_BE _ _ _ _ ht) as (vt & vt' & hvt & hvt' & et).
    destruct (All2_JoinE_ex Γ _ _ hv) as (lx & ly & hlx & hly & hxy).
    destruct a as [lvl ty def val], a' as [lvl' ty' def' val']; cbn in hl, hlx, hly, hvd, hvd', hvt, hvt'.
    apply (BE_JoinE Γ pb _ _
      (tPrim (primArray; primArrayModel {| array_level := lvl; array_value := lx; array_default := vd; array_type := vt |}))
      (tPrim (primArray; primArrayModel {| array_level := lvl'; array_value := ly; array_default := vd'; array_type := vt' |}))).
    - eapply rt_trans; [|eapply rt_trans].
      + eapply (BE_list Γ Γ (fun l => tPrim (primArray; primArrayModel
                  {| array_level := lvl; array_value := l; array_default := def; array_type := ty |})));
          [| | |exact hlx].
        * intros l l' s. exact (array_red_val _ _ {| array_level := lvl; array_value := l; array_default := def; array_type := ty |} l' s).
        * intros l l' s. exact (array_eta_val {| array_level := lvl; array_value := l; array_default := def; array_type := ty |} l' s).
        * intros l l' ec. rewrite !canon_array. now rewrite ec.
      + eapply (BE_map Γ Γ (fun x => tPrim (primArray; primArrayModel
                  {| array_level := lvl; array_value := lx; array_default := x; array_type := ty |})));
          [| | |exact hvd].
        * intros a b s. exact (array_red_def _ _ {| array_level := lvl; array_value := lx; array_default := a; array_type := ty |} b s).
        * intros a b s. exact (array_eta_def {| array_level := lvl; array_value := lx; array_default := a; array_type := ty |} b s).
        * intros a b ec. rewrite !canon_array. now rewrite ec.
      + eapply (BE_map Γ Γ (fun x => tPrim (primArray; primArrayModel
                  {| array_level := lvl; array_value := lx; array_default := vd; array_type := x |})));
          [| | |exact hvt].
        * intros a b s. exact (array_red_type _ _ {| array_level := lvl; array_value := lx; array_default := vd; array_type := a |} b s).
        * intros a b s. exact (array_eta_type {| array_level := lvl; array_value := lx; array_default := vd; array_type := a |} b s).
        * intros a b ec. rewrite !canon_array. now rewrite ec.
    - eapply rt_trans; [|eapply rt_trans].
      + eapply (BE_list Γ Γ (fun l => tPrim (primArray; primArrayModel
                  {| array_level := lvl'; array_value := l; array_default := def'; array_type := ty' |})));
          [| | |exact hly].
        * intros l l' s. exact (array_red_val _ _ {| array_level := lvl'; array_value := l; array_default := def'; array_type := ty' |} l' s).
        * intros l l' s. exact (array_eta_val {| array_level := lvl'; array_value := l; array_default := def'; array_type := ty' |} l' s).
        * intros l l' ec. rewrite !canon_array. now rewrite ec.
      + eapply (BE_map Γ Γ (fun x => tPrim (primArray; primArrayModel
                  {| array_level := lvl'; array_value := ly; array_default := x; array_type := ty' |})));
          [| | |exact hvd'].
        * intros a b s. exact (array_red_def _ _ {| array_level := lvl'; array_value := ly; array_default := a; array_type := ty' |} b s).
        * intros a b s. exact (array_eta_def {| array_level := lvl'; array_value := ly; array_default := a; array_type := ty' |} b s).
        * intros a b ec. rewrite !canon_array. now rewrite ec.
      + eapply (BE_map Γ Γ (fun x => tPrim (primArray; primArrayModel
                  {| array_level := lvl'; array_value := ly; array_default := vd'; array_type := x |})));
          [| | |exact hvt'].
        * intros a b s. exact (array_red_type _ _ {| array_level := lvl'; array_value := ly; array_default := vd'; array_type := a |} b s).
        * intros a b s. exact (array_eta_type {| array_level := lvl'; array_value := ly; array_default := vd'; array_type := a |} b s).
        * intros a b ec. rewrite !canon_array. now rewrite ec.
    - rewrite !canon_array. constructor. constructor; cbn.
      + exact hl.
      + exact (RF_canon _ _ _ _ ed).
      + exact (RF_canon _ _ _ _ et).
      + apply All2_map. exact hxy.
  Qed.

  (** Fixpoints: the bodies first (in the left [fix_context]; the right body's
      chain moves from [fix_context mfix] to [fix_context mfix'], both made of
      assumptions), then the types. *)
  Lemma BE_fix_ty Γ (mk : mfixpoint term -> term) mfix mfix1 :
    (forall m m1, OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) m m1 ->
                  red1 Σ Γ (mk m) (mk m1)) ->
    (forall m m1, OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) m m1 -> eta1 (mk m) (mk m1)) ->
    (forall m m1, map (canon_def canon) m = map (canon_def canon) m1 -> canon (mk m) = canon (mk m1)) ->
    All2 (fun d d1 => ((dname d, dbody d, rarg d) = (dname d1, dbody d1, rarg d1)) × BE Γ (dtype d) (dtype d1))
      mfix mfix1 ->
    BE Γ (mk mfix) (mk mfix1).
  Proof.
    intros hr he hc h.
    enough (H : forall pre, BE Γ (mk (pre ++ mfix)) (mk (pre ++ mfix1))) by exact (H []).
    induction h as [|d d1 l l' [e hb] _ IH]; intros pre; [apply rt_refl|].
    destruct d as [na ty bo ra], d1 as [na1 ty1 bo1 ra1]; cbn in e, hb.
    injection e as e1 e2 e3; subst na1 bo1 ra1.
    eapply rt_trans.
    - eapply (BE_map Γ Γ (fun y => mk (pre ++ {| dname := na; dtype := y; dbody := bo; rarg := ra |} :: l)));
        [| | |exact hb].
      + intros a b s. apply hr. apply OnOne2_app. constructor. split; [exact s|reflexivity].
      + intros a b s. apply he. apply OnOne2_app. constructor. split; [exact s|reflexivity].
      + intros a b ec. apply hc. rewrite !map_app. cbn [map]. unfold canon_def; cbn. now rewrite ec.
    - specialize (IH (pre ++ [{| dname := na; dtype := ty1; dbody := bo; rarg := ra |}])).
      rewrite <- !app_assoc in IH. exact IH.
  Qed.

  Lemma BE_fix_body Γ Δ (mk : mfixpoint term -> term) mfix mfix1 :
    (forall m m1, OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context m)) dbody (fun x => (dname x, dtype x, rarg x))) m m1 ->
                  red1 Σ Γ (mk m) (mk m1)) ->
    (forall m m1, OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) m m1 -> eta1 (mk m) (mk m1)) ->
    (forall m m1, map (canon_def canon) m = map (canon_def canon) m1 -> canon (mk m) = canon (mk m1)) ->
    fix_context mfix = Δ ->
    All2 (fun d d1 => ((dname d, dtype d, rarg d) = (dname d1, dtype d1, rarg d1)) × BE (Γ ,,, Δ) (dbody d) (dbody d1))
      mfix mfix1 ->
    BE Γ (mk mfix) (mk mfix1).
  Proof.
    intros hr he hc hΔ h.
    enough (H : forall pre, fix_context (pre ++ mfix) = Δ -> BE Γ (mk (pre ++ mfix)) (mk (pre ++ mfix1)))
      by exact (H [] hΔ).
    clear hΔ. induction h as [|d d1 l l' [e hb] _ IH]; intros pre hpre; [apply rt_refl|].
    destruct d as [na ty bo ra], d1 as [na1 ty1 bo1 ra1]; cbn in e, hb.
    injection e as e1 e2 e3; subst na1 ty1 ra1.
    have hfc : forall y, fix_context (pre ++ {| dname := na; dtype := ty; dbody := y; rarg := ra |} :: l) = Δ.
    { intros y. rewrite -hpre. apply fix_context_nt. rewrite !map_app. reflexivity. }
    eapply rt_trans.
    - eapply (BE_map (Γ ,,, Δ) Γ (fun y => mk (pre ++ {| dname := na; dtype := ty; dbody := y; rarg := ra |} :: l)));
        [| | |exact hb].
      + intros a b s. apply hr. apply OnOne2_app. constructor. split; [|reflexivity].
        cbn [dbody]. rewrite (hfc a). exact s.
      + intros a b s. apply he. apply OnOne2_app. constructor. split; [exact s|reflexivity].
      + intros a b ec. apply hc. rewrite !map_app. cbn [map]. unfold canon_def; cbn. now rewrite ec.
    - specialize (IH (pre ++ [{| dname := na; dtype := ty; dbody := bo1; rarg := ra |}])).
      rewrite <- !app_assoc in IH. apply IH.
      rewrite -hpre. apply fix_context_nt. rewrite !map_app. reflexivity.
  Qed.

  (** One proof for [tFix] and [tCoFix], over the node-forming function [mk]
      and its congruence constructors. *)
  Lemma JoinE_mfix (mk : mfixpoint term -> term)
            (mk_canon : forall m, canon (mk m) = mk (map (canon_def canon) m))
            (mk_red_ty : forall Γ m m1, OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x => (dname x, dbody x, rarg x))) m m1 ->
                          red1 Σ Γ (mk m) (mk m1))
            (mk_red_body : forall Γ m m1,
                OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context m)) dbody (fun x => (dname x, dtype x, rarg x))) m m1 ->
                red1 Σ Γ (mk m) (mk m1))
            (mk_eta_ty : forall m m1, OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) m m1 ->
                          eta1 (mk m) (mk m1))
            (mk_eta_body : forall m m1, OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) m m1 ->
                          eta1 (mk m) (mk m1))
            (mk_RF : forall pb m m1, eq_mfixpoint (RF Conv 0) m m1 -> RF pb 0 (mk m) (mk m1))
            Γ pb mfix mfix' :
      All2 (fun d d' => J Γ Conv (dtype d) (dtype d') × J (Γ ,,, fix_context mfix) Conv (dbody d) (dbody d') ×
                        (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) mfix mfix' ->
      J Γ pb (mk mfix) (mk mfix').
    Proof.
      intros h.
      have hctx : upto_domain_r_bodies (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix').
      { apply upto_domain_r_bodies_app; [exact (upto_domain_r_bodies_fix_context _ _ h)|apply upto_domain_r_bodies_refl]. }
      assert (hw : All2 (fun d d' => ∑ e e',
         (BE (Γ ,,, fix_context mfix) (dbody d) (dbody e) × BE Γ (dtype d) (dtype e) ×
          (dname e = dname d) × (rarg e = rarg d)) ×
         (BE (Γ ,,, fix_context mfix') (dbody d') (dbody e') × BE Γ (dtype d') (dtype e') ×
          (dname e' = dname d') × (rarg e' = rarg d')) ×
         (RF Conv 0 (canon (dtype e)) (canon (dtype e')) × RF Conv 0 (canon (dbody e)) (canon (dbody e')) ×
          (rarg e = rarg e') × eq_binder_annot (dname e) (dname e'))) mfix mfix').
      { eapply All2_impl; [exact h|]. intros d d' (ht & hb & hra & hn).
        destruct (JoinE_BE _ _ _ _ ht) as (vt & vt' & hvt & hvt' & et).
        destruct (JoinE_BE _ _ _ _ hb) as (vb & vb' & hvb & hvb' & eb).
        exists {| dname := dname d; dtype := vt; dbody := vb; rarg := rarg d |},
               {| dname := dname d'; dtype := vt'; dbody := vb'; rarg := rarg d' |}; cbn.
        exact ((hvb, (hvt, (eq_refl, eq_refl))), ((BE_ctx _ _ _ _ hctx hvb', (hvt', (eq_refl, eq_refl))),
                (RF_canon _ _ _ _ et, (RF_canon _ _ _ _ eb, (hra, hn))))). }
      destruct (All2_ex3 _ _ _ _ _ hw) as (le & le' & hl & hr & hlr).
      destruct (All2_mid
        (fun d m => ((dname d, dtype d, rarg d) = (dname m, dtype m, rarg m)) ×
                    BE (Γ ,,, fix_context mfix) (dbody d) (dbody m))
        (fun m e => ((dname m, dbody m, rarg m) = (dname e, dbody e, rarg e)) × BE Γ (dtype m) (dtype e))
        _ (fun d e => {| dname := dname d; dtype := dtype d; dbody := dbody e; rarg := rarg d |}) mfix le hl)
        as (lm & hm1 & hm2).
      { intros d e (hb & ht & hn & hra). cbn. split; [split; [reflexivity|exact hb]|split; [|exact ht]].
        now rewrite hn hra. }
      destruct (All2_mid
        (fun d m => ((dname d, dtype d, rarg d) = (dname m, dtype m, rarg m)) ×
                    BE (Γ ,,, fix_context mfix') (dbody d) (dbody m))
        (fun m e => ((dname m, dbody m, rarg m) = (dname e, dbody e, rarg e)) × BE Γ (dtype m) (dtype e))
        _ (fun d e => {| dname := dname d; dtype := dtype d; dbody := dbody e; rarg := rarg d |}) mfix' le' hr)
        as (lm' & hm1' & hm2').
      { intros d e (hb & ht & hn & hra). cbn. split; [split; [reflexivity|exact hb]|split; [|exact ht]].
        now rewrite hn hra. }
      apply (BE_JoinE Γ pb _ _ (mk le) (mk le')).
      - eapply rt_trans.
        + eapply (BE_fix_body Γ (fix_context mfix) mk); [exact (mk_red_body Γ)|exact mk_eta_body| |reflexivity|exact hm1].
          intros m m1 e. now rewrite !mk_canon e.
        + eapply (BE_fix_ty Γ mk); [exact (mk_red_ty Γ)|exact mk_eta_ty| |exact hm2].
          intros m m1 e. now rewrite !mk_canon e.
      - eapply rt_trans.
        + eapply (BE_fix_body Γ (fix_context mfix') mk); [exact (mk_red_body Γ)|exact mk_eta_body| |reflexivity|exact hm1'].
          intros m m1 e. now rewrite !mk_canon e.
        + eapply (BE_fix_ty Γ mk); [exact (mk_red_ty Γ)|exact mk_eta_ty| |exact hm2'].
          intros m m1 e. now rewrite !mk_canon e.
      - rewrite !mk_canon. apply mk_RF. unfold eq_mfixpoint. apply All2_map.
        eapply All2_impl; [exact hlr|]. intros e e' (h1 & h2 & h3 & h4). unfold canon_def; cbn.
        exact (h1, (h2, (h3, h4))).
    Qed.

  Lemma JoinE_Fix Γ pb mfix mfix' idx :
    All2 (fun d d' => J Γ Conv (dtype d) (dtype d') × J (Γ ,,, fix_context mfix) Conv (dbody d) (dbody d') ×
                      (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) mfix mfix' ->
    J Γ pb (tFix mfix idx) (tFix mfix' idx).
  Proof.
    apply (JoinE_mfix (fun m => tFix m idx)).
    - intros m. reflexivity.
    - intros Γ' m m1 s. exact (fix_red_ty _ _ m m1 idx s).
    - intros Γ' m m1 s. exact (fix_red_body _ _ m m1 idx s).
    - intros m m1 s. exact (fix_eta_ty m m1 idx s).
    - intros m m1 s. exact (fix_eta_body m m1 idx s).
    - intros pb' m m1 e. constructor. exact e.
  Qed.

  Lemma JoinE_CoFix Γ pb mfix mfix' idx :
    All2 (fun d d' => J Γ Conv (dtype d) (dtype d') × J (Γ ,,, fix_context mfix) Conv (dbody d) (dbody d') ×
                      (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) mfix mfix' ->
    J Γ pb (tCoFix mfix idx) (tCoFix mfix' idx).
  Proof.
    apply (JoinE_mfix (fun m => tCoFix m idx)).
    - intros m. reflexivity.
    - intros Γ' m m1 s. exact (cofix_red_ty _ _ m m1 idx s).
    - intros Γ' m m1 s. exact (cofix_red_body _ _ m m1 idx s).
    - intros m m1 s. exact (cofix_eta_ty m m1 idx s).
    - intros m m1 s. exact (cofix_eta_body m m1 idx s).
    - intros pb' m m1 e. constructor. exact e.
  Qed.

  (** ** Scoping of the induction hypotheses *)

  Lemma All2_dep_J Γ (hΓ : is_closed_context Γ) l l' (H : All2 (cumulSpecE0 Σ Γ Conv) l l') :
    All2_dep (fun t u _ => is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u -> J Γ Conv t u) H ->
    forallb (is_open_term Γ) l -> forallb (is_open_term Γ) l' -> All2 (J Γ Conv) l l'.
  Proof.
    induction 1 as [|x y l l' h hs IH' _ IH]; cbn; [constructor|].
    move/andP => [hx hl]. move/andP => [hy hl']. constructor; [exact (IH' hΓ hx hy)|exact (IH hl hl')].
  Qed.

  Lemma All2_dep_brs Γ p brs brs' n' (hΓ : is_closed_context Γ)
    (Hb : cumul_branches (fun Γ => cumulSpecE0 Σ Γ Conv) Γ p brs brs') :
    forallb (is_open_term Γ) (pparams p) ->
    All2_dep (fun br br' Hc => is_closed_context (Γ ,,, inst_case_branch_context p br) ->
                is_open_term (Γ ,,, inst_case_branch_context p br) (bbody br) ->
                is_open_term (Γ ,,, inst_case_branch_context p br) (bbody br') ->
                J (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br')) Hb ->
    forallb (fun br => test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams p| (bcontext br) &&
             on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br)) brs ->
    forallb (fun br => test_context_k (fun k => on_free_vars (closedP k xpredT)) n' (bcontext br) &&
             on_free_vars (shiftnP #|bcontext br| (shiftnP #|Γ| xpred0)) (bbody br)) brs' ->
    All2 (fun br br' => eq_context_upto_names (bcontext br) (bcontext br') ×
            J (Γ ,,, inst_case_branch_context p br) Conv (bbody br) (bbody br')) brs brs'.
  Proof.
    intros hpl hdep. induction hdep as [|br br' l l' hr hs IH' _ IH]; cbn; [constructor|].
    destruct hr as [hc hcu].
    move/andP => [/andP [hcx hbx] hl]. move/andP => [/andP [_ hby] hl'].
    constructor; [split; [exact hc|]|exact (IH hl hl')].
    apply IH'.
    - rewrite /inst_case_branch_context.
      apply PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context; [exact hpl| |exact hΓ].
      rewrite -test_context_k_closed_on_free_vars_ctx. exact hcx.
    - apply open_app. rewrite inst_case_branch_context_length. exact hbx.
    - apply open_app. rewrite inst_case_branch_context_length (All2_length hc). exact hby.
  Qed.

  Lemma All2_dep_mfix Γ Δ n (mfix mfix' : mfixpoint term)
    (H : All2 (fun x y => cumulSpecE0 Σ Γ Conv (dtype x) (dtype y) *
            ((cumulSpecE0 Σ (Γ ,,, Δ) Conv (dbody x) (dbody y)) × (rarg x = rarg y) ×
             eq_binder_annot (dname x) (dname y))) mfix mfix') :
    is_closed_context Γ -> is_closed_context (Γ ,,, Δ) -> #|Δ| = n ->
    All2_dep (fun x y H =>
      (is_closed_context Γ -> is_open_term Γ (dtype x) -> is_open_term Γ (dtype y) -> J Γ Conv (dtype x) (dtype y)) ×
      (is_closed_context (Γ ,,, Δ) -> is_open_term (Γ ,,, Δ) (dbody x) -> is_open_term (Γ ,,, Δ) (dbody y) ->
       J (Γ ,,, Δ) Conv (dbody x) (dbody y))) H ->
    All (test_def (is_open_term Γ) (on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)))) mfix ->
    All (test_def (is_open_term Γ) (on_free_vars (shiftnP n (shiftnP #|Γ| xpred0)))) mfix' ->
    All2 (fun d d' => J Γ Conv (dtype d) (dtype d') × J (Γ ,,, Δ) Conv (dbody d) (dbody d') ×
                      (rarg d = rarg d') × eq_binder_annot (dname d) (dname d')) mfix mfix'.
  Proof.
    intros hΓ hΔ hn hdep. induction hdep as [|x y l l' h hs [IHt IHb] _ IH]; intros hl hr; [constructor|].
    inversion hl as [|? ? hx hl1]; subst. inversion hr as [|? ? hy hr1]; subst.
    destruct h as (ht & hb & hra & hna).
    move: hx; rewrite /test_def => /andP [htx hbx]. move: hy; rewrite /test_def => /andP [hty hby].
    constructor; [|exact (IH hl1 hr1)].
    refine (IHt hΓ htx hty, (IHb hΔ _ _, (hra, hna))).
    - apply open_app. first [exact hbx|rewrite hn; exact hbx].
    - apply open_app. first [exact hby|rewrite hn; exact hby].
  Qed.

  Lemma open_mfix_ctx Γ mfix :
    is_closed_context Γ -> is_open_term Γ (tFix mfix 0) -> is_closed_context (Γ ,,, fix_context mfix).
  Proof.
    intros hΓ h. rewrite on_free_vars_ctx_app hΓ /=. apply on_free_vars_fix_context.
    exact (forallb_All _ _ h).
  Qed.

  (** **A2: spec ⇒ join**, for every rule, with [cumul_eta_l] as the named
      premise [I5_eta_l_case] (obligation 9). *)
  Theorem I5_spec_to_join (heta : I5_eta_l_case r Σ) Γ pb t u :
    is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u ->
    Σ ;;; Γ ⊢ t ≤sE[pb] u -> J Γ pb t u.
  Proof.
    intros hΓ ht hu h. revert Γ pb t u h hΓ ht hu.
    apply (cumulSpecE0_rect cf Σ (fun _ _ Γ pb t u _ =>
      is_closed_context Γ -> is_open_term Γ t -> is_open_term Γ u -> J Γ pb t u)).
    - (* beta *) intros Γ pb na t b a _ _ _. apply JoinE_red1. apply red_beta.
    - (* zeta *) intros Γ pb na b t b' _ _ _. apply JoinE_red1. apply red_zeta.
    - (* rel *) intros Γ pb i body pf _ _ _. apply JoinE_red1. exact (red_rel _ _ i body pf).
    - (* iota *) intros Γ pb ci c u args p brs br hbr hn _ _ _. apply JoinE_red1. exact (red_iota _ _ ci c u args p brs br hbr hn).
    - (* fix *) intros Γ pb mfix idx args narg fn hf hc _ _ _. apply JoinE_red1. exact (red_fix _ _ mfix idx args narg fn hf hc).
    - (* cofix case *) intros Γ pb ci p mfix idx args narg fn brs hf _ _ _. apply JoinE_red1.
      exact (red_cofix_case _ _ ci p mfix idx args narg fn brs hf).
    - (* cofix proj *) intros Γ pb p mfix idx args narg fn hf _ _ _. apply JoinE_red1.
      exact (red_cofix_proj _ _ p mfix idx args narg fn hf).
    - (* delta *) intros Γ pb c decl body hd u hb _ _ _. apply JoinE_red1. exact (red_delta _ _ c decl body hd u hb).
    - (* prim_op: one [red_prim_op] step, so the join is that step *)
      intros Γ pb c decl u op ls r0 v hop hd hb hden hback _ _ _. apply JoinE_red1.
      exact (red_prim_op _ _ c decl u op ls r0 v hop hd hb hden hback).
    - (* proj *) intros Γ pb p args u arg ha _ _ _. apply JoinE_red1. exact (red_proj _ _ p args u arg ha).
    - (* Trans: A3 *) intros Γ pb t u v hΓ0 hu0 _ IH1 _ IH2 hΓ ht hv.
      exact (I5_join_trans Σ wfΣ r Γ pb t u v hΓ0 hu0 (IH1 hΓ ht hu0) (IH2 hΓ hu0 hv)).
    - (* Sym *) intros Γ pb t u _ IH hΓ ht hu. apply JoinE_sym. exact (IH hΓ hu ht).
    - (* Refl *) intros Γ pb t _ _ _. now apply JoinE_canon_eq.
    - (* Evar *) intros Γ pb ev l l' H IH hΓ hl hr. apply JoinE_Evar. exact (All2_dep_J Γ hΓ l l' H IH hl hr).
    - (* App *) intros Γ pb t t' u u' _ IH1 _ IH2 hΓ hl hr.
      move: hl hr. cbn [on_free_vars]. move/andP => [hl1 hl2]. move/andP => [hr1 hr2].
      exact (JoinE_App Γ pb t t' u u' (IH1 hΓ hl1 hr1) (IH2 hΓ hl2 hr2)).
    - (* Lambda *) intros Γ pb na na' ty ty' t t' hna _ _ _ IH hΓ hl hr.
      move: hl hr. cbn [on_free_vars]. move/andP => [hl1 hl2]. move/andP => [hr1 hr2].
      apply JoinE_Lambda. apply IH; [exact (closed_snoc_vass Γ na ty hΓ hl1)|exact (open_snoc Γ _ t hl2)|exact (open_snoc Γ _ t' hr2)].
    - (* Prod *) intros Γ pb na na' a a' b b' hna _ IHa _ IHb hΓ hl hr.
      move: hl hr. cbn [on_free_vars]. move/andP => [hl1 hl2]. move/andP => [hr1 hr2].
      apply JoinE_Prod; [exact hna|exact (IHa hΓ hl1 hr1)|].
      apply IHb; [exact (closed_snoc_vass Γ na a hΓ hl1)|exact (open_snoc Γ _ b hl2)|exact (open_snoc Γ _ b' hr2)].
    - (* LetIn *) intros Γ pb na na' t t' ty ty' u u' hna _ IHt _ IHty _ IHu hΓ hl hr.
      move: (hl) (hr). cbn [on_free_vars]. move/and3P => [hl1 hl2 hl3]. move/and3P => [hr1 hr2 hr3].
      apply JoinE_LetIn; [exact hΓ|exact hl|exact hr|exact hna|exact (IHt hΓ hl1 hr1)|exact (IHty hΓ hl2 hr2)|].
      apply IHu; [exact (closed_snoc_vdef Γ na t ty hΓ hl1 hl2)|exact (open_snoc Γ _ u hl3)|exact (open_snoc Γ _ u' hr3)].
    - (* Case *) intros Γ pb ci p p' c c' brs brs' Hp Hpdep Hc IHc Hb IHb hΓ hl hr.
      destruct Hp as (hpar & hu & hctx & hret). cbn in Hpdep. destruct Hpdep as (IHpar & _ & IHret).
      move: (hl) (hr). cbn [on_free_vars]. move/and5P => [hpl hrl hcl hcc hbl]. move/and5P => [hpr hrr hcr hcc' hbr].
      apply JoinE_Case; [exact hΓ|exact hl|exact hr|exact (All2_dep_J Γ hΓ _ _ hpar IHpar hpl hpr)|exact hu|exact hctx| | |].
      + apply IHret.
        * rewrite /inst_case_predicate_context.
          apply PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context; [exact hpl| |exact hΓ].
          rewrite -test_context_k_closed_on_free_vars_ctx. exact hcl.
        * apply open_app. rewrite inst_case_predicate_context_length. exact hrl.
        * apply open_app. rewrite inst_case_predicate_context_length (All2_length hctx). exact hrr.
      + exact (IHc hΓ hcc hcc').
      + exact (All2_dep_brs Γ p brs brs' #|pparams p'| hΓ Hb hpl IHb hbl hbr).
    - (* Proj *) intros Γ pb p c c' _ IH hΓ hl hr. apply JoinE_Proj. exact (IH hΓ hl hr).
    - (* Fix *) intros Γ pb mfix mfix' idx H IH hΓ hl hr. apply JoinE_Fix.
      have hall := forallb_All _ _ hl. have hall' := forallb_All _ _ hr.
      have hlen := All2_length H. rewrite -hlen in hall'.
      exact (All2_dep_mfix Γ (fix_context mfix) #|mfix| mfix mfix' H hΓ (open_mfix_ctx Γ mfix hΓ hl)
               (fix_context_length mfix) IH hall hall').
    - (* CoFix *) intros Γ pb mfix mfix' idx H IH hΓ hl hr. apply JoinE_CoFix.
      have hall := forallb_All _ _ hl. have hall' := forallb_All _ _ hr.
      have hlen := All2_length H. rewrite -hlen in hall'.
      exact (All2_dep_mfix Γ (fix_context mfix) #|mfix| mfix mfix' H hΓ (open_mfix_ctx Γ mfix hΓ hl)
               (fix_context_length mfix) IH hall hall').
    - (* Prim *) intros Γ pb p p' e de hΓ hl hr. apply JoinE_Prim.
      destruct de as [i|f|s|a a' hre eqdef eqty eqt _ IHd IHt IHv].
      1-3: constructor.
      move: hl hr. cbn [on_free_vars]. simp test_prim. cbn.
      move/andP => [/andP [hvl hdl] htl]. move/andP => [/andP [hvr hdr] htr].
      constructor; [exact hre|exact (IHd hΓ hdl hdr)|exact (IHt hΓ htl htr)|].
      exact (All2_dep_J Γ hΓ _ _ eqt IHv hvl hvr).
    - (* Ind *) intros Γ pb i u u' args args' hu H IH hΓ hl hr. apply JoinE_Ind; [exact hu|].
      move: hl hr. rewrite !on_free_vars_mkApps /= => hl hr.
      exact (All2_dep_J Γ hΓ _ _ H IH hl hr).
    - (* Construct *) intros Γ pb i k u u' args args' hu H IH hΓ hl hr. apply JoinE_Construct; [exact hu|].
      move: hl hr. rewrite !on_free_vars_mkApps /= => hl hr.
      exact (All2_dep_J Γ hΓ _ _ H IH hl hr).
    - (* Sort *) intros Γ pb s s' hs _ _ _. now apply JoinE_Sort.
    - (* Const *) intros Γ pb c u u' hu' _ _ _. now apply JoinE_Const.
    - (* cumul_eta_l: obligation 9's premise *) intros Γ pb na A t u _ IH hΓ hl hr.
      move: (hl). cbn [on_free_vars]. move/andP => [hA ht].
      apply (heta Γ pb na A t u hΓ hl hr).
      apply IH; [exact (closed_snoc_vass Γ na A hΓ hA)|exact (open_snoc Γ _ t ht)|].
      apply open_snoc. cbn [on_free_vars]. apply/andP; split; [|reflexivity].
      apply on_free_vars_lift0. rewrite (on_free_vars_ext _ _ u (addnP_shiftnP 1 _)). exact hr.
  Qed.

End A2.

(** ** Obligation 8 at [FInstFollowKernel] (after repair (a))

  The restated I5 at the kernel's constructor rule, for every [cumulSpecE0]
  rule, with [cumul_eta_l] still the named premise [I5_eta_l_case]
  (obligation 9). A2 above, A4 ([I5_join_to_spec]) and A3 ([I5_join_trans],
  used inside A2) are parametric in [r]; this is their instance at
  [FInstFollowKernel].

  **Hypotheses satisfiable (FRAC's rule):** [wf Σ] by any well-formed
  environment; [I5_eta_l_case] is obligation 9's statement, discharged there
  (its probe: [lanes/eta/obligation9-probe.md]). *)
Theorem I5_obligation8_FollowKernel {cf : checker_flags} (Σ : global_env_ext) (wfΣ : ClosedBodies Σ) :
  I5_eta_l_case FInstFollowKernel Σ -> I5_statement FInstFollowKernel Σ.
Proof.
  intros heta Γ pb t u hΓ ht hu. split.
  - exact (I5_spec_to_join Σ wfΣ FInstFollowKernel heta Γ pb t u hΓ ht hu).
  - exact (I5_join_to_spec Σ wfΣ FInstFollowKernel Γ pb t u hΓ ht hu).
Qed.
