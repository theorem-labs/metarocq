(* Distributed under the terms of the MIT license.   *)
(* The header is base [PCUICNormal]'s (same Requires, same order), so that the copied scripts run
   with the same tactics: a plain [depelim] is Stdlib Program's here, as in base, because [Program] is
   imported after [Equations]; and base's second Import line ([PCUICNormal.v:1908]) stands at the same
   place, before [red_ctx_rel_substE]. One name resolves differently here than at base's place:
   [OnOne2_nth_error], which [PCUICNormal] itself redefines at [:2648] (after its uses at [:1484-1498],
   which mean [All_Forall.OnOne2_nth_error]); the copies write that one qualified. *)
From Equations Require Import Equations.
From Stdlib Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaRocq.Utils Require Import utils monad_utils.
From MetaRocq.Common Require Import config Universes BasicAst Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTactics PCUICOnOne PCUICCases
     PCUICContextReduction PCUICEquality PCUICLiftSubst PCUICTyping PCUICWeakeningEnvConv
     PCUICWeakeningEnvTyp PCUICReduction PCUICClosedTyp PCUICPrimitiveRed
     PCUICInduction PCUICRedTypeIrrelevance PCUICOnFreeVars PCUICEtaExpand PCUICNormal.
From Stdlib Require Import ssreflect ssrbool.
Set Asymmetric Patterns.
(* The E environment, Required only and named qualified: [PCUICTypingEta.wfE] (an existing class) and
   its [ClosedBodies] instance [PCUICClosedTypEta.wfE_ClosedBodies]. *)
From MetaRocq.PCUIC Require PCUICTypingEta PCUICClosedBodies PCUICClosedTypEta.
Local Abbreviation wfE := PCUICTypingEta.wfE.
Local Abbreviation wfE_ClosedBodies := PCUICClosedTypEta.wfE_ClosedBodies.

(** * ETAK discharge, row 13: [whnf_red_inv] over [wfE] (the field of [U_facts])

  BET-64 EtaCheckerLane, worker EtaTranscribe6, 2026-10-30. Row 13 of
  [lanes/eta/etak/eta51-sizing.md] (TRANSCRIPTION). The E twin of base [PCUICNormal.whnf_red_inv]
  ([PCUICNormal.v:2300]) and of the base lemmas of [PCUICNormal.v:1019-2312] that take [wf Σ]:
  [red1_mkApps_tConst_inv] ([:1019]), [whne_red1_ind] ([:1222]), [whne_pres1] ([:1476]), [whne_pres]
  ([:1542]), [whnf_lit_pres1] ([:1556]), [whnf_pres1] ([:1598]), [whnf_pres] ([:1670]),
  [red_ctx_rel_subst] ([:1910]), [red_terms_on_free_vars] ([:1969]), [br_fvs_pres] ([:1984]),
  [whnf_red_trans] ([:2004]), [whne_red1_inv] ([:2157]), [whnf_red1_inv] ([:2223]). Each E twin is base's
  statement with [wf Σ] replaced by [wfE Σ] and the name suffixed [E]; reduction, [whnf], [whne] and
  [whnf_red] are untyped and unchanged in E. The proof scripts are base's. The changes:
  - [declared_constant_to_gen] is generic over [on_global_env]; [wfE Σ] serves it unchanged.
  - Base uses four lemmas stated under [wf Σ] whose proofs are their [ClosedBodies] twins through
    [wf_ClosedBodies]: [red_red] ([PCUICSubstitution.v:1594]), [red_on_free_vars]
    ([Typing/PCUICClosedTyp.v:865]), [red_red_ctx] and [red_context_app_right]
    ([PCUICContextReduction.v:438], [:465]). The E scripts call the twins themselves, [red_red_cb]
    ([PCUICSubstitution.v:1482]), [PCUICClosedTyp.red_on_free_vars_cb] ([:856]), [red_red_ctx_cb] and
    [red_context_app_right_cb] ([PCUICContextReduction.v:191], [:320]), at
    [wfE_ClosedBodies] ([Typing/PCUICClosedTypEta.v:581]).
  - Calls to the copied lemmas name their E twins.
  - BET-339 (ship lineage, base integ-all8 [1a92b56c]; the line numbers above are frac/eta's base):
    base [whne] gains [whne_case_cofix_dep] (a case with [ci_cofix_nondep] unset on a cofixpoint is
    neutral). Base integ-all8 restates [whne_red1_ind] with the hypothesis [Hcase_cofix_dep] and adds
    its case to the proofs of [whne_red1_ind], [whne_pres1] and [whne_red1_inv]; the E twins take the
    same hypothesis and base integ-all8's case scripts, verbatim. These are internal lemmas; the
    statement of [whnf_red_invE] (the field) is unchanged.
  The lemmas of the block that take no [wf] ([whnf_red_refl], [whnf_red_mkApps], [OnOne2_primapp_split],
  [red1_mkApps_tFix_inv], ...) are base's, used unchanged. No hypothesis (no [Context], no class field). *)

Local Ltac inv H := inversion H; subst; clear H.

(** Base [red1_mkApps_tConst_inv] ([PCUICNormal.v:1019]). *)
Lemma red1_mkApps_tConst_invE {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ c u decl op args t' :
  lookup_env Σ c = Some (ConstantDecl decl) ->
  cst_body decl = None ->
  prim_op_of Σ c = Some op ->
  #|args| <= arity op ->
  prim_reduct Σ op args = None ->
  red1 Σ Γ (mkApps (tConst c u) args) t' ->
  ∑ args', (t' = mkApps (tConst c u) args') × OnOne2 (red1 Σ Γ) args args'.
Proof.
  intros hl hb hop hlen hcf r.
  revert t' hlen hcf r. induction args using rev_ind; intros t' hlen hcf r.
  - cbn in r. depelim r; try solve_discr.
    + (* red_delta: cst_body = Some, contradicting hb *)
      unshelve epose proof (hg := declared_constant_to_gen isdecl); eauto.
      unfold declared_constant_gen in hg. rewrite hl in hg.
      noconf hg. congruence.
    + (* red_prim_op with ls = [] : prim_reduct = Some, contradicting hcf *)
      exfalso. destruct ls; [|discriminate]. rewrite hop in e. noconf e.
      move: hcf. rewrite /prim_reduct /= e1 e2 //.
  - rewrite mkApps_snoc in r. depelim r; try solve_discr; try solve [help].
    + (* red_prim_op at the root: args ++ [x0] all literals, prim_reduct = Some *)
      exfalso. move: hcf.
      rewrite -mkApps_snoc in x. apply mkApps_eq_inj in x as [eh ea]; [|easy|easy]. noconf eh.
      rewrite hop in e. noconf e.
      rewrite -ea /prim_reduct lits_of_args_map e1 e2 //.
    + (* app_red_l: the head application reduces *)
      edestruct (IHargs N1) as (args' & -> & ho).
      * rewrite length_app /= in hlen; lia.
      * apply prim_reduct_short. rewrite length_app /= in hlen; lia.
      * exact r.
      * exists (args' ++ [x]). rewrite mkApps_snoc. split; [reflexivity|].
        now apply OnOne2_app_r.
    + (* app_red_r: the last argument reduces *)
      exists (args ++ [N2]). rewrite mkApps_snoc. split; [reflexivity|].
      apply OnOne2_app. now constructor.
Qed.

Section whne_red1_indE.
Context (flags : RedFlags.t).
Context (Σ : global_env).
Context (Γ : context).
Context (P : term -> term -> Type).

(** Base [whne_red1_ind] ([PCUICNormal.v:1222]). *)
Lemma whne_red1_indE {cf:checker_flags} {wfΣ : wfE Σ}
      (Hlam_nobeta_1 : forall na A b M',
          RedFlags.beta flags = false ->
          red1 Σ Γ A M' ->
          P (tLambda na A b) (tLambda na M' b))
      (Hlam_nobeta_2 : forall na A b M',
          RedFlags.beta flags = false ->
          red1 Σ (Γ,, vass na A) b M' ->
          P (tLambda na A b) (tLambda na A M'))
      (Hevar : forall n l l',
          OnOne2 (red1 Σ Γ) l l' ->
          P (tEvar n l) (tEvar n l'))
      (Hletin_nozeta_1 :
         forall t' na B b t,
           RedFlags.zeta flags = false ->
           red1 Σ Γ (tLetIn na B b t) t' ->
           P (tLetIn na B b t) t')
      (Hconst_nodelta : forall t' c u,
          RedFlags.delta flags = false ->
          red1 Σ Γ (tConst c u) t' ->
          P (tConst c u) t')
      (Hbeta_nobeta :
         forall na t b v,
           RedFlags.beta flags = false ->
           P (tApp (tLambda na t b) v) (b{0 := v}))
      (Hfix_nofix :
         forall v mfix idx args narg fn,
           RedFlags.fix_ flags = false ->
           nth_error mfix idx = Some narg ->
           is_constructor (rarg narg) (args ++ [v]) = true ->
           P (mkApps (tFix mfix idx) (args ++ [v])) (mkApps fn (args ++ [v])))
      (Happ_1 : forall f v N1,
          whne flags Σ Γ f ->
          red1 Σ Γ f N1 ->
          P f N1 ->
          P (tApp f v) (tApp N1 v))
      (Happ_2 : forall f v N2,
          whne flags Σ Γ f ->
          red1 Σ Γ v N2 ->
          P (tApp f v) (tApp f N2))
      (Hfix_red_arg : forall mfix idx args narg arg x,
          nth_error mfix idx = Some narg ->
          nth_error args (rarg narg) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2 (fun a a' => red1 Σ Γ a a') args x ->
          (forall t', red1 Σ Γ arg t' -> P arg t') ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix mfix idx) x))
      (Hfix_red_def_type : forall mfix idx args d arg x,
          nth_error mfix idx = Some d ->
          nth_error args (rarg d) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2
            (fun x y : def term =>
               red1 Σ Γ (dtype x) (dtype y) *
               ((dname x, dbody x, BasicAst.rarg x) =
                (dname y, dbody y, BasicAst.rarg y))) mfix x ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix x idx) args))
      (Hfix_red_def_body : forall mfix idx args narg arg x,
          nth_error mfix idx = Some narg ->
          nth_error args (rarg narg) = Some arg ->
          whne flags Σ Γ arg ->
          OnOne2
            (fun x y : def term =>
               red1 Σ (Γ ,,, fix_context mfix) (dbody x) (dbody y) *
               ((dname x, dtype x, BasicAst.rarg x) =
                (dname y, dtype y, BasicAst.rarg y))) mfix x ->
          P (mkApps (tFix mfix idx) args) (mkApps (tFix x idx) args))
      (Hfix_red_type_nofix : forall defs i mfix1,
          RedFlags.fix_ flags = false ->
          OnOne2
            (fun x y : def term =>
               red1 Σ Γ (dtype x) (dtype y) *
               ((dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)))
            defs mfix1 ->
          P (tFix defs i) (tFix mfix1 i))
      (Hfix_red_body_nofix : forall defs i mfix1,
          RedFlags.fix_ flags = false ->
          OnOne2
            (fun x y : def term =>
               red1 Σ (Γ ,,, fix_context defs) (dbody x) (dbody y) *
               ((dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)))
            defs mfix1 ->
          P (tFix defs i) (tFix mfix1 i))
      (Hcase_params : forall i p c brs params',
          whne flags Σ Γ c ->
          OnOne2 (red1 Σ Γ) p.(pparams) params' ->
          P (tCase i p c brs) (tCase i (set_pparams p params') c brs))
      (Hcase_motive : forall i  p c brs p',
          whne flags Σ Γ c ->
          red1 Σ (Γ ,,, inst_case_predicate_context p) p.(preturn) p' ->
          P (tCase i p c brs) (tCase i (set_preturn p p') c brs))
      (Hcase_discr : forall i p c brs c',
          whne flags Σ Γ c ->
          red1 Σ Γ c c' ->
          P c c' ->
          P (tCase i p c brs) (tCase i p c' brs))
      (Hcase_branch : forall i p c brs brs',
          whne flags Σ Γ c ->
          OnOne2 (fun br br' =>
            let ctx := inst_case_branch_context p br in
            (on_Trel_eq (red1 Σ (Γ ,,, ctx)) bbody bcontext br br')%type)
            brs brs' ->
          P (tCase i p c brs) (tCase i p c brs'))
      (Hcase_noiota : forall t' i p c brs,
          RedFlags.iota flags = false ->
          red1 Σ Γ (tCase i p c brs) t' ->
          P (tCase i p c brs) t')
      (Hcase_cofix_dep : forall t' i p mfix idx args brs,
          i.(ci_cofix_nondep) = false ->
          red1 Σ Γ (tCase i p (mkApps (tCoFix mfix idx) args) brs) t' ->
          P (tCase i p (mkApps (tCoFix mfix idx) args) brs) t')
      (Hproj : forall p c c',
          whne flags Σ Γ c ->
          red1 Σ Γ c c' ->
          P c c' ->
          P (tProj p c) (tProj p c'))
      (Hproj_cofix_noiota : forall p mfix idx args narg fn,
          RedFlags.iota flags = false ->
          unfold_cofix mfix idx = Some (narg, fn) ->
          P (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args)))
      (Hproj_noiota : forall p args u arg,
          RedFlags.iota flags = false ->
          nth_error args (p.(proj_npars) + p.(proj_arg)) = Some arg ->
          P (tProj p (mkApps (tConstruct p.(proj_ind) 0 u) args)) arg)
      (Hproj_discr_noiota : forall p c c',
          RedFlags.iota flags = false ->
          red1 Σ Γ c c' ->
          P (tProj p c) (tProj p c'))
      (Hprimapp_stuck : forall c u decl op ls a rest t',
          lookup_env Σ c = Some (ConstantDecl decl) ->
          decl.(cst_body) = None ->
          prim_op_of Σ c = Some op ->
          #|ls| + S #|rest| = arity op ->
          whne flags Σ Γ a ->
          (forall a', red1 Σ Γ a a' -> P a a') ->
          red1 Σ Γ (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) t' ->
          P (mkApps (tConst c u) (map term_of_lit ls ++ a :: rest)) t')
      (Hprimapp_inert : forall c u decl op ls t',
          lookup_env Σ c = Some (ConstantDecl decl) ->
          decl.(cst_body) = None ->
          prim_op_of Σ c = Some op ->
          #|ls| = arity op ->
          prim_reduct Σ op (map term_of_lit ls) = None ->
          red1 Σ Γ (mkApps (tConst c u) (map term_of_lit ls)) t' ->
          P (mkApps (tConst c u) (map term_of_lit ls)) t')
      (* Under [nodelta] every constant is neutral ([whne_const_nodelta]), so a
         registered application is neutral there too, and the rule still fires:
         [red1] does not read the flags.  Vacuous at [RedFlags.default]. *)
      (Hprimapp_nodelta : forall c u decl op ls r v,
          RedFlags.delta flags = false ->
          prim_op_of Σ c = Some op ->
          declared_constant Σ c decl ->
          cst_body decl = None ->
          prim_op_denote op ls = Some r ->
          readback Σ (po_shape (info op)) r = Some v ->
          P (mkApps (tConst c u) (map term_of_lit ls)) v) :
  forall t t', whne flags Σ Γ t -> red1 Σ Γ t t' -> P t t'.
Proof using Type.
  intros t t' wh r.
  induction wh in t, t', wh, r |- *; cbn in *.
  - depelim r; try congruence; solve_discr.
  - depelim r; solve_discr; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; eauto.
  - eauto.
  - depelim r; solve_discr; try congruence.
    unshelve eapply declared_constant_to_gen in isdecl; try exact wfΣ.
    unfold declared_constant, declared_constant_gen in isdecl.
    rewrite e in isdecl.
    inv isdecl.
    congruence.
  - eauto.
  - depelim r; eauto.
    + depelim wh; solve_discr.
      now apply Hbeta_nobeta.
    + unfold unfold_fix in *.
      destruct args as [|? ? _] using MRList.rev_ind; [now solve_discr|].
      rewrite mkApps_app in x.
      cbn in *.
      inv x.
      eapply whne_mkApps_inv in wh as [wh|(? & ? & ? & ? & e3 & _)]; [|discriminate|easy].
      destruct wh as [|].
      * depelim w; try congruence.
        all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                  try reflexivity; cbn in x; noconf x).
        -- exfalso. match goal with H : nth_error [] ?n = Some _ |- _ =>
             now rewrite nth_error_nil in H end.
        -- rewrite <- mkApps_snoc.
           case_eq (nth_error mfix idx); [intros d H|intros H];
             rewrite H in e; [|discriminate].
           noconf e. eapply Hfix_nofix; eauto.
      * destruct s as (?&?&?&?&?&?&?&?).
        inv e1.
        rewrite e2 in e.
        inv e.
        unfold is_constructor in e0.
        erewrite nth_error_app_left in e0 by eassumption.
        now apply whne_isConstruct_app in w; auto.
    + (* red_prim_op: the head would have to be neutral, but it is an
         unsaturated application of a registered operation. *)
      destruct ls as [|l ls _] using MRList.rev_ind; [now cbn in x|].
      rewrite map_app mkApps_app /= in x. noconf x.
      case_eq (RedFlags.delta flags); intros hd.
      2:{ pose proof (Hprimapp_nodelta c u decl op (ls ++ [l]) r v0 hd e d e0 e1 e2) as hp.
          rewrite map_app mkApps_app /= in hp. exact hp. }
      exfalso.
      pose proof (prim_op_denote_args _ _ _ e1) as hargs.
      rewrite map_app /= in hargs.
      assert (harity : arity op = S #|ls|)
        by (unfold arity; rewrite -hargs length_app length_map /=; lia).
      eapply whne_mkApps_inv in wh
        as [[w|(? & ? & ? & ? & e3 & _)]|(? & ? & ? & op' & e3 & _ & _ & hop' & hle & _)];
        try reflexivity; try discriminate.
      * eapply whne_tConst_prim with (op := op); [exact hd|exact e| |exact w]. lia.
      * noconf e3. rewrite e in hop'. noconf hop'.
        rewrite length_map in hle. lia.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { unfold unfold_fix. rewrite e.
         unfold is_constructor.
         rewrite e0.
         destruct isConstruct_app eqn:ctor; [|easy].
         now eapply whne_isConstruct_app in ctor. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
  - depelim r; eauto.
    all: try solve [help].
    destruct args using MRList.rev_ind; [|rewrite mkApps_app in x; cbn in x; discriminate].
    cbn in *.
    unfold is_constructor in e1.
    rewrite nth_error_nil in e1; discriminate.
  - depelim r; eauto. all: try solve [help].
    + eapply whne_mkApps_inv in wh as [wh|(? & ? & ? & ? & e3 & _)]; [|discriminate|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w; try help.
      all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                try reflexivity; cbn in x; noconf x).
    + try solve_discr.
      all: eapply whne_mkApps_inv in wh as [[w|(? & ? & ? & ? & e3 & _)]|(? & ? & ? & ? & e3 & _)];
        try reflexivity; try discriminate.
      all: depelim w; help.
  - eauto.
  - eapply Hcase_cofix_dep; eauto.
  - depelim r; eauto. all: try solve [help].
    + try solve_discr.
      all: eapply whne_mkApps_inv in wh as [[w|(? & ? & ? & ? & e3 & _)]|(? & ? & ? & ? & e3 & _)];
        try reflexivity; try discriminate.
      all: depelim w; help.
    + eapply whne_mkApps_inv in wh as [wh|(? & ? & ? & ? & e3 & _)]; [|discriminate|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim w; try help.
      all: try (apply (f_equal decompose_app) in x; rewrite decompose_app_mkApps in x;
                try reflexivity; cbn in x; noconf x).
  - depelim r; eauto. all: try solve [help|solve_discr].
  - (* whne_primapp_stuck *)
    eapply Hprimapp_stuck; eauto.
  - (* whne_primapp_inert *)
    eapply Hprimapp_inert; eauto.
Qed.
End whne_red1_indE.

(** Base [whne_pres1] ([PCUICNormal.v:1476]). *)
Lemma whne_pres1E {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ t t' :
  red1 Σ Γ t t' ->
  whne RedFlags.default Σ Γ t ->
  whne RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  apply (whne_red1_indE RedFlags.default Σ Γ (fun _ => whne RedFlags.default Σ Γ))
         with (t := t) (t' := t'); intros; try easy.
  - eapply All_Forall.OnOne2_nth_error in H0; eauto.
    destruct H0 as (?&?&[->|]).
    + eapply whne_fixapp; eauto.
    + apply X1 in r0.
      eapply whne_fixapp; eauto.
  - unfold unfold_fix in *.
    destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply All_Forall.OnOne2_nth_error in nth; eauto.
    inv H.
    destruct nth as (?&?&[->|(?&?)]).
    + eapply whne_fixapp; eauto.
    + eapply whne_fixapp; eauto.
      now inv e0.
  - destruct (nth_error mfix idx) eqn:nth; [|easy].
    eapply All_Forall.OnOne2_nth_error in nth; eauto.
    inv H.
    destruct nth as (?&?&[->|(?&?)]).
    + eapply whne_fixapp; eauto.
    + eapply whne_fixapp; eauto.
      now inv e0.
  - match goal with
    | h : red1 _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ |- _ => depelim h
    end.
    + solve_discr.
    + solve_discr.
    + congruence.
    + (* red_prim_op: its left side is an application of a constant, not a case *)
      match goal with x : mkApps (tConst _ _) ?l = tCase _ _ _ _ |- _ =>
        let l' := fresh "l" in remember l as l' eqn:Hl; clear Hl;
        destruct l' as [|? l' _] using MRList.rev_ind;
          [discriminate x|rewrite mkApps_app in x; discriminate x]
      end.
    + now apply whne_case_cofix_dep.
    + now apply whne_case_cofix_dep.
    + match goal with
      | h : red1 _ _ (mkApps (tCoFix _ _) _) _ |- _ =>
        eapply red1_mkApps_tCoFix_inv in h as [[(?&->&?)|(?&->&?)]|(?&->&?)]
      end; now apply whne_case_cofix_dep.
    + now apply whne_case_cofix_dep.
  - (* Hprimapp_stuck: a stuck primitive application steps inside an argument *)
    clear r wh.
    rename c into c0, u into u0, decl into decl0, op into op0,
           ls into ls0, a into a0, rest into rest0.
    match goal with [ H : lookup_env _ _ = _ |- _ ] => rename H into hl0 end.
    match goal with [ H : cst_body _ = None |- _ ] => rename H into hb0 end.
    match goal with [ H : prim_op_of _ _ = Some _ |- _ ] => rename H into hop0 end.
    match goal with [ H : _ + S _ = arity _ |- _ ] => rename H into hlen0 end.
    match goal with [ H : red1 _ _ (mkApps _ _) _ |- _ ] => rename H into hr0 end.
    assert (hle : #|map term_of_lit ls0 ++ a0 :: rest0| <= arity op0)
      by (rewrite length_app length_map /=; lia).
    assert (ha0 : lit_of_term a0 = None)
      by (eapply whne_not_lit; eassumption).
    assert (hcf : prim_reduct Σ op0 (map term_of_lit ls0 ++ a0 :: rest0) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app ha0) //).
    eapply red1_mkApps_tConst_invE in hr0 as (args' & -> & ho); try eassumption.
    assert (hnolit : forall l t, red1 Σ Γ (term_of_lit l) t -> False)
      by (intros ? ? Hl; eapply red1_term_of_lit; exact Hl).
    destruct (OnOne2_primapp_split _ _ _ _ hnolit ho) as [(a'&->&ra)|(rest'&->&ho')].
    + eapply whne_primapp_stuck; [ eassumption .. | ].
      match goal with
      | [ Hih : forall _, red1 _ _ _ _ -> whne _ _ _ _ |- _ ] => eapply Hih; exact ra
      end.
    + eapply whne_primapp_stuck; [ eassumption | eassumption | eassumption | | eassumption ].
      now rewrite -(OnOne2_length ho').
  - (* Hprimapp_inert: a literal application cannot step *)
    exfalso.
    match goal with
    | [ Hr : red1 _ _ (mkApps (tConst _ _) (map term_of_lit ?ls0)) _ |- _ ] =>
        eapply (red1_mkApps_tConst_invE _ _ _ _ _ _ (map term_of_lit ls0))
          in Hr as (args' & _ & ho)
    end.
    2-4: eassumption.
    2: rewrite length_map; lia.
    2: eassumption.
    eapply OnOne2_map_term_of_lit; exact ho.
Qed.

(** Base [whne_pres] ([PCUICNormal.v:1542]). *)
Lemma whne_presE {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ t t' :
  red Σ Γ t t' ->
  whne RedFlags.default Σ Γ t -> whne RedFlags.default Σ Γ t'.
Proof.
  induction 1 using red_rect_n1; eauto using whne_pres1E.
Qed.

(** Base [whnf_lit_pres1] ([PCUICNormal.v:1556]). *)
Lemma whnf_lit_pres1E {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ a a' :
  whnf RedFlags.default Σ Γ a ->
  lit_of_term a = None ->
  red1 Σ Γ a a' ->
  lit_of_term a' = None.
Proof.
  intros wh hlit r. destruct wh.
  - (* neutral: a' is neutral, hence not a literal *)
    eapply whne_not_lit. eapply whne_pres1E; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; reflexivity.
  - depelim r; solve_discr; reflexivity.
  - apply red1_mkApps_tConstruct_inv in r as (v'&->&_).
    destruct v' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
  - apply red1_mkApps_tInd_inv in r as (v'&->&_).
    destruct v' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
  - assert (hnc : match unfold_fix mfix idx with
                  | Some (rarg, _) => is_constructor rarg args = false
                  | None => True end).
    { unfold unfold_fix. destruct o as [[? [-> ?]]|hn];
      [now unfold is_constructor; rewrite H|now rewrite hn]. }
    eapply red1_mkApps_tFix_inv in r as [[(v'&->&_)|(mfix'&->&_)]|(mfix'&->&_)]; tea.
    all: match goal with |- lit_of_term (mkApps _ ?l) = None =>
           destruct l using MRList.rev_ind end; rewrite ?mkApps_snoc; reflexivity.
  - apply red1_mkApps_tCoFix_inv in r as [[(v'&->&_)|(mfix'&->&_)]|(mfix'&->&_)];
      match goal with |- lit_of_term (mkApps _ ?l) = None =>
        destruct l using MRList.rev_ind end; rewrite ?mkApps_snoc; reflexivity.
  - cbn in hlit. depelim r; solve_discr; cbn; reflexivity.
  - (* partial: cannot fire (too few arguments); reduces inside an argument *)
    assert (hcf : prim_reduct Σ op args = None) by now apply prim_reduct_short.
    assert (hle : #|args| <= arity op) by lia.
    eapply red1_mkApps_tConst_invE in r as (args'&->&_); try eassumption.
    destruct args' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
  - (* rigid: cannot fire (a non-literal argument); reduces inside an argument *)
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    assert (hcf : prim_reduct Σ op (map term_of_lit ls ++ a :: rest) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app e3) //).
    eapply red1_mkApps_tConst_invE in r as (args'&->&_); try eassumption.
    destruct args' using MRList.rev_ind; [reflexivity|now rewrite mkApps_snoc].
Qed.

(** Base [whnf_pres1] ([PCUICNormal.v:1598]). *)
Lemma whnf_pres1E {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ t t' :
  red1 Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t ->
  whnf RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  induction wh in wh, t, t', r |- *; cbn in *.
  - constructor.
    now eapply whne_pres1E.
  - depelim r; solve_discr.
  - depelim r; try easy; solve_discr.
  - depelim r; try easy; solve_discr.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_cstrapp.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_indapp.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { unfold unfold_fix. destruct o as [[? [-> ?]] | ];
        unfold is_constructor; now rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_fixapp. destruct o as [[d [? ?]] | ]; [left ; exists d| easy].
      split; eauto.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H0.
      lia.
    + apply whnf_fixapp.
      destruct o as [[d [? ?]] | ]; [left| right].
      eapply OnOne2_sym in o0.
      eapply OnOne2_nth_error_r in o0; eauto.
      destruct o0 as [? [? ?]]. eexists; split; eauto.
      destruct s as [| [? ?]]. now subst. now inv e0.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
    + apply whnf_fixapp.
      destruct o as [[d [? ?]] | ]; [left| right].
      eapply OnOne2_sym in o0.
      eapply OnOne2_nth_error_r in o0; eauto.
      destruct o0 as [? [? ?]]. eexists; split; eauto.
      destruct s as [| [? ?]]. now subst. now inv e0.
      apply OnOne2_length in o0.
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
  - eapply red1_mkApps_tCoFix_inv in r as [[(?&->&?)|(?&->&?)]|(?&->&?)]; eauto.
  - depelim r; solve_discr; eapply whnf_prim.
  - (* whnf_primapp_partial: still unsaturated after a step inside an argument *)
    assert (hle : #|args| <= arity op) by lia.
    assert (hcf : prim_reduct Σ op args = None) by now apply prim_reduct_short.
    eapply red1_mkApps_tConst_invE in r as (args'&->&ho); try eassumption.
    eapply whnf_primapp_partial; try eassumption.
    apply OnOne2_length in ho; lia.
  - (* whnf_primapp_rigid: still blocked on a whnf non-literal after a step *)
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    assert (hcf : prim_reduct Σ op (map term_of_lit ls ++ a :: rest) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app e3) //).
    eapply red1_mkApps_tConst_invE in r as (args'&->&ho); try eassumption.
    assert (hnolit : forall l t, red1 Σ Γ (term_of_lit l) t -> False)
      by (intros ? ? Hl; eapply red1_term_of_lit; exact Hl).
    destruct (OnOne2_primapp_split _ _ _ _ hnolit ho) as [(a'&->&ra)|(rest'&->&ho')].
    + eapply whnf_primapp_rigid; try eassumption.
      * match goal with
        | [ H : forall _, red1 _ _ a _ -> whnf _ _ _ _ |- _ ] => eapply H; exact ra
        end.
      * eapply whnf_lit_pres1E; try eassumption.
    + eapply whnf_primapp_rigid; try eassumption.
      now rewrite -(OnOne2_length ho').
Qed.

(** Base [whnf_pres] ([PCUICNormal.v:1670]). *)
Lemma whnf_presE {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ t t' :
  red Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t -> whnf RedFlags.default Σ Γ t'.
Proof.
  induction 1 using red_rect_n1; eauto using whnf_pres1E.
Qed.

(* Base's second Import line ([PCUICNormal.v:1908]), at base's place. *)
From MetaRocq.PCUIC Require Import PCUICWellScopedCumulativity PCUICOnFreeVars PCUICConfluence PCUICSR PCUICConversion PCUICSubstitution.

(** Base [red_ctx_rel_subst] ([PCUICNormal.v:1910]); [red_red] is its [ClosedBodies] twin [red_red_cb]. *)
Lemma red_ctx_rel_substE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} P Γ Γ' s s' Δ :
  All2 (red Σ Γ) s s' ->
  All (on_free_vars (shiftnP #|Γ| P)) s ->
  untyped_subslet Γ s Γ' ->
  on_free_vars_ctx P (Γ ,,, Γ' ,,, Δ) ->
  red_context_rel Σ Γ (subst_context s 0 Δ) (subst_context s' 0 Δ).
Proof.
  intros Hs ons subs onctx.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  induction Δ; cbn.
  * rewrite !subst_context_nil. constructor.
  * move: onctx => /=. rewrite on_free_vars_ctx_snoc => /andP[] onctx ona.
    rewrite !subst_context_snoc !Nat.add_0_r.
    constructor; eauto.
    now apply IHΔ.
    destruct a as [na [b|] ty]; constructor; cbn.
    relativize #|Δ|. eapply red_red_cb; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
    relativize #|Δ|. eapply red_red_cb; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
    relativize #|Δ|. eapply red_red_cb; tea. 4:auto.
    erewrite on_free_vars_ctx_on_ctx_free_vars => //; tea.
    unfold on_free_vars_decl, test_decl in onctx. cbn in onctx.
    now move/andP: ona.
    solve_all. rewrite !app_context_length Nat.add_assoc -shiftnP_add addnP_shiftnP //.
Qed.

(** Base [red_terms_on_free_vars] ([PCUICNormal.v:1969]); [red_on_free_vars] is its [ClosedBodies]
    twin [PCUICClosedTyp.red_on_free_vars_cb]. *)
Lemma red_terms_on_free_varsE {cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ ts us}:
  is_closed_context Γ ->
  forallb (is_open_term Γ) ts ->
  All2 (red Σ Γ) ts us ->
  forallb (is_open_term Γ) us.
Proof.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  solve_all. eapply PCUICClosedTyp.red_on_free_vars_cb; tea.
  now rewrite on_free_vars_ctx_on_ctx_free_vars.
Qed.

(** Base [br_fvs_pres] ([PCUICNormal.v:1984]); [red_on_free_vars] as above. *)
Lemma br_fvs_presE {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} Γ motive brs brs' :
  is_closed_context Γ ->
  forallb (is_open_term Γ) (pparams motive) ->
  All (br_fvs Γ motive) brs ->
  All2
    (fun br br' : branch term =>
    red Σ (Γ,,, inst_case_branch_context motive br)
       (bbody br) (bbody br') * (bcontext br = bcontext br')) brs brs' ->
  All (br_fvs Γ motive) brs'.
Proof.
  intros clΓ clpars.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  unfold br_fvs; solve_all.
  now rewrite b0 in H.
  rewrite -b0. eapply PCUICClosedTyp.red_on_free_vars_cb; tea.
  rewrite shiftnP_add. relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
  2:len.
  rewrite on_free_vars_ctx_app clΓ /=.
  eapply on_free_vars_ctx_inst_case_context; trea. solve_all.
Qed.

(** Base [whnf_red_trans] ([PCUICNormal.v:2004]); [red_red_ctx] and [red_context_app_right] are their
    [ClosedBodies] twins [red_red_ctx_cb] and [red_context_app_right_cb], at [cbΣ]. *)
Lemma whnf_red_transE {cf:checker_flags} {Σ : global_env_ext} Γ x y z : wfE Σ ->
  is_closed_context Γ ->
  is_open_term Γ x ->
  whnf_red Σ Γ x y ->
  whnf_red Σ Γ y z ->
  whnf_red Σ Γ x z.
Proof.
  intros wf onΓ onx xy yz.
  pose proof (wfE_ClosedBodies Σ.1) as cbΣ.
  revert onx z yz.
  (* [Equations.Prop.DepElim.depelim] is written out here and below on purpose, as in base: in this
     file a plain [depelim] is Stdlib Program's, whose [existT] simplification uses the axiom
     [Eqdep.Eq_rect_eq.eq_rect_eq]; Equations' version needs no axiom here. *)
  induction xy; intros onx z yz; Equations.Prop.DepElim.depelim yz; repeat inv_on_free_vars; eauto using whnf_red.
  - constructor.
    eapply All2_trans; eauto.
    typeclasses eauto.
  - constructor; eauto.
    all: try etransitivity; eauto.
  - constructor.
    eapply All2_trans; eauto.
    1: { intros ? ? ? (->&->&?&?) (->&->&?&?).
         do 2 (split; auto).
         split; etransitivity; eauto. }
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&?&?).
    do 3 (split; auto).
    eapply context_pres_let_bodies_red; eauto.
    apply fix_context_pres_let_bodies.
    now apply All2_length in a.
  - simpl in *.
    constructor; try solve [etransitivity; eauto].
    + eapply All2_trans; eauto.
      typeclasses eauto.
    + etransitivity; [eassumption|].
      have clp: on_ctx_free_vars (closedP #|Γ,,, inst_case_predicate_context motive| xpredT)
        (Γ,,, inst_case_predicate_context motive).
      { rewrite closedP_shiftnP_eq on_free_vars_ctx_on_ctx_free_vars.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
        rewrite test_context_k_closed_on_free_vars_ctx //. }
      eapply red_red_ctx_cb. 5:tea. all:eauto; revgoals.
      apply red_context_app_right_cb; eauto.
      * apply red_context_refl.
      * rewrite /inst_case_predicate_context /=.
        rewrite /inst_case_context.
        eapply (red_ctx_rel_substE (Σ := empty_ext Σ)).
        eapply All2_rev => //.
        eapply All_rev. solve_all.
        instantiate (1 := List.rev (fake_params #|pparams motive|)).
        rewrite -(List.length_rev (pparams motive)).
        eapply params_subslet.
        rewrite !on_free_vars_ctx_app onΓ /=. len.
        rewrite on_free_vars_ctx_subst_instance.
        rewrite closed_fake_params /=.
        setoid_rewrite closedP_shiftnP_eq in p1.
        eapply on_free_vars_ctx_impl; tea.
        rewrite /shiftnP. intros i. rewrite !orb_false_r.
        move/Nat.ltb_lt => ?. apply Nat.ltb_lt. lia.
      * eapply PCUICClosedTyp.red_on_free_vars_cb; tea.
        len. rewrite closedP_shiftnP_eq -shiftnP_add //.
      * rewrite closedP_shiftnP_eq.
        relativize #|Γ ,,, _|; [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //. cbn.
        eapply red_terms_on_free_varsE; tea.
        rewrite test_context_k_closed_on_free_vars_ctx -(All2_length a) //.

    + eapply forallb_All in p3.
      epose proof (br_fvs_presE _ _ _ _ onΓ p p3 a0).
      eapply (All2_impl (P:=fun br br' => br_fvs Γ motive br ×
        red Σ (Γ,,, inst_case_branch_context motive br) (bbody br) (bbody br') *
            (bcontext br = bcontext br'))).
      2:intuition.
      eapply All2_trans with brs'.
      { clear -wf p.
        intros br br' br''. intuition auto. 2:congruence.
        etransitivity; tea. unfold inst_case_branch_context in *. now rewrite -b1 in a2. }
      1:solve_all.
      eapply All2_All_mix_left in a2; tea. eapply All2_impl; tea.
      intros br br'; cbn. intuition auto.
      unfold br_fvs in a3.
      move/andP: a3 => [] fvbctx fvbr.
      eapply red_red_ctx_cb. 5:tea. all:eauto; revgoals.
      apply red_context_app_right_cb; eauto.
      * rewrite closedP_shiftnP_eq on_free_vars_ctx_on_ctx_free_vars.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
      * apply red_context_refl.
      * rewrite /inst_case_branch_context /=.
        rewrite /inst_case_context.
        eapply (red_ctx_rel_substE (Σ := empty_ext Σ)).
        eapply All2_rev => //.
        eapply All_rev. solve_all.
        instantiate (1 := List.rev (fake_params #|pparams motive|)).
        rewrite -(List.length_rev (pparams motive)).
        eapply params_subslet.
        rewrite !on_free_vars_ctx_app onΓ /=. len.
        rewrite on_free_vars_ctx_subst_instance.
        rewrite closed_fake_params /=.
        move: fvbctx.
        rewrite test_context_k_closed_on_free_vars_ctx closedP_shiftnP_eq => H.
        eapply on_free_vars_ctx_impl; tea.
        rewrite /shiftnP. intros i. rewrite !orb_false_r.
        move/Nat.ltb_lt => ?. apply Nat.ltb_lt. lia.
      * rewrite shiftnP_add.
        relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
      * rewrite shiftnP_add.
        relativize (#|_| + _); [erewrite on_free_vars_ctx_on_ctx_free_vars|].
        2:len.
        rewrite on_free_vars_ctx_app onΓ /=.
        eapply on_free_vars_ctx_inst_case_context => //.
        eapply red_terms_on_free_varsE; tea.
        now rewrite -(All2_length a).
  - constructor.
    etransitivity; eauto.
  - constructor; etransitivity; eauto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; eauto; [|constructor].
    apply All2_fold_refl.
    intros _ ?. reflexivity.
  - constructor; etransitivity; eauto.
    eapply context_pres_let_bodies_red; eauto.
    constructor; eauto; [|constructor].
    apply All2_fold_refl.
    intros _ ?; reflexivity.
  - constructor.
    eapply All2_trans; eauto.
    1: { intros ? ? ? (->&->&?&?) (->&->&?&?).
         do 2 (split; auto).
         split; etransitivity; eauto. }
    eapply All2_impl; eauto.
    cbn.
    intros ? ? (->&->&?&?).
    do 3 (split; auto).
    eapply context_pres_let_bodies_red; eauto.
    apply fix_context_pres_let_bodies.
    now apply All2_length in a.
  - (* One sentence: a sentence that starts with [Equations.] parses as the [Equations] command. *)
    constructor; Equations.Prop.DepElim.depelim o; Equations.Prop.DepElim.depelim o0; constructor; eauto.
    * etransitivity; tea.
    * etransitivity; tea.
    * etransitivity; tea.
    * eapply All2_trans; eauto.
      tc.
Qed.

(** Base [whne_red1_inv] ([PCUICNormal.v:2157]). *)
Lemma whne_red1_invE {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ t t' :
  whne RedFlags.default Σ Γ t ->
  red1 Σ Γ t t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wh r.
  apply (whne_red1_indE
           RedFlags.default Σ Γ
           (whnf_red Σ Γ)); intros; cbn in *; try easy; eauto using whnf_red.
  - constructor.
    eapply OnOne2_All2; eauto.
  - constructor; auto.
    now apply whnf_red_refl_whne.
  - apply whnf_red_mkApps; eauto.
    1: constructor; apply All2_same; auto.
    eapply OnOne2_All2; eauto.
  - apply whnf_red_mkApps; eauto.
    + constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply All2_same; auto.
  - apply whnf_red_mkApps; eauto.
    + constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply All2_same; auto.
  - constructor; auto.
    * eapply OnOne2_All2; eauto.
    * eapply All2_same; intuition auto.
  - econstructor; auto. apply All2_same; auto.
    eapply All2_same; intuition auto.
  - destruct p; econstructor; eauto; simpl.
    * eapply All2_same; auto.
    * eapply All2_same; intuition auto.
  - destruct p;  econstructor; eauto; simpl.
    * eapply All2_same; reflexivity.
    * eapply OnOne2_All2; eauto.
      cbn. intros ? ? [? <-].
      intuition eauto; try reflexivity.
  - match goal with
    | h : red1 _ _ (tCase _ _ (mkApps (tCoFix _ _) _) _) _ |- _ => depelim h
    end.
    + solve_discr.
    + solve_discr.
    + congruence.
    + (* red_prim_op: its left side is an application of a constant, not a case *)
      match goal with x : mkApps (tConst _ _) ?l = tCase _ _ _ _ |- _ =>
        let l' := fresh "l" in remember l as l' eqn:Hl; clear Hl;
        destruct l' as [|? l' _] using MRList.rev_ind;
          [discriminate x|rewrite mkApps_app in x; discriminate x]
      end.
    + constructor; auto.
      * eapply OnOne2_All2; eauto.
      * eapply All2_same; intuition auto.
    + econstructor; auto. apply All2_same; auto.
      eapply All2_same; intuition auto.
    + destruct p; econstructor; eauto; simpl.
      * eapply All2_same; auto.
      * eapply All2_same; intuition auto.
    + destruct p; econstructor; eauto; simpl.
      * eapply All2_same; reflexivity.
      * eapply OnOne2_All2; eauto.
        cbn. intros ? ? [? <-].
        intuition eauto; try reflexivity.
  - (* Hprimapp_stuck: the step is inside an argument; the head stays *)
    rename c into c0, u into u0, decl into decl0, op into op0,
           ls into ls0, a into a0, rest into rest0.
    match goal with [ H : red1 _ _ (mkApps _ _) _ |- _ ] => rename H into hr0 end.
    match goal with [ H : whne _ _ _ a0 |- _ ] => rename H into hw0 end.
    assert (hle : #|map term_of_lit ls0 ++ a0 :: rest0| <= arity op0)
      by (rewrite length_app length_map /=; lia).
    assert (ha0 : lit_of_term a0 = None) by (eapply whne_not_lit; exact hw0).
    assert (hcf : prim_reduct Σ op0 (map term_of_lit ls0 ++ a0 :: rest0) = None)
      by (rewrite /prim_reduct /lits_of_args (split_lits_app ha0) //).
    eapply red1_mkApps_tConst_invE in hr0 as (args' & -> & ho); try eassumption.
    apply whnf_red_mkApps; [econstructor; eassumption|eapply OnOne2_All2; eauto].
  - (* Hprimapp_inert: a literal application cannot step *)
    exfalso.
    rename c into c0, u into u0, decl into decl0, op into op0, ls into ls0.
    match goal with [ H : red1 _ _ (mkApps _ _) _ |- _ ] => rename H into hr0 end.
    match goal with [ H : prim_reduct _ _ _ = None |- _ ] => rename H into hcf end.
    assert (hle : #|map term_of_lit ls0| <= arity op0)
      by (rewrite length_map; lia).
    eapply red1_mkApps_tConst_invE in hr0 as (args' & _ & ho); try eassumption.
    eapply OnOne2_map_term_of_lit; exact ho.
Qed.

(** Base [whnf_red1_inv] ([PCUICNormal.v:2223]). *)
Lemma whnf_red1_invE {cf:checker_flags} Σ {wfΣ : wfE Σ} Γ t t' :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wh r.
  destruct wh.
  - eapply whne_red1_invE; eauto.
  - depelim r; solve_discr.
  - depelim r; solve_discr; constructor; eauto using whnf_red.
  - depelim r; solve_discr; constructor; eauto using whnf_red.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_red_mkApps; eauto using whnf_red.
    eapply OnOne2_All2; eauto.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_red_mkApps; eauto using whnf_red.
    eapply OnOne2_All2; eauto.
  - apply red1_mkApps_tFix_inv in r.
    2: { unfold unfold_fix. destruct o as [[? [-> ?]]|];
         now unfold is_constructor; rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_red_mkApps; auto.
      2: eapply OnOne2_All2; eauto.
      constructor.
      apply All2_same; auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
  - apply red1_mkApps_tCoFix_inv in r.
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_red_mkApps; auto.
      2: eapply OnOne2_All2; eauto.
      constructor.
      apply All2_same; auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
    + apply whnf_red_mkApps.
      2: apply All2_same; auto.
      constructor.
      eapply OnOne2_All2; eauto.
      cbn.
      intros ? ? (?&[= -> -> ->]).
      auto.
  - depelim r; solve_discr; constructor; eauto.
    * constructor; eauto. eapply OnOne2_All2; eauto.
    * constructor; eauto. cbn. eapply All2_same; eauto.
    * constructor; eauto. cbn. eapply All2_same; eauto.
  - (* whnf_primapp_partial: the step is inside an argument; the head stays *)
    assert (hle : #|args| <= arity op) by lia.
    assert (hcf : prim_reduct Σ op args = None) by now apply prim_reduct_short.
    eapply red1_mkApps_tConst_invE in r as (args'&->&ho); try eassumption.
    apply whnf_red_mkApps; [ econstructor; eassumption | eapply OnOne2_All2; eauto ].
  - (* whnf_primapp_rigid: the step is inside an argument; the head stays *)
    assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
      by (rewrite length_app length_map /=; lia).
    assert (hcf : prim_reduct Σ op (map term_of_lit ls ++ a :: rest) = None)
      by (rewrite /prim_reduct /lits_of_args split_lits_app //).
    eapply red1_mkApps_tConst_invE in r as (args'&->&ho); try eassumption.
    apply whnf_red_mkApps; [ econstructor; eassumption | eapply OnOne2_All2; eauto ].
Qed.

(** Base [whnf_red_inv] ([PCUICNormal.v:2300]): the field [whnf_red_inv] of [U_facts] (row 13). *)
Lemma whnf_red_invE {cf:checker_flags} {Σ : global_env_ext} Γ t t' :
  wfE Σ ->
  whnf RedFlags.default Σ Γ t ->
  Σ ;;; Γ ⊢ t ⇝ t' ->
  whnf_red Σ Γ t t'.
Proof.
  intros wf wh [clΓ clt r].
  induction r using red_rect_n1.
  - apply whnf_red_refl; auto.
  - eapply whnf_red1_invE in X; eauto.
    + eapply whnf_red_transE; tea.
    + eapply whnf_presE; eauto.
Qed.
