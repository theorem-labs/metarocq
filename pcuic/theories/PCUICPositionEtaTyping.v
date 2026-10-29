(* Distributed under the terms of the MIT license. *)
(** * K3a: the semantic and typed lemmas about the η views of [PCUICPositionEta]

  Plan I7 revisions 13-15 (lanes/eta/plan.md §2). The η views themselves and their
  syntactic lemmas are in [PCUICPositionEta]; this file has what reads a context:

  - renaming ([eta_ren_urenaming], [eta_ren_body], rev 15 C3; [eta_rename_red], rev 15
    C3 RESTATED with two scoping premises, and its refutation in the unscoped form
    [eta_rename_red_unscoped_false]; [eta_rename_whnf], new, by induction on
    [whnf]/[whne]; the case and fix context commutations of rev 15 C6);
  - scoping ([zipp_eta_open], rev 15 C6);
  - the η context relation ([ws_cumul_ctx_pbE_eta_step], the Σ-level content of rev 15
    C4 [conv_stack_ctx_eta_eta_step], which is stated over [abstract_env_ext_rel] in
    [PCUICSafeConversionEtaK4]);
  - typing: the η companion ([eta_companion_welltypedE], rev 13), [wf_localE_focus_context]
    (rev 15 C6), and, over named hypotheses, [wf_localE_push_real] (rev 14/15 C8, conclusion
    RESTATED as squashed), [wf_localE_eta_step] (rev 14/15 C8), [eta_rename_typing] (rev 15 C6).

  The three typed lemmas that need E metatheory not yet on [frac/eta] are proved once,
  generically, in section [EtaTypingGen], over an abstract typing relation and the
  base-shaped facts they use. Section [EtaTypingE] instantiates it at [typingE]; the facts
  provable now ([typingE_wf_local], the [welltypedE] constructor, and [typingE_rename_P], the
  E copy of [PCUICRenameTyp.typing_rename_P], from [PCUICRenameTypEta.typing_rename_PE]) are
  discharged there, and the others are its named [Context] hypotheses:
  - [closed_context_conversionE] (row T0, the E copy of
    [PCUICContextConversionTyp.closed_context_conversion]);
  - [welltypedE_context] (rows T6 + T2a + T0: the E copy of
    [PCUICPositionEta.welltyped_context], which uses the inversions, validity and context
    conversion).
  Section [EtaTypingBase] instantiates the same generic section at base [typing], with every
  hypothesis discharged by a base lemma. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment EnvironmentTyping.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICSigmaCalculus
     PCUICOnFreeVars PCUICClosed PCUICRenameDef PCUICRenameConv PCUICOnFreeVarsConv
     PCUICReduction PCUICOnOne PCUICNormal PCUICPrimitive PCUICPrimitiveRed PCUICTyping
     PCUICWellScopedCumulativity PCUICTypingEta PCUICTypingEtaInd
     PCUICWellScopedCumulativityEta PCUICContextConversionEta PCUICClosedBodies.
From MetaRocq.PCUIC Require PCUICEtaC1b PCUICRenameTyp PCUICContextConversionTyp PCUICClosedTyp.
(* [typing_rename_PE], which proves [typingE_rename_P] (section EtaTypingE); qualified, nothing imported. *)
From MetaRocq.PCUIC Require PCUICRenameTypEta.

(* LAST, so that the η stack shadows any base stack name. *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

(* ===================================================================== *)
(* Renaming: the η renaming is a renaming of the structural context into  *)
(* the η context (rev 15 C3).                                              *)
(* ===================================================================== *)

Lemma no_Eta_arg_real se π : is_eta_frame se = false -> no_Eta_arg (se :: π) = no_Eta_arg π.
Proof. destruct se; first [discriminate | reflexivity]. Qed.

Lemma stack_context_cons se π : stack_context (se :: π) = stack_entry_context se ++ stack_context π.
Proof. reflexivity. Qed.

(* the target's variable [f i] has a body exactly when the source's [i] has one *)
Definition ren_body_pres (Γ Δ : context) (f : nat -> nat) :=
  forall n d, nth_error Γ n = Some d ->
    ∑ d', nth_error Δ (f n) = Some d' × (decl_body d' = None <-> decl_body d = None).

Lemma ren_body_pres_ext Γ Δ f g : f =1 g -> ren_body_pres Γ Δ f -> ren_body_pres Γ Δ g.
Proof. intros hfg h n d hn. rewrite -(hfg n). exact (h n d hn). Qed.

Lemma ren_body_pres_weaken1 Γ Δ f d0 :
  ren_body_pres Γ Δ f -> ren_body_pres Γ (Δ ,, d0) (rshiftk 1 ∘ f).
Proof. intros h n d hn. exact (h n d hn). Qed.

Lemma ren_body_pres_context Γ Δ Ξ f : ren_body_pres Γ Δ f ->
  ren_body_pres (Γ ,,, Ξ) (Δ ,,, rename_context f Ξ) (shiftn #|Ξ| f).
Proof.
  intros h n d hn. unfold shiftn.
  destruct (Nat.ltb n #|Ξ|) eqn:hcmp; [apply Nat.ltb_lt in hcmp as hlt | apply Nat.ltb_ge in hcmp as hge].
  - rewrite (nth_error_app_context_lt n Γ Ξ hlt) in hn.
    have hlt' : n < #|rename_context f Ξ| by rewrite rename_context_length.
    rewrite (nth_error_app_context_lt n Δ _ hlt').
    rewrite PCUICRenameTyp.nth_error_rename_context hn /=.
    eexists; split; [reflexivity|]. cbn. destruct (decl_body d); cbn; split; congruence.
  - rewrite (nth_error_app_context_ge n Γ Ξ hge) in hn.
    destruct (h _ _ hn) as [d' [hn' hb]].
    exists d'. split; [|exact hb].
    have hge' : #|rename_context f Ξ| <= #|Ξ| + f (n - #|Ξ|) by rewrite rename_context_length; lia.
    rewrite (nth_error_app_context_ge _ Δ _ hge') rename_context_length.
    replace (#|Ξ| + f (n - #|Ξ|) - #|Ξ|) with (f (n - #|Ξ|)) by lia.
    exact hn'.
Qed.

Lemma urenaming_weaken1 P Γ Δ f d0 :
  urenaming P Γ Δ f -> urenaming P Γ (Δ ,, d0) (rshiftk 1 ∘ f).
Proof.
  intros h i decl hP e.
  destruct (h i decl hP e) as [decl' [hn [ha [ht hb]]]].
  exists decl'. split; [exact hn|]. split; [exact ha|]. split.
  - etransitivity.
    { symmetry. exact (rename_compose (rshiftk 1) (f ∘ rshiftk (S i)) (decl_type decl)). }
    etransitivity; [exact (f_equal (rename (rshiftk 1)) ht)|].
    rewrite rename_rename_eta. apply rename_ext. intros x. reflexivity.
  - move: hb. destruct (decl_body decl) as [b|]; cbn; [|trivial].
    destruct (decl_body decl') as [b'|]; cbn; [|intros [=]].
    intros [= hb]. f_equal.
    etransitivity.
    { symmetry. exact (rename_compose (rshiftk 1) (f ∘ rshiftk (S i)) b). }
    etransitivity; [exact (f_equal (rename (rshiftk 1)) hb)|].
    rewrite rename_rename_eta. apply rename_ext. intros x. reflexivity.
Qed.

Lemma urenaming_id_ctx P Γ : urenaming P Γ Γ id.
Proof.
  intros i decl _ e. exists decl. split; [exact e|]. split; [reflexivity|]. split.
  - apply rename_ext. intros x. reflexivity.
  - destruct (decl_body decl); cbn; [|trivial]. f_equal.
    all: apply rename_ext; intros x; reflexivity.
Qed.

Lemma eta_ren_Eta_app_pw na A π : eta_ren (Eta_app na A :: π) 0 =1 rshiftk 1 ∘ eta_ren π 0.
Proof.
  intros n. change (eta_ren π 1 (S n) = S (eta_ren π 0 n)).
  exact (eq_trans (eta_ren_S π 0 (S n)) (shiftn_1_S _ n)).
Qed.

Lemma eta_ren_real_pw se π : is_eta_frame se = false ->
  eta_ren (se :: π) 0 =1 shiftn #|stack_entry_context se| (eta_ren π 0).
Proof.
  intros he n. rewrite eta_ren_real //.
  exact (eta_ren_shiftn π #|stack_entry_context se| 0 n).
Qed.

Lemma app_context_real Γ se π :
  Γ ,,, stack_context (se :: π) = (Γ ,,, stack_context π) ,,, stack_entry_context se.
Proof. rewrite stack_context_cons /app_context. now rewrite app_assoc. Qed.

Lemma app_context_eta_real Γ se π : is_eta_frame se = false ->
  Γ ,,, stack_context_eta (se :: π) =
  (Γ ,,, stack_context_eta π) ,,, rename_context (eta_ren π 0) (stack_entry_context se).
Proof.
  intros he. rewrite stack_context_eta_real // -(eta_rename_fold_context π 0) /app_context.
  now rewrite app_assoc.
Qed.

Lemma eta_ren_props Γ π : no_Eta_arg π ->
  urenaming xpredT (Γ ,,, stack_context π) (Γ ,,, stack_context_eta π) (eta_ren π 0) ×
  ren_body_pres (Γ ,,, stack_context π) (Γ ,,, stack_context_eta π) (eta_ren π 0).
Proof.
  induction π as [|se π IH]; intros hna.
  - split; [apply urenaming_id_ctx|]. intros n d hn. exists d. split; [exact hn|reflexivity].
  - destruct (is_eta_frame se) eqn:he.
    + destruct se; try discriminate he; cbn in hna; try discriminate hna.
      (* Eta_app *)
      destruct (IH hna) as [hu hb]. split.
      * apply (urenaming_ext xpredT xpredT _ _ (rshiftk 1 ∘ eta_ren π 0));
          [reflexivity | | exact (urenaming_weaken1 _ _ _ _ (vass na A) hu)].
        intros n. exact (eq_sym (eta_ren_Eta_app_pw na A π n)).
      * apply (ren_body_pres_ext _ _ (rshiftk 1 ∘ eta_ren π 0));
          [| exact (ren_body_pres_weaken1 _ _ _ (vass na A) hb)].
        intros n. exact (eq_sym (eta_ren_Eta_app_pw na A π n)).
    + rewrite no_Eta_arg_real // in hna.
      destruct (IH hna) as [hu hb].
      rewrite app_context_real app_context_eta_real //. split.
      * apply (urenaming_ext (shiftnP #|stack_entry_context se| xpredT) xpredT _ _
                 (shiftn #|stack_entry_context se| (eta_ren π 0)));
          [ | | exact (urenaming_context _ _ _ (stack_entry_context se) _ hu)].
        { intros n. apply shiftnP_xpredT. }
        { intros n. exact (eq_sym (eta_ren_real_pw se π he n)). }
      * apply (ren_body_pres_ext _ _ (shiftn #|stack_entry_context se| (eta_ren π 0)));
          [ | exact (ren_body_pres_context _ _ (stack_entry_context se) _ hb)].
        intros n. exact (eq_sym (eta_ren_real_pw se π he n)).
Qed.

(* rev 15 (C3): source the structural context, target the η context *)
Lemma eta_ren_urenaming Γ π : no_Eta_arg π ->
  urenaming xpredT (Γ ,,, stack_context π) (Γ ,,, stack_context_eta π) (eta_ren π 0).
Proof. intros h. exact (eta_ren_props Γ π h).1. Qed.

(* rev 15 (C3): the body-preserving fact eta_rename_whnf needs *)
Lemma eta_ren_body Γ π n d : no_Eta_arg π ->
  nth_error (Γ ,,, stack_context π) n = Some d ->
  ∑ d', nth_error (Γ ,,, stack_context_eta π) (eta_ren π 0 n) = Some d' ×
        (decl_body d' = None <-> decl_body d = None).
Proof. intros h. exact ((eta_ren_props Γ π h).2 n d). Qed.

Lemma eta_ren_scope Γ π i : no_Eta_arg π ->
  i < #|Γ ,,, stack_context π| -> eta_ren π 0 i < #|Γ ,,, stack_context_eta π|.
Proof.
  intros hna hi.
  destruct (nth_error (Γ ,,, stack_context π) i) as [d|] eqn:e.
  - destruct (eta_ren_body Γ π i d hna e) as [d' [hn _]]. exact (nth_error_Some_length hn).
  - apply nth_error_None in e. lia.
Qed.

Lemma eta_rename_open Γ π x : no_Eta_arg π ->
  is_open_term (Γ ,,, stack_context π) x ->
  is_open_term (Γ ,,, stack_context_eta π) (eta_rename π 0 x).
Proof.
  intros hna hx. rewrite eta_rename_rename on_free_vars_rename.
  eapply on_free_vars_impl; [|exact hx].
  intros i. rewrite /shiftnP /= !orb_false_r => /Nat.ltb_lt hi.
  apply/Nat.ltb_lt. exact (eta_ren_scope Γ π i hna hi).
Qed.

(* rev 15 (C3), RESTATED twice (lane lead, 2026-10-29): the two scoping premises are new
   (without them the statement is false: [eta_rename_red_unscoped_false] below), and
   [wf Σ] is replaced by [ClosedBodies Σ], which [wfE_ClosedBodies] supplies inside the E
   checker (it holds only [∥ wf_extE Σ ∥], and wfE does not imply wf). *)
Lemma eta_rename_red {cf} (Σ : global_env_ext) Γ π t u : ClosedBodies Σ -> no_Eta_arg π ->
  is_closed_context (Γ ,,, stack_context π) -> is_open_term (Γ ,,, stack_context π) t ->
  red Σ (Γ ,,, stack_context π) t u ->
  red Σ (Γ ,,, stack_context_eta π) (eta_rename π 0 t) (eta_rename π 0 u).
Proof.
  intros cbΣ hna hΓ ht hr.
  rewrite !eta_rename_rename.
  eapply (red_rename_cb (shiftnP #|Γ ,,, stack_context π| xpred0)); [exact cbΣ| | | exact ht | exact hr].
  - eapply urenaming_impl; [|exact (eta_ren_urenaming Γ π hna)]. intros i _. reflexivity.
  - rewrite on_free_vars_ctx_on_ctx_free_vars. exact hΓ.
Qed.

(* --- The counterexample to the unscoped form (lane lead's ruling: a checked lemma) --- *)

Definition ru_na : aname := mkBindAnn nAnon Relevant.
Definition ru_ci : case_info :=
  {| ci_ind := {| inductive_mind := (MPfile [], "I"); inductive_ind := 0 |};
     ci_npar := 0; ci_relevance := Relevant; ci_cofix_nondep := true |}.
(* a case whose predicate context mentions a variable outside it: ill-scoped *)
Definition ru_pred (r : term) : predicate term :=
  {| pparams := []; puinst := []; pcontext := [vdef ru_na (tRel 5) (tSort sProp)]; preturn := r |}.
Definition ru_case (r : term) : term := tCase ru_ci (ru_pred r) (tSort sProp) [].
Definition ru_ctx : context := [vass ru_na (tSort sProp)].

Lemma ru_red1_inv {cf} (Σ : global_env_ext) r y :
  r = tRel 0 \/ r = tRel 6 -> red1 Σ ru_ctx (ru_case r) y -> r = tRel 0 /\ y = ru_case (tRel 6).
Proof.
  intros hr h. unfold ru_case, ru_pred in h.
  depelim h; solve_discr.
  all: cbn in *.
  all: try match goal with o : OnOne2 _ [] _ |- _ => solve [depelim o] end.
  all: try match goal with h : red1 _ _ (tSort _) _ |- _ => solve [depelim h; solve_discr] end.
  all: destruct hr as [-> | ->].
  all: match goal with h : red1 _ _ (tRel _) _ |- _ => depelim h; solve_discr end.
  all: cbn in *; try discriminate.
  all: match goal with e : Some (Some _) = Some (Some _) |- _ => noconf e end.
  all: split; reflexivity.
Qed.

Lemma ru_red_inv {cf} (Σ : global_env_ext) x y : red Σ ru_ctx x y ->
  (x = ru_case (tRel 0) \/ x = ru_case (tRel 6)) -> (y = ru_case (tRel 0) \/ y = ru_case (tRel 6)).
Proof.
  induction 1 as [x y r|x|x y z r1 IH1 r2 IH2]; intros hx.
  - destruct hx as [-> | ->].
    + right. exact (proj2 (ru_red1_inv Σ (tRel 0) y (or_introl eq_refl) r)).
    + destruct (ru_red1_inv Σ (tRel 6) y (or_intror eq_refl) r) as [h _]. discriminate h.
  - exact hx.
  - exact (IH2 (IH1 hx)).
Qed.

(* rev 15 C3's [eta_rename_red] without the scoping premises is FALSE.
   π = [Eta_app na Prop] (the renaming is [lift 1 0]), Γ = [], and the ill-scoped
   [tCase] whose predicate context is [vdef x (tRel 5) Prop]: the source steps
   [preturn := tRel 0] to [tRel 6] by [case_red_return] and [red_rel]; renaming does
   not touch the predicate context, so the target must step [tRel 0] to [tRel 7],
   which no reduction reaches. *)
Lemma eta_rename_red_unscoped_false {cf} :
  (forall (Σ : global_env_ext) Γ π t u, wf Σ -> no_Eta_arg π ->
     red Σ (Γ ,,, stack_context π) t u ->
     red Σ (Γ ,,, stack_context_eta π) (eta_rename π 0 t) (eta_rename π 0 u)) -> False.
Proof.
  intros H.
  set (Σ0 := empty_ext empty_global_env).
  set (π0 := [Eta_app ru_na (tSort sProp)]).
  have hsrc : red Σ0 ([] ,,, stack_context π0) (ru_case (tRel 0)) (ru_case (tRel 6)).
  { apply rt_step.
    change (ru_case (tRel 6)) with
      (tCase ru_ci (set_preturn (ru_pred (tRel 0)) (lift0 1 (tRel 5))) (tSort sProp) []).
    apply case_red_return. eapply red_rel. reflexivity. }
  have htgt : red Σ0 ru_ctx (ru_case (tRel 0)) (ru_case (tRel 7)) :=
    H Σ0 [] π0 _ _ (@PCUICEtaC1b.wf_empty_global_env cf) eq_refl hsrc.
  destruct (ru_red_inv Σ0 _ _ htgt (or_introl eq_refl)) as [e|e];
    cbv [ru_case ru_pred] in e; congruence.
Qed.

(* --- whnf is preserved by a renaming that keeps assumptions assumptions --------- *)

Lemma rename_term_of_lit f l : rename f (term_of_lit l) = term_of_lit l.
Proof. destruct l; reflexivity. Qed.

Lemma map_rename_term_of_lit f ls : map (rename f) (map term_of_lit ls) = map term_of_lit ls.
Proof. rewrite map_map. apply map_ext. intros l. apply rename_term_of_lit. Qed.

Lemma lit_of_term_rename f a : lit_of_term (rename f a) = lit_of_term a.
Proof.
  destruct a; try reflexivity.
  destruct prim as [tag model]. destruct model; reflexivity.
Qed.

Section WhnfRename.
  Context (flags : RedFlags.t) (Σ : global_env).
  Context (Γ Δ : context) (f : nat -> nat).
  Context (hf : forall i, option_map decl_body (nth_error Γ i) = Some None ->
                          option_map decl_body (nth_error Δ (f i)) = Some None).

  Lemma whne_rename t : whne flags Σ Γ t -> whne flags Σ Δ (rename f t).
  Proof using hf.
    induction 1; cbn [rename]; rewrite ?rename_mkApps; cbn [rename].
    all: try solve [econstructor; eauto].
    - (* fixapp *)
      eapply whne_fixapp.
      + match goal with h : nth_error mfix idx = Some _ |- _ => rewrite nth_error_map h end.
        reflexivity.
      + cbn. match goal with h : nth_error args _ = Some _ |- _ => rewrite nth_error_map h end.
        reflexivity.
      + exact IHX.
    - (* primapp_stuck *)
      rewrite map_app map_rename_term_of_lit. cbn [map].
      eapply whne_primapp_stuck; eauto. now rewrite length_map.
    - (* primapp_inert *)
      rewrite map_rename_term_of_lit.
      eapply whne_primapp_inert; eauto.
  Qed.

  Lemma whnf_rename t : whnf flags Σ Γ t -> whnf flags Σ Δ (rename f t).
  Proof using hf.
    induction 1; cbn [rename]; rewrite ?rename_mkApps; cbn [rename].
    1: (constructor; now apply whne_rename).
    all: try solve [ eapply whnf_sort | eapply whnf_prod | eapply whnf_lam | eapply whnf_cstrapp
                   | eapply whnf_indapp | eapply whnf_cofixapp | eapply whnf_prim ].
    - (* fixapp *)
      apply whnf_fixapp.
      match goal with o : _ \/ _ |- _ => destruct o as [[d [hd hn]]|hn] end.
      + left. exists (map_def (rename f) (rename (shiftn #|mfix| f)) d). split.
        * rewrite nth_error_map hd. reflexivity.
        * cbn. rewrite nth_error_map hn. reflexivity.
      + right. rewrite nth_error_map hn. reflexivity.
    - (* primapp_partial *)
      eapply whnf_primapp_partial; eauto. now rewrite length_map.
    - (* primapp_rigid *)
      rewrite map_app map_rename_term_of_lit. cbn [map].
      eapply whnf_primapp_rigid; eauto.
      + now rewrite length_map.
      + now rewrite lit_of_term_rename.
  Qed.
End WhnfRename.

(* rev 15 (C3): NEW, by induction on whnf/whne; the whne_rel case uses eta_ren_body *)
Lemma eta_rename_whnf flags Σ Γ π t : no_Eta_arg π ->
  whnf flags Σ (Γ ,,, stack_context π) t ->
  whnf flags Σ (Γ ,,, stack_context_eta π) (eta_rename π 0 t).
Proof.
  intros hna h. rewrite eta_rename_rename. eapply whnf_rename; [|exact h].
  intros i hi. destruct (nth_error (Γ ,,, stack_context π) i) as [d|] eqn:hn; [|discriminate hi].
  destruct (eta_ren_body Γ π i d hna hn) as [d' [hn' hb]].
  rewrite hn'. cbn in hi |- *. f_equal. apply hb. now injection hi.
Qed.

(* rev 15 (C6): case and fix binders, beside eta_rename_tLambda *)
Lemma eta_rename_inst_case_predicate_context π d p :
  on_free_vars_ctx (closedP #|pparams p| xpredT) (pcontext p) ->
  inst_case_predicate_context (rename_predicate (eta_ren π d) p)
  = rename_context (eta_ren π d) (inst_case_predicate_context p).
Proof. apply inst_case_predicate_context_rename. Qed.

Lemma eta_rename_inst_case_branch_context π d p br :
  on_free_vars_ctx (closedP #|pparams p| xpredT) (bcontext br) ->
  inst_case_branch_context (rename_predicate (eta_ren π d) p) (rename_branch (eta_ren π d) br)
  = rename_context (eta_ren π d) (inst_case_branch_context p br).
Proof. apply inst_case_branch_context_rename. Qed.

Lemma eta_rename_fix_context π d mfix :
  fix_context (map (map_def (rename (eta_ren π d)) (rename (shiftn #|mfix| (eta_ren π d)))) mfix)
  = rename_context (eta_ren π d) (fix_context mfix).
Proof. apply rename_fix_context. Qed.

(* ===================================================================== *)
(* The η run at the head of a stack.                                       *)
(* ===================================================================== *)

Lemma stack_context_eta_drop_eta_run π :
  ∑ Δ, #|Δ| = eta_run π × stack_context_eta π = stack_context_eta (drop_eta_run π) ,,, Δ.
Proof.
  induction π as [|se π IH]; [exists []; split; reflexivity|].
  destruct se; try (exists []; split; reflexivity).
  destruct IH as [Δ [hl he]]. exists (vass na A :: Δ). split; [cbn; now rewrite hl|].
  cbn [stack_context_eta stack_entry_context_eta drop_eta_run]. rewrite he. reflexivity.
Qed.

Lemma eta_ren_run π d n u a σ : drop_eta_run π = Eta_arg u a :: σ -> d <= n ->
  eta_ren π d n = eta_run π + n.
Proof.
  induction π as [|se π IH] in d, n |- *; intros h hd; [cbn in h; discriminate h|].
  destruct se; cbn [drop_eta_run] in h; try discriminate h.
  - (* Eta_app *)
    change (eta_ren π (S d) (lift_renaming 1 d n) = S (eta_run π + n)).
    unfold lift_renaming. destruct (Nat.leb_spec d n); [|lia]. cbv beta iota.
    rewrite (IH (S d) (1 + n) h); lia.
  - (* Eta_arg *) reflexivity.
Qed.

(* the virtual side's facts from virt_ok (as virt_ok_focus, plus the stack shape) *)
Lemma virt_ok_virtual t π : virt_ok t π = true -> no_Eta_arg π = false ->
  ∑ k u a σ, [× t = tRel k, decompose_stack π = ([], π), drop_eta_run π = Eta_arg u a :: σ &
               k < eta_run (decompose_stack σ).2].
Proof.
  unfold virt_ok. intros hv hna. rewrite hna in hv. cbn [orb] in hv.
  destruct (decompose_stack π) as [args ρ] eqn:hd.
  destruct t; cbn in hv; try discriminate hv.
  destruct (drop_eta_run ρ) as [|se σ] eqn:hdr; cbn in hv; try discriminate hv.
  destruct se; cbn in hv; try discriminate hv.
  move/andP: hv => [hnil hlt].
  destruct args; [|discriminate hnil].
  apply Nat.ltb_lt in hlt.
  have hπ := decompose_stack_eq _ _ _ hd. cbn in hπ. subst ρ.
  do 4 eexists. split; eauto.
Qed.

(* rev 15 (C6): G5's η-scoping lemma *)
Lemma zipp_eta_open Γ t π :
  virt_ok t π = true ->
  is_open_term Γ (zipc t π) ->
  is_closed_context (Γ ,,, stack_context_eta π) ->
  is_open_term (Γ ,,, stack_context_eta π) (zipp_eta t π).
Proof.
  intros hv ho _.
  destruct (no_Eta_arg π) eqn:hna.
  - (* real side *)
    destruct (decompose_stack π) as [args ρ] eqn:hd.
    have hπ := decompose_stack_eq _ _ _ hd. subst π.
    have hρ : no_Eta_arg ρ by rewrite no_Eta_arg_appstack in hna.
    have hrel : forall x, is_open_term (Γ ,,, stack_context ρ) x ->
                  is_open_term (Γ ,,, stack_context_eta ρ) (eta_rename ρ 0 x).
    { intros x hx. now apply eta_rename_open. }
    rewrite zipc_appstack in ho.
    have hcl : closedn (#|stack_context ρ| + #|Γ|) (mkApps t args).
    { have hz := closedn_zip #|Γ| (mkApps t args) ρ hρ.
      have e1 := on_free_vars_ext (closedP #|Γ| xpredT) (shiftnP #|Γ| xpred0)
                   (zipc (mkApps t args) ρ) (closedP_shiftnP #|Γ|).
      have e : closedn #|Γ| (zipc (mkApps t args) ρ).
      { rewrite closedP_on_free_vars e1. exact ho. }
      rewrite e in hz. symmetry in hz. move/andP: hz => [_ h]. exact h. }
    rewrite closedn_mkApps in hcl. move/andP: hcl => [hct hcargs].
    have hopen : forall x, closedn (#|stack_context ρ| + #|Γ|) x ->
                   is_open_term (Γ ,,, stack_context ρ) x.
    { intros x hx. apply closedn_on_free_vars. now rewrite app_context_length. }
    unfold zipp_eta. rewrite (decompose_stack_eta_eq _ _ _ hd) /=.
    rewrite eta_rename_appstack stack_context_eta_appstack.
    rewrite on_free_vars_mkApps. apply/andP; split.
    + apply hrel, hopen, hct.
    + rewrite forallb_app. apply/andP; split.
      * rewrite forallb_map. eapply forallb_impl; [|exact hcargs].
        intros x _ hx. apply hrel, hopen, hx.
      * unfold eta_virtuals. rewrite forallb_map. apply forallb_forall.
        intros k hk. apply in_rev, in_seq in hk.
        cbn. rewrite /shiftnP orb_false_r. apply/Nat.ltb_lt.
        destruct (stack_context_eta_drop_eta_run ρ) as [Δ [hl he]].
        rewrite app_context_length he app_context_length. lia.
  - (* virtual side *)
    destruct (virt_ok_virtual t π hv hna) as (k & u & a & σ & [-> hd hdr hk]).
    unfold zipp_eta. rewrite (decompose_stack_eta_eq _ _ _ hd) /=.
    destruct (stack_context_eta_drop_eta_run π) as [Δ [hl he]].
    rewrite hdr in he.
    destruct (decompose_stack σ) as [args' σ'] eqn:hdσ. cbn [snd] in hk.
    have hσ := decompose_stack_eq _ _ _ hdσ. subst σ.
    destruct (stack_context_eta_drop_eta_run σ') as [Δ' [hl' he']].
    have hlen : #|Γ ,,, stack_context_eta π| = #|Γ| + #|Δ| + #|Δ'| + #|stack_context_eta (drop_eta_run σ')|.
    { rewrite app_context_length he app_context_length.
      cbn [stack_context_eta stack_entry_context_eta app].
      rewrite stack_context_eta_appstack he' app_context_length. lia. }
    rewrite on_free_vars_mkApps. apply/andP; split.
    + rewrite eta_rename_rename. cbn [rename on_free_vars].
      rewrite (eta_ren_run π 0 k u a (appstack args' σ') hdr) //; [lia|].
      rewrite /shiftnP orb_false_r. apply/Nat.ltb_lt. rewrite hlen. lia.
    + unfold eta_virtuals. rewrite forallb_map. apply forallb_forall.
      intros i hi. apply in_rev, in_seq in hi.
      cbn. rewrite /shiftnP orb_false_r. apply/Nat.ltb_lt. rewrite hlen. lia.
Qed.

(* ===================================================================== *)
(* The η context relation: the η step adds the same declaration on both   *)
(* sides (rev 14 NB1, rev 15 C4).                                          *)
(* ===================================================================== *)

Lemma ws_cumul_ctx_pbE_closed_left {cf} pb (Σ : global_env_ext) Δ Δ' :
  ws_cumul_ctx_pbE pb Σ Δ Δ' -> is_closed_context Δ.
Proof.
  induction 1 as [|Δ Δ' d d' h IH hd]; [reflexivity|].
  rewrite on_free_vars_ctx_snoc IH /=. unfold ws_cumul_declsE in hd.
  destruct hd as [na na' A A' hna hA|na na' b A b' A' hna hb hA];
    rewrite /on_free_vars_decl /test_decl /=.
  - exact (wsE_left hA).
  - rewrite (wsE_left hb) (wsE_left hA). reflexivity.
Qed.

(* The Σ-level content of rev 15 C4 [conv_stack_ctx_eta_eta_step]. *)
Lemma ws_cumul_ctx_pbE_eta_step {cf} (Σ : global_env_ext) Γ na A π_i args ρ_j :
  is_open_term (Γ ,,, stack_context_eta π_i) (eta_rename π_i 0 A) ->
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta π_i) (Γ ,,, stack_context_eta (appstack args ρ_j)) ->
  ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta (Lambda_bd na A :: π_i))
    (Γ ,,, stack_context_eta (appstack args (Eta_app na (eta_rename π_i 0 A) :: ρ_j))).
Proof.
  intros hA hx.
  rewrite stack_context_eta_eta_step_lambda stack_context_eta_eta_step_other.
  rewrite stack_context_eta_appstack in hx.
  constructor; [exact hx|]. unfold ws_cumul_declsE. constructor; [reflexivity|].
  exact {| wsE_ctx := ws_cumul_ctx_pbE_closed_left _ _ _ _ hx; wsE_left := hA; wsE_right := hA;
           wsE_join := JoinE_refl Σ _ Conv _ |}.
Qed.

(* ===================================================================== *)
(* Typing, part 1: what holds over typingE with no hypothesis.             *)
(* ===================================================================== *)

(* rev 13 (B2): the η companion, the one well-typedness claim the η view makes:
   the k-th binder of the run is the vass of an Eta_app. *)
Lemma eta_companion_welltypedE {cf} (Σ : global_env_ext) Γ ρ k :
  k < eta_run ρ -> wf_localE Σ (Γ ,,, stack_context_eta ρ) ->
  welltypedE Σ (Γ ,,, stack_context_eta ρ) (tRel k).
Proof.
  intros hk hwf.
  destruct (stack_context_eta_run_vass ρ k hk) as [decl [hn _]].
  econstructor. eapply typeE_Rel; [exact hwf|].
  rewrite (nth_error_app_context_lt k Γ _ (nth_error_Some_length hn)). exact hn.
Qed.

(* rev 15 (C6): G1's suffix fact, on the virtual side *)
Lemma wf_localE_focus_context {cf} (Σ : global_env_ext) Γ t π :
  virt_ok t π = true -> no_Eta_arg π = false ->
  wf_localE Σ (Γ ,,, stack_context_eta π) -> wf_localE Σ (Γ ,,, focus_context π).
Proof.
  intros hv hna hwf.
  destruct (virt_ok_virtual t π hv hna) as (k & u & a & σ & [_ hd hdr _]).
  unfold focus_context. rewrite hd /= hdr /=.
  destruct (stack_context_eta_drop_eta_run π) as [Δ [_ he]].
  rewrite he hdr app_context_assoc in hwf.
  exact (wf_localE_app_l _ _ _ hwf).
Qed.

(* ===================================================================== *)
(* Typing, part 2: the lemmas that need E metatheory not yet on frac/eta, *)
(* proved once over an abstract typing relation and the base-shaped facts *)
(* they use.                                                               *)
(* ===================================================================== *)

Section EtaTypingGen.
  (* the typing relation, its well-typedness predicate, its context relation and the
     environment well-formedness its metatheory assumes *)
  Context (TY : global_env_ext -> context -> term -> term -> Type).
  Context (WT : global_env_ext -> context -> term -> Prop).
  Context (CTX : global_env_ext -> context -> context -> Type).
  Context (WFΣ : global_env_ext -> Type).

  Local Notation wfl Σ Γ := (All_local_env (lift_typing1 (TY Σ)) Γ).

  (* base [PCUICTyping.typing_wf_local] *)
  Context (TY_wf_local : forall Σ Γ t T, TY Σ Γ t T -> wfl Σ Γ).
  (* the well-typedness predicate, inverted into a squashed derivation *)
  Context (WT_inv : forall Σ Γ t, WT Σ Γ t -> ∥ ∑ T, TY Σ Γ t T ∥).
  (* base [PCUICRenameTyp.typing_rename_P] *)
  Context (TY_rename_P : forall P Σ Γ Δ f t A, WFΣ Σ ->
    wfl Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f -> TY Σ Γ t A -> TY Σ Δ (rename f t) (rename f A)).
  (* base [PCUICContextConversionTyp.closed_context_conversion] *)
  Context (TY_closed_context_conversion : forall Σ, WFΣ Σ -> forall Γ t T Γ',
    TY Σ Γ t T -> wfl Σ Γ' -> CTX Σ Γ Γ' -> TY Σ Γ' t T).
  (* base [PCUICPositionEta.welltyped_context] *)
  Context (WT_context : forall Σ, WFΣ Σ -> forall Γ t, no_Eta_arg (snd t) ->
    WT Σ Γ (zip t) -> WT Σ (Γ ,,, stack_context (snd t)) (fst t)).

  (* a well-formed context extension is renamed into a well-formed one *)
  Lemma wfl_rename_app Σ (wfΣ : WFΣ Σ) Γs Γt f Ξ :
    urenaming xpredT Γs Γt f -> wfl Σ Γt -> wfl Σ (Γs ,,, Ξ) ->
    wfl Σ (Γt ,,, rename_context f Ξ).
  Proof using TY_rename_P.
    intros hf hΓt hΞ.
    apply All_local_env_app_inv in hΞ as [_ hΞ].
    induction hΞ as [|Δ decl IH hd] using All_local_rel_ind1; [exact hΓt|].
    rewrite rename_context_snoc. apply All_local_env_snoc; [exact IH|].
    eapply lift_typing_map with (j := j_decl _) => //.
    eapply lift_typing_impl; [exact hd|].
    intros t T h. eapply (TY_rename_P xpredT); [exact wfΣ| split; [exact IH|] | exact h].
    apply (urenaming_ext (shiftnP #|Δ| xpredT) (shiftnP #|Γs ,,, Δ| xpredT) _ _ (shiftn #|Δ| f));
      [ | reflexivity | exact (urenaming_context _ _ _ Δ _ hf)].
    intros i. rewrite (shiftnP_xpredT #|Δ| i) (shiftnP_xpredT #|Γs ,,, Δ| i). reflexivity.
  Qed.

  Lemma wf_local_push_real_gen Σ (wfΣ : WFΣ Σ) Γ t se π :
    is_eta_frame se = false -> no_Eta_arg π ->
    WT Σ Γ (zipc t (se :: π)) -> wfl Σ (Γ ,,, stack_context_eta π) ->
    ∥ wfl Σ (Γ ,,, stack_context_eta (se :: π)) ∥.
  Proof using TY_wf_local WT_inv TY_rename_P WT_context.
    intros hse hna hwt hwf.
    have hna' : no_Eta_arg (se :: π) by rewrite no_Eta_arg_real.
    have h1 := WT_context Σ wfΣ Γ (t, se :: π) hna' hwt. cbn [fst snd] in h1.
    destruct (WT_inv _ _ _ h1) as [[T hT]].
    have hctx := TY_wf_local _ _ _ _ hT.
    rewrite app_context_real in hctx.
    rewrite app_context_eta_real //.
    constructor. exact (wfl_rename_app Σ wfΣ _ _ _ _ (eta_ren_urenaming Γ π hna) hwf hctx).
  Qed.

  Lemma wf_local_eta_step_gen Σ (wfΣ : WFΣ Σ) Γ na A π_i args ρ_j :
    wfl Σ (Γ ,,, stack_context_eta (Lambda_bd na A :: π_i)) ->
    CTX Σ (Γ ,,, stack_context_eta π_i) (Γ ,,, stack_context_eta ρ_j) ->
    wfl Σ (Γ ,,, stack_context_eta ρ_j) ->
    wfl Σ (Γ ,,, stack_context_eta (appstack args (Eta_app na (eta_rename π_i 0 A) :: ρ_j))).
  Proof using TY_closed_context_conversion.
    intros h1 hx h3.
    rewrite stack_context_eta_eta_step_lambda in h1.
    rewrite stack_context_eta_eta_step_other.
    apply All_local_env_tip in h1 as [_ hA].
    apply All_local_env_snoc; [exact h3|].
    eapply lift_typing_impl; [exact hA|].
    intros t T h. exact (TY_closed_context_conversion Σ wfΣ _ t T _ h h3 hx).
  Qed.

  Lemma eta_rename_typing_gen Σ (wfΣ : WFΣ Σ) Γ π t T : no_Eta_arg π ->
    wfl Σ (Γ ,,, stack_context_eta π) ->
    TY Σ (Γ ,,, stack_context π) t T ->
    TY Σ (Γ ,,, stack_context_eta π) (eta_rename π 0 t) (eta_rename π 0 T).
  Proof using TY_rename_P.
    intros hna hwf ht. rewrite !eta_rename_rename.
    eapply (TY_rename_P xpredT); [exact wfΣ| split; [exact hwf|] | exact ht].
    apply (urenaming_ext xpredT (shiftnP #|Γ ,,, stack_context π| xpredT) _ _ (eta_ren π 0));
      [ | reflexivity | exact (eta_ren_urenaming Γ π hna)].
    intros i. exact (eq_sym (shiftnP_xpredT _ i)).
  Qed.
End EtaTypingGen.

(* ===================================================================== *)
(* Typing, part 3: the instantiation at typingE. Its named hypotheses are  *)
(* the E metatheory rows not yet on frac/eta.                              *)
(* ===================================================================== *)

Lemma welltypedE_inv {cf} Σ Γ t : welltypedE Σ Γ t -> ∥ ∑ T, Σ ;;; Γ |-E t : T ∥.
Proof. intros [T h]. constructor. exists T. exact h. Qed.

Section EtaTypingE.
  Context {cf : checker_flags}.

  (* PROVED (was a named hypothesis, row T0; EtaIntegrate9, 2026-10-29): the E copy of base
     [PCUICRenameTyp.typing_rename_P], same statement as the hypothesis it replaces. It is the
     exact twin [PCUICRenameTypEta.typing_rename_PE], whose [renamingE (shiftnP #|Γ| P) Σ Γ Δ f]
     unfolds to [wf_localE Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f] (EtaHypProve's
     [typingE_rename_P_proved], PCUICTypingEtaHypsProved). *)
  Lemma typingE_rename_P : forall P (Σ : global_env_ext) Γ Δ f t A, wfE Σ.1 ->
    wf_localE Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f ->
    Σ ;;; Γ |-E t : A -> Σ ;;; Δ |-E rename f t : rename f A.
  Proof.
    intros P Σ Γ Δ f t A wfΣ hr h. exact (PCUICRenameTypEta.typing_rename_PE (wfΣ := wfΣ) hr h).
  Qed.
  (* NAMED HYPOTHESIS, row T0: the E copy of base
     [PCUICContextConversionTyp.closed_context_conversion].
     Satisfying instance (base typing): [closed_context_conversion_inst].
     Not a known-false form: typed (typingE derivation, wf_localE target) and the context
     relation is the scoped ws_cumul_ctx_pbE of A8 (PCUICContextConversionEta), whose term
     version is already proved stable under context conversion there
     ([ws_cumul_pbE_ws_cumul_ctx]); no fix/cofix witness. *)
  Context (closed_context_conversionE : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |-E t : T -> wf_localE Σ Γ' -> ws_cumul_ctx_pbE Conv Σ Γ Γ' -> Σ ;;; Γ' |-E t : T).
  (* NAMED HYPOTHESIS, rows T6 (E inversions) + T2a (E validity) + T0 (E context
     conversion): the E copy of base [PCUICPositionEta.welltyped_context].
     Satisfying instance (base typing): [welltyped_context_inst].
     Not a known-false form: typed in and out (welltypedE of the whole term gives
     welltypedE of the focus under the frames' binders); it reads no conversion witness and
     has no closed-only premise. *)
  Context (welltypedE_context : forall (Σ : global_env_ext), wfE Σ.1 -> forall Γ t,
    no_Eta_arg (snd t) -> welltypedE Σ Γ (zip t) -> welltypedE Σ (Γ ,,, stack_context (snd t)) (fst t)).

  (* rev 14/15 C8, RESTATED (lane lead, 2026-10-29): the conclusion is squashed (the
     premise welltypedE is a Prop, the conclusion wf_localE a Type), and the environment
     premise is wfE (the E checker holds only ∥ wf_extE Σ ∥). *)
  Lemma wf_localE_push_real (Σ : global_env_ext) {wfΣ : wfE Σ.1} Γ t se π :
    is_eta_frame se = false -> no_Eta_arg π ->
    welltypedE Σ Γ (zipc t (se :: π)) -> wf_localE Σ (Γ ,,, stack_context_eta π) ->
    ∥ wf_localE Σ (Γ ,,, stack_context_eta (se :: π)) ∥.
  Proof using welltypedE_context.
    exact (wf_local_push_real_gen typingE welltypedE (fun Σ => wfE Σ.1)
             (fun Σ Γ t T h => typingE_wf_local h) welltypedE_inv typingE_rename_P
             welltypedE_context Σ wfΣ Γ t se π).
  Qed.

  (* rev 14/15 C8, RESTATED: wfE instead of wf; ws_cumul_ctx_pbE has no FInst argument
     in this tree. The pushed declaration is the λ side's, moved across hx. *)
  Lemma wf_localE_eta_step (Σ : global_env_ext) {wfΣ : wfE Σ.1} Γ na A π_i args ρ_j :
    wf_localE Σ (Γ ,,, stack_context_eta (Lambda_bd na A :: π_i)) ->
    ws_cumul_ctx_pbE Conv Σ (Γ ,,, stack_context_eta π_i) (Γ ,,, stack_context_eta ρ_j) ->
    wf_localE Σ (Γ ,,, stack_context_eta ρ_j) ->
    wf_localE Σ (Γ ,,, stack_context_eta (appstack args (Eta_app na (eta_rename π_i 0 A) :: ρ_j))).
  Proof using closed_context_conversionE.
    exact (wf_local_eta_step_gen typingE (fun Σ Γ Γ' => ws_cumul_ctx_pbE Conv Σ Γ Γ')
             (fun Σ => wfE Σ.1) closed_context_conversionE Σ wfΣ Γ na A π_i args ρ_j).
  Qed.

  (* rev 15 C6, RESTATED: wfE instead of wf. The E copy of typing_rename_prop (row T0)
     with eta_ren_urenaming. *)
  Lemma eta_rename_typing (Σ : global_env_ext) {wfΣ : wfE Σ.1} Γ π t T : no_Eta_arg π ->
    wf_localE Σ (Γ ,,, stack_context_eta π) ->
    Σ ;;; Γ ,,, stack_context π |-E t : T ->
    Σ ;;; Γ ,,, stack_context_eta π |-E eta_rename π 0 t : eta_rename π 0 T.
  Proof using Type.
    exact (eta_rename_typing_gen typingE (fun Σ => wfE Σ.1) typingE_rename_P Σ wfΣ Γ π t T).
  Qed.
End EtaTypingE.

(* ===================================================================== *)
(* Typing, part 4: the instantiation at BASE typing, every hypothesis of   *)
(* [EtaTypingGen] discharged by a base lemma.                              *)
(*                                                                         *)
(* (1) This base instance shows that the hypotheses of [EtaTypingGen] are  *)
(*     jointly consistent and that its three lemmas are about something    *)
(*     real: each is applied below with every premise proved.              *)
(* (2) It does NOT discharge the instantiation at typingE ([EtaTypingE]):  *)
(*     [closed_context_conversionE] (row T0) and [welltypedE_context]      *)
(*     (rows T6, T2a, T0) remain hypotheses until their rows land; the     *)
(*     third, [typingE_rename_P], is proved there.                         *)
(* ===================================================================== *)

Section EtaTypingBase.
  Context {cf : checker_flags}.

  Lemma welltyped_inv Σ Γ t : welltyped Σ Γ t -> ∥ ∑ T, Σ ;;; Γ |- t : T ∥.
  Proof. intros [T h]. constructor. exists T. exact h. Qed.

  Lemma typing_rename_P_inst P (Σ : global_env_ext) Γ Δ f t A : wf Σ.1 ->
    wf_local Σ Δ × urenaming (shiftnP #|Γ| P) Γ Δ f ->
    Σ ;;; Γ |- t : A -> Σ ;;; Δ |- rename f t : rename f A.
  Proof. intros wfΣ hr ht. exact (PCUICRenameTyp.typing_rename_P (wfΣ := wfΣ) hr ht). Qed.

  Lemma closed_context_conversion_inst (Σ : global_env_ext) : wf Σ.1 -> forall Γ t T Γ',
    Σ ;;; Γ |- t : T -> wf_local Σ Γ' -> Σ ⊢ Γ = Γ' -> Σ ;;; Γ' |- t : T.
  Proof.
    intros wfΣ Γ t T Γ' h hΓ' hc.
    exact (PCUICContextConversionTyp.closed_context_conversion (wfΣ := wfΣ) Γ h hΓ' hc).
  Qed.

  Lemma welltyped_context_inst (Σ : global_env_ext) : wf Σ.1 -> forall Γ t,
    no_Eta_arg (snd t) -> welltyped Σ Γ (zip t) -> welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof. intros wfΣ. exact (welltyped_context Σ wfΣ). Qed.

  Lemma wf_local_push_real_base (Σ : global_env_ext) (wfΣ : wf Σ.1) Γ t se π :
    is_eta_frame se = false -> no_Eta_arg π ->
    welltyped Σ Γ (zipc t (se :: π)) -> wf_local Σ (Γ ,,, stack_context_eta π) ->
    ∥ wf_local Σ (Γ ,,, stack_context_eta (se :: π)) ∥.
  Proof.
    exact (wf_local_push_real_gen typing welltyped (fun Σ => wf Σ.1)
             (fun Σ Γ t T h => typing_wf_local h) welltyped_inv typing_rename_P_inst
             welltyped_context_inst Σ wfΣ Γ t se π).
  Qed.

  Lemma wf_local_eta_step_base (Σ : global_env_ext) (wfΣ : wf Σ.1) Γ na A π_i args ρ_j :
    wf_local Σ (Γ ,,, stack_context_eta (Lambda_bd na A :: π_i)) ->
    Σ ⊢ Γ ,,, stack_context_eta π_i = Γ ,,, stack_context_eta ρ_j ->
    wf_local Σ (Γ ,,, stack_context_eta ρ_j) ->
    wf_local Σ (Γ ,,, stack_context_eta (appstack args (Eta_app na (eta_rename π_i 0 A) :: ρ_j))).
  Proof.
    exact (wf_local_eta_step_gen typing (fun Σ Γ Γ' => Σ ⊢ Γ = Γ') (fun Σ => wf Σ.1)
             closed_context_conversion_inst Σ wfΣ Γ na A π_i args ρ_j).
  Qed.

  Lemma eta_rename_typing_base (Σ : global_env_ext) (wfΣ : wf Σ.1) Γ π t T : no_Eta_arg π ->
    wf_local Σ (Γ ,,, stack_context_eta π) ->
    Σ ;;; Γ ,,, stack_context π |- t : T ->
    Σ ;;; Γ ,,, stack_context_eta π |- eta_rename π 0 t : eta_rename π 0 T.
  Proof.
    exact (eta_rename_typing_gen typing (fun Σ => wf Σ.1) typing_rename_P_inst Σ wfΣ Γ π t T).
  Qed.
End EtaTypingBase.

(* ===================================================================== *)
(* Concrete satisfying instances: the premises the restatements added      *)
(* (scoping and ClosedBodies for eta_rename_red; wfE for the typed lemmas;  *)
(* the premises of wf_localE_push_real), and the base instances applied.   *)
(* Environment: the empty one, [pk_Σ].                                     *)
(* ===================================================================== *)

Section Instances.
  Context {cf : checker_flags}.

  Definition pk_Σ : global_env_ext := empty_ext empty_global_env.
  Definition pk_P : term := tSort sProp.
  Definition pk_na : aname := mkBindAnn nAnon Relevant.

  Lemma pk_wf : wf pk_Σ.1.
  Proof. exact PCUICEtaC1b.wf_empty_global_env. Qed.

  (* the new environment premise of the typed lemmas *)
  Lemma pk_wfE : wfE pk_Σ.1.
  Proof. exact (wf_incl_E pk_wf). Qed.

  (* the new environment premise of eta_rename_red *)
  Lemma pk_cb : ClosedBodies pk_Σ.
  Proof. exact (@PCUICClosedTyp.wf_ClosedBodies _ pk_Σ.1 pk_wf). Qed.

  (* eta_rename_red applied, every premise proved; the renaming is a real one: the η binder
     sits between Γ and the λ's binder, so Γ's variable tRel 1 becomes tRel 2. *)
  Definition pk_Γ : context := [vass pk_na pk_P].
  Definition pk_π : stack := [Lambda_bd pk_na pk_P; Eta_app pk_na pk_P].
  Definition pk_t : term := tApp (tLambda pk_na pk_P (tRel 0)) (tRel 1).

  Lemma eta_rename_red_inst :
    red pk_Σ (pk_Γ ,,, stack_context_eta pk_π) (eta_rename pk_π 0 pk_t) (eta_rename pk_π 0 (tRel 1)).
  Proof.
    apply eta_rename_red.
    - exact pk_cb.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - apply rt_step. exact (red_beta _ _ pk_na pk_P (tRel 0) (tRel 1)).
  Qed.

  Lemma eta_rename_red_inst_value : eta_rename pk_π 0 (tRel 1) = tRel 2.
  Proof. reflexivity. Qed.

  (* typing in pk_Σ, over typingE and over base typing *)
  Lemma pk_P_typedE Γ : wf_localE pk_Σ Γ -> pk_Σ ;;; Γ |-E pk_P : tSort (Sort.super sProp).
  Proof. intros h. apply typeE_Sort; [exact h|cbn; trivial]. Qed.

  Lemma pk_vassE Γ : wf_localE pk_Σ Γ -> lift_typing typingE pk_Σ Γ (j_vass pk_na pk_P).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (pk_P_typedE Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma pk_wflE1 : wf_localE pk_Σ [vass pk_na pk_P].
  Proof. apply localenv_cons_abs; [constructor|exact (pk_vassE [] localenv_nil)]. Qed.

  Lemma pk_lambda_welltypedE : welltypedE pk_Σ [] (tLambda pk_na pk_P (tRel 0)).
  Proof.
    econstructor. apply typeE_Lambda.
    - exact (pk_vassE [] localenv_nil).
    - exact (typeE_Rel _ _ 0 (vass pk_na pk_P) pk_wflE1 eq_refl).
  Qed.

  (* the premises of wf_localE_push_real, jointly satisfied (se := Lambda_bd, π := []) *)
  Lemma wf_localE_push_real_premises_inst :
    [× is_eta_frame (Lambda_bd pk_na pk_P) = false, no_Eta_arg ([] : stack),
       welltypedE pk_Σ [] (zipc (tRel 0) [Lambda_bd pk_na pk_P]) &
       wf_localE pk_Σ ([] ,,, stack_context_eta [])].
  Proof. split; [reflexivity|reflexivity|exact pk_lambda_welltypedE|constructor]. Qed.

  Lemma pk_P_typed Γ : wf_local pk_Σ Γ -> pk_Σ ;;; Γ |- pk_P : tSort (Sort.super sProp).
  Proof. intros h. apply type_Sort; [exact h|cbn; trivial]. Qed.

  Lemma pk_vass Γ : wf_local pk_Σ Γ -> lift_typing typing pk_Σ Γ (j_vass pk_na pk_P).
  Proof.
    intros h. split; [exact tt|]. exists (Sort.super sProp).
    split; [exact (pk_P_typed Γ h)|]. split; [exact I|reflexivity].
  Qed.

  Lemma pk_wfl1 : wf_local pk_Σ [vass pk_na pk_P].
  Proof. apply localenv_cons_abs; [constructor|exact (pk_vass [] localenv_nil)]. Qed.

  Lemma pk_lambda_welltyped : welltyped pk_Σ [] (tLambda pk_na pk_P (tRel 0)).
  Proof.
    econstructor. apply type_Lambda.
    - exact (pk_vass [] localenv_nil).
    - exact (type_Rel _ _ 0 (vass pk_na pk_P) pk_wfl1 eq_refl).
  Qed.

  (* the base instance of [wf_local_push_real_gen], applied with every premise proved *)
  Lemma wf_local_push_real_base_inst :
    ∥ wf_local pk_Σ ([] ,,, stack_context_eta [Lambda_bd pk_na pk_P]) ∥.
  Proof.
    exact (wf_local_push_real_base pk_Σ pk_wf [] (tRel 0) (Lambda_bd pk_na pk_P) []
             eq_refl eq_refl pk_lambda_welltyped localenv_nil).
  Qed.

  (* the base instance of [eta_rename_typing_gen], applied: tRel 0 under the λ's binder,
     with an η binder below it *)
  Definition pk_π2 : stack := [Lambda_bd pk_na pk_P; Eta_app pk_na pk_P].

  Lemma pk_wfl2 : wf_local pk_Σ ([] ,,, stack_context_eta pk_π2).
  Proof.
    change (wf_local pk_Σ ([] ,, vass pk_na pk_P ,, vass pk_na (lift 1 0 pk_P))).
    apply localenv_cons_abs; [exact pk_wfl1|].
    exact (pk_vass _ pk_wfl1).
  Qed.

  Lemma eta_rename_typing_base_inst :
    pk_Σ ;;; [] ,,, stack_context_eta pk_π2 |- eta_rename pk_π2 0 (tRel 0) : eta_rename pk_π2 0 (lift0 1 pk_P).
  Proof.
    apply (eta_rename_typing_base pk_Σ pk_wf [] pk_π2 (tRel 0) (lift0 1 pk_P) eq_refl pk_wfl2).
    exact (type_Rel _ _ 0 (vass pk_na pk_P) pk_wfl1 eq_refl).
  Qed.

  (* the base instance of [wf_local_eta_step_gen], applied: the λ side is
     [Lambda_bd na P :: []], the other side [Eta_app na P :: []] *)
  Lemma wf_local_eta_step_base_inst :
    wf_local pk_Σ ([] ,,, stack_context_eta (appstack [] (Eta_app pk_na (eta_rename [] 0 pk_P) :: []))).
  Proof.
    apply (wf_local_eta_step_base pk_Σ pk_wf [] pk_na pk_P [] [] []).
    - exact pk_wfl1.
    - constructor.
    - constructor.
  Qed.

  (* Satisfying instances of the rev 13-15 lemmas with premises (plan rev 15: every lemma
     stated there gets one). The virtual state is nb2a's (rev 15 C6): Γ = [a; f; A], most
     recent first, focus tRel 0, stack Eta_arg f [] :: App_l a :: Eta_app x A :: []. *)
  Definition nb_Γ : context := [vass pk_na pk_P; vass pk_na pk_P; vass pk_na pk_P].
  Definition nb_π : stack := [Eta_arg (tRel 1) []; App_l (tRel 0); Eta_app pk_na (tRel 2)].

  Lemma nb_virt_ok : virt_ok (tRel 0) nb_π = true.
  Proof. reflexivity. Qed.

  Lemma nb_no_Eta_arg : no_Eta_arg nb_π = false.
  Proof. reflexivity. Qed.

  Lemma zipp_eta_open_inst : is_open_term (nb_Γ ,,, stack_context_eta nb_π) (zipp_eta (tRel 0) nb_π).
  Proof. exact (zipp_eta_open nb_Γ (tRel 0) nb_π nb_virt_ok eq_refl eq_refl). Qed.

  Definition virt_ok_focus_inst := virt_ok_focus (tRel 0) nb_π nb_virt_ok nb_no_Eta_arg.

  Definition virt_ok_virtual_inst := virt_ok_virtual (tRel 0) nb_π nb_virt_ok nb_no_Eta_arg.

  Lemma virt_ok_not_head_inst : no_Eta_arg ([] : stack) = true.
  Proof. exact (virt_ok_not_head (tLambda pk_na pk_P (tRel 0)) [] eq_refl eq_refl). Qed.

  Lemma virt_ok_reduce_inst : virt_ok (tRel 0) (appstack [] (decompose_stack nb_π).2) = true.
  Proof. exact (virt_ok_reduce (tRel 0) nb_π (tRel 0) [] nb_virt_ok (or_intror (conj eq_refl eq_refl))). Qed.

  (* the mixed state: an η step on the virtual side pushes Eta_app above the Eta_arg *)
  Lemma virt_ok_eta_step_inst : virt_ok (tRel 0) (appstack [] (Eta_app pk_na pk_P :: nb_π)) = true.
  Proof. exact (virt_ok_eta_step (tRel 0) [] pk_na pk_P nb_π nb_virt_ok). Qed.

  Definition eta_ren_urenaming_inst := eta_ren_urenaming pk_Γ pk_π eq_refl.

  Lemma nb_wfl0 : wf_localE pk_Σ [vass pk_na pk_P].
  Proof. exact pk_wflE1. Qed.

  Lemma nb_wfl1 : wf_localE pk_Σ [vass pk_na pk_P; vass pk_na pk_P].
  Proof. apply localenv_cons_abs; [exact nb_wfl0|exact (pk_vassE _ nb_wfl0)]. Qed.

  Lemma nb_wfl2 : wf_localE pk_Σ nb_Γ.
  Proof. apply localenv_cons_abs; [exact nb_wfl1|exact (pk_vassE _ nb_wfl1)]. Qed.

  Lemma nb_wfl_eta : wf_localE pk_Σ (nb_Γ ,,, stack_context_eta nb_π).
  Proof.
    change (wf_localE pk_Σ (nb_Γ ,, vass pk_na (tRel 2))).
    apply localenv_cons_abs; [exact nb_wfl2|].
    split; [exact tt|]. exists sProp.
    split; [exact (typeE_Rel _ _ 2 (vass pk_na pk_P) nb_wfl2 eq_refl)|].
    split; [exact I|reflexivity].
  Qed.

  Lemma wf_localE_focus_context_inst : wf_localE pk_Σ (nb_Γ ,,, focus_context nb_π).
  Proof. exact (wf_localE_focus_context pk_Σ nb_Γ (tRel 0) nb_π nb_virt_ok nb_no_Eta_arg nb_wfl_eta). Qed.

  Lemma eta_companion_welltypedE_inst :
    welltypedE pk_Σ ([] ,,, stack_context_eta [Eta_app pk_na pk_P]) (tRel 0).
  Proof. exact (eta_companion_welltypedE pk_Σ [] [Eta_app pk_na pk_P] 0 (le_n 1) pk_wflE1). Qed.

  Lemma ws_cumul_ctx_pbE_eta_step_inst :
    ws_cumul_ctx_pbE Conv pk_Σ ([] ,,, stack_context_eta (Lambda_bd pk_na pk_P :: []))
      ([] ,,, stack_context_eta (appstack [] (Eta_app pk_na (eta_rename [] 0 pk_P) :: []))).
  Proof. exact (ws_cumul_ctx_pbE_eta_step pk_Σ [] pk_na pk_P [] [] [] eq_refl (All2_fold_nil _)). Qed.
End Instances.
