(* Distributed under the terms of the MIT license. *)
(** * [Typing/PCUICWeakeningTyp] over [typingE]

  Weakening of [typingE] derivations with respect to the local context. The base
  file copied over [typingE], [wf_localE] and [wfE]; every lemma takes the suffix [E]
  and states its base twin with the relations renamed, and [isType]/[isTypeRel] become
  [on_type (lift_typing typingE)]/[on_type_rel (lift_typing typingE)]. Every proof
  goes through the renaming lemma [typing_rename_propE] ([Typing/PCUICRenameTypEta]),
  as base's goes through [typing_rename_prop]. The proofs are base's. *)
From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICCumulativity
  PCUICClosed
  PCUICSigmaCalculus PCUICRenameDef PCUICRenameConv PCUICRenameTyp PCUICOnFreeVars
  PCUICClosedConv PCUICClosedTyp PCUICWeakeningConv
  PCUICTypingEta PCUICTypingEtaInd PCUICClosedTypEta PCUICRenameTypEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations Require Import Equations.

Implicit Types cf : checker_flags.

Set Default Goal Selector "!".
Generalizable Variables Σ Γ t T.

Lemma weakening_wf_localE {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' Γ''} :
  wf_localE Σ (Γ ,,, Γ') ->
  wf_localE Σ (Γ ,,, Γ'') ->
  wf_localE Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ').
Proof.
  intros wfΓ' wfΓ''.
  pose proof (env_propE_wf_local typing_rename_propE _ wfΣ _ wfΓ') as X. simpl in X.
  eapply All_local_env_app_inv in X as [XΓ XΓ'].
  apply All_local_env_app => //.
  rewrite /lift_context.
  apply All_local_env_fold.
  eapply (All_local_env_impl_ind XΓ').
  intros Δ j IH H; simpl.
  eapply lift_typing_f_impl => //.
  2: intros ?? Hf; rewrite -/(lift_context #|Γ''| 0 Δ).
  2: rewrite Nat.add_0_r; rewrite !lift_rename; apply Hf.
  eapply (H xpredT).
  split.
  + apply All_local_env_app; auto.
    apply All_local_env_fold, IH.
  + apply weakening_renaming.
Qed.

Lemma weakening_wf_local_eqE {cf: checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' Γ'' n} :
  wf_localE Σ (Γ ,,, Γ') ->
  wf_localE Σ (Γ ,,, Γ'') ->
  n = #|Γ''| ->
  wf_localE Σ (Γ ,,, Γ'' ,,, lift_context n 0 Γ').
Proof.
  intros ? ? ->; now apply weakening_wf_localE.
Qed.

Lemma weakening_rename_typingE `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' Γ''} {t T} :
  wf_localE Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |-E t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, rename_context (lift_renaming #|Γ''| 0) Γ' |-E
    rename (lift_renaming #|Γ''| #|Γ'|) t :
    rename (lift_renaming #|Γ''| #|Γ'|) T.
Proof.
  intros wfext Ht.
  eapply (typing_renameE); eauto; rewrite rename_context_lift_context.
  - eapply weakening_wf_localE; cbn; eauto using typingE_wf_local.
  - now apply weakening_renaming.
Qed.

Lemma weakening_typingE `{cf : checker_flags} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ Γ' Γ''} {t T} :
  wf_localE Σ (Γ ,,, Γ'') ->
  Σ ;;; Γ ,,, Γ' |-E t : T ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |-E lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros wfext Ht.
  rewrite !lift_rename.
  eapply (typing_renameE); eauto.
  - eapply weakening_wf_localE; eauto using typingE_wf_local.
  - now apply weakening_renaming.
Qed.

Lemma weakeningE `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wfE Σ.1 -> wf_localE Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |-E t : T ->
  Σ ;;; Γ ,,, Γ' |-E lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  eapply (weakening_typingE (Γ' := [])); eauto.
Qed.

Lemma weaken_wf_localE {cf:checker_flags} {Σ Δ} Γ :
  wfE Σ.1 ->
  wf_localE Σ Γ ->
  wf_localE Σ Δ -> wf_localE Σ (Γ ,,, Δ).
Proof.
  intros wfΣ wfΓ wfΔ.
  generalize (weakening_wf_localE (Γ := []) (Γ'' := Γ) (Γ' := Δ)) => /=.
  rewrite !app_context_nil_l.
  move/(_ wfΔ wfΓ).
  rewrite closed_ctx_lift //.
  now eapply closed_wf_localE.
Qed.


Lemma lift_declared_constantE `{checker_flags} Σ cst decl n k :
  wfE Σ ->
  declared_constant Σ cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  intros wf declc.
  rewrite /map_constant_body; destruct decl; simpl; f_equal; rewrite ?lift_rename.
  - eapply declared_constant_closed_typeE in declc; eauto.
    now rewrite rename_closed.
  - destruct cst_body0 eqn:cb => /= //.
    f_equal.
    eapply declared_constant_closed_bodyE in declc; simpl; eauto.
    now rewrite lift_rename rename_closed.
Qed.


(** Variant with more freedom on the length to apply it in backward-chainings. *)
Lemma weakening_lengthE {cf:checker_flags} Σ Γ Γ' t T n :
  wfE Σ.1 ->
  n = #|Γ'| ->
  wf_localE Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |-E t : T ->
  Σ ;;; Γ ,,, Γ' |-E (lift0 n) t : (lift0 n) T.
Proof. intros wfΣ ->; now apply weakeningE. Qed.

Lemma weaken_ctxE {cf:checker_flags} {Σ Γ t T} Δ :
  wfE Σ.1 ->
  wf_localE Σ Δ ->
  Σ ;;; Γ |-E t : T ->
  Σ ;;; Δ ,,, Γ |-E t : T.
Proof.
  intros wfΣ wfΔ ty.
  epose proof (weakening_typingE (Γ := [])).
  rewrite !app_context_nil_l in X.
  forward X by eauto using typingE_wf_local.
  specialize (X ty).
  eapply typecheck_closedE in ty as [_ [clΓ [clt clT]%andb_and]]; auto.
  rewrite !lift_closed // in X.
  now rewrite closed_ctx_lift in X.
Qed.

Lemma weakening_genE : forall (cf : checker_flags) (Σ : global_env_ext)
  (Γ Γ' : context) (t T : term) n, n = #|Γ'| ->
  wfE Σ ->
  wf_localE Σ (Γ ,,, Γ') ->
  Σ;;; Γ |-E t : T -> Σ;;; Γ ,,, Γ' |-E (lift0 n) t : (lift0 n) T.
Proof.
  intros ; subst n; now apply weakeningE.
Qed.

(** Convenience lemma when going through instantiation for renaming.
    Δ is arbitrary here, it does not have to be the weakening of some other context. *)
Lemma shift_typingE {cf} {Σ : global_env_ext} {wfΣ : wfE Σ} {Γ t T n Δ} :
  Σ ;;; Γ |-E t : T ->
  wf_localE Σ (Γ ,,, Δ) ->
  n = #|Δ| ->
  Σ ;;; Γ ,,, Δ |-E t.[↑^n] : T.[↑^n].
Proof.
  intros ht hΔ ->.
  eapply meta_conv_allE. 3-4:now rewrite -rename_inst -lift0_rename.
  2:reflexivity.
  eapply weakening_genE => //.
Qed.

Lemma lift_typing_weakeningE {cf : checker_flags} Σ Γ Γ' j :
  wfE Σ.1 -> wf_localE Σ (Γ ,,, Γ') ->
  lift_typing typingE Σ Γ j ->
  lift_typing typingE Σ (Γ ,,, Γ') (judgment_map (lift0 #|Γ'|) j).
Proof.
  intros wfΣ wfΓ Hj.
  apply lift_typing_f_impl with (1 := Hj) => // t T.
  now apply weakeningE.
Qed.

Lemma lift_typing_weaken_ctxE {cf : checker_flags} Σ Γ Δ j :
  wfE Σ.1 -> wf_localE Σ Δ ->
  lift_typing typingE Σ Γ j ->
  lift_typing typingE Σ (Δ ,,, Γ) j.
Proof.
  intros wfΣ wfΔ Hj.
  apply lift_typing_impl with (1 := Hj) => t T.
  now apply weaken_ctxE.
Qed.

Corollary All_mfix_wfE {cf:checker_flags} Σ Γ mfix :
  wfE Σ.1 -> wf_localE Σ Γ ->
  All (fun d : def term => on_type_rel (lift_typing typingE) Σ Γ (dtype d) (dname d).(binder_relevance)) mfix ->
  wf_localE Σ (Γ ,,, fix_context mfix).
Proof.
  move=> wfΣ wf a; move: wf.
  change (fix_context mfix) with (fix_context_gen #|@nil context_decl| mfix).
  change Γ with (Γ ,,, []).
  generalize (@nil context_decl) as Δ.
  rewrite /fix_context_gen.
  intros Δ wfΔ.
  eapply All_local_env_app; auto.
  induction a in Δ, wfΔ |- *; simpl; auto.
  1: now constructor.
  simpl.
  eapply All_local_env_app; auto.
  * constructor. 1: constructor.
    now eapply lift_typing_weakeningE in p.
  * specialize (IHa (Δ ,,, [vass (dname x) (lift0 #|Δ| (dtype x))])).
    rewrite length_app in IHa. simpl in IHa.
    forward IHa.
    + simpl; constructor; auto.
      now eapply lift_typing_weakeningE in p.
    + eapply All_local_env_impl; eauto.
      simpl; intros.
      rewrite app_context_assoc. apply X.
Qed.

Lemma lift_typing_weakening_skipnE {cf:checker_flags} {Σ : global_env_ext} {n Γ j}
  (isdecl : n <= #|Γ|) :
  wfE Σ -> wf_localE Σ Γ ->
  lift_typing typingE Σ (skipn n Γ) j ->
  lift_typing typingE Σ Γ (judgment_map (lift0 n) j).
Proof.
  intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
  assert (n = #|firstn n Γ|).
  { rewrite firstn_length_le; auto with arith. }
  rewrite {3}H.
  now eapply lift_typing_weakeningE in wfty.
Qed.

Lemma All_local_env_nth_error_weakenE {cf:checker_flags} {Σ : global_env_ext} {Γ n decl} :
  wfE Σ -> wf_localE Σ Γ ->
  nth_error Γ n = Some decl ->
  lift_typing typingE Σ Γ (j_decl (map_decl (lift0 (S n)) decl)).
Proof using Type.
  intros hΣ hΓ e.
  eapply All_local_env_nth_error in e as hj; tea.
  apply nth_error_Some_length in e.
  now apply lift_typing_weakening_skipnE in hj.
Qed.

Lemma isType_liftE {cf:checker_flags} {Σ : global_env_ext} {n Γ ty}
  (isdecl : n <= #|Γ|):
  wfE Σ -> wf_localE Σ Γ ->
  on_type (lift_typing typingE) Σ (skipn n Γ) ty ->
  on_type (lift_typing typingE) Σ Γ (lift0 n ty).
Proof.
  now apply @lift_typing_weakening_skipnE with (j := Typ _).
Qed.

Lemma isTypeRel_liftE {cf:checker_flags} {Σ : global_env_ext} {n Γ ty r}
  (isdecl : n <= #|Γ|):
  wfE Σ -> wf_localE Σ Γ ->
  on_type_rel (lift_typing typingE) Σ (skipn n Γ) ty r ->
  on_type_rel (lift_typing typingE) Σ Γ (lift0 n ty) r.
Proof.
  now apply @lift_typing_weakening_skipnE with (j := TypRel _ _).
Qed.
