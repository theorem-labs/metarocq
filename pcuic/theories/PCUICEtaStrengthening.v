(* Distributed under the terms of the MIT license. *)
(** * red1 lift-strengthening

   Reflects one [red1] step on a lifted term back to the unlifted one. Nothing
   here mentions η; it is the one ingredient C3 ([PCUICEtaC3BR]) needs that is
   about [red1] alone.

   The import closure of this file reaches neither [PCUICConfluence] nor
   [PCUICParallelReductionConfluence], and C3's does not either. Importing base
   [BDStrengthening] would break that: it reaches [PCUICSR] and so
   [PCUICConfluence]. So [urenaming_strengthen], [on_ctx_free_vars_strengthenP]
   and the [unlift] definitions are copied here from that file; their proofs are
   pure renaming and arithmetic and need nothing else from it. *)

From Stdlib Require Import Morphisms.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICSigmaCalculus PCUICClosed
     PCUICOnFreeVars PCUICReduction PCUICRenameDef PCUICRenameConv
     PCUICOnFreeVarsConv PCUICInstConv PCUICClosedTyp PCUICTyping PCUICClosedBodies.
From MetaRocq.PCUIC Require Import PCUICWeakeningConv PCUICRenameTyp.
From Equations Require Import Equations.
From Equations.Prop Require Import DepElim.
From Stdlib Require Import ssreflect ssrbool.

Implicit Types (cf : checker_flags).


Local Ltac case_inequalities :=
  match goal with
  | |- context [?x <=? ?y] => destruct (Nat.leb_spec x y)
  | |- context [?x <? ?y] => destruct (Nat.ltb_spec x y)
  end.
(** ** Ported from [BDStrengthening.v] — same proofs, confluence-free closure. *)

Definition unlift_renaming n k i := if i <? k then i else i - n.
Definition unlift n k := rename (unlift_renaming n k).

Lemma lift_unlift n k : (unlift_renaming n k) ∘ (lift_renaming n k) =1 ren_id.
Proof.
  intros i. rewrite /unlift_renaming /lift_renaming /ren_id.
  repeat nat_compare_specs. all: lia.
Qed.

Lemma lift_unlift_term {n k} t : unlift n k (lift n k t) = t.
Proof.
  by rewrite lift_rename /unlift (rename_compose _ _ _) lift_unlift rename_ren_id.
Qed.

(** On the strengthened predicate, lifting undoes unlifting. *)
Lemma lift_unlift_renaming n k i :
  strengthenP k n xpredT i -> lift_renaming n k (unlift_renaming n k i) = i.
Proof.
  rewrite /strengthenP /lift_renaming /unlift_renaming.
  repeat nat_compare_specs => //=. all: lia.
Qed.


(** Local copies from base [BDStrengthening] (see the header: importing it would
    pull in the confluence files). *)
Lemma Alli_impl_le {A P Q} {l : list A} {n} :
  Alli P n l -> (forall m x, m <= n + #|l| -> P m x -> Q m x) -> Alli Q n l.
Proof.
  induction 1; intros H; [constructor|constructor].
  - apply H => //. lia.
  - apply IHX. intros. apply H => //. cbn. lia.
Qed.

Lemma addnP_strengthen_lift i k k' :
  i <= k' ->
  (addnP (S i) (strengthenP k' k xpredT)) ∘ (lift_renaming k (Nat.pred k' - i)) =1 xpredT.
Proof.
  intros l ?. rewrite /addnP /strengthenP /lift_renaming.
  destruct (Nat.leb_spec (Nat.pred k' - i) a) => //.
  all: case_inequalities => //. all: case_inequalities => //. all: lia.
Qed.
Lemma rename_unlift_lift n k t :
  rename (unlift_renaming n k) (lift n k t) = t.
Proof. exact (lift_unlift_term t). Qed.

(** Context free-vars under [strengthenP], ported verbatim from BDStrengthening. *)
Lemma on_ctx_free_vars_strengthenP Γ Γ' Γ'':
  on_ctx_free_vars xpredT Γ ->
  on_ctx_free_vars xpredT Γ'' ->
  on_ctx_free_vars (strengthenP #|Γ''| #|Γ'| xpredT) (Γ,,,Γ',,,lift_context #|Γ'| 0 Γ'').
Proof.
  intros hΓ hΓ''.
  rewrite !on_ctx_free_vars_app.
  repeat (apply /andP ; split).
  - rewrite /on_ctx_free_vars /lift_context /=.
    erewrite alli_fold_context_k_prop.
    apply alli_Alli in hΓ''.
    eapply alli_Alli, Alli_impl_le ; tea.
    move => i [? [?|] ?] /= ?.
    + rewrite /on_free_vars_decl /test_decl /= !addnP_xpredT => /andP [? ?].
      apply /implyP => _.
      apply /andP ; split.
      all: rewrite lift_rename on_free_vars_rename Nat.add_0_r addnP_strengthen_lift //.
    + rewrite /on_free_vars_decl /test_decl /= !addnP_xpredT => ?.
      apply /implyP => _.
      rewrite lift_rename on_free_vars_rename Nat.add_0_r addnP_strengthen_lift //.
  - rewrite lift_context_length.
    rewrite /on_ctx_free_vars.
    apply alli_Alli.
    eapply forall_nth_error_Alli.
    intros i ? ?.
    assert (i < #|Γ'|) by (apply nth_error_Some ; congruence).
    rewrite /addnP /strengthenP /=.
    repeat case_inequalities => //=. all: lia.
  - rewrite addnP_add lift_context_length.
    erewrite on_ctx_free_vars_proper.
    3: reflexivity. 1: eassumption.
    intros ?. rewrite /addnP /strengthenP.
    case_inequalities => //. case_inequalities => //. lia.
Qed.

(** [urenaming_strengthen], ported verbatim from BDStrengthening. *)
Lemma urenaming_strengthen P Γ Γ' Γ'' :
  urenaming (strengthenP #|Γ''| #|Γ'| P) (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'') (Γ,,,Γ'') (unlift_renaming #|Γ'| #|Γ''|).
Proof.
  rewrite <- rename_context_lift_context.
  intros i decl' pi nthi.
  rewrite /strengthenP in pi.
  destruct (Nat.ltb_spec0 i #|Γ''|) as [iΓ''|iΓ''].
  - rewrite nth_error_app_context_lt in nthi.
    1: by rewrite fold_context_k_length.
    rewrite nth_error_rename_context in nthi.
    apply option_map_Some in nthi as [decl'' []]. subst.
    eexists ; split ; [idtac|split ; [idtac|split]].
    + rewrite /unlift_renaming.
      move: (iΓ'') => /Nat.ltb_spec0 ->.
      rewrite nth_error_app_context_lt //.
      eassumption.
    + reflexivity.
    + rewrite /= rename_compose.
      apply rename_proper ; auto. intros x.
      rewrite !rshiftk_S lift_renaming_spec -(shiftn_rshiftk _ _ _) !shiftn_add -lift_renaming_spec.
      rewrite Nat.add_0_r Nat.add_comm Nat.sub_add; try lia.
      rewrite (lift_unlift _ _ _) /ren_id /unlift_renaming.
      by move: (iΓ'') => /Nat.ltb_spec0 ->.
    + cbn ; destruct (decl_body decl'') ; rewrite //=.
      f_equal. rewrite rename_compose.
      apply rename_proper ; auto. intros x.
      change (S (i + _)) with
        (rshiftk (S i) (shiftn (#|Γ''| - S i) (lift_renaming #|Γ'| 0) x)).
      rewrite shiftn_lift_renaming lift_renaming_spec -(shiftn_rshiftk _ _ _) shiftn_add.
      rewrite -lift_renaming_spec Nat.add_0_r.
      rewrite Nat.add_comm Nat.sub_add //.
      rewrite (lift_unlift _ _ _) /ren_id /unlift_renaming.
      by move: (iΓ'') => /Nat.ltb_spec0 ->.
  - rewrite -app_context_assoc /= in nthi.
    destruct (Nat.ltb_spec0 i (#|Γ''| + #|Γ'|)) as [iΓ'|iΓ'] ; cbn in * ; [congruence|..].
    apply Nat.nlt_ge in iΓ'.
    rewrite nth_error_app_context_ge length_app /= rename_context_length // in nthi.
    eexists ; repeat split.
    + rewrite /unlift_renaming.
      case_inequalities. 1: lia.
      rewrite nth_error_app_context_ge ; [lia|..].
      rewrite -nthi. f_equal. lia.
    + apply rename_proper ; auto. intros x.
      rewrite /unlift_renaming.
      case_inequalities. 1: lia.
      case_inequalities. all: lia.
    + destruct (decl_body decl') ; rewrite //=.
      f_equal. apply rename_proper ; auto. intros x.
      rewrite /unlift_renaming.
      case_inequalities. 1: lia.
      case_inequalities. all: lia.
Qed.

(** ** The strengthening lemmas proper. *)

Lemma red1_strengthening_gen {cf} {Σ : global_env} {wfΣ : ClosedBodies Σ} Γ Γ' Γ'' M N' :
  on_ctx_free_vars xpredT Γ ->
  on_ctx_free_vars xpredT Γ'' ->
  on_free_vars xpredT M ->
  red1 Σ (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'') (lift #|Γ'| #|Γ''| M) N' ->
  ∑ N, red1 Σ (Γ ,,, Γ'') M N × N' = lift #|Γ'| #|Γ''| N.
Proof.
  intros HΓ HΓ'' HfvM H.
  assert (HM : on_free_vars (strengthenP #|Γ''| #|Γ'| xpredT) (lift #|Γ'| #|Γ''| M)).
  { now rewrite on_free_vars_lift. }
  assert (Hctx : on_ctx_free_vars (strengthenP #|Γ''| #|Γ'| xpredT)
                   (Γ ,,, Γ' ,,, lift_context #|Γ'| 0 Γ'')).
  { now apply on_ctx_free_vars_strengthenP. }
  assert (HN' : on_free_vars (strengthenP #|Γ''| #|Γ'| xpredT) N').
  { eapply (@red1_on_free_vars_cb cf _ (empty_ext Σ) _ _ _ wfΣ); [exact H|exact HM|exact Hctx]. }
  exists (unlift #|Γ'| #|Γ''| N'). split.
  - eapply (red1_rename_cb _ _ _ _ _ _ (unlift_renaming #|Γ'| #|Γ''|)) in H; tea.
    2: apply urenaming_strengthen.
    rewrite rename_unlift_lift in H. exact H.
  - rewrite /unlift lift_rename rename_compose.
    symmetry. etransitivity.
    + eapply (rename_ext_cond (strengthenP #|Γ''| #|Γ'| xpredT) _ ren_id); [|exact HN'].
      intros i Hi. rewrite /ren_id. now apply lift_unlift_renaming.
    + apply rename_ren_id.
Qed.

(** The single-binder corollary C3 uses ([PCUICEtaC3BR]). No condition on [d].
    At a call site the two premises come from the scoping hypotheses by one
    monotonicity step each:
      [on_ctx_free_vars xpredT Γ] from [is_closed_context Γ]:
        rewrite on_ctx_free_vars_xpredT; eapply on_free_vars_ctx_impl; [|eassumption]; done.
      [on_free_vars xpredT t] from [is_open_term Γ t]:
        eapply on_free_vars_impl; [|eassumption]; done.
    ([is_closed_context] is [on_free_vars_ctx xpred0], not [xpredT], and base's
    [on_ctx_free_vars_impl] is commented out.) *)
Lemma red1_strengthening {cf} {Σ : global_env} {wfΣ : ClosedBodies Σ} Γ d t u :
  on_ctx_free_vars xpredT Γ ->
  on_free_vars xpredT t ->
  red1 Σ (Γ ,, d) (lift0 1 t) u -> ∑ u', (u = lift0 1 u') × red1 Σ Γ t u'.
Proof.
  intros HΓ Hfv H.
  unshelve edestruct (@red1_strengthening_gen cf Σ wfΣ Γ [d] [] t u) as (N & HR & HE).
  { exact HΓ. }
  { reflexivity. }
  { exact Hfv. }
  { cbn. exact H. }
  exists N. split; [exact HE|exact HR].
Qed.
