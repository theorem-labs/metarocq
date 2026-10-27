(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane: red1 lift-strengthening.

   Reflects one [red1] step on a lifted term back to the unlifted one:
   if [lift0 1 t] reduces, the reduct is itself a lift and [t] reduces.

   Deliberately a SIBLING of [PCUICEtaConfluence.v], not part of it: this needs
   the renaming/free-variable machinery (Conversion/, Typing/, Bidirectional/),
   and the foundation file is Required by several workers that must not pay for
   it. Nothing here mentions eta — it is pure base [red1] — so it can be
   Required independently of the eta foundation.

   ROUTE: strengthen the RENAMING rather than invert the lift, which is how base
   proves [weakening_red1] (Conversion/PCUICWeakeningConv.v:252, via
   [red1_rename] + [weakening_renaming]). The 2020 port
   (origin/eta_postpo:PCUICBasicStrengthening.v:130-455) inverted the lift with a
   ~325-line [red1_ind_all] induction; on the 9.2 AST its [red_iota] case runs
   through [iota_red] over [inst_case_branch_context]/[expand_lets], exactly
   where a hand port is most fragile. [urenaming_strengthen] replaces all of it.

   PREMISES, both genuine and both carried by base's corresponding lemma:
   - [wf Σ]: needed by [red1_rename] and [red1_on_free_vars]; the mechanism is
     [red_delta] of a constant, whose body must be closed.
   - [on_free_vars xpredT M]: NOT provable on the 9.2 AST. Witness: the [tCase]
     branch of [on_free_vars] (Syntax/PCUICOnFreeVars.v:72) contains
       test_context_k (fun k => on_free_vars (closedP k xpredT)) #|pparams| pcontext
     and the same for each [br.(bcontext)]; neither conjunct mentions [p], so it
     demands CLOSED predicate/branch contexts however permissive [p] is, and a
     tCase with an open pcontext declaration falsifies [on_free_vars xpredT].
     Accordingly [on_free_vars_true], [on_free_vars_xpredT] and
     [test_context_k_true] are ALL commented out (Syntax/PCUICOnFreeVars.v:139-166),
     and base's own [weakening_red1] carries [on_free_vars xpredT M] as an
     explicit premise immediately after [wf Σ] (Conversion/PCUICWeakeningConv.v:254).
     The premise is intrinsic to strengthening [red1] on this AST, not a cost of
     the renaming route: a version without it would claim more than base claims.
     Callers that carry [is_open_term Γ t] discharge it via [shiftnP_xpredT]. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICReduction PCUICOnFreeVars PCUICSigmaCalculus PCUICTyping.
From MetaRocq.PCUIC Require Import PCUICRenameConv PCUICOnFreeVarsConv
     PCUICInstConv PCUICClosedTyp BDStrengthening.
From Equations Require Import Equations.

From Stdlib Require Import ssreflect ssrbool.

Implicit Types (cf : checker_flags).

(** On the strengthened predicate, lifting undoes unlifting. *)
Lemma lift_unlift_renaming n k i :
  strengthenP k n xpredT i -> lift_renaming n k (unlift_renaming n k i) = i.
Proof.
  rewrite /strengthenP /lift_renaming /unlift_renaming.
  repeat nat_compare_specs => //=.
  all: lia.
Qed.

(** [lift_unlift_term] stated in [rename] form, which is how it appears after
    [red1_rename] (which produces [rename f _], not the folded [unlift]). *)
Lemma rename_unlift_lift n k t :
  rename (unlift_renaming n k) (lift n k t) = t.
Proof. exact (lift_unlift_term t). Qed.

(** The general form: strengthen [Γ'] out from under [Γ'']. *)
Lemma red1_strengthening_gen {cf} {Σ : global_env} {wfΣ : wf Σ} Γ Γ' Γ'' M N' :
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
  { eapply (@red1_on_free_vars cf _ (empty_ext Σ) _ _ _ wfΣ); [exact H|exact HM|exact Hctx]. }
  exists (unlift #|Γ'| #|Γ''| N'). split.
  - eapply (red1_rename _ _ _ _ _ _ (unlift_renaming #|Γ'| #|Γ''|)) in H; tea.
    2: apply urenaming_strengthen.
    rewrite rename_unlift_lift in H. exact H.
  - rewrite /unlift lift_rename rename_compose.
    symmetry. etransitivity.
    + eapply (rename_ext_cond (strengthenP #|Γ''| #|Γ'| xpredT) _ ren_id); [|exact HN'].
      intros i Hi. rewrite /ren_id. now apply lift_unlift_renaming.
    + apply rename_ren_id.
Qed.

(** The single-binder corollary the C3 provers Require. No condition is placed
    on [d], the binder stripped.

    DISCHARGING THE PREMISES AT A C3 CALL SITE — note [is_closed_context] is
    [on_free_vars_ctx xpred0] (Syntax/PCUICOnFreeVars.v:259), xpred0 NOT xpredT,
    so neither premise is definitionally what C3 carries; each is ONE
    monotonicity step ([xpred0 ≤ xpredT] pointwise, [on_free_vars] monotone):
      on_ctx_free_vars xpredT Γ   from  is_closed_context Γ :
        rewrite on_ctx_free_vars_xpredT; eapply on_free_vars_ctx_impl; [|eassumption]; done.
      on_free_vars xpredT t       from  is_open_term Γ t :
        eapply on_free_vars_impl; [|eassumption]; done.
    ([on_ctx_free_vars_impl] is commented out at :991, hence going through
     [on_ctx_free_vars_xpredT] and the ctx-level [on_free_vars_ctx_impl].) *)
Lemma red1_strengthening {cf} {Σ : global_env} {wfΣ : wf Σ} Γ d t u :
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
