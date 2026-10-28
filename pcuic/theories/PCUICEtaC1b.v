(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, C4: REFUTATIONS of row C1b and of C4 itself.

   [C1b_false : C1b_statement -> False] and [C4_false : C4_statement -> False],
   both over the pinned statements of [PCUICEtaBetaEta]. The C4 witness is at
   the end of the file; it reuses the C1b normality lemmas.

   Row C1b, pinned as [C1b_statement] in [PCUICEtaBetaEta], asks for
     [upto_domain t t' -> eta1 t u -> ∑ u', clos_refl eta1 t' u' × upto_domain u u']
   over the shared [eta1]/[upto_domain] of [PCUICEtaDefs]. This is the exact
   hypothesis that [HR_A_instantiable] ([PCUICEtaC4Shape]) leaves open, and the
   (E vs S) hypothesis of [HR_strong_commutation_modulo_statement] and
   [HR_modulo_statement] ([PCUICEtaBetaEta]) at the instance
   [S := eta1], [E := upto_domain], [Q := is_open_term Γ].

   It is FALSE. Witness (all binders are [mkBindAnn nAnon Relevant], [P := tSort sProp]):

     t  = λ x:P. (P (λ y:P. y)) x       an η-redex: t = eta_redex x P u
     u  = P (λ y:P. y)                   t →η u   (eta_red)
     t' = λ x:P. (P (λ y:x. y)) x        t ~ t'   (upto_domain: only an inner
                                                   λ DOMAIN differs, P vs x)

   In [t'] the bound [x] occurs in the inner λ's DOMAIN, so the function part is
   not [lift0 1] of anything and [t'] is not an η-redex. [t'] has no [eta1]
   step at all and no [red1] step in any [Σ]/[Γ] (its head is a sort, its every
   [tRel] is bound by a λ, so is a [vass]). So the only term [t'] reaches, by
   any number of β or η steps, is [t'] itself; and [upto_domain u t'] fails
   because [u] is an application and [t'] a λ.

   Hence the refutation holds in the strongest form we could state:
   - for the statement as pinned: [C1b_false : C1b_statement -> False];
   - relativised to well-scoped terms, the form (A)/(B) actually consume
     ([C1b_false_open]; [t], [t'] are closed, so [is_open_term Γ] holds for every [Γ]);
   - with the related side relaxed to [clos_refl_trans (beta_eta1 Σ Γ)], i.e.
     βη-many-steps ([C1b_false_open_betaeta]). So no relaxation of the closure on
     the related side repairs it; a repair has to change [eta1], [upto_domain]
     or the (A)/(B) decomposition.

   Dependencies: [PCUICEtaDefs], [PCUICEtaBetaEta] (for [C1b_statement], [C4_statement],
   [beta_eta1]), [PCUICTyping] (for [wf]) and base syntax/reduction only. No [Context], no [Axiom], no [Admitted]. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICReduction
     PCUICOnFreeVars PCUICTyping PCUICEtaDefs PCUICEtaBetaEta.

Import PCUICOnFreeVars (is_open_term, is_closed_context).

(** ** The witness *)

Definition c1b_na : aname := mkBindAnn nAnon Relevant.
Definition c1b_P : term := tSort sProp.
(** [λ y:x. y] at depth one: the domain is the outer bound variable. *)
Definition c1b_L : term := tLambda c1b_na (tRel 0) (tRel 0).
Definition c1b_u : term := tApp c1b_P (tLambda c1b_na c1b_P (tRel 0)).
Definition c1b_t : term := eta_redex c1b_na c1b_P c1b_u.
Definition c1b_t' : term := tLambda c1b_na c1b_P (tApp (tApp c1b_P c1b_L) (tRel 0)).

Lemma c1b_step : eta1 c1b_t c1b_u.
Proof. apply eta_red. Qed.

Lemma c1b_upto : upto_domain c1b_t c1b_t'.
Proof.
  unfold c1b_t, c1b_t', c1b_u, c1b_L, c1b_P. cbn.
  repeat constructor.
Qed.

Lemma c1b_not_upto : upto_domain c1b_u c1b_t' -> False.
Proof. unfold c1b_u, c1b_t'. intros H. inversion H. Qed.

Lemma c1b_open (Γ : context) : is_open_term Γ c1b_t × is_open_term Γ c1b_t'.
Proof. split; vm_compute; reflexivity. Qed.

(** ** [c1b_t'] is [eta1]-normal *)

Lemma lift_1_0_not_Rel0 T : lift 1 0 T = tRel 0 -> False.
Proof. destruct T; cbn; congruence. Qed.

Lemma lift_1_0_not_PL T : lift 1 0 T = tApp c1b_P c1b_L -> False.
Proof.
  unfold c1b_P, c1b_L. intros E.
  destruct T; cbn in E; try discriminate E.
  match type of E with tApp _ (lift 1 0 ?T2) = _ => destruct T2; cbn in E; try discriminate E end.
  injection E; intros; eapply lift_1_0_not_Rel0; eassumption.
Qed.

Ltac unf := unfold c1b_t', c1b_L, c1b_P in *.

Ltac inv_eta H :=
  let x := fresh "x" in
  let Ex := fresh "Ex" in
  match type of H with eta1 ?t _ => remember t as x eqn:Ex end;
  destruct H; try discriminate Ex; injection Ex; intros; subst.

Lemma eta_normal_Sort s v : eta1 (tSort s) v -> False.
Proof. unf. intros H. inv_eta H. Qed.

Lemma eta_normal_Rel n v : eta1 (tRel n) v -> False.
Proof. unf. intros H. inv_eta H. Qed.

Lemma eta_normal_L v : eta1 c1b_L v -> False.
Proof.
  unf. intros H. inv_eta H; eapply eta_normal_Rel; eassumption.
Qed.

Lemma eta_normal_PL v : eta1 (tApp c1b_P c1b_L) v -> False.
Proof.
  unf. intros H. inv_eta H.
  - eapply eta_normal_Sort; eassumption.
  - eapply eta_normal_L; eassumption.
Qed.

Lemma eta_normal_body v : eta1 (tApp (tApp c1b_P c1b_L) (tRel 0)) v -> False.
Proof.
  unf. intros H. inv_eta H.
  - eapply eta_normal_PL; eassumption.
  - eapply eta_normal_Rel; eassumption.
Qed.

Lemma eta_normal_t' v : eta1 c1b_t' v -> False.
Proof.
  unf. intros H. inv_eta H.
  all: first
    [ eapply lift_1_0_not_PL; eassumption
    | eapply lift_1_0_not_PL; symmetry; eassumption
    | eapply eta_normal_Sort; eassumption
    | eapply eta_normal_body; eassumption ].
Qed.

(** ** [c1b_t'] is [red1]-normal, in every [Σ] and [Γ] *)

Lemma mkApps_fix_head mfix idx args t :
  mkApps (tFix mfix idx) args = t -> fst (decompose_app t) = tFix mfix idx.
Proof. intros <-. rewrite decompose_app_mkApps //. Qed.

Ltac inv_red H :=
  let x := fresh "x" in
  let Ex := fresh "Ex" in
  match type of H with red1 _ _ ?t _ => remember t as x eqn:Ex end;
  destruct H; try discriminate Ex;
  try (apply mkApps_fix_head in Ex; unfold decompose_app in Ex; cbn in Ex; discriminate Ex);
  injection Ex; intros; subst.

Lemma red_normal_Sort Σ Γ s v : red1 Σ Γ (tSort s) v -> False.
Proof. unf. intros H. inv_red H. Qed.

Lemma red_normal_Rel0 Σ Γ na X v : red1 Σ (Γ ,, vass na X) (tRel 0) v -> False.
Proof.
  unf. intros H. inv_red H.
  match goal with e : option_map decl_body _ = _ |- _ => cbn in e; discriminate e end.
Qed.

Lemma red_normal_L Σ Γ na X v : red1 Σ (Γ ,, vass na X) c1b_L v -> False.
Proof.
  unf. intros H. inv_red H; eapply red_normal_Rel0; eassumption.
Qed.

Lemma red_normal_PL Σ Γ na X v : red1 Σ (Γ ,, vass na X) (tApp c1b_P c1b_L) v -> False.
Proof.
  unf. intros H. inv_red H.
  - eapply red_normal_Sort; eassumption.
  - eapply red_normal_L; eassumption.
Qed.

Lemma red_normal_body Σ Γ na X v :
  red1 Σ (Γ ,, vass na X) (tApp (tApp c1b_P c1b_L) (tRel 0)) v -> False.
Proof.
  unf. intros H. inv_red H.
  - eapply red_normal_PL; eassumption.
  - eapply red_normal_Rel0; eassumption.
Qed.

Lemma red_normal_t' Σ Γ v : red1 Σ Γ c1b_t' v -> False.
Proof.
  unf. intros H. inv_red H.
  - eapply red_normal_Sort; eassumption.
  - eapply red_normal_body; eassumption.
Qed.

Lemma betaeta_normal_t' Σ Γ v : beta_eta1 Σ Γ c1b_t' v -> False.
Proof.
  intros [H|H]; [exact (red_normal_t' _ _ _ H) | exact (eta_normal_t' _ H)].
Qed.

(** ** From normality to "reaches only itself" *)

Lemma rt_from_normal {A} (R : A -> A -> Type) x y :
  (forall v, R x v -> False) -> clos_refl_trans R x y -> y = x.
Proof.
  intros Hn H. revert Hn. induction H; intros Hn.
  - exfalso. eapply Hn; eassumption.
  - reflexivity.
  - specialize (IHclos_refl_trans1 Hn). subst.
    exact (IHclos_refl_trans2 Hn).
Qed.

Lemma clos_refl_rt {A} (R : A -> A -> Type) x y : clos_refl R x y -> clos_refl_trans R x y.
Proof. destruct 1; first [apply rt_step; assumption | apply rt_refl]. Qed.

(** ** The refutations *)

(** Strongest form: relativised to well-scoped terms, related side βη-many-steps. *)
Theorem C1b_false_open_betaeta (Σ : global_env) (Γ : context) :
  (forall t t' u, is_open_term Γ t -> is_open_term Γ t' ->
     upto_domain t t' -> eta1 t u ->
     ∑ u', clos_refl_trans (beta_eta1 Σ Γ) t' u' × upto_domain u u') -> False.
Proof.
  intros H.
  destruct (c1b_open Γ) as [Ht Ht'].
  destruct (H _ _ _ Ht Ht' c1b_upto c1b_step) as (u' & Hr & Hu).
  apply (rt_from_normal _ _ _ (betaeta_normal_t' Σ Γ)) in Hr. subst u'.
  exact (c1b_not_upto Hu).
Qed.

(** The (E vs S) hypothesis of (A)/(B) at [Q := is_open_term Γ]. *)
Theorem C1b_false_open (Γ : context) :
  (forall t t' u, is_open_term Γ t -> is_open_term Γ t' ->
     upto_domain t t' -> eta1 t u ->
     ∑ u', clos_refl eta1 t' u' × upto_domain u u') -> False.
Proof.
  intros H.
  destruct (c1b_open Γ) as [Ht Ht'].
  destruct (H _ _ _ Ht Ht' c1b_upto c1b_step) as (u' & Hr & Hu).
  apply clos_refl_rt, (rt_from_normal _ _ _ eta_normal_t') in Hr. subst u'.
  exact (c1b_not_upto Hu).
Qed.

(** Row C1b as pinned ([C1b_statement], [PCUICEtaBetaEta]); it is verbatim the
    C1b premise of [HR_A_instantiable]. *)
Theorem C1b_false : C1b_statement -> False.
Proof.
  intros H. apply (C1b_false_open []).
  intros t t' u _ _. exact (H t t' u).
Qed.


(** ** C4 itself is FALSE ([C4_statement], [PCUICEtaBetaEta])

   Same root cause one step further (EtaL2's witness). With [P := tSort sProp]:

     c4_s = λz:P. (P (λx:z. ((λy:P. y) x))) z         closed: the inner domain is z
     η then η:  c4_s →η c1b_t = λz:P. (P (λy:P. y)) z  →η c1b_u = P (λy:P. y)
     β:         c4_s →β c1b_t' = λz:P. (P (λx:z. x)) z

   [c1b_u] and [c1b_t'] are βη-normal in every [Σ]/[Γ] (proved by inversion on
   the [red1] and [eta1] constructors), and [upto_domain c1b_u c1b_t'] fails
   (application against λ). So the two reducts of [c4_s] have no common
   reduct modulo [upto_domain]. All premises of [C4_statement] are discharged at
   [default_checker_flags], [empty_global_env] (proved [wf]), [Γ := []]. *)

Definition c4_s : term :=
  tLambda c1b_na c1b_P
    (tApp (tApp c1b_P (tLambda c1b_na (tRel 0) (tApp (tLambda c1b_na c1b_P (tRel 0)) (tRel 0))))
          (tRel 0)).

(** Generic λ-normality, from normality of the domain and the body. *)
Lemma red_normal_lam Σ Γ na A b :
  (forall v, red1 Σ Γ A v -> False) ->
  (forall v, red1 Σ (Γ ,, vass na A) b v -> False) ->
  forall v, red1 Σ Γ (tLambda na A b) v -> False.
Proof.
  intros HA Hb v H. inv_red H; eauto.
Qed.

Lemma eta_normal_lam na A b :
  (forall v, eta1 A v -> False) ->
  (forall v, eta1 b v -> False) ->
  match b with tApp _ _ => False | _ => True end ->
  forall v, eta1 (tLambda na A b) v -> False.
Proof.
  intros HA Hb Hshape v H. inv_eta H; first [exact Hshape | eauto].
Qed.

(** *** (a) The two reductions *)

Lemma c4_s_eta_step : eta1 c4_s c1b_t.
Proof.
  unfold c4_s, c1b_t, c1b_u, c1b_P. cbn.
  apply abs_eta_r. apply app_eta_l. apply app_eta_r.
  exact (eta_red c1b_na (tLambda c1b_na (tSort sProp) (tRel 0)) (tRel 0)).
Qed.

Lemma c4_s_beta_step Σ Γ : red1 Σ Γ c4_s c1b_t'.
Proof.
  unfold c4_s, c1b_t', c1b_L.
  apply abs_red_r. apply app_red_l. apply app_red_r. apply abs_red_r.
  exact (red_beta Σ _ c1b_na c1b_P (tRel 0) (tRel 0)).
Qed.

Lemma c4_s_to_u Σ Γ : beta_eta Σ Γ c4_s c1b_u.
Proof.
  eapply rt_trans with (y := c1b_t).
  - apply rt_step. right. exact c4_s_eta_step.
  - apply rt_step. right. exact c1b_step.
Qed.

Lemma c4_s_to_t' Σ Γ : beta_eta Σ Γ c4_s c1b_t'.
Proof. apply rt_step. left. apply c4_s_beta_step. Qed.

(** *** (b) Normality of [c1b_u] ([c1b_t'] is [betaeta_normal_t'] above) *)

Lemma red_normal_u Σ Γ v : red1 Σ Γ c1b_u v -> False.
Proof.
  unfold c1b_u, c1b_P. intros H. inv_red H.
  - eapply red_normal_Sort; eassumption.
  - eapply (red_normal_lam _ _ _ _ _ (fun v => red_normal_Sort _ _ _ v)
                                     (fun v => red_normal_Rel0 _ _ _ _ v)).
    eassumption.
Qed.

Lemma eta_normal_u v : eta1 c1b_u v -> False.
Proof.
  unfold c1b_u, c1b_P. intros H. inv_eta H.
  - eapply eta_normal_Sort; eassumption.
  - eapply (eta_normal_lam _ _ _ (fun v => eta_normal_Sort _ v) (fun v => eta_normal_Rel _ v) I).
    eassumption.
Qed.

Lemma betaeta_normal_u Σ Γ v : beta_eta1 Σ Γ c1b_u v -> False.
Proof. intros [H|H]; [exact (red_normal_u _ _ _ H) | exact (eta_normal_u _ H)]. Qed.

(** *** (d) Side conditions *)

Lemma wf_empty_global_env {cf : checker_flags} : wf empty_global_env.
Proof.
  split.
  - split; [|split].
    + intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
    + intros x Hx.
      change (LevelSet.In x (LevelSet.union (ContextSet.levels ContextSet.empty)
                                            (LevelSet.singleton Level.lzero))) in Hx.
      apply LevelSet.union_spec in Hx as [Hx|Hx].
      * exfalso. eapply LevelSet.empty_spec. exact Hx.
      * apply LevelSet.singleton_spec in Hx. hnf in Hx. subst x. reflexivity.
    + exists {| valuation_mono := fun _ => 1%positive; valuation_poly := fun _ => 0 |}.
      intros x Hx. exfalso. eapply ConstraintSet.empty_spec. exact Hx.
  - constructor.
Qed.

Lemma closed_context_nil : is_closed_context ([] : context).
Proof. reflexivity. Qed.

Lemma c4_s_open : is_open_term ([] : context) c4_s.
Proof. vm_compute; reflexivity. Qed.

(** *** The refutation of C4 *)

Theorem C4_false : C4_statement -> False.
Proof.
  intros H.
  destruct (H default_checker_flags empty_global_env (@wf_empty_global_env default_checker_flags)
              [] c4_s c1b_u c1b_t' closed_context_nil c4_s_open
              (c4_s_to_u _ _) (c4_s_to_t' _ _)) as (u' & v' & Hu & Hv & HE).
  apply (rt_from_normal _ _ _ (betaeta_normal_u _ _)) in Hu.
  apply (rt_from_normal _ _ _ (betaeta_normal_t' _ _)) in Hv.
  subst u' v'. exact (c1b_not_upto HE).
Qed.
