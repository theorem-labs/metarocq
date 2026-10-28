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
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICReduction
     PCUICInduction PCUICCases PCUICEquality PCUICOnFreeVars PCUICTyping
     PCUICEtaDefs PCUICEtaBetaEta.

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


(** ** F1/F2: [E2] does NOT commute with [red1]

   [E2 := clos_refl_sym_trans (upto_domain ∪ eta1)] is the comparison of the
   design gate's repair (2). It is stated HERE, locally; no shared file changes.

   The blockage is in the REDUCTION, not in the comparison: η-expanding a case
   SCRUTINEE turns a constructor application into a λ, and iota does not fire on
   a λ. So a term that iota-reduces is [E2]-related to a term that cannot move at
   all, by β or by η.

   The inductive is a one-constructor, zero-parameter inductive [EtaC1b.I] with
   constructor 0; it is never looked up, since [red1]'s [red_iota] reads only the
   branch list and the arity equation, not the environment. F1 uses a branch of
   arity 0 and no arguments; F2 a branch of arity 1 and one argument. *)

Definition f_ci : case_info :=
  {| ci_ind := mkInd (MPfile ["EtaC1b"%bs], "I"%bs) 0; ci_npar := 0; ci_relevance := Relevant |}.
Definition f_p : predicate term :=
  {| pparams := []; puinst := []; pcontext := []; preturn := c1b_P |}.
Definition f_br : branch term := {| bcontext := []; bbody := c1b_P |}.
Definition f_br1 : branch term := {| bcontext := [vass c1b_na c1b_P]; bbody := c1b_P |}.
Definition f_C : term := tConstruct f_ci.(ci_ind) 0 [].

(** *** The [E2]-invariant: "contains a constructor", λ domains ignored.

   [upto_domain] ignores λ domains and [eta1] deletes one, so the invariant must
   ignore them too. Primitive values are given [false] on both sides, which is
   invariant because no [eta1] or [upto_domain] step relates a [tPrim] to a
   non-[tPrim]. *)

Fixpoint hasC (t : term) : bool :=
  match t with
  | tConstruct _ _ _ => true
  | tLambda _ _ b => hasC b
  | tProd _ a b => hasC a || hasC b
  | tLetIn _ b ty u => hasC b || hasC ty || hasC u
  | tApp u v => hasC u || hasC v
  | tEvar _ l => existsb hasC l
  | tCase _ p c brs =>
      existsb hasC p.(pparams) || hasC p.(preturn) || hasC c
      || existsb (fun br => hasC br.(bbody)) brs
  | tProj _ c => hasC c
  | tFix m _ => existsb (fun d => hasC d.(dtype) || hasC d.(dbody)) m
  | tCoFix m _ => existsb (fun d => hasC d.(dtype) || hasC d.(dbody)) m
  | _ => false
  end.

Lemma existsb_All_ext {A} (f g : A -> bool) l :
  All (fun x => f x = g x) l -> existsb f l = existsb g l.
Proof. induction 1; cbn; congruence. Qed.

Ltac hasC_rw :=
  repeat match goal with
  | H : forall k, hasC (lift _ k _) = hasC _ |- _ => rewrite H
  end.

Lemma hasC_lift n t : forall k, hasC (lift n k t) = hasC t.
Proof.
  induction t using term_forall_list_ind; intros k; cbn; hasC_rw; try reflexivity.
  all: try solve [ induction X; cbn; congruence ].
  all: try solve
    [ destruct X as (Hpars & _ & Hret); rewrite Hret;
      assert (HA : existsb hasC (map (lift n k) (pparams p)) = existsb hasC (pparams p))
        by (clear -Hpars; induction Hpars; cbn; congruence);
      assert (HD : existsb (fun br : branch term => hasC (bbody br))
                     (map_branches_k (lift n) id k l)
                   = existsb (fun br : branch term => hasC (bbody br)) l)
        by (clear -X0; induction X0; cbn; [reflexivity|];
            match goal with H : _ × _ |- _ => destruct H as [_ Hb]; rewrite Hb end;
            congruence);
      rewrite HA HD; reflexivity ].
  all: try solve
    [ repeat match goal with |- context [lift _ (#|?m| + ?K)] => generalize (#|m| + K)%nat; intro end;
      induction X; cbn; [reflexivity|];
      match goal with H : _ × _ |- _ => destruct H as [Ht Hb]; rewrite Ht Hb end;
      congruence ].
Qed.

Lemma All2_upto_existsb {l l'} :
  All (fun t => forall v, upto_domain t v -> hasC t = hasC v) l ->
  All2 upto_domain l l' -> existsb hasC l = existsb hasC l'.
Proof.
  intros H a. pose proof (All2_All_mix_left H a) as a'. clear H a.
  induction a'; cbn; [reflexivity|].
  destruct r as [Hh Hr]. rewrite (Hh _ Hr) IHa'. reflexivity.
Qed.

Lemma hasC_upto t : forall v, upto_domain t v -> hasC t = hasC v.
Proof.
  induction t using term_forall_list_ind; intros v e; depelim e; cbn [hasC];
    repeat match goal with
    | H : forall v, upto_domain ?x v -> hasC ?x = hasC v, E : upto_domain ?x _ |- _ =>
        rewrite (H _ E); clear H E
    end;
    try reflexivity.
  (* Evar *)
  all: try solve [ match goal with
                   | X : All _ ?l, A : All2 upto_domain ?l ?l' |- _ =>
                       exact (All2_upto_existsb X A)
                   end ].
  (* Case *)
  all: try solve
    [ destruct X as (Hpars & _ & Hret);
      match goal with
      | A : All2 upto_domain (pparams _) (pparams _) |- _ =>
          rewrite (All2_upto_existsb Hpars A)
      end;
      match goal with
      | R : upto_domain (preturn _) (preturn _) |- _ => rewrite (Hret _ R)
      end;
      f_equal;
      match goal with
      | B : All2 _ ?brs ?brs' |- _ => pose proof (All2_All_mix_left X0 B) as bb; clear B X0
      end;
      induction bb; cbn; [reflexivity|];
      destruct r as [[_ Hbb] [_ Hr]]; rewrite (Hbb _ Hr) IHbb; reflexivity ].
  (* Fix / CoFix *)
  all: try solve
    [ match goal with
      | A : All2 _ ?m ?m' |- _ => pose proof (All2_All_mix_left X A) as mm; clear A X
      end;
      induction mm; cbn; [reflexivity|];
      destruct r as [[Hd Hb] (Ht & Hbo & _)];
      rewrite (Hd _ Ht) (Hb _ Hbo) IHmm; reflexivity ].
Qed.

Lemma OnOne2_hasC {l l'} :
  OnOne2 (Trel_conj eta1 (fun t u => hasC t = hasC u)) l l' ->
  existsb hasC l = existsb hasC l'.
Proof.
  induction 1; cbn; [|congruence].
  match goal with H : _ × _ |- _ => destruct H as [_ He] end. congruence.
Qed.

Lemma OnOne2_hasC_br {brs brs'} :
  OnOne2 (on_Trel_eq (Trel_conj eta1 (fun t u => hasC t = hasC u)) bbody bcontext) brs brs' ->
  existsb (fun br : branch term => hasC (bbody br)) brs
  = existsb (fun br : branch term => hasC (bbody br)) brs'.
Proof.
  induction 1; cbn; [|congruence].
  match goal with H : _ × _ |- _ => destruct H as [[_ He] _] end. congruence.
Qed.

Lemma OnOne2_hasC_mfix_ty {m m'} :
  OnOne2 (on_Trel_eq (Trel_conj eta1 (fun t u => hasC t = hasC u)) dtype
                     (fun x => (dname x, dbody x, rarg x))) m m' ->
  existsb (fun d : def term => hasC (dtype d) || hasC (dbody d)) m
  = existsb (fun d : def term => hasC (dtype d) || hasC (dbody d)) m'.
Proof.
  induction 1; cbn; [|congruence].
  match goal with H : _ × _ |- _ => destruct H as [[_ He] Heq] end.
  unfold on_Trel in Heq; cbn in Heq. injection Heq; intros; congruence.
Qed.

Lemma OnOne2_hasC_mfix_body {m m'} :
  OnOne2 (on_Trel_eq (Trel_conj eta1 (fun t u => hasC t = hasC u)) dbody
                     (fun x => (dname x, dtype x, rarg x))) m m' ->
  existsb (fun d : def term => hasC (dtype d) || hasC (dbody d)) m
  = existsb (fun d : def term => hasC (dtype d) || hasC (dbody d)) m'.
Proof.
  induction 1; cbn; [|congruence].
  match goal with H : _ × _ |- _ => destruct H as [[_ He] Heq] end.
  unfold on_Trel in Heq; cbn in Heq. injection Heq; intros; congruence.
Qed.

Lemma hasC_eta1 t u : eta1 t u -> hasC t = hasC u.
Proof.
  revert t u. apply (eta1_ind_all (fun t u => hasC t = hasC u)); intros; cbn;
    rewrite ?hasC_lift ?orb_false_r;
    repeat match goal with H : hasC _ = hasC _ |- _ => rewrite H end;
    try reflexivity.
  all: try solve [ first [ erewrite OnOne2_hasC by eassumption
                         | erewrite OnOne2_hasC_br by eassumption
                         | erewrite OnOne2_hasC_mfix_ty by eassumption
                         | erewrite OnOne2_hasC_mfix_body by eassumption ]; reflexivity ].
Qed.

Definition E2 : term -> term -> Type :=
  clos_refl_sym_trans (fun t u => (upto_domain t u + eta1 t u)%type).

Lemma hasC_E2 t u : E2 t u -> hasC t = hasC u.
Proof.
  induction 1.
  - destruct r as [H|H]; [now apply hasC_upto | now apply hasC_eta1].
  - reflexivity.
  - now symmetry.
  - etransitivity; eassumption.
Qed.

Lemma not_E2_sort t : hasC t = true -> E2 t c1b_P -> False.
Proof. intros Ht H. apply hasC_E2 in H. rewrite Ht in H. discriminate H. Qed.

(** *** The witnesses *)

Definition f_L : term := tLambda c1b_na (tRel 0) (tRel 0).      (* λw:x. w, x the outer binder *)
Definition f_LS : term := tLambda c1b_na c1b_P (tRel 0).         (* λw:P. w, closed *)

Definition f_a : term := tCase f_ci f_p f_C [f_br].
Definition f_a' : term := tCase f_ci f_p (tLambda c1b_na c1b_P (tApp f_C (tRel 0))) [f_br].

Definition f_y : term :=
  tCase f_ci f_p (tLambda c1b_na c1b_P (tApp (tApp f_C f_L) (tRel 0))) [f_br1].
Definition f_y2 : term :=
  tCase f_ci f_p (tLambda c1b_na c1b_P (tApp (tApp f_C f_LS) (tRel 0))) [f_br1].
Definition f_z : term := tCase f_ci f_p (tApp f_C f_LS) [f_br1].

(** *** Inversion helpers for [mkApps]-headed [red1] rules *)

Lemma mkApps_eq_Lambda f args na A b :
  ~~ isApp f -> mkApps f args = tLambda na A b -> f = tLambda na A b.
Proof.
  intros Hf E. apply (f_equal decompose_app) in E.
  rewrite (decompose_app_mkApps f args Hf) in E. cbn in E. now injection E.
Qed.

Lemma mkApps_Construct_not_Lambda ind n u args na A b :
  mkApps (tConstruct ind n u) args = tLambda na A b -> False.
Proof. intros E. apply mkApps_eq_Lambda in E; [discriminate E | reflexivity]. Qed.

Lemma mkApps_CoFix_not_Lambda mfix idx args na A b :
  mkApps (tCoFix mfix idx) args = tLambda na A b -> False.
Proof. intros E. apply mkApps_eq_Lambda in E; [discriminate E | reflexivity]. Qed.

(** *** (a) The reductions and the [E2] relations *)

Lemma f_a'_eta : eta1 f_a' f_a.
Proof.
  unfold f_a', f_a. apply case_eta_discr. exact (eta_red c1b_na f_C c1b_P).
Qed.

Lemma f_a_iota Σ Γ : red1 Σ Γ f_a c1b_P.
Proof.
  unfold f_a.
  assert (E : iota_red 0 f_p [] f_br = c1b_P) by (vm_compute; reflexivity).
  rewrite <- E. exact (red_iota Σ Γ f_ci 0 [] [] f_p [f_br] f_br eq_refl eq_refl).
Qed.

Lemma f_z_iota Σ Γ : red1 Σ Γ f_z c1b_P.
Proof.
  unfold f_z.
  assert (E : iota_red 0 f_p [f_LS] f_br1 = c1b_P) by (vm_compute; reflexivity).
  rewrite <- E. exact (red_iota Σ Γ f_ci 0 [] [f_LS] f_p [f_br1] f_br1 eq_refl eq_refl).
Qed.

Lemma f_y_upto : upto_domain f_y f_y2.
Proof.
  unfold f_y, f_y2, f_p, f_br1, f_L, f_LS, f_C, c1b_P.
  apply utd_Case; cbn.
  - constructor.
  - reflexivity.
  - reflexivity.
  - constructor.
  - repeat constructor.
  - constructor; [|constructor]. split; [reflexivity|constructor].
Qed.

Lemma f_y2_eta : eta1 f_y2 f_z.
Proof.
  unfold f_y2, f_z. apply case_eta_discr.
  exact (eta_red c1b_na (tApp f_C f_LS) c1b_P).
Qed.

Lemma E2_step_upto t u : upto_domain t u -> E2 t u.
Proof. intros H. apply rst_step. now left. Qed.

Lemma E2_step_eta t u : eta1 t u -> E2 t u.
Proof. intros H. apply rst_step. now right. Qed.

Lemma f_a_E2 : E2 f_a f_a'.
Proof. apply rst_sym. apply E2_step_eta. exact f_a'_eta. Qed.

Lemma f_z_E2 : E2 f_z f_y.
Proof.
  apply rst_sym. eapply rst_trans.
  - apply E2_step_upto. exact f_y_upto.
  - apply E2_step_eta. exact f_y2_eta.
Qed.

(** *** (c) [f_a'] and [f_y] are normal *)

Lemma red_normal_Construct Σ Γ ind n u v : red1 Σ Γ (tConstruct ind n u) v -> False.
Proof. intros H. inv_red H. Qed.

Lemma eta_normal_Construct ind n u v : eta1 (tConstruct ind n u) v -> False.
Proof. intros H. inv_eta H. Qed.

Lemma red_normal_appC Σ Γ na A v :
  red1 Σ (Γ ,, vass na A) (tApp f_C (tRel 0)) v -> False.
Proof.
  unfold f_C. intros H. inv_red H.
  - eapply red_normal_Construct; eassumption.
  - eapply red_normal_Rel0; eassumption.
Qed.

Lemma red_normal_a'_scrut Σ Γ v :
  red1 Σ Γ (tLambda c1b_na c1b_P (tApp f_C (tRel 0))) v -> False.
Proof.
  apply red_normal_lam.
  - intros x. unfold c1b_P. apply red_normal_Sort.
  - intros x. apply red_normal_appC.
Qed.

Lemma red_normal_case1 Σ Γ ci p c br v :
  pparams p = [] ->
  (forall Δ x, red1 Σ (Γ ,,, Δ) (preturn p) x -> False) ->
  (forall x, red1 Σ Γ c x -> False) ->
  (forall Δ x, red1 Σ (Γ ,,, Δ) (bbody br) x -> False) ->
  (forall ind n u args, c = mkApps (tConstruct ind n u) args -> False) ->
  (forall mfix idx args, c = mkApps (tCoFix mfix idx) args -> False) ->
  red1 Σ Γ (tCase ci p c [br]) v -> False.
Proof.
  intros Hpar Hret Hc Hbr Hcon Hcof H. inv_red H.
  all: first
    [ solve [eapply Hcon; reflexivity]
    | solve [eapply Hcof; reflexivity]
    | solve [eapply Hcon; symmetry; eassumption]
    | solve [eapply Hcof; symmetry; eassumption]
    | solve [eapply Hcon; eassumption]
    | solve [eapply Hcof; eassumption]
    | solve [eapply Hret; eassumption]
    | solve [eapply Hc; eassumption]
    | solve [match goal with o : OnOne2 _ (pparams _) _ |- _ => rewrite Hpar in o; depelim o end]
    | solve [match goal with o : OnOne2 _ [_] _ |- _ => depelim o end;
             [ match goal with Hp : _ × _ |- _ => destruct Hp as [Hb _]; eapply Hbr; exact Hb end
             | match goal with o : OnOne2 _ _ _ |- _ => depelim o end ]] ].
Qed.

Lemma red_normal_a' Σ Γ v : red1 Σ Γ f_a' v -> False.
Proof.
  unfold f_a'. apply red_normal_case1.
  - reflexivity.
  - intros Δ x. cbn. unfold c1b_P. apply red_normal_Sort.
  - intros x. apply red_normal_a'_scrut.
  - intros Δ x. cbn. unfold c1b_P. apply red_normal_Sort.
  - intros ind n u args E. eapply mkApps_Construct_not_Lambda. symmetry; exact E.
  - intros mfix idx args E. eapply mkApps_CoFix_not_Lambda. symmetry; exact E.
Qed.

Lemma lift_1_0_not_CL T : lift 1 0 T = tApp f_C f_L -> False.
Proof.
  unfold f_C, f_L. intros E.
  destruct T; cbn in E; try discriminate E.
  match type of E with tApp _ (lift 1 0 ?T2) = _ => destruct T2; cbn in E; try discriminate E end.
  injection E; intros; eapply lift_1_0_not_Rel0; eassumption.
Qed.

Lemma red_normal_fL Σ Γ na A v : red1 Σ (Γ ,, vass na A) f_L v -> False.
Proof.
  unfold f_L. apply red_normal_lam.
  - intros x. apply red_normal_Rel0.
  - intros x. apply red_normal_Rel0.
Qed.

Lemma eta_normal_L' v : eta1 f_L v -> False.
Proof.
  unfold f_L. apply eta_normal_lam.
  - intros x. apply eta_normal_Rel.
  - intros x. apply eta_normal_Rel.
  - exact I.
Qed.

Lemma red_normal_y_scrut Σ Γ v :
  red1 Σ Γ (tLambda c1b_na c1b_P (tApp (tApp f_C f_L) (tRel 0))) v -> False.
Proof.
  apply red_normal_lam.
  - intros x. unfold c1b_P. apply red_normal_Sort.
  - intros x H. inv_red H.
    + (* app_red_l on (tApp f_C f_L) *)
      match goal with H : red1 _ _ (tApp f_C f_L) _ |- _ => rename H into Hl end.
      unfold f_C in Hl. inv_red Hl.
      * eapply red_normal_Construct; eassumption.
      * eapply red_normal_fL; eassumption.
    + eapply red_normal_Rel0; eassumption.
Qed.

Lemma eta_normal_y_scrut v :
  eta1 (tLambda c1b_na c1b_P (tApp (tApp f_C f_L) (tRel 0))) v -> False.
Proof.
  intros H. inv_eta H.
  - (* eta_red: the function part would have to be a lift *)
    eapply lift_1_0_not_CL; eassumption.
  - (* abs_eta_l: the domain *)
    unfold c1b_P in *. eapply eta_normal_Sort; eassumption.
  - (* abs_eta_r: the body *)
    match goal with H : eta1 (tApp (tApp f_C f_L) (tRel 0)) _ |- _ => rename H into Hb end.
    inv_eta Hb.
    + match goal with H : eta1 (tApp f_C f_L) _ |- _ => rename H into Hl end.
      unfold f_C in Hl. inv_eta Hl.
      * eapply eta_normal_Construct; eassumption.
      * eapply eta_normal_L'; eassumption.
    + eapply eta_normal_Rel; eassumption.
Qed.

Lemma red_normal_y Σ Γ v : red1 Σ Γ f_y v -> False.
Proof.
  unfold f_y. apply red_normal_case1.
  - reflexivity.
  - intros Δ x. cbn. unfold c1b_P. apply red_normal_Sort.
  - intros x. apply red_normal_y_scrut.
  - intros Δ x. cbn. unfold c1b_P. apply red_normal_Sort.
  - intros ind n u args E. eapply mkApps_Construct_not_Lambda. symmetry; exact E.
  - intros mfix idx args E. eapply mkApps_CoFix_not_Lambda. symmetry; exact E.
Qed.

Lemma eta_normal_y v : eta1 f_y v -> False.
Proof.
  unfold f_y, f_p, f_br1 in *. intros H. inv_eta H.
  all: first
    [ solve [eapply eta_normal_y_scrut; eassumption]
    | solve [cbn in *; unfold c1b_P in *; eapply eta_normal_Sort; eassumption]
    | solve [match goal with o : OnOne2 _ _ _ |- _ => cbn in o; depelim o end]
    | solve [match goal with o : OnOne2 _ _ _ |- _ => cbn in o; depelim o end;
             [ match goal with Hp : _ × _ |- _ =>
                 destruct Hp as [Hb _]; cbn in Hb; unfold c1b_P in Hb;
                 eapply eta_normal_Sort; exact Hb end
             | match goal with o : OnOne2 _ _ _ |- _ => depelim o end ]] ].
Qed.

Lemma betaeta_normal_y Σ Γ v : beta_eta1 Σ Γ f_y v -> False.
Proof. intros [H|H]; [exact (red_normal_y _ _ _ H) | exact (eta_normal_y _ H)]. Qed.

(** *** (d) The refutations *)

Lemma hasC_f_a' : hasC f_a' = true.
Proof. reflexivity. Qed.

Lemma hasC_f_y : hasC f_y = true.
Proof. reflexivity. Qed.

(** F1: [E2] does not commute with [red1]: [f_a] iota-reduces to [c1b_P], it is
    [E2]-related to [f_a'], and [f_a'] has no [red1] step at all. *)
Theorem E2_red_no_commute :
  (forall (Σ : global_env) (Γ : context) (t t' u : term),
     E2 t t' -> red1 Σ Γ t u ->
     ∑ u', clos_refl_trans (red1 Σ Γ) t' u' × E2 u u') -> False.
Proof.
  intros H.
  destruct (H empty_global_env [] f_a f_a' c1b_P f_a_E2 (f_a_iota _ _)) as (u' & Hr & HE).
  apply (rt_from_normal _ _ _ (red_normal_a' empty_global_env [])) in Hr. subst u'.
  exact (not_E2_sort _ hasC_f_a' (rst_sym _ _ _ HE)).
Qed.

(** F2: the stronger form. [f_y] has no step at all — not even an η step — so
    keeping η steps in the joins does not rescue the route: the blockage is in
    the REDUCTION (iota does not fire on an η-expanded scrutinee), not in the
    comparison. *)
Theorem E2_red_no_commute_strong :
  (forall (Σ : global_env) (Γ : context) (t t' u : term),
     E2 t t' -> red1 Σ Γ t u ->
     ∑ u', clos_refl_trans (beta_eta1 Σ Γ) t' u' × E2 u u') -> False.
Proof.
  intros H.
  destruct (H empty_global_env [] f_z f_y c1b_P f_z_E2 (f_z_iota _ _)) as (u' & Hr & HE).
  apply (rt_from_normal _ _ _ (betaeta_normal_y empty_global_env [])) in Hr. subst u'.
  exact (not_E2_sort _ hasC_f_y (rst_sym _ _ _ HE)).
Qed.

(** ** [t0]: βη-confluence modulo [E2] is FALSE (design gate r2, S4)

   EtaRepairSound's witness ([lanes/eta/plan-gate-r2.md:119-125]): [s] with its
   head replaced by a constructor, under a projection. With [S := c1b_P]:

     t0 = tProj p (λz:S. (C (λx:z. ((λy:S.y) x))) z)       closed; the inner domain is z
     η, η, red_proj:  t0 ⇝ λy:S.y                           = N1
     β:               t0 ⇝ tProj p (λz:S. (C (λx:z.x)) z)  = N2

   [N1] and [N2] are βη-normal in every [Σ]/[Γ], and they are not [E2]-related:
   [N2] contains a constructor and [N1] does not ([hasC_E2]). So the conclusion
   that §6.1 priced ("βη-confluence modulo [E2]") is false, not only its premise.
   Under the canonical-domain route that replaced it ([canon_beta_eta_confluence],
   [PCUICEtaCanonC4.v]) [canon t0] joins: β, then the now-unblocked η, then
   [red_proj], reaches [λx:S.x = canon N1]. *)

Definition t0_p : projection := {| proj_ind := f_ci.(ci_ind); proj_npars := 0; proj_arg := 0 |}.
Definition t0_inner : term := tLambda c1b_na (tRel 0) (tApp f_LS (tRel 0)).   (* λx:z. ((λy:S.y) x) *)
Definition t0 : term := tProj t0_p (tLambda c1b_na c1b_P (tApp (tApp f_C t0_inner) (tRel 0))).
Definition t0_N1 : term := f_LS.
Definition t0_N2 : term := tProj t0_p (tLambda c1b_na c1b_P (tApp (tApp f_C f_L) (tRel 0))).

Lemma t0_eta1 : eta1 t0 (tProj t0_p (tLambda c1b_na c1b_P (tApp (tApp f_C f_LS) (tRel 0)))).
Proof.
  unfold t0, t0_inner. apply proj_eta. apply abs_eta_r. apply app_eta_l. apply app_eta_r.
  exact (eta_red c1b_na f_LS (tRel 0)).
Qed.

Lemma t0_eta2 :
  eta1 (tProj t0_p (tLambda c1b_na c1b_P (tApp (tApp f_C f_LS) (tRel 0)))) (tProj t0_p (tApp f_C f_LS)).
Proof. apply proj_eta. exact (eta_red c1b_na (tApp f_C f_LS) c1b_P). Qed.

Lemma t0_proj Σ Γ : red1 Σ Γ (tProj t0_p (tApp f_C f_LS)) t0_N1.
Proof. exact (red_proj Σ Γ t0_p [f_LS] [] f_LS eq_refl). Qed.

Lemma t0_beta Σ Γ : red1 Σ Γ t0 t0_N2.
Proof.
  unfold t0, t0_inner, t0_N2, f_L, f_LS.
  apply proj_red. apply abs_red_r. apply app_red_l. apply app_red_r. apply abs_red_r.
  exact (red_beta Σ _ c1b_na c1b_P (tRel 0) (tRel 0)).
Qed.

Lemma t0_to_N1 Σ Γ : beta_eta Σ Γ t0 t0_N1.
Proof.
  eapply rt_trans; [apply rt_step; right; exact t0_eta1|].
  eapply rt_trans; [apply rt_step; right; exact t0_eta2|].
  apply rt_step; left; apply t0_proj.
Qed.

Lemma t0_to_N2 Σ Γ : beta_eta Σ Γ t0 t0_N2.
Proof. apply rt_step; left; apply t0_beta. Qed.

Lemma betaeta_normal_N1 Σ Γ v : beta_eta1 Σ Γ t0_N1 v -> False.
Proof.
  unfold t0_N1, f_LS, c1b_P. intros [H|H].
  - exact (red_normal_lam _ _ _ _ _ (fun v => red_normal_Sort _ _ _ v) (fun v => red_normal_Rel0 _ _ _ _ v) v H).
  - exact (eta_normal_lam _ _ _ (fun v => eta_normal_Sort _ v) (fun v => eta_normal_Rel _ v) I v H).
Qed.

Lemma red_normal_N2 Σ Γ v : red1 Σ Γ t0_N2 v -> False.
Proof.
  unfold t0_N2. intros H. inv_red H.
  all: first
    [ solve [eapply mkApps_Construct_not_Lambda; symmetry; eassumption]
    | solve [eapply mkApps_Construct_not_Lambda; eassumption]
    | solve [eapply mkApps_CoFix_not_Lambda; symmetry; eassumption]
    | solve [eapply mkApps_CoFix_not_Lambda; eassumption]
    | solve [eapply red_normal_y_scrut; eassumption] ].
Qed.

Lemma eta_normal_N2 v : eta1 t0_N2 v -> False.
Proof. unfold t0_N2. intros H. inv_eta H. eapply eta_normal_y_scrut; eassumption. Qed.

Lemma betaeta_normal_N2 Σ Γ v : beta_eta1 Σ Γ t0_N2 v -> False.
Proof. intros [H|H]; [exact (red_normal_N2 _ _ _ H) | exact (eta_normal_N2 _ H)]. Qed.

Lemma t0_open : is_open_term ([] : context) t0.
Proof. vm_compute; reflexivity. Qed.

(** The refutation, with every premise of [C4_statement] discharged and the
    comparison widened from [upto_domain] to [E2]. *)
Theorem betaeta_confluence_mod_E2_false :
  (forall (cf : checker_flags) (Σ : global_env) (wfΣ : wf Σ) (Γ : context) (t u v : term),
     is_closed_context Γ -> is_open_term Γ t ->
     beta_eta Σ Γ t u -> beta_eta Σ Γ t v ->
     ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × E2 u' v') -> False.
Proof.
  intros H.
  destruct (H default_checker_flags empty_global_env (@wf_empty_global_env default_checker_flags)
              [] t0 t0_N1 t0_N2 closed_context_nil t0_open (t0_to_N1 _ _) (t0_to_N2 _ _))
    as (u' & v' & Hu & Hv & HE).
  apply (rt_from_normal _ _ _ (betaeta_normal_N1 _ _)) in Hu.
  apply (rt_from_normal _ _ _ (betaeta_normal_N2 _ _)) in Hv.
  subst u' v'. apply hasC_E2 in HE. vm_compute in HE. discriminate HE.
Qed.

(** ** Typed C1b is false too (plan.md §6.1, the correction to the correction)

   The witnesses above are ill-typed (a sort applied to an argument), so they
   say nothing about a TYPED C1b. This one is well-typed, with
   [Γ := [A : Prop]] ([tc_Γ0]; [Prop] keeps the universe side conditions
   trivial, nothing below depends on it being [Prop]):

     t  = λx:A. (λy:A. y) x                 η-contracts to  u = λy:A. y
     t' = λx:A. (λy:((λw:A. A) x). y) x     upto_domain t t', and t' has NO η step

   [t'] is η-normal because [x] occurs in the inner domain, and [lift0 1 _] never
   contains variable 0. The domain is a REDEX that reduces to [A], so [t'] is
   well-typed: the argument [x : A] is accepted at [(λw:A. A) x] by one β step in
   the cumulativity. So typing does not rescue C1b. *)

From MetaRocq.PCUIC Require Import PCUICCumulativitySpec.

Section TypedC1b.
  #[local] Existing Instance default_checker_flags.

  Definition tc_Σ : global_env_ext := (empty_global_env, Monomorphic_ctx).
  Definition tc_A : term := tSort sProp.
  Definition tc_Γ0 : context := [vass c1b_na tc_A].
  Definition tc_Γ1 : context := tc_Γ0 ,, vass c1b_na (tRel 0).
  Definition tc_u : term := tLambda c1b_na (tRel 0) (tRel 0).
  Definition tc_t : term := tLambda c1b_na (tRel 0) (tApp (tLambda c1b_na (tRel 1) (tRel 0)) (tRel 0)).
  Definition tc_D : term := tApp (tLambda c1b_na (tRel 1) (tRel 2)) (tRel 0).
  Definition tc_t' : term := tLambda c1b_na (tRel 0) (tApp (tLambda c1b_na tc_D (tRel 0)) (tRel 0)).
  Definition tc_Γ3 : context := tc_Γ1 ,, vass c1b_na tc_D.

  (** *** Typing *)

  Lemma tc_vass (Γ : context) (na : aname) A s :
    tc_Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing tc_Σ Γ (j_vass na A).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [exact I|exact r]. Qed.

  Lemma tc_vass_s (Γ : context) (na : aname) A s :
    tc_Σ ;;; Γ |- A : tSort s -> isSortRel s na.(binder_relevance) ->
    lift_typing typing tc_Σ Γ (j_vass_s na A s).
  Proof. intros h r. split; [exact tt|]. exists s. split; [exact h|]. split; [reflexivity|exact r]. Qed.

  Lemma tc_wf0 : wf_local tc_Σ tc_Γ0.
  Proof.
    apply localenv_cons_abs; [constructor|].
    apply (tc_vass [] c1b_na tc_A (Sort.super sProp)); [|reflexivity].
    apply type_Sort; [constructor|cbn; trivial].
  Qed.

  Lemma tc_wf1 : wf_local tc_Σ tc_Γ1.
  Proof.
    apply localenv_cons_abs; [exact tc_wf0|].
    apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 0 (vass c1b_na tc_A) tc_wf0 eq_refl)|reflexivity].
  Qed.

  Lemma tc_wf2 : wf_local tc_Σ (tc_Γ1 ,, vass c1b_na (tRel 1)).
  Proof.
    apply localenv_cons_abs; [exact tc_wf1|].
    apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 1 (vass c1b_na tc_A) tc_wf1 eq_refl)|reflexivity].
  Qed.

  Lemma tc_D_typed : tc_Σ ;;; tc_Γ1 |- tc_D : tSort sProp.
  Proof.
    refine (type_App _ _ (tLambda c1b_na (tRel 1) (tRel 2)) c1b_na (tRel 1) (tSort sProp)
              (Sort.sort_of_product sProp (Sort.super sProp)) (tRel 0) _ _ _).
    - apply type_Prod.
      + apply (tc_vass_s _ _ _ sProp); [exact (type_Rel _ _ 1 (vass c1b_na tc_A) tc_wf1 eq_refl)|reflexivity].
      + apply type_Sort; [exact tc_wf2|cbn; trivial].
    - apply type_Lambda.
      + apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 1 (vass c1b_na tc_A) tc_wf1 eq_refl)|reflexivity].
      + exact (type_Rel _ _ 2 (vass c1b_na tc_A) tc_wf2 eq_refl).
    - exact (type_Rel _ _ 0 (vass c1b_na (tRel 0)) tc_wf1 eq_refl).
  Qed.

  Lemma tc_wf3 : wf_local tc_Σ tc_Γ3.
  Proof. apply localenv_cons_abs; [exact tc_wf1|]. exact (tc_vass _ c1b_na _ sProp tc_D_typed ltac:(reflexivity)). Qed.

  Lemma tc_wf3w : wf_local tc_Σ (tc_Γ3 ,, vass c1b_na (tRel 2)).
  Proof.
    apply localenv_cons_abs; [exact tc_wf3|].
    apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 2 (vass c1b_na tc_A) tc_wf3 eq_refl)|reflexivity].
  Qed.

  Lemma tc_liftD_typed : tc_Σ ;;; tc_Γ3 |- lift0 1 tc_D : tSort sProp.
  Proof.
    refine (type_App _ _ (tLambda c1b_na (tRel 2) (tRel 3)) c1b_na (tRel 2) (tSort sProp)
              (Sort.sort_of_product sProp (Sort.super sProp)) (tRel 1) _ _ _).
    - apply type_Prod.
      + apply (tc_vass_s _ _ _ sProp); [exact (type_Rel _ _ 2 (vass c1b_na tc_A) tc_wf3 eq_refl)|reflexivity].
      + apply type_Sort; [exact tc_wf3w|cbn; trivial].
    - apply type_Lambda.
      + apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 2 (vass c1b_na tc_A) tc_wf3 eq_refl)|reflexivity].
      + exact (type_Rel _ _ 3 (vass c1b_na tc_A) tc_wf3w eq_refl).
    - exact (type_Rel _ _ 1 (vass c1b_na (tRel 0)) tc_wf3 eq_refl).
  Qed.

  Lemma tc_t'_typed : tc_Σ ;;; tc_Γ0 |- tc_t' : tProd c1b_na (tRel 0) tc_D.
  Proof.
    apply type_Lambda.
    - apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 0 (vass c1b_na tc_A) tc_wf0 eq_refl)|reflexivity].
    - refine (type_App _ _ (tLambda c1b_na tc_D (tRel 0)) c1b_na tc_D (lift0 1 tc_D)
                (Sort.sort_of_product sProp sProp) (tRel 0) _ _ _).
      + apply type_Prod; [exact (tc_vass_s _ c1b_na _ sProp tc_D_typed ltac:(reflexivity))|exact tc_liftD_typed].
      + apply type_Lambda; [exact (tc_vass _ c1b_na _ sProp tc_D_typed ltac:(reflexivity))|].
        exact (type_Rel _ _ 0 (vass c1b_na tc_D) tc_wf3 eq_refl).
      + eapply type_Cumul; [exact (type_Rel _ _ 0 (vass c1b_na (tRel 0)) tc_wf1 eq_refl)|exact tc_D_typed|].
        apply cumul_Sym. exact (cumul_beta _ _ _ c1b_na (tRel 1) (tRel 2) (tRel 0)).
  Qed.

  Lemma tc_t_typed : tc_Σ ;;; tc_Γ0 |- tc_t : tProd c1b_na (tRel 0) (tRel 1).
  Proof.
    apply type_Lambda.
    - apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 0 (vass c1b_na tc_A) tc_wf0 eq_refl)|reflexivity].
    - refine (type_App _ _ (tLambda c1b_na (tRel 1) (tRel 0)) c1b_na (tRel 1) (tRel 2)
                (Sort.sort_of_product sProp sProp) (tRel 0) _ _ _).
      + apply type_Prod.
        * apply (tc_vass_s _ _ _ sProp); [exact (type_Rel _ _ 1 (vass c1b_na tc_A) tc_wf1 eq_refl)|reflexivity].
        * exact (type_Rel _ _ 2 (vass c1b_na tc_A) tc_wf2 eq_refl).
      + apply type_Lambda.
        * apply (tc_vass _ _ _ sProp); [exact (type_Rel _ _ 1 (vass c1b_na tc_A) tc_wf1 eq_refl)|reflexivity].
        * exact (type_Rel _ _ 0 (vass c1b_na (tRel 1)) tc_wf2 eq_refl).
      + exact (type_Rel _ _ 0 (vass c1b_na (tRel 0)) tc_wf1 eq_refl).
  Qed.

  (** *** The η facts *)

  Lemma tc_eta : eta1 tc_t tc_u.
  Proof. exact (eta_red c1b_na tc_u (tRel 0)). Qed.

  Lemma tc_upto : upto_domain tc_t tc_t'.
  Proof. unfold tc_t, tc_t', tc_D. repeat constructor. Qed.

  Lemma tc_not_upto : upto_domain tc_u tc_t' -> False.
  Proof.
    unfold tc_u, tc_t'. intros H. inversion H; subst.
    match goal with h : upto_domain (tRel _) _ |- _ => inversion h end.
  Qed.

  Lemma tc_eta_normal_lamRel n m v : eta1 (tLambda c1b_na (tRel n) (tRel m)) v -> False.
  Proof. intros H. inv_eta H; first [congruence | eapply eta_normal_Rel; eassumption]. Qed.

  Lemma tc_eta_normal_D v : eta1 tc_D v -> False.
  Proof.
    unfold tc_D. intros H. inv_eta H.
    all: first [eapply tc_eta_normal_lamRel; eassumption | eapply eta_normal_Rel; eassumption].
  Qed.

  Lemma tc_eta_normal_lamD v : eta1 (tLambda c1b_na tc_D (tRel 0)) v -> False.
  Proof.
    intros H. inv_eta H.
    all: first [congruence | eapply tc_eta_normal_D; eassumption | eapply eta_normal_Rel; eassumption].
  Qed.

  Lemma tc_eta_normal_body' v : eta1 (tApp (tLambda c1b_na tc_D (tRel 0)) (tRel 0)) v -> False.
  Proof.
    intros H. inv_eta H.
    all: first [eapply tc_eta_normal_lamD; eassumption | eapply eta_normal_Rel; eassumption].
  Qed.

  (** The inner domain mentions variable 0 ([x]), so the function part of [t']'s
      body is not a lift. *)
  Lemma lift_1_0_not_lamD T : lift 1 0 T = tLambda c1b_na tc_D (tRel 0) -> False.
  Proof.
    unfold tc_D. intros E. destruct T; cbn in E; try discriminate E.
    injection E as _ e2 _.
    match type of e2 with lift 1 0 ?X = _ => destruct X end; cbn in e2; try discriminate e2.
    injection e2 as _ e5. exact (lift_1_0_not_Rel0 _ e5).
  Qed.

  Lemma tc_eta_normal_t' v : eta1 tc_t' v -> False.
  Proof.
    unfold tc_t'. intros H. inv_eta H.
    all: first
      [ eapply lift_1_0_not_lamD; eassumption
      | eapply lift_1_0_not_lamD; symmetry; eassumption
      | eapply eta_normal_Rel; eassumption
      | eapply tc_eta_normal_body'; eassumption ].
  Qed.

  (** *** The refutation *)

  Theorem C1b_false_typed :
    (forall (Σ : global_env_ext) (Γ : context) (t t' u T T' : term),
       wf Σ.1 -> Σ ;;; Γ |- t : T -> Σ ;;; Γ |- t' : T' ->
       upto_domain t t' -> eta1 t u ->
       ∑ u', clos_refl eta1 t' u' × upto_domain u u') -> False.
  Proof.
    intros H.
    destruct (H tc_Σ tc_Γ0 tc_t tc_t' tc_u _ _ (@wf_empty_global_env default_checker_flags)
                tc_t_typed tc_t'_typed tc_upto tc_eta) as (u' & hr & he).
    destruct hr as [? h|]; [exact (tc_eta_normal_t' _ h)|exact (tc_not_upto he)].
  Qed.

End TypedC1b.
