(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, row C3 — the ordinary [red1] congruence cases (prover C)

  The eta1-route C3 main induction ([red1_ind_all]) splits into:
  - the four unlocking cases ([red_fix], [red_cofix_case], [red_cofix_proj],
    [red_proj]) — owned by C3Prover1/2/3;
  - the [tCase] reduction rows ([case_red_param/return/discr/brs], [red_iota]) —
    owned by C3Falsifier (PCUICEtaC3Falsify.v);
  - **the ordinary congruence rows and the base rewrite rows — this file.**

  Each case is a square of the *unscoped* C3 (matching C3Falsifier's [C3]/[joinable]),
  proved from the full-C3 induction hypothesis [IH : C3 Σ] (discharged on structurally
  smaller terms by the outer induction) plus the η congruence toolkit of
  [PCUICEtaC3C].  The pure congruence rows need neither [wf Σ] nor scoping nor
  [eta_subst]; the base rewrite rows ([red_beta], [red_zeta], [red_rel], [red_delta])
  are separated out because they overlap η nontrivially and are the remaining work. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Prop Require Import DepElim.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICInduction PCUICPrimitive
     PCUICCases PCUICReduction PCUICEtaDefs PCUICEtaC3C.

Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope type_scope.

Notation eta_rt := (clos_refl_trans eta1).
Definition red_le Σ Γ := clos_refl (red1 Σ Γ).

Definition joinable {cf:checker_flags} (Σ : global_env) (Γ : context) (u v : term) : Type :=
  ∑ w w', red_le Σ Γ u w × eta_rt v w' × upto_domain w w'.

Definition C3 {cf:checker_flags} (Σ : global_env) : Type :=
  forall Γ t u v, red1 Σ Γ t v -> eta1 t u -> joinable Σ Γ u v.

(** [red_le] (reflexive closure of [red1]) congruences used to transport the join. *)

Lemma red_le_App_l Σ Γ a b c : red_le Σ Γ a b -> red_le Σ Γ (tApp a c) (tApp b c).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma red_le_App_r Σ Γ a b c : red_le Σ Γ b c -> red_le Σ Γ (tApp a b) (tApp a c).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma red_le_Prod_l Σ Γ na a b c : red_le Σ Γ a b -> red_le Σ Γ (tProd na a c) (tProd na b c).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma red_le_Proj Σ Γ p a b : red_le Σ Γ a b -> red_le Σ Γ (tProj p a) (tProj p b).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.

(** Lifting [clos_refl]/[clos_refl_trans] of [OnOne2] through a cons. *)
Lemma clos_refl_OnOne2_cons {A} (R : A -> A -> Type) a l l' :
  clos_refl (OnOne2 R) l l' -> clos_refl (OnOne2 R) (a :: l) (a :: l').
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma crt_OnOne2_cons {A} (R : A -> A -> Type) a l l' :
  clos_refl_trans (OnOne2 R) l l' -> clos_refl_trans (OnOne2 R) (a :: l) (a :: l').
Proof. induction 1; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eauto]. Qed.
Lemma clos_refl_OnOne2_hd {A} (R : A -> A -> Type) a w tl :
  clos_refl R a w -> clos_refl (OnOne2 R) (a :: tl) (w :: tl).
Proof. destruct 1; [apply r_step; now constructor|apply r_refl]. Qed.
Lemma crt_OnOne2_hd {A} (R : A -> A -> Type) a w tl :
  clos_refl_trans R a w -> clos_refl_trans (OnOne2 R) (a :: tl) (w :: tl).
Proof. induction 1; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eauto]. Qed.

Lemma subst_app_lift_rel0 a c : subst0 [a] (tApp (lift0 1 c) (tRel 0)) = tApp c a.
Proof.
  assert (H00 : 0 <= 0) by lia. simpl.
  rewrite (simpl_subst [a] c 0 0 H00). simpl. rewrite !lift0_id. reflexivity.
Qed.

Section Cong.
  Context {cf : checker_flags} (Σ : global_env).
  Context (IH : C3 Σ).

  (** Discharged elsewhere, kept as named hypotheses (same discipline as
      C3Falsifier). [eta_subst] : EtaL2 frac/eta-l2 @ 7b4491f0 and C3Prover2
      frac/eta-c3-C3Prover2 @ 9463536a, both GREEN/unconditional. [red1_eta_ctx_strong]
      : EtaL2 pinned in PCUICEtaConfluence.v, proving. Require, do not retype. *)
  Context (eta_subst : forall s s' b b', All2 eta s s' -> eta b b' ->
             eta (subst0 s b) (subst0 s' b')).
  Context (red1_eta_ctx_strong : forall Γ Δ t w,
             red1 Σ Γ t w -> All2 (All_decls eta) Γ Δ ->
             ∑ w', red1 Σ Δ t w' × eta w w').

  Local Lemma all2_upto_refl l : All2 upto_domain l l.
  Proof. apply All2_same, upto_domain_refl. Qed.

  Local Lemma all_decls_eta_refl d : All_decls eta d d.
  Proof. destruct d as [? [|] ?]; constructor; apply rt_refl. Qed.
  Local Lemma eta_ctx_refl Γ : All2 (All_decls eta) Γ Γ.
  Proof. apply All2_same, all_decls_eta_refl. Qed.

  (** *** The two-[OnOne2] list diamond: a [red1] step and an [eta1] step on the
      same list [l].  Same position → the element [IH]; different positions →
      parallel.  Output: a [clos_refl] of [OnOne2 red1] on the η-side list and a
      [clos_refl_trans] of [OnOne2 eta1] on the red-side list, joined by
      [All2 upto_domain]. *)
  Lemma c3_OnOne2 Γ l l' l'' :
    OnOne2 (red1 Σ Γ) l l' -> OnOne2 eta1 l l'' ->
    ∑ lw lw', clos_refl (OnOne2 (red1 Σ Γ)) l'' lw
              × clos_refl_trans (OnOne2 eta1) l' lw'
              × All2 upto_domain lw lw'.
  Proof.
    intros hr. revert l''. induction hr as [hd hd' tl pr | hd tl tl' hr IHr]; intros l'' he.
    - (* red1 at head *) depelim he.
      + (* eta at head : same position *)
        destruct (IH _ _ _ _ pr e) as (w & w' & hw & hw' & hu).
        exists (w :: tl), (w' :: tl). split; [|split].
        * now apply clos_refl_OnOne2_hd.
        * now apply crt_OnOne2_hd.
        * constructor; [exact hu|apply all2_upto_refl].
      + (* eta in tail : different positions *)
        eexists (hd' :: _), (hd' :: _). split; [|split].
        * apply r_step. constructor. exact pr.
        * apply crt_OnOne2_cons. apply rt_step. eassumption.
        * apply all2_upto_refl.
    - (* red1 in tail *) depelim he.
      + (* eta at head : different positions *)
        eexists (_ :: tl'), (_ :: tl'). split; [|split].
        * apply clos_refl_OnOne2_cons. apply r_step. exact hr.
        * apply crt_OnOne2_hd. apply rt_step. eassumption.
        * apply all2_upto_refl.
      + (* eta in tail : recurse *)
        destruct (IHr _ ltac:(eassumption)) as (lw & lw' & hw & hw' & hu).
        exists (hd :: lw), (hd :: lw'). split; [|split].
        * now apply clos_refl_OnOne2_cons.
        * now apply crt_OnOne2_cons.
        * constructor; [apply upto_domain_refl|exact hu].
  Qed.

  (** *** evar_red : red1 in one position of the [tEvar] argument list. *)
  Lemma c3_evar_red Γ ev l l' u :
    OnOne2 (red1 Σ Γ) l l' -> eta1 (tEvar ev l) u -> joinable Σ Γ u (tEvar ev l').
  Proof.
    intros hr he. depelim he.
    destruct (c3_OnOne2 _ _ _ _ hr ltac:(eassumption)) as (lw & lw' & hw & hw' & hu).
    exists (tEvar ev lw), (tEvar ev lw'). split; [|split].
    - destruct hw; [apply r_step; now constructor|apply r_refl].
    - clear -hw'. induction hw';
        [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eauto].
    - now constructor.
  Qed.

  (** A joined pair stays joined under any [red_le]/[eta_rt]-preserving frame given
      explicitly. *)

  (** *** app_red_l : red1 in the function, η anywhere in [tApp M1 M2]. *)
  Lemma c3_app_red_l Γ M1 N1 M2 u :
    red1 Σ Γ M1 N1 -> eta1 (tApp M1 M2) u -> joinable Σ Γ u (tApp N1 M2).
  Proof.
    intros hr he. depelim he.
    - (* app_eta_l : eta1 M1 N1' *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tApp w M2), (tApp w' M2). split; [|split].
      + now apply red_le_App_l.
      + now apply eta_App_l.
      + constructor; [exact hd|apply upto_domain_refl].
    - (* app_eta_r : eta1 M2 N2 *)
      exists (tApp N1 N2), (tApp N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply app_eta_r.
      + apply upto_domain_refl.
  Qed.

  (** *** app_red_r : red1 in the argument. *)
  Lemma c3_app_red_r Γ M1 M2 N2 u :
    red1 Σ Γ M2 N2 -> eta1 (tApp M1 M2) u -> joinable Σ Γ u (tApp M1 N2).
  Proof.
    intros hr he. depelim he.
    - (* app_eta_l : eta1 M1 N1 *)
      exists (tApp N1 N2), (tApp N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply app_eta_l.
      + apply upto_domain_refl.
    - (* app_eta_r : eta1 M2 N2' *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tApp M1 w), (tApp M1 w'). split; [|split].
      + now apply red_le_App_r.
      + now apply eta_App_r.
      + constructor; [apply upto_domain_refl|exact hd].
  Qed.

  (** *** prod_red_l : red1 in the domain. *)
  Lemma c3_prod_red_l Γ na M1 N1 M2 u :
    red1 Σ Γ M1 N1 -> eta1 (tProd na M1 M2) u -> joinable Σ Γ u (tProd na N1 M2).
  Proof.
    intros hr he. depelim he.
    - destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tProd na w M2), (tProd na w' M2). split; [|split].
      + now apply red_le_Prod_l.
      + now apply eta_Prod_l.
      + constructor; [exact hd|apply upto_domain_refl].
    - exists (tProd na N1 N2), (tProd na N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply prod_eta_r.
      + apply upto_domain_refl.
  Qed.

  (** *** proj_red : red1 in the projected term. *)
  Lemma c3_proj_red Γ p c c' u :
    red1 Σ Γ c c' -> eta1 (tProj p c) u -> joinable Σ Γ u (tProj p c').
  Proof.
    intros hr he. depelim he.
    destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
    exists (tProj p w), (tProj p w'). split; [|split].
    - now apply red_le_Proj.
    - now apply eta_Proj.
    - now constructor.
  Qed.

  (** *** abs_red_l : red1 in the λ domain.  All three η-inversions are clean
      (the [eta_red] overlap contracts the whole redex; the domain reduction only
      changes the ignored domain, so one η-step on [v] rejoins). *)
  Lemma c3_abs_red_l Γ na M N1 N u :
    red1 Σ Γ M N1 -> eta1 (tLambda na M N) u -> joinable Σ Γ u (tLambda na N1 N).
  Proof.
    intros hr he. depelim he.
    - (* eta_red : N = tApp (lift0 1 u) (tRel 0), M is the ignored domain *)
      eexists; eexists. split; [apply r_refl|split].
      + apply rt_step. apply eta_red.
      + apply upto_domain_refl.
    - (* abs_eta_l : eta1 M M' *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tLambda na w N), (tLambda na w' N). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_Lambda_l.
      + now constructor.
    - (* abs_eta_r : eta1 N N' (parallel to the domain reduction) *)
      eexists; eexists. split; [|split].
      + apply r_step. apply abs_red_l. exact hr.
      + apply rt_step. apply abs_eta_r. exact he.
      + apply upto_domain_refl.
  Qed.

  (** *** letin congruences (def / ty / body).  Parallel η / IH as for app. *)
  Lemma c3_letin_red_def Γ na b t b' r u :
    red1 Σ Γ b r -> eta1 (tLetIn na b t b') u -> joinable Σ Γ u (tLetIn na r t b').
  Proof.
    intros hr he. depelim he.
    - destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tLetIn na w t b'), (tLetIn na w' t b'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_LetIn_b.
      + constructor; [exact hd|apply upto_domain_refl|apply upto_domain_refl].
    - exists (tLetIn na r r0 b'), (tLetIn na r r0 b'). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_ty.
      + apply upto_domain_refl.
    - exists (tLetIn na r t r0), (tLetIn na r t r0). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_body.
      + apply upto_domain_refl.
  Qed.
  Lemma c3_letin_red_ty Γ na b t b' r u :
    red1 Σ Γ t r -> eta1 (tLetIn na b t b') u -> joinable Σ Γ u (tLetIn na b r b').
  Proof.
    intros hr he. depelim he.
    - exists (tLetIn na r0 r b'), (tLetIn na r0 r b'). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_def.
      + apply upto_domain_refl.
    - destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tLetIn na b w b'), (tLetIn na b w' b'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_LetIn_t.
      + constructor; [apply upto_domain_refl|exact hd|apply upto_domain_refl].
    - exists (tLetIn na b r r0), (tLetIn na b r r0). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_body.
      + apply upto_domain_refl.
  Qed.

  (** *** Base rewrite rows. *)

  (** red_rel / red_delta : [eta1] has no step on [tRel] / [tConst], so the η
      inversion is vacuous. *)
  Lemma c3_red_rel Γ i body u :
    option_map decl_body (nth_error Γ i) = Some (Some body) ->
    eta1 (tRel i) u -> joinable Σ Γ u (lift0 (S i) body).
  Proof. intros _ he. depelim he. Qed.

  Lemma c3_red_delta Γ c decl body (isdecl : declared_constant Σ c decl) u0 u :
    decl.(cst_body) = Some body ->
    eta1 (tConst c u0) u -> joinable Σ Γ u (subst_instance u0 body).
  Proof. intros _ he. depelim he. Qed.

  (** red_beta : discharged by [eta_subst] (β-on-the-η-side / β-created overlaps
      all close; the [eta_red] overlap collapses to equality by [simpl_subst]). *)
  Lemma c3_red_beta Γ na A b a u :
    eta1 (tApp (tLambda na A b) a) u -> joinable Σ Γ u (subst0 [a] b).
  Proof.
    intros he. depelim he.
    - (* app_eta_l : η on the λ *) depelim he.
      + (* eta_red : λ = eta_redex, b = tApp (lift0 1 c) (tRel 0) *)
        rewrite subst_app_lift_rel0.
        eexists; eexists. split; [apply r_refl|split; [apply rt_refl|apply upto_domain_refl]].
      + (* abs_eta_l : η in the domain (ignored by β) *)
        exists (subst0 [a] b), (subst0 [a] b). split; [|split].
        * apply r_step. apply red_beta.
        * apply rt_refl.
        * apply upto_domain_refl.
      + (* abs_eta_r : η in the body *)
        exists (subst0 [a] M'), (subst0 [a] M'). split; [|split].
        * apply r_step. apply red_beta.
        * apply eta_subst; [apply All2_same; reflexivity|apply rt_step; eassumption].
        * apply upto_domain_refl.
    - (* app_eta_r : η in the argument *)
      exists (subst0 [N2] b), (subst0 [N2] b). split; [|split].
      + apply r_step. apply red_beta.
      + apply eta_subst; [|apply rt_refl].
        constructor; [apply rt_step; eassumption|constructor].
      + apply upto_domain_refl.
  Qed.

  (** red_zeta : discharged by [eta_subst]. *)
  Lemma c3_red_zeta Γ na b t0 b' u :
    eta1 (tLetIn na b t0 b') u -> joinable Σ Γ u (subst0 [b] b').
  Proof.
    intros he. depelim he.
    - (* letin_eta_def : η in the bound term *)
      exists (subst0 [r] b'), (subst0 [r] b'). split; [|split].
      + apply r_step. apply red_zeta.
      + apply eta_subst; [|apply rt_refl].
        constructor; [apply rt_step; eassumption|constructor].
      + apply upto_domain_refl.
    - (* letin_eta_ty : η in the type (ignored by ζ) *)
      exists (subst0 [b] b'), (subst0 [b] b'). split; [|split].
      + apply r_step. apply red_zeta.
      + apply rt_refl.
      + apply upto_domain_refl.
    - (* letin_eta_body : η in the body *)
      exists (subst0 [b] r), (subst0 [b] r). split; [|split].
      + apply r_step. apply red_zeta.
      + apply eta_subst; [apply All2_same; reflexivity|apply rt_step; eassumption].
      + apply upto_domain_refl.
  Qed.

  (** *** prod_red_r : red1 in the Π codomain (under the binder); the parallel
      η-in-domain case goes through [red1_eta_ctx_strong]. *)
  Lemma c3_prod_red_r Γ na M M2 N2 u :
    red1 Σ (Γ ,, vass na M) M2 N2 -> eta1 (tProd na M M2) u -> joinable Σ Γ u (tProd na M N2).
  Proof.
    intros hr he. depelim he.
    - (* prod_eta_l : η in the domain M -> N1, reduction under the changed context *)
      destruct (red1_eta_ctx_strong (Γ ,, vass na M) (Γ ,, vass na N1) M2 N2 hr)
        as (w & hw & hw').
      { constructor; [constructor; apply rt_step; eassumption | apply eta_ctx_refl]. }
      exists (tProd na N1 w), (tProd na N1 w). split; [|split].
      + apply r_step. apply prod_red_r. exact hw.
      + apply eta_Prod; [apply rt_step; eassumption | exact hw'].
      + apply upto_domain_refl.
    - (* prod_eta_r : η in the codomain *)
      destruct (IH _ _ _ _ hr he) as (w & w' & hw & hw' & hd).
      exists (tProd na M w), (tProd na M w'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_Prod_r.
      + constructor; [apply upto_domain_refl|exact hd].
  Qed.

End Cong.
