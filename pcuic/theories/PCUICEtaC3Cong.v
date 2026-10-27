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
     PCUICCases PCUICOnFreeVars PCUICReduction PCUICTyping PCUICEtaDefs PCUICEtaC3C
     PCUICEtaConfluence PCUICEtaStrengthening.

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

Lemma upto_domain_array (a a' : array_model term) :
  a.(array_level) = a'.(array_level) ->
  upto_domain a.(array_default) a'.(array_default) ->
  upto_domain a.(array_type) a'.(array_type) ->
  All2 upto_domain a.(array_value) a'.(array_value) ->
  upto_domain (tPrim (primArray; primArrayModel a)) (tPrim (primArray; primArrayModel a')).
Proof. intros hl hd ht hv. constructor. constructor; auto. now rewrite hl. Qed.

Lemma red1_set_array_default Σ Γ arr x y : red1 Σ Γ x y ->
  red1 Σ Γ (tPrim (primArray; primArrayModel (set_array_default arr x)))
           (tPrim (primArray; primArrayModel (set_array_default arr y))).
Proof.
  intro r.
  assert (E : set_array_default (set_array_default arr x) y = set_array_default arr y)
    by (now destruct arr).
  rewrite <- E. exact (@array_red_def Σ Γ (set_array_default arr x) y r).
Qed.
Lemma red_le_set_array_default Σ Γ arr x y : red_le Σ Γ x y ->
  red_le Σ Γ (tPrim (primArray; primArrayModel (set_array_default arr x)))
             (tPrim (primArray; primArrayModel (set_array_default arr y))).
Proof. destruct 1; [apply r_step; now apply red1_set_array_default|apply r_refl]. Qed.

Lemma red1_set_array_type Σ Γ arr x y : red1 Σ Γ x y ->
  red1 Σ Γ (tPrim (primArray; primArrayModel (set_array_type arr x)))
           (tPrim (primArray; primArrayModel (set_array_type arr y))).
Proof.
  intro r.
  assert (E : set_array_type (set_array_type arr x) y = set_array_type arr y)
    by (now destruct arr).
  rewrite <- E. exact (@array_red_type Σ Γ (set_array_type arr x) y r).
Qed.
Lemma red_le_set_array_type Σ Γ arr x y : red_le Σ Γ x y ->
  red_le Σ Γ (tPrim (primArray; primArrayModel (set_array_type arr x)))
             (tPrim (primArray; primArrayModel (set_array_type arr y))).
Proof. destruct 1; [apply r_step; now apply red1_set_array_type|apply r_refl]. Qed.

Lemma red1_set_array_value Σ Γ arr l l' : OnOne2 (red1 Σ Γ) l l' ->
  red1 Σ Γ (tPrim (primArray; primArrayModel (set_array_value arr l)))
           (tPrim (primArray; primArrayModel (set_array_value arr l'))).
Proof.
  intro o.
  assert (E : set_array_value (set_array_value arr l) l' = set_array_value arr l')
    by (now destruct arr).
  rewrite <- E. exact (@array_red_val Σ Γ (set_array_value arr l) l' o).
Qed.
Lemma red_le_set_array_value Σ Γ arr l l' : clos_refl (OnOne2 (red1 Σ Γ)) l l' ->
  red_le Σ Γ (tPrim (primArray; primArrayModel (set_array_value arr l)))
             (tPrim (primArray; primArrayModel (set_array_value arr l'))).
Proof. destruct 1; [apply r_step; now apply red1_set_array_value|apply r_refl]. Qed.
Lemma eta1_set_array_value arr l l' : OnOne2 eta1 l l' ->
  eta1 (tPrim (primArray; primArrayModel (set_array_value arr l)))
       (tPrim (primArray; primArrayModel (set_array_value arr l'))).
Proof.
  intro o.
  assert (E : set_array_value (set_array_value arr l) l' = set_array_value arr l')
    by (now destruct arr).
  rewrite <- E. exact (array_eta_val (set_array_value arr l) l' o).
Qed.
Lemma eta_set_array_value arr l l' : clos_refl_trans (OnOne2 eta1) l l' ->
  clos_refl_trans eta1 (tPrim (primArray; primArrayModel (set_array_value arr l)))
                       (tPrim (primArray; primArrayModel (set_array_value arr l'))).
Proof.
  induction 1; [apply rt_step; now apply eta1_set_array_value|apply rt_refl|eapply rt_trans; eauto].
Qed.

(** Def-field setters and the per-field [eta]/[upto] lifts for fix/cofix.  A fixed
    carrier [d] supplies the untouched fields, so [clos_refl_trans] threads cleanly
    (the intermediate terms all go through [set_dtype d] / [set_dbody d]). *)
Definition set_dtype (d : def term) (ty : term) : def term :=
  {| dname := dname d; dtype := ty; dbody := dbody d; rarg := rarg d |}.
Definition set_dbody (d : def term) (bo : term) : def term :=
  {| dname := dname d; dtype := dtype d; dbody := bo; rarg := rarg d |}.
Definition updef (x y : def term) : Type :=
  upto_domain x.(dtype) y.(dtype) × upto_domain x.(dbody) y.(dbody) × x.(rarg) = y.(rarg).
Lemma updef_refl x : updef x x.
Proof. split; [apply upto_domain_refl|split; [apply upto_domain_refl|reflexivity]]. Qed.

Notation gfix := (fun x : def term => (dname x, dbody x, rarg x)).
Notation gfixb := (fun x : def term => (dname x, dtype x, rarg x)).

Lemma crt_set_dtype d X Y : clos_refl_trans eta1 X Y ->
  clos_refl_trans (on_Trel_eq eta1 dtype gfix) (set_dtype d X) (set_dtype d Y).
Proof.
  induction 1; [apply rt_step; split; [exact r|reflexivity]|apply rt_refl|eapply rt_trans; eauto].
Qed.
Lemma crt_set_dbody d X Y : clos_refl_trans eta1 X Y ->
  clos_refl_trans (on_Trel_eq eta1 dbody gfixb) (set_dbody d X) (set_dbody d Y).
Proof.
  induction 1; [apply rt_step; split; [exact r|reflexivity]|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma utd_fix_of idx m m' : All2 updef m m' -> upto_domain (tFix m idx) (tFix m' idx).
Proof. intro h. now constructor. Qed.
Lemma utd_cofix_of idx m m' : All2 updef m m' -> upto_domain (tCoFix m idx) (tCoFix m' idx).
Proof. intro h. now constructor. Qed.

(** Type-generic two-[OnOne2] diamond (the proof of [c3_OnOne2], abstracted over
    the element type [A] and the three element relations [R] (red leg), [S] (eta
    leg), [U] (join).  The red leg carries, per element, a local join [J] for the
    [S]-match — exactly the shape [red1_ind_all]'s per-element IH provides.  Reused
    for the fix/cofix def-lists via [on_Trel_eq] on the dtype field. *)
Lemma onOne2_diamond {A} (R S U : A -> A -> Type) :
  (forall x, U x x) ->
  forall l l' l'',
  OnOne2 (fun a a' => R a a'
            × (forall b, S a b -> ∑ w w', clos_refl R b w × clos_refl_trans S a' w' × U w w'))
         l l' ->
  OnOne2 S l l'' ->
  ∑ lw lw', clos_refl (OnOne2 R) l'' lw × clos_refl_trans (OnOne2 S) l' lw' × All2 U lw lw'.
Proof.
  intros Urefl l l' l'' hr. revert l''.
  induction hr as [hd hd' tl pr | hd tl tl' hr IHr]; intros l'' he.
  - depelim he.
    + destruct (snd pr _ ltac:(eassumption)) as (w & w' & hw & hw' & hu).
      exists (w :: tl), (w' :: tl). split; [|split].
      * now apply clos_refl_OnOne2_hd.
      * now apply crt_OnOne2_hd.
      * constructor; [exact hu|apply All2_same; exact Urefl].
    + eexists (hd' :: _), (hd' :: _). split; [|split].
      * apply r_step. constructor. exact (fst pr).
      * apply crt_OnOne2_cons. apply rt_step. eassumption.
      * apply All2_same; exact Urefl.
  - depelim he.
    + eexists (_ :: tl'), (_ :: tl'). split; [|split].
      * apply clos_refl_OnOne2_cons. apply r_step.
        eapply OnOne2_impl; [exact hr|]. intros ? ? h. exact (fst h).
      * apply crt_OnOne2_hd. apply rt_step. eassumption.
      * apply All2_same; exact Urefl.
    + destruct (IHr _ ltac:(eassumption)) as (lw & lw' & hw & hw' & hu).
      exists (hd :: lw), (hd :: lw'). split; [|split].
      * now apply clos_refl_OnOne2_cons.
      * now apply crt_OnOne2_cons.
      * constructor; [exact (Urefl hd)|exact hu].
  Qed.

Section Cong.
  Context {cf : checker_flags} (Σ : global_env).
  (** NO global [IH : C3 Σ] here, deliberately.  The AUTHORITATIVE C3 is the
      hardened one (wf Σ + is_closed_context + is_open_term), and its [red1_ind_all]
      induction offers, per congruence row, only an induction hypothesis for THAT
      row's sub-reduction, already under the row's extended context.  A global
      unscoped [IH : C3 Σ] cannot be fed by it: the shell would have to produce C3
      at arbitrary Γ/t with no scoping in hand.  So every row below takes a LOCAL
      IH for exactly its own sub-reduction, which is what the induction hands over;
      the shell discharges the row's scoping obligations.  Do NOT "simplify" this
      back to a global IH. *)

  (** [eta_subst], [red1_eta_ctx_strong], [eta_ctx_refl] (PCUICEtaConfluence) and
      [red1_strengthening] (PCUICEtaStrengthening), [lift_unfold_fix/cofix],
      [lift_is_constructor] are all REAL now (merged frac/eta-l2-strengthen @ bacbdf55);
      no staged hypotheses remain. *)

  Local Lemma all2_upto_refl l : All2 upto_domain l l.
  Proof. apply All2_same, upto_domain_refl. Qed.

  Local Lemma all_decls_eta_refl d : All_decls eta d d.
  Proof. destruct d as [? [|] ?]; constructor; apply rt_refl. Qed.

  (** *** The two-[OnOne2] list diamond: a [red1] step and an [eta1] step on the
      same list [l].  Same position → the element's LOCAL IH (carried on the
      [OnOne2] exactly as [red1_ind_all] hands it over, as a [Trel_conj]);
      different positions → parallel.  Output: a [clos_refl] of [OnOne2 red1] on
      the η-side list and a [clos_refl_trans] of [OnOne2 eta1] on the red-side
      list, joined by [All2 upto_domain]. *)
  Lemma c3_OnOne2 Γ l l' l'' :
    OnOne2 (fun a a' => red1 Σ Γ a a' × (forall b, eta1 a b -> joinable Σ Γ b a')) l l' ->
    OnOne2 eta1 l l'' ->
    ∑ lw lw', clos_refl (OnOne2 (red1 Σ Γ)) l'' lw
              × clos_refl_trans (OnOne2 eta1) l' lw'
              × All2 upto_domain lw lw'.
  Proof.
    intros hr. revert l''. induction hr as [hd hd' tl pr | hd tl tl' hr IHr]; intros l'' he.
    - (* red1 at head *) depelim he.
      + (* eta at head : same position, use the element's local IH *)
        destruct (snd pr _ e) as (w & w' & hw & hw' & hu).
        exists (w :: tl), (w' :: tl). split; [|split].
        * now apply clos_refl_OnOne2_hd.
        * now apply crt_OnOne2_hd.
        * constructor; [exact hu|apply all2_upto_refl].
      + (* eta in tail : different positions *)
        eexists (hd' :: _), (hd' :: _). split; [|split].
        * apply r_step. constructor. exact (fst pr).
        * apply crt_OnOne2_cons. apply rt_step. eassumption.
        * apply all2_upto_refl.
    - (* red1 in tail *) depelim he.
      + (* eta at head : different positions *)
        eexists (_ :: tl'), (_ :: tl'). split; [|split].
        * apply clos_refl_OnOne2_cons. apply r_step.
          eapply OnOne2_impl; [exact hr|]. intros ? ? h. exact (fst h).
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
    OnOne2 (fun a a' => red1 Σ Γ a a' × (forall b, eta1 a b -> joinable Σ Γ b a')) l l' ->
    eta1 (tEvar ev l) u -> joinable Σ Γ u (tEvar ev l').
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
    red1 Σ Γ M1 N1 -> (forall u', eta1 M1 u' -> joinable Σ Γ u' N1) ->
    eta1 (tApp M1 M2) u -> joinable Σ Γ u (tApp N1 M2).
  Proof.
    intros hr IHM he. depelim he.
    - (* app_eta_l : eta1 M1 N1' *)
      destruct (IHM _ he) as (w & w' & hw & hw' & hd).
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
    red1 Σ Γ M2 N2 -> (forall u', eta1 M2 u' -> joinable Σ Γ u' N2) ->
    eta1 (tApp M1 M2) u -> joinable Σ Γ u (tApp M1 N2).
  Proof.
    intros hr IHM he. depelim he.
    - (* app_eta_l : eta1 M1 N1 *)
      exists (tApp N1 N2), (tApp N1 N2). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply app_eta_l.
      + apply upto_domain_refl.
    - (* app_eta_r : eta1 M2 N2' *)
      destruct (IHM _ he) as (w & w' & hw & hw' & hd).
      exists (tApp M1 w), (tApp M1 w'). split; [|split].
      + now apply red_le_App_r.
      + now apply eta_App_r.
      + constructor; [apply upto_domain_refl|exact hd].
  Qed.

  (** *** prod_red_l : red1 in the domain. *)
  Lemma c3_prod_red_l Γ na M1 N1 M2 u :
    red1 Σ Γ M1 N1 -> (forall u', eta1 M1 u' -> joinable Σ Γ u' N1) ->
    eta1 (tProd na M1 M2) u -> joinable Σ Γ u (tProd na N1 M2).
  Proof.
    intros hr IHM he. depelim he.
    - destruct (IHM _ he) as (w & w' & hw & hw' & hd).
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
    red1 Σ Γ c c' -> (forall u', eta1 c u' -> joinable Σ Γ u' c') ->
    eta1 (tProj p c) u -> joinable Σ Γ u (tProj p c').
  Proof.
    intros hr IHc he. depelim he.
    destruct (IHc _ he) as (w & w' & hw & hw' & hd).
    exists (tProj p w), (tProj p w'). split; [|split].
    - now apply red_le_Proj.
    - now apply eta_Proj.
    - now constructor.
  Qed.

  (** *** abs_red_l : red1 in the λ domain.  All three η-inversions are clean
      (the [eta_red] overlap contracts the whole redex; the domain reduction only
      changes the ignored domain, so one η-step on [v] rejoins). *)
  Lemma c3_abs_red_l Γ na M N1 N u :
    red1 Σ Γ M N1 -> (forall u', eta1 M u' -> joinable Σ Γ u' N1) ->
    eta1 (tLambda na M N) u -> joinable Σ Γ u (tLambda na N1 N).
  Proof.
    intros hr IHM he. depelim he.
    - (* eta_red : N = tApp (lift0 1 u) (tRel 0), M is the ignored domain *)
      eexists; eexists. split; [apply r_refl|split].
      + apply rt_step. apply eta_red.
      + apply upto_domain_refl.
    - (* abs_eta_l : eta1 M M' *)
      destruct (IHM _ he) as (w & w' & hw & hw' & hd).
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
    red1 Σ Γ b r -> (forall u', eta1 b u' -> joinable Σ Γ u' r) ->
    eta1 (tLetIn na b t b') u -> joinable Σ Γ u (tLetIn na r t b').
  Proof.
    intros hr IHb he. depelim he.
    - destruct (IHb _ he) as (w & w' & hw & hw' & hd).
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
    red1 Σ Γ t r -> (forall u', eta1 t u' -> joinable Σ Γ u' r) ->
    eta1 (tLetIn na b t b') u -> joinable Σ Γ u (tLetIn na b r b').
  Proof.
    intros hr IHt he. depelim he.
    - exists (tLetIn na r0 r b'), (tLetIn na r0 r b'). split; [|split].
      + apply r_step. now constructor.
      + apply rt_step. now apply letin_eta_def.
      + apply upto_domain_refl.
    - destruct (IHt _ he) as (w & w' & hw & hw' & hd).
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
    red1 Σ (Γ ,, vass na M) M2 N2 ->
    (forall u', eta1 M2 u' -> joinable Σ (Γ ,, vass na M) u' N2) ->
    eta1 (tProd na M M2) u -> joinable Σ Γ u (tProd na M N2).
  Proof.
    intros hr IHM2 he. depelim he.
    - (* prod_eta_l : η in the domain M -> N1, reduction under the changed context *)
      destruct (red1_eta_ctx_strong Σ (Γ ,, vass na M) (Γ ,, vass na N1) M2 N2 hr)
        as (w & hw & hw').
      { apply All2_cons; [constructor; apply rt_step; eassumption | apply eta_ctx_refl]. }
      exists (tProd na N1 w), (tProd na N1 w). split; [|split].
      + apply r_step. apply prod_red_r. exact hw.
      + apply eta_Prod; [apply rt_step; eassumption | exact hw'].
      + apply upto_domain_refl.
    - (* prod_eta_r : η in the codomain *)
      destruct (IHM2 _ he) as (w & w' & hw & hw' & hd).
      exists (tProd na M w), (tProd na M w'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_Prod_r.
      + constructor; [apply upto_domain_refl|exact hd].
  Qed.

  (** *** letin_red_body : red1 in the let body (under [vdef]); the parallel
      η-in-def / η-in-type cases change the [vdef] context, discharged by
      [red1_eta_ctx_strong]. *)
  Lemma c3_letin_red_body Γ na b t0 b' r u :
    red1 Σ (Γ ,, vdef na b t0) b' r ->
    (forall u', eta1 b' u' -> joinable Σ (Γ ,, vdef na b t0) u' r) ->
    eta1 (tLetIn na b t0 b') u -> joinable Σ Γ u (tLetIn na b t0 r).
  Proof.
    intros hr IHb' he. depelim he.
    - (* letin_eta_def : η in the bound term b -> r0 *)
      destruct (red1_eta_ctx_strong Σ (Γ ,, vdef na b t0) (Γ ,, vdef na r0 t0) b' r hr)
        as (w & hw & hw').
      { apply All2_cons; [constructor; [apply rt_step; eassumption|apply rt_refl]
                         | apply eta_ctx_refl]. }
      exists (tLetIn na r0 t0 w), (tLetIn na r0 t0 w). split; [|split].
      + apply r_step. now constructor.
      + apply eta_LetIn; [apply rt_step; eassumption|apply rt_refl|exact hw'].
      + apply upto_domain_refl.
    - (* letin_eta_ty : η in the type t0 -> r0 *)
      destruct (red1_eta_ctx_strong Σ (Γ ,, vdef na b t0) (Γ ,, vdef na b r0) b' r hr)
        as (w & hw & hw').
      { apply All2_cons; [constructor; [apply rt_refl|apply rt_step; eassumption]
                         | apply eta_ctx_refl]. }
      exists (tLetIn na b r0 w), (tLetIn na b r0 w). split; [|split].
      + apply r_step. now constructor.
      + apply eta_LetIn; [apply rt_refl|apply rt_step; eassumption|exact hw'].
      + apply upto_domain_refl.
    - (* letin_eta_body : η in the body b' -> r0 (same subterm, via IH) *)
      destruct (IHb' _ he) as (w & w' & hw & hw' & hd).
      exists (tLetIn na b t0 w), (tLetIn na b t0 w'). split; [|split].
      + destruct hw; [apply r_step; now constructor|apply r_refl].
      + now apply eta_LetIn_c.
      + constructor; [apply upto_domain_refl|apply upto_domain_refl|exact hd].
  Qed.

  (** *** Primitive-array reductions.  Set-field commutations are all
      [now destruct arr]; same-field via the local IH, cross-field parallel. *)

  Lemma c3_array_red_def Γ arr def u :
    red1 Σ Γ arr.(array_default) def ->
    (forall u', eta1 arr.(array_default) u' -> joinable Σ Γ u' def) ->
    eta1 (tPrim (primArray; primArrayModel arr)) u ->
    joinable Σ Γ u (tPrim (primArray; primArrayModel (set_array_default arr def))).
  Proof.
    intros hr IHd he. depelim he.
    - (* array_eta_val : parallel (red default, η value) *)
      eexists; eexists. split; [|split].
      + apply r_step. apply array_red_def. exact hr.
      + apply rt_step. apply array_eta_val. eassumption.
      + apply upto_domain_refl.
    - (* array_eta_def : same field, via IH *)
      destruct (IHd _ ltac:(eassumption)) as (w & w' & hw & hw' & hu).
      exists (tPrim (primArray; primArrayModel (set_array_default arr w))),
             (tPrim (primArray; primArrayModel (set_array_default arr w'))). split; [|split].
      + now apply red_le_set_array_default.
      + now apply eta_Array_default.
      + apply upto_domain_array; cbn;
          [reflexivity|exact hu|apply upto_domain_refl|apply all2_upto_refl].
    - (* array_eta_type : parallel (red default, η type) *)
      eexists; eexists. split; [|split].
      + apply r_step. apply array_red_def. exact hr.
      + apply rt_step. apply array_eta_type. eassumption.
      + apply upto_domain_refl.
  Qed.

  Lemma c3_array_red_type Γ arr ty0 u :
    red1 Σ Γ arr.(array_type) ty0 ->
    (forall u', eta1 arr.(array_type) u' -> joinable Σ Γ u' ty0) ->
    eta1 (tPrim (primArray; primArrayModel arr)) u ->
    joinable Σ Γ u (tPrim (primArray; primArrayModel (set_array_type arr ty0))).
  Proof.
    intros hr IHt he. depelim he.
    - (* array_eta_val : parallel *)
      eexists; eexists. split; [|split].
      + apply r_step. apply array_red_type. exact hr.
      + apply rt_step. apply array_eta_val. eassumption.
      + apply upto_domain_refl.
    - (* array_eta_def : parallel *)
      eexists; eexists. split; [|split].
      + apply r_step. apply array_red_type. exact hr.
      + apply rt_step. apply array_eta_def. eassumption.
      + apply upto_domain_refl.
    - (* array_eta_type : same field, via IH *)
      destruct (IHt _ ltac:(eassumption)) as (w & w' & hw & hw' & hu).
      exists (tPrim (primArray; primArrayModel (set_array_type arr w))),
             (tPrim (primArray; primArrayModel (set_array_type arr w'))). split; [|split].
      + now apply red_le_set_array_type.
      + now apply eta_Array_type.
      + apply upto_domain_array; cbn;
          [reflexivity|apply upto_domain_refl|exact hu|apply all2_upto_refl].
  Qed.

  Lemma c3_array_red_val Γ arr value u :
    OnOne2 (fun a a' => red1 Σ Γ a a' × (forall b, eta1 a b -> joinable Σ Γ b a'))
           arr.(array_value) value ->
    eta1 (tPrim (primArray; primArrayModel arr)) u ->
    joinable Σ Γ u (tPrim (primArray; primArrayModel (set_array_value arr value))).
  Proof.
    intros hr he. depelim he.
    - (* array_eta_val : both in the value list, use the diamond *)
      destruct (c3_OnOne2 _ _ _ _ hr ltac:(eassumption)) as (lw & lw' & hw & hw' & hu).
      exists (tPrim (primArray; primArrayModel (set_array_value arr lw))),
             (tPrim (primArray; primArrayModel (set_array_value arr lw'))). split; [|split].
      + now apply red_le_set_array_value.
      + now apply eta_set_array_value.
      + apply upto_domain_array; cbn; [reflexivity|apply upto_domain_refl|apply upto_domain_refl|exact hu].
    - (* array_eta_def : parallel *)
      eexists; eexists. split; [|split].
      + apply r_step. apply array_red_val.
        eapply OnOne2_impl; [exact hr|]. intros ? ? h. exact (fst h).
      + apply rt_step. apply array_eta_def. eassumption.
      + apply upto_domain_refl.
    - (* array_eta_type : parallel *)
      eexists; eexists. split; [|split].
      + apply r_step. apply array_red_val.
        eapply OnOne2_impl; [exact hr|]. intros ? ? h. exact (fst h).
      + apply rt_step. apply array_eta_type. eassumption.
      + apply upto_domain_refl.
  Qed.

  (** Σ-dependent per-field red lift and the tFix congruence lifts. *)
  Lemma clos_refl_set_dtype Γ d X Y : clos_refl (red1 Σ Γ) X Y ->
    clos_refl (on_Trel_eq (red1 Σ Γ) dtype gfix) (set_dtype d X) (set_dtype d Y).
  Proof. destruct 1; [apply r_step; split; [exact r|reflexivity]|apply r_refl]. Qed.
  Lemma red_le_fix_ty Γ idx m0 m1 :
    clos_refl (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype gfix)) m0 m1 ->
    red_le Σ Γ (tFix m0 idx) (tFix m1 idx).
  Proof. destruct 1; [apply r_step; now apply fix_red_ty|apply r_refl]. Qed.
  Lemma eta_fix_ty_rt idx m0 m1 :
    clos_refl_trans (OnOne2 (on_Trel_eq eta1 dtype gfix)) m0 m1 ->
    clos_refl_trans eta1 (tFix m0 idx) (tFix m1 idx).
  Proof.
    induction 1; [apply rt_step; now apply fix_eta_ty|apply rt_refl|eapply rt_trans; eauto].
  Qed.

  Local Lemma set_dtype_id d : set_dtype d (dtype d) = d.
  Proof. now destruct d. Qed.

  (** *** fix_red_ty : red1 in one dtype.  η on dtype → same-field diamond
      (onOne2_diamond + local IH); η on dbody → cross-field parallel. *)
  Lemma c3_fix_red_ty Γ mfix0 mfix1 idx u :
    OnOne2 (on_Trel_eq (fun x y => red1 Σ Γ x y
              × (forall u', eta1 x u' -> joinable Σ Γ u' y)) dtype gfix) mfix0 mfix1 ->
    eta1 (tFix mfix0 idx) u -> joinable Σ Γ u (tFix mfix1 idx).
  Proof.
    intros hr he. depelim he.
    - (* fix_eta_ty : η on dtype, same field *)
      assert (hin : OnOne2 (fun a a' => on_Trel_eq (red1 Σ Γ) dtype gfix a a'
                      × (forall b, on_Trel_eq eta1 dtype gfix a b ->
                         ∑ w w', clos_refl (on_Trel_eq (red1 Σ Γ) dtype gfix) b w
                                 × clos_refl_trans (on_Trel_eq eta1 dtype gfix) a' w'
                                 × updef w w')) mfix0 mfix1).
      { eapply OnOne2_impl; [exact hr|]. intros a a' [[rd IHd] geq]. split.
        - split; [exact rd|exact geq].
        - intros b [eb gbeq]. destruct (IHd _ eb) as (dw & dw' & hdw & hdw' & hu).
          exists (set_dtype b dw), (set_dtype a' dw'). split; [|split].
          + rewrite <- (set_dtype_id b) at 1. now apply clos_refl_set_dtype.
          + rewrite <- (set_dtype_id a') at 1. now apply crt_set_dtype.
          + split; [exact hu|split]; cbn.
            * assert (dbody b = dbody a') by congruence. rewrite H. apply upto_domain_refl.
            * congruence. }
      destruct (onOne2_diamond (on_Trel_eq (red1 Σ Γ) dtype gfix)
                 (on_Trel_eq eta1 dtype gfix) updef updef_refl mfix0 mfix1 _ hin
                 ltac:(eassumption)) as (mw & mw' & hw & hw' & hu).
      exists (tFix mw idx), (tFix mw' idx). split; [|split].
      + now apply red_le_fix_ty.
      + now apply eta_fix_ty_rt.
      + now apply utd_fix_of.
    - (* fix_eta_body : η on dbody, cross field — parallel *)
      assert (hin : OnOne2 (fun a a' => on_Trel_eq (red1 Σ Γ) dtype gfix a a'
                      × (forall b, on_Trel_eq eta1 dbody gfixb a b ->
                         ∑ w w', clos_refl (on_Trel_eq (red1 Σ Γ) dtype gfix) b w
                                 × clos_refl_trans (on_Trel_eq eta1 dbody gfixb) a' w'
                                 × updef w w')) mfix0 mfix1).
      { eapply OnOne2_impl; [exact hr|]. intros a a' [[rd IHd] geq]. split.
        - split; [exact rd|exact geq].
        - intros b [eb gbeq].
          exists (set_dbody a' (dbody b)), (set_dbody a' (dbody b)). split; [|split].
          + apply r_step. split; cbn.
            * assert (dtype b = dtype a) by congruence. rewrite H. exact rd.
            * congruence.
          + apply rt_step. split; cbn.
            * assert (dbody a' = dbody a) by congruence. rewrite H. exact eb.
            * congruence.
          + apply updef_refl. }
      destruct (onOne2_diamond (on_Trel_eq (red1 Σ Γ) dtype gfix)
                 (on_Trel_eq eta1 dbody gfixb) updef updef_refl mfix0 mfix1 _ hin
                 ltac:(eassumption)) as (mw & mw' & hw & hw' & hu).
      exists (tFix mw idx), (tFix mw' idx). split; [|split].
      + now apply red_le_fix_ty.
      + (* eta via fix_eta_body *)
        clear -hw'. induction hw';
          [apply rt_step; now apply fix_eta_body|apply rt_refl|eapply rt_trans; eauto].
      + now apply utd_fix_of.
  Qed.

  Lemma red_le_cofix_ty Γ idx m0 m1 :
    clos_refl (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype gfix)) m0 m1 ->
    red_le Σ Γ (tCoFix m0 idx) (tCoFix m1 idx).
  Proof. destruct 1; [apply r_step; now apply cofix_red_ty|apply r_refl]. Qed.
  Lemma eta_cofix_ty_rt idx m0 m1 :
    clos_refl_trans (OnOne2 (on_Trel_eq eta1 dtype gfix)) m0 m1 ->
    clos_refl_trans eta1 (tCoFix m0 idx) (tCoFix m1 idx).
  Proof.
    induction 1; [apply rt_step; now apply cofix_eta_ty|apply rt_refl|eapply rt_trans; eauto].
  Qed.

  Lemma c3_cofix_red_ty Γ mfix0 mfix1 idx u :
    OnOne2 (on_Trel_eq (fun x y => red1 Σ Γ x y
              × (forall u', eta1 x u' -> joinable Σ Γ u' y)) dtype gfix) mfix0 mfix1 ->
    eta1 (tCoFix mfix0 idx) u -> joinable Σ Γ u (tCoFix mfix1 idx).
  Proof.
    intros hr he. depelim he.
    - (* cofix_eta_ty : same field *)
      assert (hin : OnOne2 (fun a a' => on_Trel_eq (red1 Σ Γ) dtype gfix a a'
                      × (forall b, on_Trel_eq eta1 dtype gfix a b ->
                         ∑ w w', clos_refl (on_Trel_eq (red1 Σ Γ) dtype gfix) b w
                                 × clos_refl_trans (on_Trel_eq eta1 dtype gfix) a' w'
                                 × updef w w')) mfix0 mfix1).
      { eapply OnOne2_impl; [exact hr|]. intros a a' [[rd IHd] geq]. split.
        - split; [exact rd|exact geq].
        - intros b [eb gbeq]. destruct (IHd _ eb) as (dw & dw' & hdw & hdw' & hu).
          exists (set_dtype b dw), (set_dtype a' dw'). split; [|split].
          + rewrite <- (set_dtype_id b) at 1. now apply clos_refl_set_dtype.
          + rewrite <- (set_dtype_id a') at 1. now apply crt_set_dtype.
          + split; [exact hu|split]; cbn.
            * assert (dbody b = dbody a') by congruence. rewrite H. apply upto_domain_refl.
            * congruence. }
      destruct (onOne2_diamond (on_Trel_eq (red1 Σ Γ) dtype gfix)
                 (on_Trel_eq eta1 dtype gfix) updef updef_refl mfix0 mfix1 _ hin
                 ltac:(eassumption)) as (mw & mw' & hw & hw' & hu).
      exists (tCoFix mw idx), (tCoFix mw' idx). split; [|split].
      + now apply red_le_cofix_ty.
      + now apply eta_cofix_ty_rt.
      + now apply utd_cofix_of.
    - (* cofix_eta_body : cross field *)
      assert (hin : OnOne2 (fun a a' => on_Trel_eq (red1 Σ Γ) dtype gfix a a'
                      × (forall b, on_Trel_eq eta1 dbody gfixb a b ->
                         ∑ w w', clos_refl (on_Trel_eq (red1 Σ Γ) dtype gfix) b w
                                 × clos_refl_trans (on_Trel_eq eta1 dbody gfixb) a' w'
                                 × updef w w')) mfix0 mfix1).
      { eapply OnOne2_impl; [exact hr|]. intros a a' [[rd IHd] geq]. split.
        - split; [exact rd|exact geq].
        - intros b [eb gbeq].
          exists (set_dbody a' (dbody b)), (set_dbody a' (dbody b)). split; [|split].
          + apply r_step. split; cbn.
            * assert (dtype b = dtype a) by congruence. rewrite H. exact rd.
            * congruence.
          + apply rt_step. split; cbn.
            * assert (dbody a' = dbody a) by congruence. rewrite H. exact eb.
            * congruence.
          + apply updef_refl. }
      destruct (onOne2_diamond (on_Trel_eq (red1 Σ Γ) dtype gfix)
                 (on_Trel_eq eta1 dbody gfixb) updef updef_refl mfix0 mfix1 _ hin
                 ltac:(eassumption)) as (mw & mw' & hw & hw' & hu).
      exists (tCoFix mw idx), (tCoFix mw' idx). split; [|split].
      + now apply red_le_cofix_ty.
      + clear -hw'. induction hw';
          [apply rt_step; now apply cofix_eta_body|apply rt_refl|eapply rt_trans; eauto].
      + now apply utd_cofix_of.
  Qed.


  (** Body-field lifts + fix_context congruences, for fix/cofix_red_body. *)
  Lemma clos_refl_set_dbody Γ d X Y : clos_refl (red1 Σ Γ) X Y ->
    clos_refl (on_Trel_eq (red1 Σ Γ) dbody gfixb) (set_dbody d X) (set_dbody d Y).
  Proof. destruct 1; [apply r_step; split; [exact r|reflexivity]|apply r_refl]. Qed.
  Local Lemma set_dbody_id d : set_dbody d (dbody d) = d.
  Proof. now destruct d. Qed.
  Lemma red_le_fix_body Γ idx m0 m1 :
    clos_refl (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context m0)) dbody gfixb)) m0 m1 ->
    red_le Σ Γ (tFix m0 idx) (tFix m1 idx).
  Proof. destruct 1; [apply r_step; now apply fix_red_body|apply r_refl]. Qed.
  Lemma eta_fix_body_rt idx m0 m1 :
    clos_refl_trans (OnOne2 (on_Trel_eq eta1 dbody gfixb)) m0 m1 ->
    clos_refl_trans eta1 (tFix m0 idx) (tFix m1 idx).
  Proof.
    induction 1; [apply rt_step; now apply fix_eta_body|apply rt_refl|eapply rt_trans; eauto].
  Qed.
  Lemma red_le_cofix_body Γ idx m0 m1 :
    clos_refl (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, fix_context m0)) dbody gfixb)) m0 m1 ->
    red_le Σ Γ (tCoFix m0 idx) (tCoFix m1 idx).
  Proof. destruct 1; [apply r_step; now apply cofix_red_body|apply r_refl]. Qed.
  Lemma eta_cofix_body_rt idx m0 m1 :
    clos_refl_trans (OnOne2 (on_Trel_eq eta1 dbody gfixb)) m0 m1 ->
    clos_refl_trans eta1 (tCoFix m0 idx) (tCoFix m1 idx).
  Proof.
    induction 1; [apply rt_step; now apply cofix_eta_body|apply rt_refl|eapply rt_trans; eauto].
  Qed.

  (** fix_context depends only on dname+dtype: a dbody η-step leaves it equal;
      a dtype η-step makes the two fix_contexts eta_ctx-related. *)
  Lemma mapi_fix_dbody m m' : OnOne2 (on_Trel_eq eta1 dbody gfixb) m m' ->
    forall k, mapi_rec (fun i d => vass (dname d) (lift0 i (dtype d))) m k
            = mapi_rec (fun i d => vass (dname d) (lift0 i (dtype d))) m' k.
  Proof.
    induction 1 as [hd hd' tl p|hd tl tl' o IH]; intro k; cbn.
    - f_equal. destruct p as [_ geq]. destruct hd as [n t b r], hd' as [n0 t0 b0 r0].
      cbn in geq. inversion geq; subst. reflexivity.
    - f_equal. apply IH.
  Qed.
  Lemma fix_context_dbody_eq m m' :
    OnOne2 (on_Trel_eq eta1 dbody gfixb) m m' -> fix_context m = fix_context m'.
  Proof. intro h. unfold fix_context, fix_context_gen. f_equal. now apply mapi_fix_dbody. Qed.

  Lemma mapi_fix_eta_dtype m m' : OnOne2 (on_Trel_eq eta1 dtype gfix) m m' ->
    forall k, All2 (All_decls eta)
        (mapi_rec (fun i d => vass (dname d) (lift0 i (dtype d))) m k)
        (mapi_rec (fun i d => vass (dname d) (lift0 i (dtype d))) m' k).
  Proof.
    induction 1 as [hd hd' tl p|hd tl tl' o IH]; intro k; cbn.
    - constructor.
      + destruct p as [e geq]. destruct hd as [n t b r], hd' as [n0 t0 b0 r0].
        cbn in *. inversion geq; subst. constructor. apply eta_lift. now apply rt_step.
      + apply All2_same. apply all_decls_eta_refl.
    - constructor; [apply all_decls_eta_refl|apply IH].
  Qed.
  Lemma fix_context_eta_dtype m m' :
    OnOne2 (on_Trel_eq eta1 dtype gfix) m m' -> eta_ctx (fix_context m) (fix_context m').
  Proof.
    intro h. unfold eta_ctx, fix_context, fix_context_gen. apply All2_rev.
    now apply mapi_fix_eta_dtype.
  Qed.

  (** Invert a [tFix] application appearing under a [lift0 1]: the head fix and
      the spine both come from unlifted data.  Pure syntax, via decompose_app. *)
  Lemma lift_mkApps_tFix_inv n k M mfix idx args :
    lift n k M = mkApps (tFix mfix idx) args ->
    ∑ mfix' args', (M = mkApps (tFix mfix' idx) args')
      × (mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix')
      × (args = map (lift n k) args').
  Proof.
    intro H. destruct (decompose_app M) as [f a] eqn:da.
    pose proof (decompose_app_lift n k M f a da) as dl.
    rewrite H decompose_app_mkApps // in dl.
    apply decompose_app_inv in da.
    destruct f; cbn in dl; noconf dl.
    eexists _, _. split; [|split].
    - rewrite da. reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
End Cong.
