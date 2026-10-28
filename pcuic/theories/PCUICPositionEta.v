(* Distributed under the terms of the MIT license. *)
(* BET-315 eta lane (L5): copy of Syntax/PCUICPosition.v with the read-time lifted
   [Eta_app] frame and the focus-dropping [Eta_arg] frame (plan.md rev 11 §2 I7, §3 K3(a)).
   The structural stack operations keep their base meaning; the eta semantics is a
   separate view (eta_lift / decompose_stack_eta / zipp_eta / stack_context_eta). The
   five no-[Eta_arg] side-condition lemmas (zipc_inj, stack_position_atpos,
   welltyped_zipc_zipp, welltyped_context, welltyped_zipc_stack_context) are restated
   here. Imported by L5's safechecker copies only.
   RE-CUT 2026-10-28 onto trunk 0729d50e: the η diff (d84799fa) three-way merged into
   trunk's PCUICPosition.v, which adds prim-ops' [Prim_app] frame and its clauses in
   [fill_hole], [closedn_stack_entry] and [stack_entry_choice] (merge without conflict;
   no proof needed a new [Prim_app] case). *)
From Stdlib Require Import RelationClasses ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Common Require Import PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICInduction
     PCUICReflect PCUICEquality PCUICLiftSubst PCUICCases
     PCUICAstUtils PCUICUnivSubst PCUICTyping
     PCUICCasesContexts PCUICGlobalEnv
     PCUICAlpha PCUICInversion PCUICSubstitution
     PCUICContextConversion PCUICContextConversionTyp PCUICValidity PCUICArities
     PCUICUnivSubstitutionConv PCUICUnivSubstitutionTyp
     PCUICOnFreeVars PCUICSpine PCUICInductives PCUICReduction
     PCUICWellScopedCumulativity PCUICCumulativity PCUICSR
     PCUICWeakeningTyp PCUICContexts PCUICInductiveInversion.

Import MonadNotation.

Import MonadNotation.

Import MonadNotation.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Inductive context_decl_choice :=
| choose_decl_body
| choose_decl_type.

Derive NoConfusion NoConfusionHom EqDec for context_decl_choice.

Definition context_choice := nat * context_decl_choice.

(* A choice is a local position.
   We define positions in a non dependent way to make it more practical.
 *)
Inductive choice :=
| app_l
| app_r
| case_par (n : nat)
| case_preturn
| case_c
| case_brsbody (n : nat)
| proj_c
| fix_mfix_ty (n : nat)
| fix_mfix_bd (n : nat)
| cofix_mfix_ty (n : nat)
| cofix_mfix_bd (n : nat)
| lam_ty
| lam_tm
| prod_l
| prod_r
| let_bd
| let_ty
| let_in
| array_def
| array_ty
| array_val (n : nat).

Derive NoConfusion NoConfusionHom EqDec for choice.

#[global]
Instance reflect_choice : ReflectEq choice :=
  let h := EqDec_ReflectEq choice in _.

Definition position := list choice.

Definition context_choice_term (Γ : context) (c : context_choice) : option term :=
  let '(decli, declc) := c in
  match nth_error Γ decli with
  | Some {| decl_body := body; decl_type := type |} =>
    match declc with
    | choose_decl_body => body
    | choose_decl_type => Some type
    end
  | None => None
  end.

Fixpoint validpos t (p : position) {struct p} :=
  match p with
  | [] => true
  | c :: p =>
    match c, t with
    | app_l, tApp u v => validpos u p
    | app_r, tApp u v => validpos v p
    | case_par par, tCase ci pr c brs =>
      match nth_error pr.(pparams) par with
      | Some par =>  validpos par p
      | None => false
      end
    | case_preturn, tCase ci pr c brs => validpos pr.(preturn) p
    | case_c, tCase ci pr c brs => validpos c p
    | case_brsbody n, tCase ci pr c brs =>
        match nth_error brs n with
        | Some br => validpos br.(bbody) p
        | None => false
        end
    | proj_c, tProj pr c => validpos c p
    | fix_mfix_ty n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dtype) p
        | None => false
        end
    | fix_mfix_bd n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dbody) p
        | None => false
        end
    | cofix_mfix_ty n, tCoFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dtype) p
        | None => false
        end
    | cofix_mfix_bd n, tCoFix mfix idx =>
        match nth_error mfix n with
        | Some d => validpos d.(dbody) p
        | None => false
        end
    | lam_ty, tLambda na A t => validpos A p
    | lam_tm, tLambda na A t => validpos t p
    | prod_l, tProd na A B => validpos A p
    | prod_r, tProd na A B => validpos B p
    | let_bd, tLetIn na b B t => validpos b p
    | let_ty, tLetIn na b B t => validpos B p
    | let_in, tLetIn na b B t => validpos t p
    | array_def, tPrim (primArray; primArrayModel a) => validpos (array_default a) p
    | array_ty, tPrim (primArray; primArrayModel a) => validpos (array_type a) p
    | array_val n, tPrim (primArray; primArrayModel a) =>
      match nth_error (array_value a) n with
      | Some d => validpos d p
      | None => false
      end
    | _, _ => false
    end
  end.

Definition pos (t : term) := { p : position | validpos t p = true }.

Arguments exist {_ _} _ _.

Definition dapp_l u v (p : pos u) : pos (tApp u v) :=
  exist (app_l :: proj1_sig p) (proj2_sig p).

Definition dapp_r u v (p : pos v) : pos (tApp u v) :=
  exist (app_r :: proj1_sig p) (proj2_sig p).

Definition dcase_preturn ci pr c brs (p : pos pr.(preturn)) : pos (tCase ci pr c brs) :=
  exist (case_preturn :: proj1_sig p) (proj2_sig p).

Definition dcase_c ci pr c brs (p : pos c) : pos (tCase ci pr c brs) :=
  exist (case_c :: proj1_sig p) (proj2_sig p).

(* Equations dcase_brs (n : nat) (ci : inductive × nat)
  (pr c : term) (brs : list (nat × term)) (m : nat) (br : term)
  (h : nth_error brs n = Some (m,br))
  (p : pos br) : pos (tCase ci pr c brs) :=
  dcase_brs n ci pr c brs m br h p :=
    exist (case_brs n :: ` p) _.
Next Obligation.
  rewrite h. exact (proj2_sig p).
Qed.
Transparent dcase_brs. *)

Definition dproj_c pr c (p : pos c) : pos (tProj pr c) :=
  exist (proj_c :: proj1_sig p) (proj2_sig p).

Definition dlam_ty na A t (p : pos A) : pos (tLambda na A t) :=
  exist (lam_ty :: proj1_sig p) (proj2_sig p).

Definition dlam_tm na A t (p : pos t) : pos (tLambda na A t) :=
  exist (lam_tm :: proj1_sig p) (proj2_sig p).

Definition dprod_l na A B (p : pos A) : pos (tProd na A B) :=
  exist (prod_l :: proj1_sig p) (proj2_sig p).

Definition dprod_r na A B (p : pos B) : pos (tProd na A B) :=
  exist (prod_r :: proj1_sig p) (proj2_sig p).

Definition dlet_bd na b B t (p : pos b) : pos (tLetIn na b B t) :=
  exist (let_bd :: proj1_sig p) (proj2_sig p).

Definition dlet_ty na b B t (p : pos B) : pos (tLetIn na b B t) :=
  exist (let_ty :: proj1_sig p) (proj2_sig p).

Definition dlet_in na b B t (p : pos t) : pos (tLetIn na b B t) :=
  exist (let_in :: proj1_sig p) (proj2_sig p).

Lemma eq_context_upto_context_choice_term Σ cmp_universe cmp_sort pb Γ Γ' c :
  eq_context_upto Σ cmp_universe cmp_sort pb Γ Γ' ->
  rel_option (eq_term_upto_univ Σ cmp_universe cmp_sort (match c.2 with
                                      | choose_decl_body => Conv
                                      | choose_decl_type => pb
                                      end) )
             (context_choice_term Γ c)
             (context_choice_term Γ' c).
Proof.
  intros eq.
  destruct c as (n&c).
  eapply eq_context_upto_nth_error with (ctx := Γ) (ctx' := Γ') (n := n) in eq.
  depelim eq; cbn in *.
  - rewrite H, H0.
    destruct e as ((?&?)&?); cbn in *.
    destruct a, b; cbn in *.
    destruct c; auto.
    constructor; auto.
  - rewrite H, H0.
    constructor.
Qed.

Lemma eq_term_upto_valid_pos :
  forall {Σ u v p cmp_universe cmp_sort pb napp},
    validpos u p ->
    eq_term_upto_univ_napp Σ cmp_universe cmp_sort pb napp u v ->
    validpos v p.
Proof.
  intros Σ u v p cmp_universe cmp_sort pb napp vp e.
  induction p as [| c p ih ] in u, v, pb, napp, vp, e |- *.
  - reflexivity.
  - destruct c, u. all: try discriminate.
    all: try solve [
      dependent destruction e ; simpl ;
      eapply ih ; eauto
    ].
    + dependent destruction e. simpl in *.
      destruct (nth_error (pparams p0) n) as [par|] eqn:enth. 2: discriminate.
      destruct e.
      induction a in n, par, enth, ih, vp |- *. 1: rewrite enth. 1: assumption.
      destruct n.
      * simpl in *. apply some_inj in enth. subst.
        intuition eauto.
      * simpl in *. eapply IHa. all: eauto.
    + dependent destruction e. simpl in *.
      eapply ih; eauto. apply e.
    + dependent destruction e. simpl in *.
      destruct nth_error eqn:nth; [|congruence].
      eapply All2_nth_error_Some in e1; eauto.
      destruct e1 as (?&->&_&eq).
      eauto.
    + dependent destruction e. simpl in *.
      destruct (nth_error mfix n) as [[na ty bo ra]|] eqn:e1. 2: discriminate.
      eapply All2_nth_error_Some in e; eauto.
      destruct e as (?&->&H&_).
      now eapply ih.
    + dependent destruction e. simpl in *.
      destruct (nth_error mfix n) as [[na ty bo ra]|] eqn:e1. 2: discriminate.
      eapply All2_nth_error_Some in e; eauto.
      destruct e as (?&->&_&H&_).
      now eapply ih.
    + dependent destruction e. simpl in *.
      destruct (nth_error mfix n) as [[na ty bo ra]|] eqn:e1. 2: discriminate.
      eapply All2_nth_error_Some in e; eauto.
      destruct e as (?&->&H&_).
      now eapply ih.
    + dependent destruction e. simpl in *.
      destruct (nth_error mfix n) as [[na ty bo ra]|] eqn:e1. 2: discriminate.
      eapply All2_nth_error_Some in e; eauto.
      destruct e as (?&->&_&H&_).
      now eapply ih.
    + depelim e. depelim o; eauto.
    + depelim e; depelim o; eauto.
    + depelim e. depelim o; eauto.
      cbn in vp. destruct (nth_error (array_value a) n) eqn:e'; try discriminate.
      cbn. eapply All2_nth_error_Some in a0 as [t' [-> ?]]; tea. eapply ih; tea.
Qed.

Lemma eq_term_valid_pos :
  forall `{cf : checker_flags} {Σ G u v p},
    validpos u p ->
    eq_term Σ G u v ->
    validpos v p.
Proof.
  intros cf Σ G u v p vp e.
  eapply eq_term_upto_valid_pos. all: eauto.
Qed.

Inductive positionR : position -> position -> Prop :=
| positionR_app_lr p q : positionR (app_r :: p) (app_l :: q)
| positionR_deep c p q : positionR p q -> positionR (c :: p) (c :: q)
| positionR_root c p : positionR (c :: p) [].

Derive Signature for positionR.

Definition posR {t} (p q : pos t) : Prop :=
  positionR (proj1_sig p) (proj1_sig q).

Lemma posR_Acc :
  forall t p, Acc (@posR t) p.
Proof.
  assert (forall pr c p, Acc posR p -> Acc posR (dproj_c pr c p))
    as Acc_proj_c.
  { intros pr c p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na b B t p, Acc posR p -> Acc posR (dlet_bd na b B t p))
    as Acc_let_bd.
  { intros na b B t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na b B t p, Acc posR p -> Acc posR (dlet_ty na b B t p))
    as Acc_let_ty.
  { intros na b B t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na b B t p, Acc posR p -> Acc posR (dlet_in na b B t p))
    as Acc_let_in.
  { intros na b B t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A B p, Acc posR p -> Acc posR (dprod_l na A B p))
    as Acc_prod_l.
  { intros na A B p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A B p, Acc posR p -> Acc posR (dprod_r na A B p))
    as Acc_prod_r.
  { intros na A B p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A t p, Acc posR p -> Acc posR (dlam_ty na A t p))
    as Acc_lam_ty.
  { intros na A t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall na A t p, Acc posR p -> Acc posR (dlam_tm na A t p))
    as Acc_lam_tm.
  { intros na A t p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (forall u v p, Acc posR p -> Acc posR (dapp_r u v p))
    as Acc_app_r.
  { intros u v p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h. cbn in e.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall u v p,
      Acc posR p ->
      (forall q : pos v, Acc posR q) ->
      Acc posR (dapp_l u v p)
  ) as Acc_app_l.
  { intros u v p h ih.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    - eapply Acc_app_r with (p := exist p0 e). eapply ih.
    - eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall n ci pr c brs par (p : pos par)
      (e : nth_error pr.(pparams) n = Some par)
      (e1 : validpos (tCase ci pr c brs) (case_par n :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_par n :: proj1_sig p) e1)
  ) as Acc_case_pars.
  { intros n ci pr c brs par p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos par in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall ci pr c brs p,
      Acc posR p ->
      Acc posR (dcase_preturn ci pr c brs p)
  ) as Acc_case_p.
  { intros ci pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall ci pr c brs p,
      Acc posR p ->
      Acc posR (dcase_c ci pr c brs p)
  ) as Acc_case_c.
  { intros ci pr c brs p h.
    induction h as [p ih1 ih2].
    constructor. intros [q e] h.
    dependent destruction h.
    eapply (ih2 (exist p0 e)). assumption.
  }
  assert (
    forall n ci pr c brs br (p : pos br.(bbody))
      (e : nth_error brs n = Some br)
      (e1 : validpos (tCase ci pr c brs) (case_brsbody n :: proj1_sig p) = true),
      Acc posR p ->
      Acc posR (exist (case_brsbody n :: proj1_sig p) e1)
  ) as Acc_case_brs.
  { intros n ci pr c brs br p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos br.(bbody) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n mfix idx d (p : pos d.(dtype))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tFix mfix idx) (fix_mfix_ty n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (fix_mfix_ty n :: proj1_sig p) e1)
  ) as Acc_fix_mfix_ty.
  { intros n mfix idx d p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos d.(dtype) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n mfix idx d (p : pos d.(dbody))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tFix mfix idx) (fix_mfix_bd n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (fix_mfix_bd n :: proj1_sig p) e1)
  ) as Acc_fix_mfix_bd.
  { intros n mfix idx d p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos d.(dbody) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n mfix idx d (p : pos d.(dtype))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tCoFix mfix idx) (cofix_mfix_ty n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (cofix_mfix_ty n :: proj1_sig p) e1)
  ) as Acc_cofix_mfix_ty.
  { intros n mfix idx d p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos d.(dtype) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall n mfix idx d (p : pos d.(dbody))
      (e : nth_error mfix n = Some d)
      (e1 : validpos (tCoFix mfix idx) (cofix_mfix_bd n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (cofix_mfix_bd n :: proj1_sig p) e1)
  ) as Acc_cofix_mfix_bd.
  { intros n mfix idx d p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos d.(dbody) in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall a (p : pos a.(array_default))
      (e : validpos (tPrim (primArray; primArrayModel a)) (array_def :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (array_def :: proj1_sig p) e)
  ) as Acc_array_def.
  { intros a p e h.
    induction h as [p ih1 ih2] in e |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos a.(array_default) in _).
    - simpl. cbn in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall a (p : pos a.(array_type))
      (e : validpos (tPrim (primArray; primArrayModel a)) (array_ty :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (array_ty :: proj1_sig p) e)
  ) as Acc_array_ty.
  { intros a p e h.
    induction h as [p ih1 ih2] in e |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos a.(array_type) in _).
    - simpl. cbn in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  assert (
    forall a n v (p : pos v)
      (e : nth_error a.(array_value) n = Some v)
      (e1 : validpos (tPrim (primArray; primArrayModel a)) (array_val n :: proj1_sig p)),
      Acc posR p ->
      Acc posR (exist (array_val n :: proj1_sig p) e1)
  ) as Acc_array_val.
  { intros a n v p e e1 h.
    induction h as [p ih1 ih2] in e, e1 |- *.
    constructor. intros [q e2] h.
    dependent destruction h.
    simple refine (let q := exist p0 _ : pos v in _).
    - simpl. cbn in e2. rewrite e in e2. assumption.
    - specialize (ih2 q). eapply ih2. all: assumption.
  }
  intro t. induction t using term_forall_list_ind ; intros q.
  all: try solve [
             destruct q as [q e] ; destruct q as [| c q] ; [
               constructor ; intros [p' e'] h ;
               unfold posR in h ; cbn in h ;
               dependent destruction h ;
               destruct c ; cbn in e' ; discriminate
             | destruct c ; cbn in e ; discriminate
             ]
           ].
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_prod_l with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_prod_r with (p := exist p0 e').
        eapply IHt2.
    + destruct c ; noconf e.
      * eapply Acc_prod_l with (p := exist q e).
        eapply IHt1.
      * eapply Acc_prod_r with (p := exist q e).
        eapply IHt2.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_lam_ty with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_lam_tm with (p := exist p0 e').
        eapply IHt2.
    + destruct c ; noconf e.
      * eapply Acc_lam_ty with (p := exist q e).
        eapply IHt1.
      * eapply Acc_lam_tm with (p := exist q e).
        eapply IHt2.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_let_bd with (p := exist p0 e').
        eapply IHt1.
      * eapply Acc_let_ty with (p := exist p0 e').
        eapply IHt2.
      * eapply Acc_let_in with (p := exist p0 e').
        eapply IHt3.
    + destruct c ; noconf e.
      * eapply Acc_let_bd with (p := exist q e).
        eapply IHt1.
      * eapply Acc_let_ty with (p := exist q e).
        eapply IHt2.
      * eapply Acc_let_in with (p := exist q e).
        eapply IHt3.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * eapply Acc_app_l with (p := exist p0 e').
        -- eapply IHt1.
        -- assumption.
      * eapply Acc_app_r with (p := exist p0 e').
        eapply IHt2.
    + destruct c ; noconf e.
      * eapply Acc_app_l with (p := exist q e).
        -- eapply IHt1.
        -- assumption.
      * eapply Acc_app_r with (p := exist q e).
        eapply IHt2.
  - destruct X as [IHXpars IHXpred].
    destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      * simpl in e'.
        case_eq (nth_error (pparams p) n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros par e1.
        eapply All_nth_error in IHXpars as ihpar. 2: exact e1.
        unshelve eapply Acc_case_pars with (1 := e1) (p := exist p0 _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihpar.
      * eapply Acc_case_p with (p := exist p0 e').
        eapply IHXpred.
      * eapply Acc_case_c with (p := exist p0 e').
        eapply IHt.
      * simpl in e'.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros br e1.
        eapply All_nth_error in X0 as ihbr. 2: exact e1.
        simpl in ihbr.
        unshelve eapply Acc_case_brs with (1 := e1) (p := exist p0 _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihbr.
    + destruct c ; noconf e.
      * simpl in e.
        case_eq (nth_error (pparams p) n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros par e1.
        eapply All_nth_error in IHXpars as ihpar. 2: exact e1.
        unshelve eapply Acc_case_pars with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihpar.
      * eapply Acc_case_p with (p := exist q e).
        eapply IHXpred.
      * eapply Acc_case_c with (p := exist q e).
        eapply IHt.
      * simpl in e.
        case_eq (nth_error l n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros br e1.
        eapply All_nth_error in X0 as ihbr. 2: exact e1.
        simpl in ihbr.
        unshelve eapply Acc_case_brs with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihbr.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c ; noconf e'.
      eapply Acc_proj_c with (p := exist p e').
      eapply IHt.
    + destruct c ; noconf e.
      eapply Acc_proj_c with (p := exist q e).
      eapply IHt.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c. all: noconf e'.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_ty with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_bd with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
    + destruct c. all: noconf e.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_ty with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_fix_mfix_bd with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct c. all: noconf e'.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_ty with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
      * simpl in e'.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_bd with (1 := e1) (p := exist p _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
    + destruct c. all: noconf e.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_ty with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
      * simpl in e.
        case_eq (nth_error m n0).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros [na ty bo ra] e1.
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_cofix_mfix_bd with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
  - destruct q as [q e]. destruct q as [| c q].
    + constructor. intros [p' e'] h.
      unfold posR in h. cbn in h.
      dependent destruction h.
      destruct p as [? []];
      destruct c. all: noconf e'.
      * eapply Acc_array_def with (p := exist p0 e'), X.
      * eapply Acc_array_ty with (p := exist p0 e'), X.
      * simpl in e'.
        case_eq (nth_error (array_value a) n).
        2:{ intro h. pose proof e' as hh. rewrite h in hh. discriminate. }
        intros v e1. destruct X as [_ [_ X]].
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_array_val with (1 := e1) (p := exist p0 _).
        -- simpl. rewrite e1 in e'. assumption.
        -- eapply ihm.
    + destruct p as [? []]; destruct c; noconf e.
      * eapply Acc_array_def with (p := exist q e), X.
      * eapply Acc_array_ty with (p := exist q e), X.
      * simpl in e.
        case_eq (nth_error (array_value a) n).
        2:{ intro h. pose proof e as hh. rewrite h in hh. discriminate. }
        intros v e1. destruct X as [_ [_ X]].
        eapply All_nth_error in X as ihm. 2: exact e1.
        simpl in ihm.
        unshelve eapply Acc_array_val with (1 := e1) (p := exist q _).
        -- simpl. rewrite e1 in e. assumption.
        -- eapply ihm.
Qed.

Fixpoint atpos t (p : position) {struct p} : term :=
  match p with
  | [] => t
  | c :: p =>
    match c, t with
    | app_l, tApp u v => atpos u p
    | app_r, tApp u v => atpos v p
    | case_par n, tCase ci pr c brs =>
      match nth_error pr.(pparams) n with
      | Some par => atpos par p
      | None => tRel 0
      end
    | case_preturn, tCase ci pr c brs => atpos pr.(preturn) p
    | case_c, tCase ci pr c brs => atpos c p
    | case_brsbody n, tCase ci pr c brs =>
        match nth_error brs n with
        | Some br => atpos br.(bbody) p
        | None => tRel 0
        end
    | proj_c, tProj pr c => atpos c p
    | fix_mfix_ty n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dtype) p
        | None => tRel 0
        end
    | fix_mfix_bd n, tFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dbody) p
        | None => tRel 0
        end
    | cofix_mfix_ty n, tCoFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dtype) p
        | None => tRel 0
        end
    | cofix_mfix_bd n, tCoFix mfix idx =>
        match nth_error mfix n with
        | Some d => atpos d.(dbody) p
        | None => tRel 0
        end
    | lam_ty, tLambda na A t => atpos A p
    | lam_tm, tLambda na A t => atpos t p
    | prod_l, tProd na A B => atpos A p
    | prod_r, tProd na A B => atpos B p
    | let_bd, tLetIn na b B t => atpos b p
    | let_ty, tLetIn na b B t => atpos B p
    | let_in, tLetIn na b B t => atpos t p
    | array_def, tPrim (primArray; primArrayModel a) => atpos a.(array_default) p
    | array_ty, tPrim (primArray; primArrayModel a) => atpos a.(array_type) p
    | array_val n, tPrim (primArray; primArrayModel a) =>
      match nth_error a.(array_value) n with
      | Some v => atpos v p
      | None => tRel 0
      end
    | _, _ => tRel 0
    end
  end.

Lemma poscat_atpos :
  forall t p q, atpos t (p ++ q) = atpos (atpos t p) q.
Proof.
  assert (forall p, atpos (tRel 0) p = tRel 0) as hh.
  { intros p. destruct p.
    - reflexivity.
    - destruct c ; reflexivity.
  }
  intros t p q.
  revert t q. induction p ; intros t q.
  - cbn. reflexivity.
  - destruct t ; destruct a.
    all: try solve [ rewrite hh ; reflexivity ].
    all: try apply IHp.
    + simpl. destruct nth_error as [?|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + simpl. destruct nth_error as [[na ty bo ra]|] eqn:e.
      * apply IHp.
      * rewrite hh. reflexivity.
    + destruct prim as [? []]; simpl. 1-3:now rewrite hh.
      now rewrite IHp.
    + destruct prim as [? []]; simpl. 1-3:now rewrite hh.
      now rewrite IHp.
    + destruct prim as [? []]; simpl. 1-3:now rewrite hh.
      destruct nth_error eqn:e.
      * now rewrite IHp.
      * now rewrite hh.
Qed.

Lemma poscat_valid :
  forall t p q,
    validpos t p ->
    validpos (atpos t p) q ->
    validpos t (p ++ q).
Proof.
  intros t p q hp hq.
  revert t q hp hq.
  induction p ; intros t q hp hq.
  - assumption.
  - destruct t ; destruct a.
    all: try noconf hp.
    all: try (apply IHp ; assumption).
    all: simpl in *;
      repeat
        match goal with
        | [prim: prim_val |- _] => destruct prim as [? []]
        | [H: context[nth_error ?a ?b] |- _] =>
          destruct (nth_error a b); [|discriminate]
        | [H: context[context_choice_term ?a ?b] |- _] =>
          destruct (context_choice_term a b); [|discriminate]
        end;
      auto.
Qed.

Lemma positionR_poscat :
  forall p q1 q2,
    positionR q1 q2 ->
    positionR (p ++ q1) (p ++ q2).
Proof.
  intro p. induction p ; intros q1 q2 h.
  - assumption.
  - cbn. constructor. eapply IHp. assumption.
Qed.

Lemma atpos_assoc :
  forall t p q,
    atpos (atpos t p) q = atpos t (p ++ q).
Proof.
  intros t p q. revert t q.
  induction p ; intros t q.
  - reflexivity.
  - destruct a, t.
    all: simpl.
    all: try apply IHp.
    all: destruct q ; try reflexivity.
    all: try (destruct c ; reflexivity).
    all:
      repeat
        match goal with
        | [prim: prim_val |- _] => destruct prim as [? []]
        | |- context[nth_error ?a ?b] =>
          destruct (nth_error a b); auto
        | |- context[context_choice_term ?a ?b] =>
          destruct (context_choice_term a b); auto
        end.
    all: rewrite ?app_nil_r.
    all: simpl; auto.
    all: try solve [destruct c; auto]; try solve [destruct c0; auto].
    all: rewrite <- IHp; auto.
Qed.

Lemma positionR_trans : Transitive positionR.
Proof.
  intros p q r h1 h2.
  revert r h2.
  induction h1 ; intros r h2.
  - dependent induction h2.
    + constructor.
    + constructor.
  - dependent induction h2.
    + constructor.
    + constructor. eapply IHh1. assumption.
    + constructor.
  - dependent induction h2.
Qed.

Lemma posR_trans :
  forall t, Transitive (@posR t).
Proof.
  intros t p q r h1 h2.
  eapply positionR_trans ; eassumption.
Qed.

Lemma positionR_poscat_nonil :
  forall p q, q <> [] -> positionR (p ++ q) p.
Proof.
  intros p q e.
  revert q e.
  induction p ; intros q e.
  - destruct q ; nodec.
    exfalso. apply e. reflexivity.
  - cbn. constructor. apply IHp. assumption.
Qed.

(* Hole in fixpoint definition *)
Variant def_hole :=
| def_hole_type (dname : aname) (dbody : term) (rarg : nat)
| def_hole_body (dname : aname) (dtype : term) (rarg : nat).

Definition mfix_hole := mfixpoint term * def_hole * mfixpoint term.

(* Represents a context_decl with a hole in it *)
Variant context_decl_hole : Type :=
| decl_hole_type (na : aname) (body : option term)
| decl_hole_body (na : aname) (type : term).

(* Represents a context with a hole in it *)
Definition context_hole := context * context_decl_hole * context.

Variant predicate_hole :=
| pred_hole_params
    (params1 params2 : list term)
    (puinst : Instance.t)
    (pcontext : context)
    (preturn : term)
| pred_hole_return
    (pparams : list term)
    (puinst : Instance.t)
    (pcontext : context).

Variant branch_hole :=
| branch_hole_body (bcontext : context).

Definition branches_hole := list (branch term) * branch_hole * list (branch term).

(* Represents a non-nested term with a hole in it *)
Variant stack_entry : Type :=
| App_l (v : term) (* Hole in head *)
| App_r (u : term) (* Hole in arg *)
(* Hole in the argument a primitive operation is evaluating.  The arguments
   already in weak-head normal form are [done]; those still to evaluate stay
   on the stack, as [Fix_app] leaves them. *)
| Prim_app
    (c : kername) (u : Instance.t) (op : prim_op) (done : list term)
| Fix_app (* Hole in last arg *)
    (mfix : mfixpoint term) (idx : nat) (args : list term)
| Fix (mfix : mfix_hole) (idx : nat)
| CoFix_app (* Hole in last arg *)
    (mfix : mfixpoint term) (idx : nat) (args : list term)
| CoFix (mfix : mfix_hole) (idx : nat)
| Case_pred (* Hole in predicate *)
    (ci : case_info)
    (p : predicate_hole)
    (c : term)
    (brs : list (branch term))
| Case_discr (* Hole in scrutinee *)
    (ci : case_info)
    (p : predicate term)
    (brs : list (branch term))
| Case_branch (* Hole in branch *)
    (ci : case_info)
    (p : predicate term)
    (c : term)
    (brs : branches_hole)
| Proj (* Hole in projectee *)
    (p : projection)
| Prod_l (na : aname) (B : term)
| Prod_r (na : aname) (A : term)
| Lambda_ty (na : aname) (b : term)
| Lambda_bd (na : aname) (A : term)
| LetIn_bd (na : aname) (B t : term)
| LetIn_ty (na : aname) (b t : term)
| LetIn_in (na : aname) (b B : term)
| PrimArray_ty (l : Level.t) (l : list term) (def : term)
| PrimArray_def (l : Level.t) (l : list term) (ty : term)
(* Hole in one of the values *)
| PrimArray_val (l : Level.t) (bef : list term) (after : list term) (def : term) (ty : term)
(* BET-315 eta: read-time lifted eta frame. [Eta_app na A] holds the eta binder [vass na A]
   for the eta-aware views but is transparent to [zipc] (fill_hole = identity). *)
| Eta_app (na : aname) (A : term)
(* BET-315 eta: focus-dropping virtual-argument frame. [Eta_arg t args] records the real
   head/spine so that [fill_hole _ (Eta_arg t args) = mkApps t args] (the hole is dropped). *)
| Eta_arg (t : term) (args : list term).

Definition stack := list stack_entry.

Derive NoConfusion for def_hole context_decl_hole predicate_hole branch_hole stack_entry.

#[global]
Instance EqDec_def_hole : EqDec def_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

#[global]
Instance EqDec_context_decl_hole : EqDec context_decl_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

#[global]
Instance EqDec_predicate_hole : EqDec predicate_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

#[global]
Instance EqDec_branch_hole : EqDec branch_hole.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

#[global]
Instance EqDec_stack_entry : EqDec stack_entry.
Proof. intros ? ?; decide equality; apply eq_dec. Defined.

#[global]
Instance reflect_stack : ReflectEq stack :=
  let h := EqDec_ReflectEq stack in _.

Definition fill_mfix_hole '((mfix1, m, mfix2) : mfix_hole) (t : term) : mfixpoint term :=
  let def :=
      match m with
      | def_hole_type dname dbody rarg =>
        {| dname := dname;
           dtype := t;
           dbody := dbody;
           rarg := rarg |}
      | def_hole_body dname dtype rarg =>
        {| dname := dname;
           dtype := dtype;
           dbody := t;
           rarg := rarg |}
      end in
  mfix1 ++ (def :: mfix2).

Definition fill_context_hole '((ctx1, decl, ctx2) : context_hole) (t : term) : context :=
  let decl :=
      match decl with
      | decl_hole_type na body =>
        {| decl_name := na; decl_body := body; decl_type := t |}
      | decl_hole_body na type => {| decl_name := na; decl_body := Some t; decl_type := type |}
      end in
  ctx1 ,,, [decl] ,,, ctx2.

Definition fill_predicate_hole (p : predicate_hole) (t : term) : predicate term :=
  match p with
  | pred_hole_params params1 params2 puinst pcontext preturn =>
    {| pparams := params1 ++ (t :: params2);
       puinst := puinst;
       pcontext := pcontext;
       preturn := preturn |}
  | pred_hole_return pparams puinst pcontext =>
    {| pparams := pparams;
       puinst := puinst;
       pcontext := pcontext;
       preturn := t |}
  end.

Definition fill_branches_hole '((brs1, br, brs2) : branches_hole) (t : term) : list (branch term) :=
  let br :=
      match br with
      | branch_hole_body bcontext =>
        {| bcontext := bcontext; bbody := t |}
      end in
  brs1 ++ (br :: brs2).

Definition fill_hole (t : term) (se : stack_entry) : term :=
  match se with
  | App_l v => tApp t v
  | App_r u => tApp u t
  | Prim_app c u op done => tApp (mkApps (tConst c u) done) t
  | Fix_app mfix idx args => tApp (mkApps (tFix mfix idx) args) t
  | Fix mfix idx => tFix (fill_mfix_hole mfix t) idx
  | CoFix_app mfix idx args => tApp (mkApps (tCoFix mfix idx) args) t
  | CoFix mfix idx => tCoFix (fill_mfix_hole mfix t) idx
  | Case_pred ci p c brs => tCase ci (fill_predicate_hole p t) c brs
  | Case_discr ci p brs => tCase ci p t brs
  | Case_branch ci p c brs => tCase ci p c (fill_branches_hole brs t)
  | Proj p => tProj p t
  | Prod_l na B => tProd na t B
  | Prod_r na A => tProd na A t
  | Lambda_ty na b => tLambda na t b
  | Lambda_bd na A => tLambda na A t
  | LetIn_bd na B u => tLetIn na t B u
  | LetIn_ty na b u => tLetIn na b t u
  | LetIn_in na b B => tLetIn na b B t
  | PrimArray_def l v ty => tPrim (primArray; primArrayModel {| array_level := l; array_value := v; array_default := t; array_type := ty |})
  | PrimArray_ty l v def => tPrim (primArray; primArrayModel {| array_level := l; array_value := v; array_default := def; array_type := t |})
  | PrimArray_val l bef after def ty => tPrim (primArray; primArrayModel {| array_level := l; array_value := bef ++ (t :: after); array_default := def; array_type := ty |})
  (* BET-315 eta: [Eta_app] is transparent (identity on the focus); [Eta_arg t args]
     drops the hole and restores the real term [mkApps t args]. *)
  | Eta_app na A => t
  | Eta_arg u args => mkApps u args
  end.

(* Not using fold_left here to get the right unfolding behavior *)
Fixpoint zipc (t : term) (stack : stack) : term :=
  match stack with
  | [] => t
  | se :: stack => zipc (fill_hole t se) stack
  end.

Definition zip (t : term * stack) : term := zipc (fst t) (snd t).

Tactic Notation "zip" "fold" "in" hyp(h) :=
  lazymatch type of h with
  | context C[ zipc ?t ?π ] =>
    let C' := context C[ zip (t,π) ] in
    change C' in h
  end.

Tactic Notation "zip" "fold" :=
  lazymatch goal with
  | |- context C[ zipc ?t ?π ] =>
    let C' := context C[ zip (t,π) ] in
    change C'
  end.

(* TODO Tail-rec version *)
(* Get the arguments out of a stack *)
Fixpoint decompose_stack (π : stack) : list term × stack :=
  match π with
  | App_l u :: π => let '(l,π) := decompose_stack π in (u :: l, π)
  | _ => ([], π)
  end.

(* TODO Tail-rec *)
Definition appstack (l : list term) (π : stack) : stack :=
  map App_l l ++ π.

Lemma decompose_stack_eq :
  forall π l ρ,
    decompose_stack π = (l, ρ) ->
    π = appstack l ρ.
Proof.
  intros π l ρ eq.
  revert l ρ eq. induction π ; intros l ρ eq.
  - noconf eq; auto.
  - cbn in *.
    destruct decompose_stack.
    destruct a; noconf eq; cbn in *; auto.
    f_equal.
    eauto.
Qed.

Lemma decompose_stack_not_app :
  forall π l u ρ,
    decompose_stack π = (l, App_l u :: ρ) -> False.
Proof.
  intros π l u ρ eq.
  revert u l ρ eq. induction π ; intros u l ρ eq.
  - noconf eq.
  - cbn in eq.
    destruct decompose_stack.
    destruct a; noconf eq; cbn in *; auto.
    eauto.
Qed.

Lemma zipc_appstack :
  forall {t args ρ},
    zipc t (appstack args ρ) = zipc (mkApps t args) ρ.
Proof.
  intros t args ρ. revert t ρ. induction args ; intros t ρ.
  - cbn. reflexivity.
  - cbn. apply IHargs.
Qed.

Lemma decompose_stack_appstack :
  forall l ρ,
    decompose_stack (appstack l ρ) =
    (l ++ fst (decompose_stack ρ), snd (decompose_stack ρ)).
Proof.
  intros l. induction l ; intros ρ.
  - cbn. destruct (decompose_stack ρ). reflexivity.
  - cbn. rewrite IHl. reflexivity.
Qed.

Fixpoint decompose_stack_at π n : option (list term * term * stack) :=
  match π with
  | App_l u :: π =>
    match n with
    | 0 => ret ([], u, π)
    | S n =>
      r <- decompose_stack_at π n ;;
        let '(l, v, π) := r in
        ret (u :: l, v, π)
    end
  | _ => None
  end.

Lemma decompose_stack_at_eq :
  forall π n l u ρ,
    decompose_stack_at π n = Some (l,u,ρ) ->
    π = appstack l (App_l u :: ρ).
Proof.
  intros π n l u ρ h.
  induction π in n, l, u, ρ, h |- *.
  - noconf h.
  - cbn in h.
    destruct n as [|n].
    + destruct a; noconf h; auto.
    + specialize (IHπ n).
      destruct decompose_stack_at.
      * destruct p as ((?&?)&?).
        destruct a; noconf h.
        cbn.
        f_equal; eauto.
      * destruct a; noconf h.
Qed.

Lemma decompose_stack_at_length :
  forall π n l u ρ,
    decompose_stack_at π n = Some (l,u,ρ) ->
    #|l| = n.
Proof.
  intros π n l u ρ h.
  induction π in n, l, u, ρ, h |- *.
  - noconf h.
  - cbn in h.
    destruct n as [|n].
    + destruct a; noconf h; auto.
    + specialize (IHπ n).
      destruct decompose_stack_at.
      * destruct p as ((?&?)&?).
        destruct a; noconf h.
        cbn.
        f_equal; eauto.
      * destruct a; noconf h.
Qed.

(* TODO Find a better place for this. *)
(* The current fix_context asks for too much information. *)
Definition fix_context_alt (l : list (aname × term)) : context :=
  List.rev (mapi (fun i d => vass d.1 (lift0 i d.2)) l).

Definition def_sig (d : def term) : aname × term :=
  (d.(dname), d.(dtype)).

Lemma fix_context_fix_context_alt :
  forall m,
    fix_context m = fix_context_alt (map def_sig m).
Proof.
  intros m.
  unfold fix_context_alt, fix_context.
  f_equal. rewrite mapi_map. eapply mapi_ext.
  intros i [na ty bo ra]. simpl. reflexivity.
Qed.

Definition mfix_hole_context '((mfix1, def, mfix2) : mfix_hole) : context :=
  match def with
  | def_hole_type _ _ _ => []
  | def_hole_body na ty _ =>
    fix_context_alt (map def_sig mfix1 ++ (na, ty) :: map def_sig mfix2)
  end.

Definition context_hole_context '((ctx1, decl, ctx2) : context_hole) : context :=
  ctx1.

Definition predicate_hole_context (p : predicate_hole) : context :=
  match p with
  | pred_hole_params _ _ _ _ _ => []
  | pred_hole_return pparams puinst pcontext =>
    inst_case_context pparams puinst pcontext
  end.

Definition branches_hole_context p '((brs1, br, brs2) : branches_hole) : context :=
  match br with
  | branch_hole_body bcontext => inst_case_context p.(pparams) p.(puinst) bcontext
  end.

Definition stack_entry_context (se : stack_entry) : context :=
  match se with
  | Fix mfix idx => mfix_hole_context mfix
  | CoFix mfix idx => mfix_hole_context mfix
  | Case_pred ci p c brs => predicate_hole_context p
  | Case_branch ci p c brs => branches_hole_context p brs
  | Prod_r na A => [vass na A]
  | Lambda_bd na A => [vass na A]
  | LetIn_in na b B => [vdef na b B]
  | _ => []
  end.

Definition stack_context : stack -> context :=
  flat_map stack_entry_context.

Lemma stack_context_appstack :
  forall {π args},
    stack_context (appstack args π) = stack_context π.
Proof.
  intros π args.
  revert π. induction args ; intros π.
  - reflexivity.
  - simpl. apply IHargs.
Qed.

Definition closedn_mfix_hole k '((mfix1, m, mfix2) : mfix_hole) : bool :=
  let k' := (k + #|mfix1| + 1 + #|mfix2|) in
  let def :=
      match m with
      | def_hole_type dname dbody rarg =>
        closedn k' dbody
      | def_hole_body dname dtype rarg =>
        closedn k dtype
      end in
  [&& forallb (test_def (closedn k) (closedn k')) mfix1,
      def & forallb (test_def (closedn k) (closedn k')) mfix2].

Definition closedn_context_hole k '((ctx1, decl, ctx2) : context_hole) : bool :=
  let decl :=
      match decl with
      | decl_hole_type na body => option_default (closedn (k + #|ctx1|)) body true
      | decl_hole_body na type => closedn (k + #|ctx1|) type
      end in
  [&& closedn_ctx k ctx1, decl & closedn_ctx (k + S #|ctx1|) ctx2].

Definition closedn_predicate_hole k (p : predicate_hole) : bool :=
  match p with
  | pred_hole_params params1 params2 puinst pcontext preturn =>
    [&& forallb (closedn k) params1,
        forallb (closedn k) params2,
        closedn_ctx (#|params1| + S #|params2|) pcontext &
        closedn (k + #|pcontext|) preturn]
  | pred_hole_return pparams puinst pcontext =>
    forallb (closedn k) pparams && closedn_ctx #|pparams| pcontext
  end.

Definition predicate_hole_pars (p : predicate_hole) : nat :=
  match p with
  | pred_hole_params params1 params2 puinst pcontext preturn =>
    #|params1| + 1 + #|params2|
  | pred_hole_return pparams puinst pcontext => #|pparams|
  end.

Definition closedn_branches_hole k (pred : predicate term) '((brs1, br, brs2) : branches_hole) : bool :=
  let br :=
      match br with
      | branch_hole_body bcontext => closedn_ctx #|pparams pred| bcontext
      end in
  [&& test_branches_k pred closedn k brs1, br &
      test_branches_k pred closedn k brs2].

Definition test_branch_k_pars ppars (p : nat -> term -> bool) k (b : branch term) :=
  test_context_k p ppars b.(bcontext) && p (#|b.(bcontext)| + k) b.(bbody).

Notation test_branches_k_pars p test k brs :=
  (List.forallb (test_branch_k_pars p test k) brs).

Definition closedn_stack_entry k se :=
  match se with
  | App_l v => closedn k v
  | App_r u => closedn k u
  | Prim_app c u op done => closedn k (mkApps (tConst c u) done)
  | Fix_app mfix idx args => closedn k (mkApps (tFix mfix idx) args)
  | Fix mfix idx => closedn_mfix_hole k mfix
  | CoFix_app mfix idx args => closedn k (mkApps (tCoFix mfix idx) args)
  | CoFix mfix idx => closedn_mfix_hole k mfix
  | Case_pred ci p c brs =>
    [&& closedn_predicate_hole k p, closedn k c &
        test_branches_k_pars (predicate_hole_pars p) closedn k brs]
  | Case_discr ci p brs =>
    test_predicate_k xpredT closedn k p && test_branches_k p closedn k brs
  | Case_branch ci p c brs =>
    [&& test_predicate_k xpredT closedn k p, closedn k c &
        closedn_branches_hole k p brs]
  | Proj p => true
  | Prod_l na B => closedn (S k) B
  | Prod_r na A => closedn k A
  | Lambda_ty na b => closedn (S k) b
  | Lambda_bd na A => closedn k A
  | LetIn_bd na B u => closedn k B && closedn (S k) u
  | LetIn_ty na b u => closedn k b && closedn (S k) u
  | LetIn_in na b B => closedn k b && closedn k B
  | PrimArray_def l v ty => forallb (closedn k) v && closedn k ty
  | PrimArray_ty l v def => forallb (closedn k) v && closedn k def
  | PrimArray_val l bef after def ty => forallb (closedn k) bef && forallb (closedn k) after && closedn k def && closedn k ty
  (* BET-315 eta: structural closedness. [Eta_app] is transparent (fill_hole = id), so it
     constrains no focus here; its binder [A] is scoped by the eta [closedn_zip] view. *)
  | Eta_app na A => true
  | Eta_arg u args => closedn k (mkApps u args)
  end.

Fixpoint closedn_stack k π :=
  match π with
  | [] => true
  | se :: π =>
    closedn_stack_entry (k + #|stack_context π|) se &&
    closedn_stack k π
  end.

Definition context_hole_choice '((ctx1, decl, ctx2) : context_hole) : context_choice :=
  let decl :=
      match decl with
      | decl_hole_type _ _ => choose_decl_type
      | decl_hole_body _ _ => choose_decl_body
      end in
  (#|ctx2|, decl).

Definition stack_entry_choice (se : stack_entry) : choice :=
  match se with
  | App_l v => app_l
  | App_r u => app_r
  | Prim_app c u op done => app_r
  | Fix_app mfix idx args => app_r
  | Fix (mfix1, def_hole_type _ _ _, _) idx => fix_mfix_ty #|mfix1|
  | Fix (mfix1, def_hole_body _ _ _, _) idx => fix_mfix_bd #|mfix1|
  | CoFix_app mfix idx args => app_r
  | CoFix (mfix1, def_hole_type _ _ _, _) idx => cofix_mfix_ty #|mfix1|
  | CoFix (mfix1, def_hole_body _ _ _, _) idx => cofix_mfix_bd #|mfix1|
  | Case_pred ci (pred_hole_params pars1 _ _ _ _) c brs => case_par #|pars1|
  | Case_pred ci (pred_hole_return _ _ _) c brs => case_preturn
  | Case_discr ci p brs => case_c
  | Case_branch ci p c (brs1, branch_hole_body _, brs2) => case_brsbody #|brs1|
  | Proj p => proj_c
  | Prod_l na B => prod_l
  | Prod_r na A => prod_r
  | Lambda_ty na b => lam_ty
  | Lambda_bd na A => lam_tm
  | LetIn_bd na B t => let_bd
  | LetIn_ty na b t => let_ty
  | LetIn_in na b B => let_in
  | PrimArray_def u v ty => array_def
  | PrimArray_ty u v def => array_ty
  | PrimArray_val l bef aft def ty => array_val #|bef|
  (* BET-315 eta: never consulted ([stack_position] skips both frames); dummy value. *)
  | Eta_app na A => app_l
  | Eta_arg u args => app_l
  end.

(* BET-315 eta: [stack_position] skips both eta frames. They are transparent to [zipc]
   ([Eta_app]) or focus-dropping ([Eta_arg]), so neither corresponds to a [choice] step;
   positions therefore descend only through the real structure. *)
Fixpoint stack_position (π : stack) : position :=
  match π with
  | [] => []
  | Eta_app _ _ :: π => stack_position π
  | Eta_arg _ _ :: π => stack_position π
  | se :: π => stack_position π ++ [stack_entry_choice se]
  end.

Lemma stack_position_cons_Eta_app na A π :
  stack_position (Eta_app na A :: π) = stack_position π.
Proof. reflexivity. Qed.

Lemma stack_position_cons_Eta_arg u args π :
  stack_position (Eta_arg u args :: π) = stack_position π.
Proof. reflexivity. Qed.

Lemma stack_position_cons se π :
  (forall na A, se <> Eta_app na A) ->
  (forall u args, se <> Eta_arg u args) ->
  stack_position (se :: π) =
  stack_position π ++ [stack_entry_choice se].
Proof.
  intros h1 h2.
  destruct se; try reflexivity.
  - now destruct (h1 na A).
  - now destruct (h2 t args).
Qed.

(* BET-315 eta: a frame-filter predicate. [Eta_app] is transparent and [stack_position]
   skips it, so it never breaks the position lemmas; [Eta_arg] drops the focus, so the
   three position/typing lemmas below are restated with the side condition "π has no
   [Eta_arg]" (plan.md rev 11 §3 K3(a), gate F-2/B-2). *)
Definition is_Eta_arg (se : stack_entry) : bool :=
  match se with Eta_arg _ _ => true | _ => false end.

Fixpoint no_Eta_arg (π : stack) : bool :=
  match π with
  | [] => true
  | se :: π => negb (is_Eta_arg se) && no_Eta_arg π
  end.

Lemma no_Eta_arg_cons se π :
  no_Eta_arg (se :: π) = negb (is_Eta_arg se) && no_Eta_arg π.
Proof. reflexivity. Qed.

Lemma no_Eta_arg_appstack args π :
  no_Eta_arg (appstack args π) = no_Eta_arg π.
Proof.
  unfold appstack. induction args; cbn; auto.
Qed.

Lemma stack_position_atpos :
  forall t π, no_Eta_arg π -> atpos (zipc t π) (stack_position π) = t.
Proof.
  intros t π. revert t. induction π as [|a π IH]; intros u hna.
  - reflexivity.
  - cbn in hna. apply andb_prop in hna as [ha hπ].
    pose proof (fun t => IH t hπ) as IH'. clear IH.
    destruct a; try discriminate ha;
      try (cbn [stack_position zipc fill_hole]; solve [apply IH']).
    all: cbn [stack_position stack_entry_choice zipc fill_hole];
         rewrite poscat_atpos, IH'; cbn; auto.
    all: try (destruct mfix as ((?&?)&?); destruct d; cbn; rewrite nth_error_snoc; auto).
    all: try (destruct p; cbn; try rewrite nth_error_snoc; auto).
    all: try (destruct brs as ((?&[])&?); cbn; rewrite nth_error_snoc; auto).
    all: try (rewrite nth_error_snoc; auto).
Qed.

(* BET-315 eta: the base [stack_position_valid] is FALSE for a stack with a
   position-contributing frame above an [Eta_arg] — e.g. [App_l v :: Eta_arg w [] :: []]:
   [stack_position = [app_l]] but [zipc t _ = w], and [validpos w [app_l] = false]
   (reported to the lane lead). It is restated with "no [Eta_arg]" ([Eta_app] is safe),
   and a dedicated head-[Eta_arg] form is given for the virtual Args state, where the
   [Eta_arg] frame is always the head with a no-[Eta_arg] tail. *)
Lemma stack_position_valid :
  forall t π, no_Eta_arg π -> validpos (zipc t π) (stack_position π).
Proof.
  intros t π. revert t. induction π as [|a π IH]; intros u hna.
  - reflexivity.
  - cbn in hna. apply andb_prop in hna as [ha hπ].
    pose proof (fun t => IH t hπ) as IHv. clear IH.
    pose proof (fun t => stack_position_atpos t π hπ) as IHa.
    destruct a; try discriminate ha;
      try (cbn [stack_position zipc fill_hole]; solve [apply IHv]).
    all: cbn [stack_position stack_entry_choice zipc fill_hole];
         apply poscat_valid; [ apply IHv | rewrite IHa; cbn; auto ].
    all: try (destruct mfix as ((?&?)&?); destruct d; cbn; rewrite nth_error_snoc; auto).
    all: try (destruct p; cbn; try rewrite nth_error_snoc; auto).
    all: try (destruct brs as ((?&[])&?); cbn; rewrite nth_error_snoc; auto).
    all: try (rewrite nth_error_snoc; auto).
Qed.

(* BET-315 eta: the virtual Args state's stack [Eta_arg u args :: ρ] with [no_Eta_arg ρ].
   The head [Eta_arg] drops the focus and contributes no choice, so validity reduces to
   the no-[Eta_arg] lemma on ρ with the real focus [mkApps u args]. *)
Lemma stack_position_valid_Eta_arg :
  forall t u args ρ, no_Eta_arg ρ ->
    validpos (zipc t (Eta_arg u args :: ρ)) (stack_position (Eta_arg u args :: ρ)).
Proof.
  intros t u args ρ hρ.
  cbn [stack_position zipc fill_hole].
  now apply stack_position_valid.
Qed.

Definition stack_pos (t : term) (π : stack) (h : no_Eta_arg π) : pos (zipc t π) :=
  exist (stack_position π) (stack_position_valid t π h).

(* BET-315 eta: the well-formedness invariant of every checker state. A normal state's
   stack has no [Eta_arg]; the virtual-argument state's stack is [Eta_arg u args :: ρ]
   with the [Eta_arg] as HEAD and a no-[Eta_arg] tail (nothing above it). [wf_stack]
   covers both, so [stack_pos_wf] gives a valid position for every pack, including the
   virtual side, which the K4 order needs. *)
Definition wf_stack (π : stack) : bool :=
  match π with
  | Eta_arg _ _ :: ρ => no_Eta_arg ρ
  | _ => no_Eta_arg π
  end.

Lemma wf_stack_no_Eta_arg π : no_Eta_arg π -> wf_stack π.
Proof.
  intro h. destruct π as [|a ρ]; [exact h|].
  destruct a; try exact h.
  (* Eta_arg head: no_Eta_arg (Eta_arg..::ρ) is false *)
  cbn in h. discriminate h.
Qed.

Lemma stack_position_valid_wf t π :
  wf_stack π -> validpos (zipc t π) (stack_position π).
Proof.
  intro h. destruct π as [|a ρ].
  - now apply stack_position_valid.
  - destruct a; try (apply stack_position_valid; exact h).
    apply stack_position_valid_Eta_arg; exact h.
Qed.

Definition stack_pos_wf (t : term) (π : stack) (h : wf_stack π) : pos (zipc t π) :=
  exist (stack_position π) (stack_position_valid_wf t π h).

(* TODO: Move *)
Lemma map_const {X Y} (y : Y) (l : list X) :
  map (fun _ => y) l = repeat y #|l|.
Proof.
  induction l; cbn; auto.
  f_equal; auto.
Qed.

Lemma repeat_snoc {A} (a : A) n :
  repeat a (S n) = repeat a n ++ [a].
Proof.
  induction n; auto.
  cbn.
  f_equal; auto.
Qed.

Lemma rev_repeat {A} (a : A) n :
  List.rev (repeat a n) = repeat a n.
Proof.
  induction n; auto.
  rewrite repeat_snoc at 1.
  rewrite rev_app_distr; cbn.
  f_equal; auto.
Qed.

Lemma stack_position_appstack :
  forall args ρ,
    stack_position (appstack args ρ) =
    stack_position ρ ++ repeat app_l #|args|.
Proof.
  intros args ρ. induction args as [|a args IH] in ρ |- *.
  - cbn. now rewrite app_nil_r.
  - cbn [length]. rewrite repeat_snoc.
    change (appstack (a :: args) ρ) with (App_l a :: appstack args ρ).
    cbn [stack_position stack_entry_choice].
    rewrite IH. now rewrite app_assoc.
Qed.

Section Stacks.
  Context (Σ : global_env_ext).
  Context `{checker_flags}.

  Lemma fill_context_hole_inj c t t' :
    fill_context_hole c t = fill_context_hole c t' ->
    t = t'.
  Proof using Type.
    intros eq.
    destruct c as ((?&[])&?); cbn in *.
    all: apply app_inj_length_l in eq as (_&eq); noconf eq; auto.
  Qed.

  (* BET-315 eta: false for [Eta_arg] ([fill_hole _ (Eta_arg t args) = mkApps t args]
     drops the hole, so the conclusion is independent of the focus); [Eta_app] is the
     identity and so is fine. Restated with the no-[Eta_arg] side condition (plan K3(a)). *)
  Lemma zipc_inj :
    forall u v π, no_Eta_arg π -> zipc u π = zipc v π -> u = v.
  Proof using Type.
    intros u v π. revert u v.
    induction π as [|a π IHπ]; intros u v hna e; auto.
    cbn in hna. apply andb_prop in hna as [ha hπ].
    cbn in e. apply (IHπ _ _ hπ) in e.
    destruct a; cbn in ha; try discriminate ha; cbn in e; noconf e; auto.
    - destruct mfix as ((?&[])&?); cbn in *.
      all: apply app_inj_length_l in H0 as (_&H0); auto.
      all: noconf H0; auto.
    - destruct mfix as ((?&[])&?); cbn in *.
      all: apply app_inj_length_l in H0 as (_&H0); auto.
      all: noconf H0; auto.
    - destruct p; cbn in *; noconf H0; auto.
      + apply app_inj_length_l in H0 as (_&H0); auto.
        noconf H0; auto.
    - destruct brs as ((?&[])&?); cbn in *.
      + apply app_inj_length_l in H0 as (_&H0); auto; noconf H0.
        reflexivity.
    - eapply app_inj_length_l in H0 as (_&H0); auto.
      now noconf H0.
  Qed.

  Definition isStackApp (π : stack) : bool :=
    match π with
    | App_l _ :: _ => true
    | _ => false
    end.

  Lemma isStackApp_false_appstack :
    forall l π,
      isStackApp (appstack l π) = false ->
      l = [].
  Proof using Type.
    intros l π h. destruct l ; try discriminate. reflexivity.
  Qed.

  (* Before we were zipping terms and stacks.
     Now, we even add the context into the mix.
   *)
  Definition zipx (Γ : context) (t : term) (π : stack) : term :=
    it_mkLambda_or_LetIn Γ (zipc t π).

  Fixpoint context_position (Γ : context) : position :=
    match Γ with
    | [] => []
    | {| decl_name := na ; decl_body := None ; decl_type := A |} :: Γ =>
      context_position Γ ++ [ lam_tm ]
    | {| decl_name := na ; decl_body := Some b ; decl_type := A |} :: Γ =>
      context_position Γ ++ [ let_in ]
    end.

  Lemma context_position_atpos :
    forall Γ t, atpos (it_mkLambda_or_LetIn Γ t) (context_position Γ) = t.
  Proof using Type.
    intros Γ t. revert t. induction Γ as [| d Γ ih ] ; intro t.
    - reflexivity.
    - destruct d as [na [b|] A].
      + simpl. rewrite poscat_atpos. rewrite ih. reflexivity.
      + simpl. rewrite poscat_atpos. rewrite ih. reflexivity.
  Qed.

  Lemma context_position_valid :
    forall Γ t, validpos (it_mkLambda_or_LetIn Γ t) (context_position Γ).
  Proof using Type.
    intros Γ t. revert t. induction Γ as [| [na [b|] A] Γ ih ] ; intro t.
    - reflexivity.
    - simpl. eapply poscat_valid.
      + eapply ih.
      + rewrite context_position_atpos. reflexivity.
    - simpl. eapply poscat_valid.
      + eapply ih.
      + rewrite context_position_atpos. reflexivity.
  Qed.

  Lemma positionR_context_position_inv :
    forall Γ p q,
      positionR (context_position Γ ++ p) (context_position Γ ++ q) ->
      positionR p q.
  Proof using Type.
    intros Γ p q h.
    revert p q h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros p q h.
    - assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
    - cbn in h. rewrite <- 2!app_assoc in h. apply ih in h.
      cbn in h. dependent destruction h.
      assumption.
  Qed.

  Definition xposition (Γ : context) (π : stack) : position :=
    context_position Γ ++ stack_position π.

  Lemma xposition_atpos :
    forall Γ t π, no_Eta_arg π -> atpos (zipx Γ t π) (xposition Γ π) = t.
  Proof using Type.
    intros Γ t π hπ. unfold xposition.
    rewrite poscat_atpos.
    rewrite context_position_atpos.
    now apply stack_position_atpos.
  Qed.

  Lemma xposition_valid :
    forall Γ t π, no_Eta_arg π -> validpos (zipx Γ t π) (xposition Γ π).
  Proof using Type.
    intros Γ t π hπ. unfold xposition.
    eapply poscat_valid.
    - apply context_position_valid.
    - rewrite context_position_atpos.
      now apply stack_position_valid.
  Qed.

  Lemma positionR_xposition_inv :
    forall Γ ρ1 ρ2,
      positionR (xposition Γ ρ1) (xposition Γ ρ2) ->
      positionR (stack_position ρ1) (stack_position ρ2).
  Proof using Type.
    intros Γ ρ1 ρ2 h.
    eapply positionR_context_position_inv.
    eassumption.
  Qed.

  Definition xpos (Γ : context) (t : term) (π : stack) (h : no_Eta_arg π) : pos (zipx Γ t π) :=
    exist (xposition Γ π) (xposition_valid Γ t π h).

  Lemma positionR_stack_pos_xpos :
    forall Γ π1 π2,
      positionR (stack_position π1) (stack_position π2) ->
      positionR (xposition Γ π1) (xposition Γ π2).
  Proof using Type.
    intros Γ π1 π2 h.
    unfold xposition.
    eapply positionR_poscat. assumption.
  Qed.

  Definition zipp (t : term) (π : stack) : term :=
    let '(args, ρ) := decompose_stack π in
    mkApps t args.

  Lemma stack_cat_appstack :
    forall args ρ,
      appstack args [] ++ ρ = appstack args ρ.
  Proof using Type.
    intros args ρ.
    revert ρ. induction args ; intros ρ.
    - reflexivity.
    - simpl. rewrite IHargs. reflexivity.
  Qed.

  Lemma decompose_stack_twice :
    forall π args ρ,
      decompose_stack π = (args, ρ) ->
      decompose_stack ρ = ([], ρ).
  Proof using Type.
    intros π args ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite decompose_stack_appstack in e.
    case_eq (decompose_stack ρ). intros l θ eq.
    rewrite eq in e. cbn in e. inversion e. subst.
    f_equal. clear - H1.
    revert l H1.
    induction args ; intros l h.
    - assumption.
    - apply IHargs. cbn in h. inversion h. rewrite H0. assumption.
  Qed.

  Lemma zipc_stack_cat :
    forall t π ρ,
      zipc t (π ++ ρ) = zipc (zipc t π) ρ.
  Proof using Type.
    intros t π ρ. revert t ρ.
    induction π ; intros u ρ; auto.
    simpl.
    rewrite IHπ; auto.
  Qed.

  Lemma stack_position_stack_cat :
    forall π ρ,
      stack_position (ρ ++ π) =
      stack_position π ++ stack_position ρ.
  Proof using Type.
    intros π ρ. induction ρ as [|a ρ IH]; simpl.
    - now rewrite app_nil_r.
    - destruct a; simpl; rewrite IH; try (rewrite app_assoc); reflexivity.
  Qed.

  Lemma stack_context_stack_cat :
    forall π ρ,
      stack_context (ρ ++ π) = stack_context π ,,, stack_context ρ.
  Proof using Type.
    intros π ρ.
    unfold stack_context.
    rewrite !flat_map_concat_map.
    rewrite map_app, concat_app; auto.
  Qed.

  Definition zippx (t : term) (π : stack) : term :=
    let '(args, ρ) := decompose_stack π in
    it_mkLambda_or_LetIn (stack_context ρ) (mkApps t args).

  (* Alternatively, we could go for the following definition. *)
  (* Definition zippx t π := *)
  (*   it_mkLambda_or_LetIn (stack_context π) (zipp t π). *)

End Stacks.

(* Context closure *)
Definition context_clos (R : term -> term -> Type) u v :=
  ∑ u' v' π,
    R u' v' ×
    (u = zipc u' π /\ v = zipc v' π).

Definition context_env_clos (R : context -> term -> term -> Type) Γ u v :=
  ∑ u' v' π,
    R (Γ ,,, stack_context π) u' v' ×
    (u = zipc u' π /\ v = zipc v' π).

From Stdlib Require Import ssreflect.

(* Lemma fill_mfix_hole_length mfix t : #|fill_mfix_hole mfix t| = #| *)

(* Lemma closedn_fill_hole k mfix t : closedn k (fill_mfix_hole mfix t) = closedn (#|stack_entry_context se| + k) t &&
  closedn_stack_entry k se.
Proof.
  destruct se; simpl => //; try bool_congr. *)

(* BET-315 eta: false for [Eta_arg] (its [fill_hole] drops the focus [t]); [Eta_app] is
   the identity and [closedn_stack_entry] is [true] there, so it is fine. Restated with
   [is_Eta_arg se = false]. *)
Lemma closedn_fill_hole k t se : is_Eta_arg se = false ->
  closedn k (fill_hole t se) = closedn (#|stack_entry_context se| + k) t &&
  closedn_stack_entry k se.
Proof.
  intros hse.
  destruct se; cbn in hse; try discriminate hse; simpl => //; try bool_congr; try ring.
  - destruct mfix as ((mfix1&[])&mfix2); cbn; len.
    * rewrite -app_tip_assoc !forallb_app.
      replace (k + #|mfix1| + 1 + #|mfix2|) with (#|mfix1| + S #|mfix2| + k) by lia.
      rewrite !andb_assoc andb_true_r /=. ring.
    * rewrite -app_tip_assoc !forallb_app.
      replace (k + #|mfix1| + 1 + #|mfix2|) with (#|mfix1| + S #|mfix2| + k) by lia.
      rewrite !andb_assoc andb_true_r /= ?length_map. ring.
  - destruct mfix as ((mfix1&[])&mfix2); cbn; len.
    * rewrite -app_tip_assoc !forallb_app.
      replace (k + #|mfix1| + 1 + #|mfix2|) with (#|mfix1| + S #|mfix2| + k) by lia.
      rewrite !andb_assoc andb_true_r /=. ring.
    * rewrite -app_tip_assoc !forallb_app.
      replace (k + #|mfix1| + 1 + #|mfix2|) with (#|mfix1| + S #|mfix2| + k) by lia.
      rewrite !andb_assoc andb_true_r /= ?length_map. ring.
  - destruct p; cbn.
    all: try (unfold test_predicate_k; cbn; rewrite !forallb_app /=; len; ring_simplify;
              try (replace (k + #|pcontext|) with (#|pcontext| + k) by lia);
              rewrite - !andb_assoc; repeat bool_congr;
              try (apply forallb_ext; intros []; cbn;
                   unfold test_branch_k, test_branch_k_pars; cbn; len;
                   try (now rewrite -Nat.add_assoc /=))).
    all: try (unfold test_predicate_k; cbn; len;
              rewrite - !andb_assoc; repeat bool_congr).
    all: try reflexivity.
  - destruct brs as [[brs []] brs']; cbn.
    rewrite -app_tip_assoc !forallb_app; cbn.
    len; ring_simplify; rewrite - !andb_assoc; repeat bool_congr.
  - cbn. bool_congr.
  - cbn; rewrite -!andb_assoc; bool_congr.
  - cbn. rewrite !forallb_app -!andb_assoc; repeat bool_congr.
Qed.

Lemma closedn_zip k t π : no_Eta_arg π ->
  closedn k (zipc t π) = closedn_stack k π && closedn (#|stack_context π| + k) t.
Proof.
  intros hna. induction π as [|a π IH] in k, t, hna |- * => //.
  cbn in hna. move: hna => /andP [ha hπ].
  simpl.
  rewrite (IH _ _ hπ). bool_congr. len.
  rewrite closedn_fill_hole; [exact (negbTE ha)|].
  rewrite Nat.add_assoc (Nat.add_comm #|stack_context π| k). ring.
Qed.

(* ===================================================================== *)
(* BET-315 eta: the eta-aware VIEWS (plan.md rev 11 §2 I7, revisions 8-9).  *)
(* Two different counts: a LIFT count that stops at the first [Eta_arg], and *)
(* a framewise CONTEXT view that does not.                                   *)
(* ===================================================================== *)

Definition head_is_Eta_app (π : stack) : bool :=
  match π with Eta_app _ _ :: _ => true | _ => false end.

Definition drop_eta_app (π : stack) : stack :=
  match π with Eta_app _ _ :: π => π | _ => π end.

(* [eta_lift π] = the number of [Eta_app] frames in π BEFORE the first [Eta_arg]
   frame (every eta binder between the current focus and where the lift was
   introduced). Real frames are passed through; the first [Eta_arg] stops it. *)
Fixpoint eta_lift (π : stack) : nat :=
  match π with
  | [] => 0
  | Eta_app _ _ :: π => S (eta_lift π)
  | Eta_arg _ _ :: π => 0
  | _ :: π => eta_lift π
  end.

Fixpoint count_Eta_app (π : stack) : nat :=
  match π with
  | [] => 0
  | Eta_app _ _ :: π => S (count_Eta_app π)
  | _ :: π => count_Eta_app π
  end.

Lemma eta_lift_appstack args π : eta_lift (appstack args π) = eta_lift π.
Proof.
  induction args as [|a args IH]; [reflexivity|].
  change (appstack (a :: args) π) with (App_l a :: appstack args π).
  cbn [eta_lift]. exact IH.
Qed.

(* Invariant tying the two (plan K3a): the lift count never exceeds the number of
   [Eta_app] frames, with equality exactly when π has no [Eta_arg]. *)
Lemma eta_lift_le_count π : eta_lift π <= count_Eta_app π.
Proof.
  induction π as [|a π IH]; cbn; auto.
  destruct a; cbn; lia.
Qed.

Lemma eta_lift_eq_count_no_Eta_arg π :
  no_Eta_arg π -> eta_lift π = count_Eta_app π.
Proof.
  induction π as [|a π IH]; cbn; auto.
  move=> /andP [ha hπ]. specialize (IH hπ).
  destruct a; cbn in ha; try discriminate ha; cbn; rewrite ?IH; auto.
Qed.

(* [decompose_stack_eta π]: the spine is lifted by [eta_lift π], and the virtual
   [tRel 0] is appended exactly when the first non-[App_l] frame is [Eta_app]
   (plan rev 8/9, D2(a)). *)
Definition decompose_stack_eta (π : stack) : list term * stack :=
  let '(args, ρ) := decompose_stack π in
  let k := eta_lift π in
  (map (lift0 k) args ++ (if head_is_Eta_app ρ then [tRel 0] else []), drop_eta_app ρ).

(* napp invariant (gate C3): the virtual argument adds exactly one to the spine
   length precisely when the first non-[App_l] frame is [Eta_app]. *)
Lemma decompose_stack_eta_length π :
  #|(decompose_stack_eta π).1| =
  #|(decompose_stack π).1| + (if head_is_Eta_app (decompose_stack π).2 then 1 else 0).
Proof.
  unfold decompose_stack_eta.
  destruct (decompose_stack π) as [args ρ] eqn:E; cbn.
  destruct (head_is_Eta_app ρ) eqn:He; cbn; len; lia.
Qed.

Definition zipp_eta (t : term) (π : stack) : term :=
  mkApps (lift0 (eta_lift π) t) (decompose_stack_eta π).1.

(* The defining equation of the eta step (plan I7): in a state whose head non-[App_l]
   frame is [Eta_app] (with a lift-0 tail), the eta reading of the non-lambda side is
   the lifted head applied to the real spine and the virtual [tRel 0]. *)
Lemma zipp_eta_Eta_app t2 args na A ρ :
  eta_lift ρ = 0 ->
  zipp_eta t2 (appstack args (Eta_app na A :: ρ)) =
  tApp (lift0 1 (mkApps t2 args)) (tRel 0).
Proof.
  intros hρ.
  assert (Hd : decompose_stack (appstack args (Eta_app na A :: ρ)) = (args, Eta_app na A :: ρ)).
  { rewrite decompose_stack_appstack. cbn. now rewrite app_nil_r. }
  assert (Hk : eta_lift (appstack args (Eta_app na A :: ρ)) = 1).
  { rewrite eta_lift_appstack. cbn [eta_lift]. now rewrite hρ. }
  unfold zipp_eta, decompose_stack_eta.
  rewrite Hd Hk. cbn.
  rewrite mkApps_app. cbn [mkApps]. rewrite -lift_mkApps. reflexivity.
Qed.

(* Framewise eta context (plan rev 9, D3): EVERY [Eta_app] below the focus contributes
   its binder at its own position in the stack, whether or not an [Eta_arg] lies between
   — unlike [eta_lift], which must not, because in the virtual-argument state the focus
   is the literal [tRel 0] (lift 0) while the context must still carry [vass na A]. *)
Definition stack_entry_context_eta (se : stack_entry) : context :=
  match se with
  | Eta_app na A => [vass na A]
  | Eta_arg _ _ => []
  | _ => stack_entry_context se
  end.

Definition stack_context_eta : stack -> context :=
  flat_map stack_entry_context_eta.

Lemma stack_context_eta_appstack args π :
  stack_context_eta (appstack args π) = stack_context_eta π.
Proof.
  unfold appstack. induction args as [|a args IH]; cbn; auto.
Qed.

Lemma stack_context_eta_Eta_app na A π :
  stack_context_eta (Eta_app na A :: π) = vass na A :: stack_context_eta π.
Proof. reflexivity. Qed.

Lemma stack_context_eta_cat π ρ :
  stack_context_eta (ρ ++ π) = stack_context_eta π ,,, stack_context_eta ρ.
Proof.
  unfold stack_context_eta.
  rewrite !flat_map_concat_map map_app concat_app; auto.
Qed.

(* ===================================================================== *)
(* BET-315 eta: the three [PCUICSafeLemmata] no-[Eta_arg] side-condition lemmas    *)
(* (plan K3(a), gate F-2/B-2), restated here with the structural [stack_context].   *)
(* Helpers [wf_inst_case_context] / [wf_case_inst_case_context] copied verbatim from *)
(* [PCUICSafeLemmata] (both stack-free) to avoid importing the base stack type.      *)
(* ===================================================================== *)

Arguments zip /.
Implicit Types (cf : checker_flags) (Σ : global_env_ext).


Lemma wf_inst_case_context {cf Σ} {wfΣ : wf Σ} {Γ} {ci : case_info}
  {mdecl idecl} {uinst params} ctx :
  declared_inductive Σ ci mdecl idecl ->
  wf_local Σ Γ ->
  consistent_instance_ext Σ (ind_universes mdecl) uinst ->
  spine_subst Σ Γ params (List.rev params) (smash_context [] (subst_instance uinst (ind_params mdecl))) ->
  wf_local_rel Σ (Γ,,, smash_context [] (ind_params mdecl)@[uinst]) ctx@[uinst] ->
  wf_local Σ (Γ ,,, inst_case_context params uinst ctx).
Proof.
  move=> isdecl wfΓ cu sp wfr.
  rewrite /pre_case_predicate_context_gen /inst_case_context /ind_predicate_context /=.
  eapply PCUICSubstitution.substitution_wf_local.
  * eapply sp.
  * unshelve epose proof (on_minductive_wf_params_indices_inst isdecl _ cu).
  rewrite PCUICUnivSubstitutionConv.subst_instance_app_ctx in X.
  eapply All_local_env_app_inv in X as [].
  eapply All_local_env_app => //.
  eapply wf_local_smash_end.
  now eapply weaken_wf_local; tea.
Qed.

Lemma wf_case_inst_case_context {cf Σ} {wfΣ : wf Σ}
  {Γ mdecl idecl} {ci : case_info} {p} ps (args : list term) :
  declared_inductive Σ ci mdecl idecl ->
  isType Σ Γ (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ args)) ->
  wf_predicate mdecl idecl p ->
  let predctx := case_predicate_context ci mdecl idecl p in
  Σ;;; Γ ,,, predctx |- p.(preturn) : tSort ps ->
  let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
  eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
  forall i cdecl br,
    declared_constructor Σ (ci.(ci_ind), i) mdecl idecl cdecl ->
    wf_branch cdecl br ->
    eq_context_upto_names (bcontext br) (cstr_branch_context ci mdecl cdecl) ->
    wf_local Σ (Γ ,,, inst_case_context (pparams p) (puinst p) br.(bcontext)) ×
     Σ ⊢ Γ ,,, inst_case_context (pparams p) (puinst p) br.(bcontext) =
         Γ ,,, case_branch_context ci mdecl p (forget_types br.(bcontext)) cdecl.
Proof.
  intros isdecl Hc wfp bc Hp ptm wfpctx.
  intros i cdecl br declc wfbr onctx.
  destruct (wf_case_branch_type ps args isdecl Hc wfp Hp wfpctx _ _ _ declc wfbr) as []; auto.
  have wfΓ : wf_local Σ Γ by pcuic.
  eapply isType_mkApps_Ind_smash in Hc as [? []]; tea.
  2:{ now rewrite (wf_predicate_length_pars wfp). }
  have wfctx : wf_local Σ (Γ,,, inst_case_branch_context p br).
  { erewrite <- PCUICCasesContexts.inst_case_branch_context_eq; tea. apply a1. }
  split => //.
  rewrite PCUICCasesContexts.inst_case_branch_context_eq //.
  eapply ws_cumul_ctx_pb_refl. fvs.
Qed.

Section EtaWelltyped.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : wf Σ).

  (* [welltyped_context] restated with "no [Eta_arg]". [Eta_app] is transparent to
     [zipc] and contributes no structural binder, so it goes through the inductive
     hypothesis; [Eta_arg] drops the focus and is excluded. *)
  Lemma welltyped_context :
    forall Γ t, no_Eta_arg (snd t) ->
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof using hΣ.
    intros Γ [t π] hna h. simpl in *.
    destruct h as [T h].
    induction π as [|a π IHπ] in Γ, t, T, h, hna |- *.
    1: { econstructor; eauto. }
    cbn in hna. move: hna => /andP [ha hπ].
    destruct a; cbn in ha; try discriminate ha; simpl in *.
    all: apply (IHπ _ _ hπ) in h as (?&typ).
    all: try apply inversion_App in typ as (?&?&?&?&?&?); auto.
    all: try apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    all: try apply inversion_Prod in typ as (?&?&?&?&?); auto.
    all: try apply inversion_Lambda in typ as (?&?&?&?); auto.
    all: try apply inversion_LetIn in typ as (?&?&?&?); auto.
    all: try solve [econstructor; eauto].
    - apply inversion_Fix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isTypeRel_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0. destruct o as (t0 & _); cbn in t0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_CoFix in typ as (?&?&?&?&?&?&?); eauto.
      destruct mfix as ((?&[])&?); simpl in *.
      + eapply All_app in a as (_&a).
        depelim a.
        eauto using isTypeRel_welltyped.
      + eapply All_app in a0 as (_&a0).
        depelim a0. destruct o as (t0 & _); cbn in t0.
        rewrite fix_context_fix_context_alt in t0.
        rewrite map_app in t0.
        simpl in t0.
        rewrite app_context_assoc.
        econstructor; eauto.
    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      rewrite app_context_assoc.
      destruct p.
      + apply validity in scrut_ty as (_ & ? & typ & _).
        clear brs_ty.
        apply inversion_mkApps in typ as (?&_&spine); auto; simpl in *.
        clear -spine.
        rewrite -app_assoc -app_comm_cons in spine.
        revert spine; generalize (tSort x3); intros t' spine.
        induction params1 in spine, x4, t' |- *; cbn in *.
        * depelim spine.
          econstructor; eauto.
        * depelim spine; eauto.
      + cbn. exists (tSort ps).
        cbn. move: pret_ty. cbn [fill_predicate_hole preturn].
        move=> Ht.
        cbn [fill_predicate_hole preturn] in predctx.
        eapply context_conversion; tea.
        * unfold predctx in Ht.
          eapply typing_wf_local in scrut_ty.
          eapply wf_inst_case_context; tea.
          ** cbn in ind_inst.
             unshelve epose proof (ctx_inst_spine_subst _ ind_inst).
             { eapply weaken_wf_local; tea.
               eapply (on_minductive_wf_params_indices_inst x1); tas. }
              move: X. generalize (ctx_inst_sub ind_inst).
              intros l.
              rewrite subst_instance_app => X.
              unshelve epose proof (spine_subst_app_inv _ X) as [sp _].
              { rewrite (wf_predicate_length_pars wf_pred). len.
                eapply (declared_minductive_ind_npars x1). }
              now eapply spine_subst_smash in sp.
          ** cbn in conv_pctx.
             eapply All_local_env_app_inv. eapply wf_local_alpha.
             ++ instantiate (1 := (Γ,,, stack_context π,,, smash_context [] (ind_params x)@[puinst],,, (ind_predicate_context ci x x0)@[puinst])).
                eapply All2_app => //.
                { eapply alpha_eq_subst_instance. now symmetry. }
                reflexivity.
             ++ eapply wf_ind_predicate; tea.

        * rewrite /predctx.
          cbn in conv_pctx.
          rewrite /case_predicate_context /= /case_predicate_context_gen.
          rewrite /pre_case_predicate_context_gen.
          rewrite /inst_case_context.
          apply eq_context_upto_names_conv_context.
          eapply All2_app. 2:{ reflexivity. }
          apply (PCUICAlpha.inst_case_predicate_context_eq (ind:=ci) wf_pred).
          cbn. now symmetry.

    - apply inversion_Case in typ as (?&?&?&?&[]&?); auto.
      econstructor; eauto.
    - apply inversion_Case in typ as (mdecl&idecl&decli&args&[]&?); auto.
      destruct brs as ((?&?)&?).
      simpl fill_branches_hole in brs_ty.
      destruct b; cbn in *.
      set (br := {| bcontext := bcontext; bbody := t |}) in *.
      apply All2i_app_inv_r in brs_ty as (?&?&?&?&a).
      eapply All2i_length in a0.
      depelim a. clear a.
      destruct p0 as (wfl&(cc&typ&r)). clear r.
      rewrite -app_assoc.
      eexists.
      pose proof (typing_wf_local scrut_ty).
      eapply validity in scrut_ty.
      have declc : declared_constructor Σ (ci, #|x|) mdecl idecl x1.
      { split; auto. rewrite e /= nth_error_app_ge // Nat.sub_diag //. }
      have wf_branch : wf_branch x1 {| bcontext := bcontext; bbody := t |}.
      { eapply Forall2_All2 in wf_brs. eapply All2_nth_error with (n := #|x|) in wf_brs; tea.
        * rewrite e /= nth_error_app_ge // Nat.sub_diag //.
        * rewrite a0 /= nth_error_app_ge // Nat.sub_diag //. }
      destruct (wf_case_inst_case_context ps args decli scrut_ty wf_pred pret_ty conv_pctx
        _ _ _ declc wf_branch wfl).
      cbn in *.
      eapply closed_context_conversion; tea.
      now symmetry.
    - apply unlift_TypUniv in l. now econstructor.
    - now eapply isTypeRel_welltyped.
    - apply unlift_TermTyp in l. now econstructor.
    - apply lift_sorting_forget_body in l. now eapply isTypeRel_welltyped.
    - eapply inversion_Prim in typ as (?&?&[]); eauto.
      depelim p0. now eexists.
    - eapply inversion_Prim in typ as (?&?&[]); eauto.
      depelim p0. now eexists.
    - eapply inversion_Prim in typ as (?&?&[]); eauto.
      depelim p0. cbn in *.
      eapply All_app in hvalue as [_ hvalue]. depelim hvalue.
      now eexists.
  Qed.

  Lemma welltyped_zipc_zipp :
    forall Γ t π, no_Eta_arg π ->
      welltyped Σ Γ (zipc t π) ->
      welltyped Σ (Γ ,,, stack_context π) (zipp t π).
  Proof using hΣ.
    intros Γ t π hna h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    assert (hρ : no_Eta_arg ρ) by (move: hna; rewrite no_Eta_arg_appstack; auto).
    rewrite zipc_appstack in h.
    apply (welltyped_context Γ (mkApps t l, ρ) hρ) in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.

  Lemma welltyped_zipc_stack_context Γ t π ρ args :
    no_Eta_arg π ->
    decompose_stack π = (args, ρ) ->
    welltyped Σ Γ (zipc t π) ->
    welltyped Σ (Γ ,,, stack_context π) (zipc t (appstack args [])).
  Proof using hΣ.
    intros hna h h1.
    assert (hρ : no_Eta_arg ρ).
    { pose proof (decompose_stack_eq _ _ _ h) as ->.
      move: hna. rewrite no_Eta_arg_appstack; auto. }
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, h1 |- *.
    - cbn in *.
      now apply (welltyped_context Γ (t, ρ) hρ).
    - simpl. eauto.
  Qed.

End EtaWelltyped.

(* ===================================================================== *)
(* BET-315 eta, K4 TERMINATION: the position decreases each obligation needs.  *)
(*                                                                             *)
(* The measure is the base lexicographic [R_aux] (PCUICSafeConversion.v:191) on *)
(*   (side-1 term, side-1 position, side-2 term, side-2 position, state).       *)
(* Both eta frames are transparent to [zipc] ([Eta_app] by [fill_hole = id],    *)
(* [Eta_arg] because its [fill_hole] restores the real term) and are SKIPPED by *)
(* [stack_position], so every descent reduces exactly one component. The facts  *)
(* below are the [eqt] / [positionR] hypotheses that [R_positionR] (:395),      *)
(* [R_positionR2] (:467) and [R_stateR] (:512) consume.                         *)
(* ===================================================================== *)

(* --- eta frames are transparent to the measure ------------------------------ *)

(* [Eta_app] adds no structural term and no position: side i's term and position
   are literally unchanged when the eta frame is pushed after its spine. *)
Lemma zipc_Eta_app t na A π : zipc t (Eta_app na A :: π) = zipc t π.
Proof. reflexivity. Qed.

Lemma zipc_appstack_Eta_app t args na A ρ :
  zipc t (appstack args (Eta_app na A :: ρ)) = zipc t (appstack args ρ).
Proof. rewrite !zipc_appstack. reflexivity. Qed.

Lemma stack_position_appstack_Eta_app args na A ρ :
  stack_position (appstack args (Eta_app na A :: ρ)) = stack_position (appstack args ρ).
Proof. rewrite !stack_position_appstack. reflexivity. Qed.

(* [Eta_arg] drops the hole and restores the real term, so side i's [zipc] is the
   unchanged real term and its position is unchanged (the fold skips the frame). *)
Lemma zipc_Eta_arg t u args π :
  zipc t (Eta_arg u args :: π) = zipc (mkApps u args) π.
Proof. reflexivity. Qed.

Lemma zipc_Eta_arg_appstack t u args ρ :
  zipc t (Eta_arg u args :: ρ) = zipc u (appstack args ρ).
Proof. cbn [zipc fill_hole]. now rewrite zipc_appstack. Qed.

Lemma wf_stack_Eta_arg u args ρ : no_Eta_arg ρ -> wf_stack (Eta_arg u args :: ρ).
Proof. intro h. exact h. Qed.

(* --- (1)/(1') the eta branch: the lambda side descends by [Lambda_bd] -------- *)

(* The lambda side's [zipc] is UNCHANGED (the frame reassembles the lambda), so the
   [eqt] hypothesis of R_positionR / R_positionR2 is a reflexivity ... *)
Lemma zipc_Lambda_bd na A b π :
  zipc b (Lambda_bd na A :: π) = zipc (tLambda na A b) π.
Proof. reflexivity. Qed.

(* ... and its position strictly deepens, which is the [positionR] hypothesis. *)
Lemma positionR_Lambda_bd na A π :
  positionR (stack_position (Lambda_bd na A :: π)) (stack_position π).
Proof.
  cbn [stack_position stack_entry_choice].
  apply positionR_poscat_nonil. discriminate.
Qed.

(* --- (2) the virtual-argument descent of the E [_isconv_args'] --------------- *)

Lemma positionR_repeat_app_l_app_r n :
  positionR (repeat app_l n ++ [app_r]) (repeat app_l n ++ [app_l]).
Proof.
  induction n as [|n IH]; cbn.
  - constructor.
  - constructor. exact IH.
Qed.

(* The REAL side descends by [App_r] into its real argument: its position strictly
   deepens, exactly as in base (the obligation at PCUICSafeConversion.v:5060-5076). *)
Lemma positionR_App_r_appstack t2 u l π :
  positionR (stack_position (App_r t2 :: appstack l π))
            (stack_position (appstack (u :: l) π)).
Proof.
  cbn [stack_position stack_entry_choice].
  rewrite !stack_position_appstack.
  cbn [length]. rewrite repeat_snoc.
  rewrite -!app_assoc.
  apply positionR_poscat.
  apply positionR_repeat_app_l_app_r.
Qed.

(* The VIRTUAL side keeps its term and its position: pushing [Eta_arg u args] over the
   focus [tRel 0] leaves [zipc] equal to the real term it came from, and the position
   fold skips the frame. These are the "side i unchanged" hypotheses of R_positionR2. *)
Lemma virtual_side_zipc_unchanged u args ρ :
  zipc (tRel 0) (Eta_arg u args :: ρ) = zipc u (appstack args ρ).
Proof. apply zipc_Eta_arg_appstack. Qed.

Lemma virtual_side_position_unchanged u args ρ :
  stack_position (Eta_arg u args :: ρ) = stack_position ρ.
Proof. reflexivity. Qed.
