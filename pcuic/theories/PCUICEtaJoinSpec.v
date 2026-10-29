(* Distributed under the terms of the MIT license. *)

(** * A4 (join ⇒ spec): the bridges that do not mention U1'

  A4 ([I5_join_to_spec], [PCUICEtaI5]) says a canonical join implies the η
  specification. It needs the reduction steps of a join to be specification steps.
  This file holds the bridge for [red1]:

    [red1_cumulSpecE] : red1 Σ Γ M N -> Σ ;;; Γ ⊢ M ≤sE[Conv] N

  It is base [red1_cumulSpec] ([PCUICConversion]), ported to the η specification
  ([PCUICCumulativitySpecEta]) with constructor renames only ([cumul_*] →
  [cumulE_*], [convSpec] → [convSpecE]). The η specification is base's
  [cumulSpec0] plus [cumul_eta_l] and scoping premises on [cumulE_Trans]; this
  proof uses neither, so no scoping premise appears.

  Dependencies: base syntax, [red1], [PCUICCumulativitySpecEta]. No confluence
  file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICEquality PCUICReduction
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICEtaDefs.

(** Base declares this instance in [PCUICConversion.v:69]; the ported proof's
    [reflexivity] on [All2 R l l] relies on it, and this file does not (and must
    not) import [PCUICConversion]. *)
#[local] Existing Instance All2_reflexivity.

Section RedSpecE.

  Context {cf : checker_flags} (Σ : global_env_ext).

  Proposition red1_cumulSpecE (Γ : context) (M N : term) :
    red1 Σ Γ M N -> Σ ;;; Γ ⊢ M ≤sE[Conv] N.
  Proof.
  intro r. induction r using red1_ind_all; try (econstructor; eauto; reflexivity).
  - eapply cumulE_Case; try reflexivity.
    * destruct p as [p x]. cbn in *. try repeat split; cbn; try reflexivity.
      change (fun t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) with (convSpecE Σ Γ).
      induction X; econstructor; try reflexivity; try eassumption. exact (p.2).
    * apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
  - eapply cumulE_Case; try reflexivity.
    * change (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) with (convSpecE Σ).
      destruct p as [p x]. cbn in *. try repeat split; cbn; try reflexivity; eauto.
    * apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
  - eapply cumulE_Case; try reflexivity.
    * change (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) with (convSpecE Σ).
      destruct p as [p x]. cbn in *. try repeat split; cbn; try reflexivity; eauto.
    * eauto.
    * apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
  - eapply cumulE_Case; try reflexivity.
    * change (fun Γ t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) with (convSpecE Σ).
      destruct p as [p x]. cbn in *. try repeat split; cbn; try reflexivity; eauto.
    * induction X; econstructor.
      + unfold cumul_branch. destruct p0 as [ [ _ hbody ] hhd ]. rewrite hhd. split; eauto. reflexivity.
      + apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
      + split; reflexivity.
      + exact IHX.
  - eapply cumulE_Evar.
    change (fun t u => Σ ;;; Γ ⊢ t ≤sE[Conv] u) with (convSpecE Σ Γ).
    induction X; econstructor; eauto; try reflexivity.
    * exact p.2.
  - eapply cumulE_Fix. unfold cumul_mfixpoint. set (Ξ := fix_context mfix0). clearbody Ξ.
    induction X; econstructor; eauto; try reflexivity.
    * destruct p as [ [ _ hdtype ] e ].
      pose proof (erarg := snd_eq e). pose proof (edbody := snd_eq (fst_eq e)).
      pose proof (edname := fst_eq (fst_eq e)). clear e. destruct erarg, edbody, edname.
      repeat split; eauto ; try reflexivity.
    * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
    * repeat split; reflexivity.
  - eapply cumulE_Fix. unfold cumul_mfixpoint. set (Ξ := fix_context mfix0) in *. clearbody Ξ.
    induction X; econstructor; eauto; try reflexivity.
    * destruct p as [ [ _ hdtype ] e ].
      pose proof (erarg := snd_eq e). pose proof (edbody := snd_eq (fst_eq e)).
      pose proof (edname := fst_eq (fst_eq e)). clear e. destruct erarg, edbody, edname.
      repeat split; eauto ; try reflexivity.
    * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
    * repeat split; reflexivity.
  - eapply cumulE_CoFix. unfold cumul_mfixpoint. set (Ξ := fix_context mfix0) in *. clearbody Ξ.
    induction X; econstructor; eauto; try reflexivity.
    * destruct p as [ [ _ hdtype ] e ].
      pose proof (erarg := snd_eq e). pose proof (edbody := snd_eq (fst_eq e)).
      pose proof (edname := fst_eq (fst_eq e)). clear e. destruct erarg, edbody, edname.
      repeat split; eauto ; try reflexivity.
    * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
    * repeat split; reflexivity.
  - eapply cumulE_CoFix. unfold cumul_mfixpoint. set (Ξ := fix_context mfix0) in *. clearbody Ξ.
    induction X; econstructor; eauto; try reflexivity.
    * destruct p as [ [ _ hdtype ] e ].
      pose proof (erarg := snd_eq e). pose proof (edbody := snd_eq (fst_eq e)).
      pose proof (edname := fst_eq (fst_eq e)). clear e. destruct erarg, edbody, edname.
      repeat split; eauto ; try reflexivity.
    * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
    * repeat split; reflexivity.
  - eapply cumulE_Prim. constructor; eauto; try reflexivity.
    eapply OnOne2_All2; tea; intuition eauto.
    + apply X0.
    + reflexivity.
  - eapply cumulE_Prim. constructor; eauto; trea.
  - eapply cumulE_Prim; constructor; eauto; trea.
  Defined.

  (** [Conv] spec steps are [pb] spec steps (two symmetries). *)
  Proposition convSpecE_cumulSpecE (Γ : context) (pb : conv_pb) (M N : term) :
    Σ ;;; Γ ⊢ M ≤sE[Conv] N -> Σ ;;; Γ ⊢ M ≤sE[pb] N.
  Proof. intro h. apply cumulE_Sym. apply cumulE_Sym. exact h. Defined.

  (** ** [eta1] steps are spec steps

    The root contraction is [cumul_eta_l] with a reflexivity premise; every
    other case is a congruence. [eta1] is context-free, so the induction
    hypothesis holds in EVERY context, which is what the binder cases need. *)
  Proposition eta1_cumulSpecE (M N : term) :
    eta1 M N -> forall Γ, Σ ;;; Γ ⊢ M ≤sE[Conv] N.
  Proof.
    revert M N.
    apply (eta1_ind_all (fun M N => forall Γ, Σ ;;; Γ ⊢ M ≤sE[Conv] N)).
    (* One bullet per [eta1] case, in [eta1_ind_all]'s order, and NO prelude: a
       [try solve] prelude closed [eta_red] as well and shifted every bullet. *)
    - (* eta_red: [cumul_eta_l] on a reflexive premise *)
      intros na t A Γ. apply cumul_eta_l. reflexivity.
    - (* abs_eta_l *)
      intros na M M' N _ IH Γ. apply cumulE_Lambda; [reflexivity|apply IH|reflexivity].
    - (* abs_eta_r *)
      intros na M M' N _ IH Γ. apply cumulE_Lambda; [reflexivity|reflexivity|apply IH].
    - (* letin_eta_def *)
      intros na b t b' r _ IH Γ.
      apply cumulE_LetIn; [reflexivity|apply IH|reflexivity|reflexivity].
    - (* letin_eta_ty *)
      intros na b t b' r _ IH Γ.
      apply cumulE_LetIn; [reflexivity|reflexivity|apply IH|reflexivity].
    - (* letin_eta_body *)
      intros na b t b' r _ IH Γ.
      apply cumulE_LetIn; [reflexivity|reflexivity|reflexivity|apply IH].
    - (* case_eta_param *)
      intros ci p params' c brs X Γ.
      eapply cumulE_Case; try reflexivity.
      + repeat split; cbn; try reflexivity.
        induction X as [hd hd' tl [_ IH]|hd tl tl' _ IHX]; constructor;
          [exact (IH Γ)|apply All2_reflexivity; intro; reflexivity|reflexivity|exact IHX].
      + apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
    - (* case_eta_return *)
      intros ci p preturn' c brs _ IH Γ.
      eapply cumulE_Case; try reflexivity.
      + repeat split; cbn; try reflexivity; eauto.
      + apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
    - (* case_eta_discr *)
      intros ci p c c' brs _ IH Γ.
      eapply cumulE_Case.
      + repeat split; cbn; reflexivity.
      + apply IH.
      + apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
    - (* case_eta_brs *)
      intros ci p c brs brs' X Γ.
      eapply cumulE_Case; try reflexivity.
      + repeat split; cbn; try reflexivity.
      + induction X as [hd hd' tl [[_ IH] hc]|hd tl tl' _ IHX]; constructor.
        * unfold cumul_branch. rewrite hc. split; [reflexivity|apply IH].
        * apply All2_reflexivity. eapply Prod_reflexivity; intro x; reflexivity.
        * split; reflexivity.
        * exact IHX.
    - (* proj_eta *)
      intros pr c c' _ IH Γ. apply cumulE_Proj, IH.
    - (* app_eta_l *)
      intros M1 N1 M2 _ IH Γ. apply cumulE_App; [apply IH|reflexivity].
    - (* app_eta_r *)
      intros M2 N2 M1 _ IH Γ. apply cumulE_App; [reflexivity|apply IH].
    - (* prod_eta_l *)
      intros na M1 M2 N1 _ IH Γ. apply cumulE_Prod; [reflexivity|apply IH|reflexivity].
    - (* prod_eta_r *)
      intros na M2 N2 M1 _ IH Γ. apply cumulE_Prod; [reflexivity|reflexivity|apply IH].
    - (* evar_eta *)
      intros ev l l' X Γ. eapply cumulE_Evar.
      induction X as [hd hd' tl [_ IH]|hd tl tl' _ IHX]; constructor;
        [exact (IH Γ)|apply All2_reflexivity; intro; reflexivity|reflexivity|exact IHX].
    - (* fix_eta_ty *)
      intros mfix0 mfix1 idx X Γ.
      eapply cumulE_Fix. unfold cumul_mfixpoint.
      generalize (fix_context mfix0) as Ξ.
      induction X as [hd hd' tl [[_ IH] e]|hd tl tl' _ IHX]; intros Ξ; constructor.
      * injection e as en eb er. repeat split; cbn; rewrite ?en ?eb ?er; try reflexivity. apply IH.
      * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
      * repeat split; reflexivity.
      * apply IHX.
    - (* fix_eta_body *)
      intros mfix0 mfix1 idx X Γ.
      eapply cumulE_Fix. unfold cumul_mfixpoint.
      generalize (fix_context mfix0) as Ξ.
      induction X as [hd hd' tl [[_ IH] e]|hd tl tl' _ IHX]; intros Ξ; constructor.
      * injection e as en et er. repeat split; cbn; rewrite ?en ?et ?er; try reflexivity. apply IH.
      * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
      * repeat split; reflexivity.
      * apply IHX.
    - (* cofix_eta_ty *)
      intros mfix0 mfix1 idx X Γ.
      eapply cumulE_CoFix. unfold cumul_mfixpoint.
      generalize (fix_context mfix0) as Ξ.
      induction X as [hd hd' tl [[_ IH] e]|hd tl tl' _ IHX]; intros Ξ; constructor.
      * injection e as en eb er. repeat split; cbn; rewrite ?en ?eb ?er; try reflexivity. apply IH.
      * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
      * repeat split; reflexivity.
      * apply IHX.
    - (* cofix_eta_body *)
      intros mfix0 mfix1 idx X Γ.
      eapply cumulE_CoFix. unfold cumul_mfixpoint.
      generalize (fix_context mfix0) as Ξ.
      induction X as [hd hd' tl [[_ IH] e]|hd tl tl' _ IHX]; intros Ξ; constructor.
      * injection e as en et er. repeat split; cbn; rewrite ?en ?et ?er; try reflexivity. apply IH.
      * apply All2_reflexivity. repeat eapply Prod_reflexivity; intro x; reflexivity.
      * repeat split; reflexivity.
      * apply IHX.
    - (* array_eta_val *)
      intros arr value X Γ.
      eapply cumulE_Prim. constructor; cbn; try reflexivity.
      induction X as [hd hd' tl [_ IH]|hd tl tl' _ IHX]; constructor;
        [exact (IH Γ)|apply All2_reflexivity; intro; reflexivity|reflexivity|exact IHX].
    - (* array_eta_def *)
      intros arr d _ IH Γ. eapply cumulE_Prim. constructor; cbn; try reflexivity. apply IH.
    - (* array_eta_type *)
      intros arr ty _ IH Γ. eapply cumulE_Prim. constructor; cbn; try reflexivity. apply IH.
  Defined.

End RedSpecE.
