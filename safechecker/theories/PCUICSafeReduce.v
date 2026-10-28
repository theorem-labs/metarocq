(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import RelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICGeneration PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICPosition PCUICNormal
     PCUICInversion PCUICSR PCUICSN
     PCUICUtils PCUICReduction PCUICValidity PCUICSafeLemmata
     PCUICConfluence PCUICConversion
     PCUICOnFreeVars PCUICWellScopedCumulativity
     PCUICClassification PCUICArityRed PCUICPrimitiveRed PCUICPrimCanonical.

From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfReduction PCUICWfEnv.

From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Equations Transparent.
Set Equations With UIP.

(** * Reduction machine for PCUIC without fuel

  We implement the reduction machine of Rocq without relying on fuel.
  Instead we assume strong normalization of the system (for well-typed terms)
  and proceed by well-founded induction.

  Once extracted, this should roughly correspond to the OCaml implementation.

 *)

(* From Program *)
Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : metarocq_scope.

Set Default Goal Selector "!".

Local Set Keyed Unification.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma welltyped_is_closed_context {cf Σ} {wfΣ : wf Σ} {Γ t} :
  welltyped Σ Γ t -> is_closed_context Γ.
Proof.
  intros []. now eapply typing_wf_local in X; fvs.
Qed.
#[global] Hint Resolve welltyped_is_closed_context : fvs.

Lemma welltyped_is_open_term {cf Σ} {wfΣ : wf Σ} {Γ t} :
  welltyped Σ Γ t -> is_open_term Γ t.
Proof.
  intros []; fvs.
Qed.
#[global] Hint Resolve welltyped_is_open_term : fvs.

(** Filling the [Prim_app] frame: the evaluated arguments, then the argument,
    then the rest of the spine. *)
Lemma mkApps_tApp_app u args v l :
  mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l).
Proof. rewrite mkApps_app. reflexivity. Qed.

(** The position of an argument under the [Prim_app] frame is strictly to the
    right of the head's: [n] application nodes then the argument, against [m > n]
    application nodes down to the head. *)
Lemma positionR_repeat_app_r n m :
  n < m -> positionR (repeat app_l n ++ [app_r]) (repeat app_l m).
Proof.
  induction n in m |- *; intros h; destruct m as [|m]; try lia; cbn.
  - constructor.
  - constructor. apply IHn. lia.
Qed.

(** ** Primitive operations: facts the machine needs (BET-319 rows I and Q) *)

(** §4.2(b)1, gate 4 ([on_prim_op_result]): in a well-formed environment the
    readback of a registered operation's result never fails.  This is why the
    machine's readback-[None] branch is unreachable, and why [whd_rel], the
    machine's graph, has no constructor for it (change log 15(a)). *)
Lemma wf_prim_op_readback {cf} {Σ : global_env} (wfΣ : wf Σ) {c cb op ls r} :
  lookup_env Σ c = Some (ConstantDecl cb) ->
  prim_op_of Σ c = Some op ->
  prim_op_denote op ls = Some r ->
  ∑ v, readback Σ (po_shape (info op)) r = Some v.
Proof.
  intros hl hop hden.
  pose proof (prim_op_denote_shape _ _ _ hden) as hsh.
  destruct (po_shape (info op)) eqn:hshape, r as [i|b]; cbn in hsh |- *; try contradiction.
  - eexists; reflexivity.
  - destruct (lookup_on_global_env_prim wfΣ hl) as (Σ' & [_ _ hretro hpd]).
    cbn in hpd.
    specialize (hpd op (eq_trans (f_equal (fun r => Retroknowledge.prim_op_of r c) hretro) hop)).
    destruct hpd as [_ _ _ _ hres].
    rewrite hshape in hres. cbn in hres.
    destruct hres as (i0 & mdecl & idecl & hb' & _).
    unfold primitive_bool in hb'. rewrite hretro in hb'.
    rewrite hb'. eexists; reflexivity.
Qed.

(** The saturated twin of [typing_spine_prim_args]: a spine that consumes every
    argument type of a registered operation ends at its result type. *)
Lemma typing_spine_prim_args_sat {cf} {Σ : global_env_ext} {wfΣ : wf Σ}
  {Γ r tags res T} {args : list term} ty ty' :
  PCUICPrimOpType.prim_arg_types r tags res = Some ty ->
  Σ ;;; Γ ⊢ ty ≤ ty' ->
  #|args| = #|tags| ->
  PCUICArities.typing_spine Σ Γ ty' args T ->
  Σ ;;; Γ ⊢ res ≤ T.
Proof.
  induction tags as [|t tags ih] in args, ty, ty' |- *; intros hty hle hlen hsp.
  - destruct args as [|x args]; [|cbn in hlen; lia].
    cbn in hty. noconf hty. depelim hsp. etransitivity; tea.
  - cbn in hty.
    destruct (PCUICPrimOpType.prim_tag_type r t) as [a|] eqn:ht; [|discriminate hty].
    destruct (PCUICPrimOpType.prim_arg_types r tags res) as [rest|] eqn:hrest;
      [|discriminate hty].
    cbn in hty. noconf hty.
    destruct args as [|x args]; [cbn in hlen; lia|].
    depelim hsp.
    assert (hP : Σ ;;; Γ ⊢ tImpl a rest ≤ tProd na A B) by (etransitivity; tea).
    unfold tImpl in hP.
    eapply ws_cumul_pb_Prod_Prod_inv in hP as [_ hdom hcod].
    eapply substitution0_ws_cumul_pb in hcod; tea.
    unfold subst1 in hcod. rewrite simpl_subst_k in hcod; [|reflexivity].
    exact (ih args rest (B {0 := x}) eq_refl hcod ltac:(cbn in hlen; lia) hsp).
Qed.

(** A saturated application of a registered operation has the operation's
    result type, the int type constant or the registered booleans, never a
    product, so it cannot be applied further.  [reduce_stack_whnf] uses this to
    refute an over-applied rigid application, which has no weak-head form. *)
Lemma prim_app_saturated_not_prod {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ c u op args na A B} :
  prim_op_of Σ c = Some op -> #|args| = arity op ->
  Σ ;;; Γ |- mkApps (tConst c u) args : tProd na A B -> False.
Proof.
  intros hop hlen ht.
  pose proof (validity ht) as isT.
  eapply PCUICSpine.inversion_mkApps_direct in ht as (A0 & s & hc & _ & hsp); tea.
  eapply inversion_Const in hc as (decl & wfΓ & hdecl & cu & hle); tea.
  destruct (prim_op_head_type wfΓ hdecl cu hop hle) as (res & Tp & [hsh hTp hTA hres _]).
  pose proof (typing_spine_prim_args_sat Tp A0 hTp hTA hlen hsp) as hcum.
  destruct (po_shape (info op)) eqn:hshape; cbn in hsh, hres.
  - (* SInt: the result is the int type constant, a bodiless non-operation *)
    destruct hres as (kn & d & [hpc hdecl' hinv]).
    unfold PCUICPrimOpType.prim_tag_type, EnvironmentTyping.retro_type_constant in hsh.
    cbn in hpc. rewrite hpc in hsh. cbn in hsh. noconf hsh.
    destruct hinv as [_ hbody _].
    pose proof wfΣ as (_ & wfr & _).
    assert (hnop : prim_op_of Σ kn = None)
      by exact (prim_op_of_primitive_constant Σ primInt kn wfr hpc).
    destruct (ws_cumul_pb_Axiom_l_inv (args := []) hdecl' hbody hnop hcum)
      as (u' & args' & [hred _ _]).
    eapply invert_red_prod in hred as (dom' & codom' & [e _ _]).
    apply (f_equal decompose_app) in e.
    rewrite decompose_app_mkApps in e; [|reflexivity].
    cbn in e. discriminate e.
  - (* SBool: the result is the registered inductive *)
    destruct (Retroknowledge.retro_bool _) as [ind|]; cbn in hsh; noconf hsh.
    exact (invert_cumul_ind_prod (args := []) hcum).
Qed.

(** The rest of a decomposed stack starts with no application. *)
Lemma decompose_stack_snd_nil {π args ρ} :
  decompose_stack π = (args, ρ) -> decompose_stack ρ = ([], ρ).
Proof.
  intros e. apply decompose_stack_noStackApp in e.
  destruct ρ as [|s ρ]; [reflexivity|].
  destruct s; cbn in *; try discriminate; reflexivity.
Qed.

(** An operation applied beyond its arity is ill-typed: its saturated part has
    the result type, which is not a product. *)
Lemma prim_app_overapplied_ill_typed {cf} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ c u op args} :
  prim_op_of Σ c = Some op -> arity op < #|args| ->
  welltyped Σ Γ (mkApps (tConst c u) args) -> False.
Proof.
  intros hop hlt [T ht].
  rewrite <- (firstn_skipn (arity op) args), mkApps_app in ht.
  destruct (skipn (arity op) args) as [|x more] eqn:hsk.
  { apply (f_equal (@length _)) in hsk. rewrite length_skipn in hsk. cbn in hsk. lia. }
  cbn in ht.
  eapply inversion_mkApps in ht as (A & htapp & _); tea.
  eapply inversion_App in htapp as (na & A' & B' & hf & _); tea.
  eapply prim_app_saturated_not_prod; [exact hop| |exact hf].
  rewrite length_firstn. lia.
Qed.

(** The blocking argument of a well-typed rigid application is neutral. *)
Lemma prim_rigid_arg_whne {cf} {Σ : global_env_ext} {wfΣ : wf Σ} flags {Γ c u op ls a rest T} :
  prim_op_of Σ c = Some op -> #|ls| + S #|rest| = arity op ->
  whnf flags Σ Γ a -> lit_of_term a = None ->
  Σ ;;; Γ |- mkApps (tConst c u) (map term_of_lit ls ++ a :: rest) : T ->
  whne flags Σ Γ a.
Proof.
  intros hop hlen hwa hnl typ.
  assert (hle : #|map term_of_lit ls ++ a :: rest| <= arity op)
    by (rewrite length_app, length_map; cbn; lia).
  destruct (prim_app_typing_inv hop typ hle) as [hargs _].
  destruct (nth_error (po_args (info op)) #|ls|) as [tag|] eqn:htag.
  2:{ apply nth_error_None in htag. unfold arity in hlen. lia. }
  assert (hnth : nth_error (map term_of_lit ls ++ a :: rest) #|ls| = Some a).
  { rewrite nth_error_app2; [rewrite length_map, Nat.sub_diag; reflexivity|].
    rewrite length_map; lia. }
  destruct (hargs _ _ _ hnth htag) as (kn & hkn & hta).
  pose proof (validity typ) as isT.
  eapply PCUICSpine.inversion_mkApps_direct in typ as (A0 & s0 & hc & _ & _); tea.
  eapply inversion_Const in hc as (decl0 & wfΓ0 & hdecl0 & cu0 & hle0); tea.
  destruct (prim_op_head_type wfΓ0 hdecl0 cu0 hop hle0) as (res & Tp & [_ _ _ _ hdeclared]).
  eapply All_nth_error in hdeclared; [|exact htag].
  destruct hdeclared as (kn' & d' & [hkn' hd' hinv']).
  rewrite hkn in hkn'. noconf hkn'.
  exact (whnf_prim_type_canonical flags hkn hd' hinv' (prim_op_args_int_or_string htag) hwa hta hnl).
Qed.


(* We assume normalization of the reduction.

   We state is as well-foundedness of the reduction.
*)
Section Measure.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).
  Context (Σ : global_env_ext).

  Definition R_aux Γ :=
    dlexprod (cored Σ Γ) (@posR).

  Definition R Γ u v :=
    R_aux Γ (zip u ; stack_pos (fst u) (snd u))
            (zip v ; stack_pos (fst v) (snd v)).

  Lemma cored_welltyped :
    forall {Γ u v},
      wf Σ -> welltyped Σ Γ u ->
      cored Σ Γ v u ->
      welltyped Σ Γ v.
  Proof using Type.
    intros Γ u v HΣ h r.
    revert h. induction r ; intros h.
    - destruct h as [A HA]. exists A.
      eapply subject_reduction1 ; eassumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A HA]. exists A.
      eapply subject_reduction1 ; eassumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      wf Σ -> welltyped Σ Γ u ->
      red (fst Σ) Γ u v ->
      welltyped Σ Γ v.
  Proof using Type.
    intros hΣ Γ u v h r. apply red_cored_or_eq in r.
    destruct r as [r|[]]; [|assumption].
    eapply cored_welltyped ; eauto.
  Qed.


  Derive Signature for Acc.
  Lemma R_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2),
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; p1) (t2 ; p2).
  Proof using Type.
    intros Γ t1 t2 p1 p2 e h.
    subst. right. assumption.
  Qed.

  Definition Req Γ t t' :=
    t = t' \/ R Γ t t'.

  Lemma Rtrans :
    forall Γ u v w,
      R Γ u v ->
      R Γ v w ->
      R Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2.
    eapply dlexprod_trans.
    - intros ? ? ? ? ?. eapply cored_trans' ; eassumption.
    - eapply posR_trans.
    - eassumption.
    - eassumption.
  Qed.

  Lemma Req_trans :
    forall {Γ}, Transitive (Req Γ).
  Proof using Type.
    intros Γ u v w h1 h2.
    destruct h1.
    - subst. assumption.
    - destruct h2.
      + subst. right. assumption.
      + right. eapply Rtrans ; eassumption.
  Qed.

  Lemma R_to_Req :
    forall {Γ u v},
      R Γ u v ->
      Req Γ u v.
  Proof using Type.
    intros Γ u v h.
    right. assumption.
  Qed.

  Instance Req_refl : forall Γ, Reflexive (Req Γ).
  Proof using Type.
    intros Γ.
    left. reflexivity.
  Qed.

  Lemma R_Req_R :
    forall {Γ u v w},
      R Γ u v ->
      Req Γ v w ->
      R Γ u w.
  Proof using Type.
    intros Γ u v w h1 h2.
    destruct h2.
    - subst. assumption.
    - eapply Rtrans ; eassumption.
  Qed.

End Measure.

(* Added by Julien Forest on 13/11/20 in Rocq stdlib, adapted to subset case by M. Sozeau *)
Section Acc_sidecond_generator.
  Context {A : Type} {R : A -> A -> Prop} {P : A -> Prop}.
  Variable Pimpl : forall x y, P x -> R y x -> P y.
  (* *Lazily* add 2^n - 1 Acc_intro on top of wf.
     Needed for fast reductions using Function and Program Fixpoint
     and probably using Fix and Fix_F_2
   *)
  Fixpoint Acc_intro_generator n (acc : forall t, P t -> Acc R t) : forall t, P t -> Acc R t :=
    match n with
        | O => acc
        | S n => fun x Px =>
                   Acc_intro x (fun y Hy => Acc_intro_generator n (Acc_intro_generator n acc) y (Pimpl _ _ Px Hy))
    end.
End Acc_sidecond_generator.
(** We leave it opaque for now, as some simplification tactics
  might otherwise unfold the large Acc proof. Don't forget to make it transparent
  when computing. *)
Opaque Acc_intro_generator.

Section Reduce.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

(*  Local Definition gΣ := abstract_env_ext_rel Σ. *)

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Existing Instance Req_refl.

Lemma acc_dlexprod_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
  (forall x, well_founded (leB x)) ->
  forall x,
    Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
    forall y,
      Acc (leB x) y ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
Proof using Type.
intros hw. induction 1 as [x hx ih1].
intros y. induction 1 as [y hy ih2].
constructor.
intros [x' y'] h.
destruct HQ as [[p q]].
specialize (h p q).
simple inversion h.
- intro hA. inversion H0. inversion H1. subst.
  eapply ih1.
  + intros. now eapply (HP _ _ _ _ q).
  + apply hw.
- intro hB. rewrite <- H0.
  pose proof (projT2_eq H1) as p2.
  set (projT1_eq H1) as p1 in *; cbn in p1.
  destruct p1; cbn in p2; destruct p2.
  eapply ih2. assumption.
Qed.

Lemma dlexprod_Acc_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
Proof using Type.
  intros hB x y hA.
  eapply acc_dlexprod_gen ; try assumption.
  apply hB.
Qed.

Definition R_singleton Abs A
  (R : Abs -> A -> A -> Prop) (Q : Abs -> Prop) x (q : Q x)
  (HQ : forall x x' , Q x -> Q x' -> x = x') (a a' : A) :
  R x a a' <-> (forall x, Q x -> R x a a').
Proof using Type.
  split.
  - intros H x' q'.  specialize (HQ x x' q q'). subst; eauto.
  - eauto.
Defined.

Fixpoint Acc_equiv A (R R' : A -> A -> Prop)
  (Heq : forall a a', R a a' <-> R' a a') a
  (HAcc : Acc R a) : Acc R' a.
Proof using Type.
  econstructor. intros. apply Heq in H.
  destruct HAcc. eapply Acc_equiv; eauto.
Defined.

Corollary R_Acc_aux :
    forall Γ t p,
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t) ->
    (Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R_aux Σ Γ t t') (t ; p)).
  Proof using normalization_in.
    intros Γ t p h.
    eapply dlexprod_Acc_gen.
    - apply abstract_env_ext_exists.
    - intros. eapply abstract_env_cored; try apply H1; eauto.
    - intros x. unfold well_founded.
      eapply posR_Acc.
    - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
      destruct (heΣ _ wfΣ).
      eapply Acc_equiv; try
      eapply normalization_in; eauto.
      eapply R_singleton with (Q := abstract_env_ext_rel X)
          (R := fun Σ a a' => cored Σ Γ a a'); eauto.
      intros; eapply abstract_env_ext_irr; eauto.
  Defined.

  Corollary R_Acc :
    forall Γ t,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip t)) ->
      Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ t t') t.
  Proof using normalization_in.
    intros Γ t h.
    pose proof (R_Acc_aux _ _ (stack_pos (fst t) (snd t)) h) as h'.
    clear h. rename h' into h.
    dependent induction h.
    constructor. intros y hy.
    eapply H0; eauto.
  Qed.



  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition Pr (t' : term * stack) π :=
    snd (decompose_stack π) = snd (decompose_stack (snd t')).

  Notation givePr := (_) (only parsing).

  Definition Pr' (t' : term * stack) :=
    isApp (fst t') = false /\
    (RedFlags.beta flags -> isLambda (fst t') -> isStackApp (snd t') = false).

  Notation givePr' := (conj _ (fun β hl => _)) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist res prf_Σ) := reduce t π smaller in
     exist res (fun Σ wfΣ => let '((conj prf (conj h (conj h1 h2)))) := prf_Σ Σ wfΣ in conj (Req_trans _ _ _ _ _ (R_to_Req _ (smaller Σ wfΣ))) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist (t,π) (fun Σ wfΣ => conj _ (conj givePr givePr'))) (only parsing).

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

  Lemma Req_red Σ :
    forall Γ x y,
      Req Σ Γ y x ->
      ∥ red Σ Γ (zip x) (zip y) ∥.
  Proof using Type.
    intros Γ [t π] [t' π'] h; simpl.
    dependent destruction h.
    - repeat zip fold. rewrite H.
      constructor. reflexivity.
    - dependent destruction H.
      + eapply cored_red. assumption.
      + simpl in H0. inversion H0.
        constructor. reflexivity.
  Qed.


  (* Show Obligation Tactic. *)
  Ltac obTac :=
    (* program_simpl ; *)
    Program.Tactics.program_simplify ;
    Equations.CoreTactics.equations_simpl ;
    try Program.Tactics.program_solve_wf ;
    try reflexivity.

  Obligation Tactic := obTac.

  Equations discr_construct (t : term) : Prop :=
    discr_construct (tConstruct ind n ui) := False ;
    discr_construct _ := True.

  Inductive construct_view : term -> Type :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Equations construct_viewc t : construct_view t :=
    construct_viewc (tConstruct ind n ui) := view_construct ind n ui ;
    construct_viewc t := view_other t I.

  (** [readback] on the abstract environment: the booleans are read through
      [abstract_primitive_bool].  It computes the same term as [readback] on
      every environment the abstract one stands for. *)
  Definition abstract_readback (s : prim_shape) (r : prim_result) : option term :=
    match s, r with
    | SInt, RInt i => Some (tPrim (prim_int i))
    | SBool, RBool b =>
        match abstract_primitive_bool X with
        | Some ind => Some (tConstruct ind (if b then 0 else 1) [])
        | None => None
        end
    | SInt, RBool _ | SBool, RInt _ => None
    end.

  Lemma abstract_readback_correct Σ (wfΣ : abstract_env_ext_rel X Σ) s r :
    abstract_readback s r = readback Σ s r.
  Proof using Type.
    destruct s, r; cbn; try reflexivity.
    rewrite (abstract_primitive_bool_correct X Σ wfΣ). reflexivity.
  Qed.

  (* Tailored view for _reduce_stack *)
  Equations red_discr (t : term) (π : stack) : Prop :=
    red_discr (tRel _) _ := False ;
    red_discr (tLetIn _ _ _ _) _ := False ;
    red_discr (tConst _ _) _ := False ;
    red_discr (tApp _ _) _ := False ;
    red_discr (tLambda _ _ _) (App_l _ :: _) := False ;
    red_discr (tFix _ _) _ := False ;
    red_discr (tCase _ _ _ _) _ := False ;
    red_discr (tProj _ _) _ := False ;
    red_discr _ _ := True.

  Inductive red_view : term -> stack -> Type :=
  | red_view_Rel c π : red_view (tRel c) π
  | red_view_LetIn A b B c π : red_view (tLetIn A b B c) π
  | red_view_Const c u π : red_view (tConst c u) π
  | red_view_App f a π : red_view (tApp f a) π
  | red_view_Lambda na A t a args : red_view (tLambda na A t) (App_l a :: args)
  | red_view_Fix mfix idx π : red_view (tFix mfix idx) π
  | red_view_Case ci p c brs π : red_view (tCase ci p c brs) π
  | red_view_Proj p c π : red_view (tProj p c) π
  | red_view_other t π : red_discr t π -> red_view t π.

  Equations red_viewc t π : red_view t π :=
    red_viewc (tRel c) π := red_view_Rel c π ;
    red_viewc (tLetIn A b B c) π := red_view_LetIn A b B c π ;
    red_viewc (tConst c u) π := red_view_Const c u π ;
    red_viewc (tApp f a) π := red_view_App f a π ;
    red_viewc (tLambda na A t) (App_l a :: args) := red_view_Lambda na A t a args ;
    red_viewc (tFix mfix idx) π := red_view_Fix mfix idx π ;
    red_viewc (tCase ci p c brs) π := red_view_Case ci p c brs π ;
    red_viewc (tProj p c) π := red_view_Proj p c π ;
    red_viewc t π := red_view_other t π I.

  Equations discr_construct_cofix (t : term) : Prop :=
    discr_construct_cofix (tConstruct ind n ui) := False ;
    discr_construct_cofix (tCoFix mfix idx) := False ;
    discr_construct_cofix _ := True.

  Inductive construct_cofix_view : term -> Type :=
  | ccview_construct : forall ind n ui, construct_cofix_view (tConstruct ind n ui)
  | ccview_cofix : forall mfix idx, construct_cofix_view (tCoFix mfix idx)
  | ccview_other : forall t, discr_construct_cofix t -> construct_cofix_view t.

  Equations cc_viewc t : construct_cofix_view t :=
    cc_viewc (tConstruct ind n ui) := ccview_construct ind n ui ;
    cc_viewc (tCoFix mfix idx) := ccview_cofix mfix idx ;
    cc_viewc t := ccview_other t I.

  Equations discr_construct0_cofix (t : term) : Prop :=
    discr_construct0_cofix (tConstruct ind n ui) := n <> 0 ;
    discr_construct0_cofix (tCoFix mfix idx) := False ;
    discr_construct0_cofix _ := True.

  Inductive construct0_cofix_view : term -> Type :=
  | cc0view_construct : forall ind ui, construct0_cofix_view (tConstruct ind 0 ui)
  | cc0view_cofix : forall mfix idx, construct0_cofix_view (tCoFix mfix idx)
  | cc0view_other : forall t, discr_construct0_cofix t -> construct0_cofix_view t.

  Equations cc0_viewc t : construct0_cofix_view t :=
    cc0_viewc (tConstruct ind 0 ui) := cc0view_construct ind ui ;
    cc0_viewc (tCoFix mfix idx) := cc0view_cofix mfix idx ;
    cc0_viewc t := cc0view_other t _.

  Equations _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (t,π)))
            (reduce : forall t' π', (forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (t',π') (t,π)) ->
                               { t'' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' })
    : { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t,π) /\ Pr t' π /\ Pr' t' } :=

    _reduce_stack Γ t π h reduce with red_viewc t π := {

    | red_view_Rel c π with inspect (nth_error (Γ ,,, stack_context π) c) := {
      | @exist None eq := False_rect _ _ ;
      | @exist (Some d) eq with inspect d.(decl_body) := {
        | @exist None _ := give (tRel c) π ;
        | @exist (Some b) H := rec reduce (lift0 (S c) b) π
        }
      } ;

    | red_view_LetIn A b B c π with RedFlags.zeta flags := {
      | true := rec reduce (subst10 b c) π ;
      | false := give (tLetIn A b B c) π
      } ;

    | red_view_Const c u π with RedFlags.delta flags := {
      | true with inspect (abstract_env_lookup X c) := {
        | @exist (Some (ConstantDecl {| cst_body := Some body |})) eq :=
          let body' := subst_instance u body in
          rec reduce body' π ;
        | @exist (Some (InductiveDecl _)) eq := False_rect _ _ ;
        | @exist None eq := False_rect _ _ ;
        (* A bodiless constant (design §7.2).  An axiom stops the machine; a
           registered operation saturated on the stack evaluates its arguments
           left to right under the [Prim_app] frame, as [red_view_Fix] does its
           recursive argument under [Fix_app], and fires when they are all
           literals.  [whd_rel], the machine's graph, has one constructor per
           leaf below. *)
        | @exist (Some (ConstantDecl {| cst_body := None |})) eq
            with inspect (abstract_prim_op_of X c) := {
          | @exist None eqop := give (tConst c u) π ;
          | @exist (Some op) eqop with inspect (decompose_stack π) := {
            | @exist (args, ρ) eqπ with inspect (arity op <=? #|args|) := {
              | @exist false hsat := give (tConst c u) π ;
              | @exist true hsat with inspect (split_lits (firstn (arity op) args)) := {
                | @exist (inl ls) eqs with inspect (prim_op_denote op ls) := {
                  | @exist None eqd := give (tConst c u) π ;
                  | @exist (Some r) eqd
                      with inspect (abstract_readback (po_shape (info op)) r) := {
                    | @exist (Some v) eqv := rec reduce v (appstack (skipn (arity op) args) ρ) ;
                    | @exist None eqv := False_rect _ _
                    }
                  } ;
                | @exist (inr (ls, a, rest)) eqs
                    with inspect (reduce a (Prim_app c u op (map term_of_lit ls)
                                     :: appstack (rest ++ skipn (arity op) args) ρ) _) := {
                  | @exist (@exist (t, ρ') prf) eqr with inspect (decompose_stack ρ') := {
                    | @exist (l, θ) eql with inspect (lit_of_term (mkApps t l)) := {
                      | @exist (Some lit) eqlit :=
                        rec reduce (tConst c u)
                          (appstack (map term_of_lit ls ++ mkApps t l
                                       :: rest ++ skipn (arity op) args) ρ) ;
                      | @exist None eqlit :=
                        give (tConst c u)
                          (appstack (map term_of_lit ls ++ mkApps t l
                                       :: rest ++ skipn (arity op) args) ρ)
                      }
                    }
                  }
                }
              }
            }
          }
        } ;
      | _ := give (tConst c u) π
      } ;

    | red_view_App f a π := rec reduce f (App_l a :: π) ;

    | red_view_Lambda na A t a args with inspect (RedFlags.beta flags) := {
      | @exist true eq1 := rec reduce (subst10 a t) args ;
      | @exist false eq1 := give (tLambda na A t) (App_l a :: args)
      } ;

    | red_view_Fix mfix idx π with RedFlags.fix_ flags := {
      | true with inspect (unfold_fix mfix idx) := {
        | @exist (Some (narg, fn)) eq1 with inspect (decompose_stack_at π narg) := {
          | @exist (Some (args, c, ρ)) eq2 with inspect (reduce c (Fix_app mfix idx args :: ρ) _) := {
            | @exist (@exist (t, ρ') prf) eq3 with construct_viewc t := {
              | view_construct ind n ui with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  rec reduce fn (appstack args (App_l (mkApps (tConstruct ind n ui) l) :: ρ))
                } ;
              | view_other t ht with inspect (decompose_stack ρ') := {
                | @exist (l, θ) eq4 :=
                  give (tFix mfix idx) (appstack args (App_l (mkApps t l) :: ρ))
                }
              }
            } ;
          | _ := give (tFix mfix idx) π
          } ;
        | _ := give (tFix mfix idx) π
        } ;
      | false := give (tFix mfix idx) π
      } ;

    | red_view_Case ci p c brs π with RedFlags.iota flags := {
      | true with inspect (reduce c (Case_discr ci p brs :: π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc_viewc t := {
            | ccview_construct ind' c' inst' with inspect (nth_error brs c') := {
              | exist (Some br) eqbr := rec reduce (iota_red ci.(ci_npar) p args br) π ;
              | exist None bot := False_rect _ _ } ;
            | ccview_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (narg, fn)) eq' :=
                rec reduce (tCase ci p (mkApps fn args) brs) π ;
              | @exist None bot := False_rect _ _
              } ;
            | ccview_other t ht := give (tCase ci p (mkApps t args) brs) π
            }
          }
        } ;
      | false := give (tCase ci p c brs) π
      } ;

    | red_view_Proj p c π with RedFlags.iota flags := {
      | true with inspect (reduce c (Proj p :: π) _) := {
        | @exist (@exist (t,π') prf) eq with inspect (decompose_stack π') := {
          | @exist (args, ρ) prf' with cc0_viewc t := {
            | cc0view_construct ind' _
              with inspect (nth_error args (p.(proj_npars) + p.(proj_arg))) := {
              | @exist (Some arg) eqa := rec reduce arg π ;
              | @exist None eqa := False_rect _ _
              } ;
            | cc0view_cofix mfix idx with inspect (unfold_cofix mfix idx) := {
              | @exist (Some (rarg, fn)) eq' :=
                rec reduce (tProj p (mkApps fn args)) π ;
              | @exist None bot := False_rect _ _
              } ;
            | cc0view_other t ht := give (tProj p (mkApps t args)) π
            }
          }
        } ;
      | false := give (tProj p c) π
      } ;

    | red_view_other t π discr := give t π

    }.

  (* tRel *)
  Next Obligation.
    left.
    econstructor.
    eapply red1_context.
    eapply red_rel. rewrite <- eq. cbn. f_equal.
    symmetry. assumption.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ].
    pose proof (welltyped_context _ hΣ _ _ (h _ wfΣ)) as hc.
    simpl in hc.
    (* Should be a lemma! *)
    clear - eq hc hΣ.
    revert c hc eq.
    generalize (Γ ,,, stack_context π) as Δ. clear Γ π.
    intro Γ.
    induction Γ ; intros c hc eq.
    - destruct hc as [A h].
      apply inversion_Rel in h as hh ; auto.
      destruct hh as [? [? [e ?]]].
      rewrite e in eq. discriminate eq.
    - destruct c.
      + cbn in eq. discriminate.
      + cbn in eq. eapply IHΓ ; try eassumption.
        destruct hc as [A h].
        apply inversion_Rel in h as hh ; auto.
        destruct hh as [? [? [e ?]]].
        cbn in e. rewrite e in eq. discriminate.
  Qed.

  (* tLetIn *)
  Next Obligation.
    left. econstructor.
    eapply red1_context.
    econstructor.
  Qed.

  (* tConst *)
  Next Obligation.
    left. econstructor. eapply red1_context.
    econstructor.
    - unfold declared_constant, declared_constant_gen.
      rewrite (abstract_env_lookup_correct _ _ _ wfΣ). rewrite <- eq. reflexivity.
    - cbn. reflexivity.
  Qed.
  (* tConst, a registered operation (design §7.2).  Equations places these
     right after the defined-constant obligation, because the bodiless clause
     shares its [cst_body] split. *)

  (* The operation fires: one [red_prim_op] step, under the over-applied tail. *)
  Next Obligation.
    left.
    symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs. symmetry in eqd. symmetry in eqv. symmetry in eqop.
    rewrite (abstract_readback_correct Σ wfΣ) in eqv.
    rewrite (abstract_prim_op_of_correct X c Σ wfΣ) in eqop.
    cbn. rewrite !zipc_appstack.
    repeat zip fold. eapply cored_context.
    assert (e : mkApps (tConst c u) args =
                mkApps (mkApps (tConst c u) (map term_of_lit ls)) (skipn (arity op) args)).
    { rewrite <- mkApps_app. f_equal. exact (prim_args_eq_inl eqs). }
    rewrite e. left. eapply red1_mkApps_f.
    eapply red_prim_op with (decl := {| cst_type := cst_type0; cst_body := None;
                                       cst_universes := cst_universes0;
                                       cst_relevance := cst_relevance0 |});
      [exact eqop| |reflexivity|exact eqd|exact eqv].
    unfold declared_constant, declared_constant_gen.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ). rewrite <- eq. reflexivity.
  Qed.
  Next Obligation.
    symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    match goal with H : Pr _ (appstack _ _) |- _ =>
      unfold Pr in H |- *; rewrite decompose_stack_appstack in H;
      rewrite decompose_stack_appstack; cbn in H |- *; exact H end.
  Qed.
  (* The readback of a fired operation cannot fail (§4.2(b)1, gate 4). *)
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    rewrite (abstract_readback_correct Σ wfΣ) in eqv.
    rewrite (abstract_prim_op_of_correct X c Σ wfΣ) in eqop.
    pose proof (abstract_env_lookup_correct' X c wfΣ) as hl. rewrite <- eq in hl.
    destruct (wf_prim_op_readback wΣ hl (eq_sym eqop) (eq_sym eqd)) as [v hv].
    rewrite hv in eqv. discriminate eqv.
  Qed.
  (* The [Prim_app] frame: the argument under evaluation is in the same term, to
     the right of the head. *)
  Next Obligation.
    symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs.
    eapply R_positionR.
    - cbn. rewrite !zipc_appstack. f_equal.
      rewrite mkApps_tApp_app. f_equal. symmetry. exact (prim_args_eq eqs).
    - simpl. rewrite ?stack_position_cons, ?stack_position_appstack. simpl.
      rewrite <- app_assoc. eapply positionR_poscat.
      apply positionR_repeat_app_r.
      pose proof (f_equal (@length _) (prim_args_eq eqs)) as hl.
      rewrite !length_app in hl. cbn in hl. rewrite ?length_app in hl.
      rewrite ?length_app. lia.
  Qed.
  (* The argument reduced to a literal: re-enter on the head.  The step is
     strict because the argument was not a literal. *)
  Next Obligation.
    clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs.
    assert (hne : mkApps t l <> a).
    { intros e. rewrite e in eqlit. rewrite (snd (split_lits_inr eqs)) in eqlit.
      discriminate eqlit. }
    destruct (prf Σ wfΣ) as [hreq [hpr _]].
    unfold Pr in hpr. cbn in hpr.
    symmetry in eql. rewrite eql in hpr. cbn in hpr. subst θ.
    apply decompose_stack_eq in eql. subst ρ'.
    destruct hreq as [heq | hR].
    - exfalso. apply hne. injection heq as -> hs.
      destruct l as [|x l]; [reflexivity|]. cbn in hs. discriminate hs.
    - dependent destruction hR.
      + left.
        match goal with H : cored _ _ _ _ |- _ =>
          cbn in H; rewrite !zipc_appstack in H; cbn in H; rewrite ?zipc_appstack in H;
          rewrite ?mkApps_tApp_app in H; rewrite <- (prim_args_eq eqs) in H;
          cbn; rewrite !zipc_appstack; exact H end.
      + exfalso. apply hne.
        match goal with
        | Hz : {| pr1 := ?y; pr2 := _ |} = {| pr1 := ?x; pr2 := _ |} |- _ =>
          assert (hzz : x = y) by (apply (f_equal pr1) in Hz; symmetry; exact Hz)
        end.
        apply (zipc_inj _ _ (Prim_app c u op (map term_of_lit ls)
                               :: appstack (rest ++ skipn (arity op) args) ρ)).
        rewrite <- zipc_appstack. exact hzz.
  Qed.
  Next Obligation.
    try clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    match goal with H : Pr _ (appstack _ _) |- _ =>
      unfold Pr in H |- *; rewrite decompose_stack_appstack in H;
      rewrite decompose_stack_appstack; cbn in H |- *; exact H end.
  Qed.
  (* The argument's weak-head form is not a literal: the application stops. *)
  Next Obligation.
    clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    symmetry in eqs.
    destruct (prf Σ wfΣ) as [hreq [hpr _]].
    unfold Pr in hpr. cbn in hpr.
    symmetry in eql. rewrite eql in hpr. cbn in hpr. subst θ.
    apply decompose_stack_eq in eql. subst ρ'.
    assert (hsame : mkApps t l = a ->
      Req Σ Γ (tConst c u, appstack (map term_of_lit ls ++ mkApps t l
                                       :: rest ++ skipn (arity op) args) ρ)
              (tConst c u, appstack args ρ)).
    { intros e. left. rewrite e, <- (prim_args_eq eqs). reflexivity. }
    destruct hreq as [heq | hR].
    - apply hsame. injection heq as -> hs.
      destruct l as [|x l]; [reflexivity|]. cbn in hs. discriminate hs.
    - dependent destruction hR.
      + right. left.
        match goal with H : cored _ _ _ _ |- _ =>
          cbn in H; rewrite !zipc_appstack in H; cbn in H; rewrite ?zipc_appstack in H;
          rewrite ?mkApps_tApp_app in H; rewrite <- (prim_args_eq eqs) in H;
          cbn; rewrite !zipc_appstack; exact H end.
      + apply hsame.
        match goal with
        | Hz : {| pr1 := ?y; pr2 := _ |} = {| pr1 := ?x; pr2 := _ |} |- _ =>
          assert (hzz : x = y) by (apply (f_equal pr1) in Hz; symmetry; exact Hz)
        end.
        apply (zipc_inj _ _ (Prim_app c u op (map term_of_lit ls)
                               :: appstack (rest ++ skipn (arity op) args) ρ)).
        rewrite <- zipc_appstack. exact hzz.
  Qed.
  Next Obligation.
    try clear eqr. symmetry in eqπ. apply decompose_stack_eq in eqπ. subst π.
    unfold Pr. cbn. rewrite !decompose_stack_appstack. reflexivity.
  Qed.

  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    specialize (h _ wfΣ).
    eapply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_Const in h as [decl [? [d [? ?]]]] ; auto.
    unfold declared_constant, declared_constant_gen in d.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ), <- eq in d.
    discriminate.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [wΣ].
    specialize (h _ wfΣ).
    eapply welltyped_context in h ; auto. simpl in h.
    destruct h as [T h].
    apply inversion_Const in h as [decl [? [d [? ?]]]] ; auto.
    unfold declared_constant, declared_constant_gen in d.
    rewrite (abstract_env_lookup_correct _ _ _ wfΣ), <- eq in d.
    discriminate.
  Qed.

  (* tApp *)
  Next Obligation.
    right.
    simpl. unfold posR. simpl.
    rewrite stack_position_cons.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. rewrite e in h. cbn in h.
    assumption.
  Qed.

  (* tLambda *)
  Next Obligation.
    left. econstructor.
    cbn. eapply red1_context. econstructor.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    case_eq (decompose_stack args). intros l ρ e.
    cbn. unfold Pr in h. rewrite e in h. cbn in h.
    assumption.
  Qed.
  Next Obligation.
    rewrite β in eq1. discriminate.
  Qed.

  (* tFix *)
  Next Obligation.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2). subst.
    eapply R_positionR.
    - cbn. rewrite zipc_appstack. cbn. reflexivity.
    - simpl. rewrite !stack_position_appstack, !stack_position_cons. simpl.
      rewrite <- app_assoc.
      eapply positionR_poscat.
      constructor.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite H in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. subst. clear e.

    case_eq (decompose_stack ρ'). intros ll s e1.
    pose proof (decompose_stack_eq _ _ _ e1). subst.

    eapply R_Req_R.
    - instantiate (1 := (tFix mfix idx, appstack (args ++ (mkApps (tConstruct ind n ui) l) :: l') π')).
      left. cbn. rewrite 2!zipc_appstack. cbn. rewrite zipc_appstack.
      repeat zip fold. eapply cored_context.
      assert (forall args l u v, mkApps (tApp (mkApps u args) v) l = mkApps u (args ++ v :: l)) as thm.
      { clear. intro args. induction args ; intros l u v.
        - reflexivity.
        - cbn. rewrite IHargs. reflexivity.
      }
      rewrite thm.
      left. eapply red_fix.
      + eauto.
      + unfold is_constructor.
        rewrite nth_error_app2 by eauto.
        replace (#|args| - #|args|) with 0 by auto with arith.
        cbn.
        unfold isConstruct_app.
        rewrite decompose_app_mkApps by reflexivity.
        reflexivity.
    - destruct r.
      + inversion H0. subst.
        destruct ll.
        * cbn in H3. subst. cbn in eq4. inversion eq4. subst.
          reflexivity.
        * cbn in H3. discriminate H3.
      + dependent destruction H0.
        * cbn in H0. rewrite 2!zipc_appstack in H0.
          rewrite decompose_stack_appstack in eq4.
          case_eq (decompose_stack s). intros l0 s0 e2.
          rewrite e2 in eq4. cbn in eq4.
          destruct l0.
          -- rewrite app_nil_r in eq4. inversion eq4. subst. clear eq4.
             pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             symmetry in ee. subst.
             right. left.
             cbn. rewrite !zipc_appstack.
             unfold Pr in p. cbn in p.
             rewrite e1 in p. cbn in p. subst.
             cbn in H0.
             clear - H0.

             match goal with
             | |- ?A =>
               let e := fresh "e" in
               let B := type of H0 in
               assert (A = B) as e ; [| rewrite e ; assumption ]
             end.
             set (t := tConstruct ind n ui). clearbody t.
             set (f := tFix mfix idx). clearbody f.
             f_equal.
             ++ clear. revert ll π' l' t f.
                induction args ; intros ll π' l' t f.
                ** cbn. rewrite zipc_appstack. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
             ++ clear. revert π' l' c f.
                induction args ; intros π' l' c f.
                ** cbn. reflexivity.
                ** cbn. rewrite IHargs. reflexivity.
          -- pose proof (decompose_stack_eq _ _ _ e2) as ee. cbn in ee.
             subst. exfalso.
             eapply decompose_stack_not_app. eassumption.
        * cbn in H1. inversion H1.
          rewrite 2!zipc_appstack in H3.
          unfold Pr in p. cbn in p.
          rewrite e1 in p. cbn in p. subst.
          cbn in H3. rewrite zipc_appstack in H3.
          apply zipc_inj in H3.
          apply PCUICAstUtils.mkApps_inj in H3.
          inversion H3. subst.
          rewrite e1 in eq4. inversion eq4. subst.
          reflexivity.
  Qed.
  Next Obligation.
    unfold Pr. cbn.
    unfold Pr in h. cbn in h.
    rewrite decompose_stack_appstack in h. cbn in h.
    case_eq (decompose_stack ρ). intros l1 ρ1 e.
    rewrite e in h. cbn in h. subst.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2).
    subst.
    rewrite decompose_stack_appstack. cbn.
    rewrite e. cbn. reflexivity.
  Qed.
  Next Obligation.
    case_eq (decompose_stack π). intros ll π' e.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2) as e2.
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite e2 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. subst. clear e.
    symmetry in eq4. apply decompose_stack_eq in eq4 as ?. subst.

    rewrite e2.
    destruct r as [r | r].
    - inversion r. subst.
      destruct l. 2: discriminate.
      cbn in *. subst.
      left. reflexivity.
    - unfold Pr in p. cbn in p.
      rewrite eq4 in p. simpl in p. subst.
      dependent destruction r.
      + cbn in H. rewrite zipc_appstack in H.
        cbn in H. rewrite !zipc_appstack in H.
        right. left. cbn. rewrite !zipc_appstack. cbn.
        rewrite !zipc_appstack. assumption.
      + cbn in H0. inversion H0.
        rewrite !zipc_appstack in H2. cbn in H2.
        rewrite zipc_appstack in H2.
        apply zipc_inj in H2. apply PCUICAstUtils.mkApps_inj in H2.
        inversion H2. subst.
        left. reflexivity.
  Qed.
  Next Obligation.
    symmetry in eq4.
    clear eq3. specialize (prf _ wfΣ). destruct prf as [r [p p0]].
    unfold Pr in p. cbn in p.
    rewrite eq4 in p. simpl in p. subst.
    unfold Pr. cbn.
    rewrite decompose_stack_appstack. cbn.
    case_eq (decompose_stack π). intros ll π' e. cbn.
    pose proof (decompose_stack_eq _ _ _ e). subst.
    symmetry in eq2.
    pose proof (decompose_stack_at_eq _ _ _ _ _ eq2) as e2.
    pose proof (decompose_stack_at_length _ _ _ _ _ eq2).
    case_eq (decompose_stack ρ). intros l' θ' e'. cbn.
    pose proof (decompose_stack_eq _ _ _ e'). subst.
    rewrite e2 in e. rewrite decompose_stack_appstack in e.
    cbn in e. rewrite e' in e. cbn in e. inversion e. reflexivity.
  Qed.

  (* tCase *)
  Next Obligation.
    right. unfold posR. simpl.
    rewrite stack_position_cons.
    eapply positionR_poscat_nonil. discriminate.
  Qed.
  Next Obligation.
    clear eq.
    pose proof (hΣ := hΣ _ wfΣ).
    sq. specialize (prf _ wfΣ). destruct prf as [r [p0 p1]].

    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'. specialize (h _ wfΣ).
    eapply red_welltyped in r' ; tea.
    zip fold in r'.
    apply welltyped_context in r' as (?&typ); auto; cbn in *.
    apply PCUICInductiveInversion.invert_Case_Construct in typ as H; auto.
    2: now sq.
    destruct H as (?&?&nth&?); subst.
    rewrite nth in eqbr; noconf eqbr.
    constructor.
    eapply cored_red_cored; cycle 1.
    - zip fold in r; exact r.
    - constructor.
      eapply red1_context.
      eapply red_iota; eauto.
  Qed.
  Next Obligation.
    clear eq.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'.
    eapply red_welltyped in r; eauto.
    zip fold in r.
    apply welltyped_context in r as (?&typ); auto; cbn in *.
    apply PCUICInductiveInversion.invert_Case_Construct in typ as H; auto.
    2: now sq.
    destruct H as (?&?&nth&?); subst.
    rewrite nth in bot; congruence.
  Qed.
  Next Obligation.
    clear eq.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r. pose hΣ.
    sq.
    rewrite zipc_appstack in r.
    cbn in r.
    pose proof r as r'.
    eapply red_welltyped in r; eauto.
    zip fold in r.
    apply welltyped_context in r as (?&typ); auto; cbn in *.
    constructor.
    eapply cored_red_cored; cycle 1.
    - zip fold in r'; exact r'.
    - constructor.
      eapply red1_context.
      eapply red_cofix_case; eauto.
  Qed.
  Next Obligation.
    clear eq. destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    sq.
    sq.
    unfold Pr in p0. cbn in p0.
    pose proof p0 as hh.
    rewrite <- prf' in hh. cbn in hh. subst.
    apply eq_sym, decompose_stack_eq in prf'; subst.
    apply Req_red in r; cbn in r.
    sq.
    pose proof r as r'.
    eapply red_welltyped in r; eauto.
    zip fold in r.
    apply welltyped_context in r as (?&typ); auto; cbn in *.
    apply inversion_CoFix in typ as (?&?&?&?&?&?&?); auto.
    unfold unfold_cofix in bot.
    rewrite e in bot.
    congruence.
  Qed.
  Next Obligation.
    clear eq reduce h.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [p0 p1]].
    destruct r.
    - inversion H. subst.
      clear H.
      cbn in prf'. inversion prf'. subst. reflexivity.
    - unfold Pr in p0. cbn in p0.
      rewrite <- prf' in p0. cbn in p0. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* tProj *)
  Next Obligation.
    right. unfold posR. simpl.
    rewrite stack_position_cons.
    rewrite <- app_nil_r.
    eapply positionR_poscat.
    constructor.
  Qed.
  Next Obligation.
    pose proof (hΣ := hΣ _ wfΣ).
    destruct (prf Σ wfΣ)  as [r [p' p0]].
    sq.
    left.
    apply Req_red in r as hr.
    sq.
    pose proof (red_welltyped _ hΣ (h _ wfΣ) hr) as hh.
    eapply cored_red_cored ; try eassumption.
    unfold Pr in p'. simpl in p'. pose proof p' as p''.
    rewrite <- prf' in p''. simpl in p''. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst. cbn. rewrite zipc_appstack. cbn.
    do 2 zip fold. eapply cored_context.
    constructor.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh. apply welltyped_context in hh. 2: assumption.
    simpl in hh. apply Proj_Construct_ind_eq in hh. all: eauto.
    subst. constructor. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    sq.
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    symmetry in prf'. apply decompose_stack_eq in prf' as ?.
    subst.
    apply Req_red in r as hr.
    sq.
    pose proof (red_welltyped _ hΣ (h _ wfΣ) hr) as hh.
    cbn in hh. rewrite zipc_appstack in hh. cbn in hh.
    zip fold in hh.
    apply welltyped_context in hh. 2: assumption.
    simpl in hh.
    apply Proj_red_cond in hh. all: eauto.
  Qed.
  Next Obligation.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    dependent destruction r.
    - inversion H. subst.
      left. eapply cored_context.
      constructor.
      simpl in prf'. inversion prf'. subst.
      eapply red_cofix_proj with (args := []). eauto.
    - clear eq.
      dependent destruction H.
      + left.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        cbn in H. rewrite zipc_appstack in H. cbn in H.
        eapply cored_trans' ; try eassumption.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
      + left.
        cbn in H0. destruct y'. inversion H0. subst. clear H0.
        symmetry in prf'. apply decompose_stack_eq in prf' as ?. subst.
        rewrite zipc_appstack in H2. cbn in H2.
        cbn. rewrite H2.
        zip fold. eapply cored_context.
        constructor. eapply red_cofix_proj. eauto.
  Qed.
  Next Obligation.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    sq.
    unfold Pr in pr. simpl in pr.
    pose proof pr as p'.
    rewrite <- prf' in p'. simpl in p'. subst.
    assert (h' : welltyped Σ Γ (zip (tProj p (mkApps (tCoFix mfix idx) args), π))).
    { dependent destruction r.
      - inversion H. subst.
        simpl in prf'. inversion prf'. subst. now apply h.
      - clear eq. dependent destruction H.
        + apply cored_red in H. destruct H as [r].
          eapply red_welltyped ; eauto.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          cbn in r. rewrite zipc_appstack in r. cbn in r.
          assumption.
        + cbn in H0. destruct y'. inversion H0. subst. clear H0.
          symmetry in prf'. apply decompose_stack_eq in prf'. subst.
          rewrite zipc_appstack in H2. cbn in H2.
          cbn. rewrite <- H2. now apply h.
          }
    replace (zip (tProj p (mkApps (tCoFix mfix idx) args), π))
      with (zip (tCoFix mfix idx, appstack args (Proj p :: π)))
      in h'.
    - sq.
      apply welltyped_context in h' ; auto. simpl in h'.
      destruct h' as [T h'].
      apply inversion_CoFix in h' ; auto.
      destruct h' as [decl [? [e [? [? ?]]]]].
      unfold unfold_cofix in bot.
      rewrite e in bot. discriminate.
    - cbn. rewrite zipc_appstack. reflexivity.
  Qed.
  Next Obligation.
    clear eq.
    destruct (hΣ _ wfΣ) as [hΣ]. destruct (prf Σ wfΣ)  as [r [pr p0]].
    dependent destruction r.
    - inversion H. subst. cbn in prf'. inversion prf'. subst.
      cbn. reflexivity.
    - unfold Pr in pr. cbn in pr.
      rewrite <- prf' in pr. cbn in pr. subst.
      dependent destruction H.
      + cbn in H. symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H. cbn in H.
        right. econstructor. assumption.
      + cbn in H0. inversion H0. subst. clear H0.
        symmetry in prf'.
        pose proof (decompose_stack_eq _ _ _ prf'). subst.
        rewrite zipc_appstack in H2. cbn in H2.
        apply zipc_inj in H2. inversion H2. subst.
        reflexivity.
  Qed.

  (* Other *)
  Next Obligation.
    revert discr.
    apply_funelim (red_discr t π). all: auto.
  Qed.
  Next Obligation.
    revert discr hl.
    apply_funelim (red_discr t π). all: easy.
  Qed.

  Lemma welltyped_R_pres Σ (wfΣ : abstract_env_ext_rel X Σ) Γ :
    forall x y : term × stack, welltyped Σ Γ (zip x) -> R Σ Γ y x -> welltyped Σ Γ (zip y).
  Proof using Type.
    intros x y H HR.
    pose proof (heΣ := heΣ _ wfΣ).
    pose proof (hΣ := hΣ _ wfΣ).
    clear wfΣ X_type X normalization_in.
    sq.
    destruct x as [x πx], y as [y πy].
    dependent induction HR.
    - eapply cored_welltyped. all: eauto.
    - simpl in H1. revert H1; intros [= H2 _].
      now rewrite <- H2.
  Qed.

  Section reducewf.
    Context (Γ : context).

    Notation sigmaarg :=
      (sigma (fun t => sigma (fun π => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ (zipc t π)))).

    Local Instance wf_proof : WellFounded (fun x y : sigmaarg =>
        forall Σ, abstract_env_ext_rel X Σ -> R Σ Γ (pr1 x, pr1 (pr2 x)) (pr1 y, pr1 (pr2 y))).
    Proof using normalization_in.
      intros [t [π wt]].
      (* We fuel the accessibility proof to run reduction inside Rocq. *)
      unshelve eapply (Acc_intro_generator
        (R:=fun x y : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (x.(pr1), x.(pr2).(pr1)) (y.(pr1), y.(pr2).(pr1)))
        (P:=fun x : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (x.(pr1), x.(pr2).(pr1))))
        (fun x y Px Hy => _) 1000 _ {| pr1 := t; pr2 := {| pr1 := π; pr2 := wt |} |} wt).
      - cbn in *. intros. destruct y as [t' [π' wt']]. cbn. now apply wt'.
      - cbn in *. intros.
        destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
        destruct (hΣ _ wfΣ) as [hΣ]. pose proof (R_Acc Γ (t0.(pr1), t0.(pr2).(pr1)) H).
        clear -H0. destruct t0 as [t [π wt]].
        cbn in *. revert wt.
        depind H0. intros wt. constructor. intros. eapply H0.
        * cbn in H1. exact H1.
        * reflexivity.
  Defined.

  Equations reduce_stack_full (t : term) (π : stack) (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (t,π))) :
    { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t, π) /\ Pr t' π /\ Pr' t' }
    by wf (t, π) (fun (x y : term * stack) => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ x y) :=
    reduce_stack_full t π h := _reduce_stack Γ t π h (fun t' π' hr => reduce_stack_full t' π' (fun Σ wfΣ' => welltyped_R_pres Σ wfΣ' Γ _ _ (h Σ wfΣ') (hr Σ wfΣ'))).

  End reducewf.

  Definition reduce_stack Γ t π h :=
    let '(exist ts _) := reduce_stack_full Γ t π h in ts.

  Lemma reduce_stack_Req :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
     Req Σ Γ (reduce_stack Γ t π h) (t, π).
  Proof using Type.
    intros Σ wfΣ Γ t π h.
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r _]];
    eassumption.
  Qed.

  Theorem reduce_stack_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
      ∥ Σ ;;; Γ ⊢ zip (t, π) ⇝ zip (reduce_stack Γ t π h) ∥.
  Proof using Type.
    intros Σ wfΣ Γ t π h.
    assert (req := reduce_stack_Req Σ wfΣ _ _ _ h).
    eapply Req_red in req.
    destruct (hΣ _ wfΣ).
    sq. eapply into_closed_red; fvs.
  Qed.

  Lemma reduce_stack_decompose :
    forall Γ t π h,
      snd (decompose_stack (snd (reduce_stack Γ t π h))) =
      snd (decompose_stack π).
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p p']]];
    try eassumption.
    unfold Pr in p. symmetry. assumption.
  Qed.

  Lemma reduce_stack_context :
    forall Γ t π h,
      stack_context (snd (reduce_stack Γ t π h)) =
      stack_context π.
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    pose proof (reduce_stack_decompose Γ t π h) as hd.
    case_eq (decompose_stack π). intros l ρ e1.
    case_eq (decompose_stack (snd (reduce_stack Γ t π h))). intros l' ρ' e2.
    rewrite e1 in hd. rewrite e2 in hd. cbn in hd. subst.
    pose proof (decompose_stack_eq _ _ _ e1).
    pose proof (decompose_stack_eq _ _ _ e2) as eq.
    rewrite eq. subst.
    rewrite 2!stack_context_appstack. reflexivity.
  Qed.

  Definition isred (t : term * stack) :=
    isApp (fst t) = false /\
    (isLambda (fst t) -> isStackApp (snd t) = false).

  Lemma reduce_stack_isred :
    forall Γ t π h,
      RedFlags.beta flags ->
      isred (reduce_stack Γ t π h).
  Proof using Type.
    intros Γ t π h hr.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
    split.
    - assumption.
    - apply hLam. assumption.
  Qed.

  Lemma reduce_stack_noApp :
    forall Γ t π h,
      isApp (fst (reduce_stack Γ t π h)) = false.
  Proof using Type.
    intros Γ t π h.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    unfold reduce_stack.
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
  Qed.

  Lemma reduce_stack_noLamApp :
    forall Γ t π h,
      RedFlags.beta flags ->
      isLambda (fst (reduce_stack Γ t π h)) ->
      isStackApp (snd (reduce_stack Γ t π h)) = false.
  Proof using Type.
    intros Γ t π h.
    unfold reduce_stack.
    destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
    edestruct (reduce_stack_full Γ t π h) as [[t' π'] [r [p [hApp hLam]]]]; eauto.
  Qed.

  Definition reduce_term Γ t
    (h : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :=
    zip (reduce_stack Γ t [] h).

  Theorem reduce_term_sound :
    forall Γ t (h : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
      Σ, abstract_env_ext_rel X Σ ->
      ∥ Σ ;;; Γ ⊢ t ⇝ reduce_term Γ t h ∥.
  Proof using Type.
    intros Γ t h Σ wfΣ.
    unfold reduce_term.
    refine (reduce_stack_sound _ _ _ _ [] _); eauto.
  Qed.

  Lemma reduce_term_welltyped Γ t h Σ (wfΣ : abstract_env_ext_rel X Σ) :
    welltyped Σ Γ (reduce_term Γ t h).
  Proof using Type.
    destruct (reduce_term_sound Γ t h Σ wfΣ) as [r].
    destruct (hΣ Σ wfΣ) as [wΣ].
    exact (red_welltyped Σ wΣ (h Σ wfΣ) r).
  Qed.

  Scheme Acc_ind' := Induction for Acc Sort Prop.

  Lemma Fix_F_prop :
    forall A R P f (pred : forall x : A, P x -> Prop) x hx,
      (forall x aux, (forall y hy, pred y (aux y hy)) -> pred x (f x aux)) ->
      pred x (@Fix_F A R P f x hx).
  Proof using Type.
    intros A R P f pred x hx h.
    induction hx using Acc_ind'.
    cbn. eapply h. assumption.
  Qed.

  Lemma reduce_stack_prop :
    forall Γ t π h (P : term × stack -> term × stack -> Prop),
      (forall t π h aux,
          (forall t' π' hR, P (t', π') (` (aux t' π' hR))) ->
          P (t, π) (` (_reduce_stack Γ t π h aux))) ->
      P (t, π) (reduce_stack Γ t π h).
  Proof using Type.
    intros Γ t π h P hP.
    unfold reduce_stack.
    case_eq (reduce_stack_full Γ t π h).
    apply_funelim (reduce_stack_full Γ t π h); clear -hP.
    intros t π wt ih [t' ρ] ? e.
    match type of e with
    | _ = ?u =>
      change (P (t, π) (` u))
    end.
    rewrite <- e.
    apply hP. intros t'0 π' hR.
    specialize (ih _ _ hR).
    set (r := reduce_stack_full _ _ _ _) in *.
    eapply (ih _ (proj2_sig r)). clearbody r. now destruct r.
  Qed.

  Lemma decompose_stack_at_appstack_None l s n :
    isStackApp s = false ->
    nth_error l n = None <->
    decompose_stack_at (appstack l s) n = None.
  Proof using Type.
    intros no_app.
    induction l in l, n |- *; cbn in *.
    - rewrite nth_error_nil.
      split; intros; try easy.
      destruct s as [|[]]; cbn in *; easy.
    - destruct n; [easy|].
      cbn in *.
      split.
      + rewrite IHl.
        now intros ->.
      + rewrite IHl.
        now destruct decompose_stack_at as [((?&?)&?)|]; intros.
  Qed.

  Lemma mkApps_tApp hd arg args :
    mkApps (tApp hd arg) args = mkApps hd (arg :: args).
  Proof using Type. reflexivity. Qed.

  Lemma tApp_mkApps hd args arg :
    tApp (mkApps hd args) arg = mkApps hd (args ++ [arg]).
  Proof using Type.
    change (tApp ?hd ?a) with (mkApps hd [a]).
    now rewrite mkApps_app.
  Qed.

  Lemma whnf_non_ctor_finite_ind_typed Σ Γ t ind u args :
    wf Σ ->
    whnf flags Σ Γ t ->
    isConstruct_app t = false ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite = false ->
    Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
    whne flags Σ Γ t.
  Proof using Type.
    intros wf wh ctor fin typ.
    destruct wh.
    - easy.
    - apply inversion_Sort in typ as (?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Prod in typ as (?&?&?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Lambda in typ as (?&?&?&?); auto.
      exfalso; eapply invert_cumul_prod_ind; eauto.
    - unfold isConstruct_app in ctor.
      now rewrite decompose_app_mkApps in ctor.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct o as [[? [-> ?]] | ->]; eauto.
    - apply typing_cofix_coind in typ; auto.
      unfold is_true in typ.
      unfold PCUICAst.PCUICEnvironment.fst_ctx in *.
      congruence.
    - eapply inversion_Prim in typ as (prim_ty & cdecl & [? hpc hdecl hinv ? w]); tea.
      pose proof wf as (_ & wfr & _).
      exfalso. eapply (invert_cumul_prim_type_ind hdecl hinv); [|exact w].
      exact (prim_op_of_primitive_constant Σ _ _ wfr hpc).
    (* An unsaturated operation has a product type, never an inductive one. *)
    - exfalso.
      match goal with
      | hop : prim_op_of _ _ = Some _, hlt : #|?l| < arity _ |- _ =>
        destruct (prim_app_typing_inv (wfΣ := wf) hop typ (Nat.lt_le_incl _ _ hlt))
          as [_ hprod];
        destruct (hprod hlt) as (na & A & B & hle);
        exact (invert_cumul_prod_ind hle)
      end.
    (* A rigid application: its blocking argument is typed at a primitive type
       and is a weak-head normal form that is not a literal, so it is neutral
       ([whnf_prim_type_canonical]) and the application is stuck. *)
    - eapply whne_primapp_stuck; try eassumption.
      eapply (prim_rigid_arg_whne (wfΣ := wf)); eassumption.
  Qed.

  Definition isCoFix_app t :=
    match (decompose_app t).1 with
    | tCoFix _ _ => true
    | _ => false
    end.

  Lemma whnf_non_ctor_non_cofix_ind_typed Σ Γ t ind u args :
    wf Σ ->
    whnf flags Σ Γ t ->
    isConstruct_app t = false ->
    isCoFix_app t = false ->
    Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
    whne flags Σ Γ t.
  Proof using Type.
    intros wf wh ctor cof typ.
    destruct wh.
    - easy.
    - apply inversion_Sort in typ as (?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Prod in typ as (?&?&?&?&?); auto.
      exfalso; eapply invert_cumul_sort_ind; eauto.
    - apply inversion_Lambda in typ as (?&?&?&?); auto.
      exfalso; eapply invert_cumul_prod_ind; eauto.
    - unfold isConstruct_app in ctor.
      now rewrite decompose_app_mkApps in ctor.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
      unfold unfold_fix. destruct o as [[? [-> ?]] | ->]; eauto.
    - unfold isCoFix_app in cof.
      now rewrite decompose_app_mkApps in cof.
    - eapply inversion_Prim in typ as (prim_ty & cdecl & [? hpc hdecl hinv ? w]); tea.
      pose proof wf as (_ & wfr & _).
      exfalso. eapply (invert_cumul_prim_type_ind hdecl hinv); [|exact w].
      exact (prim_op_of_primitive_constant Σ _ _ wfr hpc).
    (* An unsaturated operation has a product type, never an inductive one. *)
    - exfalso.
      match goal with
      | hop : prim_op_of _ _ = Some _, hlt : #|?l| < arity _ |- _ =>
        destruct (prim_app_typing_inv (wfΣ := wf) hop typ (Nat.lt_le_incl _ _ hlt))
          as [_ hprod];
        destruct (hprod hlt) as (na & A & B & hle);
        exact (invert_cumul_prod_ind hle)
      end.
    (* A rigid application is stuck on its blocking argument. *)
    - eapply whne_primapp_stuck; try eassumption.
      eapply (prim_rigid_arg_whne (wfΣ := wf)); eassumption.
  Qed.

  Lemma whnf_fix_arg_whne mfix idx body Σ Γ t before args aftr ty :
    wf Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    Σ ;;; Γ |- mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr) : ty ->
    whne flags Σ Γ (mkApps t args).
  Proof using Type.
    intros wf uf shape wh typ.
    apply inversion_mkApps in typ as (fix_ty & typ_fix & typ_args); auto.
    apply inversion_Fix in typ_fix as (def&f&e&a&a0&i&w); auto.
    eapply All_nth_error in a; eauto.
    apply isTypeRel_isType in a.
    eapply wf_fixpoint_spine in i; eauto.
    2: { eapply PCUICSpine.typing_spine_strengthen; eauto. }
    unfold unfold_fix in uf.
    rewrite e in uf.
    rewrite nth_error_snoc in i by congruence.
    destruct i as (?&?&?&typ&fin).
    eapply whnf_non_ctor_finite_ind_typed; try eassumption.
    - unfold isConstruct_app.
      rewrite decompose_app_mkApps by (now destruct t).
      cbn.
      now destruct t.
    - destruct check_recursivity_kind eqn:cofin in |- *; [|easy].
      eapply check_recursivity_kind_inj in fin; [|exact cofin].
      congruence.
  Qed.

  Lemma whnf_case_arg_whne Σ Γ hd args ci p brs T :
    wf Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    Σ;;; Γ |- tCase ci p (mkApps hd args) brs : T ->
    whne flags Σ Γ (mkApps hd args).
  Proof using Type.
    intros wf shape wh typ.
    apply inversion_Case in typ as (?&?&isdecl&?&[]&?); auto.
    eapply whnf_non_ctor_non_cofix_ind_typed; try eassumption.
    - unfold isConstruct_app.
      now rewrite decompose_app_mkApps; destruct hd.
    - unfold isCoFix_app.
      now rewrite decompose_app_mkApps; destruct hd.
  Qed.

  Lemma whnf_proj_arg_whne Σ Γ hd args p T :
    wf Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    Σ ;;; Γ |- tProj p (mkApps hd args) : T ->
    whne flags Σ Γ (mkApps hd args).
  Proof using Type.
    intros wf shape wh typ.
    assert (typ' := typ).
    apply inversion_Proj in typ as (?&?&?&?&?&?&?&?&?); auto.
    cbn in *.
    eapply whnf_non_ctor_non_cofix_ind_typed; try eassumption.
    - unfold isConstruct_app.
      rewrite decompose_app_mkApps by (now destruct hd).
      cbn.
      destruct hd; try easy.
      destruct p as [].
      eapply PCUICInductiveInversion.invert_Proj_Construct in typ' as (?&?&?); auto.
      2: sq; eapply wf.
      congruence.
    - unfold isCoFix_app.
      now rewrite decompose_app_mkApps; destruct hd.
  Qed.

  Lemma reduce_stack_whnf :
    forall Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ),
      let '(u, ρ) := reduce_stack Γ t π h in
       ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥.
  Proof using Type.
    intros Γ t π h Σ wfΣ.
    eapply reduce_stack_prop
      with (P := fun x y =>
        let '(u, ρ) := y in
        ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥
      ).
    clear -wfΣ.
    intros t π h aux.
    apply_funelim (_reduce_stack Γ t π h aux); clear -wfΣ.
    all: simpl.
    all: intros *.
    all: repeat match goal with
      [ |- (forall (t' : term) (π' : stack)
         (hR : forall Σ,
               abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ }) -> _ ] => intros reduce
    | [ |- (forall (t' : term) (π' : stack)
        (hR : forall Σ,
          abstract_env_ext_rel X Σ -> R Σ _ _ _), _) -> _ ] => intros haux
          | [ |- _ ] => intros ?
    end.
    all: try match goal with
             | |- context[False_rect _ ?f] => destruct f
             end.
    (* The bodiless-constant leaves of the Const branch (design §7.2), found by
       their [abstract_prim_op_of] equation; every other goal is left to the
       positional bullets below. *)
    all: try solve [
      repeat match goal with H : inspect _ = _ |- _ => clear H end;
      match goal with
      (* an axiom *)
      | hop : None = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c
        |- context [ zipp _ ?π ] =>
          unfold zipp; case_eq (decompose_stack π); intros;
          constructor; constructor; eapply whne_mkApps; eapply whne_const;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop ]
      (* a recursive call: the operation fired, or an argument became a literal *)
      | hop : Some _ = abstract_prim_op_of X _,
        rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), _
        |- _ =>
          match goal with |- context [ rf ?x ?y ?z ] =>
            case_eq (rf x y z); specialize (ha x y z);
            intros [t' π'] Ha eq'; cbn; rewrite eq' in ha; cbn in ha; assumption
          end
      (* unsaturated *)
      | hsat : false = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
        hop : Some ?op = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c |- _ =>
          unfold zipp; rewrite <- hπ; cbn; constructor;
          eapply whnf_primapp_partial;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop
          | apply Nat.leb_gt; symmetry; exact hsat ]
      (* saturated on literals, the denotation fails *)
      | hd : None = prim_op_denote ?op ?ls, hs : inl ?ls = split_lits (firstn (arity ?op) ?args),
        hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
        hop : Some ?op = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c |- _ =>
          symmetry in hs; symmetry in hsat; apply Nat.leb_le in hsat;
          unfold zipp; rewrite <- hπ; cbn;
          rewrite (prim_args_eq_inl hs), mkApps_app;
          constructor; constructor; eapply whne_mkApps; eapply whne_primapp_inert;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop
          | rewrite <- (split_lits_length_inl hs), length_firstn; lia
          | rewrite prim_reduct_lits, <- hd; reflexivity ]
      (* the reduced argument is not a literal: rigid, or ill-typed if over-applied *)
      | hlit : None = lit_of_term (mkApps ?t ?l), hl' : (?l, ?θ) = decompose_stack ?ρ',
        hs : inr (?ls, ?a, ?rest) = split_lits (firstn (arity ?op) ?args),
        hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
        hop : Some ?op = abstract_prim_op_of X ?c,
        hl : Some (ConstantDecl _) = abstract_env_lookup X ?c,
        rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), _ |- _ =>
          let hw := fresh "hw" in
          match goal with
          | hr : exist (t, ρ') ?prf = rf a ?s ?z |- _ =>
            pose proof (ha a s z) as hw; rewrite <- hr in hw; cbn in hw;
            destruct (prf Σ wfΣ) as [_ [hpr _]]; clear hr
          | hr : rf a ?s ?z = exist (t, ρ') ?prf |- _ =>
            pose proof (ha a s z) as hw; rewrite hr in hw; cbn in hw;
            destruct (prf Σ wfΣ) as [_ [hpr _]]; clear hr
          end;
          unfold Pr in hpr; cbn in hpr; rewrite <- hl' in hpr; cbn in hpr; subst θ;
          symmetry in hl'; apply decompose_stack_eq in hl'; subst ρ';
          unfold zipp in hw; rewrite decompose_stack_appstack in hw; cbn in hw;
          rewrite app_nil_r, ?stack_context_appstack in hw; cbn in hw;
          rewrite ?stack_context_appstack in hw;
          symmetry in hs; symmetry in hsat; apply Nat.leb_le in hsat;
          destruct (split_lits_inr hs) as [efirst _];
          assert (hlen : #|ls| + S #|rest| = arity op)
            by (apply (f_equal (@length _)) in efirst;
                rewrite length_firstn, length_app, length_map in efirst; cbn in efirst; lia);
          pose proof (decompose_stack_snd_nil (eq_sym hπ)) as hρ;
          unfold zipp; rewrite decompose_stack_appstack, hρ; cbn;
          rewrite app_nil_r, stack_context_appstack;
          destruct (skipn (arity op) args) as [|x more] eqn:hsk;
          [ rewrite app_nil_r; destruct hw as [hw]; constructor;
            eapply whnf_primapp_rigid;
            [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; exact hl]
            | reflexivity
            | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; exact hop
            | exact hlen | exact hw | symmetry; exact hlit ]
          | exfalso;
            match goal with hwt : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ _ (zip (tConst _ _, _)) |- _ =>
              destruct (hΣ _ wfΣ) as [wΣ];
              pose proof (hwt _ wfΣ) as hwt';
              symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
              cbn in hwt'; rewrite zipc_appstack in hwt'; zip fold in hwt';
              apply welltyped_context in hwt'; [|exact wΣ]; cbn in hwt';
              eapply (prim_app_overapplied_ill_typed (wfΣ := wΣ)
                        (eq_trans (eq_sym (abstract_prim_op_of_correct X _ _ wfΣ)) (eq_sym hop)));
              [|exact hwt'];
              apply (f_equal (@length _)) in hsk; rewrite length_skipn in hsk; cbn in hsk; lia
            end ]
      end ].
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] H eq.
      rewrite eq in haux. cbn in haux.
      assumption.
    - clear Heq.
      revert discr.
      revert h reduce haux; apply_funelim (red_discr t π); clear -wfΣ.
      all: intros; try destruct discr.
      all: try solve [ constructor ; constructor ].
      all: try solve [
        unfold zipp ; case_eq (decompose_stack π) ; intros ;
        do 2 constructor ; eapply whne_mkApps ; constructor
      ].
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eauto with pcuic.
        * exfalso.
          destruct (hΣ _ wfΣ) as [hΣ].
          cbn in h. zip fold in h.
          specialize (h _ wfΣ).
          apply welltyped_context in h; auto.
          simpl in h. rewrite stack_context_appstack in h.
          destruct h as [T h].
          apply inversion_App in h as (?&?&?&?&?); auto.
          apply inversion_Sort in t0 as (?&?&?); auto.
          eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv; eauto.
      + unfold zipp.
        case_eq (decompose_stack π). intros l ρ e.
        apply decompose_stack_eq in e. subst.
        destruct l.
        * simpl. eauto with pcuic.
        * exfalso.
          destruct (hΣ _ wfΣ) as [hΣ].
          cbn in h. zip fold in h.
          specialize (h _ wfΣ). apply welltyped_context in h; auto.
          simpl in h. rewrite stack_context_appstack in h.
          destruct h as [T h].
          apply inversion_App in h as (?&?&?&?&?); auto.
          apply inversion_Prod in t0 as (?&?&?&?&?); auto.
          eapply PCUICConversion.ws_cumul_pb_Sort_Prod_inv; eauto.
        + unfold zipp.
          case_eq (decompose_stack π). intros l ρ e.
          apply decompose_stack_eq in e. subst.
          destruct l.
          * simpl. eauto with pcuic.
          * exfalso.
            destruct (hΣ _ wfΣ) as [hΣ].
            cbn in h. zip fold in h.
            specialize (h _ wfΣ).
            apply welltyped_context in h; auto.
            simpl in h. rewrite stack_context_appstack in h.
            destruct h as [T h].
            apply inversion_App in h as (?&?&?&?&?); auto.
            apply inversion_Prim in t0 as (prim_ty & cdecl & [? hpc hdecl hinv ? w]); auto.
            pose proof hΣ as (_ & wfr & _).
            eapply (PCUICConversion.invert_cumul_prim_type_prod hdecl hinv); [|exact w].
            exact (prim_op_of_primitive_constant Σ _ _ wfr hpc).
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. econstructor.
      rewrite <- eq. cbn.
      cbn in H. inversion e. reflexivity.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_letin_nozeta. assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_const_nodelta. assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π'] Ha eq. cbn.
      rewrite eq in haux. cbn in haux.
      assumption.
    - unfold zipp. destruct decompose_stack eqn:eq.
      apply decompose_stack_noStackApp in eq as ?.
      apply decompose_stack_eq in eq.
      destruct l.
      + cbn in *; subst.
        cbn in *; congruence.
      + cbn.
        constructor.
        apply whnf_mkApps.
        apply whne_app.
        now apply whne_lam_nobeta.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_mkApps.
      now apply whne_fix_nofix.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_fixapp.
      clear -e. unfold unfold_fix in e. now destruct nth_error.
    - unfold zipp.
      destruct decompose_stack eqn:eq.
      apply decompose_stack_noStackApp in eq as ?.
      apply decompose_stack_eq in eq.
      subst.
      constructor.
      apply whnf_fixapp.
      clear -e eq1 H. unfold unfold_fix in eq1. symmetry in e.
      apply <- decompose_stack_at_appstack_None in e ; eauto.
      destruct (nth_error mfix idx) ; [left | now right]. eexists; split ; now eauto.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        specialize (haux x y z) as ?;
        destruct (reduce x y z)
      end.
      destruct (a _ wfΣ) as (?&?&?&?).
      now destruct x.
    - match type of eq3 with
      | context [ reduce ?x ?y ?z ] =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq3; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -wfΣ hΣ eq4 ht eq2 eq1 h prf haux.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- eq4 in stacks.
      subst.
      symmetry in eq2.
      assert (narg = #|args|) as -> by (now apply decompose_stack_at_length in eq2).
      eapply decompose_stack_at_eq in eq2 as ->.
      symmetry in eq4.
      apply decompose_stack_eq in eq4.
      subst.
      rewrite zipc_appstack in h.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_welltyped in h; eauto.
      rewrite zipc_appstack in h.
      cbn in h.
      rewrite tApp_mkApps in h.
      unfold zipp in *.
      apply welltyped_zipc_zipp in h; auto.
      unfold zipp in *.
      rewrite decompose_stack_appstack in *.
      cbn.
      destruct (decompose_stack ρ) eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      cbn in *.
      rewrite <-mkApps_app in h.
      destruct h as (ty&typ).
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in typ;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      destruct H as (noapp&_); cbn in *.
      rewrite app_nil_r in *.
      rewrite <- app_assoc in *.
      cbn in *.
      destruct haux.
      symmetry in eq1.
      constructor.
      constructor. unfold unfold_fix in eq1.
      case_eq (nth_error mfix idx); [intros d e | intro e]; rewrite e in eq1; inversion eq1.
      eapply whne_fixapp.
      + eassumption.
      + now apply nth_error_snoc.
      + eapply whnf_fix_arg_whne; eauto.
        * unfold unfold_fix. now rewrite e.
        * now destruct t.
    - unfold zipp.
      destruct decompose_stack.
      constructor.
      apply whnf_mkApps.
      now apply whne_case_noiota.
    - match type of eq with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -hΣ wfΣ ht prf' h prf haux.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- prf' in stacks.
      subst.
      symmetry in prf'.
      apply decompose_stack_eq in prf' as ->.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_welltyped in h; eauto using sq.
      clear r.
      rewrite zipc_appstack in h.
      cbn in h.
      zip fold in h.
      apply welltyped_context in h; auto.
      cbn in *.
      destruct h as (ty&typ).
      unfold zipp in *.
      rewrite decompose_stack_appstack in haux; cbn in *.

      destruct decompose_stack eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in typ;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      rewrite app_nil_r in *.
      destruct haux.
      constructor.
      apply whnf_mkApps, whne_case.
      eapply whnf_case_arg_whne; eauto.
      destruct H as (noapp&_).
      now destruct t.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
    - unfold zipp. case_eq (decompose_stack π). intros.
      constructor. constructor. eapply whne_mkApps. eapply whne_proj_noiota. assumption.
    - match type of eq with
      | _ = reduce ?x ?y ?z =>
        specialize (haux x y z);
          destruct (reduce x y z)
      end.
      noconf eq; cbn in *.
      pose proof (hΣ _ wfΣ) as [hΣ].
      clear -hΣ wfΣ ht prf' h prf haux.
      destruct (prf _ wfΣ) as (r&stacks&?).
      unfold Pr in stacks.
      cbn in *.
      unfold snd in stacks.
      rewrite <- prf' in stacks.
      subst.
      symmetry in prf'.
      apply decompose_stack_eq in prf' as ->.
      apply Req_red in r as [r].
      cbn in *.
      eapply red_welltyped in h; eauto using sq.
      clear r.
      rewrite zipc_appstack in h.
      cbn in h.
      zip fold in h.
      apply welltyped_context in h; auto.
      cbn in *.
      destruct h as (ty&typ).
      unfold zipp in *.
      rewrite decompose_stack_appstack in haux; cbn in *.

      destruct decompose_stack eqn:decomp.
      apply decompose_stack_eq in decomp as ->.
      repeat (try rewrite stack_context_appstack;
        try rewrite stack_context_appstack in typ;
        try rewrite stack_context_appstack in haux;
        try rewrite stack_context_appstack in H;
        cbn in * ).
      rewrite app_nil_r in *.
      destruct haux.
      constructor. apply whnf_mkApps, whne_proj.
      eapply whnf_proj_arg_whne; eauto.
      destruct H as (noapp&_).
      now destruct t.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq'. cbn.
      rewrite eq' in haux. cbn in haux.
      assumption.
    - match goal with
      | |- context [ reduce ?x ?y ?z ] =>
        case_eq (reduce x y z) ;
        specialize (haux x y z)
      end.
      intros [t' π''] Ha eq''. cbn.
      rewrite eq'' in haux. cbn in haux.
      assumption.
  Qed.

  Theorem reduce_term_complete Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t h :
    ∥whnf flags Σ Γ (reduce_term Γ t h)∥.
  Proof using Type.
    pose proof (reduce_stack_whnf Γ t [] h _ wfΣ) as H.
    unfold reduce_term.
    unfold reduce_stack in *.
    destruct reduce_stack_full.
    destruct (a _ wfΣ) as (_&stack_eq&_).
    unfold Pr in stack_eq.
    cbn in stack_eq.
    destruct decompose_stack eqn:decomp.
    cbn in *.
    subst.
    apply decompose_stack_eq in decomp.
    unfold zip, zipp in *.
    destruct x; cbn in *.
    subst s.
    rewrite zipc_appstack.
    rewrite stack_context_appstack, decompose_stack_appstack in H.
    cbn in *.
    now rewrite app_nil_r in H.
  Qed.

  (** ** The machine computes [PCUICArityRed.whd_rel]

    With every flag on except possibly [zeta], the machine started on [t] and
    the stack [π] stops at the [whd_rel] form of [t] applied to the arguments
    of [π], in the context of [π]. *)

  Lemma whd_rel_fix_iota_app zeta (Σ : global_env) Γ mfix idx fn pre c post ind n ui cargs h l :
    unfold_fix mfix idx = Some (#|pre|, fn) ->
    whd_rel zeta Σ Γ c [] (tConstruct ind n ui) cargs ->
    whd_rel zeta Σ Γ fn (pre ++ mkApps (tConstruct ind n ui) cargs :: post) h l ->
    whd_rel zeta Σ Γ (tFix mfix idx) (pre ++ c :: post) h l.
  Proof using Type.
    intros hu hc hfn.
    eapply whd_fix_iota; [exact hu|apply nth_error_snoc; reflexivity|exact hc|].
    rewrite firstn_app_left by reflexivity.
    change (pre ++ c :: post) with (pre ++ [c] ++ post).
    rewrite (app_assoc pre [c] post).
    rewrite skipn_all_app_eq by (rewrite length_app; cbn; lia).
    exact hfn.
  Qed.

  Lemma whd_rel_fix_stuck_app zeta (Σ : global_env) Γ mfix idx fn pre c post t cargs :
    unfold_fix mfix idx = Some (#|pre|, fn) ->
    whd_rel zeta Σ Γ c [] t cargs -> whd_is_construct t = false ->
    whd_rel zeta Σ Γ (tFix mfix idx) (pre ++ c :: post)
      (tFix mfix idx) (pre ++ mkApps t cargs :: post).
  Proof using Type.
    intros hu hc ht.
    assert (e : pre ++ mkApps t cargs :: post =
      firstn #|pre| (pre ++ c :: post) ++ mkApps t cargs :: skipn (S #|pre|) (pre ++ c :: post)).
    { rewrite firstn_app_left by reflexivity.
      change (pre ++ c :: post) with (pre ++ [c] ++ post).
      rewrite (app_assoc pre [c] post).
      rewrite skipn_all_app_eq by (rewrite length_app; cbn; lia).
      reflexivity. }
    rewrite e.
    eapply whd_fix_stuck; [exact hu|apply nth_error_snoc; reflexivity|exact hc|exact ht].
  Qed.

  Lemma decompose_stack_App_l_fst a π :
    (decompose_stack (App_l a :: π)).1 = a :: (decompose_stack π).1.
  Proof using Type.
    cbn. now destruct (decompose_stack π).
  Qed.

  Lemma decompose_stack_appstack_App_l_fst args x ρ :
    (decompose_stack (appstack args (App_l x :: ρ))).1 = args ++ x :: (decompose_stack ρ).1.
  Proof using Type.
    rewrite decompose_stack_appstack. cbn. now destruct (decompose_stack ρ).
  Qed.

  Lemma decompose_stack_at_None_fst π n :
    decompose_stack_at π n = None -> nth_error (decompose_stack π).1 n = None.
  Proof using Type.
    intros h.
    destruct (decompose_stack π) as [l ρ] eqn:e. cbn.
    assert (hs : isStackApp ρ = false) by (eapply decompose_stack_noStackApp; exact e).
    apply decompose_stack_eq in e. subst π.
    exact (proj2 (decompose_stack_at_appstack_None l ρ n hs) h).
  Qed.

  Lemma red_discr_whd_stop_head t π :
    red_discr t π -> whd_stop_head t (decompose_stack π).1.
  Proof using Type.
    destruct t; cbn; try (intros; reflexivity); try (intros h; exact (False_rect _ h)).
    destruct π as [|[] π]; cbn; intros h; first [reflexivity|exact (False_rect _ h)].
  Qed.

  Lemma discr_construct_whd_is_construct t :
    discr_construct t -> whd_is_construct t = false.
  Proof using Type.
    destruct t; cbn; intros h; try reflexivity; exact (False_rect _ h).
  Qed.

  Lemma discr_construct_cofix_whd t :
    discr_construct_cofix t -> whd_is_construct t = false /\ whd_is_cofix t = false.
  Proof using Type.
    destruct t; cbn; intros h; try (split; reflexivity); exact (False_rect _ h).
  Qed.

  Lemma discr_construct0_cofix_whd t :
    discr_construct0_cofix t -> whd_is_construct0 t = false /\ whd_is_cofix t = false.
  Proof using Type.
    destruct t; cbn; intros h; try (split; reflexivity).
    - destruct n; [exact (False_rect _ (h eq_refl))|split; reflexivity].
    - exact (False_rect _ h).
  Qed.

  (** The term a discriminant reduces to is well typed in the position of the
      discriminant. *)
  Lemma reduce_discr_welltyped Σ (wfΣ : abstract_env_ext_rel X Σ) Γ c fr π t π' args ρ :
    isStackApp (fr :: π) = false ->
    welltyped Σ Γ (zip (c, fr :: π)) ->
    Req Σ Γ (t, π') (c, fr :: π) ->
    Pr (t, π') (fr :: π) ->
    (args, ρ) = decompose_stack π' ->
    welltyped Σ (Γ ,,, stack_context π) (fill_hole (mkApps t args) fr).
  Proof using Type.
    intros hs wt r hpr hdec.
    assert (hd0 : decompose_stack (fr :: π) = ([], fr :: π)).
    { destruct fr; cbn in hs; try discriminate; reflexivity. }
    unfold Pr in hpr. cbn [snd] in hpr.
    rewrite hd0, <- hdec in hpr. cbn [snd] in hpr. subst ρ.
    symmetry in hdec. apply decompose_stack_eq in hdec. subst π'.
    destruct (hΣ _ wfΣ) as [wΣ].
    apply Req_red in r as [r].
    pose proof (red_welltyped Σ wΣ wt r) as wt'.
    change (welltyped Σ Γ (zipc t (appstack args (fr :: π)))) in wt'.
    rewrite zipc_appstack in wt'.
    exact (welltyped_context Σ wΣ Γ (fill_hole (mkApps t args) fr, π) wt').
  Qed.

  Lemma reduce_stack_whd_rel
    (hbeta : RedFlags.beta flags) (hiota : RedFlags.iota flags)
    (hdelta : RedFlags.delta flags) (hfix : RedFlags.fix_ flags) :
    forall Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ),
      ∥ whd_rel (RedFlags.zeta flags) Σ.1 (Γ ,,, stack_context π) t
          (decompose_stack π).1 (fst (reduce_stack Γ t π h))
          (decompose_stack (snd (reduce_stack Γ t π h))).1 ∥.
  Proof using Type.
    intros Γ t π h Σ wfΣ.
    apply (reduce_stack_prop Γ t π h (fun x y =>
      ∥ whd_rel (RedFlags.zeta flags) Σ.1 (Γ ,,, stack_context (snd x)) (fst x)
          (decompose_stack (snd x)).1 (fst y) (decompose_stack (snd y)).1 ∥)).
    clear -wfΣ hbeta hiota hdelta hfix.
    intros t π h aux.
    apply_funelim (_reduce_stack Γ t π h aux); clear -wfΣ hbeta hiota hdelta hfix.
    all: intros *.
    all: repeat match goal with
      | [ |- (forall (t' : term) (π' : stack)
              (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ }) -> _ ] =>
          intros reduce
      | [ |- (forall (t' : term) (π' : stack)
              (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), _) -> _ ] =>
          intros haux
      | [ |- _ ] => intros ?
      end.
    all: try match goal with |- context [False_rect _ ?f] => destruct f end.
    all: cbn [fst snd proj1_sig] in *; try cbv zeta.
    (* The equations [inspect _ = _] of the elimination principle depend on the
       hypotheses that the branches rewrite; they are not needed. *)
    all: repeat match goal with H : inspect _ = _ |- _ => clear H end.
    (* The recursive call [rf] and its hypothesis [ha] are found by their types:
       a pattern under [all:] cannot name a local hypothesis. *)
    (* The discriminant of a fixpoint, a case or a projection: the machine's
       result on it, and for a case or a projection the typing of the term the
       discriminant reduced to. *)
    all: try match goal with
      | rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), ∥ _ ∥ |- _ =>
        match goal with
        | e : exist (?t0, ?π0) ?prf = rf ?c ?s ?z |- _ =>
          let hc := fresh "hc" in
          pose proof (ha c s z) as hc; rewrite <- e in hc;
          cbn [fst snd proj1_sig decompose_stack] in hc;
          repeat match goal with
            | e' : (_, _) = decompose_stack π0 |- _ =>
                match type of hc with context [decompose_stack π0] =>
                  rewrite <- e' in hc; cbn [fst snd] in hc end
            end;
          try match goal with
            | e' : (?args, ?ρ) = decompose_stack π0,
              hw : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ _ _ |- _ =>
                match s with
                | ?fr :: ?ρs =>
                  pose proof (reduce_discr_welltyped Σ wfΣ _ c fr ρs t0 π0 args ρ eq_refl
                    (hw Σ wfΣ) (proj1 (prf Σ wfΣ)) (proj1 (proj2 (prf Σ wfΣ))) e') as wtc
                end
            end
        end
      end.
    (* The recursive call that ends the branch. *)
    all: try match goal with
      | rf : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), { _ : _ | _ },
        ha : forall (t' : term) (π' : stack)
               (hR : forall Σ, abstract_env_ext_rel X Σ -> R Σ _ _ _), ∥ _ ∥ |- _ =>
        match goal with
        | |- context [ rf ?x ?y ?z ] =>
          let hr := fresh "hr" in let er := fresh "er" in
          let tr := fresh "tr" in let πr := fresh "πr" in
          case_eq (rf x y z); pose proof (ha x y z) as hr;
          intros [tr πr] ? er; rewrite er in hr; cbn [fst snd proj1_sig] in hr |- *
        end
      end.
    (* The equations on machine results mention the branch's hypotheses through
       the obligations they carry; the closers below rewrite those hypotheses. *)
    all: repeat match goal with
      | H : exist _ _ = _ |- _ => clear H
      | H : _ = exist _ _ |- _ => clear H
      end.
    all: repeat match goal with H : ∥ _ ∥ |- _ => destruct H as [H] end.
    all: first
      [ exfalso; congruence
      (* tRel *)
      | constructor; eapply whd_rel_unfold;
        [symmetry; eassumption|symmetry; eassumption|eassumption]
      | constructor; eapply whd_rel_assum; [symmetry; eassumption|symmetry; eassumption]
      (* tLetIn *)
      | constructor; eapply whd_zeta; [assumption|eassumption]
      | constructor; apply whd_letin_stop; assumption
      (* tConst *)
      | constructor; eapply whd_delta;
        [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
        | reflexivity | eassumption ]
      | constructor; eapply whd_axiom;
        [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
        | reflexivity
        | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption ]
      (* a registered operation (design §7.2): one closer per leaf *)
      | match goal with
        | hsat : false = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π |- _ =>
          rewrite <- hπ; cbn [fst]; constructor; eapply whd_prim_partial;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_gt; symmetry; exact hsat ]
        end
      | match goal with
        | hd : None = prim_op_denote ?op ?ls, hs : inl ?ls = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π |- _ =>
          rewrite <- hπ; cbn [fst]; constructor; eapply whd_prim_inert;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | symmetry; exact hd ]
        end
      | match goal with
        | hd : Some ?r = prim_op_denote ?op ?ls, hv : Some ?v = abstract_readback _ ?r,
          hs : inl ?ls = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
          hr : whd_rel _ _ _ ?v _ _ _ |- _ =>
          let hρ := fresh "hρ" in
          pose proof (decompose_stack_snd_nil (eq_sym hπ)) as hρ;
          assert (hctx : stack_context π = stack_context ρ)
            by (symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
                now rewrite stack_context_appstack);
          rewrite <- hπ; cbn [fst]; rewrite hctx;
          rewrite decompose_stack_appstack, hρ, stack_context_appstack in hr;
          cbn [fst] in hr; rewrite app_nil_r in hr;
          constructor; eapply whd_prim_fire;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | symmetry; exact hd
          | rewrite <- (abstract_readback_correct _ wfΣ); symmetry; exact hv
          | exact hr ]
        end
      | match goal with
        | hlit : Some _ = lit_of_term (mkApps ?t ?l),
          hs : inr (?ls, ?a, ?rest) = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
          hc : whd_rel _ _ (_ ,,, ?Δc) ?a _ ?t ?l,
          hr : whd_rel _ _ (_ ,,, ?Δr) (tConst _ _) _ _ _ |- _ =>
          let hρ := fresh "hρ" in
          pose proof (decompose_stack_snd_nil (eq_sym hπ)) as hρ;
          assert (hctx : stack_context π = stack_context ρ)
            by (symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
                now rewrite stack_context_appstack);
          replace Δc with (stack_context ρ) in hc
            by (cbn; rewrite ?stack_context_appstack; reflexivity);
          replace Δr with (stack_context ρ) in hr
            by (rewrite ?stack_context_appstack; reflexivity);
          rewrite decompose_stack_appstack, hρ in hr; cbn [fst] in hr; rewrite app_nil_r in hr;
          rewrite <- hπ; cbn [fst]; rewrite hctx;
          constructor; eapply whd_prim_arg;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | exact hc
          | symmetry; exact hlit
          | exact hr ]
        end
      | match goal with
        | hlit : None = lit_of_term (mkApps ?t ?l),
          hs : inr (?ls, ?a, ?rest) = split_lits (firstn (arity ?op) ?args),
          hsat : true = (arity ?op <=? #|?args|), hπ : (?args, ?ρ) = decompose_stack ?π,
          hc : whd_rel _ _ (_ ,,, ?Δc) ?a _ ?t ?l |- _ =>
          let hρ := fresh "hρ" in
          pose proof (decompose_stack_snd_nil (eq_sym hπ)) as hρ;
          assert (hctx : stack_context π = stack_context ρ)
            by (symmetry in hπ; apply decompose_stack_eq in hπ; subst π;
                now rewrite stack_context_appstack);
          replace Δc with (stack_context ρ) in hc
            by (cbn; rewrite ?stack_context_appstack; reflexivity);
          rewrite <- hπ; cbn [fst]; rewrite hctx;
          rewrite decompose_stack_appstack, hρ; cbn [fst]; rewrite app_nil_r;
          constructor; eapply whd_prim_stuck;
          [ etransitivity; [exact (abstract_env_lookup_correct' X _ wfΣ)|symmetry; eassumption]
          | reflexivity
          | rewrite <- (abstract_prim_op_of_correct X _ _ wfΣ); symmetry; eassumption
          | apply Nat.leb_le; symmetry; exact hsat
          | symmetry; exact hs
          | exact hc
          | symmetry; exact hlit ]
        end
      (* tApp *)
      | constructor; rewrite decompose_stack_App_l_fst in *; eapply whd_app; eassumption
      (* tLambda *)
      | constructor; rewrite decompose_stack_App_l_fst; eapply whd_beta; eassumption
      (* tFix *)
      | match goal with
        | e1 : Some (_, _) = unfold_fix _ _, e2 : Some (_, _, _) = decompose_stack_at ?π0 _ |- _ =>
            let hlen := fresh "hlen" in
            symmetry in e2;
            pose proof (decompose_stack_at_length _ _ _ _ _ e2) as hlen;
            apply decompose_stack_at_eq in e2; subst π0; subst;
            rewrite ?decompose_stack_appstack_App_l_fst, ?stack_context_appstack in *;
            constructor;
            first
              [ eapply whd_rel_fix_iota_app; [symmetry; exact e1|eassumption|eassumption]
              | eapply whd_rel_fix_stuck_app;
                [symmetry; exact e1|eassumption
                |apply discr_construct_whd_is_construct; assumption] ]
        end
      | match goal with
        | e1 : Some (_, _) = unfold_fix _ _, e2 : None = decompose_stack_at _ _ |- _ =>
            constructor; eapply whd_fix_noarg;
            [symmetry; exact e1|apply decompose_stack_at_None_fst; symmetry; exact e2]
        end
      | match goal with
        | e1 : None = unfold_fix _ _ |- _ =>
            constructor; apply whd_fix_nounfold; symmetry; exact e1
        end
      (* tCase on a constructor: the typing gives [ci_ind] and the argument count *)
      | match goal with
        | wtc : welltyped _ _ (fill_hole (mkApps (tConstruct ?ind' _ _) _) (Case_discr _ _ _)),
          eqbr : Some _ = nth_error _ _ |- _ =>
            let T := fresh "T" in let typ := fresh "typ" in
            let ei := fresh "ei" in let br' := fresh "br'" in
            let hbr := fresh "hbr" in let hlen := fresh "hlen" in
            destruct wtc as [T typ]; cbn [fill_hole] in typ;
            destruct (PCUICInductiveInversion.invert_Case_Construct _ (hΣ _ wfΣ) typ)
              as [ei [br' [hbr hlen]]];
            subst ind'; rewrite hbr in eqbr; noconf eqbr;
            constructor; eapply whd_iota; [eassumption|eassumption|eassumption|eassumption]
        end
      (* tProj on a constructor: the typing gives [proj_ind] *)
      | match goal with
        | wtc : welltyped _ _ (fill_hole (mkApps (tConstruct ?ind' _ _) _) (Proj _)) |- _ =>
            let T := fresh "T" in let typ := fresh "typ" in let ei := fresh "ei" in
            destruct wtc as [T typ]; cbn [fill_hole] in typ;
            pose proof (PCUICInductiveInversion.Proj_Construct_ind_eq _ (hΣ _ wfΣ) typ) as ei;
            subst ind';
            constructor; eapply whd_proj; [eassumption|symmetry; eassumption|eassumption]
        end
      (* cofixpoints and stuck discriminants *)
      | constructor; eapply whd_case_cofix; [eassumption|symmetry; eassumption|eassumption]
      | constructor; eapply whd_proj_cofix; [eassumption|symmetry; eassumption|eassumption]
      | match goal with
        | ht : discr_construct_cofix _ |- _ =>
            let h1 := fresh "h1" in let h2 := fresh "h2" in
            destruct (discr_construct_cofix_whd _ ht) as [h1 h2];
            constructor; eapply whd_case_stuck; eassumption
        end
      | match goal with
        | ht : discr_construct0_cofix _ |- _ =>
            let h1 := fresh "h1" in let h2 := fresh "h2" in
            destruct (discr_construct0_cofix_whd _ ht) as [h1 h2];
            constructor; eapply whd_proj_stuck; eassumption
        end
      (* every other head stops the machine *)
      | constructor; apply whd_stop; apply red_discr_whd_stop_head; assumption ].
  Qed.

  (** [reduce_term] is the [whd_rel] normal form, in applicative form. *)
  Theorem reduce_term_whd_rel
    (hbeta : RedFlags.beta flags) (hiota : RedFlags.iota flags)
    (hdelta : RedFlags.delta flags) (hfix : RedFlags.fix_ flags)
    Γ t h Σ (wfΣ : abstract_env_ext_rel X Σ) :
    exists hd l, reduce_term Γ t h = mkApps hd l /\
      ∥ whd_rel (RedFlags.zeta flags) Σ.1 Γ t [] hd l ∥.
  Proof using Type.
    unfold reduce_term.
    generalize (reduce_stack_whd_rel hbeta hiota hdelta hfix Γ t [] h Σ wfΣ)
      (reduce_stack_decompose Γ t [] h).
    destruct (reduce_stack Γ t [] h) as [u ρ]. cbn. intros w e.
    assert (eρ : ρ = appstack (decompose_stack ρ).1 []).
    { apply decompose_stack_eq. rewrite <- e. now destruct (decompose_stack ρ). }
    exists u, (decompose_stack ρ).1. split; [|exact w].
    transitivity (zipc u (appstack (decompose_stack ρ).1 [])).
    - f_equal. exact eρ.
    - exact (@zipc_appstack u (decompose_stack ρ).1 []).
  Qed.

End Reduce.

Section ReduceFns.

  Context {cf : checker_flags} {no : normalizing_flags}
          {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Definition hnf := reduce_term RedFlags.default X_type X.

  Theorem hnf_sound {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥ Σ ;;; Γ ⊢ t ⇝ hnf Γ t h ∥.
  Proof using Type.
    unfold hnf.
    destruct (reduce_term_sound RedFlags.default _ X _ _ h Σ wfΣ).
    sq. eapply into_closed_red; fvs.
  Defined.

  Theorem hnf_complete {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥whnf RedFlags.default Σ Γ (hnf Γ t h)∥.
  Proof using Type.
    apply reduce_term_complete; eauto.
  Qed.

  Equations? reduce_to_sort (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ u, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tSort u ∥) :=
    reduce_to_sort Γ t h with view_sortc t := {
      | view_sort_sort s => Checked_comp (s; _);
      | view_sort_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_sortc hnft := {
          | view_sort_sort s => Checked_comp (s; _);
          | view_sort_other hnft r => TypeError_comp (NotASort hnft) _
        }
      }.
  Proof using Type.
    * destruct (h _ wfΣ) as [? hs].
      pose proof (hΣ := hΣ _ X _ wfΣ). sq.
      eapply (wt_closed_red_refl hs).
    * pose proof (hnf_sound (h:=h)).
      now rewrite eq.
    * destruct (abstract_env_ext_exists X) as [[Σ wfΣ]]. specialize (X1 _ wfΣ).
      pose proof (hΣ := hΣ _ X _ wfΣ). sq.
      edestruct (@hnf_complete Γ t h) as [wh]; eauto.
      edestruct (@hnf_sound Γ t h) as [r']; eauto.
      eapply PCUICContextConversion.closed_red_confluence in X1 as (?&r1&r2); eauto.
      apply invert_red_sort in r2 as ->.
      eapply whnf_red_inv in r1; eauto.
      depelim r1.
      rewrite H in r.
      now cbn in r.
  Qed.

  Lemma reduce_to_sort_complete {Γ t wt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_sort Γ t wt = TypeError_comp e p ->
    (forall s, red Σ Γ t (tSort s) -> False).
  Proof using Type.
    intros _ s r.
    apply p.
    exists s.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ _ X _ wfΣ). sq.
    eapply into_closed_red in r ; fvs.
    Unshelve. eauto.
  Qed.

  Equations? reduce_to_prod (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ na a b, forall  Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tProd na a b ∥) :=
    reduce_to_prod Γ t h with view_prodc t := {
      | view_prod_prod na a b => Checked_comp (na; a; b; _);
      | view_prod_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_prodc hnft := {
          | view_prod_prod na a b => Checked_comp (na; a; b; _);
          | view_prod_other hnft _ => TypeError_comp (NotAProduct t hnft) _
        }
      }.
  Proof using Type.
    * destruct (h _ wfΣ) as [? hs].
      pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
      now eapply wt_closed_red_refl.
    * pose proof (hnf_sound (h:=h)).
      now rewrite eq.
    * destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (X3 _ wfΣ).
      sq.
      edestruct (@hnf_complete Γ t h) as [wh]; eauto.
      edestruct (@hnf_sound Γ t h) as [r']; eauto.
      destruct (hΣ _ _ _ wfΣ).
      eapply PCUICContextConversion.closed_red_confluence in X3 as (?&r1&r2); eauto.
      apply invert_red_prod in r2 as (?&?&[-> ? ?]); auto.
      eapply whnf_red_inv in r1; auto.
      depelim r1.
      now rewrite H in n0.
  Qed.

  Lemma reduce_to_prod_complete {Γ t wt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_prod Γ t wt = TypeError_comp e p ->
    (forall na a b, red Σ Γ t (tProd na a b) -> False).
  Proof using Type.
    intros _ na a b r.
    apply p.
    exists na, a, b.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
    eapply into_closed_red; fvs.
    Unshelve. eauto.
  Qed.

  Equations? reduce_to_ind (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ i u l, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ mkApps (tInd i u) l ∥) :=
    reduce_to_ind Γ t h with inspect (decompose_app t) := {
      | exist (thd, args) eq_decomp with view_indc thd := {
        | view_ind_tInd i u => Checked_comp (i; u; args; _);
        | view_ind_other thd _ with inspect (reduce_stack RedFlags.default _ X Γ t [] h) := {
          | exist (hnft, π) eq with view_indc hnft := {
            | view_ind_tInd i' u with inspect (decompose_stack π) := {
              | exist (l, _) eq_decomp' => Checked_comp (i'; u; l; _)
              };
            | view_ind_other _ _ => TypeError_comp (NotAnInductive t) _
            }
          }
        }
      }.
  Proof using Type.
    - specialize (h _ wfΣ). destruct h  as [? h].
      assert (Xeq : mkApps (tInd i u) args = t).
      { etransitivity. 2: symmetry; eapply mkApps_decompose_app.
        now rewrite <- eq_decomp. }
      rewrite Xeq. pose proof (hΣ := hΣ _ _ _ wfΣ); sq; eapply (wt_closed_red_refl h).
    - pose proof (reduce_stack_sound RedFlags.default _ X _ wfΣ _ _ [] h).
      rewrite <- eq in H.
      cbn in *.
      assert (π = appstack l []) as ->.
      2: { now rewrite zipc_appstack in H. }
      unfold reduce_stack in eq.
      edestruct reduce_stack_full as (?&_&stack_val&?); eauto.
      subst x.
      unfold Pr in stack_val.
      cbn in *.
      assert (decomp: decompose_stack π = ((decompose_stack π).1, [])).
      { rewrite stack_val.
        now destruct decompose_stack. }
      apply decompose_stack_eq in decomp as ->.
      now rewrite <- eq_decomp'.
    - destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
      specialize (X3 _ wfΣ).
      pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
      pose proof (reduce_stack_whnf RedFlags.default _ X Γ t [] h _  wfΣ) as wh.
      unfold reduce_stack in *.
      edestruct reduce_stack_full as ((hd&π')&r'&stack_valid&(notapp&_)); eauto.
      destruct wh as [wh].
      apply Req_red in r' as [r'].
      unfold Pr in stack_valid.
      cbn in *.
      eapply into_closed_red in r'; fvs.
      eapply PCUICContextConversion.closed_red_confluence in r' as (?&r1&r2).
      2 : exact X3.
      assert (exists args, π' = appstack args []) as (?&->).
      { exists ((decompose_stack π').1).
        assert (decomp: decompose_stack π' = ((decompose_stack π').1, [])).
        { now rewrite stack_valid; destruct decompose_stack; cbn. }
        now apply decompose_stack_eq in decomp. }
      unfold zipp in wh.
      rewrite stack_context_appstack, decompose_stack_appstack in wh.
      rewrite zipc_appstack in r2.
      cbn in *.
      rewrite app_nil_r in wh.
      eapply whnf_red_inv in r2; eauto.
      apply invert_red_mkApps_tInd in r1 as (?&[-> _ ?]); auto.
      apply whnf_red_mkApps_inv in r2 as (?&?); auto.
      depelim w.
      noconf eq.
      discriminate i0.
  Qed.

  Lemma reduce_to_ind_complete  Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ty wat e p :
    reduce_to_ind Γ ty wat = TypeError_comp e p ->
    forall ind u args,
      red Σ Γ ty (mkApps (tInd ind u) args) ->
      False.
  Proof using Type.
    intros _ ind u args' r.
    apply p.
    exists ind, u, args'.
    intros.
    erewrite (abstract_env_ext_irr _ _ wfΣ); eauto.
    pose proof (hΣ := hΣ _ _ _ wfΣ). sq.
    eapply into_closed_red ; fvs.
    Unshelve. eauto.
  Qed.

  (* Definition of assumption-only arities (without lets) *)
  Definition arity_ass := aname * term.

  Fixpoint mkAssumArity (l : list arity_ass) (s : sort) : term :=
    match l with
    | [] => tSort s
    | (na, A) :: l => tProd na A (mkAssumArity l s)
    end.

  Definition arity_ass_context := rev_map (fun '(na, A) => vass na A).

  Lemma assumption_context_arity_ass_context l :
    assumption_context (arity_ass_context l).
  Proof using Type.
    unfold arity_ass_context.
    rewrite rev_map_spec.
    induction l using MRList.rev_ind; cbn.
    - constructor.
    - rewrite map_app, rev_app_distr.
      cbn.
      destruct x.
      constructor; auto.
  Qed.

  Lemma mkAssumArity_it_mkProd_or_LetIn (l : list arity_ass) (s : sort) :
    mkAssumArity l s = it_mkProd_or_LetIn (arity_ass_context l) (tSort s).
  Proof using Type.
    unfold arity_ass_context.
    rewrite rev_map_spec.
    induction l; auto.
    cbn.
    destruct a.
    rewrite IHl, it_mkProd_or_LetIn_app; auto.
  Qed.

  Lemma isArity_mkAssumArity l s :
    isArity (mkAssumArity l s).
  Proof using Type.
    induction l as [|(na & A) l IH]; cbn; auto.
  Qed.

  Record conv_arity {Γ T} : Type :=
    build_conv_arity {
        conv_ar_context : list arity_ass;
        conv_ar_univ : sort;
        conv_ar_red : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ T ⇝ mkAssumArity conv_ar_context conv_ar_univ ∥
      }.

  Global Arguments conv_arity : clear implicits.

  Lemma conv_arity_Is_conv_to_Arity {Γ T} :
    is_closed_context Γ ->
    is_open_term Γ T ->
    conv_arity Γ T ->
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), Is_conv_to_Arity Σ Γ T.
  Proof using Type.
    intros clΓ clT [asses univ r] Σ wfΣ.
    eexists. destruct (r _ wfΣ). split; [sq|]; tea.
    apply isArity_mkAssumArity.
  Qed.

  Lemma isArity_red Σ Γ u v :
    isArity u ->
    red Σ Γ u v ->
    isArity v.
  Proof using Type.
    intros arity_u r.
    induction r using red_rect_n1; [easy|].
    eapply isArity_red1; eassumption.
  Qed.

  Lemma Is_conv_to_Arity_red Σ {wfΣ : wf Σ} Γ T T' :
    Is_conv_to_Arity Σ Γ T ->
    Σ ;;; Γ ⊢ T ⇝ T' ->
    Is_conv_to_Arity Σ Γ T'.
  Proof using Type.
    unfold Is_conv_to_Arity.
    intros [T'' (redT'' & is_arity)] red.
    sq.
    destruct (PCUICContextConversion.closed_red_confluence red redT'') as (a & reda' & reda'').
    exists a.
    split; [easy|].
    clear -is_arity reda''.
    eapply isArity_red; eauto. exact reda''.
  Qed.

  Local Instance wellfounded Σ wfΣ {normalization:NormalizationIn Σ} : WellFounded (@hnf_subterm_rel _ Σ) :=
    @wf_hnf_subterm _ _ _ normalization (heΣ _ X Σ wfΣ).

End ReduceFns.
