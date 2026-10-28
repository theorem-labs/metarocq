(* Tests of the call-by-need fast path of conversion, [PCUICCallByNeed].

   The machine tests run [whnf] on a fixed term and check the answer by [vm_compute]. The
   conversion tests run [cbn_conv_answer] and [cbn_conv], the function that
   [PCUICTypeChecker.convert] calls. None of them looks up the environment, so they hold for
   every abstract environment [X]. The last section is a well-typed input on which the fast
   path answers [true], with the conversion that [convert_cbn_sound] derives from that
   answer, for every abstract environment and for a concrete one. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICWellScopedCumulativity.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICWfEnvImpl PCUICCallByNeed
  PCUICCallByNeedSoundHookProof.

Definition t_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition t_nat : inductive :=
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
Definition t_O : term := tConstruct t_nat 0 [].
Definition t_S : term := tConstruct t_nat 1 [].
Definition t_ci (npar : nat) : case_info :=
  {| ci_ind := t_nat; ci_npar := npar; ci_relevance := Relevant |}.
Definition t_pred : predicate term :=
  {| pparams := []; puinst := []; pcontext := []; preturn := tSort sProp |}.

Section Machine.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** Weak-head evaluation of [t] in [Γ], from the initial state, with the fuel of a real
    call. *)
  Definition t_run (Γ : context) (t : term) : cbn_res (cbn_value * list root * cbn_state) :=
    whnf X_type X Γ #|Γ| cbn_depth env_empty (mkCode String2pos.xH path_nil t) []
      [] cbn_init.

  (** ** Iota: the arity of the constructor

    The machine selects a branch only under [red_iota]'s own condition,
    [#|args| = ci_npar + context_assumptions bcontext], where [args] are all the arguments
    of the constructor, parameters included. *)

  (** It must refuse: one parameter, a constructor with no argument, an empty context. *)
  Definition t_iota_short : term :=
    tCase (t_ci 1) t_pred t_O [{| bcontext := []; bbody := tSort sProp |}].

  Lemma iota_refuses_missing_parameters : t_run [] t_iota_short = CFail WShape.
  Proof. vm_compute. reflexivity. Qed.

  (** It must fire: no parameter, [S O] against a branch with one assumption, which selects
    the argument [O]. *)
  Definition t_iota_fire : term :=
    tCase (t_ci 0) t_pred (tApp t_S t_O)
      [{| bcontext := []; bbody := tSort sProp |};
       {| bcontext := [vass t_na (tInd t_nat [])]; bbody := tRel 0 |}].

  Lemma iota_fires_on_full_arity :
    match t_run [] t_iota_fire with
    | COk (v, _, _) => v = VCon t_O []
    | CFail _ => False
    end.
  Proof. vm_compute. reflexivity. Qed.

  (** It must fire with a parameter: one parameter, [S] applied to the parameter [Prop] and
    to [O], against a branch with one assumption. The branch binds the argument after the
    parameter, [O]. *)
  Definition t_iota_fire_npar : term :=
    tCase (t_ci 1) t_pred (tApp (tApp t_S (tSort sProp)) t_O)
      [{| bcontext := []; bbody := tSort sProp |};
       {| bcontext := [vass t_na (tInd t_nat [])]; bbody := tRel 0 |}].

  Lemma iota_fires_after_parameters :
    match t_run [] t_iota_fire_npar with
    | COk (v, _, _) => v = VCon t_O []
    | CFail _ => False
    end.
  Proof. vm_compute. reflexivity. Qed.

  (** A branch context with a let-in: the arity condition holds ([O] has no argument and the
    context has no assumption) and PCUIC's iota fires, but the machine gives up. This is a
    deliberate completeness limit: the machine does no [expand_lets], so it declines, the
    fast path answers "don't know", and the full conversion checker decides. *)
  Definition t_iota_letin : term :=
    tCase (t_ci 0) t_pred t_O
      [{| bcontext := [vdef t_na t_O (tInd t_nat [])]; bbody := tRel 0 |}].

  Lemma iota_gives_up_on_letin_context : t_run [] t_iota_letin = CFail WShape.
  Proof. vm_compute. reflexivity. Qed.

  (** ** Fixpoint: the forced recursive argument

    To unfold a fixpoint the machine forces the recursive argument to a constructor and
    passes the forced value in a fresh cell, not the argument's own cell. In
    [F := fix f n := fun g => g n], [Γ = [k]], [t = F ((fun x => x) (S O)) k], the cells are
    allocated in this order: 1 for [k], 2 for the argument, 3 for [O], 4 for the fresh copy
    of the forced value [S O], and 5 for the fixpoint. *)
  Definition t_fixF : term :=
    tFix [{| dname := t_na; dtype := tSort sProp;
             dbody := tLambda t_na (tInd t_nat [])
                        (tLambda t_na (tSort sProp) (tApp (tRel 0) (tRel 1)));
             rarg := 0 |}] 0.

  Definition t_fix : term :=
    tApp (tApp t_fixF (tApp (tLambda t_na (tInd t_nat []) (tRel 0)) (tApp t_S t_O))) (tRel 0).

  Definition t_fixΓ : context := [vass t_na (tSort sProp)].

  Lemma fix_passes_a_fresh_forced_cell :
    match t_run t_fixΓ t_fix with
    | COk (VNeu (NVar 0) [a], _, s) =>
        a = HAddr 4 /\ heap_get a s = Some (CDone (VCon t_S [HAddr 3]))
    | _ => False
    end.
  Proof. vm_compute. split; reflexivity. Qed.

  (** And the value reads back as [k (S O)], a reduct of [t]. *)
  Lemma fix_reads_back_a_reduct :
    match t_run t_fixΓ t_fix with
    | COk (v, _, s) =>
        match rb_value 1 cbn_depth 1 v s with
        | COk (u, _) => u = tApp (tRel 0) (tApp t_S t_O)
        | CFail _ => False
        end
    | CFail _ => False
    end.
  Proof. vm_compute. reflexivity. Qed.

  (** ** Conversion: the fast path does not answer "convertible" on a stuck match

    [t_iota_short] is stuck in PCUIC, so it is not convertible to [Prop]. The machine
    refuses the branch, so the fast path gives up with [WShape] and [convert] falls through
    to the full conversion checker. *)
  Lemma cbn_conv_answer_refuses_missing_parameters :
    cbn_conv_answer X_type X Conv [] t_iota_short (tSort sProp) = CbnFail WShape.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cbn_conv_refuses_missing_parameters :
    cbn_conv X_type X Conv [] t_iota_short (tSort sProp) = false.
  Proof. vm_compute. reflexivity. Qed.
End Machine.

(** * A well-typed input on which the fast path answers [true]

  [Γ = [x := (fun q : P => q) p : P; p : P; P : Prop]], [t = x], [u = p]. The machine
  unfolds the let-bound [x], reduces the redex to [p] and compares the two variables. The
  syntactic test [eqb_term] that [convert] runs first fails on [tRel 0] against [tRel 1], so
  [convert] reaches the fast path on this input. *)

Definition wt_Γ : context :=
  [vdef t_na (tApp (tLambda t_na (tRel 1) (tRel 0)) (tRel 0)) (tRel 1);
   vass t_na (tRel 0);
   vass t_na (tSort sProp)].
Definition wt_t : term := tRel 0.
Definition wt_u : term := tRel 1.

Section WellTyped.
  Context {cf : checker_flags}.

  (** The context is well formed in every global environment: it names no constant and no
    universe level. *)
  Lemma wt_wf_local (Σ : global_env_ext) : wf_local Σ wt_Γ.
  Proof.
    assert (h1 : wf_local Σ [vass t_na (tSort sProp)]).
    { constructor; [constructor|]. split; [exact tt|].
      exists (Sort.super sProp). split; [|split; [exact I|reflexivity]].
      apply type_Sort; [constructor|exact I]. }
    assert (h2 : wf_local Σ [vass t_na (tRel 0); vass t_na (tSort sProp)]).
    { constructor; [exact h1|]. split; [exact tt|].
      exists sProp. split; [|split; [exact I|reflexivity]].
      exact (type_Rel Σ _ 0 _ h1 eq_refl). }
    assert (hP2 : Σ ;;; [vass t_na (tRel 0); vass t_na (tSort sProp)] |- tRel 1 : tSort sProp)
      by exact (type_Rel Σ _ 1 _ h2 eq_refl).
    assert (h3 : wf_local Σ [vass t_na (tRel 1); vass t_na (tRel 0); vass t_na (tSort sProp)]).
    { constructor; [exact h2|]. split; [exact tt|].
      exists sProp. split; [exact hP2|split; [exact I|reflexivity]]. }
    constructor; [exact h2|]. split.
    - cbn. change (tRel 1) with ((tRel 2) {0 := tRel 0}).
      eapply type_App with (na := t_na) (A := tRel 1) (B := tRel 2)
        (s := Sort.sort_of_product sProp sProp).
      + apply type_Prod.
        * split; [exact tt|]. exists sProp. split; [exact hP2|split; reflexivity].
        * exact (type_Rel Σ _ 2 _ h3 eq_refl).
      + apply type_Lambda.
        * split; [exact tt|]. exists sProp. split; [exact hP2|split; [exact I|reflexivity]].
        * exact (type_Rel Σ _ 0 _ h3 eq_refl).
      + exact (type_Rel Σ _ 0 _ h2 eq_refl).
    - exists sProp. split; [exact hP2|split; [exact I|reflexivity]].
  Qed.

  Lemma wt_t_welltyped (Σ : global_env_ext) : welltyped Σ wt_Γ wt_t.
  Proof. econstructor. exact (type_Rel Σ _ 0 _ (wt_wf_local Σ) eq_refl). Qed.

  Lemma wt_u_welltyped (Σ : global_env_ext) : welltyped Σ wt_Γ wt_u.
  Proof. econstructor. exact (type_Rel Σ _ 1 _ (wt_wf_local Σ) eq_refl). Qed.

  (** [convert] tries [eqb_term_upto_univ] first and calls [cbn_conv] only when it fails. It
    fails here, whatever the universe comparisons are: on two variables it compares their
    indices, and [0 <> 1]. So [convert] takes the fast path on this input. *)
  Lemma wt_eqb_false cmpu cmps gen :
    PCUICEqualityDec.eqb_term_upto_univ_napp cmpu cmps gen Conv 0 wt_t wt_u = false.
  Proof. reflexivity. Qed.

  (** The fast path answers [true], by computation, for every abstract environment. *)
  Lemma wt_cbn_conv_true (X_type : abstract_env_impl) (X : X_type.π2.π1) :
    cbn_conv X_type X Conv wt_Γ wt_t wt_u = true.
  Proof. vm_compute. reflexivity. Qed.

  (** Every premise of [convert_cbn_sound] holds, so the answer is the conversion, in every
    abstract environment. *)
  Theorem wt_fast_path_sound (X_type : abstract_env_impl) (X : X_type.π2.π1) :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; wt_Γ ⊢ wt_t ≤[Conv] wt_u ∥.
  Proof.
    exact (convert_cbn_sound X_type X Conv wt_Γ wt_t wt_u
             (fun Σ _ => wt_t_welltyped Σ) (fun Σ _ => wt_u_welltyped Σ)
             (eq_sym (wt_cbn_conv_true X_type X))).
  Qed.

  (** ** The same at a concrete environment

    The canonical abstract environment of [PCUICWfEnvImpl], built from the empty global
    environment by [abstract_env_empty_ext]. The statement is parametric in the guard
    implementation [guard], so it holds for whichever implementation the checker is built
    with. *)
  Context {guard : abstract_guard_impl}.

  Definition wt_X : (@canonical_abstract_env_impl cf guard).π2.π1 :=
    @abstract_env_empty_ext cf canonical_abstract_env_impl abstract_env_empty.

  Definition wt_Σ : global_env_ext :=
    ({| universes := (LevelSet.singleton Level.lzero, ConstraintSet.empty);
        declarations := [];
        retroknowledge := Retroknowledge.empty |}, Monomorphic_ctx).

  Lemma wt_Σ_rel : abstract_env_ext_rel wt_X wt_Σ.
  Proof.
    apply (proj1 (@abstract_env_empty_ext_rel cf canonical_abstract_env_impl
                    abstract_env_empty wt_Σ)).
    split; reflexivity.
  Qed.

  (** [cbn_conv] answers [true] at [wt_X], both inputs are well typed in the environment
    [wt_Σ] that [wt_X] stands for, and the conversion holds there. *)
  Theorem wt_fast_path_concrete :
    cbn_conv canonical_abstract_env_impl wt_X Conv wt_Γ wt_t wt_u = true
    /\ abstract_env_ext_rel wt_X wt_Σ
    /\ welltyped wt_Σ wt_Γ wt_t /\ welltyped wt_Σ wt_Γ wt_u
    /\ ∥ wt_Σ ;;; wt_Γ ⊢ wt_t ≤[Conv] wt_u ∥.
  Proof.
    split; [exact (wt_cbn_conv_true _ wt_X)|].
    split; [exact wt_Σ_rel|].
    split; [exact (wt_t_welltyped wt_Σ)|].
    split; [exact (wt_u_welltyped wt_Σ)|].
    exact (wt_fast_path_sound _ wt_X wt_Σ wt_Σ_rel).
  Qed.
End WellTyped.
