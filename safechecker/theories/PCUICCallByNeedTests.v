(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed.

(** * Regression tests of the call-by-need machine

  Each test runs the machine on a fixed term and checks the answer by computation. None of
  them looks up the environment, so they hold for every abstract environment [X]. *)

Section Tests.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  Definition t_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
  Definition t_nat : inductive :=
    {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
  Definition t_O : term := tConstruct t_nat 0 [].
  Definition t_S : term := tConstruct t_nat 1 [].
  Definition t_ci (npar : nat) : case_info :=
    {| ci_ind := t_nat; ci_npar := npar; ci_relevance := Relevant |}.
  Definition t_pred : predicate term :=
    {| pparams := []; puinst := []; pcontext := []; preturn := tSort sProp |}.

  (** Weak-head evaluation of [t] in [Γ], from the initial state, with the fuel of a real
    call. *)
  Definition t_run (Γ : context) (t : term) : cbn_res (cbn_value * list root * cbn_state) :=
    whnf X_type X Γ #|Γ| false cbn_depth env_empty (mkCode String2pos.xH path_nil t) []
      [] cbn_init.

  (** ** Iota: the arity of the constructor

    The branch test once compared the arguments left after dropping the parameters,
    [#|skipn ci_npar args|], with the length of the branch context. A constructor with fewer
    arguments than the match has parameters drops to no arguments at all, so with an empty
    branch context the test passed and the machine selected a branch for a term that PCUIC
    leaves stuck. The test is now [red_iota]'s own condition,
    [#|args| = ci_npar + context_assumptions bcontext]. *)

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

  (** A branch context with a let-in: the arity condition holds ([O] has no argument and the
    context has no assumption) and PCUIC's iota fires, but the machine gives up. This is a
    deliberate completeness limit, not an oversight: the machine does no [expand_lets], so it
    declines, the fast path answers "don't know", and the unchanged checker decides. *)
  Definition t_iota_letin : term :=
    tCase (t_ci 0) t_pred t_O
      [{| bcontext := [vdef t_na t_O (tInd t_nat [])]; bbody := tRel 0 |}].

  Lemma iota_gives_up_on_letin_context : t_run [] t_iota_letin = CFail WShape.
  Proof. vm_compute. reflexivity. Qed.

  (** ** Fixpoint: the forced recursive argument

    To unfold a fixpoint the machine forces the recursive argument to a constructor. It once
    left the argument's own cell in the stack. That was sound for conversion, because the
    heap read-back of a forced cell is its value, but the cell still stood for the unforced
    argument in the proof's reading, so the soundness theorem could not be stated for the
    rule. The machine now puts the forced value in a fresh cell. In
    [F := fix f n := fun g => g n], [Γ = [k]], [t = F ((fun x => x) (S O)) k], the cells are
    allocated in this order: 1 for [k], 2 for the argument, 3 for [O], 4 for the fresh copy
    of the forced value [S O] (the old machine passed 2 here), and 5 for the fixpoint. *)
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

End Tests.
