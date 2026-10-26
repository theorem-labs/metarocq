(** Tests of [PCUICGuardReduce]: one weak-head step with its discarded parts,
    and the iterated driver.  Every check is a [Check eq_refl : lhs = rhs]. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICGuardReduce.

Local Open Scope bs_scope.

(** ** Fixtures *)

Definition mp : modpath := MPfile ["guard_reduce_test"].
Definition nat_ind : inductive := {| inductive_mind := (mp, "nat"); inductive_ind := 0 |}.
Definition pair_ind : inductive := {| inductive_mind := (mp, "pair"); inductive_ind := 0 |}.
Definition box_ind : inductive := {| inductive_mind := (mp, "box"); inductive_ind := 0 |}.
Definition tNat := tInd nat_ind [].
Definition tO := tConstruct nat_ind 0 [].
Definition tS := tConstruct nat_ind 1 [].
Definition na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition v (s : ident) := tVar s.

Definition c_def : kername := (mp, "c_def").
Definition c_ax : kername := (mp, "c_ax").
Definition c_missing : kername := (mp, "c_missing").

Definition cbody (b : option term) : constant_body :=
  {| cst_type := tNat; cst_body := b; cst_universes := Monomorphic_ctx;
     cst_relevance := Relevant |}.

Definition nat_mib : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 0; ind_params := []; ind_bodies := [];
     ind_universes := Monomorphic_ctx; ind_variance := None |}.

Definition L (kn : kername) : option global_decl :=
  if kn == c_def then Some (ConstantDecl (cbody (Some (tLambda na tNat (tApp tS (tRel 0))))))
  else if kn == c_ax then Some (ConstantDecl (cbody None))
  else if kn == (mp, "nat") then Some (InductiveDecl nat_mib)
  else None.

Definition R := Retroknowledge.empty.

Definition hs := head_step L R [].

(** ** β *)

(** Unused binder: the argument is discarded with the domain. *)
Check eq_refl : hs (tApp (tLambda na tNat (v "b")) (v "a")) = Stepped (v "b") [tNat; v "a"].
(** Used binder: only the domain is discarded. *)
Check eq_refl : hs (tApp (tLambda na tNat (tRel 0)) (v "a")) = Stepped (v "a") [tNat].
(** With a spine. *)
Check eq_refl : hs (mkApps (tLambda na tNat (tRel 0)) [v "a"; v "c"])
  = Stepped (tApp (v "a") (v "c")) [tNat].
(** A lambda with no argument is stuck. *)
Check eq_refl : hs (tLambda na tNat (tRel 0)) = Stuck.

(** ** ζ *)

Check eq_refl : hs (tLetIn na (v "v") tNat (v "b")) = Stepped (v "b") [tNat; v "v"].
Check eq_refl : hs (tLetIn na (v "v") tNat (tRel 0)) = Stepped (v "v") [tNat].
Check eq_refl : hs (tApp (tLetIn na (v "v") tNat (tRel 0)) (v "c"))
  = Stepped (tApp (v "v") (v "c")) [tNat].

(** ** δ on constants *)

Check eq_refl : hs (tApp (tConst c_def []) (v "a"))
  = Stepped (tApp (tLambda na tNat (tApp tS (tRel 0))) (v "a")) [].
Check eq_refl : hs (tApp (tConst c_ax []) (v "a")) = Stuck.
Check eq_refl : hs (tConst c_missing []) = StepBad err_const_missing.
Check eq_refl : hs (tConst (mp, "nat") []) = StepBad err_not_const.

(** ** δ on local [let]s through [lctx] *)

(** [tRel 1] has body [tRel 0] in the context of position 1: reduct [tRel 2]. *)
Check eq_refl : head_step L R [None; Some (tRel 0)] (tApp (tRel 1) (v "c"))
  = Stepped (tApp (tRel 2) (v "c")) [].
Check eq_refl : head_step L R [None; Some (tRel 0)] (tRel 0) = Stuck.
Check eq_refl : head_step L R [None; Some (tRel 0)] (tRel 5) = Stuck.
Check eq_refl : hs (tRel 0) = Stuck.

(** ** Stuck heads *)

Check eq_refl : hs (tApp (v "f") (v "a")) = Stuck.
Check eq_refl : hs (tEvar 0 []) = Stuck.
Check eq_refl : hs (tSort sProp) = Stuck.
Check eq_refl : hs (tProd na tNat tNat) = Stuck.
Check eq_refl : hs tNat = Stuck.
Check eq_refl : hs (tApp tS tO) = Stuck.

(** ** ι *)

Definition ci_nat : case_info := {| ci_ind := nat_ind; ci_npar := 0; ci_relevance := Relevant |}.
Definition p_nat : predicate term :=
  {| pparams := []; puinst := []; pcontext := [vass na tNat]; preturn := v "P" |}.
Definition br_O := {| bcontext := []; bbody := v "a" |}.
Definition br_S := {| bcontext := [vass na tNat]; bbody := tRel 0 |}.

(** [match S n with O => a | S m => m end]: the reduct is the β-redex
    [(fun m => m) n]; the return type and the other branch are discarded. *)
Check eq_refl : hs (tCase ci_nat p_nat (tApp tS (v "n")) [br_O; br_S])
  = Stepped (tApp (tLambda na tNat (tRel 0)) (v "n")) [v "P"; v "a"].
(** The constructor argument then goes through β. *)
Check eq_refl : whd_steps L R [] 3 (tCase ci_nat p_nat (tApp tS (v "n")) [br_O; br_S])
  = WhdOk (v "n") [v "P"; v "a"; tNat].
(** Spine after the match. *)
Check eq_refl : hs (tApp (tCase ci_nat p_nat tO [br_O; br_S]) (v "c"))
  = Stepped (tApp (v "a") (v "c")) [v "P"; tRel 0].
(** A missing branch, a constructor of another inductive, a wrong arity. *)
Check eq_refl : hs (tCase ci_nat p_nat (tApp tS (v "n")) [br_O]) = StepBad err_case_branch.
Check eq_refl : hs (tCase ci_nat p_nat (tConstruct box_ind 0 []) [br_O; br_S])
  = StepBad err_case_ind.
Check eq_refl : hs (tCase ci_nat p_nat tS [br_O; br_S]) = StepBad err_case_arity.

(** Parameters: [box A] with one constructor [mk (A) (x : A)]; the
    parameters of the predicate and of the constructor are discarded, and
    the branch context is instantiated with the parameters. *)
Definition ci_box : case_info := {| ci_ind := box_ind; ci_npar := 1; ci_relevance := Relevant |}.
Definition p_box : predicate term :=
  {| pparams := [tNat]; puinst := []; pcontext := [vass na (tInd box_ind [])]; preturn := v "P" |}.
Definition br_box := {| bcontext := [vass na (tRel 0)]; bbody := tRel 0 |}.
Check eq_refl : hs (tCase ci_box p_box (mkApps (tConstruct box_ind 0 []) [v "A"; v "x"]) [br_box])
  = Stepped (tApp (tLambda na tNat (tRel 0)) (v "x")) [tNat; v "P"; v "A"].

(** Congruence on the scrutinee: one step of the scrutinee, rebuilt. *)
Check eq_refl : hs (tCase ci_nat p_nat (tApp (tLambda na tNat (tApp tS (tRel 0))) (v "n")) [br_O; br_S])
  = Stepped (tCase ci_nat p_nat (tApp tS (v "n")) [br_O; br_S]) [tNat].
Check eq_refl : hs (tCase ci_nat p_nat (v "x") [br_O; br_S]) = Stuck.

(** ** π *)

(** [pair A B] with constructor [mk (A B) (x : A) (y : B)]. *)
Definition pr_y : projection := {| proj_ind := pair_ind; proj_npars := 2; proj_arg := 1 |}.
Definition pair_val := mkApps (tConstruct pair_ind 0 []) [v "A"; v "B"; v "x"; v "y"].
Check eq_refl : hs (tProj pr_y pair_val) = Stepped (v "y") [v "A"; v "B"; v "x"].
Check eq_refl : hs (tApp (tProj pr_y pair_val) (v "c")) = Stepped (tApp (v "y") (v "c")) [v "A"; v "B"; v "x"].
Check eq_refl : hs (tProj {| proj_ind := pair_ind; proj_npars := 2; proj_arg := 2 |} pair_val)
  = StepBad err_proj_arg.
Check eq_refl : hs (tProj pr_y (mkApps (tConstruct box_ind 0 []) [v "A"; v "x"])) = StepBad err_proj_ctor.
(** Congruence on the projected term. *)
Check eq_refl : hs (tProj pr_y (tApp (tLambda na tNat pair_val) tO)) = Stepped (tProj pr_y pair_val) [tNat; tO].
Check eq_refl : hs (tProj pr_y (v "r")) = Stuck.

(** ** fix *)

(** [fix f (n : nat) : nat := f n]: the body names the block; nothing is
    discarded. *)
Definition fty := tProd na tNat tNat.
Definition mfix_rec := [{| dname := na; dtype := fty; dbody := tLambda na tNat (tApp (tRel 1) (tRel 0)); rarg := 0 |}].
Check eq_refl : hs (tApp (tFix mfix_rec 0) tO)
  = Stepped (tApp (tLambda na tNat (tApp (tFix mfix_rec 0) (tRel 0))) tO) [].

(** A mutual block whose first body names no function of the block: every
    type and the other body are discarded. *)
Definition mfix_mut :=
  [{| dname := na; dtype := v "T0"; dbody := tLambda na tNat (v "r"); rarg := 0 |};
   {| dname := na; dtype := v "T1"; dbody := tLambda na tNat (tApp (tRel 2) (tRel 0)); rarg := 0 |}].
Check eq_refl : hs (tApp (tFix mfix_mut 0) (tApp tS tO))
  = Stepped (tApp (tLambda na tNat (v "r")) (tApp tS tO))
      [v "T0"; v "T1"; tLambda na tNat (tApp (tRel 2) (tRel 0))].

(** The recursive argument is not a constructor but steps: one step of it,
    rebuilt (recursive argument at position 1 of 3). *)
Definition mfix_r1 := [{| dname := na; dtype := v "T"; dbody := tLambda na tNat (tLambda na tNat (tLambda na tNat (tRel 1))); rarg := 1 |}].
Check eq_refl : hs (mkApps (tFix mfix_r1 0) [v "a"; tApp (tLambda na tNat tO) (v "z"); v "c"])
  = Stepped (mkApps (tFix mfix_r1 0) [v "a"; tO; v "c"]) [tNat; v "z"].
(** ... and then unfolds. *)
Check eq_refl : hs (mkApps (tFix mfix_r1 0) [v "a"; tO; v "c"])
  = Stepped (mkApps (tLambda na tNat (tLambda na tNat (tLambda na tNat (tRel 1)))) [v "a"; tO; v "c"]) [v "T"].
(** Stuck recursive argument; too few arguments; index out of range. *)
Check eq_refl : hs (mkApps (tFix mfix_r1 0) [v "a"; v "x"; v "c"]) = Stuck.
Check eq_refl : hs (mkApps (tFix mfix_r1 0) [v "a"]) = Stuck.
Check eq_refl : hs (tApp (tFix mfix_r1 1) tO) = StepBad err_fix_index.

(** ** cofix in a scrutinee *)

(** [cofix g := S g]: the body names the block; nothing is discarded. *)
Definition mcofix := [{| dname := na; dtype := v "T"; dbody := tApp tS (tRel 0); rarg := 0 |}].
Check eq_refl : hs (tCase ci_nat p_nat (tCoFix mcofix 0) [br_O; br_S])
  = Stepped (tCase ci_nat p_nat (tApp tS (tCoFix mcofix 0)) [br_O; br_S]) [].
(** A body that does not name the block: the type is discarded. *)
Definition mcofix2 := [{| dname := na; dtype := v "T"; dbody := tApp tS (v "n"); rarg := 0 |}].
Check eq_refl : hs (tCase ci_nat p_nat (tCoFix mcofix2 0) [br_O; br_S])
  = Stepped (tCase ci_nat p_nat (tApp tS (v "n")) [br_O; br_S]) [v "T"].
Check eq_refl : hs (tProj pr_y (tCoFix mcofix2 0)) = Stepped (tProj pr_y (tApp tS (v "n"))) [v "T"].
(** A cofix outside a match or a projection is stuck. *)
Check eq_refl : hs (tCoFix mcofix 0) = Stuck.

(** ** The driver *)

Definition omega := tLambda na tNat (tApp (tRel 0) (tRel 0)).
Check eq_refl : whd_steps L R [] 4 (tApp omega omega) = WhdFuel.
Check eq_refl : whd_plain L R 0 (v "x") = WhdOk (v "x") [].
(** [2 ^ 0] call: one step taken, no call left to see [Stuck]. *)
Check eq_refl : whd_plain L R 0 (tApp (tLambda na tNat (tRel 0)) (v "a")) = WhdFuel.
Check eq_refl : whd_plain L R 1 (tApp (tLambda na tNat (tRel 0)) (v "a")) = WhdOk (v "a") [tNat].
(** δ, β, then stuck at a constructor; discarded parts accumulate in order. *)
Check eq_refl : whd_plain L R 2 (tApp (tLetIn na (v "v") tNat (tConst c_def [])) (v "a"))
  = WhdOk (tApp tS (v "a")) [tNat; v "v"; tNat].
(** A bad step propagates. *)
Check eq_refl : whd_plain L R 3 (tApp (tLambda na tNat (tConst c_missing [])) (v "a"))
  = WhdBad err_const_missing.
(** Local [let]s are seen by [whd_steps], not by [whd_plain]. *)
Check eq_refl : whd_steps L R [Some tO] 2 (tRel 0) = WhdOk tO [].
Check eq_refl : whd_plain L R 2 (tRel 0) = WhdOk (tRel 0) [].

(** ** Head inspection *)

Check eq_refl : whd_head_ctor L R [] 2 (tApp (tConst c_def []) (v "n"))
  = CtorApp nat_ind 1 [] [v "n"] [tNat].
Check eq_refl : whd_head_ctor L R [] 2 (v "x") = CtorOther (v "x") [].
Check eq_refl : whd_head_ctor L R [] 2 (tConst c_missing []) = CtorBad err_const_missing.
Check eq_refl : whd_head_ctor L R [] 1 (tApp omega omega) = CtorFuel.
