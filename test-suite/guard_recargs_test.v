(** Tests of the recursive-argument trees of PCUICRecArgs: the number of
    recursive parameters and the trees of quoted inductive blocks, as the
    kernel computes them in kernel/indtypes.ml, and the guard-time
    approximation of kernel/inductive.ml. *)
From MetaRocq.Template Require Import All.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICProgram PCUICRecArgs.
From Stdlib Require Import List PArray.

Import List.ListNotations.
Local Open Scope bs_scope.

(** A reducer for these tests only: beta, zeta and delta on constants (by
    the environment), with unary fuel; every [tRel] is an opaque variable. *)
Fixpoint test_whd (Σ : PCUICEnvironment.global_env) (fuel : nat) (t : PCUICAst.term) : red_answer :=
  match fuel with
  | 0 => RdFuel
  | S fuel =>
    let '(hd, args) := decompose_app t in
    match hd with
    | PCUICAst.tLambda _ _ b =>
      match args with
      | a :: args => test_whd Σ fuel (PCUICAst.mkApps (PCUICAst.subst10 a b) args)
      | [] => RdWhnf t
      end
    | PCUICAst.tLetIn _ v _ b => test_whd Σ fuel (PCUICAst.mkApps (PCUICAst.subst10 v b) args)
    | PCUICAst.tConst c u =>
      match PCUICEnvironment.lookup_env Σ c with
      | Some (PCUICEnvironment.ConstantDecl cb) =>
        match cb.(PCUICEnvironment.cst_body) with
        | Some b => test_whd Σ fuel (PCUICAst.mkApps (subst_instance u b) args)
        | None => RdWhnf t
        end
      | Some (PCUICEnvironment.InductiveDecl _) => RdBad "test_whd: not a constant"
      | None => RdBad "test_whd: unknown constant"
      end
    | _ => RdWhnf t
    end
  end.

Definition pcuic_env (p : Ast.Env.program) : PCUICEnvironment.global_env :=
  trans_env_env (trans_global_env p.1).

Definition ind_of (p : Ast.Env.program) : inductive :=
  match p.2 with
  | Ast.tInd ind _ => ind
  | _ => mkInd (MPfile [], "") 0
  end.

Definition test_fuel := 10.

Definition env_whd (p : Ast.Env.program) := test_whd (pcuic_env p) 1000.
Definition env_lookup (p : Ast.Env.program) := PCUICEnvironment.lookup_env (pcuic_env p).
Definition env_retro (p : Ast.Env.program) := (pcuic_env p).(PCUICEnvironment.retroknowledge).

(** [ind_block_recargs] on the block of the quoted inductive. *)
Definition run (p : Ast.Env.program) : rt_answer (nat * list wf_paths) :=
  ind_block_recargs (env_whd p) (env_lookup p) (env_retro p) test_fuel (ind_of p).(inductive_mind).

(** [get_recargs_approx] in the environment of [p], without the memo. *)
Definition approx (p : Ast.Env.program) (tree : wf_paths) (ind : inductive) (args : list PCUICAst.term)
  : rt_answer wf_paths :=
  match get_recargs_approx (env_whd p) (env_lookup p) (env_retro p) test_fuel [] tree ind args with
  | RtOk (t, _) => RtOk t
  | RtBad m => RtBad m
  | RtFuel => RtFuel
  end.

(** ** nat *)
MetaRocq Quote Recursively Definition q_nat := nat.
Definition nat_i := ind_of q_nat.
Eval vm_compute in run q_nat.
(* No parameter, so nmr = 0.  O has no argument; the argument of S is Rel 0
   at depth 0, the variable of nat, so its tree is RVar 0 0 (Mrec). *)
Definition nat_tree : wf_paths := RRec 0 [mk_paths (Mrec (RecArgInd nat_i)) [[]; [RVar 0 0]]].
Check (@eq_refl _ (RtOk (0, [nat_tree])) <: run q_nat = RtOk (0, [nat_tree])).

(** ** list *)
MetaRocq Quote Recursively Definition q_list := list.
Definition list_i := ind_of q_list.
Eval vm_compute in run q_list.
(* cons x l: x : A is the parameter Rel 0 (Norec, mk_norec); l : list A is
   Rel 2 = list (Mrec, RVar 0 0) applied to Rel 1 = A, the parameter at its
   own position, so compute_rec_par keeps nmr = 1. *)
Definition list_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd list_i)) [[]; [mk_norec; RVar 0 0]]].
Check (@eq_refl _ (RtOk (1, [list_tree])) <: run q_list = RtOk (1, [list_tree])).

(** ** A mutual block *)
Module EvenOdd.
  Inductive even : nat -> Prop :=
  | ev0 : even 0
  | evS n : odd n -> even (S n)
  with odd : nat -> Prop :=
  | odS n : even n -> odd (S n).
End EvenOdd.
MetaRocq Quote Recursively Definition q_even := EvenOdd.even.
Definition eo_kn := (ind_of q_even).(inductive_mind).
Eval vm_compute in run q_even.
(* No parameter, nmr = 0.  ra_env lists odd (RVar 0 1) at Rel 0 and even
   (RVar 0 0) at Rel 1.  evS n h: n : nat is Norec; h : odd n is Rel 1 under
   n, i.e. odd, RVar 0 1.  odS n h: h : even n is even, RVar 0 0.  The block
   is one Rtree.mk_rec of the two nodes. *)
Definition eo_defs : list wf_paths :=
  [mk_paths (Mrec (RecArgInd (mkInd eo_kn 0))) [[]; [mk_norec; RVar 0 1]];
   mk_paths (Mrec (RecArgInd (mkInd eo_kn 1))) [[mk_norec; RVar 0 0]]].
Check (@eq_refl _ (RtOk (0, [RRec 0 eo_defs; RRec 1 eo_defs]))
       <: run q_even = RtOk (0, [RRec 0 eo_defs; RRec 1 eo_defs])).

(** ** A nested inductive *)
Inductive rose := Node : list rose -> rose.
MetaRocq Quote Recursively Definition q_rose := rose.
Definition rose_i := ind_of q_rose.
Eval vm_compute in run q_rose.
(* Node l: l : list rose is Ind list applied to Rel 0 = rose, so
   check_positivity_nested on list (nmr of list = 1, so Rel 0 is its
   recursive parameter): in the constructors of list with the parameter
   replaced, the head variable of list is RVar 0 0 and rose is RVar 1 0;
   cons gets [RVar 1 0; RVar 0 0], under an Mrec (RecArgInd list) node.
   No parameter, so nmr = 0. *)
Definition rose_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd rose_i))
            [[RRec 0 [mk_paths (Mrec (RecArgInd list_i)) [[]; [RVar 1 0; RVar 0 0]]]]]].
Check (@eq_refl _ (RtOk (0, [rose_tree])) <: run q_rose = RtOk (0, [rose_tree])).

(** ** A non-uniform parameter *)
Inductive Nest (A : Type) : Type :=
| NNil : Nest A
| NCons : A -> Nest (A * A) -> Nest A.
MetaRocq Quote Recursively Definition q_nest := Nest.
Definition nest_i := ind_of q_nest.
Eval vm_compute in run q_nest.
(* NCons a n: a : A is Norec; n : Nest (A * A) is Mrec (RVar 0 0), and its
   argument A * A is not the parameter variable, so compute_rec_par returns
   0: nmr = 0 (Rocq's Nest_ind, printed below, quantifies P over A). *)
Check Nest_ind.
Definition nest_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd nest_i)) [[]; [mk_norec; RVar 0 0]]].
Check (@eq_refl _ (RtOk (0, [nest_tree])) <: run q_nest = RtOk (0, [nest_tree])).

(** ** A function-typed recursive argument *)
Inductive W := sup : (nat -> W) -> W.
MetaRocq Quote Recursively Definition q_w := W.
Definition w_i := ind_of q_w.
Eval vm_compute in run q_w.
(* sup f: f : nat -> W is a product; check_strict_positivity crosses it and
   finds Rel 1 = W under the binder: RVar 0 0.  nmr = 0. *)
Definition w_tree : wf_paths := RRec 0 [mk_paths (Mrec (RecArgInd w_i)) [[RVar 0 0]]].
Check (@eq_refl _ (RtOk (0, [w_tree])) <: run q_w = RtOk (0, [w_tree])).

(** ** A constructor with a [let] argument before a recursive one *)
Inductive LetArg : Type :=
| lnil : LetArg
| lcons (n : nat) (m := S n) (x : LetArg) : LetArg.
MetaRocq Quote Recursively Definition q_letarg := LetArg.
Definition letarg_i := ind_of q_letarg.
Eval vm_compute in run q_letarg.
(* lcons: whd_all contracts the let, so it has no tree; n : nat is Norec and
   x : LetArg is Mrec (RVar 0 0).  nmr = 0. *)
Definition letarg_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd letarg_i)) [[]; [mk_norec; RVar 0 0]]].
Check (@eq_refl _ (RtOk (0, [letarg_tree])) <: run q_letarg = RtOk (0, [letarg_tree])).

(** ** A [let] parameter *)
Inductive LetPar (A : Type) (B := A) : Type :=
| lpnil : LetPar A
| lpcons : LetPar B -> LetPar A.
MetaRocq Quote Recursively Definition q_letpar := LetPar.
Definition letpar_i := ind_of q_letpar.
Eval vm_compute in run q_letpar.
(* lpcons: LetPar B is Mrec (RVar 0 0); whd_all unfolds the let parameter B
   to A, the parameter at its own position, so compute_rec_par keeps
   nmr = 1 (Rocq's LetPar_ind, printed below, takes A as a uniform
   parameter). *)
Check LetPar_ind.
Definition letpar_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd letpar_i)) [[]; [RVar 0 0]]].
Check (@eq_refl _ (RtOk (1, [letpar_tree])) <: run q_letpar = RtOk (1, [letpar_tree])).

(** ** A record with a [let] field *)
Record LetRec (A : Type) := { lr_a : A; lr_b := lr_a; lr_c : list A }.
MetaRocq Quote Recursively Definition q_letrec := LetRec.
Definition letrec_i := ind_of q_letrec.
Eval vm_compute in run q_letrec.
(* Non-recursive block: the let field has no tree, lr_a : A and
   lr_c : list A mention no inductive of the block (Norec, the nested case
   is not entered).  No recursive occurrence lowers nmr: nmr = 1. *)
Definition letrec_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd letrec_i)) [[mk_norec; mk_norec]]].
Check (@eq_refl _ (RtOk (1, [letrec_tree])) <: run q_letrec = RtOk (1, [letrec_tree])).

(** ** An inductive nested through a primitive array *)
Inductive atree := anode : array atree -> atree.
MetaRocq Quote Recursively Definition q_atree := atree.
MetaRocq Quote Definition q_array := @array.
Definition array_kn : kername :=
  match q_array with Ast.tConst kn _ => kn | _ => (MPfile [], "") end.
Definition atree_i := ind_of q_atree.
(* The quoted environment records the array type in its retroknowledge. *)
Check (@eq_refl _ (Some array_kn)
       <: (env_retro q_atree).(Retroknowledge.retro_array) = Some array_kn).
Eval vm_compute in run q_atree.
(* anode a: a : array atree is the primitive container applied to Rel 0 =
   atree, so check_positivity_nested_primitive: the one argument of the
   modelled constructor is atree, lifted under the new Rec: RVar 1 0, under
   an Mrec (RecArgPrim array) node.  nmr = 0. *)
Definition atree_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd atree_i))
            [[RRec 0 [mk_paths (Mrec (RecArgPrim array_kn)) [[RVar 1 0]]]]]].
Check (@eq_refl _ (RtOk (0, [atree_tree])) <: run q_atree = RtOk (0, [atree_tree])).

(** ** Guard-time approximation *)

(* The subtree of the argument of Node, as the guard checker gets it from
   dest_subterms: the list node, with rose itself (closed) at the place of
   the variable RVar 1 0. *)
Definition list_rose_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd list_i)) [[]; [rose_tree; RVar 0 0]]].
Check (@eq_refl _ (RtOk [[list_rose_tree]])
       <: dest_subterms test_fuel rose_tree = RtOk [[list_rose_tree]]).

(* list rose, knowing the subtree of list rose: build_recargs_nested on list
   with the parameter rose; in cons, the argument rose (tree rose_tree) is
   traversed again (it is nested in rose_tree), and gives rose_tree; the
   tail is list itself, RVar 0 0.  The result is the subtree itself. *)
Eval vm_compute in approx q_rose list_rose_tree list_i [PCUICAst.tInd rose_i []].
Check (@eq_refl _ (RtOk list_rose_tree)
       <: approx q_rose list_rose_tree list_i [PCUICAst.tInd rose_i []] = RtOk list_rose_tree).

(* list nat, knowing the subtree of list rose: in cons, the argument nat
   is an inductive other than the one the tree expects (rose), so it is
   pruned to mk_norec. *)
Definition list_nat_tree : wf_paths :=
  RRec 0 [mk_paths (Mrec (RecArgInd list_i)) [[]; [mk_norec; RVar 0 0]]].
Check (@eq_refl _ (RtOk list_nat_tree)
       <: approx q_rose list_rose_tree list_i [PCUICAst.tInd nat_i []] = RtOk list_nat_tree).

(* A Norec tree stops the traversal at once. *)
Check (@eq_refl _ (RtOk mk_norec)
       <: approx q_rose mk_norec list_i [PCUICAst.tInd rose_i []] = RtOk mk_norec).

(* The memo returned holds each block met once: list (the container, first)
   and rose (traversed again inside cons); the computation of rose finds
   list in the memo. *)
Definition rose_list_memo := [rose_i.(inductive_mind); list_i.(inductive_mind)].
Check (@eq_refl _ (RtOk rose_list_memo)
       <: (match get_recargs_approx (env_whd q_rose) (env_lookup q_rose) (env_retro q_rose)
                   test_fuel [] list_rose_tree list_i [PCUICAst.tInd rose_i []] with
           | RtOk (_, memo) => RtOk (map fst memo)
           | RtBad m => RtBad m
           | RtFuel => RtFuel
           end) = RtOk rose_list_memo).

Definition rt_fst {X Y} (r : rt_answer (X * Y)) : rt_answer X :=
  match r with
  | RtOk p => RtOk p.1
  | RtBad m => RtBad m
  | RtFuel => RtFuel
  end.

(* has_constant_parameters with nvars = 1, k = 0: the recursive parameter
   of list (nmr = 1) must not mention the variable 0. *)
Definition hcp (args : list PCUICAst.term) : rt_answer bool :=
  rt_fst (has_constant_parameters (env_whd q_list) (env_lookup q_list) (env_retro q_list)
            test_fuel [] 1 0 list_i args).
Check (@eq_refl _ (RtOk true) <: hcp [PCUICAst.tInd nat_i []] = RtOk true).
Check (@eq_refl _ (RtOk false) <: hcp [PCUICAst.tRel 0] = RtOk false).
Check (@eq_refl _ (RtOk true) <: hcp [PCUICAst.tRel 1; PCUICAst.tRel 0] = RtOk true).

(* check_inductive_codomain: the codomain of fun n : nat => nat is an
   inductive; that of fun A : Type => A is not. *)
Definition anon : aname := mkBindAnn nAnon Relevant.
Check (@eq_refl _ (RtOk true)
       <: check_inductive_codomain (env_whd q_nat) test_fuel
            (PCUICAst.tLambda anon (PCUICAst.tInd nat_i []) (PCUICAst.tInd nat_i [])) = RtOk true).
Check (@eq_refl _ (RtOk false)
       <: check_inductive_codomain (env_whd q_nat) test_fuel
            (PCUICAst.tLambda anon (PCUICAst.tSort Sort.type0) (PCUICAst.tRel 0)) = RtOk false).

(** ** Tree operations *)

(* rec X = X does not build a node: invalid rec call. *)
Check (@eq_refl _ (RtBad "Rtree.mk_rec: invalid rec call" : rt_answer (list wf_paths))
       <: rt_mk_rec test_fuel [RVar 0 0 : wf_paths] = RtBad "Rtree.mk_rec: invalid rec call").
(* rec X = Y and Y = (a parameter of the enclosing level) is accepted. *)
Definition xy_defs : list wf_paths := [RVar 0 1; RVar 1 0].
Check (@eq_refl _ (RtOk [RRec 0 xy_defs; RRec 1 xy_defs])
       <: rt_mk_rec test_fuel xy_defs = RtOk [RRec 0 xy_defs; RRec 1 xy_defs]).
(* A tree and its one-step unfolding are equal; nat has an infinite branch. *)
Check (@eq_refl _ (RtOk true)
       <: rt_equal recarg_eqb test_fuel nat_tree
            (mk_paths (Mrec (RecArgInd nat_i)) [[]; [nat_tree]]) = RtOk true).
Check (@eq_refl _ (RtOk false) <: rt_equal recarg_eqb test_fuel nat_tree list_tree = RtOk false).
Check (@eq_refl _ (RtOk true) <: rt_is_infinite recarg_eqb test_fuel nat_tree = RtOk true).
Check (@eq_refl _ (RtOk false) <: rt_is_infinite recarg_eqb test_fuel mk_norec = RtOk false).
Check (@eq_refl _ (RtOk true) <: is_norec_path test_fuel mk_norec = RtOk true).
Check (@eq_refl _ (RtOk false) <: is_norec_path test_fuel nat_tree = RtOk false).
(* Meet of trees (labels meet when equal, otherwise the leaf Norec). *)
Definition inter_recarg (r r' : recarg) : option recarg :=
  if recarg_eqb r r' then Some r else None.
Check (@eq_refl _ (RtOk nat_tree)
       <: rt_inter recarg_eqb inter_recarg Norec test_fuel nat_tree nat_tree = RtOk nat_tree).
Check (@eq_refl _ (RtOk mk_norec)
       <: rt_inter recarg_eqb inter_recarg Norec test_fuel
            (mk_paths (Mrec (RecArgInd nat_i)) []) (mk_paths (Mrec (RecArgInd list_i)) [])
          = RtOk mk_norec).
Check (@eq_refl _ (RtOk true)
       <: rt_incl recarg_eqb inter_recarg Norec test_fuel nat_tree nat_tree = RtOk true).
(* Fuel exhaustion is reported as such. *)
Check (@eq_refl _ (RtFuel : rt_answer wf_paths)
       <: rt_expand 0 (RRec 0 [RRec 0 [RVar 0 0 : wf_paths]]) = RtFuel).
