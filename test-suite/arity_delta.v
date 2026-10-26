(* Distributed under the terms of the MIT license. *)
(** Inductives whose declared arity is a constant that unfolds to an arity.

    Rocq's kernel reduces the declared arity before splaying it
    ([Reduction.dest_arity], kernel/reduction.ml:177-181, called from
    [IndTyping.check_arity], kernel/indTyping.ml:173-175), and stores the
    unreduced user arity in [mind_user_arity] (kernel/indtypes.ml:521), which is
    what MetaRocq quotes into [ind_type] (template-rocq/src/quoter.ml:415).

    MetaRocq's [on_ind_body] asks for a *syntactic* arity
    (common/theories/EnvironmentTyping.v:1651-1653) and the checker runs
    [destArity] on [ind_type] without reducing
    (safechecker/theories/PCUICSafeChecker.v:2097-2099), so every inductive in
    part A below is rejected with "… is not an arity".  stdpp's
    [base.list_elem_of : ElemOf A (list A)] is the case found in the r188 grade
    tree; A4 is the same shape.

    Part A: accepted by Rocq's kernel, must be accepted by SafeCheck.
    Part B: declarations the kernel cannot build, doctored into a quoted
    environment, which must stay rejected. *)

From MetaRocq.Utils Require Import utils bytestring.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import All Loader.
Local Open Scope bs_scope.

(** * Part A: arities hidden behind a constant *)

From MetaRocq.SafeCheckerPlugin Require Import Loader.

(** A0: a syntactic arity.  Accepted before and after the change. *)
Inductive ad_ok : nat -> Prop := ad_ok_0 : ad_ok 0.
MetaRocq SafeCheck (@ad_ok).

(** A1: the declared arity is a Definition unfolding to an arity. *)
Definition ad_ar : Type := nat -> Prop.
Inductive ad_even : ad_ar :=
| ad_even_0 : ad_even 0
| ad_even_SS : forall n, ad_even n -> ad_even (S (S n)).
MetaRocq SafeCheck (@ad_even).

(** A2: a parametric alias. *)
Definition ad_rel (A : Type) : Type := A -> A -> Prop.
Inductive ad_le : ad_rel nat :=
| ad_le_n n : ad_le n n
| ad_le_S n m : ad_le n m -> ad_le n (S m).
MetaRocq SafeCheck (@ad_le).

(** A3: an alias of an alias. *)
Definition ad_ar2 : Type := ad_ar.
Inductive ad_odd : ad_ar2 := ad_odd_1 : ad_odd 1.
MetaRocq SafeCheck (@ad_odd).

(** A4: stdpp's singleton class [ElemOf], the r188 case [base.list_elem_of]. *)
#[universes(template=no)]
Inductive ad_list (A : Type) : Type :=
| ad_nil : ad_list A
| ad_cons : A -> ad_list A -> ad_list A.
Arguments ad_nil {A}.
Arguments ad_cons {A}.
Class AD_ElemOf (A C : Type) := ad_elem_of : A -> C -> Prop.
Inductive ad_list_elem_of {A} : AD_ElemOf A (ad_list A) :=
| ad_elem_of_here x l : ad_list_elem_of x (ad_cons x l)
| ad_elem_of_further x y l : ad_list_elem_of x l -> ad_list_elem_of x (ad_cons y l).
MetaRocq SafeCheck (@ad_list_elem_of).

(** A5: the alias reduces by iota, not only by delta. *)
Definition ad_iota (b : bool) : Type := if b then nat -> Prop else nat.
Inductive ad_pos : ad_iota true := ad_pos_1 : ad_pos 1.
MetaRocq SafeCheck (@ad_pos).

(** A6: the alias hides the sort only, no products. *)
Definition ad_prop : Type := Prop.
Inductive ad_tt : ad_prop := ad_tt_0 : ad_tt.
MetaRocq SafeCheck (@ad_tt).

(** A7: an alias that reduces to a let-bound arity.  The kernel's
    [whd_decompose_prod_decls] keeps the let, so [mind_arity_ctxt] (hence
    [ind_indices]) has a let declaration in it. *)
Definition ad_letar : Type := let X := nat in X -> Prop.
Inductive ad_letind : ad_letar := ad_letind_0 : ad_letind 0.
MetaRocq SafeCheck (@ad_letind).

(** A8: real parameters in front of an aliased index telescope. *)
Definition ad_parar (A : Type) : Type := nat -> Prop.
Inductive ad_tagged (A : Type) : ad_parar A := ad_tagged_0 : ad_tagged A 0.
MetaRocq SafeCheck (@ad_tagged).

(** A9: the whole block is mutual and both arities are aliases. *)
Definition ad_mar : Type := nat -> Prop.
Inductive ad_m1 : ad_mar := ad_m1_0 : ad_m1 0 | ad_m1_S n : ad_m2 n -> ad_m1 (S n)
with ad_m2 : ad_mar := ad_m2_S n : ad_m1 n -> ad_m2 (S n).
MetaRocq SafeCheck (@ad_m1).

(** * Part B: negative controls on doctored environments

    Rocq's kernel refuses an inductive whose declared arity does not reduce to
    an arity, so these declarations cannot be written down.  They are built by
    replacing [ind_type] in a quoted environment and given to the verified
    checker. *)

From MetaRocq.PCUIC Require Import PCUICAst PCUICTyping PCUICSN PCUICProgram.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICSafeChecker PCUICWfEnv PCUICWfEnvImpl.
From MetaRocq.SafeCheckerPlugin Require Import SafeTemplateChecker.

#[local,program] Instance fake_abstract_guard_impl : PCUICWfEnvImpl.abstract_guard_impl :=
  { guard_impl := PCUICWfEnvImpl.fake_guard_impl }.
Next Obligation. todo "the negative controls only need infer to compute". Qed.
#[local,program] Instance assume_normalization {nor} : @PCUICSN.Normalization default_checker_flags nor.
Next Obligation. todo "the negative controls only need infer to compute". Qed.
#[local] Existing Instance PCUICSN.normalization.

Definition ad_set (ty : Ast.term) (idx : option Ast.Env.context)
    (ib : Ast.Env.one_inductive_body) : Ast.Env.one_inductive_body :=
  {| Ast.Env.ind_name := ib.(Ast.Env.ind_name);
     Ast.Env.ind_indices := match idx with Some c => c | None => ib.(Ast.Env.ind_indices) end;
     Ast.Env.ind_sort := ib.(Ast.Env.ind_sort);
     Ast.Env.ind_type := ty;
     Ast.Env.ind_kelim := ib.(Ast.Env.ind_kelim);
     Ast.Env.ind_ctors := ib.(Ast.Env.ind_ctors);
     Ast.Env.ind_projs := ib.(Ast.Env.ind_projs);
     Ast.Env.ind_relevance := ib.(Ast.Env.ind_relevance) |}.

Definition ad_patch_decl (kn : kername) (ty : Ast.term) (idx : option Ast.Env.context)
    (d : kername × Ast.Env.global_decl) : kername × Ast.Env.global_decl :=
  match d.2 with
  | Ast.Env.InductiveDecl m =>
    if eqb d.1 kn then
      (d.1, Ast.Env.InductiveDecl
        {| Ast.Env.ind_finite := m.(Ast.Env.ind_finite);
           Ast.Env.ind_npars := m.(Ast.Env.ind_npars);
           Ast.Env.ind_params := m.(Ast.Env.ind_params);
           Ast.Env.ind_bodies := map (ad_set ty idx) m.(Ast.Env.ind_bodies);
           Ast.Env.ind_universes := m.(Ast.Env.ind_universes);
           Ast.Env.ind_variance := m.(Ast.Env.ind_variance) |})
    else d
  | _ => d
  end.

Definition ad_patch_gen (kn : kername) (ty : Ast.term) (idx : option Ast.Env.context)
    (p : Ast.Env.program) : Ast.Env.program :=
  ({| Ast.Env.universes := p.1.(Ast.Env.universes);
      Ast.Env.declarations := map (ad_patch_decl kn ty idx) p.1.(Ast.Env.declarations);
      Ast.Env.retroknowledge := p.1.(Ast.Env.retroknowledge) |}, p.2).

Definition ad_patch (kn : kername) (ty : Ast.term) (p : Ast.Env.program) : Ast.Env.program :=
  ad_patch_gen kn ty None p.

Definition ad_kn (t : Ast.term) : kername :=
  match t with
  | Ast.tInd ind _ => ind.(inductive_mind)
  | _ => (MPfile [], "not an inductive")
  end.

(** The source block: [ad_src : nat -> Prop], one index, sort Prop. *)
Inductive ad_src : nat -> Prop := ad_src_0 : ad_src 0.

(** Constants to put in [ind_type].  All of them are in the quoted environment
    because [ad_witness] mentions them. *)
Definition ad_notar : Type := nat.                 (* does not reduce to an arity *)
Definition ad_right : Type := nat -> Prop.         (* the arity of [ad_src] *)
Definition ad_wrongidx : Type := bool -> Prop.     (* an arity, wrong index type *)
Definition ad_wrongsort : Type := nat -> Set.      (* an arity, wrong sort *)
Axiom ad_opaque : Type.                            (* an arity-typed axiom: no body *)

(** A block with no constructors: nothing else pins its indices, so it is the
    one place where a doctored index context is not caught by [cstr_eq]. *)
Inductive ad_empty : nat -> Prop := .

Definition ad_witness :=
  (fun (a : ad_notar) (b : ad_right) (c : ad_wrongidx) (d : ad_wrongsort) (e : ad_opaque)
       (f : ad_letar) (g : ad_empty 0) =>
     ad_src 0).

MetaRocq Quote Recursively Definition ad_prog := ad_witness.

Definition ad_src_kn : kername := Eval vm_compute in ad_kn <% ad_src %>.
Definition ad_empty_kn : kername := Eval vm_compute in ad_kn <% ad_empty %>.

(** An index context made of one let, which [it_mkProd_or_LetIn] turns into a
    [tLetIn] that zeta-reduces away.  Rocq's kernel never produces it for
    [ind_type = Prop]: [whd_decompose_prod_decls] cannot introduce a let. *)
Definition ad_let_idx : Ast.Env.context :=
  [{| decl_name := {| binder_name := nNamed "x"; binder_relevance := Relevant |};
      decl_body := Some <% 0 %>;
      decl_type := <% nat %> |}].

(* [nor] is an explicit parameter so that instance resolution finds it, as in
   test-suite/reduction_test.v:67-71. *)
Definition ad_normal : @normalizing_flags default_checker_flags.
now econstructor.
Defined.

Definition ad_run_on (nor : normalizing_flags) (kn : kername) (ty : Ast.term)
    (idx : option Ast.Env.context) : string + string :=
  infer_and_print_template_program (cf := default_checker_flags)
    (ad_patch_gen kn ty idx ad_prog) Monomorphic_ctx.

Definition ad_run (nor : normalizing_flags) (ty : Ast.term) : string + string :=
  ad_run_on nor ad_src_kn ty None.

Definition ad_rejected (r : string + string) : bool :=
  match r with inl _ => false | inr _ => true end.

(** B0: the program with no patch at all is accepted, before and after the
    change: the driver itself is sound. *)
Definition ad_B0 := Eval vm_compute in
  infer_and_print_template_program (cf := default_checker_flags) (nor := ad_normal)
    ad_prog Monomorphic_ctx.
Print ad_B0.
Definition ad_B0_accepted : ad_rejected ad_B0 = false := eq_refl.

(** B1: an arity alias that matches the declared indices and sort.
    Rejected before the change, accepted after. *)
Definition ad_B1 := Eval vm_compute in ad_run ad_normal <% ad_right %>.
Print ad_B1.
Definition ad_B1_accepted : ad_rejected ad_B1 = false := eq_refl.

(** B2: a constant that does not reduce to an arity.  Rejected, always. *)
Definition ad_B2 := Eval vm_compute in ad_run ad_normal <% ad_notar %>.
Print ad_B2.
Definition ad_B2_rejected : ad_rejected ad_B2 = true := eq_refl.

(** B3: an arity with the wrong index type.  Rejected, always. *)
Definition ad_B3 := Eval vm_compute in ad_run ad_normal <% ad_wrongidx %>.
Print ad_B3.
Definition ad_B3_rejected : ad_rejected ad_B3 = true := eq_refl.

(** B4: an arity with the wrong sort.  Rejected, always. *)
Definition ad_B4 := Eval vm_compute in ad_run ad_normal <% ad_wrongsort %>.
Print ad_B4.
Definition ad_B4_rejected : ad_rejected ad_B4 = true := eq_refl.

(** B5: an axiom of type [Type]: no body, so it reduces to nothing.
    Rejected, always. *)
Definition ad_B5 := Eval vm_compute in ad_run ad_normal <% ad_opaque %>.
Print ad_B5.
Definition ad_B5_rejected : ad_rejected ad_B5 = true := eq_refl.

(** B6: the inductive's own sort, [Prop]: an arity with no products, while the
    declaration claims one index.  Rejected, always. *)
Definition ad_B6 := Eval vm_compute in ad_run ad_normal <% Prop %>.
Print ad_B6.
Definition ad_B6_rejected : ad_rejected ad_B6 = true := eq_refl.

(** B7: the inductive's own reference, [tInd ad_src], as its own arity: not an
    arity and not even a type of the right shape.  Rejected, always. *)
Definition ad_B7 := Eval vm_compute in ad_run ad_normal <% ad_src %>.
Print ad_B7.
Definition ad_B7_rejected : ad_rejected ad_B7 = true := eq_refl.

(** B8: the zeta counterexample.  [ad_empty] has no constructors; give it
    [ind_type = Prop] and an index context made of one let.  The arity built
    from the declaration is [tLetIn x 0 nat (tSort Prop)], which is *convertible*
    to [Prop] but not a reduct of it, and Rocq's kernel computes an empty index
    context for [ind_type = Prop].  Rejected, always. *)
Definition ad_B8 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% Prop %> (Some ad_let_idx).
Print ad_B8.
Definition ad_B8_rejected : ad_rejected ad_B8 = true := eq_refl.

(** B9: the mirror.  [ind_type] is a constant whose reduct keeps a let
    ([let X := nat in X -> Prop]) while the declaration's index context has the
    zeta-reduced shape [_ : nat].  Rocq's kernel reduces with [whd_allnolet]
    (kernel/reduction.ml:122-126) and keeps the let, so it never produces this
    declaration.  Rejected, always: the checker's telescope walk reduces with
    [RedFlags.zeta := false]. *)
Definition ad_B9 := Eval vm_compute in ad_run_on ad_normal ad_empty_kn <% ad_letar %> None.
Print ad_B9.
Definition ad_B9_rejected : ad_rejected ad_B9 = true := eq_refl.
