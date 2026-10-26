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

(** A10: [whd_allnolet] keeps the outer let, then unfolds its let-bound
    variable without zeta and exposes a second let.  In telescope order the
    kernel stores [Z := (let W := nat in W -> Prop); W := nat; _ : W]. *)
Definition ad_relar : Type := let Z := (let W := nat in W -> Prop) in Z.
Inductive ad_relind : ad_relar := ad_relind_0 : ad_relind 0.
MetaRocq SafeCheck (@ad_relind).

(** A11: [whd_allnolet] stops at [App (LetIn ...)], so
    [whd_decompose_prod_decls] uses its full-[whd_all] fallback. *)
Definition ad_fbar : Type := (let F := fun X : Type => X -> Prop in F) nat.
Inductive ad_fbind : ad_fbar := ad_fbind_0 : ad_fbind 0.
MetaRocq SafeCheck (@ad_fbind).

(** C1: the documented call-by-need completeness gap of the head-only design.
    The kernel accepts this block and stores [_ : true = true], because forcing
    [b] in the match updates the shared closure.  A sharing-free relation
    substitutes [negb false] and obtains [_ : negb false = true], so the
    checker intentionally continues to refuse it. *)
Definition ad_shar (b : bool) : Type := if b then (b = true -> Prop) else nat.
Inductive ad_shind : ad_shar (negb false) := ad_shind_0 : ad_shind eq_refl.
Fail MetaRocq SafeCheck (@ad_shind).

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

(** Constructorless blocks let each negative control reach the arity check:
    no constructor can mask the intended refusal.  [ad_anchor] is quoted before
    the patched blocks, so B7 also cannot fail because its [tInd] is unbound. *)
Inductive ad_anchor : Prop := .
Inductive ad_src : nat -> Prop := ad_src_0 : ad_src 0.
Inductive ad_empty : nat -> Prop := .

(** Sources and kernel-produced index telescopes for the exactness controls. *)
Inductive ad_rel_empty : ad_relar := .
Definition ad_relbad : Type :=
  let Z := (let W := nat in W -> Prop) in nat -> Prop.
Inductive ad_relbadind : ad_relbad := .

Inductive ad_fempty : ad_fbar := .
Definition ad_keepf : Type :=
  let F := fun X : Type => X -> Prop in F nat.
Inductive ad_keepfind : ad_keepf := .

Definition ad_whole : Type := forall A : Type, nat -> Prop.
Inductive ad_pempty (A : Type) : nat -> Prop := .

(** Constants to put in [ind_type]. *)
Definition ad_notar : Type := nat.                 (* does not reduce to an arity *)
Definition ad_right : Type := nat -> Prop.         (* the arity of [ad_src] *)
Definition ad_wrongidx : Type := bool -> Prop.     (* an arity, wrong index type *)
Definition ad_wrongsort : Type := nat -> Set.      (* an arity, wrong sort *)
Definition ad_zero : Type := Prop.                 (* no products, through slow path *)
Axiom ad_opaque : Type.                            (* an arity-typed axiom: no body *)

(** Keep each aliased source in its own quoted environment.  Otherwise the
    base checker stops at an earlier unpatched alias and masks the target. *)
Definition ad_witness :=
  (fun (anchor : ad_anchor)
       (a : ad_notar) (b : ad_right) (c : ad_wrongidx) (d : ad_wrongsort)
       (z : ad_zero) (e : ad_opaque) (f : ad_letar) (whole : ad_whole)
       (g : ad_empty 0) (p : ad_pempty nat 0) =>
     ad_src 0).
Definition ad_rel_witness := (fun (r : ad_rel_empty 0) => r).
Definition ad_relbad_witness := (fun (r : ad_relbadind 0) => r).
Definition ad_f_witness := (fun (f : ad_fempty 0) => f).
Definition ad_keepf_witness := (fun (f : ad_keepfind 0) => f).

MetaRocq Quote Recursively Definition ad_prog := ad_witness.
MetaRocq Quote Recursively Definition ad_rel_prog := ad_rel_witness.
MetaRocq Quote Recursively Definition ad_relbad_prog := ad_relbad_witness.
MetaRocq Quote Recursively Definition ad_f_prog := ad_f_witness.
MetaRocq Quote Recursively Definition ad_keepf_prog := ad_keepf_witness.

Definition ad_src_kn : kername := Eval vm_compute in ad_kn <% ad_src %>.
Definition ad_empty_kn : kername := Eval vm_compute in ad_kn <% ad_empty %>.
Definition ad_anchor_kn : kername := Eval vm_compute in ad_kn <% ad_anchor %>.
Definition ad_rel_empty_kn : kername := Eval vm_compute in ad_kn <% ad_rel_empty %>.
Definition ad_relbad_kn : kername := Eval vm_compute in ad_kn <% ad_relbadind %>.
Definition ad_fempty_kn : kername := Eval vm_compute in ad_kn <% ad_fempty %>.
Definition ad_keepf_kn : kername := Eval vm_compute in ad_kn <% ad_keepfind %>.
Definition ad_pempty_kn : kername := Eval vm_compute in ad_kn <% ad_pempty %>.

Fixpoint ad_find_indices (kn : kername)
    (decls : Ast.Env.global_declarations) : option Ast.Env.context :=
  match decls with
  | [] => None
  | (kn', Ast.Env.InductiveDecl m) :: tl =>
      if eqb kn kn' then
        match m.(Ast.Env.ind_bodies) with
        | ib :: _ => Some ib.(Ast.Env.ind_indices)
        | [] => None
        end
      else ad_find_indices kn tl
  | _ :: tl => ad_find_indices kn tl
  end.

Definition ad_indices_of (p : Ast.Env.program) (kn : kername) : option Ast.Env.context :=
  ad_find_indices kn p.1.(Ast.Env.declarations).
Definition ad_relbad_idx :=
  Eval vm_compute in ad_indices_of ad_relbad_prog ad_relbad_kn.
Definition ad_keepf_idx :=
  Eval vm_compute in ad_indices_of ad_keepf_prog ad_keepf_kn.
Definition ad_relbad_idx_found :
  match ad_relbad_idx with Some _ => true | None => false end = true := eq_refl.
Definition ad_keepf_idx_found :
  match ad_keepf_idx with Some _ => true | None => false end = true := eq_refl.

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

Definition ad_run_on_prog (nor : normalizing_flags) (p : Ast.Env.program)
    (kn : kername) (ty : Ast.term) (idx : option Ast.Env.context) : string + string :=
  infer_and_print_template_program (cf := default_checker_flags)
    (ad_patch_gen kn ty idx p) Monomorphic_ctx.

Definition ad_run_on (nor : normalizing_flags) (kn : kername) (ty : Ast.term)
    (idx : option Ast.Env.context) : string + string :=
  ad_run_on_prog nor ad_prog kn ty idx.

Definition ad_run (nor : normalizing_flags) (ty : Ast.term) : string + string :=
  ad_run_on nor ad_src_kn ty None.

Definition ad_rejected (r : string + string) : bool :=
  match r with inl _ => false | inr _ => true end.

(** Negative controls name the branch that refused them, not merely [inr _].
    Some slow-path controls allow the base's syntactic [NotAnArity] message or
    the post-change declaration-mismatch message; phase 2 removes the former
    alternative after the new path exists. *)
Definition ad_error_contains (needle : string) (r : string + string) : bool :=
  match r with
  | inl _ => false
  | inr msg =>
      match String.index 0 needle msg with
      | Some _ => true
      | None => false
      end
  end.

Definition ad_error_either (p q : string) (r : string + string) : bool :=
  ad_error_contains p r || ad_error_contains q r.

Definition ad_indices_mismatch :=
  "Inductive arity indices do not match the indices of the mutual declaration".
Definition ad_sort_mismatch :=
  "Inductive body sort does not match the sort of the inductive type".

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

(** B2: a constant that does not reduce to an arity.  The constructorless
    source rules out a later constructor failure. *)
Definition ad_B2 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_notar %> None.
Print ad_B2.
Definition ad_B2_reason :
  ad_error_contains "ad_notar is not an arity" ad_B2 = true := eq_refl.

(** B3: a syntactic arity with the wrong index type.  This deliberately uses
    the unchanged fast path and must fail at the index-context comparison. *)
Definition ad_B3 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% bool -> Prop %> None.
Print ad_B3.
Definition ad_B3_reason :
  ad_error_contains ad_indices_mismatch ad_B3 = true := eq_refl.

(** B4: a syntactic arity with the wrong sort. *)
Definition ad_B4 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% nat -> Set %> None.
Print ad_B4.
Definition ad_B4_reason :
  ad_error_contains ad_sort_mismatch ad_B4 = true := eq_refl.

(** B5: an axiom of type [Type]: no body, so the slow path cannot progress. *)
Definition ad_B5 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_opaque %> None.
Print ad_B5.
Definition ad_B5_reason :
  ad_error_contains "ad_opaque is not an arity" ad_B5 = true := eq_refl.

(** B6: an alias of [Prop], so it reaches the slow path, while the declaration
    still claims one index.  The new checker must reject at telescope shape,
    not at a constructor. *)
Definition ad_B6 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_zero %> None.
Print ad_B6.
Definition ad_B6_reason :
  ad_error_either "ad_zero is not an arity" ad_indices_mismatch ad_B6 = true := eq_refl.

(** B7: a bound, earlier constructorless inductive is not an arity.  Inference
    therefore succeeds before reduction, and refusal cannot be [UnboundInd]. *)
Definition ad_B7 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_anchor %> None.
Print ad_B7.
Definition ad_B7_reason :
  ad_error_contains "ad_anchor is not an arity" ad_B7 = true := eq_refl.

(** B8: the conversion-only counterexample, forced through the slow path by
    [ad_zero].  The declaration fabricates one let index although the reduct is
    [Prop], so the post-change branch is the index-shape comparison. *)
Definition ad_B8 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_zero %> (Some ad_let_idx).
Print ad_B8.
Definition ad_B8_reason :
  ad_error_either "ad_zero is not an arity" ad_indices_mismatch ad_B8 = true := eq_refl.

(** B9: the mirror.  [ad_letar] exposes and retains a let, while [ad_empty]'s
    kernel-produced index context is only [_ : nat].  The dedicated
    let-variable-unfolding flag keeps the let without enabling zeta. *)
Definition ad_B9 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_letar %> None.
Print ad_B9.
Definition ad_B9_reason :
  ad_error_either "ad_letar is not an arity" ad_indices_mismatch ad_B9 = true := eq_refl.

(** B10: the kernel never reduces through the parameter prefix.  The declared
    arity must syntactically start with [ad_pempty]'s [A : Type] parameter,
    rather than being one constant for the whole arity. *)
Definition ad_B10 := Eval vm_compute in
  ad_run_on ad_normal ad_pempty_kn <% ad_whole %> None.
Print ad_B10.
Definition ad_B10_reason :
  ad_error_contains "ad_whole is not an arity" ad_B10 = true := eq_refl.

(** B11: [ad_relar]'s actual kernel context is
    [Z := (let W := nat in W -> Prop); W := nat; _ : W].  Replace it by the
    kernel-produced context of [ad_relbadind],
    [Z := (let W := nat in W -> Prop); _ : nat].  A reducer that leaves
    let-bound variables stuck and then uses full zeta would accept this twin. *)
Definition ad_B11 := Eval vm_compute in
  ad_run_on_prog ad_normal ad_rel_prog ad_rel_empty_kn <% ad_relar %> ad_relbad_idx.
Print ad_B11.
Definition ad_B11_reason :
  ad_error_either "ad_relar is not an arity" ad_indices_mismatch ad_B11 = true := eq_refl.

(** B12: [ad_fbar] needs [whd_all] only because its head is
    [App (LetIn ...)].  Fabricating the exposed-let context of [ad_keepfind]
    checks that the fallback does not preserve that internal let. *)
Definition ad_B12 := Eval vm_compute in
  ad_run_on_prog ad_normal ad_f_prog ad_fempty_kn <% ad_fbar %> ad_keepf_idx.
Print ad_B12.
Definition ad_B12_reason :
  ad_error_either "ad_fbar is not an arity" ad_indices_mismatch ad_B12 = true := eq_refl.
