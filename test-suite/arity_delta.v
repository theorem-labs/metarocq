(* Distributed under the terms of the MIT license. *)
(** Inductives whose declared arity is a constant that unfolds to an arity.

    Rocq's kernel reduces the declared user arity before splaying it
    ([Reduction.dest_arity], called from [IndTyping.check_arity]): at each level
    it reduces with [whd_allnolet] (everything but zeta; a let-bound variable is
    still unfolded), keeps an exposed product or let, and otherwise falls back to
    [whd_all] once.  It stores the unreduced user arity, which MetaRocq quotes
    into [ind_type], and the reduced telescope, which it quotes into
    [ind_indices]/[ind_sort].

    [on_ind_body]'s field [ind_arity_red] asks that [ind_type] be the
    parameters followed by a user arity that reduces by that strategy
    ([PCUICArityRed.arity_red]) to the declaration's indices and sort, and
    [check_ind_type] computes the same reduction.  stdpp's
    [base.list_elem_of : ElemOf A (list A)] has the shape of A4.

    Part A: accepted by Rocq's kernel, must be accepted by SafeCheck.
    Part B: declarations the kernel cannot build, doctored into a quoted
    environment, which must be refused, each with the error of the branch
    that refuses it. *)

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

(** A4: stdpp's singleton class [ElemOf], the shape of [base.list_elem_of]. *)
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

(** A12: A4 with Corelib's template-polymorphic [list], as in stdpp's
    [base.list_elem_of].  [MetaRocq SafeCheck] on this tree quotes with the
    template-translating quoter, so the aliased arity [AD_ElemOf A (list A)]
    must be accepted. *)
Inductive ad_tlist_elem_of {A} : AD_ElemOf A (list A) :=
| ad_telem_of_here x l : ad_tlist_elem_of x (cons x l)
| ad_telem_of_further x y l : ad_tlist_elem_of x l -> ad_tlist_elem_of x (cons y l).
MetaRocq SafeCheck (@ad_tlist_elem_of).

(** A13: a let-bound variable as a [match] discriminant.  The kernel keeps
    [b := true] and unfolds the discriminant [Rel b] under delta; it stores
    [b := true; _ : nat].  Let-bound variables must also be unfolded in nested
    discriminant calls. *)
Definition ad_dlar : Type := let b := true in if b then nat -> Prop else nat.
Inductive ad_dlind : ad_dlar := ad_dlind_0 : ad_dlind 0.
MetaRocq SafeCheck (@ad_dlind).

(** A14: a let-parameter in front of an aliased arity with an inner let.  The
    kernel stores parameters [n := 0] and indices [Y := nat; _ : Y]. *)
Definition ad_lpar (k : nat) : Type := let Y := nat in Y -> Prop.
Inductive ad_lpind (n := 0) : ad_lpar n := ad_lpind_0 : ad_lpind 0.
MetaRocq SafeCheck (@ad_lpind).

(** A14b: the arity IS a let-parameter, so the telescope walk must unfold the
    parameter's let-bound [Rel] in the parameter context.  The kernel stores
    parameters [T := let W := nat in W -> Prop] (no assumption parameter) and
    indices [W := nat; _ : W]. *)
Inductive ad_lpind2 (T := let W := nat in W -> Prop) : T := ad_lpind2_0 : ad_lpind2 0.
MetaRocq SafeCheck (@ad_lpind2).

(** A15: the alias needs fix and iota reduction. *)
Definition ad_fixar : Type :=
  (fix f (n : nat) : Type := match n with 0 => nat -> Prop | S k => f k end) 1.
Inductive ad_fixind : ad_fixar := ad_fixind_0 : ad_fixind 0.
MetaRocq SafeCheck (@ad_fixind).

(** A16: a universe-polymorphic alias, instantiated by the inductive's own
    universe. *)
#[universes(polymorphic)]
Definition ad_upar@{u} : Type@{u+1} := Type@{u} -> Prop.
#[universes(polymorphic)]
Inductive ad_upind@{u} : ad_upar@{u} := ad_upind_0 : ad_upind nat.
MetaRocq SafeCheck (@ad_upind).

(** A18: the alias reduces through a primitive projection: delta exposes
    [ad_pf ad_prv], the projection's argument reduces to a constructor, and
    the projection contracts ([whd_proj]). *)
#[projections(primitive)]
Record ad_pr : Type := { ad_pf : Type }.
Definition ad_prv : ad_pr := {| ad_pf := nat -> Prop |}.
Inductive ad_projind : ad_pf ad_prv := ad_projind_0 : ad_projind 0.
MetaRocq SafeCheck (@ad_projind).

(** A19: the alias projects out of a cofixpoint, which must be unfolded first
    ([whd_proj_cofix]), then the projection contracts.  (A [match] on a
    coinductive would be refused by MetaRocq's typing of the alias itself, so
    the cofixpoint is a primitive coinductive record.) *)
#[projections(primitive)]
CoInductive ad_str : Type := { ad_shd : Type }.
CoFixpoint ad_cst : ad_str := {| ad_shd := nat -> Prop |}.
Definition ad_cofar : Type := ad_shd ad_cst.
Inductive ad_cofind : ad_cofar := ad_cofind_0 : ad_cofind 0.
MetaRocq SafeCheck (@ad_cofind).

(** C1: the documented call-by-need completeness gap of the head-only design.
    The kernel accepts this block and stores [_ : true = true], because forcing
    [b] in the match updates the shared closure.  A sharing-free relation
    substitutes [negb false] and obtains [_ : negb false = true], so the
    checker intentionally continues to refuse it, with the index-mismatch
    message (see [ad_C1] in part B). *)
Definition ad_shar (b : bool) : Type := if b then (b = true -> Prop) else nat.
Inductive ad_shind : ad_shar (negb false) := ad_shind_0 : ad_shind eq_refl.
Fail MetaRocq SafeCheck (@ad_shind).

(** A17: the same block declared with kernel term sharing off.
    The kernel then computes the sharing-free relation itself and stores
    [_ : negb false = true] ([ad_shind] stores [_ : true = true]), so the
    checker must accept it: spec = kernel
    without sharing. *)
Unset Kernel Term Sharing.
Inductive ad_shind_ns : ad_shar (negb false) := ad_shind_ns_0 : ad_shind_ns eq_refl.
Set Kernel Term Sharing.
MetaRocq SafeCheck (@ad_shind_ns).

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
Next Obligation. todo "the driver controls (B0-B12, C1) run infer under this test-only assumption". Qed.
#[local,program] Instance assume_normalization {nor} : @PCUICSN.Normalization default_checker_flags nor.
Next Obligation. todo "the driver controls (B0-B12, C1) run infer under this test-only assumption". Qed.
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
Definition ad_zero : Type := Prop.                 (* no products, needs reduction *)
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
    The controls B6, B8, B9, B11, B12 and C1, whose arity needs reduction,
    assert the index-mismatch message and the absence of "is not an arity":
    telescope-shape and declaration mismatches raise the index-mismatch error,
    and "is not an arity" is reserved for a head that never becomes a product,
    a let or a sort. *)
Definition ad_error_contains (needle : string) (r : string + string) : bool :=
  match r with
  | inl _ => false
  | inr msg =>
      match String.index 0 needle msg with
      | Some _ => true
      | None => false
      end
  end.

Definition ad_indices_mismatch :=
  "Inductive arity indices do not match the indices of the mutual declaration".
Definition ad_sort_mismatch :=
  "Inductive body sort does not match the sort of the inductive type".

Definition ad_mismatch_only (r : string + string) : bool :=
  ad_error_contains ad_indices_mismatch r
  && negb (ad_error_contains "is not an arity" r).

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

(** B3: a syntactic arity with the wrong index type: it must fail at the
    index-context comparison. *)
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

(** B5: an axiom of type [Type]: no body, so the reduction cannot progress. *)
Definition ad_B5 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_opaque %> None.
Print ad_B5.
Definition ad_B5_reason :
  ad_error_contains "ad_opaque is not an arity" ad_B5 = true := eq_refl.

(** B6: an alias of [Prop], so it needs reduction, while the declaration
    still claims one index.  The new checker must reject at telescope shape
    (index mismatch), not at a constructor and not as "not an arity". *)
Definition ad_B6 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_zero %> None.
Print ad_B6.
Definition ad_B6_reason :
  ad_mismatch_only ad_B6 = true := eq_refl.

(** B7: a bound, earlier constructorless inductive is not an arity.  Inference
    therefore succeeds before reduction, and refusal cannot be [UnboundInd]. *)
Definition ad_B7 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_anchor %> None.
Print ad_B7.
Definition ad_B7_reason :
  ad_error_contains "ad_anchor is not an arity" ad_B7 = true := eq_refl.

(** B8: the conversion-only counterexample, through the alias [ad_zero].
    The declaration fabricates one let index although the reduct is
    [Prop], so the refusing branch is the index-shape comparison
    (index mismatch, not "not an arity"). *)
Definition ad_B8 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_zero %> (Some ad_let_idx).
Print ad_B8.
Definition ad_B8_reason :
  ad_mismatch_only ad_B8 = true := eq_refl.

(** B9: the mirror.  [ad_letar] exposes and retains a let, while [ad_empty]'s
    kernel-produced index context is only [_ : nat].  The let is kept because
    the telescope walk runs with zeta off (no [tRel] head is involved here),
    so the post-change refusal is the index mismatch. *)
Definition ad_B9 := Eval vm_compute in
  ad_run_on ad_normal ad_empty_kn <% ad_letar %> None.
Print ad_B9.
Definition ad_B9_reason :
  ad_mismatch_only ad_B9 = true := eq_refl.

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
    let-bound variables stuck and then uses full zeta would accept this twin;
    the exact checker refuses it with the index mismatch. *)
Definition ad_B11 := Eval vm_compute in
  ad_run_on_prog ad_normal ad_rel_prog ad_rel_empty_kn <% ad_relar %> ad_relbad_idx.
Print ad_B11.
Definition ad_B11_reason :
  ad_mismatch_only ad_B11 = true := eq_refl.

(** B12: [ad_fbar] needs [whd_all] only because its head is
    [App (LetIn ...)].  Fabricating the exposed-let context of [ad_keepfind]
    checks that the fallback does not preserve that internal let: the exact
    checker refuses it with the index mismatch. *)
Definition ad_B12 := Eval vm_compute in
  ad_run_on_prog ad_normal ad_f_prog ad_fempty_kn <% ad_fbar %> ad_keepf_idx.
Print ad_B12.
Definition ad_B12_reason :
  ad_mismatch_only ad_B12 = true := eq_refl.

(** C1 through the driver: [ad_shind]'s own quoted program, unpatched.  The
    kernel stored [_ : true = true]; the sharing-free relation gives
    [_ : negb false = true], so the post-change refusal is the index mismatch,
    not "not an arity". *)
Definition ad_sh_witness := (fun (s : ad_shind eq_refl) => s).
MetaRocq Quote Recursively Definition ad_sh_prog := ad_sh_witness.
Definition ad_C1 := Eval vm_compute in
  infer_and_print_template_program (cf := default_checker_flags) (nor := ad_normal)
    ad_sh_prog Monomorphic_ctx.
Print ad_C1.
Definition ad_C1_reason : ad_mismatch_only ad_C1 = true := eq_refl.
