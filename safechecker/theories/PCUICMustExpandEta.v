(* Distributed under the terms of the MIT license. *)

(** * K1: the kernel's [MustExpand] for under-applied inductive and constructor heads

  Plan row K1 (`lanes/eta/plan.md` §3 K). The η checker's conversion
  ([PCUICSafeConversionEta]) compares two stuck heads with base [cmpb_term_napp]. For
  [tInd i u] against [tInd i u'] (and [tConstruct i k u] against [tConstruct i k u'])
  applied to fewer arguments than the cumulativity arity, base [global_variance_gen]
  returns [AllEqual], so base demands equal instances and refuses otherwise. The
  Rocq 9.2.0 kernel (tag V9.2.0) does not refuse there: [convert_inductives_gen] and
  [convert_constructors_gen] raise [MustExpand] when the argument count differs from
  the arity and the instances differ ([kernel/conversion.ml:190-193], [:224-226]); the
  caller then η-expands both heads to their full arity with [eta_expand_ind] /
  [eta_expand_constructor] ([:270-286], [it_mkLambda_or_LetIn] over [mind_arity_ctxt]
  or the constructor's context) and compares the two expansions with [eqappr] at the
  same [cv_pb] ([:634-638], [:656-660]). After β with the present arguments and ζ
  with the let-bound binders, that is a λ-vs-λ comparison, which compares the domains
  at [CONV] and the bodies at [CONV] ([:546-547]); the innermost body is the head at
  its full arity, so the instances are compared with the variance at [CONV].

  [must_expand_check] is that comparison as a pure boolean test, run where base
  [cmpb_term_napp] has failed:
  - (heads) both heads are [tInd i] (or both [tConstruct i k]) with the same [i] (and
    [k]), the two argument lists have the same length, and it is below the head's full
    arity [head_arity_gen] ([PCUICEtaFInst]: the count [global_variance_gen] tests,
    which is the kernel's [mind_nparams + mind_nrealargs] / [+ mind_consnrealargs],
    [:182-184], [:216-218]);
  - (1) the remaining binder types: the arity context ([ind_params ,,, ind_indices],
    or [ind_params ,,, cstr_args] with the block's inductives substituted as
    [type_of_constructor] does), instantiated at [u] and at [u'], ZETA-SUBSTITUTED
    ([smash_context], so a let-bound parameter's body is substituted into the later
    binder types: the required clause of the K1/F-8 measurement, plan §8k), with each
    side's present arguments substituted for the first binders, compared pairwise by
    the given syntactic comparison (the checker passes base [eqb_term], i.e.
    [eqb_term_upto_univ] at [Conv]; decidable, no recursive machine call);
  - (2) the instances at the FULL arity and at [Conv], whatever the ambient [leq]
    ([:638] → [:547]), by the given instance comparison (the checker passes
    [abstract_env_compare_global_instance]).
  The present arguments (3) are compared by the machine afterwards, as base does
  after a successful head comparison ([isconv_args]).

  ** Soundness: accept ⇒ E

  Only (heads), (2) and (3) are needed for soundness: the E specification ignores the
  η-expansion domains, and S4's [cumulSpecE_ind_underapplied_gen] /
  [cumulSpecE_construct_underapplied_gen] ([PCUICCumulativitySpecEtaClosure], proved)
  derive the pair from the full-arity [Conv] instance comparison and the arguments.
  [must_expand_check_sound] states it over [ws_cumul_pbE] (A1), the relation of the
  E checker's [conv_term]; [must_expand_view_cumulSpecE] states it over [≤sE[pb]].
  Clause (1) is there for kernel faithfulness (KF), not for soundness: the E
  specification derives [t5_inst]'s pair [I@{u}] vs [I@{v}] ([k1_t5_inner_E] below)
  while the kernel and this check refuse it ([k1_refuses_t5_inner]).

  ** KF notes (plan §6 risk rank 6, gate F-8)

  - K1 compares the binder types SYNTACTICALLY where the kernel runs its full
    conversion, so it refuses every pair whose instantiated binder types are
    convertible but not equal up to universes at [Conv] (for example, two present
    arguments that are convertible but not syntactically equal and occur in a later
    binder type). It is stricter than the kernel, never laxer, on those binders.
  - Let-bound parameters: the kernel's expansion carries them as [tLetIn]s, which its
    weak head normalisation ζ-reduces before reaching the next λ; K1 compares over the
    [smash_context]'d telescope, which is the same substitution, so a let body never
    appears as a raw de Bruijn variable. A difference that lies only in a let-bound
    parameter's body is compared only where that body is substituted (a dead let is
    never compared; the kernel ζ-drops it too, measured [a_diffw_k] in
    `lanes/eta/C3Falsifier-K1F8.md`).
  - Constructors: K1 substitutes the block's inductives at the side's instance into
    the argument types, as [type_of_constructor] does; a recursive argument's type
    then compares the two instances too. [INFERENCE, not measured: if the kernel's
    [mind_nf_lc] context keeps the block's inductives as de Bruijn references, the
    kernel compares those references and K1 is stricter there; never laxer.]
  - An argument count at or above the arity never reaches K1 (base compares at [pb]
    with the variance there); an over-applied head is ill-typed.

  ** The hypotheses are satisfiable

  [must_expand_check_sound] takes [ClosedBodies Σ] (any well-formed environment:
  [wf_ClosedBodies]; [wfE_ClosedBodies] for [wfE]), the soundness of the instance
  comparison on well-formed instances (the checker's [compare_global_instance_correct],
  [PCUICSafeConversion.v:3026]), [wf_universes] of the two heads, a closed context, and
  the arguments' [ws_cumul_pbE_terms]. All of them are met at once by the concrete
  instance at the end of this file: [k1_Σ] declares R3aProbe's
  [Cumulative Inductive I1@{*u} (A : Set) : Set] and the [t5_inst] family
  [Cumulative Inductive I@{*u} (A : Type@{u}) : Prop]; [k1_ClosedBodies];
  [k1_cmp_inst_sound]; [k1_check_I1] / [k1_check_c1] (the check accepts [I1@{u}] vs
  [I1@{v}] and [c1@{u}] vs [c1@{v}] at zero arguments with [u ≠ v]); and
  [must_expand_check_sound_inst] / [must_expand_check_sound_c1_inst], the soundness
  lemma applied to them. No E metatheory is assumed in this file: S4's lemmas and A1
  are proved. *)

From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICUnivSubst
     PCUICEquality PCUICOnFreeVars PCUICTyping PCUICWfUniverses
     PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICCumulativitySpecEtaClosure
     PCUICClosedBodies PCUICEtaFInst PCUICWellScopedCumulativityEta PCUICConversionEtaCongr.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec.

(** ** The heads *)

Definition must_expand_heads (t1 t2 : term) : option (global_reference * Instance.t * Instance.t) :=
  match t1, t2 with
  | tInd i u, tInd i' u' => if eqb i i' then Some (IndRef i, u, u') else None
  | tConstruct i k u, tConstruct i' k' u' =>
      if eqb i i' && Nat.eqb k k' then Some (ConstructRef i k, u, u') else None
  | _, _ => None
  end.

(** The two head shapes K1 accepts, as data. *)
Variant must_expand_view : term -> term -> global_reference -> Instance.t -> Instance.t -> Type :=
| must_expand_view_ind i u u' :
    must_expand_view (tInd i u) (tInd i u') (IndRef i) u u'
| must_expand_view_construct i k u u' :
    must_expand_view (tConstruct i k u) (tConstruct i k u') (ConstructRef i k) u u'.

Lemma must_expand_heads_view t1 t2 gr u u' :
  must_expand_heads t1 t2 = Some (gr, u, u') -> must_expand_view t1 t2 gr u u'.
Proof.
  rewrite /must_expand_heads.
  case: t1 => //; [move=> i1 u1|move=> i1 k1 u1]; case: t2 => //.
  - move=> i2 u2. case: (eqb_specT i1 i2) => [<-|_] //= [= <- <- <-]. constructor.
  - move=> i2 k2 u2. case: (eqb_specT i1 i2) => [<-|_] //=.
    case: (Nat.eqb_spec k1 k2) => [<-|_] //= [= <- <- <-]. constructor.
Qed.

(** The heads are closed terms: every lift and renaming fixes them. The checker's η
    view reads a head through [eta_rename], a composition of [lift 1 d]
    ([PCUICPositionEta], plan I7 rev 13), so it fixes them too. *)
Lemma must_expand_view_heads_closed t1 t2 gr u u' :
  must_expand_view t1 t2 gr u u' ->
  (forall P, on_free_vars P t1) × (forall P, on_free_vars P t2) ×
  (forall n k, lift n k t1 = t1) × (forall n k, lift n k t2 = t2).
Proof. case=> *; repeat split; intros; reflexivity. Qed.

(** ** The comparison *)

Section MustExpandCheck.

  Context (lookup : kername -> option global_decl).

  (** The full-arity context of a head at instance [u]: [ind_params ,,, ind_indices]
      for an inductive; [ind_params ,,, cstr_args] with the block's inductives
      substituted for a constructor (the context of [type_of_constructor]). *)
  Definition must_expand_context (gr : global_reference) (u : Instance.t) : option context :=
    match gr with
    | IndRef i =>
        match lookup_inductive_gen lookup i with
        | Some (mdecl, idecl) => Some (subst_instance u (ind_params mdecl ,,, ind_indices idecl))
        | None => None
        end
    | ConstructRef i k =>
        match lookup_constructor_gen lookup i k with
        | Some (mdecl, _, cdecl) =>
            Some (subst_context (inds (inductive_mind i) u (ind_bodies mdecl)) 0
                    (subst_instance u (ind_params mdecl ,,, cstr_args cdecl)))
        | None => None
        end
    | _ => None
    end.

  (** The types of the binders left after [args]: the context is first smashed (each
      let-bound binder's body substituted into the later binders, plan §8k's required
      clause), then the first [#|args|] assumption binders are instantiated with
      [args]. A binder type of the result lives in the ambient context extended by the
      remaining binders before it, so the two sides' lists compare pointwise. *)
  Definition must_expand_remaining (Δ : context) (args : list term) : list term :=
    let Δs := smash_context [] Δ in
    map decl_type (subst_context (List.rev args) 0 (firstn (#|Δs| - #|args|) Δs)).

  Context (eqb_tm : term -> term -> bool)
          (cmp_inst : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool).

  (** Clause (1): both arity contexts have [n] assumption binders, and the remaining
      binder types agree under [eqb_tm]. *)
  Definition must_expand_domains (gr : global_reference) (n : nat) (u u' : Instance.t)
    (args1 args2 : list term) : bool :=
    match must_expand_context gr u, must_expand_context gr u' with
    | Some Δ1, Some Δ2 =>
        [&& #|smash_context [] Δ1| =? n, #|smash_context [] Δ2| =? n &
            forallb2 eqb_tm (must_expand_remaining Δ1 args1) (must_expand_remaining Δ2 args2)]
    | _, _ => false
    end.

  (** K1. [args1]/[args2] are the two sides' present arguments. *)
  Definition must_expand_check (t1 : term) (args1 : list term) (t2 : term) (args2 : list term) : bool :=
    match must_expand_heads t1 t2 with
    | Some (gr, u, u') =>
        [&& #|args1| =? #|args2|, #|args1| <? head_arity_gen lookup gr,
            cmp_inst Conv gr (head_arity_gen lookup gr) u u' &
            must_expand_domains gr (head_arity_gen lookup gr) u u' args1 args2]
    | None => false
    end.

  Lemma must_expand_check_spec t1 args1 t2 args2 :
    must_expand_check t1 args1 t2 args2 ->
    ∑ gr u u', must_expand_view t1 t2 gr u u' ×
      [× #|args1| = #|args2|, #|args1| < head_arity_gen lookup gr &
         cmp_inst Conv gr (head_arity_gen lookup gr) u u'].
  Proof.
    rewrite /must_expand_check.
    destruct (must_expand_heads t1 t2) as [[[gr u] u']|] eqn:hv => //.
    move/and4P => [/Nat.eqb_spec hl /Nat.ltb_spec0 hlt hc _].
    exists gr, u, u'. split; [exact (must_expand_heads_view _ _ _ _ _ hv)|now split].
  Qed.

  Lemma must_expand_check_heads_closed t1 args1 t2 args2 :
    must_expand_check t1 args1 t2 args2 ->
    (forall n k, lift n k t1 = t1) × (forall n k, lift n k t2 = t2).
  Proof.
    move/must_expand_check_spec => [gr [u [u' [hv _]]]].
    destruct (must_expand_view_heads_closed _ _ _ _ _ hv) as (_ & _ & h1 & h2).
    now split.
  Qed.

End MustExpandCheck.

(** ** Soundness: K1's acceptance is in the E relation *)

Section MustExpandSound.

  Context {cf : checker_flags} (Σ : global_env_ext) {cb : ClosedBodies Σ}.

  (** Over the specification: S4's under-applied lemmas at the arity [n]. *)
  Lemma must_expand_view_cumulSpecE pb Γ t1 t2 gr u u' n args1 args2 :
    must_expand_view t1 t2 gr u u' ->
    #|args1| = #|args2| ->
    #|args1| <= n ->
    cmp_global_instance Σ (compare_universe Σ) Conv gr n u u' ->
    is_closed_context Γ ->
    forallb (is_open_term Γ) args1 ->
    forallb (is_open_term Γ) args2 ->
    All2 (fun a a' => Σ ;;; Γ ⊢ a ≤sE[Conv] a') args1 args2 ->
    Σ ;;; Γ ⊢ mkApps t1 args1 ≤sE[pb] mkApps t2 args2.
  Proof.
    case=> [i v v'|i k v v'] hlen hle hc hΓ ho1 ho2 hall;
      apply cumulE_Sym; apply cumulE_Sym.
    - exact (cumulSpecE_ind_underapplied_gen Σ i v v' n cb hc (n - #|args1|) Γ args1 args2
               hlen ltac:(lia) hΓ ho1 ho2 hall).
    - exact (cumulSpecE_construct_underapplied_gen Σ i k v v' n cb hc (n - #|args1|) Γ args1 args2
               hlen ltac:(lia) hΓ ho1 ho2 hall).
  Qed.

  (** Over [ws_cumul_pbE] (A1). *)
  Lemma must_expand_view_ws_cumul_pbE pb Γ t1 t2 gr u u' n args1 args2 :
    must_expand_view t1 t2 gr u u' ->
    #|args1| <= n ->
    cmp_global_instance Σ (compare_universe Σ) Conv gr n u u' ->
    is_closed_context Γ ->
    ws_cumul_pbE_terms Σ Γ args1 args2 ->
    ws_cumul_pbE pb Σ Γ (mkApps t1 args1) (mkApps t2 args2).
  Proof.
    intros hv hle hc hΓ h.
    have ho1 : forallb (is_open_term Γ) args1 by eapply WT_open_left; exact h.
    have ho2 : forallb (is_open_term Γ) args2 by eapply WT_open_right; exact h.
    destruct (must_expand_view_heads_closed _ _ _ _ _ hv) as (hc1 & hc2 & _ & _).
    apply into_ws_cumul_pbE_spec.
    - eapply must_expand_view_cumulSpecE; tea.
      + exact (All2_length h).
      + eapply All2_impl; [exact h|]. intros x y hxy. exact (ws_cumul_pbE_forget_spec hxy).
    - exact hΓ.
    - rewrite on_free_vars_mkApps hc1 /=. exact ho1.
    - rewrite on_free_vars_mkApps hc2 /=. exact ho2.
  Qed.

  Lemma must_expand_view_wf_instance t1 t2 gr u u' :
    must_expand_view t1 t2 gr u u' -> wf_universes Σ t1 -> wf_universes Σ t2 ->
    wf_instance Σ u × wf_instance Σ u'.
  Proof.
    case=> [i v v'|i k v v']; rewrite /wf_universes; cbn [on_universes];
      rewrite !wf_universeb_instance_forall => /wf_instanceP h1 /wf_instanceP h2; now split.
  Qed.

  (** The lemma the checker's K1 obligation applies. [hcmp] is what
      [compare_global_instance_correct] gives for [abstract_env_compare_global_instance];
      [wf_universes] of the heads comes from their well-typedness, as for base's
      [cmpb_term_correct]. *)
  Lemma must_expand_check_sound (lookup : kername -> option global_decl)
    (eqb_tm : term -> term -> bool)
    (cmp_inst : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
    pb Γ t1 args1 t2 args2 :
    (forall gr n u u', wf_instance Σ u -> wf_instance Σ u' ->
       cmp_inst Conv gr n u u' -> cmp_global_instance Σ (compare_universe Σ) Conv gr n u u') ->
    must_expand_check lookup eqb_tm cmp_inst t1 args1 t2 args2 ->
    wf_universes Σ t1 -> wf_universes Σ t2 ->
    is_closed_context Γ ->
    ws_cumul_pbE_terms Σ Γ args1 args2 ->
    ws_cumul_pbE pb Σ Γ (mkApps t1 args1) (mkApps t2 args2).
  Proof.
    intros hcmp hchk hw1 hw2 hΓ h.
    destruct (must_expand_check_spec lookup eqb_tm cmp_inst t1 args1 t2 args2 hchk)
      as (gr & u & u' & hv & [hlen hlt hc]).
    destruct (must_expand_view_wf_instance _ _ _ _ _ hv hw1 hw2) as [hu hu'].
    eapply must_expand_view_ws_cumul_pbE;
      [exact hv| |exact (hcmp _ _ _ _ hu hu' hc)|exact hΓ|exact h].
    lia.
  Qed.

  (** The same over the specification. *)
  Lemma must_expand_check_sound_spec (lookup : kername -> option global_decl)
    (eqb_tm : term -> term -> bool)
    (cmp_inst : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool)
    pb Γ t1 args1 t2 args2 :
    (forall gr n u u', wf_instance Σ u -> wf_instance Σ u' ->
       cmp_inst Conv gr n u u' -> cmp_global_instance Σ (compare_universe Σ) Conv gr n u u') ->
    must_expand_check lookup eqb_tm cmp_inst t1 args1 t2 args2 ->
    wf_universes Σ t1 -> wf_universes Σ t2 ->
    is_closed_context Γ ->
    ws_cumul_pbE_terms Σ Γ args1 args2 ->
    Σ ;;; Γ ⊢ mkApps t1 args1 ≤sE[pb] mkApps t2 args2.
  Proof.
    intros hcmp hchk hw1 hw2 hΓ h.
    exact (ws_cumul_pbE_forget_spec (must_expand_check_sound lookup eqb_tm cmp_inst pb Γ
             t1 args1 t2 args2 hcmp hchk hw1 hw2 hΓ h)).
  Qed.

End MustExpandSound.

(** A boolean instance comparison whose universe test implies [compare_universe] is
    sound for [cmp_global_instance]. It discharges [must_expand_check_sound]'s [hcmp]
    for any concrete comparator. *)
Lemma compare_global_instance_sound {cf : checker_flags} (Σ : global_env_ext)
  (cmpu : conv_pb -> Universe.t -> Universe.t -> bool) pb gr n ui ui' :
  (forall pb' x y, cmpu pb' x y -> compare_universe Σ pb' x y) ->
  compare_global_instance (lookup_env Σ) cmpu pb gr n ui ui' ->
  cmp_global_instance Σ (compare_universe Σ) pb gr n ui ui'.
Proof.
  intros himp h.
  have r := reflect_cmp_global_instance' (lookup_env Σ) xpredT cmpu
              (fun pb x y => is_true (cmpu pb x y)) pb gr n ui ui'
              (fun x y _ _ => idP) (fun x y _ _ => idP) (forallb_true _) (forallb_true _).
  move/r: h => h.
  eapply (cmp_global_instance_impl_same_napp Σ (fun pb x y => is_true (cmpu pb x y))
            (compare_universe Σ) pb pb gr n); [| |exact h].
  all: intros x y; apply himp.
Qed.

(** * Satisfying instances

  [k1_env] declares R3aProbe's [Cumulative Inductive I1@{*u} (A : Set) : Set := c1 : I1 A]
  (`/mnt/frac/work/eta/R3aProbe/in/r3a_kernel.v:10`) and the plan's [t5_inst] family
  [Cumulative Inductive I@{*u} (A : Type@{u}) : Prop := ci] (plan §0.3). [k1_Σ] extends
  it with two universe variables [u], [v] and no constraint, as [@{u v|}]. The
  environment satisfies [ClosedBodies] ([k1_ClosedBodies]), the only environment premise
  of the soundness lemmas; it is not claimed [wf]. The comparators are syntactic:
  universes and sorts by [eqb], instances by [compare_global_instance] over them. *)

#[local] Existing Instance default_checker_flags.

Definition k1_kn : kername := (MPfile ["K1Inst"], "I1").
Definition k1_ind : inductive := {| inductive_mind := k1_kn; inductive_ind := 0 |}.
Definition k1_na : aname := mkBindAnn (nNamed "A") Relevant.
Definition k1_set : term := tSort Sort.type0.

Definition k1_cdecl : constructor_body :=
  {| cstr_name := "c1"; cstr_args := []; cstr_indices := [];
     cstr_type := tProd k1_na k1_set (tApp (tRel 1) (tRel 0)); cstr_arity := 0 |}.

Definition k1_idecl : one_inductive_body :=
  {| ind_name := "I1"; ind_indices := []; ind_sort := Sort.type0;
     ind_type := tProd k1_na k1_set k1_set; ind_kelim := IntoAny; ind_ctors := [k1_cdecl];
     ind_projs := []; ind_relevance := Relevant |}.

Definition k1_mdecl : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 1; ind_params := [vass k1_na k1_set];
     ind_bodies := [k1_idecl];
     ind_universes := Polymorphic_ctx ([nNamed "u"], ConstraintSet.empty);
     ind_variance := Some [Variance.Irrelevant] |}.

(** [I@{*u} (A : Type@{u}) : Prop]: the parameter's type carries the instance. *)
Definition k1_kn2 : kername := (MPfile ["K1Inst"], "I").
Definition k1_ind2 : inductive := {| inductive_mind := k1_kn2; inductive_ind := 0 |}.
Definition k1_typeu : term := tSort (sType (Universe.make' (Level.lvar 0))).

Definition k1_cdecl2 : constructor_body :=
  {| cstr_name := "ci"; cstr_args := []; cstr_indices := [];
     cstr_type := tProd k1_na k1_typeu (tApp (tRel 1) (tRel 0)); cstr_arity := 0 |}.

Definition k1_idecl2 : one_inductive_body :=
  {| ind_name := "I"; ind_indices := []; ind_sort := sProp;
     ind_type := tProd k1_na k1_typeu (tSort sProp); ind_kelim := IntoAny; ind_ctors := [k1_cdecl2];
     ind_projs := []; ind_relevance := Relevant |}.

Definition k1_mdecl2 : mutual_inductive_body :=
  {| ind_finite := Finite; ind_npars := 1; ind_params := [vass k1_na k1_typeu];
     ind_bodies := [k1_idecl2];
     ind_universes := Polymorphic_ctx ([nNamed "u"], ConstraintSet.empty);
     ind_variance := Some [Variance.Irrelevant] |}.

Definition k1_env : global_env :=
  {| universes := ContextSet.empty;
     declarations := [(k1_kn2, InductiveDecl k1_mdecl2); (k1_kn, InductiveDecl k1_mdecl)];
     retroknowledge := Retroknowledge.empty |}.

Definition k1_Σ : global_env_ext :=
  (k1_env, Polymorphic_ctx ([nNamed "u"; nNamed "v"], ConstraintSet.empty)).

Definition k1_u : Instance.t := [Level.lvar 0].
Definition k1_v : Instance.t := [Level.lvar 1].

Lemma k1_ClosedBodies : ClosedBodies k1_env.
Proof.
  apply Build_ClosedBodies.
  - move=> cst decl body. rewrite /declared_constant /=.
    move=> [h|[h|[]]]; discriminate h.
  - cbn. constructor.
    + move=> [h|[]]. discriminate h.
    + constructor; [intros []|constructor].
Qed.

Definition k1_cmpu : conv_pb -> Universe.t -> Universe.t -> bool := fun _ x y => eqb x y.
Definition k1_cmps : conv_pb -> sort -> sort -> bool := fun _ x y => eqb x y.
Definition k1_cmp_inst : conv_pb -> global_reference -> nat -> Instance.t -> Instance.t -> bool :=
  compare_global_instance (lookup_env k1_env) k1_cmpu.
Definition k1_eqb_tm : term -> term -> bool :=
  eqb_term_upto_univ k1_cmpu k1_cmps k1_cmp_inst Conv.

(** [must_expand_check_sound]'s [hcmp], for the concrete comparator. *)
Lemma k1_cmp_inst_sound gr n u u' :
  wf_instance k1_Σ u -> wf_instance k1_Σ u' ->
  k1_cmp_inst Conv gr n u u' -> cmp_global_instance k1_Σ (compare_universe k1_Σ) Conv gr n u u'.
Proof.
  intros _ _ h.
  eapply (compare_global_instance_sound k1_Σ k1_cmpu); [|exact h].
  intros pb x y. rewrite /k1_cmpu. case: (eqb_spec x y) => [-> _|_ //]. reflexivity.
Qed.

(** K1 accepts [I1@{u}] vs [I1@{v}] at zero arguments ([r3a_ind0_k], kernel ACCEPT):
    the binder type [Set] agrees, and the variance is irrelevant. *)
Lemma k1_check_I1 :
  must_expand_check (lookup_env k1_env) k1_eqb_tm k1_cmp_inst (tInd k1_ind k1_u) [] (tInd k1_ind k1_v) [].
Proof. vm_compute. reflexivity. Qed.

(** K1 accepts [c1@{u}] vs [c1@{v}] at zero arguments ([r3a_cstr0_k], kernel ACCEPT). *)
Lemma k1_check_c1 :
  must_expand_check (lookup_env k1_env) k1_eqb_tm k1_cmp_inst
    (tConstruct k1_ind 0 k1_u) [] (tConstruct k1_ind 0 k1_v) [].
Proof. vm_compute. reflexivity. Qed.

Lemma k1_wf_universes_ind1 u : u = k1_u \/ u = k1_v -> wf_universes k1_Σ (tInd k1_ind u).
Proof. by move=> [->|->]; vm_compute. Qed.

Lemma k1_wf_universes_c1 u : u = k1_u \/ u = k1_v -> wf_universes k1_Σ (tConstruct k1_ind 0 u).
Proof. by move=> [->|->]; vm_compute. Qed.

Lemma k1_wf_instance u : u = k1_u \/ u = k1_v -> wf_instance k1_Σ u.
Proof. move=> h. apply/wf_instanceP. by case: h => ->; vm_compute. Qed.

(** [must_expand_check_sound] with every premise met. *)
Lemma must_expand_check_sound_inst :
  ws_cumul_pbE Cumul k1_Σ [] (mkApps (tInd k1_ind k1_u) []) (mkApps (tInd k1_ind k1_v) []).
Proof.
  exact (must_expand_check_sound k1_Σ (cb := k1_ClosedBodies) (lookup_env k1_env) k1_eqb_tm
           k1_cmp_inst Cumul [] (tInd k1_ind k1_u) [] (tInd k1_ind k1_v) []
           k1_cmp_inst_sound k1_check_I1 (k1_wf_universes_ind1 _ (or_introl eq_refl))
           (k1_wf_universes_ind1 _ (or_intror eq_refl)) eq_refl (All2_nil)).
Qed.

Lemma must_expand_check_sound_c1_inst :
  ws_cumul_pbE Conv k1_Σ [] (mkApps (tConstruct k1_ind 0 k1_u) []) (mkApps (tConstruct k1_ind 0 k1_v) []).
Proof.
  exact (must_expand_check_sound k1_Σ (cb := k1_ClosedBodies) (lookup_env k1_env) k1_eqb_tm
           k1_cmp_inst Conv [] (tConstruct k1_ind 0 k1_u) [] (tConstruct k1_ind 0 k1_v) []
           k1_cmp_inst_sound k1_check_c1 (k1_wf_universes_c1 _ (or_introl eq_refl))
           (k1_wf_universes_c1 _ (or_intror eq_refl)) eq_refl (All2_nil)).
Qed.

(** Clause (1) refuses [t5_inst]'s inner pair [I@{u}] vs [I@{v}] (kernel REFUSE,
    [t5_inst_k]/[t5_fixed], `lanes/eta/out/kernel_verdicts{,2}.v-up920.out`): the
    instances pass clause (2) ([k1_t5_inner_instances]), the binder types [Type@{u}] and
    [Type@{v}] do not. *)
Lemma k1_t5_inner_instances : k1_cmp_inst Conv (IndRef k1_ind2) 1 k1_u k1_v.
Proof. vm_compute. reflexivity. Qed.

Lemma k1_refuses_t5_inner :
  must_expand_check (lookup_env k1_env) k1_eqb_tm k1_cmp_inst
    (tInd k1_ind2 k1_u) [] (tInd k1_ind2 k1_v) [] = false.
Proof. vm_compute. reflexivity. Qed.

(** The E relation itself relates that pair (plan §0.3: "E: derivable"), so clause (1)
    is a kernel-faithfulness restriction, not a soundness one. *)
Lemma k1_t5_inner_E :
  ws_cumul_pbE Cumul k1_Σ [] (mkApps (tInd k1_ind2 k1_u) []) (mkApps (tInd k1_ind2 k1_v) []).
Proof.
  eapply (must_expand_view_ws_cumul_pbE k1_Σ (cb := k1_ClosedBodies) Cumul [] _ _ _ _ _ 1);
    [exact (must_expand_view_ind k1_ind2 k1_u k1_v)|cbn; lia| |reflexivity|constructor].
  exact (k1_cmp_inst_sound _ _ _ _ (k1_wf_instance _ (or_introl eq_refl))
           (k1_wf_instance _ (or_intror eq_refl)) k1_t5_inner_instances).
Qed.
