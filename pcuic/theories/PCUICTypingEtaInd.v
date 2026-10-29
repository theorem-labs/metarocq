(* Distributed under the terms of the MIT license. *)
(** * The induction principle of [typingE]

  A copy of base [PCUICTyping]'s size and induction machinery over [typingE],
  [wf_localE], [wfE] and [cumulSpecE0]: [typingE_size], [typingE_wf_local],
  [env_propE], [typingE_ind_env_app_size], [typingE_ind_env]. The proofs are
  base's; only the relation names change. Generic pieces ([All_map_size],
  [globenv_size], [All_local_env_size], ...) are base's and are reused. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive PCUICCases
     PCUICOnFreeVars PCUICEquality PCUICTyping PCUICCumulativitySpec PCUICCumulativitySpecEta PCUICTypingEta.

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation.
From Equations Require Import Equations.
Set Equations With UIP.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Definition tybranchesE {cf} Σ Γ ci mdecl idecl p ps ptm n ctors brs :=
  All2i
  (fun (i : nat) (cdecl : constructor_body) (br : branch term) =>
   (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) *
   (let brctxty := case_branch_type ci mdecl idecl p br ptm i cdecl in
    wf_localE Σ (Γ,,, brctxty.1)
    × Σ;;; Γ,,, brctxty.1 |-E bbody br : brctxty.2
      × Σ;;; Γ,,, brctxty.1 |-E brctxty.2 : tSort ps)) n ctors brs.

Definition branchesE_size {cf} {Σ Γ ci mdecl idecl p ps ptm brs}
   (typing_size : forall Σ Γ t T, Σ ;;; Γ |-E t : T -> size)
  {n ctors}
  (a : tybranchesE Σ Γ ci mdecl idecl p ps ptm n ctors brs) : size :=
  (all2i_size _ (fun i x y p =>
    Nat.max
      (All_local_env_size (typing_size _) _ p.2.1)
      (Nat.max (typing_size _ _ _ _ p.2.2.1) (typing_size _ _ _ _ p.2.2.2))) a).

Definition typingE_size `{cf : checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |-E t : T) : size.
Proof.
  revert Σ Γ t T d.
  fix typingE_size 5.
  destruct 1.
  10: destruct c0, c1.
  all: repeat match goal with
           | H : typingE _ _ _ _ |- _ => apply typingE_size in H
    end;
    match goal with
    | H : All2i _ _ _ _ |- _ => idtac
    | H : All_local_env _ _ |- _ => idtac
    | H : All _ _ |- _ => idtac
    | H : _ + _ |- _ => idtac
    | H : lift_typing0 _ _ |- _ => idtac
    | H1 : size, H2 : size, H3 : size |- _ => exact (S (Nat.max H1 (Nat.max H2 H3)))
    | H1 : size, H2 : size |- _ => exact (S (Nat.max H1 H2))
    | H1 : size |- _  => exact (S H1)
    | _ => exact 1
    end.
  - exact (S (All_local_env_size (typingE_size _) _ a)).
  - exact (S (All_local_env_size (typingE_size _) _ a)).
  - exact (S (Nat.max d (lift_typing_size (typingE_size _ _) _ l))).
  - exact (S (Nat.max d (lift_typing_size (typingE_size _ _) _ l))).
  - exact (S (Nat.max d (lift_typing_size (typingE_size _ _) _ l))).
  - exact (S (S (All_local_env_size (typingE_size _) _ a))).
  - exact (S (S (All_local_env_size (typingE_size _) _ a))).
  - exact (S (S (All_local_env_size (typingE_size _) _ a))).
  - exact (S (Nat.max (All_local_env_size (typingE_size _) _ wf_pctx)
      (Nat.max (ctx_inst_size _ typingE_size ind_inst)
        (Nat.max d2 (Nat.max d3 (branchesE_size typingE_size brs_ty)))))).
  - exact (S (Nat.max
      (Nat.max (All_local_env_size (typingE_size _) _ a) (all_size _ (fun x p => on_def_type_size (typingE_size Σ) _ _ p) a0))
      (all_size (on_def_body (lift_typing typingE _) _ _) (fun x p => on_def_body_size (typingE_size Σ) _ _ _ p) a1))).
  - exact (S (Nat.max
      (Nat.max (All_local_env_size (typingE_size _) _ a) (all_size _ (fun x p => on_def_type_size (typingE_size Σ) _ _ p) a0))
      (all_size (on_def_body (lift_typing typingE _) _ _) (fun x p => on_def_body_size (typingE_size Σ) _ _ _ p) a1))).
  - exact (S (Nat.max (All_local_env_size (typingE_size _) _ a) (primitive_typing_hyps_size typingE typingE_size _ _ _ p1))).
Defined.

Lemma typingE_size_pos `{checker_flags} {Σ Γ t T} (d : Σ ;;; Γ |-E t : T) : typingE_size d > 0.
Proof.
  induction d; try destruct c0, c1; simpl; try lia.
Qed.

Lemma typingE_wf_local `{cf : checker_flags} {Σ} {Γ t T} :
  Σ ;;; Γ |-E t : T -> wf_localE Σ Γ.
Proof.
  revert Σ Γ t T.
  fix f 5.
  destruct 1; eauto.
  all: exact (f _ _ _ _ l.2.π2.1).
Defined.

Lemma lift_typingE_wf_local `{cf : checker_flags} {Σ} {Γ j} :
  lift_typing typingE Σ Γ j -> wf_localE Σ Γ.
Proof.
  destruct 1 as (_ & s & Hs & _).
  now apply typingE_wf_local in Hs.
Defined.

(** The E twins of base's [wf_local] registrations ([PCUICTyping.v:631-644]): base's
    [PCUICTypingDef.typing] branch has no E counterpart, since [typingE] is the
    inductive itself. *)
#[global]
Hint Extern 4 (wf_localE _ ?Γ) =>
  match goal with
  | [ H : typingE _ _ _ _ |- _ ] => exact (typingE_wf_local H)
  | [ H : lift_typing0 (typingE _ _) _ |- _ ] => exact (lift_typingE_wf_local H)
  end : pcuic.

#[global]
Hint Resolve typingE_wf_local : wf.

#[global]
Hint Resolve lift_typingE_wf_local : wf.

Definition env_propE `{checker_flags} (P : forall Σ Γ t T, Type) (Pj : forall Σ Γ j, Type) (PΓ : forall Σ Γ, Type) :=
  forall Σ (wfΣ : wfE Σ.1) Γ t T (ty : Σ ;;; Γ |-E t : T),
  on_global_env cumulSpecE0 Pj Σ.1 * (PΓ Σ Γ * P Σ Γ t T).

Lemma env_propE_typing `{checker_flags} {P Pj PΓ} : env_propE P Pj PΓ ->
  forall Σ (wfΣ : wfE Σ.1) (Γ : context) (t T : term),
    Σ ;;; Γ |-E t : T -> P Σ Γ t T.
Proof. intros. now apply X. Qed.

Lemma typeE_Prop_wf `{checker_flags} Σ Γ : wf_localE Σ Γ -> Σ ;;; Γ |-E tSort sProp : tSort Sort.type1.
Proof.
  repeat constructor; auto.
Defined.

Lemma env_propE_wf_local `{checker_flags} {P Pj PΓ} : env_propE P Pj PΓ ->
  forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ), PΓ Σ Γ.
Proof. intros.
  pose (typeE_Prop_wf _ _ wfΓ).
  now destruct (X _ wfΣ _ _ _ t) as [? [? ?]].
Qed.

Lemma typeE_Prop `{checker_flags} Σ : Σ ;;; [] |-E tSort sProp : tSort Sort.type1.
  repeat constructor.
Defined.

Lemma env_propE_sigma `{checker_flags} {P Pj PΓ} : env_propE P Pj PΓ ->
  forall (Σ : global_env) (wfΣ : wfE Σ), on_global_env cumulSpecE0 Pj Σ.
Proof.
  intros. red in X. eapply (X (empty_ext Σ)).
  apply wfΣ.
  apply typeE_Prop.
Defined.

Lemma typingE_wf_local_size `{cf : checker_flags} {Σ} {Γ t T}
      (d :Σ ;;; Γ |-E t : T) :
  All_local_env_size (@typingE_size _ _) _ (typingE_wf_local d) < typingE_size d.
Proof.
  revert Σ Γ t T d. fix f 5.
  induction d; try destruct c0, c1; simpl;
  change (fun Γ t T (Hty : Σ;;; Γ |-E t : T) => typingE_size Hty) with (@typingE_size cf Σ); try lia.
  all: pose proof (f _ _ _ _ l.2.π2.1); unfold lift_sorting_size; cbn in *; try lia.
Qed.

Lemma wf_localE_inv `{checker_flags} {Σ Γ'} (w : wf_localE Σ Γ') :
  forall d Γ,
    Γ' = d :: Γ ->
    ∑ (w' : wf_localE Σ Γ) u,
      { ty : lift_typing1 (typingE Σ) Γ (j_decl_s d (Some u)) |
            All_local_env_size (@typingE_size _ Σ) _ w' <
            All_local_env_size (@typingE_size _ _) _ w /\
            lift_typing_size (@typingE_size _ _ _) _ ty <= All_local_env_size (@typingE_size _ _) _ w }.
Proof.
  intros d Γ ->.
  depelim w; cbn.
  all: exists w, l.2.π1, (lift_sorting_extract l).
  all: pose proof (typingE_size_pos l.2.π2.1).
  2: pose proof (typingE_size_pos l.1).
  all: simpl in *.
  all: simpl; split.
  all: try lia.
Qed.



(** *** An induction principle ensuring the Σ declarations enjoy the same properties.
    Also theads the well-formedness of the local context and the induction principle for it,
    and gives the right induction hypothesis on typingE judgments in application spines,
    fix and cofix blocks. This general version allows to get the induction hypothesis on
    any subderivation of the head of applications.

    The specialized version `typingE_ind_env` below is the one used in general, with
    no special case for applications.
 *)

Lemma typingE_ind_env_app_size `{cf : checker_flags} :
 forall (P : global_env_ext -> context -> term -> term -> Type)
        (Pj : global_env_ext -> context -> judgment -> Type)
        (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
        (PΓ : global_env_ext -> context -> Type),

   (forall Σ (wfΣ : wfE Σ) (Γ : context) (* (wfΓ : wf_localE Σ Γ) *) j,
        lift_typing_conj (typingE Σ) (P Σ) Γ j -> Pj Σ Γ j) ->

   (forall Σ (wfΣ : wfE Σ.1)  (Γ : context) (wfΓ : wf_localE Σ Γ),
        All_local_env_over (typingE Σ) (Pdecl Σ) Γ wfΓ -> All_local_env (Pj Σ) Γ -> PΓ Σ Γ) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (n : nat) decl,
       nth_error Γ n = Some decl ->
       PΓ Σ Γ ->
       P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (u : sort),
       PΓ Σ Γ ->
       wf_sort Σ u ->
       P Σ Γ (tSort u) (tSort (Sort.super u))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b : term) (s1 s2 : sort),
       PΓ Σ Γ ->
       lift_typing typingE Σ Γ (j_vass_s na t s1) ->
       Pj Σ Γ (j_vass_s na t s1) ->
       Σ ;;; Γ,, vass na t |-E b : tSort s2 ->
       P Σ (Γ,, vass na t) b (tSort s2) -> P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b bty : term),
       PΓ Σ Γ ->
       lift_typing typingE Σ Γ (j_vass na t) ->
       Pj Σ Γ (j_vass na t) ->
       Σ ;;; Γ,, vass na t |-E b : bty -> P Σ (Γ,, vass na t) b bty -> P Σ Γ (tLambda na t b) (tProd na t bty)) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (b b_ty b' b'_ty : term),
       PΓ Σ Γ ->
       lift_typing typingE Σ Γ (j_vdef na b b_ty) ->
       Pj Σ Γ (j_vdef na b b_ty) ->
       Σ ;;; Γ,, vdef na b b_ty |-E b' : b'_ty ->
       P Σ (Γ,, vdef na b b_ty) b' b'_ty -> P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t : term) na A B u s,
       PΓ Σ Γ ->
       forall (Hp : Σ ;;; Γ |-E tProd na A B : tSort s), P Σ Γ (tProd na A B) (tSort s) ->
       forall (Ht : Σ ;;; Γ |-E t : tProd na A B), P Σ Γ t (tProd na A B) ->

       (* Give a stronger induction hypothesis allowing to crawl under applications *)
       (forall t' T' (Ht' : Σ ;;; Γ |-E t' : T'), typingE_size Ht' <= max (typingE_size Ht) (typingE_size Hp) -> P Σ Γ t' T') ->

       Σ ;;; Γ |-E u : A -> P Σ Γ u A ->
       P Σ Γ (tApp t u) (B{0 := u})) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) cst u (decl : constant_body),
       on_global_env cumulSpecE0 Pj Σ.1 ->
       PΓ Σ Γ ->
       declared_constant Σ.1 cst decl ->
       consistent_instance_ext Σ decl.(cst_universes) u ->
       P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) u
         mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
       on_global_env cumulSpecE0 Pj Σ.1 ->
       PΓ Σ Γ ->
       consistent_instance_ext Σ mdecl.(ind_universes) u ->
       P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) (i : nat) u
           mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
       on_global_env cumulSpecE0 Pj Σ.1 ->
       PΓ Σ Γ ->
       consistent_instance_ext Σ mdecl.(ind_universes) u ->
       P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

     (forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (wfΓ : wf_localE Σ Γ),
      forall (ci : case_info) p c brs indices ps mdecl idecl
        (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        mdecl.(ind_npars) = ci.(ci_npar) ->
        eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
        let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
        wf_predicate mdecl idecl p ->
        consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
        forall pret : Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps,
        P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
        wf_localE Σ (Γ ,,, predctx) ->
        PΓ Σ (Γ ,,, predctx) ->
        is_allowed_elimination Σ idecl.(ind_kelim) ps ->
        isSortRel ps ci.(ci_relevance) ->
        ctx_inst (Prop_conj typingE P Σ) Γ (p.(pparams) ++ indices)
          (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
        Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
        P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
        (isCoFinite mdecl.(ind_finite) ==> on_free_vars (strengthenP 0 1 xpredT) p.(preturn)) = true ->
        let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
        wf_branches idecl brs ->
        All2i (fun i cdecl br =>
          (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
          let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
          (PΓ Σ (Γ ,,, brctxty.1) ×
          (Prop_conj typingE P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2) ×
          (Prop_conj typingE P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps)))) 0 idecl.(ind_ctors) brs ->
        P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : projection) (c : term) u
         mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
       on_global_env cumulSpecE0 Pj Σ.1 -> PΓ Σ Γ ->
       Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
       P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
       #|args| = ind_npars mdecl ->
       P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
       let types := fix_context mfix in
       fix_guard Σ Γ mfix ->
       nth_error mfix n = Some decl ->
       PΓ Σ (Γ ,,, types) ->
       All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
       All (on_def_type (Pj Σ) Γ) mfix ->
       All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
       All (on_def_body (Pj Σ) types Γ) mfix ->
       wf_fixpointE Σ Γ mfix ->
       P Σ Γ (tFix mfix n) decl.(dtype)) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
       let types := fix_context mfix in
       cofix_guard Σ Γ mfix ->
       nth_error mfix n = Some decl ->
       PΓ Σ (Γ ,,, types) ->
       All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
       All (on_def_type (Pj Σ) Γ) mfix ->
       All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
       All (on_def_body (Pj Σ) types Γ) mfix ->
       wf_cofixpointE Σ Γ mfix ->
       P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

  (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : prim_val term) prim_ty cdecl,
      PΓ Σ Γ ->
      primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
      declared_constant Σ prim_ty cdecl ->
      primitive_invariants (prim_val_tag p) cdecl ->
      primitive_typing_hyps (typingE Σ) Σ Γ p ->
      primitive_typing_hyps (P Σ) Σ Γ p ->
      P Σ Γ (tPrim p) (prim_type p prim_ty)) ->

   (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t A B : term) s,
       PΓ Σ Γ ->
       Σ ;;; Γ |-E t : A ->
       P Σ Γ t A ->
       Σ ;;; Γ |-E B : tSort s ->
       P Σ Γ B (tSort s) ->
       cumulSpecE Σ Γ A B ->
       P Σ Γ t B) ->

      env_propE P Pj PΓ.
Proof.
  intros P Pj Pdecl PΓ.
  intros Xj XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  (* NOTE (Danil): while porting to 8.9, I had to split original "pose" into 2 pieces,
    otherwise it takes forever to execure the "pose", for some reason *)
  pose proof (@Fix_F { Σ & { wfΣ : wfE Σ.1 & { Γ & { t & { T & Σ ;;; Γ |-E t : T }}}}}) as p0.
  specialize (p0 (PCUICUtils.dlexprod (precompose lt (fun Σ => globenv_size (fst Σ)))
                            (fun Σ => precompose lt (fun x => typingE_size x.π2.π2.π2.π2)))) as p.
  set (foo := (Σ; wfΣ; Γ; t; _; H) : { Σ & { wfΣ : wfE Σ.1 & { Γ & { t & { T & Σ ;;; Γ |-E t : T }}}}}).
  change Σ with foo.π1.
  change Γ with foo.π2.π2.π1.
  change t with foo.π2.π2.π2.π1.
  change T with foo.π2.π2.π2.π2.π1.
  change H with foo.π2.π2.π2.π2.π2.
  revert foo.
  match goal with
    |- let foo := _ in @?P foo => specialize (p (fun x => P x))
  end.
  forward p; [ | apply p; apply PCUICUtils.wf_dlexprod; intros; apply wf_precompose; apply lt_wf].
  clear p.
  clear Σ wfΣ Γ t T H.
  intros (Σ & wfΣ & Γ & t & t0 & H). simpl.
  intros IH. simpl in IH.
  split.
  - clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13.
    destruct Σ as [Σ φ].
    red. cbn. do 2 red in wfΣ. cbn in wfΣ.
    destruct Σ as [univs Σ]; cbn in *.
    set (Σg:= {| universes := univs; declarations := Σ |}) in *.
    destruct wfΣ as [ongu [wfr o]]; split => //; split => //.
    unfold Σg in o |- *; cbn in o.
    cbn in o |- *.
    destruct o. { constructor. }
    rename o0 into Xg.
    set (wfΣ := (ongu, (wfr, o)) : on_global_env cumulSpecE0 (lift_typing typingE) {| universes := univs; declarations := Σ |}).
    set (Σ':= {| universes := univs; declarations := Σ |}) in *.
    destruct Xg as [hfresh udecl honu Xg].
    constructor; auto; try constructor; auto.
    * unshelve eset (IH' := IH ((Σ', udecl); (wfΣ; []; (tSort sProp); _; _))).
      shelve. simpl. apply typeE_Prop.
      forward IH'. constructor 1; cbn. lia.
      apply IH'; auto.

    * simpl. simpl in *.
      destruct d.
      + apply Xj; tas.
        apply lift_typing_impl with (1 := Xg); intros ?? HT. split; tas.
        specialize (IH ((Σ', udecl); wfΣ; _; _; _; HT)).
        forward IH; [constructor 1; simpl; subst Σ' Σg; cbn; lia|].
        apply IH.
      + red in Xg.
        destruct Xg as [onI onP onNP onV]; constructor; eauto.
        { unshelve eset (IH' := fun p => IH ((Σ', udecl); wfΣ; p) _).
          constructor. cbn; subst Σ' Σg; lia. clearbody IH'. cbn in IH'.
          clear IH; rename IH' into IH.
          eapply Alli_impl; eauto. cbn in IH. clear onI onP onNP onV. intros n x Xg.
          refine {| ind_arity_red := Xg.(ind_arity_red);
                    ind_cunivs := Xg.(ind_cunivs) |}.
          - apply onArity in Xg. apply Xj; tas.
            apply lift_typing_impl with (1 := Xg); intros ?? HT. split; tas.
            apply (IH (_; _; _; HT)).
          - apply onArityRed in Xg. apply Xj; tas.
            apply lift_typing_impl with (1 := Xg); intros ?? HT. split; tas.
            apply (IH (_; _; _; HT)).
          - pose proof Xg.(onConstructors) as Xg'.
            eapply All2_impl; eauto. intros.
            destruct X as [cass tyeq onctyp oncargs oncind].
            unshelve econstructor; eauto.
            { apply Xj; tas.
              apply lift_typing_impl with (1 := onctyp); intros ?? HT. split; tas.
              apply (IH (_; _; _; HT)). }
            { apply sorts_local_ctx_impl with (1 := oncargs); intros Γ' j Hj. apply Xj; tas.
              apply lift_typing_impl with (1 := Hj); intros ?? HT. split; tas.
              apply (IH (_; _; _; HT)). }
            { eapply ctx_inst_impl with (1 := oncind); intros ?? Hj. apply Xj; tas.
              apply lift_typing_impl with (1 := Hj); intros ?? Hs. split; tas.
              apply (IH (_; _; _; Hs)). }
          - pose proof (onProjections Xg); auto.
          - pose proof (ind_sorts Xg) as Xg'. unfold check_ind_sorts in *.
            destruct Sort.to_family; auto.
            split. apply Xg'. destruct indices_matter; auto.
            eapply type_local_ctx_impl. eapply Xg'. auto. intros ?? Hj. apply Xj; tas.
            apply lift_typing_impl with (1 := Hj); intros ?? HT. split; tas.
            apply (IH (_; _; _; HT)).
           - apply Xg.(ind_relevance_compat).
           - apply (onIndices Xg). }
        { apply All_local_env_impl with (1 := onP); intros ?? Hj. apply Xj; tas.
          apply lift_typing_impl with (1 := Hj); intros ?? HT. split; tas.
          apply (IH ((Σ', udecl); (wfΣ; _; _; _; HT))).
          constructor 1. simpl. subst Σ' Σg; cbn; lia. }

  - assert (forall Γ t T (Hty : Σ ;;; Γ |-E t : T),
                  typingE_size Hty < typingE_size H ->
                  on_global_env cumulSpecE0 Pj Σ.1 * P Σ Γ t T).
    { intros.
      specialize (IH (Σ; wfΣ; _; _; _; Hty)).
      simpl in IH.
      forward IH.
      constructor 2. simpl. apply H0.
      split; apply IH. }
    (* rename X13 into X14. *)

    assert (Hdecls: typingE_size H > 1 -> on_global_env cumulSpecE0 Pj Σ.1).
    { specialize (X14 _ _ _  (typeE_Prop _)).
      cbn in X14. intros Hle. apply X14. lia. }

    assert (Hjudg : forall Γ j (Hj : lift_typing typingE Σ Γ j),
        lift_typing_size (fun t T H => @typingE_size cf Σ Γ t T H) _ Hj < typingE_size H ->
        Pj Σ Γ j).
    { intros ?? Hj Hlt.
      apply Xj; tas.
      eapply lift_typing_size_impl with (Psize := fun t T H => @typingE_size _ _ _ t T H) (tu := Hj).
      intros ?? Hty Hlt'; split; tas.
      apply X14 with (Hty := Hty). set (size_mid := lift_typing_size _ _ Hj) in *. lia. }
    clear Xj.

    assert (Hwf : forall Γ' (Hwf : wf_localE Σ Γ'),
      All_local_env_size (@typingE_size _ _) _ Hwf < typingE_size H ->
      PΓ Σ Γ').
    { intros. eapply (XΓ _ _ _ Hwf); auto.
    + clear -Pdecl wfΣ X14 H0.
      revert Hwf H0.
      induction Hwf; cbn in *; simpl in *; constructor.
      - simpl in *. apply IHHwf. lia.
      - red. apply (X14 _ _ _ t2.2.π2.1). cbn. lia.
      - simpl in *. apply IHHwf. lia.
      - red. apply (X14 _ _ _ t2.1). cbn. lia.
      - red. apply (X14 _ _ _ t2.2.π2.1). cbn. lia.
    + revert Hwf H0.
      induction Hwf; cbn in *; simpl in *; constructor.
      1,3: apply IHHwf; lia.
      all: eapply Hjudg with (Hj := t2); simpl; cbn.
      all: lia. }

    assert (Htywf : forall Γ' t T (Hty : Σ ;;; Γ' |-E t : T),
      typingE_size Hty <= typingE_size H ->
      PΓ Σ Γ').
    { intros. eapply (Hwf _ (typingE_wf_local Hty)); auto.
      pose proof (typingE_wf_local_size Hty). lia. }

    clear IH.
    assert (pΓ : PΓ Σ Γ).
    { apply (Htywf _ _ _ H). lia. }
    split; auto.
    set (wfΓ := typingE_wf_local H); clearbody wfΓ.

    destruct H; simpl in pΓ;
      try solve [  match reverse goal with
                      H : _ |- _ => eapply H
                    end; eauto;
                    unshelve eapply X14; simpl; auto with arith].

    all: try solve [ match reverse goal with H : _ |- _ => eapply H end;
      eauto; [ unshelve eapply Hjudg | unshelve eapply X14 ]; simpl; auto with arith ].

    -- match reverse goal with
          H : _ |- _ => eapply H
          end; eauto. all:try unshelve eapply X14; simpl; auto; try lia.
        exact H. 2:exact H0. 1-2:lia.
        simpl. instantiate (1:= H). instantiate (1:=H0).
        intros.
        eapply X14. instantiate (1 := Ht').
        simpl. lia.

    -- match reverse goal with
        H : _ |- _ => eapply H
        end; eauto.
        simpl in Hdecls. apply Hdecls; lia.

    -- eapply X6; eauto.
      apply Hdecls; simpl; lia.

    -- eapply X7; eauto. apply Hdecls; simpl; lia.

    -- simpl in pΓ. destruct c0, c1.
       eapply (X8 Σ wfΣ Γ (typingE_wf_local H0) ci); eauto.
        ++ eapply (X14 _ _ _ H); eauto. rewrite /predctx; simpl; lia.
        ++ eapply (X14 _ _ _ H); eauto. rewrite /predctx; simpl; lia.
        ++ eapply (Hwf _ wf_pctx). rewrite /predctx; simpl.
          change (fun Γ t T (Hty : Σ ;;; Γ |-E t : T) => typingE_size Hty) with (@typingE_size cf Σ).
          lia.
        ++ clear -ind_inst X14.
          assert (forall Γ' t T (Hty : Σ;;; Γ' |-E t : T),
            typingE_size Hty <= ctx_inst_size _ (@typingE_size _) ind_inst ->
            P Σ Γ' t T).
          { intros. eapply (X14 _ _ _ Hty). simpl.
            change (fun _ _ _ _ H => typingE_size H) with (@typingE_size cf).
            lia. }
          clear -X ind_inst.
          revert ind_inst X.
          generalize (List.rev (subst_instance (puinst p) (ind_params mdecl ,,, ind_indices idecl : context))).
          generalize (pparams p ++ indices).
          intros l c ctxi IH; induction ctxi; constructor; eauto.
          * split; tas. eapply (IH _ _ _ t0); simpl; auto. lia.
          * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.
          * eapply IHctxi. intros. eapply (IH _ _ _ Hty). simpl. lia.

        ++ eapply (X14 _ _ _ H0); simpl. lia.
        ++ clear Hdecls. simpl in Hwf, Htywf, X14.
          clear -Hwf Htywf X14.
          subst ptm predctx; induction brs_ty.
          ** constructor.
          ** destruct r0 as [eq [wfcbc [t t0]]]. constructor.
              --- split; auto. intros brctxty.
                  repeat split.
                  +++ eapply (Hwf _ wfcbc); eauto. simpl.
                    change (fun _ _ _ _ H => typingE_size H) with (@typingE_size cf).
                    change (fun _ _ _ H => typingE_size H) with (@typingE_size cf Σ).
                    lia.
                  +++ exact t.
                  +++ unshelve eapply (X14 _ _ _ t _); eauto.
                      simpl. lia.
                  +++ simpl; auto with arith.
                  +++ eapply (X14 _ _ _ t0); eauto. simpl; auto with arith.
                      lia.
              --- apply IHbrs_ty; auto. intros. apply (X14 _ _ _ Hty).
                  simpl. clear -H1; lia.
                  intros.
                  eapply (Hwf _ Hwf0). simpl. clear -H1; lia.
                  intros.
                  eapply (Htywf _ _ _ Hty). simpl; clear -H1. lia.

    -- eapply X9; eauto. apply Hdecls; simpl.
        pose proof (typingE_size_pos H). lia.
        eapply (X14 _ _ _  H). simpl. lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X11 X12.
        eapply X10; eauto; clear X10. simpl in *.
        * assert(forall Γ0 (t T : term) (Hty : Σ;;; Γ0 |-E t : T),
                  typingE_size Hty <
                  S (all_size (on_def_body (lift_typing typingE _) _ _) (fun x p => on_def_body_size (@typingE_size _ Σ) _ _ _ p) a1) ->
                  PΓ Σ Γ0).
          {intros. eapply (Htywf _ _ _ Hty); eauto. lia. }
          destruct mfix. now rewrite nth_error_nil in e.
          depelim a1. destruct o as (t & ?).
          eapply (X _ _ _ t). unfold on_def_body_sorting_size at 1. simpl. lia.
        * assert(forall j Hj,
                    lift_typing_size (fun t T H => @typingE_size _ Σ Γ t T H) j Hj <
                    S (all_size _ (fun x p => on_def_type_size (@typingE_size _ Σ) _ _ p) a0) ->
                    Pj Σ Γ j).
          { intros. eapply Hjudg with (Hj := Hj); eauto. simpl. change (typingE Σ Γ) with (fun t T => typingE Σ Γ t T). lia. }
          clear -a0 X.
          induction a0; constructor.
          ++ eapply X with (Hj := p). cbn.
            unfold on_def_type_sorting_size, lift_sorting_size, option_default_size in *.
            cbn in *. lia.
          ++ apply IHa0. intros. eapply X with (Hj := Hj); eauto.
            simpl. lia.
        * simpl in X14.
          assert (forall Γ, wf_localE Σ Γ ->
                  forall j Hj,
                  lift_typing_size (fun t T H => @typingE_size _ Σ Γ t T H) j Hj <
                  S (all_size (on_def_body (lift_typing typingE _) _ _) (fun x p => on_def_body_size (fun Γ t T H => @typingE_size cf Σ Γ t T H) _ _ _ p) a1) ->
                  Pj Σ Γ j).
          { intros. eapply Hjudg with (Hj := Hj); eauto. simpl.
            change (@typingE_size cf Σ) with (fun Γ t T tu => @typingE_size cf Σ Γ t T tu) at 5.
            change (@typingE cf Σ Γ0) with (fun t T => @typingE cf Σ Γ0 t T) at 1.
            lia. }
          clear -a1 X.
          remember (fix_context mfix) as mfixcontext eqn:e. clear e.
          induction a1; constructor.
          ++ eapply X with (Hj := p). 1: eapply typingE_wf_local, p.1. cbn. lia.
          ++ apply IHa1. intros. eapply X with (Hj := Hj); eauto.
            simpl. lia.

    -- clear X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X12.
        eapply X11; eauto; clear X11. simpl in *.
        * assert(forall Γ0 (t T : term) (Hty : Σ;;; Γ0 |-E t : T),
                  typingE_size Hty <
                  S (all_size (on_def_body (lift_typing typingE _) _ _) (fun x p => on_def_body_size (@typingE_size _ Σ) _ _ _ p) a1) ->
                  PΓ Σ Γ0).
          {intros. eapply (Htywf _ _ _ Hty); eauto. lia. }
          destruct mfix. now rewrite nth_error_nil in e.
          depelim a1. destruct o as (t & ?).
          eapply (X _ _ _ t). unfold on_def_body_sorting_size at 1. simpl. lia.
        * assert(forall j Hj,
                    lift_typing_size (fun t T H => @typingE_size _ Σ Γ t T H) j Hj <
                    S (all_size _ (fun x p => on_def_type_size (@typingE_size _ Σ) _ _ p) a0) ->
                    Pj Σ Γ j).
          { intros. eapply Hjudg with (Hj := Hj); eauto. simpl. change (typingE Σ Γ) with (fun t T => typingE Σ Γ t T). lia. }
          clear -a0 X.
          induction a0; constructor.
          ++ eapply X with (Hj := p). cbn.
            unfold on_def_type_sorting_size, lift_sorting_size, option_default_size in *.
            cbn in *. lia.
          ++ apply IHa0. intros. eapply X with (Hj := Hj); eauto.
            simpl. lia.
        * simpl in X14.
          assert (forall Γ, wf_localE Σ Γ ->
                  forall j Hj,
                  lift_typing_size (fun t T H => @typingE_size _ Σ Γ t T H) j Hj <
                  S (all_size (on_def_body (lift_typing typingE _) _ _) (fun x p => on_def_body_size (fun Γ t T H => @typingE_size cf Σ Γ t T H) _ _ _ p) a1) ->
                  Pj Σ Γ j).
          { intros. eapply Hjudg with (Hj := Hj); eauto. simpl.
            change (typingE Σ Γ0) with (fun t T => typingE Σ Γ0 t T) at 1.
            change (@typingE_size cf Σ) with (fun Γ t T tu => @typingE_size cf Σ Γ t T tu) at 5.
            lia. }
          clear -a1 X.
          remember (fix_context mfix) as mfixcontext eqn:e. clear e.
          induction a1; constructor.
          ++ eapply X with (Hj := p). 1: eapply typingE_wf_local, p.1. cbn. lia.
          ++ apply IHa1. intros. eapply X with (Hj := Hj); eauto.
            simpl. lia.

    -- eapply X12; tea.
       clear -p2 X14.
       simpl in X14. destruct p2; constructor; auto.
       * eapply (X14 _ _ _ hty). simpl. lia.
       * eapply (X14 _ _ _ hdef). simpl. lia.
       * simpl in X14. eapply (All_map_size (fun t p => @typingE_size cf Σ Γ t (array_type a0) p) _ hvalue); tea.
         intros x p hs. apply (X14 _ _ _ p). simpl. lia.
Qed.

Lemma typingE_ind_env `{cf : checker_flags} :
  forall (P : global_env_ext -> context -> term -> term -> Type)
         (Pj : global_env_ext -> context -> judgment -> Type)
         (Pdecl := fun Σ Γ wfΓ t T tyT => P Σ Γ t T)
         (PΓ : global_env_ext -> context -> Type),

    (forall Σ (wfΣ : wfE Σ) (Γ : context) (* (wfΓ : wf_localE Σ Γ) *) j,
         lift_typing_conj (typingE Σ) (P Σ) Γ j -> Pj Σ Γ j) ->

    (forall Σ (wfΣ : wfE Σ.1)  (Γ : context) (wfΓ : wf_localE Σ Γ),
         All_local_env_over (typingE Σ) (Pdecl Σ) Γ wfΓ -> All_local_env (Pj Σ) Γ -> PΓ Σ Γ) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (n : nat) decl,
        nth_error Γ n = Some decl ->
        PΓ Σ Γ ->
        P Σ Γ (tRel n) (lift0 (S n) decl.(decl_type))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (u : sort),
        PΓ Σ Γ ->
        wf_sort Σ u ->
        P Σ Γ (tSort u) (tSort (Sort.super u))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b : term) (s1 s2 : sort),
        PΓ Σ Γ ->
        lift_typing typingE Σ Γ (j_vass_s na t s1) ->
        Pj Σ Γ (j_vass_s na t s1) ->
        Σ ;;; Γ,, vass na t |-E b : tSort s2 ->
        P Σ (Γ,, vass na t) b (tSort s2) -> P Σ Γ (tProd na t b) (tSort (Sort.sort_of_product s1 s2))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (t b bty : term),
        PΓ Σ Γ ->
        lift_typing typingE Σ Γ (j_vass na t) ->
        Pj Σ Γ (j_vass na t) ->
        Σ ;;; Γ,, vass na t |-E b : bty -> P Σ (Γ,, vass na t) b bty -> P Σ Γ (tLambda na t b) (tProd na t bty)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (na : aname) (b b_ty b' b'_ty : term),
        PΓ Σ Γ ->
        lift_typing typingE Σ Γ (j_vdef na b b_ty) ->
        Pj Σ Γ (j_vdef na b b_ty) ->
        Σ ;;; Γ,, vdef na b b_ty |-E b' : b'_ty ->
        P Σ (Γ,, vdef na b b_ty) b' b'_ty -> P Σ Γ (tLetIn na b b_ty b') (tLetIn na b b_ty b'_ty)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t : term) na A B u s,
        PΓ Σ Γ ->
        Σ ;;; Γ |-E tProd na A B : tSort s -> P Σ Γ (tProd na A B) (tSort s) ->
        Σ ;;; Γ |-E t : tProd na A B -> P Σ Γ t (tProd na A B) ->
        Σ ;;; Γ |-E u : A -> P Σ Γ u A ->
        P Σ Γ (tApp t u) (B{0 := u})) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) cst u (decl : constant_body),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        declared_constant Σ.1 cst decl ->
        consistent_instance_ext Σ decl.(cst_universes) u ->
        P Σ Γ (tConst cst u) (subst_instance u (cst_type decl))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) u
          mdecl idecl (isdecl : declared_inductive Σ.1 ind mdecl idecl),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tInd ind u) (subst_instance u (ind_type idecl))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (ind : inductive) (i : nat) u
            mdecl idecl cdecl (isdecl : declared_constructor Σ.1 (ind, i) mdecl idecl cdecl),
        on_global_env cumulSpecE0 Pj Σ.1 ->
        PΓ Σ Γ ->
        consistent_instance_ext Σ mdecl.(ind_universes) u ->
        P Σ Γ (tConstruct ind i u) (type_of_constructor mdecl cdecl (ind, i) u)) ->

    (forall (Σ : global_env_ext) (wfΣ : wfE Σ) (Γ : context) (wfΓ : wf_localE Σ Γ),
    forall (ci : case_info) p c brs indices ps mdecl idecl
      (isdecl : declared_inductive Σ.1 ci.(ci_ind) mdecl idecl),
      on_global_env cumulSpecE0 Pj Σ.1 ->
      PΓ Σ Γ ->
      mdecl.(ind_npars) = ci.(ci_npar) ->
      eq_context_upto_names p.(pcontext) (ind_predicate_context ci.(ci_ind) mdecl idecl) ->
      let predctx := case_predicate_context ci.(ci_ind) mdecl idecl p in
      wf_predicate mdecl idecl p ->
      consistent_instance_ext Σ (ind_universes mdecl) p.(puinst) ->
      wf_localE Σ (Γ ,,, predctx) ->
      forall pret : Σ ;;; Γ ,,, predctx |-E p.(preturn) : tSort ps,
      P Σ (Γ ,,, predctx) p.(preturn) (tSort ps) ->
      PΓ Σ (Γ ,,, predctx) ->
      is_allowed_elimination Σ idecl.(ind_kelim) ps ->
      isSortRel ps ci.(ci_relevance) ->
      ctx_inst (Prop_conj typingE P Σ) Γ (p.(pparams) ++ indices)
        (List.rev (subst_instance p.(puinst) (mdecl.(ind_params) ,,, idecl.(ind_indices) : context))) ->
      Σ ;;; Γ |-E c : mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices) ->
      P Σ Γ c (mkApps (tInd ci.(ci_ind) p.(puinst)) (p.(pparams) ++ indices)) ->
      (isCoFinite mdecl.(ind_finite) ==> on_free_vars (strengthenP 0 1 xpredT) p.(preturn)) = true ->
      let ptm := it_mkLambda_or_LetIn predctx p.(preturn) in
      wf_branches idecl brs ->
      All2i (fun i cdecl br =>
        (eq_context_upto_names br.(bcontext) (cstr_branch_context ci mdecl cdecl)) ×
        let brctxty := case_branch_type ci.(ci_ind) mdecl idecl p br ptm i cdecl in
        (PΓ Σ (Γ ,,, brctxty.1) ×
          Prop_conj typingE P Σ (Γ ,,, brctxty.1) br.(bbody) brctxty.2 ×
          Prop_conj typingE P Σ (Γ ,,, brctxty.1) brctxty.2 (tSort ps))) 0 idecl.(ind_ctors) brs ->
      P Σ Γ (tCase ci p c brs) (mkApps ptm (indices ++ [c]))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : projection) (c : term) u
          mdecl idecl cdecl pdecl (isdecl : declared_projection Σ.1 p mdecl idecl cdecl pdecl) args,
        on_global_env cumulSpecE0 Pj Σ.1 -> PΓ Σ Γ ->
        Σ ;;; Γ |-E c : mkApps (tInd p.(proj_ind) u) args ->
        P Σ Γ c (mkApps (tInd p.(proj_ind) u) args) ->
        #|args| = ind_npars mdecl ->
        P Σ Γ (tProj p c) (subst0 (c :: List.rev args) (subst_instance u pdecl.(proj_type)))) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        fix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
        All (on_def_type (Pj Σ) Γ) mfix ->
        All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
        All (on_def_body (Pj Σ) types Γ) mfix ->
        wf_fixpointE Σ Γ mfix ->
        P Σ Γ (tFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (mfix : list (def term)) (n : nat) decl,
        let types := fix_context mfix in
        cofix_guard Σ Γ mfix ->
        nth_error mfix n = Some decl ->
        PΓ Σ (Γ ,,, types) ->
        All (on_def_type (lift_typing typingE Σ) Γ) mfix ->
        All (on_def_type (Pj Σ) Γ) mfix ->
        All (on_def_body (lift_typing typingE Σ) types Γ) mfix ->
        All (on_def_body (Pj Σ) types Γ) mfix ->
        wf_cofixpointE Σ Γ mfix ->
        P Σ Γ (tCoFix mfix n) decl.(dtype)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (p : prim_val term) prim_ty cdecl,
        PΓ Σ Γ ->
        primitive_constant Σ (prim_val_tag p) = Some prim_ty ->
        declared_constant Σ prim_ty cdecl ->
        primitive_invariants (prim_val_tag p) cdecl ->
        primitive_typing_hyps (typingE Σ) Σ Γ p ->
        primitive_typing_hyps (P Σ) Σ Γ p ->
        P Σ Γ (tPrim p) (prim_type p prim_ty)) ->

    (forall Σ (wfΣ : wfE Σ.1) (Γ : context) (wfΓ : wf_localE Σ Γ) (t A B : term) s,
        PΓ Σ Γ ->
        Σ ;;; Γ |-E t : A ->
        P Σ Γ t A ->
        Σ ;;; Γ |-E B : tSort s ->
        P Σ Γ B (tSort s) ->
        cumulSpecE Σ Γ A B ->
        P Σ Γ t B) ->

       env_propE P Pj PΓ.
Proof.
  intros P Pj Pdecl PΓ; unfold env_propE.
  intros Xj XΓ X X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 Σ wfΣ Γ t T H.
  apply typingE_ind_env_app_size; eauto.
Qed.
