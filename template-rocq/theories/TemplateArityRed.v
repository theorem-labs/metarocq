(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.Template Require Import Ast AstUtils ReflectAst LiftSubst UnivSubst Typing.

Local Open Scope type_scope.

(** * Properties of the Template weak-head relation

  [whd_rel] and [arity_red] are defined in [MetaRocq.Template.Typing], beside
  [red1], because [TemplateGlobalMaps] takes them in its [KernelRedSig]
  argument.  This file proves that a [whd_rel] derivation is a reduction
  ([whd_rel_red]) and that its head is never an application
  ([whd_rel_out_napp]); the translation to PCUIC uses both. *)

(** ** Reduction sequences *)

Lemma red1_red {Σ Γ t u} : red1 Σ Γ t u -> red Σ Γ t u.
Proof. intros r. econstructor; [constructor|exact r]. Qed.

Lemma red_trans {Σ Γ t u v} : red Σ Γ t u -> red Σ Γ u v -> red Σ Γ t v.
Proof.
  intros r1 r2. induction r2 as [|P N r IH s]; [exact r1|].
  econstructor; [exact IH|exact s].
Qed.

Lemma nth_error_nonnil {A} (l : list A) n x : nth_error l n = Some x -> l <> [].
Proof. destruct l; [destruct n; discriminate|discriminate]. Qed.

(** ** A derivation is a reduction *)

Section TemplateWhdRed.
  Context (Σ : global_env) (Γ : context).

  (** A head contraction under a stack of arguments.  [a] is never an
      application, so [mkApps a args] exposes it as [tApp a args]. *)
  Lemma red_hd_step a b args :
    isApp a = false -> red1 Σ Γ a b -> red Σ Γ (mkApps a args) (mkApps b args).
  Proof.
    intros ha r. destruct args as [|x args].
    - exact (red1_red r).
    - rewrite (LiftSubst.mkApps_tApp a (x :: args) ha ltac:(discriminate)).
      apply red1_red. now apply app_red_l.
  Qed.

  Lemma red_congr_hd (F : term -> term) c c' args :
    (forall x, isApp (F x) = false) ->
    (forall x y, red1 Σ Γ x y -> red1 Σ Γ (F x) (F y)) ->
    red Σ Γ c c' -> red Σ Γ (mkApps (F c) args) (mkApps (F c') args).
  Proof.
    intros hF hr r. induction r as [|P N r IH s].
    - constructor.
    - eapply red_trans; [exact IH|]. apply red_hd_step; [apply hF|now apply hr].
  Qed.

  Lemma red_arg_one f pre x y post :
    red Σ Γ x y ->
    red Σ Γ (tApp f (pre ++ x :: post)) (tApp f (pre ++ y :: post)).
  Proof.
    induction 1 as [|P N r IH s].
    - constructor.
    - eapply red_trans; [exact IH|]. apply red1_red, app_red_r.
      apply OnOne2_app. now constructor.
  Qed.

  Lemma red_nth_arg f args narg c c' :
    isApp f = false ->
    nth_error args narg = Some c -> red Σ Γ c c' ->
    red Σ Γ (mkApps f args) (tApp f (firstn narg args ++ c' :: skipn (S narg) args)).
  Proof.
    intros hf hn r.
    destruct (nth_error_split_firstn_skipn _ _ _ hn) as [e _].
    rewrite (LiftSubst.mkApps_tApp f args hf (nth_error_nonnil _ _ _ hn)).
    rewrite {1}e. now apply red_arg_one.
  Qed.

  (** An application node with at least one argument. *)
  Lemma mkApps_cons_tApp f pre x post :
    isApp f = false -> mkApps f (pre ++ x :: post) = tApp f (pre ++ x :: post).
  Proof.
    intros hf. apply LiftSubst.mkApps_tApp; [exact hf|destruct pre; discriminate].
  Qed.

  (** The arguments before and after the one being evaluated do not move, so a
      reduction of that one argument is a reduction of the whole application. *)
  Lemma red_prim_arg_cong c u ls a b rest tail :
    red Σ Γ a b ->
    red Σ Γ (mkApps (tConst c u) (map template_of_lit ls ++ a :: rest ++ tail))
            (mkApps (tConst c u) (map template_of_lit ls ++ b :: rest ++ tail)).
  Proof.
    intros r.
    rewrite !(mkApps_cons_tApp (tConst c u) (map template_of_lit ls) _ (rest ++ tail) eq_refl).
    now apply red_arg_one.
  Qed.

  (** [tsplit_lits] on the first [n] arguments names the maximal literal prefix
      [ls] and the first non-literal [a]; the whole argument list is then that
      decomposition followed by the over-applied tail. *)
  Lemma tprim_args_eq {args n ls a rest} :
    tsplit_lits (firstn n args) = inr (ls, a, rest) ->
    args = map template_of_lit ls ++ a :: rest ++ skipn n args.
  Proof.
    intros hs.
    rewrite -{1}(firstn_skipn n args) (proj1 (tsplit_lits_inr hs)) -app_assoc //.
  Qed.

  Lemma tprim_args_eq_inl {args n ls} :
    tsplit_lits (firstn n args) = inl ls ->
    args = map template_of_lit ls ++ skipn n args.
  Proof.
    intros hs. rewrite -{1}(firstn_skipn n args) (tsplit_lits_inl hs) //.
  Qed.

  (** A saturated literal prefix has exactly the operation's arity, so it is
      not empty and the redex is an application node. *)
  Lemma prim_lits_nonnil {args op ls} :
    arity op <= #|args| -> tsplit_lits (firstn (arity op) args) = inl ls ->
    map template_of_lit ls ++ skipn (arity op) args <> [].
  Proof.
    intros hsat hs.
    have hfl : #|firstn (arity op) args| = arity op by rewrite length_firstn; lia.
    have hlen : #|ls| = arity op by rewrite -hfl (tsplit_lits_inl hs) length_map.
    pose proof (arity_pos op).
    destruct ls as [|l0 ls0]; [cbn in hlen; lia|]; cbn; discriminate.
  Qed.

  Lemma whd_rel_red {zeta t args h l} :
    whd_rel zeta Σ Γ t args h l -> red Σ Γ (mkApps t args) (mkApps h l).
  Proof.
    induction 1 as [c args d b h l hnth hbod w IH|c args d hnth hbod
      |na b B t args h l hz w IH|na b B t args hz
      |c u decl body args h l hcst hbod w IH|c u decl args hcst hbod hpo
      |c k T args h l w IH
      |f l args h l' hf hl w IH
      |na A t a args h l w IH
      |mfix idx narg fn args c ind n ui cargs h l hunf hnth wa IHa wb IHb
      |mfix idx narg fn args c t cargs hunf hnth wa IHa hnc
      |mfix idx narg fn args hunf hnth|mfix idx args hunf
      |ci p c brs args n ui cargs mdecl idecl cdecl br h l wa IHa hbr hdecl hlen wb IHb
      |ci p c brs args mfix idx cargs narg fn h l wa IHa hunf wb IHb
      |ci p c brs args t cargs wa IHa hnc hncf
      |p c args u cargs a h l wa IHa hnth wb IHb
      |p c args mfix idx cargs narg fn h l wa IHa hunf wb IHb
      |p c args t cargs wa IHa hnc hncf
      |t args hs
      |c u decl op args ls a rest t cargs lit h l hcst hbod hpo hsat hs wa IHa hnl w IH
      |c u decl op args ls a rest t cargs hcst hbod hpo hsat hs wa IHa hnl
      |c u decl op args ls r v h l hcst hbod hpo hsat hs hden hrb w IH
      |c u decl op args ls hcst hbod hpo hsat hs hden
      |c u decl op args hcst hbod hpo hpart].
    (* tRel, let-bound: [red_rel] *)
    - eapply red_trans; [|exact IH]. apply red_hd_step; [reflexivity|].
      apply red_rel. now rewrite hnth /= hbod.
    (* tRel, assumption: stuck *)
    - constructor.
    (* zeta *)
    - eapply red_trans; [|exact IH]. apply red_hd_step; [reflexivity|].
      apply red_zeta.
    (* let, zeta off: stuck *)
    - constructor.
    (* delta *)
    - eapply red_trans; [|exact IH]. apply red_hd_step; [reflexivity|].
      eapply red_delta; [apply declared_constant_from_gen; exact hcst|exact hbod].
    (* axiom: stuck *)
    - constructor.
    (* cast stripping *)
    - eapply red_trans; [|exact IH]. apply red_hd_step; [reflexivity|].
      apply cast_red.
    (* n-ary application: pushing the arguments is an identity on [mkApps] *)
    - rewrite -(LiftSubst.mkApps_tApp f l hf hl) -mkApps_app. exact IH.
    (* beta *)
    - eapply red_trans; [|exact IH].
      rewrite (LiftSubst.mkApps_tApp (tLambda na A t) (a :: args) eq_refl
                 ltac:(discriminate)).
      apply red1_red, red_beta.
    (* fix unfolding: the recursive argument is reduced first *)
    - eapply red_trans; [|exact IHb].
      eapply red_trans.
      { eapply red_nth_arg; [reflexivity|exact hnth|exact IHa]. }
      apply red1_red. eapply red_fix; [exact hunf|].
      destruct (nth_error_split_firstn_skipn _ _ _ hnth) as [_ len].
      unfold is_constructor. rewrite (nth_error_snoc _ _ _ _ (eq_sym len)).
      unfold isConstruct_app. now rewrite decompose_app_mkApps.
    (* stuck fix: the reduced recursive argument is kept *)
    - rewrite (LiftSubst.mkApps_tApp (tFix mfix idx)
                 (firstn narg args ++ mkApps t cargs :: skipn (S narg) args) eq_refl
                 ltac:(destruct (firstn narg args); discriminate)).
      eapply red_nth_arg; [reflexivity|exact hnth|exact IHa].
    (* fix without enough arguments, and fix with no body: stuck *)
    - constructor.
    - constructor.
    (* iota *)
    - eapply red_trans; [|exact IHb].
      eapply red_trans.
      { eapply (red_congr_hd (fun x => tCase ci p x brs));
          [intros ?; reflexivity| |exact IHa].
        intros x y r. now apply case_red_discr. }
      apply red_hd_step; [reflexivity|].
      eapply red_iota;
        [exact hbr
        |apply declared_constructor_from_gen, lookup_constructor_declared_gen; exact hdecl
        |exact hlen].
    (* case on a cofix *)
    - eapply red_trans; [|exact IHb].
      eapply red_trans.
      { eapply (red_congr_hd (fun x => tCase ci p x brs));
          [intros ?; reflexivity| |exact IHa].
        intros x y r. now apply case_red_discr. }
      apply red_hd_step; [reflexivity|]. eapply red_cofix_case; exact hunf.
    (* stuck case: the reduced discriminant is kept *)
    - eapply (red_congr_hd (fun x => tCase ci p x brs));
        [intros ?; reflexivity| |exact IHa].
      intros x y r. now apply case_red_discr.
    (* projection *)
    - eapply red_trans; [|exact IHb].
      eapply red_trans.
      { eapply (red_congr_hd (fun x => tProj p x));
          [intros ?; reflexivity| |exact IHa].
        intros x y r. now apply proj_red. }
      apply red_hd_step; [reflexivity|]. now apply red_proj.
    (* projection of a cofix *)
    - eapply red_trans; [|exact IHb].
      eapply red_trans.
      { eapply (red_congr_hd (fun x => tProj p x));
          [intros ?; reflexivity| |exact IHa].
        intros x y r. now apply proj_red. }
      apply red_hd_step; [reflexivity|]. eapply red_cofix_proj; exact hunf.
    (* stuck projection *)
    - eapply (red_congr_hd (fun x => tProj p x));
        [intros ?; reflexivity| |exact IHa].
      intros x y r. now apply proj_red.
    (* the machine stops *)
    - constructor.
    (* whd_prim_arg: reduce the first non-literal argument, then re-enter *)
    - eapply red_trans; [|exact IH].
      rewrite {1}(tprim_args_eq hs). apply red_prim_arg_cong. exact IHa.
    (* whd_prim_stuck: the reduced stuck argument is kept *)
    - rewrite {1}(tprim_args_eq hs). apply red_prim_arg_cong. exact IHa.
    (* whd_prim_fire: every argument is a literal, the rule fires *)
    - eapply red_trans; [|exact IH].
      rewrite {1}(tprim_args_eq_inl hs).
      rewrite (LiftSubst.mkApps_tApp (tConst c u) _ eq_refl (prim_lits_nonnil hsat hs)).
      apply red1_red. eapply red_prim_op;
        [apply declared_constant_from_gen; exact hcst|exact hpo|exact hbod|exact hden|exact hrb].
    (* whd_prim_inert: saturated but the operation does not compute *)
    - constructor.
    (* whd_prim_partial: unsaturated *)
    - constructor.
  Qed.
End TemplateWhdRed.

(** The head the machine stops at is never an application. *)
Lemma whd_rel_out_napp {z Σ Γ t args h l} :
  whd_rel z Σ Γ t args h l -> isApp h = false.
Proof.
  induction 1; try reflexivity; try assumption.
  destruct t; cbn in hs; try discriminate; reflexivity.
Qed.
