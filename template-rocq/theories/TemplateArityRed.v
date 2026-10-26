(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.Template Require Import Ast AstUtils ReflectAst LiftSubst UnivSubst Typing.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.

Local Open Scope type_scope.

(** * Properties of the Template kernel-arity relations

  [whd_rel] and [arity_red] are defined in [MetaRocq.Template.Typing], beside
  [red1], because [TemplateGlobalMaps] takes [arity_red] as its [ArityRedSig]
  argument.  This file proves what the specification needs of them:

  - both relations are deterministic ([whd_rel_det], [arity_red_det]): every
    rule reads the environment through [lookup_env], which is a function even
    on an environment with duplicate names.

  This is the Template twin of [MetaRocq.PCUIC.PCUICArityRed]. *)

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

Lemma whd_nth_split {A} (l : list A) n x :
  nth_error l n = Some x ->
  l = firstn n l ++ x :: skipn (S n) l × #|firstn n l| = n.
Proof.
  induction l in n |- *; destruct n; cbn; intros h; try discriminate.
  - injection h as ->. split; reflexivity.
  - destruct (IHl _ h) as [e e']. split; [now rewrite {1}e|now rewrite e'].
Qed.

Lemma whd_nth_middle {A} (pre post : list A) n y :
  #|pre| = n -> nth_error (pre ++ y :: post) n = Some y.
Proof. intros <-. induction pre; cbn; auto. Qed.

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
    destruct (whd_nth_split _ _ _ hn) as [e _].
    rewrite (LiftSubst.mkApps_tApp f args hf (nth_error_nonnil _ _ _ hn)).
    rewrite {1}e. now apply red_arg_one.
  Qed.

  Lemma whd_rel_red {zeta t args h l} :
    whd_rel zeta Σ Γ t args h l -> red Σ Γ (mkApps t args) (mkApps h l).
  Proof.
    induction 1 as [c args d b h l hnth hbod w IH|c args d hnth hbod
      |na b B t args h l hz w IH|na b B t args hz
      |c u decl body args h l hcst hbod w IH|c u decl args hcst hbod
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
      |t args hs].
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
      destruct (whd_nth_split _ _ _ hnth) as [_ len].
      unfold is_constructor. rewrite (whd_nth_middle _ _ _ _ len).
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
  Qed.
End TemplateWhdRed.

Lemma red_prod_r {Σ Γ na A B B'} :
  red Σ (Γ ,, vass na A) B B' -> red Σ Γ (tProd na A B) (tProd na A B').
Proof.
  induction 1 as [|P N r IH s]; [constructor|].
  eapply red_trans; [exact IH|]. apply red1_red. now apply prod_red_r.
Qed.

Lemma red_letin_body {Σ Γ na b A B B'} :
  red Σ (Γ ,, vdef na b A) B B' -> red Σ Γ (tLetIn na b A B) (tLetIn na b A B').
Proof.
  induction 1 as [|P N r IH s]; [constructor|].
  eapply red_trans; [exact IH|]. apply red1_red. now apply letin_red_body.
Qed.

Lemma arity_red_red {Σ Γ t Δ s} :
  arity_red Σ Γ t Δ s -> red Σ Γ t (it_mkProd_or_LetIn Δ (tSort s)).
Proof.
  induction 1 as [Γ t s w|Γ t na A B Δ s w ar IH|Γ t na b A B Δ s w ar IH
    |Γ t h l h' l' Δ s w ha w' hne ar IH].
  - exact (whd_rel_red _ _ w).
  - rewrite it_mkProd_or_LetIn_app /=.
    eapply red_trans; [exact (whd_rel_red _ _ w)|]. now apply red_prod_r.
  - rewrite it_mkProd_or_LetIn_app /=.
    eapply red_trans; [exact (whd_rel_red _ _ w)|]. now apply red_letin_body.
  - eapply red_trans; [exact (whd_rel_red _ _ w)|].
    eapply red_trans; [exact (whd_rel_red _ _ w')|]. exact IH.
Qed.

(** ** Determinism

  The machine is a function: every rule reads the context with [nth_error] and
  the environment with [lookup_env]/[lookup_constructor], and the rules of one
  head are pairwise exclusive. *)

(** A head on which the machine stops cannot also be a redex. *)
Ltac whd_absurd_stop :=
  match goal with
  | H : is_true (whd_stop_head _ _) |- _ =>
      unfold is_true in H; cbn in H; discriminate
  end.

(** The reduced head of a subterm, obtained from two derivations, refutes the
    "not a constructor / not a cofix" side condition of a stuck rule. *)
Ltac whd_absurd_head :=
  match goal with
  | H : whd_is_construct _ = false |- _ => cbn in H; discriminate
  | H : whd_is_construct0 _ = false |- _ => cbn in H; discriminate
  | H : whd_is_cofix _ = false |- _ => cbn in H; discriminate
  end.

(** Make the witnesses of the two derivations equal: context and environment
    lookups are functions. *)
Ltac whd_det_subst :=
  repeat
    match goal with
    | H : ?x = Some ?a, H' : ?x = Some ?b |- _ =>
        is_var b;
        lazymatch a with
        | b => fail
        | _ => assert (b = a) as -> by congruence
        end
    | H : ?x = Some (?a1, ?a2), H' : ?x = Some (?b1, ?b2) |- _ =>
        first
          [ is_var b1;
            lazymatch a1 with
            | b1 => fail
            | _ => assert (b1 = a1) as -> by congruence
            end
          | is_var b2;
            lazymatch a2 with
            | b2 => fail
            | _ => assert (b2 = a2) as -> by congruence
            end ]
    | H : ?x = Some (ConstantDecl ?a), H' : ?x = Some (ConstantDecl ?b) |- _ =>
        is_var b;
        lazymatch a with
        | b => fail
        | _ => assert (b = a) as -> by congruence
        end
    | H : ?x = Some (?a1, ?a2, ?a3), H' : ?x = Some (?b1, ?b2, ?b3) |- _ =>
        first
          [ is_var b1;
            lazymatch a1 with
            | b1 => fail
            | _ => assert (b1 = a1) as -> by congruence
            end
          | is_var b2;
            lazymatch a2 with
            | b2 => fail
            | _ => assert (b2 = a2) as -> by congruence
            end
          | is_var b3;
            lazymatch a3 with
            | b3 => fail
            | _ => assert (b3 = a3) as -> by congruence
            end ]
    end.

(** Resolve every derivation of a reduced subterm (the discriminant or the
    recursive argument, always with an empty stack) with [IHa]. *)
Ltac whd_det_disc IHa :=
  repeat
    match goal with
    | W : whd_rel _ _ _ _ [] _ _ |- _ =>
        let e1 := fresh "e" in
        let e2 := fresh "e" in
        destruct (IHa _ _ W) as [e1 e2]; noconf e1; noconf e2; clear W
    end.

(** Close the goal with the induction hypothesis for the continuation: it is
    the derivation whose result is the one the goal asks about. *)
Ltac whd_det_IH IH :=
  match goal with
  | |- (_ = ?hh) × (_ = ?ll) =>
      match goal with
      | W : whd_rel _ _ _ _ _ hh ll |- _ => exact (IH _ _ W)
      end
  end.

Lemma whd_rel_det {z Σ Γ t args h l h' l'} :
  whd_rel z Σ Γ t args h l -> whd_rel z Σ Γ t args h' l' -> h = h' × l = l'.
Proof.
  intros w. revert h' l'.
  induction w as [c args d b h l hnth hbod w IH|c args d hnth hbod
    |na b B t args h l hz w IH|na b B t args hz
    |c u decl body args h l hcst hbod w IH|c u decl args hcst hbod
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
    |t args hs]; intros hh ll w'.
  (* tRel, let-bound *)
  - depelim w'; whd_det_subst;
      solve [whd_det_IH IH | congruence | whd_absurd_stop].
  (* tRel, assumption *)
  - depelim w'; whd_det_subst;
      solve [congruence | (split; reflexivity) | whd_absurd_stop].
  (* zeta *)
  - depelim w'; solve [whd_det_IH IH | congruence | whd_absurd_stop].
  (* let, zeta off *)
  - depelim w'; solve [congruence | (split; reflexivity) | whd_absurd_stop].
  (* delta *)
  - depelim w'; whd_det_subst;
      solve [whd_det_IH IH | congruence | whd_absurd_stop].
  (* axiom *)
  - depelim w'; whd_det_subst;
      solve [congruence | (split; reflexivity) | whd_absurd_stop].
  (* cast *)
  - depelim w'; solve [whd_det_IH IH | whd_absurd_stop].
  (* application *)
  - depelim w'; solve [whd_det_IH IH | whd_absurd_stop].
  (* beta *)
  - depelim w'; solve [whd_det_IH IH | whd_absurd_stop].
  (* fix unfolding *)
  - depelim w'; whd_det_subst; whd_det_disc IHa; whd_det_subst;
      solve [whd_det_IH IHb | whd_absurd_head | congruence | whd_absurd_stop].
  (* stuck fix *)
  - depelim w'; whd_det_subst; whd_det_disc IHa; whd_det_subst;
      solve [whd_absurd_head | congruence | (split; reflexivity) | whd_absurd_stop].
  (* fix without enough arguments *)
  - depelim w'; whd_det_subst;
      solve [congruence | (split; reflexivity) | whd_absurd_stop].
  (* fix with no unfolding *)
  - depelim w'; solve [congruence | (split; reflexivity) | whd_absurd_stop].
  (* iota *)
  - depelim w'; whd_det_disc IHa; whd_det_subst;
      solve [whd_det_IH IHb | whd_absurd_head | whd_absurd_stop].
  (* case on a cofix *)
  - depelim w'; whd_det_disc IHa; whd_det_subst;
      solve [whd_det_IH IHb | whd_absurd_head | whd_absurd_stop].
  (* stuck case *)
  - depelim w'; whd_det_disc IHa; whd_det_subst;
      solve [whd_absurd_head | (split; reflexivity) | whd_absurd_stop].
  (* projection *)
  - depelim w'; whd_det_disc IHa; whd_det_subst;
      solve [whd_det_IH IHb | whd_absurd_head | whd_absurd_stop].
  (* projection of a cofix *)
  - depelim w'; whd_det_disc IHa; whd_det_subst;
      solve [whd_det_IH IHb | whd_absurd_head | whd_absurd_stop].
  (* stuck projection *)
  - depelim w'; whd_det_disc IHa; whd_det_subst;
      solve [whd_absurd_head | (split; reflexivity) | whd_absurd_stop].
  (* the machine stops *)
  - depelim w'; solve [whd_absurd_stop | (split; reflexivity)].
Qed.

(** Both weak-head derivations of one level of the telescope agree. *)
Ltac arity_det_whd :=
  repeat
    match goal with
    | W : whd_rel ?z _ _ ?t [] _ _, W' : whd_rel ?z _ _ ?t [] _ _ |- _ =>
        tryif constr_eq W W' then fail
        else
          (let e1 := fresh "e" in
           let e2 := fresh "e" in
           destruct (whd_rel_det W W') as [e1 e2]; noconf e1; noconf e2; clear W')
    end.

(** A level that [whd_allnolet] already ends cannot take the fallback. *)
Ltac arity_det_absurd :=
  match goal with
  | H : whd_arity_head _ _ = false |- _ => cbn in H; discriminate
  end.

Ltac arity_det_IH IH :=
  match goal with
  | A : arity_red _ _ _ _ _ |- _ =>
      destruct (IH _ _ A) as [-> ->]; split; reflexivity
  end.

Lemma arity_red_det {Σ Γ t Δ s Δ' s'} :
  arity_red Σ Γ t Δ s -> arity_red Σ Γ t Δ' s' -> Δ = Δ' × s = s'.
Proof.
  intros ar. revert Δ' s'.
  induction ar as [Γ t s w|Γ t na A B Δ s w ar IH|Γ t na b A B Δ s w ar IH
    |Γ t h l h' l' Δ s w ha w' hne ar IH]; intros Δ'' s'' ar'.
  - depelim ar'; arity_det_whd;
      solve [(split; reflexivity) | arity_det_absurd].
  - depelim ar'; arity_det_whd; solve [arity_det_IH IH | arity_det_absurd].
  - depelim ar'; arity_det_whd; solve [arity_det_IH IH | arity_det_absurd].
  - depelim ar'; arity_det_whd; solve [arity_det_IH IH | arity_det_absurd].
Qed.
