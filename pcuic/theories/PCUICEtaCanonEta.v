(* Distributed under the terms of the MIT license. *)

(** * BET-315 eta lane, §6.2 obligation 5 (first half): [eta1] against [canon]

    [eta1_canon]      eta1 a b -> clos_refl eta1 (canon a) (canon b)
    [eta1_canonical]  canon t = t -> eta1 t u -> canon u = u

  [eta1_canon] is what makes (A)'s strong-commutation premise EXACT: an η step
  maps through [canon] to at most one η step. [eta1_canonical] is the [canon]
  half of "[eta1] preserves [Q]".

  **Why [eta1_canon] is only reflexive-closure.** A step INSIDE a λ domain
  ([abs_eta_l]) vanishes under [canon], which erases the domain. Every other step
  survives, and the root contraction survives because [canon] commutes with
  [lift0 1] ([canon_lift]), so [canon] of an η-redex is again an η-redex.
  (The converse fails, and nothing here needs it: [canon] can CREATE η-redexes,
  e.g. C1b's [λx:P. (P (λy:x.y)) x], whose inner domain [x] blocks η until [canon]
  erases it. Geuvers LICS 1992 records exactly this.)

  **The canonicalisation hazard (plan.md §6.2; [r3a-canon-audit.md]) does not
  arise here, and this is checked rather than assumed.** The hazard is a step
  that destroys information the FINAL COMPARISON reads; the audit found that
  η-contraction removes exactly one such thing, the application count [napp] at
  an under-applied [tInd]/[tConstruct] head. Both lemmas here are statements
  about [canon], a STRUCTURAL map that never reads [napp]. Concretely, on the
  lane lead's case: [λx:S. I1@{u} (tRel 0)] is canonical, η-contracts to
  [I1@{u}], and [canon (I1@{u}) = I1@{u}]. The [napp] drop that contraction
  causes is real, but it is a property of the later COMPARISON (obligation 8,
  repaired by F-inst), not of canonicity. Nothing in this file mentions [napp].

  Dependencies: [PCUICEtaDefs], [PCUICEtaCanon]. No confluence file. *)

From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Primitive.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICPrimitive
     PCUICLiftSubst PCUICInduction PCUICReduction PCUICEtaDefs PCUICEtaCanon.

Local Open Scope type_scope.

(** ** Closure plumbing *)

Lemma clos_refl_case {A} (R : A -> A -> Type) x y : clos_refl R x y -> R x y + (x = y).
Proof. intros h; destruct h; [now left|now right]. Qed.

Lemma clos_refl_map' {A B} (R : A -> A -> Type) (S : B -> B -> Type) (g : A -> B) x y :
  (forall a b, R a b -> S (g a) (g b)) -> clos_refl R x y -> clos_refl S (g x) (g y).
Proof.
  intros H h. destruct (clos_refl_case _ _ _ h) as [h'|<-]; [apply r_step; now apply H|apply r_refl].
Qed.

Lemma OnOne2_map_clos_refl {A B} (R : A -> A -> Type) (S : B -> B -> Type) (f : A -> B) l l' :
  OnOne2 R l l' ->
  (forall x y, R x y -> clos_refl S (f x) (f y)) ->
  clos_refl (OnOne2 S) (map f l) (map f l').
Proof.
  intros h H. induction h as [hd hd' tl r|hd tl tl' r IH]; cbn.
  - destruct (clos_refl_case _ _ _ (H _ _ r)) as [h'|e].
    + apply r_step. now constructor.
    + rewrite e. apply r_refl.
  - destruct (clos_refl_case _ _ _ IH) as [h'|e].
    + apply r_step. now constructor.
    + rewrite e. apply r_refl.
Qed.

(** ** [lift0 1] is injective (a left inverse is [subst [tRel 0] 0]) *)

Lemma lift0_1_inj x y : lift0 1 x = lift0 1 y -> x = y.
Proof.
  intros h.
  rewrite -(simpl_subst_k [tRel 0] x 0 1 eq_refl) -(simpl_subst_k [tRel 0] y 0 1 eq_refl).
  now rewrite h.
Qed.

(** ** (5a) [eta1] maps through [canon] to at most one [eta1] step *)

Lemma eta1_canon a b : eta1 a b -> clos_refl eta1 (canon a) (canon b).
Proof.
  revert a b.
  apply (eta1_ind_all (fun a b => clos_refl eta1 (canon a) (canon b))).
  - (* eta_red: canon of an η-redex is an η-redex, by [canon_lift] *)
    intros na t A. cbn [canon]. rewrite canon_lift. apply r_step. apply eta_red.
  - (* abs_eta_l: a step inside the λ DOMAIN vanishes, canon erases the domain *)
    intros. cbn [canon]. apply r_refl.
  - (* abs_eta_r *)
    intros na M M' N _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tLambda canon_la canon_dom x)); [|exact IH].
    intros ? ? h. now apply abs_eta_r.
  - (* letin_eta_def *)
    intros na b t b' r _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tLetIn (canon_na na) x (canon t) (canon b'))); [|exact IH].
    intros ? ? h. now apply letin_eta_def.
  - (* letin_eta_ty *)
    intros na b t b' r _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tLetIn (canon_na na) (canon b) x (canon b'))); [|exact IH].
    intros ? ? h. now apply letin_eta_ty.
  - (* letin_eta_body *)
    intros na b t b' r _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tLetIn (canon_na na) (canon b) (canon t) x)); [|exact IH].
    intros ? ? h. now apply letin_eta_body.
  - (* case_eta_param *)
    intros ci p params' c brs h. cbn [canon].
    eapply (clos_refl_map' _ _
      (fun ps => tCase ci (set_pparams (canon_predicate canon p) ps) (canon c)
                       (map (canon_branch canon) brs))).
    + (* [apply] cannot unify the nested [set_pparams]; the sides are convertible *)
      intros a b h'. exact (case_eta_param ci (set_pparams (canon_predicate canon p) a) b _ _ h').
    + eapply OnOne2_map_clos_refl; [exact h|]. intros x y [_ IH]. exact IH.
  - (* case_eta_return *)
    intros ci p preturn' c brs _ IH. cbn [canon].
    eapply (clos_refl_map' _ _
      (fun r => tCase ci (set_preturn (canon_predicate canon p) r) (canon c)
                      (map (canon_branch canon) brs))); [|exact IH].
    intros a b h'. exact (case_eta_return ci (set_preturn (canon_predicate canon p) a) b _ _ h').
  - (* case_eta_discr *)
    intros ci p c c' brs _ IH. cbn [canon].
    eapply (clos_refl_map' _ _
      (fun x => tCase ci (canon_predicate canon p) x (map (canon_branch canon) brs))); [|exact IH].
    intros ? ? h'. now apply case_eta_discr.
  - (* case_eta_brs *)
    intros ci p c brs brs' h. cbn [canon].
    eapply (clos_refl_map' _ _ (fun bs => tCase ci (canon_predicate canon p) (canon c) bs)).
    + intros ? ? h'. now apply case_eta_brs.
    + eapply OnOne2_map_clos_refl; [exact h|].
      intros x y [[_ IH] hc]. unfold canon_branch. rewrite hc.
      eapply (clos_refl_map' _ _
        (fun bb => {| bcontext := map canon_decl (bcontext y); bbody := bb |})); [|exact IH].
      intros ? ? h'. cbn. split; [exact h'|reflexivity].
  - (* proj_eta *)
    intros pr c c' _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tProj pr x)); [|exact IH].
    intros ? ? h. now apply proj_eta.
  - (* app_eta_l *)
    intros M1 N1 M2 _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tApp x (canon M2))); [|exact IH].
    intros ? ? h. now apply app_eta_l.
  - (* app_eta_r *)
    intros M2 N2 M1 _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tApp (canon M1) x)); [|exact IH].
    intros ? ? h. now apply app_eta_r.
  - (* prod_eta_l *)
    intros na M1 M2 N1 _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tProd (canon_na na) x (canon M2))); [|exact IH].
    intros ? ? h. now apply prod_eta_l.
  - (* prod_eta_r *)
    intros na M2 N2 M1 _ IH. cbn [canon].
    eapply (clos_refl_map' _ _ (fun x => tProd (canon_na na) (canon M1) x)); [|exact IH].
    intros ? ? h. now apply prod_eta_r.
  - (* evar_eta *)
    intros ev l l' h. cbn [canon].
    eapply (clos_refl_map' _ _ (fun ls => tEvar ev ls)).
    + intros ? ? h'. now apply evar_eta.
    + eapply OnOne2_map_clos_refl; [exact h|]. intros x y [_ IH]. exact IH.
  - (* fix_eta_ty *)
    intros mfix0 mfix1 idx h. cbn [canon].
    eapply (clos_refl_map' _ _ (fun m => tFix m idx)).
    + intros ? ? h'. now apply fix_eta_ty.
    + eapply OnOne2_map_clos_refl; [exact h|].
      intros x y [[_ IH] he]. injection he as hn hb hr. unfold canon_def.
      rewrite hn hb hr.
      eapply (clos_refl_map' _ _
        (fun ty => {| dname := canon_na (dname y); dtype := ty;
                      dbody := canon (dbody y); rarg := rarg y |})); [|exact IH].
      intros ? ? h'. cbn. split; [exact h'|reflexivity].
  - (* fix_eta_body *)
    intros mfix0 mfix1 idx h. cbn [canon].
    eapply (clos_refl_map' _ _ (fun m => tFix m idx)).
    + intros ? ? h'. now apply fix_eta_body.
    + eapply OnOne2_map_clos_refl; [exact h|].
      intros x y [[_ IH] he]. injection he as hn ht hr. unfold canon_def.
      rewrite hn ht hr.
      eapply (clos_refl_map' _ _
        (fun bo => {| dname := canon_na (dname y); dtype := canon (dtype y);
                      dbody := bo; rarg := rarg y |})); [|exact IH].
      intros ? ? h'. cbn. split; [exact h'|reflexivity].
  - (* cofix_eta_ty *)
    intros mfix0 mfix1 idx h. cbn [canon].
    eapply (clos_refl_map' _ _ (fun m => tCoFix m idx)).
    + intros ? ? h'. now apply cofix_eta_ty.
    + eapply OnOne2_map_clos_refl; [exact h|].
      intros x y [[_ IH] he]. injection he as hn hb hr. unfold canon_def.
      rewrite hn hb hr.
      eapply (clos_refl_map' _ _
        (fun ty => {| dname := canon_na (dname y); dtype := ty;
                      dbody := canon (dbody y); rarg := rarg y |})); [|exact IH].
      intros ? ? h'. cbn. split; [exact h'|reflexivity].
  - (* cofix_eta_body *)
    intros mfix0 mfix1 idx h. cbn [canon].
    eapply (clos_refl_map' _ _ (fun m => tCoFix m idx)).
    + intros ? ? h'. now apply cofix_eta_body.
    + eapply OnOne2_map_clos_refl; [exact h|].
      intros x y [[_ IH] he]. injection he as hn ht hr. unfold canon_def.
      rewrite hn ht hr.
      eapply (clos_refl_map' _ _
        (fun bo => {| dname := canon_na (dname y); dtype := canon (dtype y);
                      dbody := bo; rarg := rarg y |})); [|exact IH].
      intros ? ? h'. cbn. split; [exact h'|reflexivity].
  - (* array_eta_val *)
    intros arr value h. cbn [canon]. simp mapu_prim. unfold mapu_array_model; cbn.
    eapply (clos_refl_map' _ _
      (fun vs => tPrim (primArray; primArrayModel
        {| array_level := id (array_level arr); array_value := vs;
           array_default := canon (array_default arr);
           array_type := canon (array_type arr) |}))).
    + intros a b h'.
      exact (array_eta_val {| array_level := id (array_level arr); array_value := a;
                              array_default := canon (array_default arr);
                              array_type := canon (array_type arr) |} b h').
    + eapply OnOne2_map_clos_refl; [exact h|]. intros x y [_ IH]. exact IH.
  - (* array_eta_def *)
    intros arr d _ IH. cbn [canon]. simp mapu_prim. unfold mapu_array_model; cbn.
    eapply (clos_refl_map' _ _
      (fun x => tPrim (primArray; primArrayModel
        {| array_level := id (array_level arr); array_value := map canon (array_value arr);
           array_default := x; array_type := canon (array_type arr) |}))); [|exact IH].
    intros a b h'.
    exact (array_eta_def {| array_level := id (array_level arr);
                            array_value := map canon (array_value arr);
                            array_default := a; array_type := canon (array_type arr) |} b h').
  - (* array_eta_type *)
    intros arr ty _ IH. cbn [canon]. simp mapu_prim. unfold mapu_array_model; cbn.
    eapply (clos_refl_map' _ _
      (fun x => tPrim (primArray; primArrayModel
        {| array_level := id (array_level arr); array_value := map canon (array_value arr);
           array_default := canon (array_default arr); array_type := x |}))); [|exact IH].
    intros a b h'.
    exact (array_eta_type {| array_level := id (array_level arr);
                             array_value := map canon (array_value arr);
                             array_default := canon (array_default arr); array_type := a |} b h').
Qed.
