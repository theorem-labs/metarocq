(* Distributed under the terms of the MIT license. *)

(** * [eta1] against [canon]

    [eta1_canon]      eta1 a b -> clos_refl eta1 (canon a) (canon b)
    [eta1_canonical]  canon t = t -> eta1 t u -> canon u = u

  [eta1_canon] is what makes (A)'s strong-commutation premise exact
  ([R_c_eta1_strong_commutation], [PCUICEtaCanonCommute]): an η step maps through
  [canon] to at most one η step. [eta1_canonical] is the [canon] half of "[eta1]
  preserves canonicity".

  **Why [eta1_canon] is only a reflexive closure.** A step inside a λ domain
  ([abs_eta_l]) vanishes under [canon], which erases the domain. Every other step
  survives, and the root contraction survives because [canon] commutes with
  [lift0 1] ([canon_lift]), so [canon] of an η-redex is again an η-redex. The
  converse fails, and nothing here needs it: [canon] can create η-redexes, for
  example [λx:P. (P (λy:x.y)) x] ([PCUICEtaC1b]), whose inner domain [x] blocks η
  until [canon] erases it.

  **[canon] cannot lose what the final comparison reads.** η-contraction does
  remove the application count [napp] at an under-applied [tInd]/[tConstruct]
  head, which the comparison reads. Both lemmas here are statements about
  [canon], a structural map that never reads [napp]: for example
  [λx:S. I1@{u} (tRel 0)] is canonical, η-contracts to [I1@{u}], and
  [canon (I1@{u}) = I1@{u}]. The [napp] drop is a property of the comparison
  ([compare_term_eta], [PCUICEtaFInst]), not of [canon].

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

(** ** (5b) [eta1] preserves canonicity

  The [canon] half of "[eta1] preserves [Q]"; P-SCOPE's [eta1_on_free_vars] is
  the scoping half. The one non-congruence case is the root, where a canonical
  η-redex has a canonical contractum because [lift0 1] is injective. The one
  IMPOSSIBLE case is a step inside a λ domain: a canonical λ's domain is
  [canon_dom = tSort sProp], which has no η-redex. *)

Lemma eta1_from_sort s u : eta1 (tSort s) u -> False.
Proof. intros h; inversion h. Qed.

(** A list fixed by [f] stays fixed by one [OnOne2] step whose components
    preserve fixedness. *)
Lemma OnOne2_map_fixed {A} (R : A -> A -> Type) (f : A -> A) l l' :
  OnOne2 R l l' -> map f l = l -> (forall x y, R x y -> f x = x -> f y = y) ->
  map f l' = l'.
Proof.
  intros h. induction h as [hd hd' tl r|hd tl tl' r IH]; cbn; intros e H;
    injection e as e1 e2; f_equal; eauto.
Qed.

Lemma eta1_canonical t u : canon t = t -> eta1 t u -> canon u = u.
Proof.
  intros ct h. revert ct. revert t u h.
  apply (eta1_ind_all (fun a b => canon a = a -> canon b = b)).
  - (* eta_red: a canonical η-redex has a canonical contractum *)
    intros na t A H. cbn [canon] in H. rewrite canon_lift in H.
    injection H as _ _ H. now apply lift0_1_inj.
  - (* abs_eta_l: impossible, the canonical domain is a sort *)
    intros na M M' N h _ H. cbn [canon] in H. injection H as _ eM _.
    unfold canon_dom in eM. subst M. exfalso. exact (eta1_from_sort _ _ h).
  - (* abs_eta_r *)
    intros na M M' N _ IH H. cbn [canon] in H |- *. injection H as e1 e2 e3.
    now rewrite (IH e3) e1 e2.
  - (* letin_eta_def *)
    intros na b t b' r _ IH H. cbn [canon] in H |- *. injection H as e1 e2 e3 e4.
    now rewrite (IH e2) e1 e3 e4.
  - (* letin_eta_ty *)
    intros na b t b' r _ IH H. cbn [canon] in H |- *. injection H as e1 e2 e3 e4.
    now rewrite (IH e3) e1 e2 e4.
  - (* letin_eta_body *)
    intros na b t b' r _ IH H. cbn [canon] in H |- *. injection H as e1 e2 e3 e4.
    now rewrite (IH e4) e1 e2 e3.
  - (* case_eta_param *)
    intros ci p params' c brs h H. cbn [canon] in H |- *.
    destruct p as [pars inst ctx ret]; cbn in *.
    unfold canon_predicate in H |- *; cbn in H |- *.
    injection H as ep ectx er ec ebrs.
    rewrite (OnOne2_map_fixed _ _ _ _ h ep); [intros x y [_ IH]; exact IH|].
    now rewrite ectx er ec ebrs.
  - (* case_eta_return *)
    intros ci p preturn' c brs _ IH H. cbn [canon] in H |- *.
    destruct p as [pars inst ctx ret]; cbn in *.
    unfold canon_predicate in H |- *; cbn in H |- *.
    injection H as ep ectx er ec ebrs.
    now rewrite (IH er) ep ectx ec ebrs.
  - (* case_eta_discr *)
    intros ci p c c' brs _ IH H. cbn [canon] in H |- *.
    injection H as ep ec ebrs. now rewrite (IH ec) ep ebrs.
  - (* case_eta_brs *)
    intros ci p c brs brs' h H. cbn [canon] in H |- *.
    injection H as ep ec ebrs. rewrite ep ec.
    rewrite (OnOne2_map_fixed _ _ _ _ h ebrs); [|reflexivity].
    intros x y [[_ IH] hc]. destruct x as [cx bx], y as [cy by_]; cbn in *.
    unfold canon_branch; cbn. intros e. injection e as e1 e2. subst cy.
    now rewrite e1 (IH e2).
  - (* proj_eta *)
    intros pr c c' _ IH H. cbn [canon] in H |- *. injection H as e. now rewrite (IH e).
  - (* app_eta_l *)
    intros M1 N1 M2 _ IH H. cbn [canon] in H |- *. injection H as e1 e2.
    now rewrite (IH e1) e2.
  - (* app_eta_r *)
    intros M2 N2 M1 _ IH H. cbn [canon] in H |- *. injection H as e1 e2.
    now rewrite (IH e2) e1.
  - (* prod_eta_l *)
    intros na M1 M2 N1 _ IH H. cbn [canon] in H |- *. injection H as e1 e2 e3.
    now rewrite (IH e2) e1 e3.
  - (* prod_eta_r *)
    intros na M2 N2 M1 _ IH H. cbn [canon] in H |- *. injection H as e1 e2 e3.
    now rewrite (IH e3) e1 e2.
  - (* evar_eta *)
    intros ev l l' h H. cbn [canon] in H |- *. injection H as e.
    rewrite (OnOne2_map_fixed _ _ _ _ h e); [|reflexivity].
    intros x y [_ IH]. exact IH.
  - (* fix_eta_ty *)
    intros mfix0 mfix1 idx h H. cbn [canon] in H |- *. injection H as e.
    rewrite (OnOne2_map_fixed _ _ _ _ h e); [|reflexivity].
    intros [nx tx bx rx] [ny ty by_ ry] [[_ IH] he]; cbn in *.
    injection he as -> -> ->. unfold canon_def; cbn. intros ex. injection ex as e1 e2 e3.
    now rewrite e1 (IH e2) e3.
  - (* fix_eta_body *)
    intros mfix0 mfix1 idx h H. cbn [canon] in H |- *. injection H as e.
    rewrite (OnOne2_map_fixed _ _ _ _ h e); [|reflexivity].
    intros [nx tx bx rx] [ny ty by_ ry] [[_ IH] he]; cbn in *.
    injection he as -> -> ->. unfold canon_def; cbn. intros ex. injection ex as e1 e2 e3.
    now rewrite e1 e2 (IH e3).
  - (* cofix_eta_ty *)
    intros mfix0 mfix1 idx h H. cbn [canon] in H |- *. injection H as e.
    rewrite (OnOne2_map_fixed _ _ _ _ h e); [|reflexivity].
    intros [nx tx bx rx] [ny ty by_ ry] [[_ IH] he]; cbn in *.
    injection he as -> -> ->. unfold canon_def; cbn. intros ex. injection ex as e1 e2 e3.
    now rewrite e1 (IH e2) e3.
  - (* cofix_eta_body *)
    intros mfix0 mfix1 idx h H. cbn [canon] in H |- *. injection H as e.
    rewrite (OnOne2_map_fixed _ _ _ _ h e); [|reflexivity].
    intros [nx tx bx rx] [ny ty by_ ry] [[_ IH] he]; cbn in *.
    injection he as -> -> ->. unfold canon_def; cbn. intros ex. injection ex as e1 e2 e3.
    now rewrite e1 e2 (IH e3).
  (* [array_model]'s fields are, in order: level, type, default, value. *)
  - (* array_eta_val *)
    intros [lv aty adef avals] value h H; cbn in *. simp mapu_prim in H |- *.
    unfold mapu_array_model in H |- *; cbn in H |- *.
    injection H as et ed ev.
    rewrite (OnOne2_map_fixed _ _ _ _ h ev); [intros x y [_ IH]; exact IH|].
    now rewrite et ed.
  - (* array_eta_def *)
    intros [lv aty adef avals] d _ IH H; cbn in *. simp mapu_prim in H |- *.
    unfold mapu_array_model in H |- *; cbn in H |- *.
    injection H as et ed ev. now rewrite et (IH ed) ev.
  - (* array_eta_type *)
    intros [lv aty adef avals] t' _ IH H; cbn in *. simp mapu_prim in H |- *.
    unfold mapu_array_model in H |- *; cbn in H |- *.
    injection H as et ed ev. now rewrite (IH et) ed ev.
Qed.
