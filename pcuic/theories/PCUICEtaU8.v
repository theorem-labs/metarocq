(* Distributed under the terms of the MIT license. *)
(** * η alone is confluent (U6, U7, U8)

   - U6 [eta1_size]: every [eta1] step strictly decreases [PCUICSize.size], so η
     is strongly normalising.
   - U7 [eta1_local_confluence]: exact local confluence of [eta1] (no
     [upto_domain]), ported from upstream MetaRocq branch [eta_postpo],
     [pcuic/theories/PCUICEtaReduction.v] (2020 AST, not in this tree) to the 9.2
     AST and the shared [eta1] of [PCUICEtaDefs].
   - U8 [eta1_confluence_upto : U8_statement]: by Newman's lemma from U6 and U7,
     first exactly ([eta1_confluence]), then weakened to the [upto_domain] form
     with [upto_domain_refl].

   Newman is valid here because η alone is SN (U6). It is invalid for βη as a
   whole, because β is not SN. C1b is not needed: U7 is exact, and the Newman
   induction never works modulo [upto_domain].

   Port notes (what the 9.2 AST forced, relative to the 2020 proof):
   - The η-redex/inner-step critical pair needs [eta1] reducts of [lift0 1 t] to
     be lifts ([eta1_lift_inv], upstream [eta1_strengthening]). Its η-redex case
     needs [lift n (S k) B = lift0 1 t -> B = lift0 1 t'] (upstream
     [lift_lift_inv0], from [PCUICBasicStrengthening], which is not in this tree).
     Here it is derived algebraically from base [distr_lift_subst_rec],
     [simpl_subst_k] and [permute_lift] ([eta_lift_lift_inv]); [lift_inj] likewise
     from [simpl_subst_k]. No new term induction.
   - [tCase]: the 2020 single predicate congruence is two in 9.2
     ([case_eta_param] on a list, [case_eta_return]); branches are records with
     [bcontext], so the branch join relation is [on_Trel_eq eta bbody bcontext]. *)

From Stdlib Require Import ssreflect ssrbool Lia Wf_nat.
From Equations.Type Require Import Relation Relation_Properties.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICOnOne PCUICAstUtils PCUICLiftSubst
     PCUICPrimitive PCUICSize PCUICInduction PCUICReduction PCUICEtaDefs
     PCUICEtaReduction PCUICEtaConfluence PCUICEtaBetaEta.

Import ListNotations.

(** ** Small closure facts *)

Lemma u8_eta_refl x : eta x x.
Proof. apply rt_refl. Qed.

Lemma u8_eta_of1 x y : eta1 x y -> eta x y.
Proof. apply rt_step. Qed.

Lemma u8_eta_trans x y z : eta x y -> eta y z -> eta x z.
Proof. intros; eapply rt_trans; eassumption. Qed.

Lemma u8_eta_inv_step t u : eta t u -> (t = u) + (∑ t', eta1 t t' × eta t' u).
Proof.
  induction 1 as [x y h|x|x y z h1 IH1 h2 IH2].
  - right. exists y. split; [exact h|apply u8_eta_refl].
  - left. reflexivity.
  - destruct IH1 as [->|[t' [s r]]].
    + exact IH2.
    + right. exists t'. split; [exact s|exact (u8_eta_trans _ _ _ r h2)].
Qed.

Ltac u8_sum_leaf := eexists; split; first [eassumption | reflexivity].
Ltac u8_sum_solve :=
  first [ solve [u8_sum_leaf] | solve [left; u8_sum_solve] | solve [right; u8_sum_solve] ].

(** ** List lemmas *)

Lemma u8_All2_refl {A} (J : A -> A -> Type) : (forall x, J x x) -> forall l, All2 J l l.
Proof. intros Jr l. induction l; constructor; auto. Qed.

Lemma u8_OnOne2_All2 {A} (R J : A -> A -> Type) :
  (forall x, J x x) -> (forall x y, R x y -> J x y) ->
  forall l l', OnOne2 R l l' -> All2 J l l'.
Proof.
  intros Jr RJ l l' h. induction h; constructor; auto using u8_All2_refl.
Qed.

Lemma u8_OnOne2_cons_inv {A} {R : A -> A -> Type} {hd tl l} :
  OnOne2 R (hd :: tl) l ->
  (∑ hd', R hd hd' × (l = hd' :: tl)) + (∑ tl', OnOne2 R tl tl' × (l = hd :: tl')).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_OnOne2_map_inv {A} (f : A -> A) {Q : A -> A -> Type} (R : A -> A -> Type) {l l'} :
  OnOne2 Q (map f l) l' ->
  (forall x y a, Q x y -> x = f a -> ∑ b, R a b × (y = f b)) ->
  ∑ lB, OnOne2 R l lB × (l' = map f lB).
Proof.
  intros h H. induction l as [|a l IH] in l', h |- *; cbn in h.
  - depelim h.
  - destruct (u8_OnOne2_cons_inv h) as [[hd' [q ->]]|[tl' [h' ->]]].
    + destruct (H _ _ a q eq_refl) as [b [r ->]].
      exists (b :: l). split; [apply OnOne2_hd; exact r|reflexivity].
    + destruct (IH _ h') as [lB [r ->]].
      exists (a :: lB). split; [apply OnOne2_tl; exact r|reflexivity].
Qed.

(** One step on each side of the same list, with a pointwise join. *)
Lemma u8_OnOne2_join {A} (R1 R2 J : A -> A -> Type) :
  (forall x, J x x) -> (forall x y, R1 x y -> J x y) -> (forall x y, R2 x y -> J x y) ->
  forall l l1 l2,
  OnOne2 (fun x y => R1 x y × (forall z, R2 x z -> ∑ w, J y w × J z w)) l l1 ->
  OnOne2 R2 l l2 -> ∑ l3, All2 J l1 l3 × All2 J l2 l3.
Proof.
  intros Jr H1 H2 l l1 l2 h. revert l2.
  induction h as [hd hd' tl [r1 Hd]|hd tl tl' h IH]; intros l2 h2;
    destruct (u8_OnOne2_cons_inv h2) as [[hd2 [r2 ->]]|[tl2 [h2' ->]]].
  - destruct (Hd _ r2) as [w [j1 j2]].
    exists (w :: tl). split; constructor; auto using u8_All2_refl.
  - exists (hd' :: tl2). split; constructor; auto using u8_All2_refl.
    exact (u8_OnOne2_All2 R2 J Jr H2 _ _ h2').
  - exists (hd2 :: tl'). split; constructor; auto using u8_All2_refl.
    exact (u8_OnOne2_All2 _ J Jr (fun x y r => H1 x y (fst r)) _ _ h).
  - destruct (IH _ h2') as [l3 [a1 a2]].
    exists (hd :: l3). split; constructor; auto.
Qed.

Lemma u8_All2_mid {A} (J R1 R2 : A -> A -> Type) (mid : A -> A -> A) :
  (forall x y, J x y -> R1 x (mid x y) × R2 (mid x y) y) ->
  forall l l', All2 J l l' -> ∑ lm, All2 R1 l lm × All2 R2 lm l'.
Proof.
  intros H l l' a. induction a as [|x y l l' j a IH].
  - exists []. split; constructor.
  - destruct IH as [lm [a1 a2]]. destruct (H x y j) as [r1 r2].
    exists (mid x y :: lm). split; constructor; assumption.
Qed.

Lemma u8_OnOne2_size {A} (f : A -> nat) {Q : A -> A -> Type} {l l'} :
  OnOne2 Q l l' -> (forall x y, Q x y -> f y < f x) -> list_size f l' < list_size f l.
Proof.
  intros h H. induction h as [hd hd' tl q|hd tl tl' h IH]; cbn.
  - pose proof (H _ _ q). lia.
  - lia.
Qed.

(** ** U6: η is strongly normalising *)

Ltac u8_size_lia :=
  cbn in *; unfold predicate_size, context_size, branch_size, mfixpoint_size, def_size in *;
  cbn in *; lia.

Lemma eta1_size t u : eta1 t u -> PCUICSize.size u < PCUICSize.size t.
Proof.
  intros h. revert t u h.
  apply (eta1_ind_all (fun t u => PCUICSize.size u < PCUICSize.size t)).
  - intros na t A. cbn. rewrite size_lift. lia.
  - intros na M M' N _ IH. u8_size_lia.
  - intros na M M' N _ IH. u8_size_lia.
  - intros na b t b' r _ IH. u8_size_lia.
  - intros na b t b' r _ IH. u8_size_lia.
  - intros na b t b' r _ IH. u8_size_lia.
  - intros ci p params' c brs X.
    pose proof (u8_OnOne2_size PCUICSize.size X (fun x y q => snd q)) as H.
    u8_size_lia.
  - intros ci p preturn' c brs _ IH.
    u8_size_lia.
  - intros ci p c c' brs _ IH. u8_size_lia.
  - intros ci p c brs brs' X.
    have H : list_size (branch_size PCUICSize.size) brs' <
             list_size (branch_size PCUICSize.size) brs.
    { apply (u8_OnOne2_size _ X). intros x y [[_ hs] e].
      unfold branch_size. rewrite e. lia. }
    u8_size_lia.
  - intros pr c c' _ IH. u8_size_lia.
  - intros M1 N1 M2 _ IH. u8_size_lia.
  - intros M2 N2 M1 _ IH. u8_size_lia.
  - intros na M1 M2 N1 _ IH. u8_size_lia.
  - intros na M2 N2 M1 _ IH. u8_size_lia.
  - intros ev l l' X.
    pose proof (u8_OnOne2_size PCUICSize.size X (fun x y q => snd q)) as H.
    u8_size_lia.
  - intros m0 m1 idx X.
    have H : list_size (def_size PCUICSize.size) m1 < list_size (def_size PCUICSize.size) m0.
    { apply (u8_OnOne2_size _ X). intros x y [[_ hs] e].
      injection e as e1 e2 e3. unfold def_size. rewrite e2. lia. }
    u8_size_lia.
  - intros m0 m1 idx X.
    have H : list_size (def_size PCUICSize.size) m1 < list_size (def_size PCUICSize.size) m0.
    { apply (u8_OnOne2_size _ X). intros x y [[_ hs] e].
      injection e as e1 e2 e3. unfold def_size. rewrite e2. lia. }
    u8_size_lia.
  - intros m0 m1 idx X.
    have H : list_size (def_size PCUICSize.size) m1 < list_size (def_size PCUICSize.size) m0.
    { apply (u8_OnOne2_size _ X). intros x y [[_ hs] e].
      injection e as e1 e2 e3. unfold def_size. rewrite e2. lia. }
    u8_size_lia.
  - intros m0 m1 idx X.
    have H : list_size (def_size PCUICSize.size) m1 < list_size (def_size PCUICSize.size) m0.
    { apply (u8_OnOne2_size _ X). intros x y [[_ hs] e].
      injection e as e1 e2 e3. unfold def_size. rewrite e2. lia. }
    u8_size_lia.
  - intros arr value X.
    pose proof (u8_OnOne2_size PCUICSize.size X (fun x y q => snd q)) as H.
    u8_size_lia.
  - intros arr d _ IH. u8_size_lia.
  - intros arr ty _ IH. u8_size_lia.
Qed.

(** ** Lift algebra (derived from base, no term induction) *)

Lemma u8_lift_inj n k a b : lift n k a = lift n k b -> a = b.
Proof.
  intros E.
  have L : n = #|repeat (tRel 0) n| by rewrite repeat_length.
  by rewrite -(simpl_subst_k (repeat (tRel 0) n) a k n L)
             -(simpl_subst_k (repeat (tRel 0) n) b k n L) E.
Qed.

Lemma eta_lift_lift_inv n k B t :
  lift n (S k) B = lift0 1 t -> ∑ t', (B = lift0 1 t') × (t = lift n k t').
Proof.
  intros E.
  have D := distr_lift_subst_rec B [tRel 0] n 0 k.
  cbn [Nat.add map List.length] in D.
  rewrite E (simpl_subst_k [lift n k (tRel 0)] t 0 1 eq_refl) in D.
  exists (subst [tRel 0] 0 B). split.
  - rewrite -D (permute_lift _ n k 1 0 (Nat.le_0_l k)) Nat.add_1_r in E.
    exact (u8_lift_inj _ _ _ _ E).
  - symmetry. exact D.
Qed.

(** *** Head inversions of [lift] *)

Ltac u8_lift_inv_solve :=
  let E := fresh "E" in
  intros E; cbn [lift] in E; try discriminate E;
  injection E; intros; subst;
  repeat first [reflexivity | split | eexists].

Lemma u8_lift_tLambda_inv n k M na A b :
  tLambda na A b = lift n k M ->
  ∑ A0 b0, (M = tLambda na A0 b0) × (A = lift n k A0) × (b = lift n (S k) b0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tProd_inv n k M na A b :
  tProd na A b = lift n k M ->
  ∑ A0 b0, (M = tProd na A0 b0) × (A = lift n k A0) × (b = lift n (S k) b0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tLetIn_inv n k M na b t c :
  tLetIn na b t c = lift n k M ->
  ∑ b0 t0 c0, (M = tLetIn na b0 t0 c0) × (b = lift n k b0) × (t = lift n k t0)
              × (c = lift n (S k) c0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tApp_inv n k M f a :
  tApp f a = lift n k M ->
  ∑ f0 a0, (M = tApp f0 a0) × (f = lift n k f0) × (a = lift n k a0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tProj_inv n k M pr c :
  tProj pr c = lift n k M -> ∑ c0, (M = tProj pr c0) × (c = lift n k c0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tEvar_inv n k M ev l :
  tEvar ev l = lift n k M -> ∑ l0, (M = tEvar ev l0) × (l = map (lift n k) l0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tCase_inv n k M ci p c brs :
  tCase ci p c brs = lift n k M ->
  ∑ p0 c0 brs0, (M = tCase ci p0 c0 brs0) × (p = map_predicate_k id (lift n) k p0)
     × (c = lift n k c0) × (brs = map (map_branch_k (lift n) id k) brs0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tFix_inv n k M mfix idx :
  tFix mfix idx = lift n k M ->
  ∑ m0, (M = tFix m0 idx) × (mfix = map (map_def (lift n k) (lift n (#|m0| + k))) m0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tCoFix_inv n k M mfix idx :
  tCoFix mfix idx = lift n k M ->
  ∑ m0, (M = tCoFix m0 idx) × (mfix = map (map_def (lift n k) (lift n (#|m0| + k))) m0).
Proof. destruct M; u8_lift_inv_solve. Qed.

Lemma u8_lift_tRel0_inv n k a : tRel 0 = lift n (S k) a -> a = tRel 0.
Proof.
  destruct a as [j| | | | | | | | | | | | | | |]; cbn [lift]; intros E; try discriminate E.
  injection E as E. revert E.
  destruct (Nat.leb_spec0 (S k) j) as [H|H]; cbn; intros E; [lia|].
  subst j. reflexivity.
Qed.

(** [prim_val] is a dependent pair; read the array model through a function
    instead of [injection]. *)
Definition u8_prim_arr (p : prim_val term) : option (array_model term) :=
  match p.π2 with
  | primArrayModel a => Some a
  | _ => None
  end.

Definition u8_term_arr (t : term) : option (array_model term) :=
  match t with
  | tPrim p => u8_prim_arr p
  | _ => None
  end.

Lemma u8_prim_arr_inj (a b : array_model term) :
  @eq (prim_val term) (primArray; primArrayModel a) (primArray; primArrayModel b) -> a = b.
Proof. intros E. apply (f_equal u8_prim_arr) in E. cbn in E. injection E as E. exact E. Qed.

Lemma u8_lift_prim_arr_inv n k M arr :
  tPrim (primArray; primArrayModel arr) = lift n k M ->
  ∑ a, (M = tPrim (primArray; primArrayModel a)) × (arr = mapu_array_model id (lift n k) a).
Proof.
  intros E. apply (f_equal u8_term_arr) in E.
  destruct M as [| | | | | | | | | | | | | | |pr]; cbn in E; try discriminate E.
  destruct pr as [tg m]; destruct m as [i|f|s|a]; cbn in E; try discriminate E.
  injection E as ->. exists a. split; reflexivity.
Qed.

(** ** [eta1] reducts of a lift are lifts (upstream [eta1_strengthening]) *)

Lemma eta1_lift_inv n t u : eta1 t u ->
  forall k M, t = lift n k M -> ∑ N, eta1 M N × (u = lift n k N).
Proof.
  intros h. revert t u h.
  apply (eta1_ind_all (fun t u => forall k M, t = lift n k M -> ∑ N, eta1 M N × (u = lift n k N))).
  - (* eta_red *)
    intros na t A k M E.
    destruct (u8_lift_tLambda_inv _ _ _ _ _ _ E) as (A0 & b0 & -> & -> & Eb).
    destruct (u8_lift_tApp_inv _ _ _ _ _ Eb) as (f0 & a0 & -> & Ef & Ea).
    rewrite (u8_lift_tRel0_inv _ _ _ Ea).
    destruct (eta_lift_lift_inv n k f0 t (eq_sym Ef)) as (t' & -> & ->).
    exists t'. split; [apply eta_red|reflexivity].
  - intros na M M' N h IH k M0 E.
    destruct (u8_lift_tLambda_inv _ _ _ _ _ _ E) as (A0 & b0 & -> & -> & ->).
    destruct (IH k A0 eq_refl) as (N1 & h1 & ->).
    exists (tLambda na N1 b0). split; [apply abs_eta_l; exact h1|reflexivity].
  - intros na M M' N h IH k M0 E.
    destruct (u8_lift_tLambda_inv _ _ _ _ _ _ E) as (A0 & b0 & -> & -> & ->).
    destruct (IH (S k) b0 eq_refl) as (N1 & h1 & ->).
    exists (tLambda na A0 N1). split; [apply abs_eta_r; exact h1|reflexivity].
  - intros na b t b' r h IH k M E.
    destruct (u8_lift_tLetIn_inv _ _ _ _ _ _ _ E) as (b0 & t0 & c0 & -> & -> & -> & ->).
    destruct (IH k b0 eq_refl) as (r0 & h1 & ->).
    exists (tLetIn na r0 t0 c0). split; [apply letin_eta_def; exact h1|reflexivity].
  - intros na b t b' r h IH k M E.
    destruct (u8_lift_tLetIn_inv _ _ _ _ _ _ _ E) as (b0 & t0 & c0 & -> & -> & -> & ->).
    destruct (IH k t0 eq_refl) as (r0 & h1 & ->).
    exists (tLetIn na b0 r0 c0). split; [apply letin_eta_ty; exact h1|reflexivity].
  - intros na b t b' r h IH k M E.
    destruct (u8_lift_tLetIn_inv _ _ _ _ _ _ _ E) as (b0 & t0 & c0 & -> & -> & -> & ->).
    destruct (IH (S k) c0 eq_refl) as (r0 & h1 & ->).
    exists (tLetIn na b0 t0 r0). split; [apply letin_eta_body; exact h1|reflexivity].
  - (* case_eta_param *)
    intros ci p params' c brs X k M E.
    destruct (u8_lift_tCase_inv _ _ _ _ _ _ _ E) as (p0 & c0 & brs0 & -> & -> & -> & ->).
    change (pparams (map_predicate_k id (lift n) k p0)) with (map (lift n k) (pparams p0)) in X.
    destruct (u8_OnOne2_map_inv (lift n k) eta1 X (fun x y a q e => snd q k a e))
      as (l1 & hl & ->).
    exists (tCase ci (set_pparams p0 l1) c0 brs0).
    split; [apply case_eta_param; exact hl|reflexivity].
  - (* case_eta_return *)
    intros ci p preturn' c brs h IH k M E.
    destruct (u8_lift_tCase_inv _ _ _ _ _ _ _ E) as (p0 & c0 & brs0 & -> & -> & -> & ->).
    destruct (IH (#|pcontext p0| + k) (preturn p0) eq_refl) as (r0 & h1 & ->).
    exists (tCase ci (set_preturn p0 r0) c0 brs0).
    split; [apply case_eta_return; exact h1|reflexivity].
  - (* case_eta_discr *)
    intros ci p c c' brs h IH k M E.
    destruct (u8_lift_tCase_inv _ _ _ _ _ _ _ E) as (p0 & c0 & brs0 & -> & -> & -> & ->).
    destruct (IH k c0 eq_refl) as (c1 & h1 & ->).
    exists (tCase ci p0 c1 brs0). split; [apply case_eta_discr; exact h1|reflexivity].
  - (* case_eta_brs *)
    intros ci p c brs brs' X k M E.
    destruct (u8_lift_tCase_inv _ _ _ _ _ _ _ E) as (p0 & c0 & brs0 & -> & -> & -> & ->).
    destruct (u8_OnOne2_map_inv (map_branch_k (lift n) id k)
                (on_Trel_eq eta1 bbody bcontext) X) as (l1 & hl & ->).
    { intros x y a [[hx Px] ex] ->.
      destruct (Px (#|bcontext a| + k) (bbody a) eq_refl) as (b0 & hb & eb).
      exists {| bcontext := bcontext a; bbody := b0 |}.
      split; [split; [exact hb|reflexivity]|].
      destruct y as [cy yb]; cbn in *. subst. reflexivity. }
    exists (tCase ci p0 c0 l1). split; [apply case_eta_brs; exact hl|reflexivity].
  - intros pr c c' h IH k M E.
    destruct (u8_lift_tProj_inv _ _ _ _ _ E) as (c0 & -> & ->).
    destruct (IH k c0 eq_refl) as (c1 & h1 & ->).
    exists (tProj pr c1). split; [apply proj_eta; exact h1|reflexivity].
  - intros M1 N1 M2 h IH k M E.
    destruct (u8_lift_tApp_inv _ _ _ _ _ E) as (f0 & a0 & -> & -> & ->).
    destruct (IH k f0 eq_refl) as (f1 & h1 & ->).
    exists (tApp f1 a0). split; [apply app_eta_l; exact h1|reflexivity].
  - intros M2 N2 M1 h IH k M E.
    destruct (u8_lift_tApp_inv _ _ _ _ _ E) as (f0 & a0 & -> & -> & ->).
    destruct (IH k a0 eq_refl) as (a1 & h1 & ->).
    exists (tApp f0 a1). split; [apply app_eta_r; exact h1|reflexivity].
  - intros na M1 M2 N1 h IH k M E.
    destruct (u8_lift_tProd_inv _ _ _ _ _ _ E) as (A0 & b0 & -> & -> & ->).
    destruct (IH k A0 eq_refl) as (A1 & h1 & ->).
    exists (tProd na A1 b0). split; [apply prod_eta_l; exact h1|reflexivity].
  - intros na M2 N2 M1 h IH k M E.
    destruct (u8_lift_tProd_inv _ _ _ _ _ _ E) as (A0 & b0 & -> & -> & ->).
    destruct (IH (S k) b0 eq_refl) as (b1 & h1 & ->).
    exists (tProd na A0 b1). split; [apply prod_eta_r; exact h1|reflexivity].
  - intros ev l l' X k M E.
    destruct (u8_lift_tEvar_inv _ _ _ _ _ E) as (l0 & -> & ->).
    destruct (u8_OnOne2_map_inv (lift n k) eta1 X (fun x y a q e => snd q k a e))
      as (l1 & hl & ->).
    exists (tEvar ev l1). split; [apply evar_eta; exact hl|reflexivity].
  - (* fix_eta_ty *)
    intros mfix0 mfix1 idx X k M E.
    destruct (u8_lift_tFix_inv _ _ _ _ _ E) as (m0 & -> & ->).
    destruct (u8_OnOne2_map_inv (map_def (lift n k) (lift n (#|m0| + k)))
                (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) X)
      as (l1 & hl & ->).
    { intros x y a [[hx Px] ex] ->.
      destruct (Px k (dtype a) eq_refl) as (b0 & hb & eb).
      exists {| dname := dname a; dtype := b0; dbody := dbody a; rarg := rarg a |}.
      split; [split; [exact hb|reflexivity]|].
      destruct y as [yn yt yb yr]; cbn in *. injection ex as e1 e2 e3. subst. reflexivity. }
    exists (tFix l1 idx). split; [apply fix_eta_ty; exact hl|].
    cbn [lift]. rewrite (OnOne2_length hl). reflexivity.
  - (* fix_eta_body *)
    intros mfix0 mfix1 idx X k M E.
    destruct (u8_lift_tFix_inv _ _ _ _ _ E) as (m0 & -> & ->).
    destruct (u8_OnOne2_map_inv (map_def (lift n k) (lift n (#|m0| + k)))
                (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) X)
      as (l1 & hl & ->).
    { intros x y a [[hx Px] ex] ->.
      destruct (Px (#|m0| + k) (dbody a) eq_refl) as (b0 & hb & eb).
      exists {| dname := dname a; dtype := dtype a; dbody := b0; rarg := rarg a |}.
      split; [split; [exact hb|reflexivity]|].
      destruct y as [yn yt yb yr]; cbn in *. injection ex as e1 e2 e3. subst. reflexivity. }
    exists (tFix l1 idx). split; [apply fix_eta_body; exact hl|].
    cbn [lift]. rewrite (OnOne2_length hl). reflexivity.
  - (* cofix_eta_ty *)
    intros mfix0 mfix1 idx X k M E.
    destruct (u8_lift_tCoFix_inv _ _ _ _ _ E) as (m0 & -> & ->).
    destruct (u8_OnOne2_map_inv (map_def (lift n k) (lift n (#|m0| + k)))
                (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) X)
      as (l1 & hl & ->).
    { intros x y a [[hx Px] ex] ->.
      destruct (Px k (dtype a) eq_refl) as (b0 & hb & eb).
      exists {| dname := dname a; dtype := b0; dbody := dbody a; rarg := rarg a |}.
      split; [split; [exact hb|reflexivity]|].
      destruct y as [yn yt yb yr]; cbn in *. injection ex as e1 e2 e3. subst. reflexivity. }
    exists (tCoFix l1 idx). split; [apply cofix_eta_ty; exact hl|].
    cbn [lift]. rewrite (OnOne2_length hl). reflexivity.
  - (* cofix_eta_body *)
    intros mfix0 mfix1 idx X k M E.
    destruct (u8_lift_tCoFix_inv _ _ _ _ _ E) as (m0 & -> & ->).
    destruct (u8_OnOne2_map_inv (map_def (lift n k) (lift n (#|m0| + k)))
                (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) X)
      as (l1 & hl & ->).
    { intros x y a [[hx Px] ex] ->.
      destruct (Px (#|m0| + k) (dbody a) eq_refl) as (b0 & hb & eb).
      exists {| dname := dname a; dtype := dtype a; dbody := b0; rarg := rarg a |}.
      split; [split; [exact hb|reflexivity]|].
      destruct y as [yn yt yb yr]; cbn in *. injection ex as e1 e2 e3. subst. reflexivity. }
    exists (tCoFix l1 idx). split; [apply cofix_eta_body; exact hl|].
    cbn [lift]. rewrite (OnOne2_length hl). reflexivity.
  - (* array_eta_val *)
    intros arr value X k M E.
    destruct (u8_lift_prim_arr_inv _ _ _ _ E) as (a & -> & ->).
    change (array_value (mapu_array_model id (lift n k) a)) with (map (lift n k) (array_value a)) in X.
    destruct (u8_OnOne2_map_inv (lift n k) eta1 X (fun x y b q e => snd q k b e))
      as (l1 & hl & ->).
    exists (tPrim (primArray; primArrayModel (set_array_value a l1))).
    split; [apply array_eta_val; exact hl|reflexivity].
  - (* array_eta_def *)
    intros arr d h IH k M E.
    destruct (u8_lift_prim_arr_inv _ _ _ _ E) as (a & -> & ->).
    destruct (IH k (array_default a) eq_refl) as (d0 & hd & ->).
    exists (tPrim (primArray; primArrayModel (set_array_default a d0))).
    split; [apply array_eta_def; exact hd|reflexivity].
  - (* array_eta_type *)
    intros arr ty h IH k M E.
    destruct (u8_lift_prim_arr_inv _ _ _ _ E) as (a & -> & ->).
    destruct (IH k (array_type a) eq_refl) as (t0 & ht & ->).
    exists (tPrim (primArray; primArrayModel (set_array_type a t0))).
    split; [apply array_eta_type; exact ht|reflexivity].
Qed.

(** ** Inversions of one [eta1] step, by head, returned as data *)

Lemma u8_eta1_tRel_inv n u : eta1 (tRel n) u -> False.
Proof. intros h; depelim h. Qed.

Lemma u8_eta1_tLambda_inv na A b u : eta1 (tLambda na A b) u ->
  (∑ t, (b = tApp (lift0 1 t) (tRel 0)) × (u = t)) +
  (∑ A', eta1 A A' × (u = tLambda na A' b)) +
  (∑ b', eta1 b b' × (u = tLambda na A b')).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tLetIn_inv na b t c u : eta1 (tLetIn na b t c) u ->
  (∑ r, eta1 b r × (u = tLetIn na r t c)) +
  (∑ r, eta1 t r × (u = tLetIn na b r c)) +
  (∑ r, eta1 c r × (u = tLetIn na b t r)).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tCase_inv ci p c brs u : eta1 (tCase ci p c brs) u ->
  (∑ ps, OnOne2 eta1 (pparams p) ps × (u = tCase ci (set_pparams p ps) c brs)) +
  (∑ r, eta1 (preturn p) r × (u = tCase ci (set_preturn p r) c brs)) +
  (∑ c', eta1 c c' × (u = tCase ci p c' brs)) +
  (∑ brs', OnOne2 (on_Trel_eq eta1 bbody bcontext) brs brs' × (u = tCase ci p c brs')).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tProj_inv pr c u : eta1 (tProj pr c) u ->
  ∑ c', eta1 c c' × (u = tProj pr c').
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tApp_inv f a u : eta1 (tApp f a) u ->
  (∑ f', eta1 f f' × (u = tApp f' a)) + (∑ a', eta1 a a' × (u = tApp f a')).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tProd_inv na A B u : eta1 (tProd na A B) u ->
  (∑ A', eta1 A A' × (u = tProd na A' B)) + (∑ B', eta1 B B' × (u = tProd na A B')).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tEvar_inv ev l u : eta1 (tEvar ev l) u ->
  ∑ l', OnOne2 eta1 l l' × (u = tEvar ev l').
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tFix_inv mfix idx u : eta1 (tFix mfix idx) u ->
  (∑ m', OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix m'
         × (u = tFix m' idx)) +
  (∑ m', OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix m'
         × (u = tFix m' idx)).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tCoFix_inv mfix idx u : eta1 (tCoFix mfix idx) u ->
  (∑ m', OnOne2 (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))) mfix m'
         × (u = tCoFix m' idx)) +
  (∑ m', OnOne2 (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))) mfix m'
         × (u = tCoFix m' idx)).
Proof. intros h; depelim h; u8_sum_solve. Qed.

Lemma u8_eta1_tPrim_inv p u : eta1 (tPrim p) u ->
  ∑ arr, (p = (primArray; primArrayModel arr)) ×
    ((∑ v, OnOne2 eta1 (array_value arr) v
           × (u = tPrim (primArray; primArrayModel (set_array_value arr v)))) +
     (∑ d, eta1 (array_default arr) d
           × (u = tPrim (primArray; primArrayModel (set_array_default arr d)))) +
     (∑ ty, eta1 (array_type arr) ty
           × (u = tPrim (primArray; primArrayModel (set_array_type arr ty))))).
Proof. intros h; depelim h; (eexists; split; [reflexivity|u8_sum_solve]). Qed.

(** ** Join relations for branches and (co)fixpoint bodies *)

Definition u8_brsJ_refl (x : branch term) :
  eta (bbody x) (bbody x) × (bcontext x = bcontext x) := (u8_eta_refl _, eq_refl).

Definition u8_brsJ_of1 (x y : branch term) :
  eta1 (bbody x) (bbody y) × (bcontext x = bcontext y) ->
  eta (bbody x) (bbody y) × (bcontext x = bcontext y) :=
  fun h => (u8_eta_of1 _ _ (fst h), snd h).

Local Notation fixR_ty := (on_Trel_eq eta1 dtype (fun x => (dname x, dbody x, rarg x))).
Local Notation fixR_bo := (on_Trel_eq eta1 dbody (fun x => (dname x, dtype x, rarg x))).
Local Notation fixJ := (fun d0 d1 : def term =>
  eta (dtype d0) (dtype d1) × eta (dbody d0) (dbody d1) × (dname d0 = dname d1)
  × (rarg d0 = rarg d1)).

Lemma u8_fixJ_refl (x : def term) : fixJ x x.
Proof. cbn. repeat split; apply u8_eta_refl. Qed.

Lemma u8_fixJ_ty (x y : def term) : fixR_ty x y -> fixJ x y.
Proof.
  intros [h e]. destruct x, y; cbn in *. injection e as -> -> ->.
  repeat split; first [apply u8_eta_refl | apply u8_eta_of1; exact h].
Qed.

Lemma u8_fixJ_bo (x y : def term) : fixR_bo x y -> fixJ x y.
Proof.
  intros [h e]. destruct x, y; cbn in *. injection e as -> -> ->.
  repeat split; first [apply u8_eta_refl | apply u8_eta_of1; exact h].
Qed.

Ltac u8_fix_close :=
  repeat split; first [assumption | apply u8_eta_refl | apply u8_eta_of1; assumption].

Lemma u8_fix_pt_ty_ty (x y : def term) :
  (eta1 (dtype x) (dtype y) × (forall u2, eta1 (dtype x) u2 -> ∑ v, eta (dtype y) v × eta u2 v))
  × ((dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) ->
  fixR_ty x y × (forall z, fixR_ty x z -> ∑ w, fixJ y w × fixJ z w).
Proof.
  intros [[hx Px] ex]. split; [exact (hx, ex)|].
  intros z [hz ez]. destruct (Px _ hz) as [w0 [j1 j2]].
  exists {| dname := dname x; dtype := w0; dbody := dbody x; rarg := rarg x |}.
  destruct x, y, z; cbn in *. injection ex as -> -> ->. injection ez as -> -> ->.
  u8_fix_close.
Qed.

Lemma u8_fix_pt_ty_bo (x y : def term) :
  (eta1 (dtype x) (dtype y) × (forall u2, eta1 (dtype x) u2 -> ∑ v, eta (dtype y) v × eta u2 v))
  × ((dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) ->
  fixR_ty x y × (forall z, fixR_bo x z -> ∑ w, fixJ y w × fixJ z w).
Proof.
  intros [[hx Px] ex]. split; [exact (hx, ex)|].
  intros z [hz ez].
  exists {| dname := dname x; dtype := dtype y; dbody := dbody z; rarg := rarg x |}.
  destruct x, y, z; cbn in *. injection ex as -> -> ->. injection ez as -> -> ->.
  u8_fix_close.
Qed.

Lemma u8_fix_pt_bo_ty (x y : def term) :
  (eta1 (dbody x) (dbody y) × (forall u2, eta1 (dbody x) u2 -> ∑ v, eta (dbody y) v × eta u2 v))
  × ((dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) ->
  fixR_bo x y × (forall z, fixR_ty x z -> ∑ w, fixJ y w × fixJ z w).
Proof.
  intros [[hx Px] ex]. split; [exact (hx, ex)|].
  intros z [hz ez].
  exists {| dname := dname x; dtype := dtype z; dbody := dbody y; rarg := rarg x |}.
  destruct x, y, z; cbn in *. injection ex as -> -> ->. injection ez as -> -> ->.
  u8_fix_close.
Qed.

Lemma u8_fix_pt_bo_bo (x y : def term) :
  (eta1 (dbody x) (dbody y) × (forall u2, eta1 (dbody x) u2 -> ∑ v, eta (dbody y) v × eta u2 v))
  × ((dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) ->
  fixR_bo x y × (forall z, fixR_bo x z -> ∑ w, fixJ y w × fixJ z w).
Proof.
  intros [[hx Px] ex]. split; [exact (hx, ex)|].
  intros z [hz ez]. destruct (Px _ hz) as [w0 [j1 j2]].
  exists {| dname := dname x; dtype := dtype x; dbody := w0; rarg := rarg x |}.
  destruct x, y, z; cbn in *. injection ex as -> -> ->. injection ez as -> -> ->.
  u8_fix_close.
Qed.

Lemma u8_fix_mid_pt (x y : def term) : fixJ x y ->
  on_Trel_eq eta dtype (fun x => (dname x, dbody x, rarg x)) x
    {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |} ×
  on_Trel_eq eta dbody (fun x => (dname x, dtype x, rarg x))
    {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |} y.
Proof.
  intros (ht & hb & en & er). cbn.
  split; split; [exact ht|reflexivity|exact hb|by rewrite en er].
Qed.

Lemma u8_eta_Fix_J idx l l' : All2 fixJ l l' -> eta (tFix l idx) (tFix l' idx).
Proof.
  intros a.
  destruct (u8_All2_mid fixJ _ _
              (fun x y => {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |})
              u8_fix_mid_pt _ _ a) as [lm [a1 a2]].
  exact (u8_eta_trans _ _ _ (eta_Fix_ty idx _ _ a1) (eta_Fix_body idx _ _ a2)).
Qed.

Lemma u8_eta_CoFix_J idx l l' : All2 fixJ l l' -> eta (tCoFix l idx) (tCoFix l' idx).
Proof.
  intros a.
  destruct (u8_All2_mid fixJ _ _
              (fun x y => {| dname := dname x; dtype := dtype y; dbody := dbody x; rarg := rarg x |})
              u8_fix_mid_pt _ _ a) as [lm [a1 a2]].
  exact (u8_eta_trans _ _ _ (eta_CoFix_ty idx _ _ a1) (eta_CoFix_body idx _ _ a2)).
Qed.

(** ** U7: exact local confluence of [eta1] *)

Lemma eta1_local_confluence t u1 u2 :
  eta1 t u1 -> eta1 t u2 -> ∑ v, eta u1 v × eta u2 v.
Proof.
  intros h. revert t u1 h u2.
  apply (eta1_ind_all (fun t u1 => forall u2, eta1 t u2 -> ∑ v, eta u1 v × eta u2 v)).
  - (* eta_red *)
    intros na t A u2 h2.
    destruct (u8_eta1_tLambda_inv _ _ _ _ h2) as [[[t2 [Eb ->]]|[A' [hA ->]]]|[b' [hb ->]]].
    + injection Eb as Et. apply u8_lift_inj in Et. subst t2.
      exists t. split; apply u8_eta_refl.
    + exists t. split; [apply u8_eta_refl|apply u8_eta_of1; apply eta_red].
    + destruct (u8_eta1_tApp_inv _ _ _ hb) as [[f' [hf ->]]|[a' [ha ->]]].
      * destruct (eta1_lift_inv _ _ _ hf 0 t eq_refl) as [t' [ht ->]].
        exists t'. split; [apply u8_eta_of1; exact ht|apply u8_eta_of1; apply eta_red].
      * exfalso; exact (u8_eta1_tRel_inv _ _ ha).
  - (* abs_eta_l *)
    intros na M M' N h IH u2 h2.
    destruct (u8_eta1_tLambda_inv _ _ _ _ h2) as [[[t2 [-> ->]]|[A' [hA ->]]]|[b' [hb ->]]].
    + exists t2. split; [apply u8_eta_of1; apply eta_red|apply u8_eta_refl].
    + destruct (IH _ hA) as [v [h1 h3]].
      exists (tLambda na v N). split; apply eta_Lambda_l; assumption.
    + exists (tLambda na M' b').
      split; apply u8_eta_of1; [apply abs_eta_r|apply abs_eta_l]; assumption.
  - (* abs_eta_r *)
    intros na M M' N h IH u2 h2.
    destruct (u8_eta1_tLambda_inv _ _ _ _ h2) as [[[t2 [-> ->]]|[A' [hA ->]]]|[b' [hb ->]]].
    + destruct (u8_eta1_tApp_inv _ _ _ h) as [[f' [hf ->]]|[a' [ha ->]]].
      * destruct (eta1_lift_inv _ _ _ hf 0 t2 eq_refl) as [t' [ht ->]].
        exists t'. split; [apply u8_eta_of1; apply eta_red|apply u8_eta_of1; exact ht].
      * exfalso; exact (u8_eta1_tRel_inv _ _ ha).
    + exists (tLambda na A' M').
      split; apply u8_eta_of1; [apply abs_eta_l|apply abs_eta_r]; assumption.
    + destruct (IH _ hb) as [v [h1 h3]].
      exists (tLambda na N v). split; apply eta_Lambda_r; assumption.
  - (* letin_eta_def *)
    intros na b t b' r h IH u2 h2.
    destruct (u8_eta1_tLetIn_inv _ _ _ _ _ h2) as [[[r2 [h2' ->]]|[r2 [h2' ->]]]|[r2 [h2' ->]]].
    + destruct (IH _ h2') as [v [h1 h3]].
      exists (tLetIn na v t b'). split; apply eta_LetIn_b; assumption.
    + exists (tLetIn na r r2 b').
      split; apply u8_eta_of1; [apply letin_eta_ty|apply letin_eta_def]; assumption.
    + exists (tLetIn na r t r2).
      split; apply u8_eta_of1; [apply letin_eta_body|apply letin_eta_def]; assumption.
  - (* letin_eta_ty *)
    intros na b t b' r h IH u2 h2.
    destruct (u8_eta1_tLetIn_inv _ _ _ _ _ h2) as [[[r2 [h2' ->]]|[r2 [h2' ->]]]|[r2 [h2' ->]]].
    + exists (tLetIn na r2 r b').
      split; apply u8_eta_of1; [apply letin_eta_def|apply letin_eta_ty]; assumption.
    + destruct (IH _ h2') as [v [h1 h3]].
      exists (tLetIn na b v b'). split; apply eta_LetIn_t; assumption.
    + exists (tLetIn na b r r2).
      split; apply u8_eta_of1; [apply letin_eta_body|apply letin_eta_ty]; assumption.
  - (* letin_eta_body *)
    intros na b t b' r h IH u2 h2.
    destruct (u8_eta1_tLetIn_inv _ _ _ _ _ h2) as [[[r2 [h2' ->]]|[r2 [h2' ->]]]|[r2 [h2' ->]]].
    + exists (tLetIn na r2 t r).
      split; apply u8_eta_of1; [apply letin_eta_def|apply letin_eta_body]; assumption.
    + exists (tLetIn na b r2 r).
      split; apply u8_eta_of1; [apply letin_eta_ty|apply letin_eta_body]; assumption.
    + destruct (IH _ h2') as [v [h1 h3]].
      exists (tLetIn na b t v). split; apply eta_LetIn_c; assumption.
  - (* case_eta_param *)
    intros ci p params' c brs X u2 h2.
    have X1 : OnOne2 eta1 (pparams p) params' := OnOne2_impl X (fun _ _ q => fst q).
    destruct (u8_eta1_tCase_inv _ _ _ _ _ h2)
      as [[[[ps [hps ->]]|[r [hr ->]]]|[c' [hc ->]]]|[brs' [hb ->]]].
    + destruct (u8_OnOne2_join eta1 eta1 eta u8_eta_refl u8_eta_of1 u8_eta_of1 _ _ _ X hps)
        as [l3 [a1 a2]].
      exists (tCase ci (set_pparams p l3) c brs). split.
      * exact (eta_Case_pars ci (set_pparams p params') c brs l3 a1).
      * exact (eta_Case_pars ci (set_pparams p ps) c brs l3 a2).
    + exists (tCase ci (set_preturn (set_pparams p params') r) c brs).
      split; apply u8_eta_of1.
      * exact (case_eta_return ci (set_pparams p params') r c brs hr).
      * exact (case_eta_param ci (set_preturn p r) params' c brs X1).
    + exists (tCase ci (set_pparams p params') c' brs).
      split; apply u8_eta_of1.
      * exact (case_eta_discr ci (set_pparams p params') c c' brs hc).
      * exact (case_eta_param ci p params' c' brs X1).
    + exists (tCase ci (set_pparams p params') c brs').
      split; apply u8_eta_of1.
      * exact (case_eta_brs ci (set_pparams p params') c brs brs' hb).
      * exact (case_eta_param ci p params' c brs' X1).
  - (* case_eta_return *)
    intros ci p preturn' c brs h IH u2 h2.
    destruct (u8_eta1_tCase_inv _ _ _ _ _ h2)
      as [[[[ps [hps ->]]|[r [hr ->]]]|[c' [hc ->]]]|[brs' [hb ->]]].
    + exists (tCase ci (set_pparams (set_preturn p preturn') ps) c brs).
      split; apply u8_eta_of1.
      * exact (case_eta_param ci (set_preturn p preturn') ps c brs hps).
      * exact (case_eta_return ci (set_pparams p ps) preturn' c brs h).
    + destruct (IH _ hr) as [v [h1 h3]].
      exists (tCase ci (set_preturn p v) c brs). split.
      * exact (eta_Case_preturn ci (set_preturn p preturn') v c brs h1).
      * exact (eta_Case_preturn ci (set_preturn p r) v c brs h3).
    + exists (tCase ci (set_preturn p preturn') c' brs).
      split; apply u8_eta_of1.
      * exact (case_eta_discr ci (set_preturn p preturn') c c' brs hc).
      * exact (case_eta_return ci p preturn' c' brs h).
    + exists (tCase ci (set_preturn p preturn') c brs').
      split; apply u8_eta_of1.
      * exact (case_eta_brs ci (set_preturn p preturn') c brs brs' hb).
      * exact (case_eta_return ci p preturn' c brs' h).
  - (* case_eta_discr *)
    intros ci p c c2 brs h IH u2 h2.
    destruct (u8_eta1_tCase_inv _ _ _ _ _ h2)
      as [[[[ps [hps ->]]|[r [hr ->]]]|[c' [hc ->]]]|[brs' [hb ->]]].
    + exists (tCase ci (set_pparams p ps) c2 brs).
      split; apply u8_eta_of1.
      * exact (case_eta_param ci p ps c2 brs hps).
      * exact (case_eta_discr ci (set_pparams p ps) c c2 brs h).
    + exists (tCase ci (set_preturn p r) c2 brs).
      split; apply u8_eta_of1.
      * exact (case_eta_return ci p r c2 brs hr).
      * exact (case_eta_discr ci (set_preturn p r) c c2 brs h).
    + destruct (IH _ hc) as [v [h1 h3]].
      exists (tCase ci p v brs). split; apply eta_Case_discr; assumption.
    + exists (tCase ci p c2 brs').
      split; apply u8_eta_of1.
      * exact (case_eta_brs ci p c2 brs brs' hb).
      * exact (case_eta_discr ci p c c2 brs' h).
  - (* case_eta_brs *)
    intros ci p c brs brs' X u2 h2.
    have Xb : OnOne2 (on_Trel_eq eta1 bbody bcontext) brs brs' :=
      OnOne2_impl X (fun _ _ q => (fst (fst q), snd q)).
    destruct (u8_eta1_tCase_inv _ _ _ _ _ h2)
      as [[[[ps [hps ->]]|[r [hr ->]]]|[c' [hc ->]]]|[brs2 [hb ->]]].
    + exists (tCase ci (set_pparams p ps) c brs').
      split; apply u8_eta_of1.
      * exact (case_eta_param ci p ps c brs' hps).
      * exact (case_eta_brs ci (set_pparams p ps) c brs brs' Xb).
    + exists (tCase ci (set_preturn p r) c brs').
      split; apply u8_eta_of1.
      * exact (case_eta_return ci p r c brs' hr).
      * exact (case_eta_brs ci (set_preturn p r) c brs brs' Xb).
    + exists (tCase ci p c' brs').
      split; apply u8_eta_of1.
      * exact (case_eta_discr ci p c c' brs' hc).
      * exact (case_eta_brs ci p c' brs brs' Xb).
    + have X2 : OnOne2 (fun x y => on_Trel_eq eta1 bbody bcontext x y ×
                  (forall z, on_Trel_eq eta1 bbody bcontext x z ->
                     ∑ w, on_Trel_eq eta bbody bcontext y w × on_Trel_eq eta bbody bcontext z w))
                  brs brs'.
      { eapply OnOne2_impl; [exact X|]. intros x y [[hx Px] ex].
        split; [exact (hx, ex)|]. intros z [hz ez].
        destruct (Px _ hz) as [w0 [j1 j2]].
        exists {| bcontext := bcontext x; bbody := w0 |}.
        split; split; cbn; [exact j1|symmetry; exact ex|exact j2|symmetry; exact ez]. }
      destruct (u8_OnOne2_join _ _ _ u8_brsJ_refl u8_brsJ_of1 u8_brsJ_of1 _ _ _ X2 hb)
        as [l3 [a1 a2]].
      exists (tCase ci p c l3). split.
      * exact (eta_Case_brs ci p c brs' l3 a1).
      * exact (eta_Case_brs ci p c brs2 l3 a2).
  - (* proj_eta *)
    intros pr c c' h IH u2 h2.
    destruct (u8_eta1_tProj_inv _ _ _ h2) as [c2 [h2' ->]].
    destruct (IH _ h2') as [v [h1 h3]].
    exists (tProj pr v). split; apply eta_Proj; assumption.
  - (* app_eta_l *)
    intros M1 N1 M2 h IH u2 h2.
    destruct (u8_eta1_tApp_inv _ _ _ h2) as [[f' [hf ->]]|[a' [ha ->]]].
    + destruct (IH _ hf) as [v [h1 h3]].
      exists (tApp v M2). split; apply eta_App_l; assumption.
    + exists (tApp N1 a').
      split; apply u8_eta_of1; [apply app_eta_r|apply app_eta_l]; assumption.
  - (* app_eta_r *)
    intros M2 N2 M1 h IH u2 h2.
    destruct (u8_eta1_tApp_inv _ _ _ h2) as [[f' [hf ->]]|[a' [ha ->]]].
    + exists (tApp f' N2).
      split; apply u8_eta_of1; [apply app_eta_l|apply app_eta_r]; assumption.
    + destruct (IH _ ha) as [v [h1 h3]].
      exists (tApp M1 v). split; apply eta_App_r; assumption.
  - (* prod_eta_l *)
    intros na M1 M2 N1 h IH u2 h2.
    destruct (u8_eta1_tProd_inv _ _ _ _ h2) as [[A' [hA ->]]|[B' [hB ->]]].
    + destruct (IH _ hA) as [v [h1 h3]].
      exists (tProd na v M2). split; apply eta_Prod_l; assumption.
    + exists (tProd na N1 B').
      split; apply u8_eta_of1; [apply prod_eta_r|apply prod_eta_l]; assumption.
  - (* prod_eta_r *)
    intros na M2 N2 M1 h IH u2 h2.
    destruct (u8_eta1_tProd_inv _ _ _ _ h2) as [[A' [hA ->]]|[B' [hB ->]]].
    + exists (tProd na A' N2).
      split; apply u8_eta_of1; [apply prod_eta_l|apply prod_eta_r]; assumption.
    + destruct (IH _ hB) as [v [h1 h3]].
      exists (tProd na M1 v). split; apply eta_Prod_r; assumption.
  - (* evar_eta *)
    intros ev l l' X u2 h2.
    destruct (u8_eta1_tEvar_inv _ _ _ h2) as [l2 [hl ->]].
    destruct (u8_OnOne2_join eta1 eta1 eta u8_eta_refl u8_eta_of1 u8_eta_of1 _ _ _ X hl)
      as [l3 [a1 a2]].
    exists (tEvar ev l3). split; apply eta_Evar; assumption.
  - (* fix_eta_ty *)
    intros mfix0 mfix1 idx X u2 h2.
    destruct (u8_eta1_tFix_inv _ _ _ h2) as [[m2 [hm ->]]|[m2 [hm ->]]].
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_ty u8_fixJ_ty _ _ _
                  (OnOne2_impl X u8_fix_pt_ty_ty) hm) as [l3 [a1 a2]].
      exists (tFix l3 idx). split; apply u8_eta_Fix_J; assumption.
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_ty u8_fixJ_bo _ _ _
                  (OnOne2_impl X u8_fix_pt_ty_bo) hm) as [l3 [a1 a2]].
      exists (tFix l3 idx). split; apply u8_eta_Fix_J; assumption.
  - (* fix_eta_body *)
    intros mfix0 mfix1 idx X u2 h2.
    destruct (u8_eta1_tFix_inv _ _ _ h2) as [[m2 [hm ->]]|[m2 [hm ->]]].
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_bo u8_fixJ_ty _ _ _
                  (OnOne2_impl X u8_fix_pt_bo_ty) hm) as [l3 [a1 a2]].
      exists (tFix l3 idx). split; apply u8_eta_Fix_J; assumption.
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_bo u8_fixJ_bo _ _ _
                  (OnOne2_impl X u8_fix_pt_bo_bo) hm) as [l3 [a1 a2]].
      exists (tFix l3 idx). split; apply u8_eta_Fix_J; assumption.
  - (* cofix_eta_ty *)
    intros mfix0 mfix1 idx X u2 h2.
    destruct (u8_eta1_tCoFix_inv _ _ _ h2) as [[m2 [hm ->]]|[m2 [hm ->]]].
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_ty u8_fixJ_ty _ _ _
                  (OnOne2_impl X u8_fix_pt_ty_ty) hm) as [l3 [a1 a2]].
      exists (tCoFix l3 idx). split; apply u8_eta_CoFix_J; assumption.
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_ty u8_fixJ_bo _ _ _
                  (OnOne2_impl X u8_fix_pt_ty_bo) hm) as [l3 [a1 a2]].
      exists (tCoFix l3 idx). split; apply u8_eta_CoFix_J; assumption.
  - (* cofix_eta_body *)
    intros mfix0 mfix1 idx X u2 h2.
    destruct (u8_eta1_tCoFix_inv _ _ _ h2) as [[m2 [hm ->]]|[m2 [hm ->]]].
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_bo u8_fixJ_ty _ _ _
                  (OnOne2_impl X u8_fix_pt_bo_ty) hm) as [l3 [a1 a2]].
      exists (tCoFix l3 idx). split; apply u8_eta_CoFix_J; assumption.
    + destruct (u8_OnOne2_join _ _ _ u8_fixJ_refl u8_fixJ_bo u8_fixJ_bo _ _ _
                  (OnOne2_impl X u8_fix_pt_bo_bo) hm) as [l3 [a1 a2]].
      exists (tCoFix l3 idx). split; apply u8_eta_CoFix_J; assumption.
  - (* array_eta_val *)
    intros arr value X u2 h2.
    have X1 : OnOne2 eta1 (array_value arr) value := OnOne2_impl X (fun _ _ q => fst q).
    destruct (u8_eta1_tPrim_inv _ _ h2)
      as [arr2 [Ep [[[v2 [hv ->]]|[d2 [hd ->]]]|[ty2 [hty ->]]]]].
    all: apply u8_prim_arr_inj in Ep; subst arr2.
    + destruct (u8_OnOne2_join eta1 eta1 eta u8_eta_refl u8_eta_of1 u8_eta_of1 _ _ _ X hv)
        as [l3 [a1 a2]].
      exists (tPrim (primArray; primArrayModel (set_array_value arr l3))). split.
      * exact (eta_Array_val (set_array_value arr value) l3 a1).
      * exact (eta_Array_val (set_array_value arr v2) l3 a2).
    + exists (tPrim (primArray; primArrayModel (set_array_default (set_array_value arr value) d2))).
      split; apply u8_eta_of1.
      * exact (array_eta_def (set_array_value arr value) d2 hd).
      * exact (array_eta_val (set_array_default arr d2) value X1).
    + exists (tPrim (primArray; primArrayModel (set_array_type (set_array_value arr value) ty2))).
      split; apply u8_eta_of1.
      * exact (array_eta_type (set_array_value arr value) ty2 hty).
      * exact (array_eta_val (set_array_type arr ty2) value X1).
  - (* array_eta_def *)
    intros arr d h IH u2 h2.
    destruct (u8_eta1_tPrim_inv _ _ h2)
      as [arr2 [Ep [[[v2 [hv ->]]|[d2 [hd ->]]]|[ty2 [hty ->]]]]].
    all: apply u8_prim_arr_inj in Ep; subst arr2.
    + exists (tPrim (primArray; primArrayModel (set_array_value (set_array_default arr d) v2))).
      split; apply u8_eta_of1.
      * exact (array_eta_val (set_array_default arr d) v2 hv).
      * exact (array_eta_def (set_array_value arr v2) d h).
    + destruct (IH _ hd) as [v [h1 h3]].
      exists (tPrim (primArray; primArrayModel (set_array_default arr v))). split.
      * exact (eta_Array_default arr d v h1).
      * exact (eta_Array_default arr d2 v h3).
    + exists (tPrim (primArray; primArrayModel (set_array_type (set_array_default arr d) ty2))).
      split; apply u8_eta_of1.
      * exact (array_eta_type (set_array_default arr d) ty2 hty).
      * exact (array_eta_def (set_array_type arr ty2) d h).
  - (* array_eta_type *)
    intros arr ty h IH u2 h2.
    destruct (u8_eta1_tPrim_inv _ _ h2)
      as [arr2 [Ep [[[v2 [hv ->]]|[d2 [hd ->]]]|[ty2 [hty ->]]]]].
    all: apply u8_prim_arr_inj in Ep; subst arr2.
    + exists (tPrim (primArray; primArrayModel (set_array_value (set_array_type arr ty) v2))).
      split; apply u8_eta_of1.
      * exact (array_eta_val (set_array_type arr ty) v2 hv).
      * exact (array_eta_type (set_array_value arr v2) ty h).
    + exists (tPrim (primArray; primArrayModel (set_array_default (set_array_type arr ty) d2))).
      split; apply u8_eta_of1.
      * exact (array_eta_def (set_array_type arr ty) d2 hd).
      * exact (array_eta_type (set_array_default arr d2) ty h).
    + destruct (IH _ hty) as [v [h1 h3]].
      exists (tPrim (primArray; primArrayModel (set_array_type arr v))). split.
      * exact (eta_Array_type arr ty v h1).
      * exact (eta_Array_type arr ty2 v h3).
Qed.

(** ** Newman: SN (U6) + local confluence (U7) ⇒ confluence, EXACTLY *)

Theorem eta1_confluence t u v : eta t u -> eta t v -> ∑ w, eta u w × eta v w.
Proof.
  revert u v. pattern t.
  apply (@well_founded_induction_type term (ltof term PCUICSize.size)
           (well_founded_ltof term PCUICSize.size)).
  clear t. intros t IH u v Hu Hv.
  destruct (u8_eta_inv_step _ _ Hu) as [<-|[u1 [s1 r1]]].
  { exists v. split; [exact Hv|apply u8_eta_refl]. }
  destruct (u8_eta_inv_step _ _ Hv) as [<-|[v1 [s2 r2]]].
  { exists u. split; [apply u8_eta_refl|exact Hu]. }
  destruct (eta1_local_confluence _ _ _ s1 s2) as [w0 [h1 h2]].
  destruct (IH u1 (eta1_size _ _ s1) u w0 r1 h1) as [w1 [k1 k2]].
  destruct (IH v1 (eta1_size _ _ s2) v w1 r2 (u8_eta_trans _ _ _ h2 k2)) as [w2 [k3 k4]].
  exists w2. split; [exact (u8_eta_trans _ _ _ k1 k4)|exact k3].
Qed.

(** ** U8, exactly as pinned in [PCUICEtaBetaEta] *)

Theorem eta1_confluence_upto : U8_statement.
Proof.
  intros t u v Hu Hv.
  destruct (eta1_confluence t u v Hu Hv) as [w [Hw1 Hw2]].
  exists w, w. split; [exact Hw1|split; [exact Hw2|apply upto_domain_refl]].
Qed.
