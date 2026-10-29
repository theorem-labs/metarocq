(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICInduction
  PCUICLiftSubst PCUICTyping PCUICEquality PCUICCumulativity PCUICOnFreeVars
  PCUICClosed PCUICSubstitution PCUICContexts PCUICWfUniverses
  PCUICWellScopedCumulativity PCUICConversion PCUICSigmaCalculus.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv PCUICCallByNeed
  PCUICCallByNeedSound PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx
  PCUICCallByNeedSoundMemo PCUICCallByNeedSoundCong PCUICCallByNeedSoundHook
  PCUICCallByNeedSoundEval PCUICCallByNeedSoundLevel PCUICCallByNeedSoundHeapWf.
From MetaRocq.PCUIC Require PCUICConfluence PCUICOnFreeVarsConv PCUICRenameConv.
From MetaRocq.SafeChecker Require PCUICSafeConversion PCUICCallByNeedSoundReadBack.

Import CanonicalTries.

Set Default Goal Selector "1".

(** * The comparison is sound on ghost readings

  The comparison of [PCUICCallByNeed] is the mutual block [cbn_conv_slot], [cbn_conv_eval],
  [cbn_conv_term], [cbn_conv_same_code], [cbn_same_code_cells], [cbn_case_cong], [cbn_case_params],
  [cbn_case_branches], [cbn_conv_rows], [cbn_conv_value], [cbn_conv_cells]. Each function answers
  [CbnCOk (true, _, _)] for "convertible", [CbnCOk (false, _, _)] for "this rule does not apply,
  try the next one" and [CbnCFail w] for "give up". Only the [true] answer is a claim.

  The file has six parts.
  - The soundness of the machine's syntactic tests ([cbn_cmp_term_sound] and its companions),
    and the substitution fact the same-code rule rests on ([cbn_subst_agree_lift]).
  - The bodies of the comparison's functions at a successor fuel, with the functions' own
    names ([cbn_same_code_cells_eq], [cbn_case_cong_eq], ...), and the syntax of a [tCase] reading
    ([cbn_rsusp_case], [cbn_open_case_inv]).
  - Syntactic facts about codes and readings ([cbn_cg_occ_inv], [cbn_cg_subst_fresh_lift], ...).
  - The shape of the roots a machine call returns ([sk_*], [cbn_machine_skel]): renamed, never
    reshaped.
  - [Section ConvGhost]: one statement [spec_f d] per function [f], read against the ghost
    reading of [PCUICCallByNeedSoundEval.cbn_machine_sound] at the master level of
    [PCUICCallByNeedSoundLevel]; one step lemma per function; and [cbn_spec_all_ind], every
    statement at every fuel, by induction on the fuel. Its hypotheses are the section's,
    including [hrb], the read-back interface [PCUICCallByNeedSoundLevel.cbn_rb_sound] that
    [PCUICCallByNeedSoundReadBack.cbn_rb_sound_holds] proves. [cbn_spec_all_holds], after the
    section, states the result with the section's parameters.
  - Two concrete runs at the real fuel [cbn_depth] that meet the premises of [cbn_spec_term] and
    satisfy its conclusion ([cbn_witness_seam_run], [cbn_witness_true_run]).

  The comparison's inputs are read with the ghost read-back, not with one that follows the
  heap: a statement with a heap-following read-back is false at the fuel [cbn_run] uses
  ([PCUICCallByNeedCounterexamples.cbn_term_seam_false]). Conversion is squashed ([∥ _ ∥])
  because [ws_cumul_pb] lives in [Type] and the readings in [Prop]; that is also the shape
  of the hook's obligation in [PCUICTypeChecker.convert]. *)

(** ** Soundness of the machine's syntactic tests

  [cbn_cmp_term], [cbn_cmp_sort], [cbn_cmp_level_conv] and [cbn_wf_term_univs] ([PCUICCallByNeed])
  and [cbn_ceq_term] ([PCUICCallByNeedSoundMemo]) read the abstract environment [X]; here they
  are shown sound for every [Σ] that [X] stands for ([abstract_env_ext_rel X Σ]). The
  syntactic comparison is [PCUICSafeConversion.cmpb_term_correct]; neither its statement
  nor its proof uses that file's section hypothesis [normalization_in].
  [cbn_wf_term_univs_correct] uses the pointwise congruence [cbn_cs_on_universes_ext], not
  functional extensionality. *)

(** [on_universes] depends only on the values of its universe test. *)
Lemma cbn_cs_on_universes_ext (f g : Universe.t -> bool) (fc : nat -> term -> bool) :
  (forall u, f u = g u) -> forall t, on_universes f fc t = on_universes g fc t.
Proof.
  intros hfg t.
  induction t using term_forall_list_ind; cbn.
  - reflexivity.
  - reflexivity.
  - eapply All_forallb_eq_forallb; tea. now intros.
  - destruct s; cbn; auto.
  - congruence.
  - congruence.
  - congruence.
  - congruence.
  - now apply forallb_ext.
  - now apply forallb_ext.
  - now apply forallb_ext.
  - destruct X as [hpar [_ hret]].
    rewrite (forallb_ext f g hfg).
    rewrite (All_forallb_eq_forallb _ (on_universes f fc) (on_universes g fc) _ hpar);
      [|now intros].
    rewrite (All_forallb_eq_forallb _ (test_branch (fc #|puinst p|) (on_universes f fc))
      (test_branch (fc #|puinst p|) (on_universes g fc)) _ X0);
      [|intros b [_ hb]; unfold test_branch; now rewrite hb].
    congruence.
  - assumption.
  - eapply All_forallb_eq_forallb; tea. intros d [h1 h2]. now rewrite h1, h2.
  - eapply All_forallb_eq_forallb; tea. intros d [h1 h2]. now rewrite h1, h2.
  - eapply test_primu_primProp; tea.
    + intros x. apply hfg.
    + now intros.
Qed.

Section CmpSound.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (hΣ : abstract_env_ext_rel X Σ).

  Lemma cbn_wf_term_univs_correct (t : term) : cbn_wf_term_univs X_type X t = wf_universes Σ t.
  Proof.
    unfold cbn_wf_term_univs, wf_universes.
    apply cbn_cs_on_universes_ext. intros u.
    symmetry. exact (abstract_env_ext_wf_universeb_correct X hΣ u).
  Qed.

  Lemma cbn_cmp_term_wf (pb : conv_pb) (napp : nat) (t u : term) :
    cbn_cmp_term X_type X pb napp t u = true -> wf_universes Σ t /\ wf_universes Σ u.
  Proof.
    unfold cbn_cmp_term. intros h.
    apply andb_true_iff in h as [h _].
    apply andb_true_iff in h as [ht hu].
    split; rewrite <- cbn_wf_term_univs_correct; assumption.
  Qed.

  Lemma cbn_cmp_term_sound (pb : conv_pb) (napp : nat) (t u : term) :
    cbn_cmp_term X_type X pb napp t u = true -> compare_term_napp Σ Σ pb napp t u.
  Proof.
    intros h. destruct (cbn_cmp_term_wf pb napp t u h) as [ht hu].
    unfold cbn_cmp_term in h. apply andb_true_iff in h as [_ h].
    exact (fst (PCUICSafeConversion.cmpb_term_correct X_type X Σ hΣ pb napp t u ht hu) h).
  Qed.

  Lemma cbn_ceq_term_sound (t u : term) :
    wf_universes Σ t -> wf_universes Σ u ->
    cbn_ceq_term X_type X t u = true -> compare_term Σ Σ Conv t u.
  Proof.
    intros ht hu h.
    exact (fst (PCUICSafeConversion.cmpb_term_correct X_type X Σ hΣ Conv 0 t u ht hu) h).
  Qed.

  Lemma cbn_cmp_sort_sound (pb : conv_pb) (s1 s2 : sort) :
    cbn_cmp_sort X_type X pb s1 s2 = true -> compare_sort Σ pb s1 s2.
  Proof.
    unfold cbn_cmp_sort. intros h.
    apply andb_true_iff in h as [h12 h].
    apply andb_true_iff in h12 as [h1 h2].
    rewrite <- (abstract_env_ext_wf_sortb_correct X hΣ) in h1.
    rewrite <- (abstract_env_ext_wf_sortb_correct X hΣ) in h2.
    assert (w1 : wf_sort Σ s1) by (apply PCUICSafeConversion.wf_sort_iff; exact h1).
    assert (w2 : wf_sort Σ s2) by (apply PCUICSafeConversion.wf_sort_iff; exact h2).
    exact (proj2 (abstract_env_compare_sort_correct X hΣ pb s1 s2 w1 w2) h).
  Qed.

  Lemma cbn_cmp_level_conv_sound (l1 l2 : Level.t) :
    cbn_cmp_level_conv X_type X l1 l2 = true ->
    compare_universe Σ Conv (Universe.make' l1) (Universe.make' l2).
  Proof.
    unfold cbn_cmp_level_conv; cbv zeta. intros h.
    apply andb_true_iff in h as [h12 h].
    apply andb_true_iff in h12 as [h1 h2].
    rewrite <- (abstract_env_ext_wf_universeb_correct X hΣ) in h1.
    rewrite <- (abstract_env_ext_wf_universeb_correct X hΣ) in h2.
    assert (w1 : wf_universe Σ (Universe.make' l1))
      by (apply PCUICSafeConversion.wf_universe_iff; exact h1).
    assert (w2 : wf_universe Σ (Universe.make' l2))
      by (apply PCUICSafeConversion.wf_universe_iff; exact h2).
    exact (proj2 (abstract_env_compare_universe_correct X hΣ Conv _ _ w1 w2) h).
  Qed.

  Lemma cbn_cmp_level_conv_instance (u1 u2 : Instance.t) :
    forallb2 (cbn_cmp_level_conv X_type X) u1 u2 = true ->
    cmp_universe_instance (compare_universe Σ Conv) u1 u2.
  Proof.
    unfold cmp_universe_instance.
    revert u2. induction u1 as [|l1 u1 IH]; intros u2; destruct u2 as [|l2 u2]; cbn;
      try (intros e; discriminate e).
    - intros _. constructor.
    - intros h. apply andb_true_iff in h as [h hs]. constructor.
      + exact (cbn_cmp_level_conv_sound l1 l2 h).
      + exact (IH u2 hs).
  Qed.
End CmpSound.

(** ** A substitution does not look at an index the term does not use

  The same-code rule skips a position whose index does not occur in the code
  ([noccur_between i 1 t]), so what it establishes of the two environments is weaker than
  "pairwise convertible". [cbn_subst_noccur_irrel] says that this is enough: two substitutions
  that agree at every index the term uses give the same term. [cbn_subst_agree_lift] is the
  instance the read-back shape [subst ts 0 (lift N #|ts| t)] meets, where the cut of the
  lift sits above every substituted index, so the occurrence test is made on [t] itself
  ([cbn_noccur_between_lift]). *)

Lemma cbn_noccA_forallb_map {A B : Type} (P : A -> Type) (p : A -> bool) (q : B -> bool)
  (f : A -> B) (l : list A) :
  All P l -> (forall x, P x -> p x = true -> q (f x) = true) ->
  forallb p l = true -> forallb q (map f l) = true.
Proof.
  intros HA Hf. induction HA as [|x l Px HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff. split.
  - exact (Hf x Px H1).
  - exact (IH H2).
Qed.

Lemma cbn_noccA_map_ext {A B : Type} (P : A -> Type) (f g : A -> B) (l : list A) :
  All P l -> (forall x, In x l -> P x -> f x = g x) -> map f l = map g l.
Proof.
  intros HA. induction HA as [|x l Px HA IH]; cbn; intros H; [reflexivity|].
  f_equal.
  - apply H; [left; reflexivity | exact Px].
  - apply IH. intros y Hy Py. apply H; [right; exact Hy | exact Py].
Qed.

Lemma cbn_noccA_forallb_false {A : Type} (p : A -> bool) (l : list A) (x : A) :
  In x l -> p x = false -> forallb p l = false.
Proof.
  intros Hin Hx. induction l as [|y l IH]; cbn in Hin |- *; [contradiction|].
  destruct Hin as [Hy|Hin].
  - subst y. rewrite Hx. reflexivity.
  - rewrite (IH Hin). apply Bool.andb_false_r.
Qed.

(* [cbn_noccA_false H] closes a goal [c = false] where [c] is a conjunction ([andb]) one of
   whose conjuncts is, up to conversion, the left side of [H : _ = false]. *)
Local Ltac cbn_noccA_false H :=
  first [ exact H
        | apply Bool.andb_false_iff;
          first [ left; cbn_noccA_false H | right; cbn_noccA_false H ] ].

(* [cbn_noccA_sub Hj] moves the agreement hypothesis [Hj] of a term to one of its direct
   subterms: if the subterm uses an index then so does the term. *)
Local Ltac cbn_noccA_sub Hj :=
  let j := fresh "j" in
  let Hj1 := fresh "Hj1" in
  let Hj2 := fresh "Hj2" in
  intros j Hj1 Hj2; apply Hj; [exact Hj1 | cbn [noccur_between]; cbn_noccA_false Hj2].

Lemma cbn_noccur_between_lift (n k i : nat) (t : term) :
  i < k -> noccur_between i 1 t = true -> noccur_between i 1 (lift n k t) = true.
Proof.
  revert n k i. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct (K <=? r) eqn:E; [|exact H].
    apply Nat.leb_le in E.
    apply Bool.orb_true_iff; right; apply Nat.leb_le; lia.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl N K I HIK H. cbn [lift noccur_between] in H |- *.
    refine (cbn_noccA_forallb_map _ _ _ _ _ Hl _ H). intros x Px Hx. apply Px; assumption.
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; first [assumption | lia].
  - (* tLambda *)
    intros na A IHA B IHB N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; first [assumption | lia].
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + apply IHb; first [assumption | lia].
    + apply IHty; first [assumption | lia].
    + apply IHB; first [assumption | lia].
  - (* tApp *)
    intros u v IHu IHv N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHu | apply IHv]; first [assumption | lia].
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p Hp c IHc brs Hbrs N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct Hp as [Hpar [Hctx Hret]].
    unfold test_predicate_k, map_predicate_k in H |- *. simpl in H |- *.
    apply Bool.andb_true_iff in H as [H Hbr].
    apply Bool.andb_true_iff in H as [H Hc].
    apply Bool.andb_true_iff in H as [H Hr].
    apply Bool.andb_true_iff in H as [Hpa Hcx].
    apply Bool.andb_true_iff; split.
    2:{ refine (cbn_noccA_forallb_map _ _ _ _ _ Hbrs _ Hbr).
        intros br [Pctx Pbody] Hb. unfold test_branch_k, map_branch_k in Hb |- *.
        simpl in Hb |- *. cbv [id].
        rewrite length_map.
        apply Bool.andb_true_iff in Hb as [Hb1 Hb2].
        apply Bool.andb_true_iff; split; [exact Hb1 | apply Pbody; [lia | exact Hb2]]. }
    apply Bool.andb_true_iff; split.
    2:{ apply IHc; assumption. }
    apply Bool.andb_true_iff; split.
    2:{ apply Hret; [lia | exact Hr]. }
    apply Bool.andb_true_iff; split.
    2:{ rewrite length_map. exact Hcx. }
    refine (cbn_noccA_forallb_map _ _ _ _ _ Hpar _ Hpa). intros x Px Hx. apply Px; assumption.
  - (* tProj *)
    intros pr c IHc N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply IHc; assumption.
  - (* tFix *)
    intros mfix idx Hm N K I HIK H. cbn [lift noccur_between] in H |- *.
    rewrite length_map.
    refine (cbn_noccA_forallb_map _ _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def, map_def in Hd |- *. simpl in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; first [assumption | lia].
  - (* tCoFix *)
    intros mfix idx Hm N K I HIK H. cbn [lift noccur_between] in H |- *.
    rewrite length_map.
    refine (cbn_noccA_forallb_map _ _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def, map_def in Hd |- *. simpl in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; first [assumption | lia].
  - (* tPrim *)
    intros prim Hprim N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cbn_noccA_forallb_map _ _ _ _ _ Hval _ H1). intros y Py Hy. apply Py; assumption.
    + apply Hdef; assumption.
    + apply Hty; assumption.
Qed.

Lemma cbn_subst_noccur_irrel (l1 l2 : list term) :
  #|l1| = #|l2| ->
  forall (b : term) (k : nat),
    (forall j, j < #|l1| -> noccur_between (k + j) 1 b = false ->
               nth_error l1 j = nth_error l2 j) ->
    subst l1 k b = subst l2 k b.
Proof.
  intros Hlen b. elim b using term_forall_list_ind.
  - (* tRel *)
    intros r k Hj. cbn [subst].
    destruct (k <=? r) eqn:E; [|reflexivity].
    apply Nat.leb_le in E.
    destruct (Nat.lt_ge_cases (r - k) #|l1|) as [Hlt|Hge].
    + assert (Heq : nth_error l1 (r - k) = nth_error l2 (r - k)).
      { apply Hj; [exact Hlt|]. cbn [noccur_between].
        apply Bool.orb_false_iff; split; [apply Nat.ltb_ge | apply Nat.leb_gt]; lia. }
      rewrite Heq. rewrite Hlen. reflexivity.
    + assert (E1 : nth_error l1 (r - k) = None) by (apply nth_error_None; lia).
      assert (E2 : nth_error l2 (r - k) = None) by (apply nth_error_None; lia).
      rewrite E1. rewrite E2. rewrite Hlen. reflexivity.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k Hj. cbn [subst].
    f_equal. apply (cbn_noccA_map_ext _ _ _ _ Hl). intros x Hin Px. apply Px.
    intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
    exact (cbn_noccA_forallb_false _ _ _ Hin Hj2).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k Hj. cbn [subst].
    f_equal; [apply IHA | apply IHB]; cbn_noccA_sub Hj.
  - (* tLambda *)
    intros na A IHA B IHB k Hj. cbn [subst].
    f_equal; [apply IHA | apply IHB]; cbn_noccA_sub Hj.
  - (* tLetIn *)
    intros na t IHt ty IHty B IHB k Hj. cbn [subst].
    f_equal; [apply IHt | apply IHty | apply IHB]; cbn_noccA_sub Hj.
  - (* tApp *)
    intros u v IHu IHv k Hj. cbn [subst].
    f_equal; [apply IHu | apply IHv]; cbn_noccA_sub Hj.
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p Hp c IHc brs Hbrs k Hj. cbn [subst].
    destruct Hp as [Hpar [Hctx Hret]].
    f_equal; [unfold map_predicate_k; f_equal | apply IHc; cbn_noccA_sub Hj | ].
    + (* pparams *)
      apply (cbn_noccA_map_ext _ _ _ _ Hpar). intros x Hin Px. apply Px.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      unfold test_predicate_k.
      pose proof (cbn_noccA_forallb_false _ _ _ Hin Hj2) as Hf. cbn_noccA_false Hf.
    + (* preturn *)
      apply Hret. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      unfold test_predicate_k.
      rewrite <- Nat.add_assoc in Hj2. cbn_noccA_false Hj2.
    + (* branches *)
      apply (cbn_noccA_map_ext _ _ _ _ Hbrs). intros br Hin [Pctx Pbody].
      unfold map_branch_k. f_equal. apply Pbody.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hb : test_branch_k p (fun k0 => noccur_between k0 1) (k + j) br = false)
        by (unfold test_branch_k; cbn_noccA_false Hj2).
      pose proof (cbn_noccA_forallb_false _ _ _ Hin Hb) as Hf. cbn_noccA_false Hf.
  - (* tProj *)
    intros pr c IHc k Hj. cbn [subst].
    f_equal; apply IHc; cbn_noccA_sub Hj.
  - (* tFix *)
    intros mfix idx Hm k Hj. cbn [subst].
    f_equal. apply (cbn_noccA_map_ext _ _ _ _ Hm). intros d Hin [Pty Pbody].
    unfold map_def. f_equal.
    + apply Pty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; cbn_noccA_false Hj2).
      exact (cbn_noccA_forallb_false _ _ _ Hin Hd).
    + apply Pbody. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; cbn_noccA_false Hj2).
      exact (cbn_noccA_forallb_false _ _ _ Hin Hd).
  - (* tCoFix *)
    intros mfix idx Hm k Hj. cbn [subst].
    f_equal. apply (cbn_noccA_map_ext _ _ _ _ Hm). intros d Hin [Pty Pbody].
    unfold map_def. f_equal.
    + apply Pty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; cbn_noccA_false Hj2).
      exact (cbn_noccA_forallb_false _ _ _ Hin Hd).
    + apply Pbody. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; cbn_noccA_false Hj2).
      exact (cbn_noccA_forallb_false _ _ _ Hin Hd).
  - (* tPrim *)
    intros prim Hprim k Hj. cbn [subst].
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    assert (E1 : subst l1 k (array_type a) = subst l2 k (array_type a)).
    { apply Hty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn. cbn_noccA_false Hj2. }
    assert (E2 : subst l1 k (array_default a) = subst l2 k (array_default a)).
    { apply Hdef. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn. cbn_noccA_false Hj2. }
    assert (E3 : map (subst l1 k) (array_value a) = map (subst l2 k) (array_value a)).
    { apply (cbn_noccA_map_ext _ _ _ _ Hval). intros y Hin Py. apply Py.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn.
      pose proof (cbn_noccA_forallb_false _ _ _ Hin Hj2) as Hf. cbn_noccA_false Hf. }
    unfold mapu_array_model.
    rewrite E1. rewrite E2. rewrite E3. reflexivity.
Qed.

Lemma cbn_subst_agree_lift (l1 l2 : list term) (N m : nat) (t : term) :
  #|l1| = #|l2| -> m = #|l1| ->
  (forall j, j < #|l1| -> noccur_between j 1 t = false ->
             nth_error l1 j = nth_error l2 j) ->
  subst l1 0 (lift N m t) = subst l2 0 (lift N m t).
Proof.
  intros Hlen Hm Hag.
  apply cbn_subst_noccur_irrel; [exact Hlen|].
  intros j Hj Hnoc. apply Hag; [exact Hj|].
  destruct (noccur_between j 1 t) eqn:E; [|reflexivity].
  exfalso.
  assert (Hl : noccur_between (0 + j) 1 (lift N m t) = true)
    by (apply cbn_noccur_between_lift; [lia | exact E]).
  rewrite Hl in Hnoc. discriminate.
Qed.

(** ** The comparison's bodies at a successor fuel, and the syntax of a [tCase] reading

  The bodies are written with the names of the comparison's functions: [cbn] would replace
  them by the raw mutual fixpoint. *)

Section ConvEqs.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat).

  Local Notation cbn_xpred0 := (fun _ : nat => false) (only parsing).
  Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).

  Lemma cbn_pfd_push_fresh_O (lvl : nat) (e1 e2 : cbn_env) (rs : list cbn_root) (s : cbn_state) :
    cbn_push_fresh 0 lvl e1 e2 rs s = CbnCOk ((lvl, e1, e2), rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_pfd_push_fresh_S (m lvl : nat) (e1 e2 : cbn_env) (rs : list cbn_root) (s : cbn_state) :
    cbn_push_fresh (S m) lvl e1 e2 rs s =
    match cbn_alloc (CbnCDone (CbnVNeu (CbnNVar lvl) [])) (CbnRE e1 :: CbnRE e2 :: rs) s with
    | CbnCOk (x, rs1, s1) =>
      match rs1 with
      | CbnRE e1' :: CbnRE e2' :: rs2 =>
        cbn_push_fresh m (S lvl) (cbn_env_push (CbnSAddr x) e1')
          (cbn_env_push (CbnSAddr x) e2') rs2 s1
      | _ => CbnCFail CbnWRoots
      end
    | CbnCFail w => CbnCFail w
    end.
  Proof. reflexivity. Qed.

  Lemma cbn_same_code_cells_eq (k : unit -> cbn_fuel) (lvl : nat) (t : term) (i : nat)
      (l1 l2 : list cbn_slot) (rs : list cbn_root) (s : cbn_state) :
    cbn_same_code_cells X_type X Γ nctx (CbnFS k) lvl t i l1 l2 rs s
    = match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | x1 :: l1, x2 :: l2 =>
        if cbn_slot_same x1 x2 || noccur_between i 1 t
        then cbn_same_code_cells X_type X Γ nctx (k tt) lvl t (S i) l1 l2 rs s
        else
          match cbn_conv_slot X_type X Γ nctx (k tt) lvl Conv x1 x2
                  (CbnRSk l1 :: CbnRSk l2 :: rs) s with
          | CbnCOk (true, rs, s) =>
            match rs with
            | CbnRSk l1 :: CbnRSk l2 :: rs =>
              cbn_same_code_cells X_type X Γ nctx (k tt) lvl t (S i) l1 l2 rs s
            | _ => CbnCFail CbnWRoots
            end
          | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
          | CbnCFail w => CbnCFail w
          end
      | _, _ => CbnCOk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma cbn_conv_same_code_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code)
      (e2 : cbn_env) (c2 : cbn_code) (rs : list cbn_root) (s : cbn_state) :
    cbn_conv_same_code X_type X Γ nctx (CbnFS k) lvl e1 c1 e2 c2 rs s
    = (if (e1.(cbn_ev_goff) == e2.(cbn_ev_goff)) && (e1.(cbn_ev_nvals) == e2.(cbn_ev_nvals)) then
         let (b, s) := cbn_code_eq X_type X c1 c2 s in
         if b then cbn_same_code_cells X_type X Γ nctx (k tt) lvl (c1.(cbn_c_term)) 0
                     (e1.(cbn_ev_vals)) (e2.(cbn_ev_vals)) rs s
         else CbnCOk (false, rs, s)
       else CbnCOk (false, rs, s)).
  Proof. reflexivity. Qed.

  Lemma cbn_case_params_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code)
      (e2 : cbn_env) (c2 : cbn_code) (i : N) (l1 l2 : list term) (rs : list cbn_root)
      (s : cbn_state) :
    cbn_case_params X_type X Γ nctx (CbnFS k) lvl e1 c1 e2 c2 i l1 l2 rs s
    = match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | t1 :: l1, t2 :: l2 =>
        match cbn_conv_term X_type X Γ nctx (k tt) lvl Conv
                e1 (cbn_child c1 (cbn_case_param_step i) t1)
                e2 (cbn_child c2 (cbn_case_param_step i) t2) (CbnRE e1 :: CbnRE e2 :: rs) s with
        | CbnCOk (true, rs, s) =>
          match rs with
          | CbnRE e1 :: CbnRE e2 :: rs =>
            cbn_case_params X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 (N.succ i)
              l1 l2 rs s
          | _ => CbnCFail CbnWRoots
          end
        | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
        | CbnCFail w => CbnCFail w
        end
      | _, _ => CbnCOk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma cbn_case_branches_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code)
      (e2 : cbn_env) (c2 : cbn_code) (i : N) (l1 l2 : list (branch term)) (rs : list cbn_root)
      (s : cbn_state) :
    cbn_case_branches X_type X Γ nctx (CbnFS k) lvl e1 c1 e2 c2 i l1 l2 rs s
    = match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | b1 :: l1, b2 :: l2 =>
        if cbn_case_ctx_ok b1.(bcontext) b2.(bcontext) then
          match cbn_push_fresh #|b1.(bcontext)| lvl e1 e2 (CbnRE e1 :: CbnRE e2 :: rs) s with
          | CbnCOk (r, rs, s) =>
            let '(lvlb, eb1, eb2) := r in
            match cbn_conv_term X_type X Γ nctx (k tt) lvlb Conv
                    eb1 (cbn_child c1 (cbn_case_branch_step i) b1.(bbody))
                    eb2 (cbn_child c2 (cbn_case_branch_step i) b2.(bbody)) rs s with
            | CbnCOk (true, rs, s) =>
              match rs with
              | CbnRE e1 :: CbnRE e2 :: rs =>
                cbn_case_branches X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 (N.succ i)
                  l1 l2 rs s
              | _ => CbnCFail CbnWRoots
              end
            | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
            | CbnCFail w => CbnCFail w
            end
          | CbnCFail w => CbnCFail w
          end
        else CbnCOk (false, rs, s)
      | _, _ => CbnCOk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma cbn_case_cong_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code)
      (e2 : cbn_env) (c2 : cbn_code) (rs : list cbn_root) (s : cbn_state) :
    cbn_case_cong X_type X Γ nctx (CbnFS k) lvl e1 c1 e2 c2 rs s
    = match c1.(cbn_c_term), c2.(cbn_c_term) with
      | tCase ci1 p1 sc1 brs1, tCase ci2 p2 sc2 brs2 =>
        if cbn_case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|)
           && (#|p1.(pparams)| == #|p2.(pparams)|)
           && forallb2 (cbn_cmp_level_conv X_type X) p1.(puinst) p2.(puinst)
           && cbn_case_ctx_ok p1.(pcontext) p2.(pcontext)
        then
          match cbn_case_params X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 0%N
                  p1.(pparams) p2.(pparams) (CbnRE e1 :: CbnRE e2 :: rs) s with
          | CbnCOk (true, rs, s) =>
            match rs with
            | CbnRE e1 :: CbnRE e2 :: rs =>
              match cbn_push_fresh #|p1.(pcontext)| lvl e1 e2 (CbnRE e1 :: CbnRE e2 :: rs) s with
              | CbnCOk (r, rs, s) =>
                let '(lvlr, er1, er2) := r in
                match cbn_conv_term X_type X Γ nctx (k tt) lvlr Conv
                        er1 (cbn_child c1 1 p1.(preturn)) er2
                          (cbn_child c2 1 p2.(preturn)) rs s with
                | CbnCOk (true, rs, s) =>
                  match rs with
                  | CbnRE e1 :: CbnRE e2 :: rs =>
                    match cbn_conv_term X_type X Γ nctx (k tt) lvl Conv
                            e1 (cbn_child c1 0 sc1) e2 (cbn_child c2 0 sc2)
                              (CbnRE e1 :: CbnRE e2 :: rs) s with
                    | CbnCOk (true, rs, s) =>
                      match rs with
                      | CbnRE e1 :: CbnRE e2 :: rs =>
                        cbn_case_branches X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 0%N
                          brs1 brs2 rs s
                      | _ => CbnCFail CbnWRoots
                      end
                    | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
                    | CbnCFail w => CbnCFail w
                    end
                  | _ => CbnCFail CbnWRoots
                  end
                | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
                | CbnCFail w => CbnCFail w
                end
              | CbnCFail w => CbnCFail w
              end
            | _ => CbnCFail CbnWRoots
            end
          | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
          | CbnCFail w => CbnCFail w
          end
        else CbnCOk (false, rs, s)
      | _, _ => CbnCOk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma cbn_cc_forallb_Forall {A : Type} (f : A -> bool) (l : list A) :
    forallb f l = true -> Forall (fun x => f x = true) l.
  Proof.
    induction l as [|x l ih]; cbn; intros h; [constructor|].
    apply andb_true_iff in h as [h1 h2]. constructor; [exact h1|exact (ih h2)].
  Qed.

  Definition cbn_rd_pred (ts : list term) (N : nat) (p : predicate term) : predicate term :=
    {| pparams := map (fun t => subst ts 0 (lift N #|ts| t)) p.(pparams);
       puinst := p.(puinst);
       pcontext := p.(pcontext);
       preturn := subst ts #|p.(pcontext)| (lift N (#|p.(pcontext)| + #|ts|) p.(preturn)) |}.

  Definition cbn_rd_br (ts : list term) (N : nat) (br : branch term) : branch term :=
    {| bcontext := br.(bcontext);
       bbody := subst ts #|br.(bcontext)| (lift N (#|br.(bcontext)| + #|ts|) br.(bbody)) |}.

  Lemma cbn_rsusp_case (ts : list term) (N : nat) (ci : case_info) (p : predicate term)
      (c : term) (brs : list (branch term)) :
    subst ts 0 (lift N #|ts| (tCase ci p c brs))
    = tCase ci (cbn_rd_pred ts N p) (subst ts 0 (lift N #|ts| c)) (map (cbn_rd_br ts N) brs).
  Proof.
    cbn [lift subst]. f_equal.
    - unfold cbn_rd_pred, map_predicate_k. cbn [pparams puinst pcontext preturn]. cbv [id].
      rewrite map_map. rewrite Nat.add_0_r. reflexivity.
    - rewrite map_map. apply map_ext. intros br. unfold cbn_rd_br, map_branch_k.
      cbn [bcontext bbody]. cbv [id]. rewrite Nat.add_0_r. reflexivity.
  Qed.

  Lemma cbn_open_case_inv (Ξ : context) (ci : case_info) (p : predicate term) (c : term)
      (brs : list (branch term)) :
    is_open_term Ξ (tCase ci p c brs) ->
    forallb (is_open_term Ξ) p.(pparams)
    /\ on_free_vars (shiftnP #|p.(pcontext)| (shiftnP #|Ξ| cbn_xpred0)) p.(preturn)
    /\ on_free_vars_ctx (closedP #|p.(pparams)| cbn_xpredT) p.(pcontext)
    /\ is_open_term Ξ c
    /\ Forall (fun br => on_free_vars_ctx (closedP #|p.(pparams)| cbn_xpredT) br.(bcontext)
                 /\ on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Ξ| cbn_xpred0)) br.(bbody))
         brs.
  Proof.
    intros h. cbn [on_free_vars is_true] in h.
    apply andb_true_iff in h as [h1 h]. apply andb_true_iff in h as [h2 h].
    apply andb_true_iff in h as [h3 h]. apply andb_true_iff in h as [h4 h5].
    rewrite test_context_k_closed_on_free_vars_ctx in h3.
    split; [exact h1|]. split; [exact h2|]. split; [exact h3|]. split; [exact h4|].
    refine (Forall_impl (cbn_cc_forallb_Forall _ _ h5) _).
    intros br hb. cbv beta in hb. apply andb_true_iff in hb as [hb1 hb2].
    rewrite test_context_k_closed_on_free_vars_ctx in hb1. split; [exact hb1|exact hb2].
  Qed.

End ConvEqs.

(** * Syntactic facts the ghost-reading comparison needs

  [cbn_cg_occ_inv]: a slot the code really uses is a subterm of the reading, so the reading's
  free-variable property passes to it (hygiene rules out an occurrence that is only in a
  [tCase] context). [cbn_cg_subst_scope_inv]: the free variables of a term above a substituted
  block. [cbn_cg_subst_fresh_lift]: fresh variables pushed at the top of an environment read
  back the lifted body. [cbn_cg_code_inv_wf_universes]: a code of a universe-checked entry is
  universe-checked. *)

Local Notation cbn_xpred0 := (fun _ : nat => false) (only parsing).
Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).

(** ** List helpers *)

Lemma cbn_cg_forallb_In {A} (p : A -> bool) (l : list A) (x : A) :
  forallb p l = true -> In x l -> p x = true.
Proof. intros H Hin. rewrite forallb_forall in H. exact (H x Hin). Qed.

Lemma cbn_cg_forallb_nth_some {A} (p : A -> bool) (l : list A) n x :
  forallb p l = true -> nth_error l n = Some x -> p x = true.
Proof. intros h hn. apply nth_error_In in hn. exact (cbn_cg_forallb_In p l x h hn). Qed.

Lemma cbn_cg_All_forallb_false {A} (Q : A -> Type) (p : A -> bool) (G : Prop) (l : list A) :
  All Q l -> forallb p l = false -> (forall x, In x l -> Q x -> p x = false -> G) -> G.
Proof.
  intros HA. induction HA as [|x l Qx HA IH]; cbn; intros H K; [discriminate H|].
  apply Bool.andb_false_iff in H as [H|H].
  - exact (K x (or_introl eq_refl) Qx H).
  - apply IH; [exact H|]. intros y Hy Qy Hpy. exact (K y (or_intror Hy) Qy Hpy).
Qed.

Lemma cbn_cg_forallb_All_impl {A} (Q : A -> Type) (p q : A -> bool) (l : list A) :
  All Q l -> (forall x, Q x -> p x = true -> q x = true) ->
  forallb p l = true -> forallb q l = true.
Proof.
  intros HA Hf. induction HA as [|x l Qx HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff; split; [exact (Hf x Qx H1) | exact (IH H2)].
Qed.

Lemma cbn_cg_forallb_map_inv {A B} (Q : A -> Type) (p : A -> bool) (q : B -> bool) (f : A -> B)
  (l : list A) :
  All Q l -> (forall x, Q x -> q (f x) = true -> p x = true) ->
  forallb q (map f l) = true -> forallb p l = true.
Proof.
  intros HA Hf. induction HA as [|x l Qx HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff; split; [exact (Hf x Qx H1) | exact (IH H2)].
Qed.

Lemma cbn_cg_test_context_k_impl_on (Q : term -> Type) (f g : nat -> term -> bool) (m : nat)
  (ctx : context) :
  onctx Q ctx -> (forall i t, Q t -> f i t = true -> g i t = true) ->
  test_context_k f m ctx = true -> test_context_k g m ctx = true.
Proof.
  intros HA Hfg. induction HA as [|d ctx [Hb Ht] HA IH]; cbn [test_context_k]; intros H;
    [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff; split; [exact (IH H1)|].
  destruct d as [na [b|] ty]; unfold test_decl in H2 |- *;
    cbn [option_default decl_body decl_type andb] in Hb, Ht, H2 |- *.
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    apply Bool.andb_true_iff; split; [exact (Hfg _ _ Hb H2) | exact (Hfg _ _ Ht H3)].
  - exact (Hfg _ _ Ht H2).
Qed.

(** ** 1. A term closed at [k] does not use an index from [k] on *)

Lemma cbn_cg_closedn_noccur : forall (t : term) (k n : nat), closedn k t -> noccur_between k n t.
Proof.
  intros t. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.orb_true_iff; left; exact H.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k n H. cbn [closedn noccur_between] in H |- *.
    refine (cbn_cg_forallb_All_impl _ _ _ _ Hl _ H). intros x Px Hx. apply Px; exact Hx.
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; assumption.
  - (* tLambda *)
    intros na A IHA B IHB k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHA | apply IHB]; assumption.
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + apply IHb; assumption.
    + apply IHty; assumption.
    + apply IHB; assumption.
  - (* tApp *)
    intros u v IHu IHv k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply IHu | apply IHv]; assumption.
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p [Hpar [Hctx Hret]] c IHc brs Hbrs k n H.
    cbn [closedn noccur_between] in H |- *.
    unfold test_predicate_k in H |- *.
    apply Bool.andb_true_iff in H as [H Hbr].
    apply Bool.andb_true_iff in H as [H Hc].
    apply Bool.andb_true_iff in H as [H Hr].
    apply Bool.andb_true_iff in H as [H Hcx].
    apply Bool.andb_true_iff in H as [Hu Hpa].
    apply Bool.andb_true_iff; split.
    2:{ refine (cbn_cg_forallb_All_impl _ _ _ _ Hbrs _ Hbr).
        intros br [Pctx Pbody] Hb. unfold test_branch_k in Hb |- *.
        apply Bool.andb_true_iff in Hb as [Hb1 Hb2].
        apply Bool.andb_true_iff; split.
        - refine (cbn_cg_test_context_k_impl_on _ _ _ _ _ Pctx _ Hb1).
          intros i t' Qt Ht. apply Qt; exact Ht.
        - apply Pbody; exact Hb2. }
    apply Bool.andb_true_iff; split.
    2:{ apply IHc; exact Hc. }
    apply Bool.andb_true_iff; split.
    2:{ apply Hret; exact Hr. }
    apply Bool.andb_true_iff; split.
    2:{ refine (cbn_cg_test_context_k_impl_on _ _ _ _ _ Hctx _ Hcx).
        intros i t' Qt Ht. apply Qt; exact Ht. }
    apply Bool.andb_true_iff; split; [reflexivity|].
    refine (cbn_cg_forallb_All_impl _ _ _ _ Hpar _ Hpa). intros x Px Hx. apply Px; exact Hx.
  - (* tProj *)
    intros pr c IHc k n H. cbn [closedn noccur_between] in H |- *. apply IHc; exact H.
  - (* tFix *)
    intros mfix idx Hm k n H. cbn [closedn noccur_between] in H |- *.
    refine (cbn_cg_forallb_All_impl _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; assumption.
  - (* tCoFix *)
    intros mfix idx Hm k n H. cbn [closedn noccur_between] in H |- *.
    refine (cbn_cg_forallb_All_impl _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; assumption.
  - (* tPrim *)
    intros prim Hprim k n H. cbn [closedn noccur_between] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cbn_cg_forallb_All_impl _ _ _ _ Hval _ H1). intros y Py Hy. apply Py; exact Hy.
    + apply Hdef; exact H2.
    + apply Hty; exact H3.
Qed.

(** ** Free-variable helpers *)

Lemma cbn_cg_hyg_shift n t : on_free_vars (shiftnP n cbn_xpredT) t = on_free_vars cbn_xpredT t.
Proof. apply on_free_vars_ext. apply shiftnP_xpredT. Qed.

Lemma cbn_cg_ofv_shiftn (P : nat -> bool) n k t :
  on_free_vars (shiftnP n (shiftnP k P)) t = on_free_vars (shiftnP (n + k) P) t.
Proof. apply on_free_vars_ext. apply shiftnP_add. Qed.

Lemma cbn_cg_ofv_lift0 (P : nat -> bool) k u :
  on_free_vars (shiftnP k P) (lift0 k u) = on_free_vars P u.
Proof.
  rewrite lift_rename. rewrite PCUICOnFreeVarsConv.on_free_vars_rename.
  apply on_free_vars_ext. intros i. cbv [shiftnP lift_renaming].
  replace (0 <=? i) with true by (symmetry; apply Nat.leb_le; lia).
  replace (k + i <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (k + i - k) with i by lia. reflexivity.
Qed.

(** Hygiene closes every [tCase] context, so no index occurs in one. *)
Lemma cbn_cg_ctx_hyg_noccur (n m : nat) (ctx : context) :
  test_context_k (fun k => on_free_vars (closedP k cbn_xpredT)) m ctx = true ->
  test_context_k (fun k' => noccur_between k' n) m ctx = true.
Proof.
  induction ctx as [|d ctx IH]; cbn [test_context_k]; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff; split; [exact (IH H1)|].
  destruct d as [na [b|] ty]; unfold test_decl in H2 |- *;
    cbn [option_default decl_body decl_type andb] in H2 |- *.
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    apply Bool.andb_true_iff; split; apply cbn_cg_closedn_noccur; rewrite closedP_on_free_vars;
      assumption.
  - apply cbn_cg_closedn_noccur; rewrite closedP_on_free_vars; assumption.
Qed.

(** ** 2. An index the term really uses *)

Lemma cbn_cg_occ_inv (P : nat -> bool) (ts : list term) (N j : nat) (u : term) :
  nth_error ts j = Some u ->
  forall (t : term) (k : nat),
    on_free_vars cbn_xpredT t ->
    noccur_between (k + j) 1 t = false ->
    on_free_vars (shiftnP k P) (subst ts k (lift N (k + #|ts|) t)) ->
    on_free_vars P u.
Proof.
  intros Hj t. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r k _ Hn Hf. cbn [noccur_between] in Hn.
    apply Bool.orb_false_iff in Hn as [H1 H2].
    apply Nat.ltb_ge in H1. apply Nat.leb_gt in H2.
    assert (Hr : r = k + j) by lia. subst r.
    assert (Hlt : j < #|ts|) by (apply nth_error_Some; rewrite Hj; discriminate).
    rewrite (lift_rel_lt N (k + j) (k + #|ts|)) in Hf by lia.
    rewrite (subst_rel_eq ts k j u (k + j) Hj eq_refl) in Hf.
    rewrite cbn_cg_ofv_lift0 in Hf. exact Hf.
  - (* tVar *) intros i k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tEvar *)
    intros ev l Hl k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply (cbn_cg_All_forallb_false _ _ _ _ Hl Hn). intros x Hin IH Hx.
    apply (IH k); [exact (cbn_cg_forallb_In _ _ _ Hh Hin) | exact Hx |].
    apply (cbn_cg_forallb_In _ _ _ Hf). apply in_map. apply in_map. exact Hin.
  - (* tSort *) intros s k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tProd *)
    intros na A IHA B IHB k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [HhA HhB]. rewrite cbn_cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [HfA HfB]. rewrite cbn_cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHA k HhA Hn HfA).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tLambda *)
    intros na A IHA B IHB k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [HhA HhB]. rewrite cbn_cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [HfA HfB]. rewrite cbn_cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHA k HhA Hn HfA).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB k Hh Hn Hf.
    cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [Hhb Hh]. apply Bool.andb_true_iff in Hh as [Hhty HhB].
    rewrite cbn_cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [Hfb Hf]. apply Bool.andb_true_iff in Hf as [Hfty HfB].
    rewrite cbn_cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn]; [apply Bool.andb_false_iff in Hn as [Hn|Hn]|].
    + exact (IHb k Hhb Hn Hfb).
    + exact (IHty k Hhty Hn Hfty).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tApp *)
    intros a b IHa IHb k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [Hha Hhb].
    apply Bool.andb_true_iff in Hf as [Hfa Hfb].
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHa k Hha Hn Hfa).
    + exact (IHb k Hhb Hn Hfb).
  - (* tConst *) intros s ui k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tInd *) intros i ui k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tConstruct *) intros i n ui k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tCase *)
    intros ci p [Hpar [Hctx Hret]] c IHc brs Hbrs k Hh Hn Hf.
    cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    unfold map_predicate_k in Hf. cbn [pparams pcontext preturn puinst] in Hf.
    apply Bool.andb_true_iff in Hh as [Hhpa Hh]. apply Bool.andb_true_iff in Hh as [Hhr Hh].
    apply Bool.andb_true_iff in Hh as [Hhcx Hh]. apply Bool.andb_true_iff in Hh as [Hhc Hhbr].
    apply Bool.andb_true_iff in Hf as [Hfpa Hf]. apply Bool.andb_true_iff in Hf as [Hfr Hf].
    apply Bool.andb_true_iff in Hf as [_ Hf]. apply Bool.andb_true_iff in Hf as [Hfc Hfbr].
    unfold test_predicate_k in Hn.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    1: apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + (* puinst *) discriminate Hn.
    + (* pparams *)
      apply (cbn_cg_All_forallb_false _ _ _ _ Hpar Hn). intros x Hin IH Hx.
      apply (IH k); [exact (cbn_cg_forallb_In _ _ _ Hhpa Hin) | exact Hx |].
      apply (cbn_cg_forallb_In _ _ _ Hfpa). apply in_map. apply in_map. exact Hin.
    + (* pcontext *)
      rewrite (cbn_cg_ctx_hyg_noccur 1 _ _ Hhcx) in Hn. discriminate Hn.
    + (* preturn *)
      apply (Hret (#|pcontext p| + k)).
      * rewrite cbn_cg_hyg_shift in Hhr. exact Hhr.
      * rewrite <- Nat.add_assoc. exact Hn.
      * rewrite cbn_cg_ofv_shiftn in Hfr. rewrite <- Nat.add_assoc. exact Hfr.
    + (* scrutinee *) exact (IHc k Hhc Hn Hfc).
    + (* branches *)
      apply (cbn_cg_All_forallb_false _ _ _ _ Hbrs Hn). intros br Hin [Pctx Pbody] Hx.
      unfold test_branch_k in Hx.
      pose proof (cbn_cg_forallb_In _ _ _ Hhbr Hin) as Hhb. cbn beta in Hhb.
      apply Bool.andb_true_iff in Hhb as [Hhbcx Hhbb].
      apply Bool.andb_false_iff in Hx as [Hx|Hx].
      * rewrite (cbn_cg_ctx_hyg_noccur 1 _ _ Hhbcx) in Hx. discriminate Hx.
      * pose proof (cbn_cg_forallb_In _ _ _ Hfbr (in_map _ _ _ (in_map _ _ _ Hin))) as Hfb.
        cbn [map_branch_k bcontext bbody id] in Hfb.
        apply Bool.andb_true_iff in Hfb as [_ Hfb].
        apply (Pbody (#|bcontext br| + k)).
        -- rewrite cbn_cg_hyg_shift in Hhbb. exact Hhbb.
        -- rewrite <- Nat.add_assoc. exact Hx.
        -- rewrite cbn_cg_ofv_shiftn in Hfb. rewrite <- Nat.add_assoc. exact Hfb.
  - (* tProj *)
    intros pr c IHc k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    exact (IHc k Hh Hn Hf).
  - (* tFix *)
    intros mfix idx Hm k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    rewrite !length_map in Hf.
    apply (cbn_cg_All_forallb_false _ _ _ _ Hm Hn). intros d Hin [Pty Pbody] Hx.
    unfold test_def in Hx.
    pose proof (cbn_cg_forallb_In _ _ _ Hh Hin) as Hhd. unfold test_def in Hhd.
    apply Bool.andb_true_iff in Hhd as [Hhty Hhbody].
    pose proof (cbn_cg_forallb_In _ _ _ Hf (in_map _ _ _ (in_map _ _ _ Hin))) as Hfd.
    unfold test_def in Hfd. cbn [map_def dtype dbody] in Hfd.
    apply Bool.andb_true_iff in Hfd as [Hfty Hfbody].
    apply Bool.andb_false_iff in Hx as [Hx|Hx].
    + exact (Pty k Hhty Hx Hfty).
    + apply (Pbody (#|mfix| + k)).
      * rewrite cbn_cg_hyg_shift in Hhbody. exact Hhbody.
      * rewrite <- Nat.add_assoc. exact Hx.
      * rewrite cbn_cg_ofv_shiftn in Hfbody. rewrite <- Nat.add_assoc. exact Hfbody.
  - (* tCoFix *)
    intros mfix idx Hm k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    rewrite !length_map in Hf.
    apply (cbn_cg_All_forallb_false _ _ _ _ Hm Hn). intros d Hin [Pty Pbody] Hx.
    unfold test_def in Hx.
    pose proof (cbn_cg_forallb_In _ _ _ Hh Hin) as Hhd. unfold test_def in Hhd.
    apply Bool.andb_true_iff in Hhd as [Hhty Hhbody].
    pose proof (cbn_cg_forallb_In _ _ _ Hf (in_map _ _ _ (in_map _ _ _ Hin))) as Hfd.
    unfold test_def in Hfd. cbn [map_def dtype dbody] in Hfd.
    apply Bool.andb_true_iff in Hfd as [Hfty Hfbody].
    apply Bool.andb_false_iff in Hx as [Hx|Hx].
    + exact (Pty k Hhty Hx Hfty).
    + apply (Pbody (#|mfix| + k)).
      * rewrite cbn_cg_hyg_shift in Hhbody. exact Hhbody.
      * rewrite <- Nat.add_assoc. exact Hx.
      * rewrite cbn_cg_ofv_shiftn in Hfbody. rewrite <- Nat.add_assoc. exact Hfbody.
  - (* tPrim *)
    intros prim Hprim k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    destruct prim as [tg [? | ? | ? | a]]; cbn -[shiftnP] in Hprim, Hh, Hn, Hf;
      try discriminate Hn.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in Hh as [Hh Hhty]. apply Bool.andb_true_iff in Hh as [Hhval Hhdef].
    apply Bool.andb_true_iff in Hf as [Hf Hfty]. apply Bool.andb_true_iff in Hf as [Hfval Hfdef].
    apply Bool.andb_false_iff in Hn as [Hn|Hn]; [apply Bool.andb_false_iff in Hn as [Hn|Hn]|].
    + apply (cbn_cg_All_forallb_false _ _ _ _ Hval Hn). intros x Hin IH Hx.
      apply (IH k); [exact (cbn_cg_forallb_In _ _ _ Hhval Hin) | exact Hx |].
      apply (cbn_cg_forallb_In _ _ _ Hfval). apply in_map. apply in_map. exact Hin.
    + exact (Hdef k Hhdef Hn Hfdef).
    + exact (Hty k Hhty Hn Hfty).
Qed.

(** ** 3. The free variables above a substituted block *)

Lemma cbn_cg_subst_scope_inv (P : nat -> bool) (ws : list term) :
  forall (b : term) (k : nat),
    on_free_vars (shiftnP k P) (subst ws k b) -> on_free_vars (shiftnP (k + #|ws|) P) b.
Proof.
  intros b. elim b using term_forall_list_ind.
  - (* tRel *)
    intros r k H. cbn [subst] in H. cbn [on_free_vars]. unfold shiftnP.
    revert H. destruct (k <=? r) eqn:E; intros H.
    + apply Nat.leb_le in E. revert H. destruct (nth_error ws (r - k)) as [x|] eqn:E2; intros H.
      * apply Bool.orb_true_iff; left. apply Nat.ltb_lt.
        assert (r - k < #|ws|) by (apply nth_error_Some; rewrite E2; discriminate). lia.
      * apply nth_error_None in E2. cbn [on_free_vars] in H. unfold shiftnP in H.
        apply Bool.orb_true_iff in H as [H|H]; [apply Nat.ltb_lt in H; lia|].
        apply Bool.orb_true_iff; right.
        replace (r - (k + #|ws|)) with (r - #|ws| - k) by lia. exact H.
    + apply Nat.leb_gt in E. apply Bool.orb_true_iff; left. apply Nat.ltb_lt. lia.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k H. cbn [subst on_free_vars] in H |- *.
    refine (cbn_cg_forallb_map_inv _ _ _ _ _ Hl _ H). intros x Px Hx. exact (Px k Hx).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite cbn_cg_ofv_shiftn in H2 |- *.
    apply Bool.andb_true_iff; split; [exact (IHA k H1) | exact (IHB (S k) H2)].
  - (* tLambda *)
    intros na A IHA B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite cbn_cg_ofv_shiftn in H2 |- *.
    apply Bool.andb_true_iff; split; [exact (IHA k H1) | exact (IHB (S k) H2)].
  - (* tLetIn *)
    intros na b0 IHb ty IHty B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H]. apply Bool.andb_true_iff in H as [H2 H3].
    rewrite cbn_cg_ofv_shiftn in H3 |- *.
    apply Bool.andb_true_iff; split; [exact (IHb k H1)|].
    apply Bool.andb_true_iff; split; [exact (IHty k H2) | exact (IHB (S k) H3)].
  - (* tApp *)
    intros a b0 IHa IHb k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [exact (IHa k H1) | exact (IHb k H2)].
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p [Hpar [Hctx Hret]] c IHc brs Hbrs k H.
    cbn [subst on_free_vars] in H |- *.
    unfold map_predicate_k in H. cbn [pparams pcontext preturn puinst] in H.
    rewrite length_map in H.
    apply Bool.andb_true_iff in H as [Hpa H]. apply Bool.andb_true_iff in H as [Hr H].
    apply Bool.andb_true_iff in H as [Hcx H]. apply Bool.andb_true_iff in H as [Hc Hbr].
    apply Bool.andb_true_iff; split.
    { refine (cbn_cg_forallb_map_inv _ _ _ _ _ Hpar _ Hpa). intros x Px Hx. exact (Px k Hx). }
    apply Bool.andb_true_iff; split.
    { rewrite cbn_cg_ofv_shiftn in Hr |- *. rewrite Nat.add_assoc. exact (Hret _ Hr). }
    apply Bool.andb_true_iff; split; [exact Hcx|].
    apply Bool.andb_true_iff; split; [exact (IHc k Hc)|].
    refine (cbn_cg_forallb_map_inv _ _ _ _ _ Hbrs _ Hbr). intros br [Pctx Pbody] Hx.
    cbn [map_branch_k bcontext bbody id] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2]. apply Bool.andb_true_iff; split; [exact Hx1|].
    rewrite cbn_cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tProj *)
    intros pr c IHc k H. cbn [subst on_free_vars] in H |- *. exact (IHc k H).
  - (* tFix *)
    intros mfix idx Hm k H. cbn [subst on_free_vars] in H |- *. rewrite !length_map in H.
    refine (cbn_cg_forallb_map_inv _ _ _ _ _ Hm _ H). intros d [Pty Pbody] Hx.
    unfold test_def in Hx |- *. cbn [map_def dtype dbody] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
    apply Bool.andb_true_iff; split; [exact (Pty k Hx1)|].
    rewrite cbn_cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tCoFix *)
    intros mfix idx Hm k H. cbn [subst on_free_vars] in H |- *. rewrite !length_map in H.
    refine (cbn_cg_forallb_map_inv _ _ _ _ _ Hm _ H). intros d [Pty Pbody] Hx.
    unfold test_def in Hx |- *. cbn [map_def dtype dbody] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
    apply Bool.andb_true_iff; split; [exact (Pty k Hx1)|].
    rewrite cbn_cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tPrim *)
    intros prim Hprim k H. cbn [subst on_free_vars] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn -[shiftnP] in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cbn_cg_forallb_map_inv _ _ _ _ _ Hval _ H1). intros y Py Hy. exact (Py k Hy).
    + exact (Hdef k H2).
    + exact (Hty k H3).
Qed.

(** ** 4. Substituting the identity readings back *)

Lemma cbn_cg_subst_idsn_lift (k : nat) (t : term) : subst (idsn k) 0 (lift k k t) = t.
Proof.
  revert t. induction k as [|k IH]; intros t.
  - cbn [idsn]. rewrite subst_empty. apply lift0_id.
  - cbn [idsn]. rewrite subst_app_simpl. rewrite idsn_length. cbn [Nat.add].
    rewrite (subst_reli_lift_id k k t (le_n k)). exact (IH t).
Qed.

(** ** 5. Substituting lifted identity readings *)

Lemma cbn_cg_subst_fresh_lift (m k : nat) (t : term) :
  subst (map (lift0 m) (idsn k)) 0 (lift (m + k) k t) = lift0 m t.
Proof.
  pose proof (distr_lift_subst (lift k k t) (idsn k) m 0) as E.
  rewrite cbn_cg_subst_idsn_lift in E. rewrite idsn_length, Nat.add_0_r in E.
  rewrite (simpl_lift t k k m k) in E by lia.
  symmetry; exact E.
Qed.

(** ** 6. Universe well-formedness of a code's term *)

Lemma cbn_cg_code_inv_wf_universes {cf : checker_flags} (Σ : global_env_ext) (e : cbn_code_entry)
  (c : cbn_code) :
  cbn_code_inv e c -> wf_universes Σ (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)) ->
  wf_universes Σ c.(cbn_c_term).
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [_ ht]] hr. revert ht.
  generalize (cbn_c_term c) as t.
  induction ks as [|k ks IH]; cbn [fold_right]; intros t ht.
  - injection ht as <-. exact hr.
  - destruct (fold_right _ _ ks) as [t0|] eqn:E; [|discriminate ht].
    pose proof (IH t0 eq_refl) as h0. clear IH E.
    unfold wf_universes in h0 |- *.
    destruct t0; cbn [on_universes] in h0; cbn in ht; try discriminate ht;
      repeat match goal with
             | H : is_true (_ && _) |- _ => apply andb_true_iff in H as [? ?]
             | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
             end.
    + (* tProd *)
      destruct k as [|[q|q|]]; cbn in ht; try discriminate ht; injection ht as <-; assumption.
    + (* tLambda *)
      destruct k as [|[q|q|]]; cbn in ht; try discriminate ht; injection ht as <-; assumption.
    + (* tLetIn *)
      destruct k as [|[q|[q|q|]|]]; cbn in ht; try discriminate ht; injection ht as <-;
        assumption.
    + (* tApp *)
      destruct k as [|[q|q|]]; cbn in ht; try discriminate ht; injection ht as <-; assumption.
    + (* tCase *)
      destruct k as [|[q|q|]]; cbn in ht.
      * injection ht as <-. assumption.
      * destruct (nth_error brs _) as [br|] eqn:Eb; cbn in ht; [|discriminate ht].
        injection ht as <-.
        match goal with H : forallb _ brs = true |- _ =>
          pose proof (cbn_cg_forallb_nth_some _ _ _ _ H Eb) as hb end.
        unfold test_branch in hb. apply andb_true_iff in hb as [_ hb]. exact hb.
      * match goal with H : forallb _ (pparams _) = true |- _ =>
          exact (cbn_cg_forallb_nth_some _ _ _ _ H ht) end.
      * injection ht as <-. assumption.
    + (* tProj *)
      destruct k as [|q]; cbn in ht; [injection ht as <-; assumption|discriminate ht].
    + (* tFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cbn_cg_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      cbn beta in hd. apply andb_true_iff in hd. exact (proj2 hd).
    + (* tCoFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cbn_cg_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      cbn beta in hd. apply andb_true_iff in hd. exact (proj2 hd).
Qed.

(** * A machine call returns the caller's roots renamed, never reshaped

  The shape of a root is the root with every heap address replaced by one constant address
  ([cbn_mp_root cbn_kc]). A renaming ([rn_*]), a collection, an allocation and every function of the
  machine give back roots of the shape of the roots they were given: each function pops
  exactly the frames it pushes, and threads the rest through calls that keep their shape. *)

#[local] Definition cbn_kc : cbn_haddr -> cbn_haddr := fun _ => CbnHAddr xH.

(** Two root lists of one shape, less their first root. *)
Lemma cbn_sk_tl r r' rs rs' :
  cbn_mp_roots cbn_kc (r' :: rs') = cbn_mp_roots cbn_kc (r :: rs) ->
    cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
Proof. intros h. exact (f_equal (@tl cbn_root) h). Qed.

(** Strip the frames a call pushed and popped, then chain the equations of the calls. *)
Local Ltac cbn_sk_fin :=
  repeat match goal with
         | h : cbn_mp_roots cbn_kc (_ :: _) = cbn_mp_roots cbn_kc (_ :: _) |- _ =>
           apply cbn_sk_tl in h
         end;
  repeat match goal with
         | h : cbn_mp_roots cbn_kc ?a = cbn_mp_roots cbn_kc ?b |- cbn_mp_roots cbn_kc ?a = _ =>
           rewrite h; clear h
         end;
  reflexivity.

(** ** A renaming keeps the shape of what it renames *)

Section SkRename.
  Context {G : Type} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G)).

  Lemma cbn_sk_rn_addrs : forall l g l' g', cbn_rn_addrs f l g = CbnCOk (l', g') ->
    map cbn_kc l' = map cbn_kc l.
  Proof.
    induction l as [|a l ih]; intros g l' g' he; simpl in he.
    - injection he as <- <-. reflexivity.
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      destruct (cbn_rn_addrs f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. cbn [map]. rewrite (ih _ _ _ e2). reflexivity.
  Qed.

  Lemma cbn_sk_rn_slot : forall x g x' g', cbn_rn_slot f x g = CbnCOk (x', g') ->
    cbn_mp_slot cbn_kc x' = cbn_mp_slot cbn_kc x.
  Proof.
    intros x. induction x as [a|vs n o c ihvs] using cbn_slot_ind'; intros g x' g' he.
    - simpl in he. destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. reflexivity.
    - rewrite cbn_rn_slot_SInl in he.
      destruct (cbn_rn_slots f vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_slot]. f_equal.
      revert g vs' g1 e1.
      induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 e1; simpl in e1.
      + injection e1 as <- <-. reflexivity.
      + destruct (cbn_rn_slot f y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
        destruct (cbn_rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
        injection e1 as <- <-. cbn [map]. rewrite (hy _ _ _ ea), (ihl _ _ _ eb). reflexivity.
  Qed.

  Lemma cbn_sk_rn_slots : forall l g l' g',
    cbn_rn_slots f l g = CbnCOk (l', g') -> cbn_mp_slots cbn_kc l' = cbn_mp_slots cbn_kc l.
  Proof.
    unfold cbn_mp_slots. induction l as [|y l ih]; intros g l' g' he; simpl in he.
    - injection he as <- <-. reflexivity.
    - destruct (cbn_rn_slot f y g) as [[y' g1]|w] eqn:e1; [|discriminate].
      destruct (cbn_rn_slots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. cbn [map].
      rewrite (cbn_sk_rn_slot _ _ _ _ e1), (ih _ _ _ e2). reflexivity.
  Qed.

  Lemma cbn_sk_rn_env e g e' g' : cbn_rn_env f e g = CbnCOk (e', g') ->
    cbn_mp_env cbn_kc e' = cbn_mp_env cbn_kc e.
  Proof.
    intros he. unfold cbn_rn_env in he.
    destruct (cbn_rn_slots f (cbn_ev_vals e) g) as [[vs g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. unfold cbn_mp_env. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff].
    rewrite (cbn_sk_rn_slots _ _ _ _ e1). reflexivity.
  Qed.

  Lemma cbn_sk_rn_value v g v' g' : cbn_rn_value f v g = CbnCOk (v', g') ->
    cbn_mp_value cbn_kc v' = cbn_mp_value cbn_kc v.
  Proof.
    intros he. unfold cbn_rn_value in he.
    destruct v as [h sp|e c|e c i sp|e c i sp|h sp|e c|e c sp].
    - destruct (cbn_rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value]. rewrite (cbn_sk_rn_addrs _ _ _ _ e1). reflexivity.
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value]. rewrite (cbn_sk_rn_env _ _ _ _ E1). reflexivity.
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (cbn_rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value].
      rewrite (cbn_sk_rn_env _ _ _ _ E1), (cbn_sk_rn_addrs _ _ _ _ E2). reflexivity.
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (cbn_rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value].
      rewrite (cbn_sk_rn_env _ _ _ _ E1), (cbn_sk_rn_addrs _ _ _ _ E2). reflexivity.
    - destruct (cbn_rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value]. rewrite (cbn_sk_rn_addrs _ _ _ _ e1). reflexivity.
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value]. rewrite (cbn_sk_rn_env _ _ _ _ E1). reflexivity.
    - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (cbn_rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_value].
      rewrite (cbn_sk_rn_env _ _ _ _ E1), (cbn_sk_rn_addrs _ _ _ _ E2). reflexivity.
  Qed.

  Lemma cbn_sk_rn_cell cl g cl' g' : cbn_rn_cell f cl g = CbnCOk (cl', g') ->
    cbn_mp_cell cbn_kc cl' = cbn_mp_cell cbn_kc cl.
  Proof.
    intros he. unfold cbn_rn_cell in he. destruct cl as [vs n o c|v| |b].
    - destruct (cbn_rn_slots f vs g) as [[vs1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_cell]. rewrite (cbn_sk_rn_slots _ _ _ _ e1). reflexivity.
    - destruct (cbn_rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [cbn_mp_cell]. rewrite (cbn_sk_rn_value _ _ _ _ e1). reflexivity.
    - injection he as <- <-. reflexivity.
    - destruct (f b g) as [[b1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. reflexivity.
  Qed.
End SkRename.

Lemma cbn_rn_root_skel {G : Type} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G)) (r : cbn_root)
  (g : G) r' g' :
  cbn_rn_root f r g = CbnCOk (r', g') -> cbn_mp_root cbn_kc r' = cbn_mp_root cbn_kc r.
Proof.
  intros he. unfold cbn_rn_root in he. destruct r as [a|x|e|v|l|l|cl].
  - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. reflexivity.
  - destruct (cbn_rn_slot f x g) as [[x1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [cbn_mp_root]. rewrite (cbn_sk_rn_slot f _ _ _ _ e1). reflexivity.
  - destruct (cbn_rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
    injection he as <- <-. cbn [cbn_mp_root]. rewrite (cbn_sk_rn_env f _ _ _ _ E1). reflexivity.
  - destruct (cbn_rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [cbn_mp_root]. rewrite (cbn_sk_rn_value f _ _ _ _ e1). reflexivity.
  - destruct (cbn_rn_slots f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [cbn_mp_root]. rewrite (cbn_sk_rn_slots f _ _ _ _ e1). reflexivity.
  - destruct (cbn_rn_addrs f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [cbn_mp_root]. rewrite (cbn_sk_rn_addrs f _ _ _ _ e1). reflexivity.
  - destruct (cbn_rn_cell f cl g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [cbn_mp_root]. rewrite (cbn_sk_rn_cell f _ _ _ _ e1). reflexivity.
Qed.

Lemma cbn_rn_roots_skel {G : Type} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G))
  (rs : list cbn_root) (g : G)
    rs' g' :
  cbn_rn_roots f rs g = CbnCOk (rs', g') -> cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
Proof.
  revert g rs' g'. induction rs as [|r rs ih]; intros g rs' g' he; simpl in he.
  - injection he as <- <-. reflexivity.
  - destruct (cbn_rn_root f r g) as [[r1 g1]|w] eqn:e1; [|discriminate].
    destruct (cbn_rn_roots f rs g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
    injection he as <- <-. unfold cbn_mp_roots in *. cbn [map].
    rewrite (cbn_rn_root_skel f _ _ _ _ e1), (ih _ _ _ e2). reflexivity.
Qed.

(** ** A collection, and an allocation *)

Lemma cbn_collect_skel (rs : list cbn_root) (s : cbn_state) rs' s' :
  cbn_collect rs s = CbnCOk (rs', s') -> cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
Proof.
  intros he. rewrite cbn_collect_eq in he.
  destruct (cbn_rn_ptree (cbn_gc_copy (Pos.add s.(cbn_st_next) cbn_cells)
    (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO)))
    s.(cbn_st_gam)
              (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next))) as
                [[cbn_gm g1]|w] eqn:e1;
    [|discriminate he].
  destruct (cbn_rn_roots (cbn_gc_copy (Pos.add s.(cbn_st_next) cbn_cells)
    (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO))) rs g1)
    as [[rs2 g2]|w] eqn:e2; [|discriminate he].
  injection he as <- <-. exact (cbn_rn_roots_skel _ _ _ _ _ e2).
Qed.

Lemma cbn_alloc_skel cl rs s a rs' s' :
  cbn_alloc cl rs s = CbnCOk (a, rs', s') -> cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
Proof.
  intros he. destruct (cbn_gc_due s) eqn:eg.
  - rewrite (cbn_alloc_gc cl rs s eg) in he.
    destruct (cbn_collect (CbnRC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate he].
    pose proof (cbn_collect_skel _ _ _ _ ec) as h1.
    destruct rs2 as [|[| | | | | |cl2] rs2]; try discriminate he.
    injection he as <- <- <-. exact (cbn_sk_tl _ _ _ _ h1).
  - rewrite (cbn_alloc_no_gc cl rs s eg) in he. injection he as <- <- <-. reflexivity.
Qed.

(** ** The machine *)

(** The decisions of a match or projection on a constructor: each test that fails fails. *)
Local Ltac cbn_dtests he :=
  repeat (match type of he with
          | context [if ?b then _ else _] => destruct b
          | context [match ?o with Some _ => _ | None => _ end] => destruct o
          | context [match ?m with O => _ | S _ => _ end] => destruct m
          end; try discriminate he).

Lemma cbn_push_fresh_skel : forall n lvl e1 e2 rs s r rs' s',
  cbn_push_fresh n lvl e1 e2 rs s = CbnCOk (r, rs', s') ->
    cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
Proof.
  induction n as [|n ih]; intros lvl e1 e2 rs s r rs' s' he; cbn [cbn_push_fresh] in he.
  - injection he as <- <- <-. reflexivity.
  - cbn_dcall he ea x1 rs1 s1.
    destruct rs1 as [|[| |f1| | | |] [|[| |f2| | | |] rs1]]; try discriminate he.
    pose proof (cbn_alloc_skel _ _ _ _ _ _ ea) as h1.
    pose proof (ih _ _ _ _ _ _ _ _ he) as h2. cbn_sk_fin.
Qed.

Section SkMachine.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat).

  Lemma cbn_gam_skel j rs s a rs' s' :
    cbn_gam X_type X Γ nctx j rs s = CbnCOk (a, rs', s') ->
      cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    intros he. unfold cbn_gam in he. cbv zeta in he.
    destruct (PTree.get (cbn_key_of_succ_nat j) s.(cbn_st_gam)) as [a0|].
    { injection he as <- <- <-. reflexivity. }
    destruct (nth_error Γ j) as [decl|]; [|discriminate he].
    destruct (decl_body decl) as [b|].
    - destruct (cbn_new_entry X_type X b [] s) as [c s1].
      cbv beta iota in he. cbn_dcall he ea a1 rs1 s2.
      injection he as <- <- <-. exact (cbn_alloc_skel _ _ _ _ _ _ ea).
    - cbv beta iota in he. cbn_dcall he ea a1 rs1 s2.
      injection he as <- <- <-. exact (cbn_alloc_skel _ _ _ _ _ _ ea).
  Qed.

  Lemma cbn_env_var_skel n e rs s x rs' s' :
    cbn_env_var X_type X Γ nctx n e rs s = CbnCOk (x, rs', s') ->
    cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    intros he. unfold cbn_env_var in he.
    destruct (nth_error e.(cbn_ev_vals) n) as [y|].
    - injection he as <- <- <-. reflexivity.
    - cbn_dcall he eg a1 rs1 s1. injection he as <- <- <-. exact (cbn_gam_skel _ _ _ _ _ _ eg).
  Qed.

  Lemma cbn_arg_slot_skel e c rs s x rs' s' :
    cbn_arg_slot X_type X Γ nctx e c rs s = CbnCOk (x, rs', s') ->
    cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    intros he. unfold cbn_arg_slot in he.
    destruct (cbn_c_term c); try (injection he as <- <- <-; reflexivity).
    exact (cbn_env_var_skel _ _ _ _ _ _ _ he).
  Qed.

  Lemma cbn_materialize_skel x rs s a rs' s' :
    cbn_materialize X_type X x rs s = CbnCOk (a, rs', s') ->
      cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    intros he. unfold cbn_materialize in he.
    destruct x as [a0|vs n o c]; [injection he as <- <- <-; reflexivity|].
    destruct (cbn_c_term c) eqn:ec; try exact (cbn_alloc_skel _ _ _ _ _ _ he).
    - lazymatch type of he with
      | context [cbn_delta X_type X ?kn ?ui s] =>
        destruct (cbn_delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
      end; exact (cbn_alloc_skel _ _ _ _ _ _ he).
    - lazymatch type of he with
      | context [nth_error ?m ?i] => destruct (nth_error m i)
      end; exact (cbn_alloc_skel _ _ _ _ _ _ he).
  Qed.

  Lemma cbn_bind_skel x body rs s y rs' s' :
    cbn_bind X_type X x body rs s = CbnCOk (y, rs', s') ->
      cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    intros he. unfold cbn_bind in he. destruct x as [a0|vals n o c].
    - injection he as <- <- <-. reflexivity.
    - destruct (cbn_once_body body s) as [b s1]. destruct b.
      + injection he as <- <- <-. reflexivity.
      + cbn_dcall he em a1 rs1 s2. injection he as <- <- <-.
        exact (cbn_materialize_skel _ _ _ _ _ _ em).
  Qed.

  Lemma cbn_mat_all_skel : forall d l rs s al rs' s',
    cbn_mat_all X_type X d l rs s = CbnCOk (al, rs', s') ->
      cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    intros d. induction d as [|k ih]; intros l rs s al rs' s' he;
      destruct l as [|x l]; cbn [cbn_mat_all] in he.
    1,3: injection he as <- <- <-; reflexivity.
    - discriminate he.
    - cbn_dcall he em a1 rs1 s1.
      destruct rs1 as [|[| | | |l1| |] rs1]; try discriminate he.
      pose proof (cbn_materialize_skel _ _ _ _ _ _ em) as h1.
      cbn_dcall he em2 al1 rs2 s2.
      destruct rs2 as [|[a0| | | | | |] rs2]; try discriminate he.
      injection he as <- <- <-.
      pose proof (ih tt _ _ _ _ _ _ em2) as h2. cbn_sk_fin.
  Qed.

  Lemma cbn_push_fix_cells_skel : forall n e c i acc rs s e' rs' s',
    cbn_push_fix_cells e c i n acc rs s = CbnCOk (e', rs', s') ->
    cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.
  Proof.
    induction n as [|n ih]; intros e c i acc rs s e' rs' s' he;
      cbn [cbn_push_fix_cells] in he.
    - injection he as <- <- <-. reflexivity.
    - cbn_dcall he ea a1 rs1 s1.
      destruct rs1 as [|[| |e1| | | |] [|[| |acc1| | | |] rs1]]; try discriminate he.
      pose proof (cbn_alloc_skel _ _ _ _ _ _ ea) as h1.
      pose proof (ih _ _ _ _ _ _ _ _ _ he) as h2. cbn_sk_fin.
  Qed.

  (** The five functions of the machine at one fuel. *)
  #[local] Definition cbn_sk_m (d : cbn_fuel) : Prop :=
    (forall a rs s v rs' s', cbn_force X_type X Γ nctx d a rs s = CbnCOk (v, rs', s') ->
       cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
    /\ (forall x stk rs s v rs' s', cbn_eval_slot X_type X Γ nctx d x stk rs s
      = CbnCOk (v, rs', s') ->
       cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
    /\ (forall e c stk rs s v rs' s', cbn_whnf X_type X Γ nctx d e c stk rs s
      = CbnCOk (v, rs', s') ->
       cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
    /\ (forall e c mfix idx stk rs s v rs' s',
         cbn_whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = CbnCOk (v, rs', s') ->
       cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
    /\ (forall v stk rs s w rs' s', cbn_apply X_type X Γ nctx d v stk rs s = CbnCOk (w, rs', s') ->
       cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs).

  Lemma cbn_sk_machine : forall d, cbn_sk_m d.
  Proof.
    intros d. induction d as [|k ih].
    - (* CbnFO: every call fails, except [cbn_apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros a rs s v rs' s' he. cbn [cbn_force] in he. discriminate he.
      + intros x stk rs s v rs' s' he. cbn [cbn_eval_slot] in he. discriminate he.
      + intros e c stk rs s v rs' s' he. cbn [cbn_whnf] in he. discriminate he.
      + intros e c mfix idx stk rs s v rs' s' he. cbn [cbn_whnf_fix] in he. discriminate he.
      + intros v stk rs s w rs' s' he. cbn [cbn_apply] in he.
        destruct stk; [injection he as <- <- <-; reflexivity|discriminate he].
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      split; [|split; [|split; [|split]]].
      + (* cbn_force *)
        intros a0 rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [cbn_force] in he.
        destruct (cbn_heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct cl as [vs n o c|vd| |b]; try discriminate he.
        * (* a suspension: evaluate it, then write the value back *)
          destruct (cbn_heap_upd a0 CbnCBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          cbn_dcall he ew vw rsw sw.
          destruct rsw as [|[ar| | | | | |] rsw]; try discriminate he.
          destruct (cbn_heap_upd ar (CbnCDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as <- <- <-.
          pose proof (IHw _ _ _ _ _ _ _ _ ew) as h1. cbn_sk_fin.
        * (* a value: the heap has it *)
          injection he as <- <- <-. reflexivity.
      + (* cbn_eval_slot *)
        intros x stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [cbn_eval_slot] in he.
        destruct x as [a|vs n o c].
        * cbn_dcall he ef vf rsf sf.
          destruct rsf as [|[| | | |lk| |] rsf]; try discriminate he.
          pose proof (IHf _ _ _ _ _ _ ef) as h1.
          pose proof (IHa _ _ _ _ _ _ _ he) as h2. cbn_sk_fin.
        * exact (IHw _ _ _ _ _ _ _ _ he).
      + (* cbn_whnf *)
        intros e c stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [cbn_whnf] in he.
        destruct (cbn_tick s0) as [st|] eqn:etick; [|discriminate he].
        destruct (cbn_c_term c) as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|kn ui
                               |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
          eqn:ec; try solve [discriminate he].
        * (* tRel *)
          cbn_dcall he ev xr rsr sr.
          destruct rsr as [|[| | | |lk| |] rsr]; try discriminate he.
          pose proof (cbn_env_var_skel _ _ _ _ _ _ _ ev) as h1.
          pose proof (IHs _ _ _ _ _ _ _ he) as h2. cbn_sk_fin.
        * (* tSort *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
        * (* tProd *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
        * (* tLambda *)
          destruct stk as [|xh stk'].
          -- injection he as <- <- <-. reflexivity.
          -- cbn_dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             pose proof (cbn_bind_skel _ _ _ _ _ _ _ eb) as h1.
             pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. cbn_sk_fin.
        * (* tLetIn *)
          cbn_dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          pose proof (cbn_arg_slot_skel _ _ _ _ _ _ _ ea) as h1.
          cbn_dcall he eb xb rsb sb.
          destruct rsb as [|[| |e2| | | |] [|[| | | |k2| |] rsb]]; try discriminate he.
          pose proof (cbn_bind_skel _ _ _ _ _ _ _ eb) as h2.
          pose proof (IHw _ _ _ _ _ _ _ _ he) as h3. cbn_sk_fin.
        * (* tApp *)
          cbn_dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          pose proof (cbn_arg_slot_skel _ _ _ _ _ _ _ ea) as h1.
          pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. cbn_sk_fin.
        * (* tConst *)
          destruct (cbn_delta X_type X kn ui st) as [[r s1]|w] eqn:ed; [|discriminate he].
          destruct r as [c'|].
          -- exact (IHw _ _ _ _ _ _ _ _ he).
          -- cbv beta iota in he.
             destruct (cbn_prim_step_of X_type X kn stk s1) as [|t rest|i x].
             ++ cbn_dcall he em sp rs1 s2.
                pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h1.
                injection he as <- <- <-. exact h1.
             ++ destruct (cbn_new_entry X_type X t [] s1) as [c2 s2].
                exact (IHw _ _ _ _ _ _ _ _ he).
             ++ cbn_dcall he ea a1 rs1 s2.
                destruct rs1 as [|[| | | |k1| |] rs1]; try discriminate he.
                pose proof (cbn_materialize_skel _ _ _ _ _ _ ea) as h1.
                cbn_dcall he ef vf rsf sf.
                destruct rsf as [|[| | | |k2| |] rsf]; try discriminate he.
                pose proof (IHf _ _ _ _ _ _ ef) as h2.
                destruct (cbn_value_is_lit vf).
                ** pose proof (IHw _ _ _ _ _ _ _ _ he) as h3. cbn_sk_fin.
                ** cbn_dcall he em sp rs3 s3.
                   pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h3.
                   injection he as <- <- <-. cbn_sk_fin.
        * (* tInd *)
          cbn_dcall he em sp rs1 s1.
          pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. exact h1.
        * (* tConstruct *)
          cbn_dcall he em sp rs1 s1.
          pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. exact h1.
        * (* tCase *)
          cbn_dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          pose proof (IHw _ _ _ _ _ _ _ _ ewc) as h1.
          destruct vc as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { destruct hd; try discriminate he. cbn_dtests he.
               pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. cbn_sk_fin. }
          all: cbn_dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h2;
               injection he as <- <- <-; cbn_sk_fin.
        * (* tProj *)
          cbn_dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          pose proof (IHw _ _ _ _ _ _ _ _ ewc) as h1.
          destruct vc as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { destruct hd; try discriminate he. cbn_dtests he.
               pose proof (IHs _ _ _ _ _ _ _ he) as h2. cbn_sk_fin. }
          all: cbn_dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h2;
               injection he as <- <- <-; cbn_sk_fin.
        * (* tFix *)
          exact (IHx _ _ _ _ _ _ _ _ _ _ he).
        * (* tPrim *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
      + (* cbn_whnf_fix *)
        intros e c mfix idx stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [cbn_whnf_fix] in he.
        destruct (nth_error mfix idx) as [def|]; [|discriminate he].
        destruct (nth_error stk (rarg def)) as [x|].
        * cbn_dcall he ea a1 rs1 s1.
          destruct rs1 as [|[| |e1| | | |] [|[| | | |k1| |] rs1]]; try discriminate he.
          pose proof (cbn_materialize_skel _ _ _ _ _ _ ea) as h1.
          cbn_dcall he ef vf rsf sf.
          destruct rsf as [|[| |e2| | | |] [|[| | | |k2| |] rsf]]; try discriminate he.
          pose proof (IHf _ _ _ _ _ _ ef) as h2.
          destruct vf as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { (* the guard holds: the forced constructor goes to a fresh cell *)
               destruct hd; try discriminate he.
               cbn_dcall he ea2 a2 rs2 s2.
               destruct rs2 as [|[| |e3| | | |] [|[| | | |k3| |] rs2]]; try discriminate he.
               pose proof (cbn_alloc_skel _ _ _ _ _ _ ea2) as h3.
               cbn_dcall he ep e4 rs3 s3.
               destruct rs3 as [|[| | | |k4| |] rs3]; try discriminate he.
               pose proof (cbn_push_fix_cells_skel _ _ _ _ _ _ _ _ _ _ ep) as h4.
               pose proof (IHw _ _ _ _ _ _ _ _ he) as h5. cbn_sk_fin. }
          all: cbn_dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h3;
               injection he as <- <- <-; cbn_sk_fin.
        * cbn_dcall he em sp rs1 s1.
          destruct rs1 as [|[| |e1| | | |] rs1]; try discriminate he.
          pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. cbn_sk_fin.
      + (* cbn_apply *)
        intros v stk rs0 s0 w rs' s' he.
        cbv beta iota zeta delta [cbn_apply] in he.
        destruct stk as [|y stk']; [injection he as <- <- <-; reflexivity|].
        destruct v as [hd sp|e c|e c idx sp|e c idx sp|nn sp|e c|e c sp]; try discriminate he.
        2: { (* a lambda: beta *)
             destruct (cbn_c_term c); try discriminate he.
             cbn_dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             pose proof (cbn_bind_skel _ _ _ _ _ _ _ eb) as h1.
             pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. cbn_sk_fin. }
        2: { (* a fixpoint: its spine goes back on the stack *)
             destruct (cbn_c_term c); try discriminate he.
             exact (IHx _ _ _ _ _ _ _ _ _ _ he). }
        all: (* the spine grows *)
             cbn_dcall he em sp1 rsm sm;
             destruct rsm as [|[| | |v1| | |] rsm]; try discriminate he;
             pose proof (cbn_mat_all_skel _ _ _ _ _ _ _ em) as h1;
             destruct (cbn_add_spine v1 sp1) as [v2|] eqn:eadd; [|discriminate he];
             injection he as <- <- <-; cbn_sk_fin.
  Qed.
End SkMachine.

Lemma cbn_machine_skel {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) : forall d,
  (forall a rs s v rs' s', cbn_force X_type X Γ nctx d a rs s = CbnCOk (v, rs', s') ->
     cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
  /\ (forall x stk rs s v rs' s', cbn_eval_slot X_type X Γ nctx d x stk rs s
    = CbnCOk (v, rs', s') ->
     cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
  /\ (forall e c stk rs s v rs' s', cbn_whnf X_type X Γ nctx d e c stk rs s = CbnCOk (v, rs', s') ->
     cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
  /\ (forall e c mfix idx stk rs s v rs' s',
       cbn_whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = CbnCOk (v, rs', s') ->
     cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs)
  /\ (forall v stk rs s w rs' s', cbn_apply X_type X Γ nctx d v stk rs s = CbnCOk (w, rs', s') ->
     cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs).
Proof. exact (cbn_sk_machine X_type X Γ nctx). Qed.


(** * The comparison on ghost readings

  A statement that reads the comparison's inputs with a heap-following read-back is false
  ([PCUICCallByNeedCounterexamples.cbn_term_seam_false]). This part states the comparison
  against the ghost reading of [cbn_machine_sound]
  ([PCUICCallByNeedSoundEval]) at the master level of [PCUICCallByNeedSoundLevel]: the state
  satisfies [cbn_minv L Q], where [L <= Q] is the comparison's logical level and [Q] the level of
  the ghost.

  Every function [f] of the comparison gets a statement [spec_f d], made of two parts.
  - The state part ([cbn_post]): from [cbn_minv L Q lo G s] and readings of the inputs under [G] at
    [Q], an answer [CbnCOk (b, rs', s')] comes with a master level [Q' >= Q] and a ghost [G'] such
    that [cbn_minv L Q' lo' G' s'] holds and every root of the caller keeps its reading, lifted by
    [Q' - Q] ([cbn_grq]). The master level rises when the comparison crosses binders: a fresh
    variable at level [L] must be below [Q] ([cbn_hwf]), and [cbn_gok_raise] lifts the ghost.
  - The conversion part ([cbn_lift_conv]): if [b = true], whenever each of the two readings is the
  lift
    by [Q - L] of a term scoped at [L], those two terms are convertible at the comparison's
    [conv_pb] in [Γ ,,, Δ] for every [Δ] of length [L - nctx]. Nothing is said of [false].
  The lifts are a premise of the conversion part, not of the call: the state part needs
  nothing of the readings beyond their existence. That matters for [cbn_same_code_cells], which
  compares environment slots whose readings are lifts only where the code uses them. *)

Section ConvGhost.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (Σ : global_env_ext).
  Context (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).
  Context (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : cbn_ctx_hyg Γ).
  Context (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                    PCUICCallByNeedSoundHook.cbn_consts_okb Σ b).

  Local Notation cbn_xpred0 := (fun _ : nat => false) (only parsing).
  Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).
  Local Notation cbn_gcok := PCUICCallByNeedSoundEval.cbn_cok.
  Local Notation cbn_MI := (cbn_minv X_type X Γ nctx Σ).

  (** ** Lifts *)

  Lemma cbn_lift0_lift0 (a b : nat) (t : term) : lift0 a (lift0 b t) = lift0 (a + b) t.
  Proof. apply simpl_lift; lia. Qed.

  Lemma cbn_map_lift0_lift0 (a b : nat) (ts : list term) :
    map (lift0 a) (map (lift0 b) ts) = map (lift0 (a + b)) ts.
  Proof. rewrite map_map. apply map_ext. intros t. apply cbn_lift0_lift0. Qed.

  (** [cbn_unl m] undoes a lift by [m]. *)
  #[local] Definition cbn_unl (m : nat) (t : term) : term := rename (fun i => i - m) t.

  Lemma cbn_unl_lift0 (m : nat) (u : term) : cbn_unl m (lift0 m u) = u.
  Proof.
    unfold cbn_unl. rewrite lift_rename, rename_compose.
    transitivity (rename ren_id u); [|apply rename_ren_id].
    apply rename_ext. intros i. unfold lift_renaming, ren_id. cbn. lia.
  Qed.

  (** [cbn_scl L u]: [u] is scoped at level [L], so open in [Γ ,,, Δ] when [#|Δ| = L - nctx].
    [cbn_inq m Q]: the free variables of the lift by [m] of a term scoped at [Q - m]. *)
  #[local] Definition cbn_scl (L : nat) (u : term) : bool := on_free_vars (shiftnP L cbn_xpred0) u.

  #[local] Definition cbn_inq (m Q : nat) (i : nat) : bool := (m <=? i) && (i <? Q).

  Lemma cbn_inq_lift0 (m L : nat) (u : term) : cbn_scl L u ->
    on_free_vars (cbn_inq m (L + m)) (lift0 m u).
  Proof.
    unfold cbn_scl. intros h. rewrite lift_rename, PCUICOnFreeVarsConv.on_free_vars_rename.
    eapply on_free_vars_impl; [|exact h].
    intros i hi. unfold shiftnP in hi. cbv beta. unfold cbn_inq, lift_renaming. cbn.
    destruct (Nat.ltb_spec i L) as [hl|hl]; cbn in hi; [|discriminate hi].
    apply andb_true_iff. split; [apply Nat.leb_le; lia|apply Nat.ltb_lt; lia].
  Qed.

  Lemma cbn_inq_unl (m Q : nat) (t : term) :
    on_free_vars (cbn_inq m Q) t -> t = lift0 m (cbn_unl m t) /\ cbn_scl (Q - m) (cbn_unl m t).
  Proof.
    intros h. split.
    - unfold cbn_unl. rewrite lift_rename, rename_compose.
      transitivity (rename ren_id t); [symmetry; apply rename_ren_id|].
      apply (PCUICOnFreeVarsConv.rename_ext_cond (cbn_inq m Q)); [|exact h].
      intros i hi. unfold cbn_inq in hi. apply andb_true_iff in hi as [h1 _].
      apply Nat.leb_le in h1. unfold lift_renaming, ren_id. cbn. lia.
    - unfold cbn_unl, cbn_scl. rewrite PCUICOnFreeVarsConv.on_free_vars_rename.
      eapply on_free_vars_impl; [|exact h].
      intros i hi. unfold cbn_inq in hi. apply andb_true_iff in hi as [h1 h2].
      apply Nat.leb_le in h1. apply Nat.ltb_lt in h2. unfold shiftnP. cbv beta.
      destruct (Nat.ltb_spec (i - m) (Q - m)); [reflexivity|lia].
  Qed.

  (** ** What a [true] claims *)

  #[local] Definition cbn_cv (L : nat) (pb : conv_pb) (u1 u2 : term) : Prop :=
    forall Δ : context, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
      ∥ Σ ;;; Γ ,,, Δ ⊢ u1 ≤[pb] u2 ∥.

  Definition cbn_lift_conv (L Q : nat) (pb : conv_pb) (t1 t2 : term) : Prop :=
    forall u1 u2 : term, t1 = lift0 (Q - L) u1 -> t2 = lift0 (Q - L) u2 ->
      cbn_scl L u1 -> cbn_scl L u2 -> cbn_cv L pb u1 u2.

  #[local] Definition cbn_cvs (L : nat) (us1 us2 : list term) : Prop :=
    forall Δ : context, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
      ∥ ws_cumul_pb_terms Σ (Γ ,,, Δ) us1 us2 ∥.

  #[local] Definition cbn_lift_conv_s (L Q : nat) (ts1 ts2 : list term) : Prop :=
    forall us1 us2 : list term,
      ts1 = map (lift0 (Q - L)) us1 -> ts2 = map (lift0 (Q - L)) us2 ->
      forallb (cbn_scl L) us1 -> forallb (cbn_scl L) us2 -> cbn_cvs L us1 us2.

  Lemma cbn_scl_open (L : nat) (Δ : context) (u : term) :
    nctx <= L -> #|Δ| = L - nctx -> cbn_scl L u -> is_open_term (Γ ,,, Δ) u.
  Proof.
    intros hL hΔ h. rewrite app_context_length, hΔ, <- hnctx.
    replace (L - nctx + nctx) with L by lia. exact h.
  Qed.

  Lemma cbn_lift_conv_refl (L Q : nat) (pb : conv_pb) (t : term) : nctx <= L ->
    cbn_lift_conv L Q pb t t.
  Proof.
    intros hL u1 u2 e1 e2 h1 h2 Δ hΔ hcl. rewrite e1 in e2.
    apply PCUICCallByNeedSoundReadBack.cbn_lift0_inj in e2. subst u2.
    constructor. apply ws_cumul_pb_refl; [exact hcl|exact (cbn_scl_open L Δ u1 hL hΔ h1)].
  Qed.

  Lemma cbn_lift_conv_lift (L Q Q' : nat) (pb : conv_pb) (t1 t2 : term) :
    L <= Q -> Q <= Q' ->
    cbn_lift_conv L Q' pb (lift0 (Q' - Q) t1) (lift0 (Q' - Q) t2) -> cbn_lift_conv L Q pb t1 t2.
  Proof.
    intros hLQ hQ h u1 u2 e1 e2 h1 h2. apply h; [| |exact h1|exact h2].
    - rewrite e1, cbn_lift0_lift0. f_equal. lia.
    - rewrite e2, cbn_lift0_lift0. f_equal. lia.
  Qed.

  Lemma cbn_lift_conv_s_lift (L Q Q' : nat) (ts1 ts2 : list term) :
    L <= Q -> Q <= Q' ->
    cbn_lift_conv_s L Q' (map (lift0 (Q' - Q)) ts1) (map (lift0 (Q' - Q)) ts2) ->
      cbn_lift_conv_s L Q ts1 ts2.
  Proof.
    intros hLQ hQ h us1 us2 e1 e2 h1 h2. apply h; [| |exact h1|exact h2].
    - rewrite e1, cbn_map_lift0_lift0. f_equal. f_equal. lia.
    - rewrite e2, cbn_map_lift0_lift0. f_equal. f_equal. lia.
  Qed.

  (** ** The caller's roots across a call that may raise the master level *)

  #[local] Definition cbn_gpq (Q Q' : nat) (G G' : cbn_ghost) (r r' : cbn_root) : Prop :=
    match r, r' with
    | CbnRA a, CbnRA a' => forall t, G a = Some t -> G' a' = Some (lift0 (Q' - Q) t)
    | CbnRSl x, CbnRSl x' =>
      forall t, cbn_g_slot nctx Q G x t -> cbn_g_slot nctx Q' G' x' (lift0 (Q' - Q) t)
    | CbnRE e, CbnRE e' =>
      e'.(cbn_ev_nvals) = e.(cbn_ev_nvals) /\ e'.(cbn_ev_goff) = e.(cbn_ev_goff)
      /\ forall ts, cbn_g_slots nctx Q G e.(cbn_ev_vals) ts ->
           cbn_g_slots nctx Q' G' e'.(cbn_ev_vals) (map (lift0 (Q' - Q)) ts)
    | CbnRV v, CbnRV v' =>
      forall t, cbn_g_value nctx Q G v t -> cbn_g_value nctx Q' G' v' (lift0 (Q' - Q) t)
    | CbnRSk l, CbnRSk l' =>
      forall ts, cbn_g_slots nctx Q G l ts -> cbn_g_slots nctx Q' G' l' (map (lift0 (Q' - Q)) ts)
    | CbnRSp l, CbnRSp l' => forall ts, cbn_g_addrs G l ts ->
      cbn_g_addrs G' l' (map (lift0 (Q' - Q)) ts)
    | CbnRC cl, CbnRC cl' =>
      forall t, cbn_g_cell nctx Q G cl t -> cbn_g_cell nctx Q' G' cl' (lift0 (Q' - Q) t)
    | _, _ => False
    end.

  (** Every root keeps its reading, lifted by [Q' - Q], and its shape ([cbn_machine_skel]): only
    its addresses change. *)
  #[local] Definition cbn_grq (Q Q' : nat) (G G' : cbn_ghost) (rs rs' : list cbn_root) : Prop :=
    cbn_gcx G G' /\ Forall2 (cbn_gpq Q Q' G G') rs rs' /\
      cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs.

  Lemma cbn_gpq_of_gpres Q G G' r r' : cbn_gpres nctx Q G G' r r' -> cbn_gpq Q Q G G' r r'.
  Proof.
    intros h. destruct r, r'; cbn in h |- *; try contradiction; rewrite Nat.sub_diag.
    all: first
      [ intros t ht; rewrite lift0_id; exact (h _ ht)
      | intros ts ht; rewrite map_lift0; exact (h _ ht)
      | destruct h as (a1 & b1 & c1); split; [exact a1|]; split; [exact b1|];
        intros ts ht; rewrite map_lift0; exact (c1 _ ht) ].
  Qed.

  Lemma cbn_grq_of_gren Q G G' rs rs' :
    cbn_gren nctx Q G G' rs rs' -> cbn_mp_roots cbn_kc rs' = cbn_mp_roots cbn_kc rs ->
      cbn_grq Q Q G G' rs rs'.
  Proof.
    intros [hc hf] hk. split; [exact hc|]. split; [|exact hk]. clear hk.
    induction hf; constructor; [apply cbn_gpq_of_gpres; assumption|assumption].
  Qed.

  Lemma cbn_grq_refl Q G rs : cbn_grq Q Q G G rs rs.
  Proof. apply cbn_grq_of_gren; [apply cbn_gren_refl|reflexivity]. Qed.

  Lemma cbn_gpq_trans Q Q1 Q2 G G1 G2 r r1 r2 :
    Q <= Q1 -> Q1 <= Q2 ->
    cbn_gpq Q Q1 G G1 r r1 -> cbn_gpq Q1 Q2 G1 G2 r1 r2 -> cbn_gpq Q Q2 G G2 r r2.
  Proof.
    intros hq1 hq2 h1 h2.
    assert (e : Q2 - Q = (Q2 - Q1) + (Q1 - Q)) by lia.
    destruct r, r1; cbn in h1; try contradiction; destruct r2; cbn in h2 |- *;
      try contradiction; rewrite e.
    all: first
      [ intros t ht; rewrite <- cbn_lift0_lift0; exact (h2 _ (h1 _ ht))
      | intros ts ht; rewrite <- cbn_map_lift0_lift0; exact (h2 _ (h1 _ ht))
      | destruct h1 as (a1 & b1 & c1), h2 as (a2 & b2 & c2);
        split; [congruence|]; split; [congruence|];
        intros ts ht; rewrite <- cbn_map_lift0_lift0; exact (c2 _ (c1 _ ht)) ].
  Qed.

  Lemma cbn_grq_trans Q Q1 Q2 G G1 G2 rs rs1 rs2 :
    Q <= Q1 -> Q1 <= Q2 ->
    cbn_grq Q Q1 G G1 rs rs1 -> cbn_grq Q1 Q2 G1 G2 rs1 rs2 -> cbn_grq Q Q2 G G2 rs rs2.
  Proof.
    intros hq1 hq2 [hc1 [hf1 hk1]] [hc2 [hf2 hk2]].
    split; [intros i e hi; exact (hc2 _ _ (hc1 _ _ hi))|].
    split; [|congruence].
    clear hk1 hk2.
    revert rs2 hf2. induction hf1 as [|r r1 l l1 hp hf ih]; intros rs2 hf2;
      inversion hf2; subst; constructor.
    - eapply cbn_gpq_trans; eassumption.
    - apply ih. assumption.
  Qed.

  Lemma cbn_grq_cons_inv_skel Q Q' G G' r rs rs1 :
    cbn_grq Q Q' G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ cbn_gpq Q Q' G G' r r' /\ cbn_grq Q Q' G G' rs rs'
      /\ cbn_mp_root cbn_kc r' = cbn_mp_root cbn_kc r.
  Proof.
    intros [hc [hf hk]]. destruct rs1 as [|r' rs']; [inversion hf|].
    exists r', rs'. split; [reflexivity|]. cbn in hk. injection hk as hk1 hk2.
    inversion hf; subst. split; [assumption|]. split; [|exact hk1].
    split; [exact hc|split; assumption].
  Qed.

  Lemma cbn_grq_cons_inv Q Q' G G' r rs rs1 :
    cbn_grq Q Q' G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ cbn_gpq Q Q' G G' r r' /\ cbn_grq Q Q' G G' rs rs'.
  Proof.
    intros h. destruct (cbn_grq_cons_inv_skel _ _ _ _ _ _ _ h) as (r' & rs' & e & h1 & h2 & _).
    exists r', rs'. split; [exact e|split; assumption].
  Qed.

  Lemma cbn_gpq_RSk_inv Q Q' G G' l r :
    cbn_gpq Q Q' G G' (CbnRSk l) r ->
    exists l', r = CbnRSk l'
      /\ forall ts, cbn_g_slots nctx Q G l ts ->
        cbn_g_slots nctx Q' G' l' (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_gpq_RSp_inv Q Q' G G' l r :
    cbn_gpq Q Q' G G' (CbnRSp l) r ->
    exists l', r = CbnRSp l' /\ forall ts, cbn_g_addrs G l ts ->
      cbn_g_addrs G' l' (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_gpq_RSl_inv Q Q' G G' x r :
    cbn_gpq Q Q' G G' (CbnRSl x) r ->
    exists x', r = CbnRSl x'
      /\ forall t, cbn_g_slot nctx Q G x t -> cbn_g_slot nctx Q' G' x' (lift0 (Q' - Q) t).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_gpq_RV_inv Q Q' G G' v r :
    cbn_gpq Q Q' G G' (CbnRV v) r ->
    exists v', r = CbnRV v'
      /\ forall t, cbn_g_value nctx Q G v t -> cbn_g_value nctx Q' G' v' (lift0 (Q' - Q) t).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_gpq_RE_inv Q Q' G G' e r :
    cbn_gpq Q Q' G G' (CbnRE e) r ->
    exists e', r = CbnRE e' /\ e'.(cbn_ev_nvals) = e.(cbn_ev_nvals) /\
      e'.(cbn_ev_goff) = e.(cbn_ev_goff)
      /\ forall ts, cbn_g_slots nctx Q G e.(cbn_ev_vals) ts ->
           cbn_g_slots nctx Q' G' e'.(cbn_ev_vals) (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  (** ** Raising the master level *)

  Lemma cbn_rwf_mono Q Q' r : Q <= Q' -> cbn_rwf Q r -> cbn_rwf Q' r.
  Proof.
    intros h. destruct r; cbn; intros hw; try exact I;
      [exact (cbn_vwf_mono _ _ _ h hw)|exact (cbn_cwf_mono _ _ _ h hw)].
  Qed.

  Lemma cbn_rwfs_mono Q Q' rs : Q <= Q' -> Forall (cbn_rwf Q) rs -> Forall (cbn_rwf Q') rs.
  Proof.
    intros h hr. induction hr as [|r rs hr0 _ ih]; constructor; [|exact ih].
    exact (cbn_rwf_mono _ _ _ h hr0).
  Qed.

  Lemma cbn_gpq_raise Q n G r : nctx <= Q -> cbn_rwf Q r ->
    cbn_gpq Q (Q + n) G (cbn_gshift n G) r r.
  Proof.
    intros hQ hw. unfold cbn_gpq. replace (Q + n - Q) with n by lia.
    destruct r; cbn in hw.
    - intros t ht. cbn. rewrite ht. reflexivity.
    - intros t ht. exact (proj1 (cbn_g_slot_shift nctx Q n hQ G) _ _ ht).
    - split; [reflexivity|]. split; [reflexivity|].
      intros ts ht. exact (proj1 (proj2 (cbn_g_slot_shift nctx Q n hQ G) _ _ ht)).
    - intros t ht. exact (cbn_g_value_shift nctx Q n hQ G _ _ hw ht).
    - intros ts ht. exact (proj1 (proj2 (cbn_g_slot_shift nctx Q n hQ G) _ _ ht)).
    - intros ts ht. apply cbn_g_addrs_shift. exact ht.
    - intros t ht. eapply cbn_g_cell_shift; eassumption.
  Qed.

  Lemma cbn_grq_raise Q n G rs : nctx <= Q -> Forall (cbn_rwf Q) rs ->
    cbn_grq Q (Q + n) G (cbn_gshift n G) rs rs.
  Proof.
    intros hQ hw. split; [intros i e hi; exact hi|]. split; [|reflexivity].
    induction hw; constructor; [apply cbn_gpq_raise; assumption|assumption].
  Qed.

  Lemma cbn_minv_raise L Q n lo G s : cbn_MI L Q lo G s -> cbn_MI L (Q + n) lo (cbn_gshift n G) s.
  Proof.
    intros [hL hQ hok hw].
    constructor; [exact hL|lia| |exact (cbn_hwf_mono Q (Q + n) s ltac:(lia) hw)].
    exact (cbn_gok_raise X_type X Γ nctx Σ wfΣ hnctx hΓ hhyg Q n lo G s ltac:(lia) hw hok).
  Qed.

  (** ** The state part of every statement *)

  #[local] Definition cbn_post (L Q : nat) (G : cbn_ghost) (rs : list cbn_root) (s' : cbn_state)
    (rs' : list cbn_root)
    : Prop :=
    exists Q' lo' G', Q <= Q' /\ cbn_MI L Q' lo' G' s' /\ Forall (cbn_rwf Q') rs'
      /\ cbn_grq Q Q' G G' rs rs'.

  Lemma cbn_post_refl L Q lo G rs s : cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
    cbn_post L Q G rs s rs.
  Proof.
    intros hm hr. exists Q, lo, G. split; [lia|]. split; [exact hm|].
    split; [exact hr|apply cbn_grq_refl].
  Qed.

  Lemma cbn_post_compose L Q Q1 G G1 rs rs1 s' rs' :
    Q <= Q1 -> cbn_grq Q Q1 G G1 rs rs1 -> cbn_post L Q1 G1 rs1 s' rs' -> cbn_post L Q G rs s' rs'.
  Proof.
    intros hq hg (Q2 & lo2 & G2 & hq2 & hm & hr & hg2). exists Q2, lo2, G2.
    split; [lia|]. split; [exact hm|]. split; [exact hr|]. eapply cbn_grq_trans; eassumption.
  Qed.

  (** A sub-call answered [false]: the caller drops the two roots it pushed. *)
  Lemma cbn_post_drop2 L Q G r1 r2 rs s' rs' :
    cbn_post L Q G (r1 :: r2 :: rs) s' rs' -> cbn_post L Q G rs s' (skipn 2 rs').
  Proof.
    intros (Q1 & lo1 & G1 & hq & hm & hr & hg).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hg) as (q1 & rsA & -> & _ & hgA).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & _ & hgB).
    exists Q1, lo1, G1. split; [exact hq|]. split; [exact hm|]. cbn [skipn].
    split; [exact (Forall_inv_tail (Forall_inv_tail hr))|exact hgB].
  Qed.

  (** ** The same-code rule, cell by cell

    [cbn_cagree L Q a i ts1 ts2]: at each position of the two slot lists, either the code [a]
    does not use the slot, or the two readings are convertible in the sense of [cbn_lift_conv]. *)
  Inductive cbn_cagree (L Q : nat) (a : term) : nat -> list term -> list term -> Prop :=
  | cbn_cagree_nil i : cbn_cagree L Q a i [] []
  | cbn_cagree_cons i u1 u2 l1 l2 :
      (noccur_between i 1 a = true \/ cbn_lift_conv L Q Conv u1 u2) ->
      cbn_cagree L Q a (S i) l1 l2 -> cbn_cagree L Q a i (u1 :: l1) (u2 :: l2).

  Lemma cbn_cagree_lift L Q Q' a i l1 l2 :
    L <= Q -> Q <= Q' ->
    cbn_cagree L Q' a i (map (lift0 (Q' - Q)) l1) (map (lift0 (Q' - Q)) l2) ->
      cbn_cagree L Q a i l1 l2.
  Proof.
    intros hL hQ. revert i l2. induction l1 as [|u1 l1 ih]; intros i [|u2 l2] h; cbn in h;
      inversion h as [i0|i0 v1 v2 m1 m2 hd hl]; subst.
    - constructor.
    - constructor; [|exact (ih _ _ hl)].
      destruct hd as [hd|hd]; [left; exact hd|right;
        exact (cbn_lift_conv_lift _ _ _ _ _ _ hL hQ hd)].
  Qed.

  Definition cbn_spec_slot (d : cbn_fuel) : Prop :=
    forall L Q lo G pb x1 x2 t1 t2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_slot nctx Q G x1 t1 -> cbn_g_slot nctx Q G x2 t2 ->
      cbn_conv_slot X_type X Γ nctx d L pb x1 x2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb t1 t2).

  Definition cbn_spec_scc (d : cbn_fuel) : Prop :=
    forall L Q lo G a i l1 l2 ts1 ts2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_slots nctx Q G l1 ts1 -> cbn_g_slots nctx Q G l2 ts2 ->
      cbn_same_code_cells X_type X Γ nctx d L a i l1 l2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_cagree L Q a i ts1 ts2).

  (** [cbn_same_code_cells] skips a position whose two slots are one address (one reading) or
    whose slot the code does not use, and compares every other position with [cbn_conv_slot]. *)
  Lemma cbn_same_code_cells_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_slot (k tt) -> cbn_spec_scc (k tt) -> cbn_spec_scc (CbnFS k).
  Proof.
    intros hS hC L Q lo G a i l1 l2 ts1 ts2 rs s b rs' s' hm hr hl1 hl2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_same_code_cells_eq in he.
    destruct l1 as [|x1 l1]; destruct l2 as [|x2 l2].
    - injection he as <- <- <-. inversion hl1; subst. inversion hl2; subst.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros _. constructor.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hl1 as [|y1 m1 u1 us1 hx1 hm1]; subst.
      inversion hl2 as [|y2 m2 u2 us2 hx2 hm2]; subst.
      destruct (cbn_slot_same x1 x2 || noccur_between i 1 a) eqn:Esk.
      + destruct (hC L Q lo G a (S i) l1 l2 us1 us2 rs s b rs' s' hm hr hm1 hm2 he)
          as [hp hc].
        split; [exact hp|]. intros hb. constructor; [|exact (hc hb)].
        apply orb_true_iff in Esk as [Esame|Enocc]; [right|left; exact Enocc].
        destruct x1 as [a1|]; destruct x2 as [a2|]; cbn in Esame; try discriminate Esame.
        apply cbn_haddr_eqb_eq in Esame. subst a2.
        apply cbn_g_slot_addr_inv in hx1. apply cbn_g_slot_addr_inv in hx2.
        rewrite hx1 in hx2. injection hx2 as <-. exact (cbn_lift_conv_refl _ _ _ _ hL).
      + destruct (cbn_conv_slot X_type X Γ nctx (k tt) L Conv x1 x2
                    (CbnRSk l1 :: CbnRSk l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
          [|discriminate he].
        assert (hr' : Forall (cbn_rwf Q) (CbnRSk l1 :: CbnRSk l2 :: rs))
          by (constructor; [exact I|constructor; [exact I|exact hr]]).
        destruct (hS L Q lo G Conv x1 x2 u1 u2 _ s b2 rs2 s2 hm hr' hx1 hx2 Ecs)
          as [hp1 hc1].
        destruct b2.
        * destruct hp1 as (Q1 & lo1 & G1 & hq1 & hm1' & hr1 & hg1).
          destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
          destruct (cbn_gpq_RSk_inv _ _ _ _ _ _ hqa) as (l1' & -> & hk1).
          destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
          destruct (cbn_gpq_RSk_inv _ _ _ _ _ _ hqb) as (l2' & -> & hk2).
          cbv beta iota in he.
          destruct (hC L Q1 lo1 G1 a (S i) l1' l2' _ _ rsB s2 b rs' s' hm1'
                      (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hm1) (hk2 _ hm2) he)
            as [hp hc].
          split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
          intros hb. constructor; [right; exact (hc1 eq_refl)|].
          exact (cbn_cagree_lift _ _ _ _ _ _ _ hLQ hq1 (hc hb)).
        * cbv beta iota in he. injection he as <- <- <-.
          split; [exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hp1)|]. intros hb; discriminate hb.
  Qed.

  (** ** The statements of the other functions *)

  Definition cbn_spec_eval (d : cbn_fuel) : Prop :=
    forall L Q lo G pb x1 x2 t1 t2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_slot nctx Q G x1 t1 -> cbn_g_slot nctx Q G x2 t2 ->
      cbn_conv_eval X_type X Γ nctx d L pb x1 x2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb t1 t2).

  Definition cbn_spec_cells (d : cbn_fuel) : Prop :=
    forall L Q lo G l1 l2 ts1 ts2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_addrs G l1 ts1 -> cbn_g_addrs G l2 ts2 ->
      cbn_conv_cells X_type X Γ nctx d L l1 l2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv_s L Q ts1 ts2).

  Definition cbn_spec_term (d : cbn_fuel) : Prop :=
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_susp nctx Q G e1 c1.(cbn_c_term) t1 -> cbn_gcok G c1 ->
      cbn_g_susp nctx Q G e2 c2.(cbn_c_term) t2 -> cbn_gcok G c2 ->
      cbn_conv_term X_type X Γ nctx d L pb e1 c1 e2 c2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb t1 t2).

  (** Two codes [cbn_code_eq] accepts: one term, or equal up to universes at [Conv]. *)
  Definition cbn_samec (a1 a2 : term) : Prop := a1 = a2 \/ ∥ compare_term Σ Σ Conv a1 a2 ∥.

  (** [cbn_conv_same_code] answers [true] with the facts the same-code rule rests on; the
    conversion of the two readings follows from them ([cbn_same_code_lift_conv] below). *)
  Definition cbn_spec_same (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> cbn_gcok G c1 -> cbn_gcok G c2 ->
      cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 ->
      cbn_conv_same_code X_type X Γ nctx d L e1 c1 e2 c2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\
      (b = true -> e1.(cbn_ev_goff) = e2.(cbn_ev_goff) /\ e1.(cbn_ev_nvals) = e2.(cbn_ev_nvals)
                   /\ cbn_samec c1.(cbn_c_term) c2.(cbn_c_term) /\
                     cbn_cagree L Q c1.(cbn_c_term) 0 ts1 ts2).

  Definition cbn_spec_case (d : cbn_fuel) : Prop :=
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_susp nctx Q G e1 c1.(cbn_c_term) t1 -> cbn_gcok G c1 ->
      cbn_g_susp nctx Q G e2 c2.(cbn_c_term) t2 -> cbn_gcok G c2 ->
      cbn_case_cong X_type X Γ nctx d L e1 c1 e2 c2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb t1 t2).

  (** The parameter codes [cbn_case_params] walks: child [cbn_case_param_step i] onwards. *)
  Inductive cbn_pcodes (G : cbn_ghost) (c : cbn_code) : N -> list term -> Prop :=
  | cbn_pcodes_nil i : cbn_pcodes G c i []
  | cbn_pcodes_cons i t l :
      cbn_gcok G (cbn_child c (cbn_case_param_step i) t) -> cbn_pcodes G c (N.succ i) l ->
      cbn_pcodes G c i (t :: l).

  Definition cbn_spec_params (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 i l1 l2 us1 us2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_pcodes G c1 i l1 -> cbn_pcodes G c2 i l2 ->
      Forall2 (cbn_g_susp nctx Q G e1) l1 us1 -> Forall2 (cbn_g_susp nctx Q G e2) l2 us2 ->
      cbn_case_params X_type X Γ nctx d L e1 c1 e2 c2 i l1 l2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv_s L Q us1 us2).

  (** A branch body read at [Q] through slots [ts], under its own [#|bcontext|] binders, and
    what a [true] claims of two of them: the lifts by [Q - L] at the cut [#|bcontext|] of two
    terms scoped at [L + #|bcontext|] are convertible. *)
  Definition cbn_rbody (ts : list term) (N : nat) (br : branch term) : term :=
    subst ts #|br.(bcontext)| (lift N (#|br.(bcontext)| + #|ts|) br.(bbody)).

  #[local] Definition cbn_lift_conv_b (L Q k : nat) (pb : conv_pb) (B1 B2 : term) : Prop :=
    forall U1 U2 : term, B1 = lift (Q - L) k U1 -> B2 = lift (Q - L) k U2 ->
      cbn_scl (L + k) U1 -> cbn_scl (L + k) U2 -> cbn_cv (L + k) pb U1 U2.

  Inductive cbn_bcodes (G : cbn_ghost) (c : cbn_code) : N -> list (branch term) -> Prop :=
  | cbn_bcodes_nil i : cbn_bcodes G c i []
  | cbn_bcodes_cons i br l :
      cbn_gcok G (cbn_child c (cbn_case_branch_step i) br.(bbody)) -> cbn_bcodes G c (N.succ i) l ->
      cbn_bcodes G c i (br :: l).

  Definition cbn_spec_branches (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 i l1 l2 ts1 ts2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_bcodes G c1 i l1 -> cbn_bcodes G c2 i l2 ->
      cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> e1.(cbn_ev_nvals) = #|e1.(cbn_ev_vals)| ->
      cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 -> e2.(cbn_ev_nvals) = #|e2.(cbn_ev_vals)| ->
      cbn_case_branches X_type X Γ nctx d L e1 c1 e2 c2 i l1 l2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\
      (b = true -> Forall2 (fun br1 br2 =>
          cbn_case_ctx_ok br1.(bcontext) br2.(bcontext) = true
          /\ cbn_lift_conv_b L Q #|br1.(bcontext)| Conv
            (cbn_rbody ts1 (Q - nctx + e1.(cbn_ev_goff)) br1)
                 (cbn_rbody ts2 (Q - nctx + e2.(cbn_ev_goff)) br2)) l1 l2).

  Definition cbn_spec_rows_on (d : cbn_fuel) (R : cbn_value -> cbn_value -> Prop) : Prop :=
    forall L Q lo G pb v1 v2 w1 w2 rs s b rs' s',
      R v1 v2 -> cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> cbn_vwf Q v1 -> cbn_vwf Q v2 ->
      cbn_g_value nctx Q G v1 w1 -> cbn_g_value nctx Q G v2 w2 ->
      cbn_conv_rows X_type X Γ nctx d L pb v1 v2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb w1 w2).

  Definition cbn_spec_rows (d : cbn_fuel) : Prop := cbn_spec_rows_on d (fun _ _ => True).

  Definition cbn_spec_value (d : cbn_fuel) : Prop :=
    forall L Q lo G pb v1 v2 w1 w2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> cbn_vwf Q v1 -> cbn_vwf Q v2 ->
      cbn_g_value nctx Q G v1 w1 -> cbn_g_value nctx Q G v2 w2 ->
      cbn_conv_value X_type X Γ nctx d L pb v1 v2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb w1 w2).

  (** All eleven functions at one fuel: the induction hypothesis of the comparison. *)
  Definition cbn_spec_all (d : cbn_fuel) : Prop :=
    cbn_spec_slot d /\ cbn_spec_eval d /\ cbn_spec_cells d /\ cbn_spec_term d /\ cbn_spec_same d /\
      cbn_spec_scc d
    /\ cbn_spec_case d /\ cbn_spec_params d /\ cbn_spec_branches d /\ cbn_spec_rows d /\
      cbn_spec_value d.

  (** The base case of the induction: at [CbnFO] every function of the comparison answers
    [CbnCFail CbnWDepth]. This is not evidence that the statements say anything; see the witness
    lemmas for that. *)
  Lemma cbn_spec_all_FO : cbn_spec_all CbnFO.
  Proof.
    repeat split; repeat intro;
      match goal with h : _ = CbnCOk _ |- _ => cbn in h; discriminate h end.
  Qed.

  (** ** Helpers for the step lemmas *)

  Lemma cbn_post_level L L' Q G rs s' rs' :
    nctx <= L -> L <= L' -> cbn_post L' Q G rs s' rs' -> cbn_post L Q G rs s' rs'.
  Proof.
    intros h1 h2 (Q' & lo' & G' & hq & [hL hLQ hok hw] & hr & hg).
    exists Q', lo', G'. split; [exact hq|].
    split; [constructor; [exact h1|lia|exact hok|exact hw]|].
    split; assumption.
  Qed.

  Lemma cbn_gren_cons_inv Q G G' r rs rs1 :
    cbn_gren nctx Q G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ cbn_gpres nctx Q G G' r r' /\ cbn_gren nctx Q G G' rs rs'.
  Proof.
    intros [hc hf]. destruct rs1 as [|r' rs']; [inversion hf|].
    exists r', rs'. split; [reflexivity|].
    inversion hf; subst. split; [assumption|split; assumption].
  Qed.

  Lemma cbn_gpres_RE_inv Q G G' e r :
    cbn_gpres nctx Q G G' (CbnRE e) r -> exists e', r = CbnRE e' /\ cbn_genv nctx Q G G' e e'.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_gpres_RV_inv Q G G' v r :
    cbn_gpres nctx Q G G' (CbnRV v) r ->
    exists v', r = CbnRV v' /\ forall t, cbn_g_value nctx Q G v t -> cbn_g_value nctx Q G' v' t.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_gpres_RSl_inv Q G G' x r :
    cbn_gpres nctx Q G G' (CbnRSl x) r ->
    exists x', r = CbnRSl x' /\ forall t, cbn_g_slot nctx Q G x t -> cbn_g_slot nctx Q G' x' t.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma cbn_ctx_closed_jctx n : is_closed_context (Γ ,,, cbn_jctx n).
  Proof. rewrite on_free_vars_ctx_app, hΓ. apply cbn_jctx_closed. Qed.

  Lemma cbn_red_scl L Δ v u :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) -> cbn_scl L v ->
    PCUICReduction.red Σ (Γ ,,, Δ) v u -> cbn_scl L u.
  Proof.
    intros hL hΔ hcl hv hr. unfold cbn_scl in *.
    assert (e : #|Γ ,,, Δ| = L) by (rewrite app_context_length, hΔ, <- hnctx; lia).
    assert (hc : on_ctx_free_vars (shiftnP L cbn_xpred0) (Γ ,,, Δ)).
    { rewrite <- e, on_free_vars_ctx_on_ctx_free_vars. exact hcl. }
    exact (PCUICRenameConv.red_on_free_vars (wfΣ := wfΣ) hc hv hr).
  Qed.

  Lemma cbn_scl_hyg L u : cbn_scl L u -> on_free_vars cbn_xpredT u.
  Proof. intros h. eapply on_free_vars_impl; [|exact h]. intros; reflexivity. Qed.

  (** The readings of the inputs reduce, at the master level, to the readings of their values:
    a [true] about the values is a [true] about the inputs. *)
  Lemma cbn_lift_conv_red L Q pb t1 t2 w1 w2 :
    nctx <= L -> L <= Q ->
    cbn_cred Γ Σ (cbn_jctx (Q - nctx)) t1 w1 -> cbn_cred Γ Σ (cbn_jctx (Q - nctx)) t2 w2 ->
    cbn_lift_conv L Q pb w1 w2 -> cbn_lift_conv L Q pb t1 t2.
  Proof.
    intros hL hQ hr1 hr2 h u1 u2 e1 e2 s1 s2 Δ hΔ hcl. subst t1 t2.
    destruct (cbn_cred_unlift Γ nctx Σ wfΣ hΓ L Q u1 w1 hL hQ (cbn_scl_hyg L u1 s1) hr1)
      as (w1' & -> & hd1).
    destruct (cbn_cred_unlift Γ nctx Σ wfΣ hΓ L Q u2 w2 hL hQ (cbn_scl_hyg L u2 s2) hr2)
      as (w2' & -> & hd2).
    assert (hj : #|cbn_jctx (L - nctx)| = L - nctx) by apply cbn_jctx_length.
    destruct (hd1 _ hj) as [rj1]. destruct (hd2 _ hj) as [rj2].
    pose proof (cbn_red_scl L _ u1 w1' hL hj (cbn_ctx_closed_jctx _) s1 rj1) as sw1.
    pose proof (cbn_red_scl L _ u2 w2' hL hj (cbn_ctx_closed_jctx _) s2 rj2) as sw2.
    destruct (h w1' w2' eq_refl eq_refl sw1 sw2 Δ hΔ hcl) as [hc].
    destruct (hd1 Δ hΔ) as [r1]. destruct (hd2 Δ hΔ) as [r2].
    constructor.
    eapply (cbn_ws_cumul_pb_closed_red (wfΣ := wfΣ)); [| |exact hc].
    - exact (into_closed_red r1 hcl (cbn_scl_open L Δ u1 hL hΔ s1)).
    - exact (into_closed_red r2 hcl (cbn_scl_open L Δ u2 hL hΔ s2)).
  Qed.

  Lemma cbn_lift_conv_s_nil L Q : cbn_lift_conv_s L Q [] [].
  Proof.
    intros us1 us2 e1 e2 _ _ Δ _ _.
    destruct us1; [|discriminate e1]. destruct us2; [|discriminate e2].
    constructor. constructor.
  Qed.

  Lemma cbn_lift_conv_s_cons L Q t1 t2 ts1 ts2 :
    cbn_lift_conv L Q Conv t1 t2 -> cbn_lift_conv_s L Q ts1 ts2 ->
      cbn_lift_conv_s L Q (t1 :: ts1) (t2 :: ts2).
  Proof.
    intros h hs us1 us2 e1 e2 s1 s2 Δ hΔ hcl.
    destruct us1 as [|u1 us1]; [discriminate e1|]. destruct us2 as [|u2 us2]; [discriminate e2|].
    cbn in e1, e2. injection e1 as e1 e1'. injection e2 as e2 e2'.
    cbn in s1, s2. apply andb_true_iff in s1 as [s1 s1']. apply andb_true_iff in s2 as [s2 s2'].
    destruct (h u1 u2 e1 e2 s1 s2 Δ hΔ hcl) as [hc].
    destruct (hs us1 us2 e1' e2' s1' s2' Δ hΔ hcl) as [hcs].
    constructor. constructor; assumption.
  Qed.

  Lemma cbn_mkApps_lift0_inv m h ts u :
    mkApps h ts = lift0 m u ->
    exists h' us, u = mkApps h' us /\ h = lift0 m h' /\ ts = map (lift0 m) us.
  Proof.
    revert u. induction ts as [|t ts ih] using rev_ind; intros u e.
    - exists u, []. cbn in e |- *. split; [reflexivity|]. split; [exact e|reflexivity].
    - rewrite mkApps_app in e. cbn in e.
      destruct u as [| | | | | | |u1 u2| | | | | | | |]; cbn in e; try discriminate e.
      injection e as e1 e2.
      destruct (ih _ e1) as (h' & us & -> & -> & ->).
      exists h', (us ++ [u2]). split; [rewrite mkApps_app; reflexivity|]. split; [reflexivity|].
      rewrite map_app. cbn. rewrite e2. reflexivity.
  Qed.

  Lemma cbn_lift0_closed_inv m h h' : closedn 0 h -> h = lift0 m h' -> h' = h.
  Proof.
    intros hc e. apply (PCUICCallByNeedSoundReadBack.cbn_lift0_inj m).
    transitivity h; [symmetry; exact e|symmetry; exact (lift_closed _ _ _ hc)].
  Qed.

  (** ** [cbn_conv_cells] *)

  Lemma cbn_conv_cells_eq k L l1 l2 rs s :
    cbn_conv_cells X_type X Γ nctx (CbnFS k) L l1 l2 rs s =
    match l1, l2 with
    | [], [] => CbnCOk (true, rs, s)
    | a1 :: l1, a2 :: l2 =>
      match cbn_conv_slot X_type X Γ nctx (k tt) L Conv (CbnSAddr a1) (CbnSAddr a2)
              (CbnRSp l1 :: CbnRSp l2 :: rs) s with
      | CbnCOk (true, rs, s) =>
        match rs with
        | CbnRSp l1 :: CbnRSp l2 :: rs => cbn_conv_cells X_type X Γ nctx (k tt) L l1 l2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
      | CbnCFail w => CbnCFail w
      end
    | _, _ => CbnCOk (false, rs, s)
    end.
  Proof. reflexivity. Qed.

  Lemma cbn_conv_cells_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_slot (k tt) -> cbn_spec_cells (k tt) -> cbn_spec_cells (CbnFS k).
  Proof.
    intros hS hC L Q lo G l1 l2 ts1 ts2 rs s b rs' s' hm hr hl1 hl2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_cells_eq in he.
    destruct l1 as [|a1 l1]; destruct l2 as [|a2 l2].
    - injection he as <- <- <-. inversion hl1; subst. inversion hl2; subst.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros _. apply cbn_lift_conv_s_nil.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hl1 as [|y1 u1 m1 us1 hx1 hm1]; subst.
      inversion hl2 as [|y2 u2 m2 us2 hx2 hm2]; subst.
      destruct (cbn_conv_slot X_type X Γ nctx (k tt) L Conv (CbnSAddr a1) (CbnSAddr a2)
                  (CbnRSp l1 :: CbnRSp l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
        [|discriminate he].
      assert (hr' : Forall (cbn_rwf Q) (CbnRSp l1 :: CbnRSp l2 :: rs))
        by (constructor; [exact I|constructor; [exact I|exact hr]]).
      destruct (hS L Q lo G Conv (CbnSAddr a1) (CbnSAddr a2) u1 u2 _ s b2 rs2 s2 hm hr'
                  ltac:(constructor; exact hx1) ltac:(constructor; exact hx2) Ecs) as [hp1 hc1].
      destruct b2.
      + destruct hp1 as (Q1 & lo1 & G1 & hq1 & hm1' & hr1 & hg1).
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
        destruct (cbn_gpq_RSp_inv _ _ _ _ _ _ hqa) as (l1' & -> & hk1).
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
        destruct (cbn_gpq_RSp_inv _ _ _ _ _ _ hqb) as (l2' & -> & hk2).
        cbv beta iota in he.
        destruct (hC L Q1 lo1 G1 l1' l2' _ _ rsB s2 b rs' s' hm1'
                    (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hm1) (hk2 _ hm2) he)
          as [hp hc].
        split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
        intros hb. apply cbn_lift_conv_s_cons; [exact (hc1 eq_refl)|].
        exact (cbn_lift_conv_s_lift _ _ _ _ _ hLQ hq1 (hc hb)).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hp1)|]. intros hb; discriminate hb.
  Qed.

  (** ** [cbn_conv_eval] and [cbn_conv_term]: the machine, then the values *)

  Lemma cbn_conv_eval_eq k L le x1 x2 rs s :
    cbn_conv_eval X_type X Γ nctx (CbnFS k) L le x1 x2 rs s =
    match cbn_eval_slot X_type X Γ nctx (k tt) x1 [] (CbnRSl x2 :: rs) s with
    | CbnCOk (v1, rs, s) =>
      match rs with
      | CbnRSl x2 :: rs =>
        match cbn_eval_slot X_type X Γ nctx (k tt) x2 [] (CbnRV v1 :: rs) s with
        | CbnCOk (v2, rs, s) =>
          match rs with
          | CbnRV v1 :: rs => cbn_conv_value X_type X Γ nctx (k tt) L le v1 v2 rs s
          | _ => CbnCFail CbnWRoots
          end
        | CbnCFail w => CbnCFail w
        end
      | _ => CbnCFail CbnWRoots
      end
    | CbnCFail w => CbnCFail w
    end.
  Proof. reflexivity. Qed.

  Lemma cbn_conv_term_eq k L le e1 c1 e2 c2 rs s :
    cbn_conv_term X_type X Γ nctx (CbnFS k) L le e1 c1 e2 c2 rs s =
    match cbn_whnf X_type X Γ nctx (k tt) e1 c1 [] (CbnRE e2 :: rs) s with
    | CbnCOk (v1, rs, s) =>
      match rs with
      | CbnRE e2 :: rs =>
        match cbn_whnf X_type X Γ nctx (k tt) e2 c2 [] (CbnRV v1 :: rs) s with
        | CbnCOk (v2, rs, s) =>
          match rs with
          | CbnRV v1 :: rs => cbn_conv_value X_type X Γ nctx (k tt) L le v1 v2 rs s
          | _ => CbnCFail CbnWRoots
          end
        | CbnCFail w => CbnCFail w
        end
      | _ => CbnCFail CbnWRoots
      end
    | CbnCFail w => CbnCFail w
    end.
  Proof. reflexivity. Qed.

  Lemma cbn_conv_eval_sound_g (k : unit -> cbn_fuel) : cbn_spec_value (k tt) ->
    cbn_spec_eval (CbnFS k).
  Proof.
    intros hV L Q lo G pb x1 x2 t1 t2 rs s b rs' s' hm hr hx1 hx2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_eval_eq in he.
    destruct (cbn_eval_slot X_type X Γ nctx (k tt) x1 [] (CbnRSl x2 :: rs) s)
      as [[[v1 rs1] s1]|w] eqn:E1; [|discriminate he].
    destruct (cbn_eval_slot_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo G
                x1 [] [] t1 _ s v1 rs1 s1 hm (Forall_cons (CbnRSl x2) I hr) hx1
                  ltac:(constructor) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & hw1 & hd1).
    destruct (cbn_gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rs1' & -> & hq1 & hg1').
    destruct (cbn_gpres_RSl_inv _ _ _ _ _ hq1) as (x2' & -> & hk1).
    cbv beta iota in he.
    destruct (cbn_eval_slot X_type X Γ nctx (k tt) x2' [] (CbnRV v1 :: rs1') s1)
      as [[[v2 rs2] s2]|w] eqn:E2; [|discriminate he].
    destruct (cbn_eval_slot_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo1 G1
                x2' [] [] t2 _ s1 v2 rs2 s2 hm1 (Forall_cons (CbnRV v1) hv1 (Forall_inv_tail hr1))
                (hk1 _ hx2) ltac:(constructor) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & hw2 & hd2).
    destruct (cbn_gren_cons_inv _ _ _ _ _ _ hg2) as (q2 & rs2' & -> & hq2 & hg2').
    destruct (cbn_gpres_RV_inv _ _ _ _ _ hq2) as (v1' & -> & hk2).
    cbv beta iota in he.
    destruct (hV L Q lo2 G2 pb v1' v2 w1 w2 rs2' s2 b rs' s' hm2 (Forall_inv_tail hr2)
                (Forall_inv hr2) hv2 (hk2 _ hw1) hw2 he) as [hp hc].
    pose proof (proj1 (proj2 (cbn_machine_skel X_type X Γ nctx (k tt))) _ _ _ _ _ _ _ E1)
      as hK1.
    pose proof (proj1 (proj2 (cbn_machine_skel X_type X Γ nctx (k tt))) _ _ _ _ _ _ _ E2)
      as hK2.
    split.
    - apply (cbn_post_compose L Q Q G G2 rs rs2' s' rs' (le_n Q)); [|exact hp].
      apply (cbn_grq_trans Q Q Q G G1 G2 rs rs1' rs2' (le_n Q) (le_n Q));
        (apply cbn_grq_of_gren; [assumption|eapply cbn_sk_tl; eassumption]).
    - intros hb. exact (cbn_lift_conv_red L Q pb t1 t2 w1 w2 hL hLQ hd1 hd2 (hc hb)).
  Qed.

  Lemma cbn_conv_term_sound_g (k : unit -> cbn_fuel) : cbn_spec_value (k tt) ->
    cbn_spec_term (CbnFS k).
  Proof.
    intros hV L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_term_eq in he.
    destruct (cbn_whnf X_type X Γ nctx (k tt) e1 c1 [] (CbnRE e2 :: rs) s)
      as [[[v1 rs1] s1]|w] eqn:E1; [|discriminate he].
    destruct (cbn_whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo G
                e1 c1 [] [] t1 _ s v1 rs1 s1 hm (Forall_cons (CbnRE e2) I hr) hs1 hc1
                  ltac:(constructor) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & hw1 & hd1).
    destruct (cbn_gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rs1' & -> & hq1 & hg1').
    destruct (cbn_gpres_RE_inv _ _ _ _ _ hq1) as (e2' & -> & hk1).
    cbv beta iota in he.
    destruct (cbn_whnf X_type X Γ nctx (k tt) e2' c2 [] (CbnRV v1 :: rs1') s1)
      as [[[v2 rs2] s2]|w] eqn:E2; [|discriminate he].
    destruct (cbn_whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo1 G1
                e2' c2 [] [] t2 _ s1 v2 rs2 s2 hm1
                  (Forall_cons (CbnRV v1) hv1 (Forall_inv_tail hr1))
                (cbn_genv_susp _ _ _ _ _ _ _ _ hk1 hs2) (cbn_cok_gcx _ _ (proj1 hg1) _ hc2)
                ltac:(constructor) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & hw2 & hd2).
    destruct (cbn_gren_cons_inv _ _ _ _ _ _ hg2) as (q2 & rs2' & -> & hq2 & hg2').
    destruct (cbn_gpres_RV_inv _ _ _ _ _ hq2) as (v1' & -> & hk2).
    cbv beta iota in he.
    destruct (hV L Q lo2 G2 pb v1' v2 w1 w2 rs2' s2 b rs' s' hm2 (Forall_inv_tail hr2)
                (Forall_inv hr2) hv2 (hk2 _ hw1) hw2 he) as [hp hc].
    pose proof (proj1 (proj2 (proj2 (cbn_machine_skel X_type X Γ nctx (k tt))))
                  _ _ _ _ _ _ _ _ E1) as hK1.
    pose proof (proj1 (proj2 (proj2 (cbn_machine_skel X_type X Γ nctx (k tt))))
                  _ _ _ _ _ _ _ _ E2) as hK2.
    split.
    - apply (cbn_post_compose L Q Q G G2 rs rs2' s' rs' (le_n Q)); [|exact hp].
      apply (cbn_grq_trans Q Q Q G G1 G2 rs rs1' rs2' (le_n Q) (le_n Q));
        (apply cbn_grq_of_gren; [assumption|eapply cbn_sk_tl; eassumption]).
    - intros hb. exact (cbn_lift_conv_red L Q pb t1 t2 w1 w2 hL hLQ hd1 hd2 (hc hb)).
  Qed.

  (** ** The rows that compare heads and spines *)

  Lemma cbn_conv_rows_con_eq k L le h1 sp1 h2 sp2 rs s :
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVCon h1 sp1) (CbnVCon h2 sp2) rs s =
    if (#|sp1| == #|sp2|) && cbn_cmp_term X_type X le #|sp1| h1 h2
    then cbn_conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s else CbnCOk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_conv_rows_var_eq k L le l1 sp1 l2 sp2 rs s :
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVNeu (CbnNVar l1) sp1)
      (CbnVNeu (CbnNVar l2) sp2) rs s =
    if l1 == l2 then cbn_conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s
    else CbnCOk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_conv_rows_const_eq k L le h1 sp1 h2 sp2 rs s :
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVNeu (CbnNConst h1) sp1)
      (CbnVNeu (CbnNConst h2) sp2)
      rs s =
    if cbn_cmp_term X_type X Conv #|sp1| h1 h2
    then cbn_conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s else CbnCOk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_conv_rows_sort_eq k L le e1 c1 e2 c2 s1 s2 rs s :
    c1.(cbn_c_term) = tSort s1 -> c2.(cbn_c_term) = tSort s2 ->
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVOpen e1 c1) (CbnVOpen e2 c2) rs s
    = CbnCOk (cbn_cmp_sort X_type X le s1 s2, rs, s).
  Proof.
    destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity.
  Qed.

  (** Shared tail of the spine rows: equal heads (up to the head test) and convertible
    spines give convertible applications. *)
  Lemma cbn_cv_spine L pb h1 h2 us1 us2 :
    nctx <= L -> (forall Δ, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
                    ∥ Σ ;;; Γ ,,, Δ ⊢ h1 ≤[pb] h2 ∥) ->
    cbn_cvs L us1 us2 -> cbn_cv L pb (mkApps h1 us1) (mkApps h2 us2).
  Proof.
    intros hL hh hs Δ hΔ hcl. destruct (hh Δ hΔ hcl) as [h]. destruct (hs Δ hΔ hcl) as [hs'].
    constructor. exact (ws_cumul_pb_mkApps (wfΣ := wfΣ) h hs').
  Qed.

  Lemma cbn_conv_rows_con_g (k : unit -> cbn_fuel) :
    cbn_spec_cells (k tt) ->
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists h1 sp1 h2 sp2, v1 = CbnVCon h1 sp1 /\
      v2 = CbnVCon h2 sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (h1 & sp1 & h2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_rows_con_eq in he.
    apply cbn_g_value_VCon_inv in hw1 as (ts1 & -> & ha1).
    apply cbn_g_value_VCon_inv in hw2 as (ts2 & -> & ha2).
    cbn in hv1, hv2.
    destruct ((#|sp1| == #|sp2|) && cbn_cmp_term X_type X pb #|sp1| h1 h2) eqn:Et;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Et as [_ Ecmp].
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply cbn_mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply cbn_mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    pose proof (cbn_lift0_closed_inv _ _ _ hv1 eh1) as ->.
    pose proof (cbn_lift0_closed_inv _ _ _ hv2 eh2) as ->.
    unfold cbn_scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    intros Δ hΔ hcl.
    destruct (hc hb us1 us2 eq_refl eq_refl sus1 sus2 Δ hΔ hcl) as [hcs].
    constructor.
    apply (cbn_ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
      [exact hcl|exact (cbn_scl_open L Δ h1 hL hΔ sh1)|exact (cbn_scl_open L Δ h2 hL hΔ sh2)|
        |exact hcs].
    pose proof (cbn_cmp_term_sound X_type X Σ hΣ pb _ h1 h2 Ecmp) as hcmp.
    rewrite <- (cbn_g_addrs_length _ _ _ ha1), length_map in hcmp. exact hcmp.
  Qed.

  Lemma cbn_conv_rows_const_g (k : unit -> cbn_fuel) :
    cbn_spec_cells (k tt) ->
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists h1 sp1 h2 sp2,
                           v1 = CbnVNeu (CbnNConst h1) sp1 /\ v2 = CbnVNeu (CbnNConst h2) sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (h1 & sp1 & h2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_rows_const_eq in he.
    apply cbn_g_value_VNeu_inv in hw1 as [(l & ts & e & _)|(h1' & ts1 & e & -> & ha1)];
      [discriminate e|injection e as <-].
    apply cbn_g_value_VNeu_inv in hw2 as [(l & ts & e & _)|(h2' & ts2 & e & -> & ha2)];
      [discriminate e|injection e as <-].
    cbn in hv1, hv2.
    destruct (cbn_cmp_term X_type X Conv #|sp1| h1 h2) eqn:Ecmp;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply cbn_mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply cbn_mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    pose proof (cbn_lift0_closed_inv _ _ _ hv1 eh1) as ->.
    pose proof (cbn_lift0_closed_inv _ _ _ hv2 eh2) as ->.
    unfold cbn_scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    intros Δ hΔ hcl.
    destruct (hc hb us1 us2 eq_refl eq_refl sus1 sus2 Δ hΔ hcl) as [hcs].
    constructor. apply (ws_cumul_eq_pb (wfΣ := wfΣ)).
    apply (cbn_ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
      [exact hcl|exact (cbn_scl_open L Δ h1 hL hΔ sh1)|exact (cbn_scl_open L Δ h2 hL hΔ sh2)|
        |exact hcs].
    pose proof (cbn_cmp_term_sound X_type X Σ hΣ Conv _ h1 h2 Ecmp) as hcmp.
    rewrite <- (cbn_g_addrs_length _ _ _ ha1), length_map in hcmp. exact hcmp.
  Qed.

  Lemma cbn_conv_rows_var_g (k : unit -> cbn_fuel) :
    cbn_spec_cells (k tt) ->
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists l1 sp1 l2 sp2,
                           v1 = CbnVNeu (CbnNVar l1) sp1 /\ v2 = CbnVNeu (CbnNVar l2) sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (l1 & sp1 & l2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_rows_var_eq in he.
    apply cbn_g_value_VNeu_inv in hw1 as [(l1' & ts1 & e & -> & ha1)|(h & ts & e & _)];
      [injection e as <-|discriminate e].
    apply cbn_g_value_VNeu_inv in hw2 as [(l2' & ts2 & e & -> & ha2)|(h & ts & e & _)];
      [injection e as <-|discriminate e].
    destruct (l1 == l2) eqn:El;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply eqb_eq in El. subst l2.
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply cbn_mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply cbn_mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    rewrite eh1 in eh2. apply PCUICCallByNeedSoundReadBack.cbn_lift0_inj in eh2. subst h2'.
    unfold cbn_scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [_ sus2].
    apply cbn_cv_spine; [exact hL| |exact (hc hb us1 us2 eq_refl eq_refl sus1 sus2)].
    intros Δ hΔ hcl. constructor. apply ws_cumul_pb_refl;
      [exact hcl|exact (cbn_scl_open L Δ h1' hL hΔ sh1)].
  Qed.

  Lemma cbn_conv_rows_sort_g (k : unit -> cbn_fuel) :
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists e1 c1 e2 c2 s1 s2,
                           v1 = CbnVOpen e1 c1 /\ v2 = CbnVOpen e2 c2
                           /\ c1.(cbn_c_term) = tSort s1 /\ c2.(cbn_c_term) = tSort s2).
  Proof.
    intros L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & e2 & c2 & s1 & s2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (cbn_conv_rows_sort_eq k L pb e1 c1 e2 c2 s1 s2 rs s h1 h2) in he.
    injection he as <- <- <-.
    split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hcs u1 u2 e1' e2' _ _ Δ hΔ hcl.
    apply cbn_g_value_VOpen_inv in hw1. apply cbn_g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & _ & _ & ->).
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & _ & _ & ->).
    cbn in e1', e2'.
    destruct u1; cbn in e1'; try discriminate e1'. injection e1' as <-.
    destruct u2; cbn in e2'; try discriminate e2'. injection e2' as <-.
    constructor. apply cbn_ws_cumul_pb_compare_term; [exact hcl|reflexivity|reflexivity|].
    constructor. exact (cbn_cmp_sort_sound X_type X Σ hΣ pb s1 s2 hcs).
  Qed.

  (** ** Fresh variables at the master level *)

  (** A fresh-variable cell for level [lvl < Q] reads [tRel (Q - S lvl)]; allocating it keeps
    [cbn_minv] ([cbn_alloc_sound], [cbn_alloc_hwf_holds]). *)
  Lemma cbn_alloc_fresh_g L Q lo G lvl rs s x rs' s' :
    cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> lvl < Q ->
    cbn_alloc (CbnCDone (CbnVNeu (CbnNVar lvl) [])) rs s = CbnCOk (x, rs', s') ->
    exists lo' G', cbn_MI L Q lo' G' s' /\ Forall (cbn_rwf Q) rs' /\ cbn_gren nctx Q G G' rs rs'
      /\ G' x = Some (tRel (Q - S lvl)).
  Proof.
    intros [hL hLQ hok hw] hr hlt he.
    assert (hj : #|cbn_jctx (Q - nctx)| = Q - nctx) by apply cbn_jctx_length.
    assert (hc : cbn_g_cell nctx Q G (CbnCDone (CbnVNeu (CbnNVar lvl) [])) (tRel (Q - S lvl))).
    { apply cbn_g_cell_done. apply (cbn_g_VNeuVar _ _ _ lvl [] []). constructor. }
    destruct (cbn_alloc_sound X_type X Γ nctx Σ (cbn_jctx (Q - nctx)) Q hj hnctx ltac:(lia) lo G
                _ _ rs s x rs' s' hok hc (fun _ => eq_refl) he)
      as (lo' & G' & hg & hok' & hx).
    destruct (cbn_alloc_hwf_holds nctx Q (CbnCDone (CbnVNeu (CbnNVar lvl) [])) rs s x rs' s'
                ltac:(lia) hw hlt hr he) as [hw' hr'].
    exists lo', G'. split; [constructor; assumption|]. split; [exact hr'|]. split; assumption.
  Qed.

  Lemma cbn_fresh_reads_S Q lvl n ts :
    lvl + S n <= Q ->
    map (lift0 (Q - (S lvl + n))) (idsn n) ++ tRel (Q - S lvl) :: ts
    = map (lift0 (Q - (lvl + S n))) (idsn (S n)) ++ ts.
  Proof.
    intros h. replace (Q - (lvl + S n)) with (Q - (S lvl + n)) by lia.
    cbn [idsn]. rewrite map_app, <- app_assoc. cbn [map app]. f_equal. f_equal.
    cbn. f_equal. lia.
  Qed.

  (** [cbn_push_fresh n lvl] pushes [n] fresh variables, levels [lvl] to [lvl + n - 1], on both
    environments; at the master level they read as the lift of [idsn n]. *)
  Lemma cbn_push_fresh_g (n : nat) :
    forall L Q lo G lvl e1 e2 ts1 ts2 rs s r rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> lvl + n <= Q ->
      cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> e1.(cbn_ev_nvals) = #|e1.(cbn_ev_vals)| ->
      cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 -> e2.(cbn_ev_nvals) = #|e2.(cbn_ev_vals)| ->
      cbn_push_fresh n lvl e1 e2 rs s = CbnCOk (r, rs', s') ->
      exists lo' G' f1 f2,
        r = (lvl + n, f1, f2) /\ cbn_MI L Q lo' G' s' /\ Forall (cbn_rwf Q) rs'
        /\ cbn_gren nctx Q G G' rs rs'
        /\ f1.(cbn_ev_nvals) = #|f1.(cbn_ev_vals)| /\ f1.(cbn_ev_goff) = e1.(cbn_ev_goff)
        /\ f2.(cbn_ev_nvals) = #|f2.(cbn_ev_vals)| /\ f2.(cbn_ev_goff) = e2.(cbn_ev_goff)
        /\ cbn_g_slots nctx Q G' f1.(cbn_ev_vals) (map (lift0 (Q - (lvl + n))) (idsn n) ++ ts1)
        /\ cbn_g_slots nctx Q G' f2.(cbn_ev_vals) (map (lift0 (Q - (lvl + n))) (idsn n) ++ ts2).
  Proof.
    induction n as [|n ih];
      intros L Q lo G lvl e1 e2 ts1 ts2 rs s r rs' s' hm hr hq hs1 hn1 hs2 hn2 he.
    - rewrite cbn_pfd_push_fresh_O in he. injection he as <- <- <-.
      exists lo, G, e1, e2. rewrite Nat.add_0_r. split; [reflexivity|].
      split; [exact hm|]. split; [exact hr|]. split; [apply cbn_gren_refl|].
      cbn [idsn map app]. repeat split; assumption.
    - rewrite cbn_pfd_push_fresh_S in he.
      destruct (cbn_alloc (CbnCDone (CbnVNeu (CbnNVar lvl) [])) (CbnRE e1 :: CbnRE e2 :: rs) s)
        as [[[x rs1] s1]|w] eqn:Ea; [|discriminate he].
      destruct (cbn_alloc_fresh_g L Q lo G lvl _ s x rs1 s1 hm
                  (Forall_cons (CbnRE e1) I (Forall_cons (CbnRE e2) I hr)) ltac:(lia) Ea)
        as (lo1 & G1 & hm1 & hr1 & hg1 & hx).
      destruct (cbn_gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hq1 & hgA).
      destruct (cbn_gpres_RE_inv _ _ _ _ _ hq1) as (e1' & -> & (hn1' & hg1' & hk1)).
      destruct (cbn_gren_cons_inv _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hq2 & hgB).
      destruct (cbn_gpres_RE_inv _ _ _ _ _ hq2) as (e2' & -> & (hn2' & hg2' & hk2)).
      cbv beta iota in he.
      pose proof (hk1 _ hs1) as hs1'. pose proof (hk2 _ hs2) as hs2'.
      pose proof (cbn_g_slots_length _ _ _ _ _ hs1) as hl1.
      pose proof (cbn_g_slots_length _ _ _ _ _ hs1') as hl1'.
      pose proof (cbn_g_slots_length _ _ _ _ _ hs2) as hl2.
      pose proof (cbn_g_slots_length _ _ _ _ _ hs2') as hl2'.
      destruct (ih L Q lo1 G1 (S lvl) (cbn_env_push (CbnSAddr x) e1')
        (cbn_env_push (CbnSAddr x) e2')
                  (tRel (Q - S lvl) :: ts1) (tRel (Q - S lvl) :: ts2) rsB s1 r rs' s' hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) ltac:(lia)
                  ltac:(constructor; [constructor; exact hx|exact hs1'])
                  ltac:(cbn; lia)
                  ltac:(constructor; [constructor; exact hx|exact hs2'])
                  ltac:(cbn; lia) he)
        as (lo' & G' & f1 & f2 & -> & hm' & hr' & hg' & hf1 & hgo1 & hf2 & hgo2 & hr1' & hr2').
      exists lo', G', f1, f2.
      split; [do 2 f_equal; lia|]. split; [exact hm'|]. split; [exact hr'|].
      split; [exact (cbn_gren_trans _ _ _ _ _ _ _ _ hgB hg')|].
      split; [exact hf1|]. split; [rewrite hgo1; exact hg1'|].
      split; [exact hf2|]. split; [rewrite hgo2; exact hg2'|].
      rewrite <- !(cbn_fresh_reads_S Q lvl n) by lia. split; assumption.
  Qed.

  (** ** Environments across a call *)

  Lemma cbn_gsusp_q Q Q' G G' e e' t u :
    nctx <= Q -> Q <= Q' -> cbn_gpq Q Q' G G' (CbnRE e) (CbnRE e') ->
    cbn_g_susp nctx Q G e t u -> cbn_g_susp nctx Q' G' e' t (lift0 (Q' - Q) u).
  Proof.
    intros hQ hQ' (hn & hg & hk) hs.
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hs) as (ts & hts & hnv & ->).
    pose proof (hk _ hts) as hts'.
    pose proof (cbn_g_slots_length _ _ _ _ _ hts) as hl.
    pose proof (cbn_g_slots_length _ _ _ _ _ hts') as hl'. rewrite length_map in hl'.
    rewrite (cbn_lift_susp_read nctx Q (Q' - Q) hQ (Q - nctx + cbn_ev_goff e) (cbn_ev_nvals e) t ts
               ltac:(lia)).
    replace (Q' - Q + (Q - nctx + cbn_ev_goff e)) with (Q' - nctx + cbn_ev_goff e') by lia.
    rewrite <- hn. apply cbn_g_susp_of_slots; [exact hts'|lia].
  Qed.

  Lemma cbn_gsusps_q Q Q' G G' e e' l us :
    nctx <= Q -> Q <= Q' -> cbn_gpq Q Q' G G' (CbnRE e) (CbnRE e') ->
    Forall2 (cbn_g_susp nctx Q G e) l us ->
      Forall2 (cbn_g_susp nctx Q' G' e') l (map (lift0 (Q' - Q)) us).
  Proof.
    intros hQ hQ' hp h. induction h; constructor; [|exact IHh].
    exact (cbn_gsusp_q _ _ _ _ _ _ _ _ hQ hQ' hp H).
  Qed.

  Lemma cbn_pcodes_gcx G G' c i l : cbn_gcx G G' -> cbn_pcodes G c i l -> cbn_pcodes G' c i l.
  Proof.
    intros hc h. induction h; constructor; [exact (cbn_cok_gcx _ _ hc _ H)|exact IHh].
  Qed.

  Lemma cbn_bcodes_gcx G G' c i l : cbn_gcx G G' -> cbn_bcodes G c i l -> cbn_bcodes G' c i l.
  Proof.
    intros hc h. induction h; constructor; [exact (cbn_cok_gcx _ _ hc _ H)|exact IHh].
  Qed.

  (** ** [cbn_case_params] *)

  Lemma cbn_case_params_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_term (k tt) -> cbn_spec_params (k tt) -> cbn_spec_params (CbnFS k).
  Proof.
    intros hT hP L Q lo G e1 c1 e2 c2 i l1 l2 us1 us2 rs s b rs' s' hm hr hp1 hp2 hu1 hu2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_case_params_eq in he.
    destruct l1 as [|t1 l1]; destruct l2 as [|t2 l2].
    - injection he as <- <- <-. inversion hu1; subst. inversion hu2; subst.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros _. apply cbn_lift_conv_s_nil.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hu1 as [|y1 v1 m1 vs1 hv1 hvs1]; subst.
      inversion hu2 as [|y2 v2 m2 vs2 hv2 hvs2]; subst.
      inversion hp1 as [|i1 z1 n1 hc1 hp1']; subst.
      inversion hp2 as [|i2 z2 n2 hc2 hp2']; subst.
      destruct (cbn_conv_term X_type X Γ nctx (k tt) L Conv
                  e1 (cbn_child c1 (cbn_case_param_step i) t1) e2
                    (cbn_child c2 (cbn_case_param_step i) t2)
                  (CbnRE e1 :: CbnRE e2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ect; [|discriminate he].
      destruct (hT L Q lo G Conv e1 (cbn_child c1 (cbn_case_param_step i) t1)
                  e2 (cbn_child c2 (cbn_case_param_step i) t2) v1 v2 _ s b2 rs2 s2 hm
                  (Forall_cons (CbnRE e1) I (Forall_cons (CbnRE e2) I hr)) hv1 hc1 hv2 hc2 Ect)
        as [hpA hcA].
      destruct b2.
      + destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q1 & rsA & -> & hqa & hgA1).
        destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqa) as (f1 & -> & hfa).
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA1) as (q2 & rsB & -> & hqb & hgB).
        destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqb) as (f2 & -> & hfb).
        cbv beta iota in he.
        destruct (hP L QA loA GA f1 c1 f2 c2 (N.succ i) l1 l2 _ _ rsB s2 b rs' s' hmA
                    (Forall_inv_tail (Forall_inv_tail hrA))
                    (cbn_pcodes_gcx _ _ _ _ _ (proj1 hgA) hp1')
                      (cbn_pcodes_gcx _ _ _ _ _ (proj1 hgA) hp2')
                    (cbn_gsusps_q Q QA G GA e1 f1 l1 vs1 ltac:(lia) hqA hqa hvs1)
                    (cbn_gsusps_q Q QA G GA e2 f2 l2 vs2 ltac:(lia) hqA hqb hvs2) he) as [hp hc].
        split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hqA hgB hp)|].
        intros hb. apply cbn_lift_conv_s_cons; [exact (hcA eq_refl)|].
        exact (cbn_lift_conv_s_lift _ _ _ _ _ hLQ hqA (hc hb)).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hpA)|]. intros hb; discriminate hb.
  Qed.

  (** ** The same-code rule on ghost readings *)

  (** The slots of an environment unlifted where the code uses them, a closed filler
    elsewhere: the logical slots the same-code rule substitutes. *)
  Fixpoint cbn_pickw (m : nat) (a : term) (i : nat) (ts : list term) : list term :=
    match ts with
    | [] => []
    | t :: ts => (if noccur_between i 1 a then tSort sProp else cbn_unl m t)
      :: cbn_pickw m a (S i) ts
    end.

  Lemma cbn_pickw_length m a i ts : #|cbn_pickw m a i ts| = #|ts|.
  Proof.
    revert i. induction ts as [|t ts ih]; intros i; cbn; [reflexivity|]. rewrite ih. reflexivity.
  Qed.

  Lemma cbn_pickw_lift m a i ts :
    (forall j u, nth_error ts j = Some u -> noccur_between (i + j) 1 a = false ->
       u = lift0 m (cbn_unl m u)) ->
    forall j, j < #|ts| -> noccur_between (i + j) 1 a = false ->
      nth_error (map (lift0 m) (cbn_pickw m a i ts)) j = nth_error ts j.
  Proof.
    revert i. induction ts as [|t ts ih]; intros i h j hj hn; cbn in hj |- *; [lia|].
    destruct j as [|j]; cbn.
    - rewrite Nat.add_0_r in hn. rewrite hn. f_equal. symmetry. apply (h 0 t eq_refl).
      rewrite Nat.add_0_r. exact hn.
    - apply ih; [|lia|replace (S i + j) with (i + S j) by lia; exact hn].
      intros j' u hu hn'. apply (h (S j') u hu). replace (i + S j') with (S i + j') by lia.
      exact hn'.
  Qed.

  Lemma cbn_pick_all2 L Q a i ts1 ts2 Δ :
    nctx <= L -> L <= Q -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    cbn_cagree L Q a i ts1 ts2 ->
    (forall j u, nth_error ts1 j = Some u -> noccur_between (i + j) 1 a = false ->
       on_free_vars (cbn_inq (Q - L) Q) u) ->
    (forall j u, nth_error ts2 j = Some u -> noccur_between (i + j) 1 a = false ->
       on_free_vars (cbn_inq (Q - L) Q) u) ->
    ∥ ws_cumul_pb_terms Σ (Γ ,,, Δ) (cbn_pickw (Q - L) a i ts1) (cbn_pickw (Q - L) a i ts2) ∥.
  Proof.
    intros hL hQ hΔ hcl h. induction h as [i|i u1 u2 l1 l2 hd hag ih]; intros h1 h2.
    - constructor. constructor.
    - assert (h1' : forall j u, nth_error l1 j = Some u -> noccur_between (S i + j) 1 a = false ->
                      on_free_vars (cbn_inq (Q - L) Q) u).
      { intros j u hu hn. apply (h1 (S j) u hu). replace (i + S j) with (S i + j) by lia.
        exact hn. }
      assert (h2' : forall j u, nth_error l2 j = Some u -> noccur_between (S i + j) 1 a = false ->
                      on_free_vars (cbn_inq (Q - L) Q) u).
      { intros j u hu hn. apply (h2 (S j) u hu). replace (i + S j) with (S i + j) by lia.
        exact hn. }
      destruct (ih h1' h2') as [hall].
      cbn [cbn_pickw]. destruct (noccur_between i 1 a) eqn:En.
      + constructor. constructor; [|exact hall].
        apply ws_cumul_pb_refl; [exact hcl|reflexivity].
      + destruct hd as [hd|hd]; [discriminate hd|].
        pose proof (h1 0 u1 eq_refl ltac:(rewrite Nat.add_0_r; exact En)) as o1.
        pose proof (h2 0 u2 eq_refl ltac:(rewrite Nat.add_0_r; exact En)) as o2.
        destruct (cbn_inq_unl _ _ _ o1) as [e1 s1]. destruct (cbn_inq_unl _ _ _ o2) as [e2 s2].
        replace (Q - (Q - L)) with L in s1, s2 by lia.
        destruct (hd _ _ e1 e2 s1 s2 Δ hΔ hcl) as [hc].
        constructor. constructor; [exact hc|exact hall].
  Qed.

  Lemma cbn_same_code_cv L Q pb n goff ts1 ts2 a Δ :
    nctx <= L -> L <= Q -> #|ts1| = n -> #|ts2| = n ->
    #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    cbn_cagree L Q a 0 ts1 ts2 ->
    (forall j u, nth_error ts1 j = Some u -> noccur_between (0 + j) 1 a = false ->
       on_free_vars (cbn_inq (Q - L) Q) u) ->
    (forall j u, nth_error ts2 j = Some u -> noccur_between (0 + j) 1 a = false ->
       on_free_vars (cbn_inq (Q - L) Q) u) ->
    cbn_scl L (subst (cbn_pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a)) ->
    ∥ Σ ;;; Γ ,,, Δ ⊢ subst (cbn_pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a) ≤[pb]
                     subst (cbn_pickw (Q - L) a 0 ts2) 0 (lift (L - nctx + goff) n a) ∥.
  Proof.
    intros hL hQ hl1 hl2 hΔ hcl hag h1 h2 hs.
    destruct (cbn_pick_all2 L Q a 0 ts1 ts2 Δ hL hQ hΔ hcl hag h1 h2) as [hall].
    constructor. apply (cbn_ws_cumul_pb_subst_open (wfΣ := wfΣ)); [exact hcl|exact hall|].
    pose proof (cbn_cg_subst_scope_inv (shiftnP L cbn_xpred0) (cbn_pickw (Q - L) a 0 ts1)
                  (lift (L - nctx + goff) n a) 0) as hsc.
    rewrite cbn_pickw_length, hl1 in hsc.
    assert (h0 : on_free_vars (shiftnP 0 (shiftnP L cbn_xpred0))
                   (subst (cbn_pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a))).
    { rewrite (on_free_vars_ext _ _ _ (shiftnP0 _)). exact hs. }
    specialize (hsc h0). rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in hsc.
    rewrite !app_context_length, cbn_fresh_context_length, cbn_pickw_length, hl1, hΔ, <- hnctx.
    assert (E : n + (L - nctx + nctx) = 0 + n + L) by lia. rewrite E. exact hsc.
  Qed.

  (** Two readings of codes [cbn_code_eq] accepts, through environments with the same counts whose
    used slots agree in the sense of [cbn_lift_conv], are convertible at any [conv_pb]. The used
    slots of a lifted reading are lifts ([cbn_cg_occ_inv]); the unused ones do not matter
    ([cbn_subst_agree_lift]). *)
  Lemma cbn_same_code_lift_conv L Q pb n goff ts1 ts2 a1 a2 :
    nctx <= L -> L <= Q -> #|ts1| = n -> #|ts2| = n ->
    on_free_vars cbn_xpredT a1 -> on_free_vars cbn_xpredT a2 ->
    cbn_samec a1 a2 -> cbn_cagree L Q a1 0 ts1 ts2 ->
    cbn_lift_conv L Q pb (subst ts1 0 (lift (Q - nctx + goff) n a1))
              (subst ts2 0 (lift (Q - nctx + goff) n a2)).
  Proof.
    intros hL hQ hl1 hl2 hy1 hy2 hsame hag u1 u2 e1 e2 s1 s2 Δ hΔ hcl.
    assert (hQm : L + (Q - L) = Q) by lia.
    assert (hN : Q - nctx + goff = (Q - L) + (L - nctx + goff)) by lia.
    assert (hinv : forall ts a, on_free_vars cbn_xpredT a -> #|ts| = n ->
              on_free_vars (cbn_inq (Q - L) Q) (subst ts 0 (lift (Q - nctx + goff) n a)) ->
              forall j u, nth_error ts j = Some u -> noccur_between (0 + j) 1 a = false ->
                on_free_vars (cbn_inq (Q - L) Q) u).
    { intros ts a hy hl hT j u hu hn.
      apply (cbn_cg_occ_inv (cbn_inq (Q - L) Q) ts (Q - nctx + goff) j u hu a 0 hy hn).
      rewrite (on_free_vars_ext _ _ _ (shiftnP0 _)). cbn [Nat.add]. rewrite hl. exact hT. }
    assert (hU : forall ts a U, on_free_vars cbn_xpredT a -> #|ts| = n ->
              subst ts 0 (lift (Q - nctx + goff) n a) = lift0 (Q - L) U ->
              on_free_vars (cbn_inq (Q - L) Q) (subst ts 0 (lift (Q - nctx + goff) n a)) ->
              U = subst (cbn_pickw (Q - L) a 0 ts) 0 (lift (L - nctx + goff) n a)).
    { intros ts a U hy hl eU hT. apply (PCUICCallByNeedSoundReadBack.cbn_lift0_inj (Q - L)).
      rewrite <- eU.
      rewrite (cbn_lift_susp_read nctx L (Q - L) hL (L - nctx + goff) n a (cbn_pickw (Q - L) a 0 ts)
                 ltac:(rewrite cbn_pickw_length; exact hl)).
      rewrite <- hN.
      apply cbn_subst_agree_lift; [rewrite length_map, cbn_pickw_length;
        reflexivity|symmetry; exact hl|].
      intros j hj hn. symmetry. apply cbn_pickw_lift; [|exact hj|exact hn].
      intros j' u hu hn'. exact (proj1 (cbn_inq_unl _ _ u (hinv ts a hy hl hT j' u hu hn'))). }
    pose proof (cbn_inq_lift0 (Q - L) L u1 s1) as hT1. rewrite hQm, <- e1 in hT1.
    pose proof (cbn_inq_lift0 (Q - L) L u2 s2) as hT2. rewrite hQm, <- e2 in hT2.
    pose proof (hU ts1 a1 u1 hy1 hl1 e1 hT1) as hU1.
    destruct hsame as [<-|[hc12]].
    - pose proof (hU ts2 a1 u2 hy1 hl2 e2 hT2) as hU2.
      rewrite hU1 in s1 |- *. rewrite hU2.
      exact (cbn_same_code_cv L Q pb n goff ts1 ts2 a1 Δ hL hQ hl1 hl2 hΔ hcl hag
               (hinv ts1 a1 hy1 hl1 hT1) (hinv ts2 a1 hy1 hl2 hT2) s1).
    - set (T2' := subst ts2 0 (lift (Q - nctx + goff) n a1)).
      assert (h12 : compare_term Σ Σ Conv T2' (subst ts2 0 (lift (Q - nctx + goff) n a2))).
      { apply subst_eq_term.
        exact (eq_term_upto_univ_lift Σ (compare_universe Σ) (compare_sort Σ) Conv
                 (Q - nctx + goff) 0 n _ _ hc12). }
      assert (h21 : compare_term Σ Σ Conv (subst ts2 0 (lift (Q - nctx + goff) n a2)) T2')
        by (symmetry; exact h12).
      pose proof (PCUICConfluence.eq_term_upto_univ_napp_on_free_vars h21 hT2) as hT2'.
      destruct (cbn_inq_unl (Q - L) Q T2' hT2') as [eT2' sT2'].
      replace (Q - (Q - L)) with L in sT2' by lia.
      pose proof (hU ts2 a1 (cbn_unl (Q - L) T2') hy1 hl2 eT2' hT2') as hU2'.
      assert (hc2 : compare_term Σ Σ Conv (cbn_unl (Q - L) T2') u2).
      { rewrite <- (cbn_unl_lift0 (Q - L) u2), <- e2.
        exact (PCUICRenameConv.eq_term_upto_univ_rename Σ _ _ Conv 0 _ _ _ h12). }
      rewrite hU1 in s1 |- *.
      destruct (cbn_same_code_cv L Q pb n goff ts1 ts2 a1 Δ hL hQ hl1 hl2 hΔ hcl hag
                  (hinv ts1 a1 hy1 hl1 hT1) (hinv ts2 a1 hy1 hl2 hT2') s1) as [h1].
      constructor. refine (@cbn_ws_cumul_pb_conv_trans_r cf Σ wfΣ pb (Γ ,,, Δ) _ _ _ h1 _).
      rewrite <- hU2'.
      apply cbn_ws_cumul_pb_compare_term; [exact hcl|exact (cbn_scl_open L Δ _ hL hΔ sT2')|
                                       exact (cbn_scl_open L Δ u2 hL hΔ s2)|exact hc2].
  Qed.

  (** [cbn_code_eq_sound], with the universe checks [cbn_code_eq] ran on the way to a syntactic
    comparison. *)
  Lemma cbn_code_eq_sound_wf (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (s : cbn_state) :
    cbn_ceq_ok X_type X (s.(cbn_st_memo)) ->
    PTree.get c1.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e1 -> cbn_code_inv e1 c1 ->
    PTree.get c2.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e2 -> cbn_code_inv e2 c2 ->
    fst (cbn_code_eq X_type X c1 c2 s) = true ->
    c1.(cbn_c_term) = c2.(cbn_c_term)
    \/ (cbn_ceq_term X_type X c1.(cbn_c_term) c2.(cbn_c_term) = true
        /\ cbn_entry_wf c1.(cbn_c_entry) s = true /\ cbn_entry_wf c2.(cbn_c_entry) s = true).
  Proof.
    intros hq g1 hi1 g2 hi2 hE.
    destruct (cbn_code_eq_sound X_type X c1 c2 e1 e2 s hq g1 hi1 g2 hi2 hE) as [h|h];
      [left; exact h|].
    destruct (cbn_same_id c1 c2) eqn:Esid.
    { left. exact (cbn_same_id_sound_table _ e1 e2 c1 c2 Esid g1 hi1 g2 hi2). }
    right. split; [exact h|].
    unfold cbn_code_eq in hE. rewrite Esid in hE.
    destruct (cbn_entry_wf c1.(cbn_c_entry) s && cbn_entry_wf c2.(cbn_c_entry) s) eqn:Ew;
      [apply andb_true_iff in Ew; exact Ew|cbn in hE; discriminate hE].
  Qed.

  Lemma cbn_conv_same_code_sound_g (k : unit -> cbn_fuel) : cbn_spec_scc (k tt) ->
    cbn_spec_same (CbnFS k).
  Proof.
    intros hC L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s' hm hr hc1 hc2 hs1 hs2 he.
    pose proof hm as [hL hLQ hok hw].
    rewrite cbn_conv_same_code_eq in he.
    destruct ((e1.(cbn_ev_goff) == e2.(cbn_ev_goff)) && (e1.(cbn_ev_nvals) == e2.(cbn_ev_nvals)))
      eqn:Eeq;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Eeq as [Eg En]. apply eqb_eq in Eg. apply eqb_eq in En.
    destruct hc1 as [ce1 [hg1 hi1]]. destruct hc2 as [ce2 [hg2 hi2]].
    destruct (cbn_gk_memo _ _ _ _ _ _ _ _ _ _ hok) as (hmi & hmo & hK & hcons & hhy).
    pose proof (hK _ _ hg1) as hg1'. pose proof (hK _ _ hg2) as hg2'.
    destruct (cbn_memo_inv_code_eq X_type X c1 c2 ce1 ce2 s hmi hg1' hi1 hg2' hi2)
      as (hmi' & hcodes & hheap & hnext & _ & _ & hgam).
    assert (hm0 : cbn_MI L Q lo G (snd (cbn_code_eq X_type X c1 c2 s))).
    { constructor; [exact hL|exact hLQ| |exact (cbn_hwf_heap Q s _ hheap hw)].
      apply (cbn_gok_same X_type X Γ nctx Σ _ Q lo G s);
        [exact hok|exact hheap|exact hnext|exact hgam|].
      split; [exact hmi'|]. split; [exact (cbn_memo_ok_codes X_type X s _ hcodes hmo)|].
      rewrite hcodes. split; [exact hK|]. split; [exact hcons|exact hhy]. }
    assert (hE : forall b0, fst (cbn_code_eq X_type X c1 c2 s) = b0 -> b0 = true ->
                   cbn_samec c1.(cbn_c_term) c2.(cbn_c_term)).
    { intros b0 Eb0 ->.
      destruct (cbn_code_eq_sound_wf c1 c2 ce1 ce2 s (proj1 (proj2 (proj2 (proj2 hmi))))
                  hg1' hi1 hg2' hi2 Eb0) as [h|(hceq & hw1 & hw2)]; [left; exact h|right].
      rewrite (cbn_memo_entry_wf X_type X s _ ce1 hmo hg1') in hw1.
      rewrite (cbn_memo_entry_wf X_type X s _ ce2 hmo hg2') in hw2.
      rewrite (cbn_wf_term_univs_correct X_type X Σ hΣ) in hw1, hw2.
      constructor.
      exact (cbn_ceq_term_sound X_type X Σ hΣ _ _ (cbn_cg_code_inv_wf_universes Σ ce1 c1 hi1 hw1)
               (cbn_cg_code_inv_wf_universes Σ ce2 c2 hi2 hw2) hceq). }
    destruct (cbn_code_eq X_type X c1 c2 s) as [b0 s0] eqn:Ece. cbn [fst snd] in hm0, hE.
    destruct b0;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm0 hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G c1.(cbn_c_term) 0 _ _ ts1 ts2 rs s0 b rs' s' hm0 hr hs1 hs2 he) as
      [hp hc].
    split; [exact hp|]. intros hb. split; [exact Eg|]. split; [exact En|].
    split; [exact (hE true eq_refl eq_refl)|exact (hc hb)].
  Qed.

  (** A [true] of [cbn_conv_same_code] makes the two readings of the codes convertible at any
    [conv_pb]. *)
  Lemma cbn_conv_same_code_sound_ghost (d : cbn_fuel) : cbn_spec_same d ->
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
      cbn_g_susp nctx Q G e1 c1.(cbn_c_term) t1 -> cbn_gcok G c1 ->
      cbn_g_susp nctx Q G e2 c2.(cbn_c_term) t2 -> cbn_gcok G c2 ->
      cbn_conv_same_code X_type X Γ nctx d L e1 c1 e2 c2 rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb t1 t2).
  Proof.
    intros hS L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ hok _].
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hs1) as (ts1 & hts1 & hn1 & ->).
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hs2) as (ts2 & hts2 & hn2 & ->).
    destruct (hS L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s' hm hr hc1 hc2 hts1 hts2 he)
      as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as (hgo & hnv & hsame & hag).
    pose proof (cbn_gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    pose proof (cbn_g_slots_length _ _ _ _ _ hts1) as hl1.
    pose proof (cbn_g_slots_length _ _ _ _ _ hts2) as hl2.
    rewrite <- hgo, <- hnv.
    apply (cbn_same_code_lift_conv L Q pb (cbn_ev_nvals e1) (cbn_ev_goff e1) ts1 ts2 _ _ hL hLQ);
      [lia|lia|exact (hch _ hc1)|exact (hch _ hc2)|exact hsame|exact hag].
  Qed.

  Lemma cbn_cagree_fix L Q m idx idx' i l1 l2 :
    cbn_cagree L Q (tFix m idx) i l1 l2 -> cbn_cagree L Q (tFix m idx') i l1 l2.
  Proof. induction 1; constructor; [exact H|exact IHcbn_cagree]. Qed.

  Lemma cbn_samec_fix m1 m2 idx1 idx2 i :
    cbn_samec (tFix m1 idx1) (tFix m2 idx2) -> cbn_samec (tFix m1 i) (tFix m2 i).
  Proof.
    intros [e|[h]]; [injection e as -> _; left; reflexivity|right; constructor].
    inversion h; subst. constructor. assumption.
  Qed.

  (** ** [cbn_conv_slot] *)

  Lemma cbn_conv_slot_eq k L le x1 x2 rs s :
    cbn_conv_slot X_type X Γ nctx (CbnFS k) L le x1 x2 rs s =
    match x1, x2 with
    | CbnSAddr a1, CbnSAddr a2 =>
      if cbn_haddr_eqb a1 a2 then CbnCOk (true, rs, s)
      else cbn_conv_eval X_type X Γ nctx (k tt) L le x1 x2 rs s
    | CbnSInl vs1 n1 o1 c1, CbnSInl vs2 n2 o2 c2 =>
      match cbn_conv_same_code X_type X Γ nctx (k tt) L (cbn_mkEnv vs1 n1 o1) c1
              (cbn_mkEnv vs2 n2 o2) c2 (CbnRSl x1 :: CbnRSl x2 :: rs) s with
      | CbnCOk (b, rs, s) =>
        match rs with
        | CbnRSl x1 :: CbnRSl x2 :: rs =>
          if b then CbnCOk (true, rs, s)
          else cbn_conv_eval X_type X Γ nctx (k tt) L le x1 x2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | CbnCFail w => CbnCFail w
      end
    | _, _ => cbn_conv_eval X_type X Γ nctx (k tt) L le x1 x2 rs s
    end.
  Proof. reflexivity. Qed.

  Lemma cbn_conv_slot_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_eval (k tt) -> cbn_spec_same (k tt) -> cbn_spec_slot (CbnFS k).
  Proof.
    intros hE hS L Q lo G pb x1 x2 t1 t2 rs s b rs' s' hm hr hx1 hx2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_slot_eq in he.
    destruct x1 as [a1|vs1 n1 o1 c1]; destruct x2 as [a2|vs2 n2 o2 c2];
      cbv beta iota in he;
      try exact (hE L Q lo G pb _ _ t1 t2 rs s b rs' s' hm hr hx1 hx2 he).
    - destruct (cbn_haddr_eqb a1 a2) eqn:Ea;
        [|exact (hE L Q lo G pb _ _ t1 t2 rs s b rs' s' hm hr hx1 hx2 he)].
      injection he as <- <- <-. split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros _.
      apply cbn_haddr_eqb_eq in Ea. subst a2.
      apply cbn_g_slot_addr_inv in hx1. apply cbn_g_slot_addr_inv in hx2.
      rewrite hx1 in hx2. injection hx2 as <-. exact (cbn_lift_conv_refl _ _ _ _ hL).
    - assert (hs1 : cbn_g_susp nctx Q G (cbn_mkEnv vs1 n1 o1) c1.(cbn_c_term) t1)
        by (eapply cbn_g_slot_inl_inv; exact hx1).
      assert (hc1 : cbn_gcok G c1) by (eapply cbn_g_slot_inl_cok; exact hx1).
      assert (hs2 : cbn_g_susp nctx Q G (cbn_mkEnv vs2 n2 o2) c2.(cbn_c_term) t2)
        by (eapply cbn_g_slot_inl_inv; exact hx2).
      assert (hc2 : cbn_gcok G c2) by (eapply cbn_g_slot_inl_cok; exact hx2).
      destruct (cbn_conv_same_code X_type X Γ nctx (k tt) L (cbn_mkEnv vs1 n1 o1) c1
                  (cbn_mkEnv vs2 n2 o2) c2
                    (CbnRSl (CbnSInl vs1 n1 o1 c1) :: CbnRSl (CbnSInl vs2 n2 o2 c2) :: rs) s)
        as [[[b0 rs0] s0]|w] eqn:Ecs; [|discriminate he].
      destruct (cbn_conv_same_code_sound_ghost (k tt) hS L Q lo G pb _ c1 _ c2 t1 t2 _ s b0 rs0 s0
                  hm (Forall_cons (CbnRSl _) I (Forall_cons (CbnRSl _) I hr)) hs1 hc1 hs2 hc2 Ecs)
        as [hp0 hc0].
      destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
      destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
      destruct (cbn_gpq_RSl_inv _ _ _ _ _ _ hqa) as (y1 & -> & hk1).
      destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
      destruct (cbn_gpq_RSl_inv _ _ _ _ _ _ hqb) as (y2 & -> & hk2).
      cbv beta iota in he.
      destruct b0.
      + injection he as <- <- <-.
        split; [|intros _; exact (hc0 eq_refl)].
        exists Q1, lo1, G1. split; [exact hq1|]. split; [exact hm1|].
        split; [exact (Forall_inv_tail (Forall_inv_tail hr1))|exact hgB].
      + destruct (hE L Q1 lo1 G1 pb y1 y2 _ _ rsB s0 b rs' s' hm1
                    (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hx1) (hk2 _ hx2) he)
          as [hp hc].
        split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
        intros hb. exact (cbn_lift_conv_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  (** ** Crossing a binder: the lambda and product rows *)

  Lemma cbn_minv_level L L' Q lo G s : cbn_MI L Q lo G s -> nctx <= L' -> L' <= Q ->
    cbn_MI L' Q lo G s.
  Proof. intros [hL hQ hok hw] h1 h2. constructor; assumption. Qed.

  (** The body of a code read through slots lifted by [d] is the lift by [d] at the cut [k]. *)
  Lemma cbn_lift_bodyk d ts N n k t :
    #|ts| = n ->
    subst (map (lift0 d) ts) k (lift (d + N) (k + n) t) = lift d k (subst ts k (lift N (k + n) t)).
  Proof.
    intros hl. pose proof (distr_lift_subst_rec (lift N (k + n) t) ts d k 0) as h.
    rewrite !Nat.add_0_r in h. rewrite h. f_equal. rewrite hl.
    symmetry. apply simpl_lift; lia.
  Qed.

  Lemma cbn_subst_rel_lift1 j U : subst [tRel j] 0 (lift (S j) 1 U) = lift0 j U.
  Proof.
    pose proof (cbn_cg_subst_fresh_lift j 1 U) as h.
    replace (map (lift0 j) (idsn 1)) with [tRel j] in h
      by (cbn; rewrite Nat.add_0_r; reflexivity).
    rewrite Nat.add_1_r in h. exact h.
  Qed.

  (** After the domains: one fresh variable at level [L], pushed on both environments, then
    the bodies at [S L]. *)
  Definition cbn_binder_tail (d : cbn_fuel) (L : nat) (pb : conv_pb) (e1 e2 : cbn_env)
      (cb1 cb2 : cbn_code) (rs : list cbn_root) (s : cbn_state) :=
    match cbn_alloc (CbnCDone (CbnVNeu (CbnNVar L) [])) (CbnRE e1 :: CbnRE e2 :: rs) s with
    | CbnCOk (x, rs, s) =>
      match rs with
      | CbnRE e1 :: CbnRE e2 :: rs =>
        cbn_conv_term X_type X Γ nctx d (S L) pb (cbn_env_push (CbnSAddr x) e1) cb1
          (cbn_env_push (CbnSAddr x) e2) cb2 rs s
      | _ => CbnCFail CbnWRoots
      end
    | CbnCFail w => CbnCFail w
    end.

  Lemma cbn_binder_tail_g (k : unit -> cbn_fuel) (hT : cbn_spec_term (k tt))
      L Q lo G pb e1 e2 cb1 cb2 ts1 ts2 rs s b rs' s' :
    cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
    cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> e1.(cbn_ev_nvals) = #|e1.(cbn_ev_vals)| ->
    cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 -> e2.(cbn_ev_nvals) = #|e2.(cbn_ev_vals)| ->
    cbn_gcok G cb1 -> cbn_gcok G cb2 ->
    cbn_binder_tail (k tt) L pb e1 e2 cb1 cb2 rs s = CbnCOk (b, rs', s') ->
    cbn_post L Q G rs s' rs' /\
    (b = true -> cbn_lift_conv_b L Q 1 pb
       (subst ts1 1 (lift (Q - nctx + e1.(cbn_ev_goff)) (S e1.(cbn_ev_nvals)) cb1.(cbn_c_term)))
       (subst ts2 1 (lift (Q - nctx + e2.(cbn_ev_goff)) (S e2.(cbn_ev_nvals)) cb2.(cbn_c_term)))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hc1 hc2 he.
    pose proof hm as [hL hLQ _ _].
    pose proof (cbn_minv_raise L Q 1 lo G s hm) as hmR.
    pose proof (cbn_rwfs_mono Q (Q + 1) rs ltac:(lia) hr) as hrR.
    pose proof (cbn_grq_raise Q 1 G rs ltac:(lia) hr) as hgR.
    pose proof (proj2 (cbn_g_slot_shift nctx Q 1 ltac:(lia) G) _ _ hs1) as [hs1R _].
    pose proof (proj2 (cbn_g_slot_shift nctx Q 1 ltac:(lia) G) _ _ hs2) as [hs2R _].
    unfold cbn_binder_tail in he.
    destruct (cbn_alloc (CbnCDone (CbnVNeu (CbnNVar L) [])) (CbnRE e1 :: CbnRE e2 :: rs) s)
      as [[[x rs1] s1]|w] eqn:Ea; [|discriminate he].
    destruct (cbn_alloc_fresh_g L (Q + 1) lo (cbn_gshift 1 G) L _ s x rs1 s1 hmR
                (Forall_cons (CbnRE e1) I (Forall_cons (CbnRE e2) I hrR)) ltac:(lia) Ea)
      as (lo1 & G1 & hm1 & hr1 & hg1 & hx).
    destruct (cbn_gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hq1 & hgA).
    destruct (cbn_gpres_RE_inv _ _ _ _ _ hq1) as (f1 & -> & (hn1' & hg1' & hk1)).
    destruct (cbn_gren_cons_inv _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hq2 & hgB).
    destruct (cbn_gpres_RE_inv _ _ _ _ _ hq2) as (f2 & -> & (hn2' & hg2' & hk2)).
    cbv beta iota in he.
    pose proof (hk1 _ hs1R) as hf1. pose proof (hk2 _ hs2R) as hf2.
    pose proof (cbn_g_slots_length _ _ _ _ _ hs1) as hl1.
    pose proof (cbn_g_slots_length _ _ _ _ _ hf1) as hl1'. rewrite length_map in hl1'.
    pose proof (cbn_g_slots_length _ _ _ _ _ hs2) as hl2.
    pose proof (cbn_g_slots_length _ _ _ _ _ hf2) as hl2'. rewrite length_map in hl2'.
    set (j := Q + 1 - S L).
    assert (hb1 : cbn_g_susp nctx (Q + 1) G1 (cbn_env_push (CbnSAddr x) f1) cb1.(cbn_c_term)
                    (subst (tRel j :: map (lift0 1) ts1) 0
                       (lift (Q + 1 - nctx + cbn_ev_goff e1) (S (cbn_ev_nvals e1))
                         cb1.(cbn_c_term)))).
    { rewrite <- hg1', <- hn1'. apply (cbn_g_susp_of_slots _ _ _ (cbn_env_push (CbnSAddr x) f1)).
      - cbn. constructor; [constructor; exact hx|exact hf1].
      - cbn. lia. }
    assert (hb2 : cbn_g_susp nctx (Q + 1) G1 (cbn_env_push (CbnSAddr x) f2) cb2.(cbn_c_term)
                    (subst (tRel j :: map (lift0 1) ts2) 0
                       (lift (Q + 1 - nctx + cbn_ev_goff e2) (S (cbn_ev_nvals e2))
                         cb2.(cbn_c_term)))).
    { rewrite <- hg2', <- hn2'. apply (cbn_g_susp_of_slots _ _ _ (cbn_env_push (CbnSAddr x) f2)).
      - cbn. constructor; [constructor; exact hx|exact hf2].
      - cbn. lia. }
    destruct (hT (S L) (Q + 1) lo1 G1 pb _ cb1 _ cb2 _ _ rsB s1 b rs' s'
                (cbn_minv_level L (S L) (Q + 1) lo1 G1 s1 hm1 ltac:(lia) ltac:(lia))
                (Forall_inv_tail (Forall_inv_tail hr1)) hb1 (cbn_cok_gcx _ _ (proj1 hg1) _ hc1)
                hb2 (cbn_cok_gcx _ _ (proj1 hg1) _ hc2) he) as [hp hc].
    split.
    - apply (cbn_post_compose L Q (Q + 1) G (cbn_gshift 1 G) rs rs s' rs' ltac:(lia) hgR).
      apply (cbn_post_compose L (Q + 1) (Q + 1) (cbn_gshift 1 G) G1 rs rsB s' rs' (le_n _)
               (cbn_grq_of_gren _ _ _ _ _ hgB
                  (cbn_sk_tl _ _ _ _ (cbn_sk_tl _ _ _ _ (cbn_alloc_skel _ _ _ _ _ _ Ea))))).
      exact (cbn_post_level L (S L) (Q + 1) G1 rsB s' rs' hL ltac:(lia) hp).
    - intros hbt U1 U2 eU1 eU2 sU1 sU2.
      rewrite Nat.add_1_r in sU1, sU2 |- *.
      apply (hc hbt U1 U2); [| |exact sU1|exact sU2].
      + rewrite cbn_subst_cons_app.
        replace (Q + 1 - nctx + cbn_ev_goff e1) with (1 + (Q - nctx + cbn_ev_goff e1)) by lia.
        replace (S (cbn_ev_nvals e1)) with (1 + #|ts1|) by lia.
        rewrite cbn_lift_bodyk by reflexivity.
        replace (1 + #|ts1|) with (S (cbn_ev_nvals e1)) by lia. rewrite eU1.
        rewrite simpl_lift by lia. subst j.
        replace (1 + (Q - L)) with (S (Q + 1 - S L)) by lia. apply cbn_subst_rel_lift1.
      + rewrite cbn_subst_cons_app.
        replace (Q + 1 - nctx + cbn_ev_goff e2) with (1 + (Q - nctx + cbn_ev_goff e2)) by lia.
        replace (S (cbn_ev_nvals e2)) with (1 + #|ts2|) by lia.
        rewrite cbn_lift_bodyk by reflexivity.
        replace (1 + #|ts2|) with (S (cbn_ev_nvals e2)) by lia. rewrite eU2.
        rewrite simpl_lift by lia. subst j.
        replace (1 + (Q - L)) with (S (Q + 1 - S L)) by lia. apply cbn_subst_rel_lift1.
  Qed.

  Lemma cbn_lift_conv_b_lift (L Q Q' k : nat) (pb : conv_pb) (B1 B2 : term) :
    L <= Q -> Q <= Q' ->
    cbn_lift_conv_b L Q' k pb (lift (Q' - Q) k B1) (lift (Q' - Q) k B2) ->
      cbn_lift_conv_b L Q k pb B1 B2.
  Proof.
    intros hLQ hQ h U1 U2 e1 e2 s1 s2. apply h; [| |exact s1|exact s2].
    - rewrite e1, simpl_lift by lia. f_equal. lia.
    - rewrite e2, simpl_lift by lia. f_equal. lia.
  Qed.

  (** Domains at [Conv], then one fresh variable and the bodies at [pbb]. *)
  Lemma cbn_binder_step (k : unit -> cbn_fuel) (hT : cbn_spec_term (k tt))
      L Q lo G pbb e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s' :
    cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
    cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> e1.(cbn_ev_nvals) = #|e1.(cbn_ev_vals)| ->
    cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 -> e2.(cbn_ev_nvals) = #|e2.(cbn_ev_vals)| ->
    cbn_gcok G (cbn_child c1 0 A1) -> cbn_gcok G (cbn_child c2 0 A2) ->
    cbn_gcok G (cbn_child c1 1 b1) -> cbn_gcok G (cbn_child c2 1 b2) ->
    match cbn_conv_term X_type X Γ nctx (k tt) L Conv e1 (cbn_child c1 0 A1) e2 (cbn_child c2 0 A2)
            (CbnRE e1 :: CbnRE e2 :: rs) s with
    | CbnCOk (true, rs, s) =>
      match rs with
      | CbnRE e1 :: CbnRE e2 :: rs => cbn_binder_tail (k tt) L pbb e1 e2 (cbn_child c1 1 b1)
        (cbn_child c2 1 b2) rs s
      | _ => CbnCFail CbnWRoots
      end
    | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
    | CbnCFail w => CbnCFail w
    end = CbnCOk (b, rs', s') ->
    cbn_post L Q G rs s' rs' /\
    (b = true ->
     cbn_lift_conv L Q Conv (subst ts1 0 (lift (Q - nctx + e1.(cbn_ev_goff)) e1.(cbn_ev_nvals) A1))
                 (subst ts2 0 (lift (Q - nctx + e2.(cbn_ev_goff)) e2.(cbn_ev_nvals) A2))
     /\ cbn_lift_conv_b L Q 1 pbb (subst ts1 1
       (lift (Q - nctx + e1.(cbn_ev_goff)) (S e1.(cbn_ev_nvals)) b1))
                      (subst ts2 1 (lift (Q - nctx + e2.(cbn_ev_goff)) (S e2.(cbn_ev_nvals)) b2))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hcA1 hcA2 hcB1 hcB2 he.
    pose proof hm as [hL hLQ _ _].
    destruct (cbn_conv_term X_type X Γ nctx (k tt) L Conv e1 (cbn_child c1 0 A1) e2
      (cbn_child c2 0 A2)
                (CbnRE e1 :: CbnRE e2 :: rs) s) as [[[bA rsA] sA]|w] eqn:EA; [|discriminate he].
    destruct (hT L Q lo G Conv e1 (cbn_child c1 0 A1) e2 (cbn_child c2 0 A2) _ _ _ s bA rsA sA hm
                (Forall_cons (CbnRE e1) I (Forall_cons (CbnRE e2) I hr))
                (cbn_g_susp_of_slots _ _ _ e1 A1 ts1 hs1 hn1) hcA1
                (cbn_g_susp_of_slots _ _ _ e2 A2 ts2 hs2 hn2) hcA2 EA) as [hpA hcA].
    destruct bA.
    - destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
      destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q1 & rsA1 & -> & hqa & hgA1).
      destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqa) as (f1 & -> & hnf1 & hgf1 & hkf1).
      destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA1) as (q2 & rsB & -> & hqb & hgB).
      destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqb) as (f2 & -> & hnf2 & hgf2 & hkf2).
      cbv beta iota in he.
      pose proof (hkf1 _ hs1) as hf1. pose proof (hkf2 _ hs2) as hf2.
      pose proof (cbn_g_slots_length _ _ _ _ _ hs1) as hl1.
      pose proof (cbn_g_slots_length _ _ _ _ _ hf1) as hl1'. rewrite length_map in hl1'.
      pose proof (cbn_g_slots_length _ _ _ _ _ hs2) as hl2.
      pose proof (cbn_g_slots_length _ _ _ _ _ hf2) as hl2'. rewrite length_map in hl2'.
      destruct (cbn_binder_tail_g k hT L QA loA GA pbb f1 f2 (cbn_child c1 1 b1) (cbn_child c2 1 b2)
                  _ _ rsB sA b rs' s' hmA (Forall_inv_tail (Forall_inv_tail hrA)) hf1
                  ltac:(lia) hf2 ltac:(lia)
                  (cbn_cok_gcx _ _ (proj1 hgA) _ hcB1) (cbn_cok_gcx _ _ (proj1 hgA) _ hcB2) he)
        as [hpB hcB].
      split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hqA hgB hpB)|].
      intros hb. split; [exact (hcA eq_refl)|].
      apply (cbn_lift_conv_b_lift L Q QA 1 pbb _ _ hLQ hqA).
      rewrite hnf1, hgf1, hnf2, hgf2 in hcB.
      replace (QA - nctx + cbn_ev_goff e1) with ((QA - Q) + (Q - nctx + cbn_ev_goff e1))
        in hcB by lia.
      replace (QA - nctx + cbn_ev_goff e2) with ((QA - Q) + (Q - nctx + cbn_ev_goff e2))
        in hcB by lia.
      replace (S (cbn_ev_nvals e1)) with (1 + #|ts1|) in hcB |- * by lia.
      replace (S (cbn_ev_nvals e2)) with (1 + #|ts2|) in hcB |- * by lia.
      rewrite !cbn_lift_bodyk in hcB by reflexivity. exact (hcB hb).
    - cbv beta iota in he. injection he as <- <- <-.
      split; [exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hpA)|]. intros hb; discriminate hb.
  Qed.

  Lemma cbn_conv_rows_lam_eq k L le e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s :
    c1.(cbn_c_term) = tLambda na1 A1 b1 -> c2.(cbn_c_term) = tLambda na2 A2 b2 ->
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVLam e1 c1) (CbnVLam e2 c2) rs s =
    if eqb_binder_annot na1 na2 then
      match cbn_conv_term X_type X Γ nctx (k tt) L Conv e1 (cbn_child c1 0 A1) e2
        (cbn_child c2 0 A2)
              (CbnRE e1 :: CbnRE e2 :: rs) s with
      | CbnCOk (true, rs, s) =>
        match rs with
        | CbnRE e1 :: CbnRE e2 :: rs =>
          cbn_binder_tail (k tt) L Conv e1 e2 (cbn_child c1 1 b1) (cbn_child c2 1 b2) rs s
        | _ => CbnCFail CbnWRoots
        end
      | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
      | CbnCFail w => CbnCFail w
      end
    else CbnCOk (false, rs, s).
  Proof. destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity. Qed.

  Lemma cbn_conv_rows_prod_eq k L le e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s :
    c1.(cbn_c_term) = tProd na1 A1 b1 -> c2.(cbn_c_term) = tProd na2 A2 b2 ->
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVOpen e1 c1) (CbnVOpen e2 c2) rs s =
    if eqb_binder_annot na1 na2 then
      match cbn_conv_term X_type X Γ nctx (k tt) L Conv e1 (cbn_child c1 0 A1) e2
        (cbn_child c2 0 A2)
              (CbnRE e1 :: CbnRE e2 :: rs) s with
      | CbnCOk (true, rs, s) =>
        match rs with
        | CbnRE e1 :: CbnRE e2 :: rs =>
          cbn_binder_tail (k tt) L le e1 e2 (cbn_child c1 1 b1) (cbn_child c2 1 b2) rs s
        | _ => CbnCFail CbnWRoots
        end
      | CbnCOk (false, rs, s) => CbnCOk (false, skipn 2 rs, s)
      | CbnCFail w => CbnCFail w
      end
    else CbnCOk (false, rs, s).
  Proof. destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity. Qed.

  (** The logical context of a body: one more assumption. *)
  Lemma cbn_snoc_closed L Δ na A :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) -> cbn_scl L A ->
    is_closed_context (Γ ,,, (Δ ,, vass na A)).
  Proof.
    intros hL hΔ hcl hA.
    change (Γ ,,, (Δ ,, vass na A)) with ((Γ ,,, Δ) ,, vass na A).
    rewrite on_free_vars_ctx_snoc, hcl. cbn. rewrite ?andb_true_r.
    exact (cbn_scl_open L Δ A hL hΔ hA).
  Qed.

  Lemma cbn_scl_binder_n L n B : on_free_vars (shiftnP n (shiftnP L cbn_xpred0)) B ->
    cbn_scl (L + n) B.
  Proof.
    intros h. unfold cbn_scl. rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in h.
    rewrite Nat.add_comm. exact h.
  Qed.

  Lemma cbn_conv_rows_lam_g (k : unit -> cbn_fuel) :
    cbn_spec_term (k tt) ->
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists e1 c1 e2 c2 na1 A1 b1 na2 A2 b2,
                           v1 = CbnVLam e1 c1 /\ v2 = CbnVLam e2 c2
                           /\ c1.(cbn_c_term) = tLambda na1 A1 b1 /\
                             c2.(cbn_c_term) = tLambda na2 A2 b2).
  Proof.
    intros hT L Q lo G pb v1 v2 w1 w2 rs s b rs' s'
      (e1 & c1 & e2 & c2 & na1 & A1 & b1 & na2 & A2 & b2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (cbn_conv_rows_lam_eq k L pb e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s h1 h2) in he.
    assert (hc1 : cbn_gcok G c1) by (eapply cbn_g_value_VLam_cok; exact hw1).
    assert (hc2 : cbn_gcok G c2) by (eapply cbn_g_value_VLam_cok; exact hw2).
    apply cbn_g_value_VLam_inv in hw1. apply cbn_g_value_VLam_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & hts1 & hn1 & ->).
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & hts2 & hn2 & ->).
    destruct (eqb_binder_annot na1 na2) eqn:Ena;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (cbn_binder_step k hT L Q lo G Conv e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s'
                hm hr hts1 hn1 hts2 hn2
                (cbn_cok_child G c1 0 A1 hc1 ltac:(rewrite h1; constructor))
                (cbn_cok_child G c2 0 A2 hc2 ltac:(rewrite h2; constructor))
                (cbn_cok_child G c1 1 b1 hc1 ltac:(rewrite h1; constructor))
                (cbn_cok_child G c2 1 b2 hc2 ltac:(rewrite h2; constructor)) he) as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as [hdom hbody].
    intros u1 u2 e1u e2u s1 s2 Δ hΔ hcl.
    cbn [lift subst] in e1u, e2u.
    destruct u1 as [| | | | |na1' A1u B1u| | | | | | | | | |]; cbn in e1u; try discriminate e1u.
    injection e1u as <- eA1 eB1.
    destruct u2 as [| | | | |na2' A2u B2u| | | | | | | | | |]; cbn in e2u; try discriminate e2u.
    injection e2u as <- eA2 eB2.
    unfold cbn_scl in s1, s2. cbn [on_free_vars] in s1, s2.
    apply andb_true_iff in s1 as [sA1 sB1]. apply andb_true_iff in s2 as [sA2 sB2].
    destruct (hdom A1u A2u eA1 eA2 sA1 sA2 Δ hΔ hcl) as [hd].
    assert (hΔ' : #|Δ ,, vass na1 A1u| = L + 1 - nctx) by (cbn; lia).
    destruct (hbody B1u B2u eB1 eB2 (cbn_scl_binder_n L 1 B1u sB1) (cbn_scl_binder_n L 1 B2u sB2)
                (Δ ,, vass na1 A1u) hΔ' (cbn_snoc_closed L Δ na1 A1u hL hΔ hcl sA1)) as [hbd].
    constructor.
    exact (ws_cumul_pb_Lambda (wfΣ := wfΣ) (eqb_binder_annot_spec _ _ Ena) hd hbd).
  Qed.

  Lemma cbn_conv_rows_prod_g (k : unit -> cbn_fuel) :
    cbn_spec_term (k tt) ->
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists e1 c1 e2 c2 na1 A1 b1 na2 A2 b2,
                           v1 = CbnVOpen e1 c1 /\ v2 = CbnVOpen e2 c2
                           /\ c1.(cbn_c_term) = tProd na1 A1 b1 /\
                             c2.(cbn_c_term) = tProd na2 A2 b2).
  Proof.
    intros hT L Q lo G pb v1 v2 w1 w2 rs s b rs' s'
      (e1 & c1 & e2 & c2 & na1 & A1 & b1 & na2 & A2 & b2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (cbn_conv_rows_prod_eq k L pb e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s h1 h2) in he.
    assert (hc1 : cbn_gcok G c1) by (inversion hw1; assumption).
    assert (hc2 : cbn_gcok G c2) by (inversion hw2; assumption).
    apply cbn_g_value_VOpen_inv in hw1. apply cbn_g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & hts1 & hn1 & ->).
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & hts2 & hn2 & ->).
    destruct (eqb_binder_annot na1 na2) eqn:Ena;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (cbn_binder_step k hT L Q lo G pb e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s'
                hm hr hts1 hn1 hts2 hn2
                (cbn_cok_child G c1 0 A1 hc1 ltac:(rewrite h1; constructor))
                (cbn_cok_child G c2 0 A2 hc2 ltac:(rewrite h2; constructor))
                (cbn_cok_child G c1 1 b1 hc1 ltac:(rewrite h1; constructor))
                (cbn_cok_child G c2 1 b2 hc2 ltac:(rewrite h2; constructor)) he) as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as [hdom hbody].
    intros u1 u2 e1u e2u s1 s2 Δ hΔ hcl.
    cbn [lift subst] in e1u, e2u.
    destruct u1 as [| | | |na1' A1u B1u| | | | | | | | | | |]; cbn in e1u; try discriminate e1u.
    injection e1u as <- eA1 eB1.
    destruct u2 as [| | | |na2' A2u B2u| | | | | | | | | | |]; cbn in e2u; try discriminate e2u.
    injection e2u as <- eA2 eB2.
    unfold cbn_scl in s1, s2. cbn [on_free_vars] in s1, s2.
    apply andb_true_iff in s1 as [sA1 sB1]. apply andb_true_iff in s2 as [sA2 sB2].
    destruct (hdom A1u A2u eA1 eA2 sA1 sA2 Δ hΔ hcl) as [hd].
    assert (hΔ' : #|Δ ,, vass na1 A1u| = L + 1 - nctx) by (cbn; lia).
    destruct (hbody B1u B2u eB1 eB2 (cbn_scl_binder_n L 1 B1u sB1) (cbn_scl_binder_n L 1 B2u sB2)
                (Δ ,, vass na1 A1u) hΔ' (cbn_snoc_closed L Δ na1 A1u hL hΔ hcl sA1)) as [hbd].
    constructor.
    exact (ws_cumul_pb_Prod (wfΣ := wfΣ) pb (eqb_binder_annot_spec _ _ Ena) hd hbd).
  Qed.

  (** ** [cbn_conv_value]: same code first, then the rows *)

  Lemma cbn_minv_tick L Q lo G s s' : cbn_tick s = Some s' -> cbn_MI L Q lo G s ->
    cbn_MI L Q lo G s'.
  Proof.
    intros ht [hL hQ hok hw]. destruct (cbn_tick_shape s s' ht) as (h1 & h2 & _ & h4 & h5).
    constructor; [exact hL|exact hQ| |exact (cbn_hwf_heap Q s s' h1 hw)].
    apply (cbn_gok_same X_type X Γ nctx Σ _ Q lo G s); [exact hok|exact h1|exact h2|exact h4|].
    eapply cbn_mok_memo; [exact h5|exact (cbn_gk_memo _ _ _ _ _ _ _ _ _ _ hok)].
  Qed.

  Lemma cbn_mkApps_inj_len f f' l l' : #|l| = #|l'| -> mkApps f l = mkApps f' l' ->
    f = f' /\ l = l'.
  Proof.
    revert l'. induction l as [|a l ih] using rev_ind; intros l' hl e.
    - destruct l'; [|discriminate hl]. split; [exact e|reflexivity].
    - destruct l' as [|a' l' _] using rev_ind; [rewrite length_app in hl; cbn in hl; lia|].
      rewrite !mkApps_app in e. cbn in e. injection e as e1 e2.
      rewrite !length_app in hl. cbn in hl.
      destruct (ih l' ltac:(lia) e1) as [-> ->]. subst a'. split; reflexivity.
  Qed.

  (** Every value reads as a head applied to the readings of its spine. *)
  Lemma cbn_g_value_spine Q G v t :
    cbn_g_value nctx Q G v t -> exists H T, t = mkApps H T /\ cbn_g_addrs G (cbn_spine_of v) T.
  Proof.
    intros h. destruct h;
      first [ eexists _, _; split; [reflexivity|eassumption]
            | exists t, []; split; [reflexivity|constructor] ].
  Qed.

  (** A value renamed without reshaping keeps the readings of its spine. *)
  Lemma cbn_spine_reads Q Q' G G' v v' H T :
    (forall t, cbn_g_value nctx Q G v t -> cbn_g_value nctx Q' G' v' (lift0 (Q' - Q) t)) ->
    cbn_mp_value cbn_kc v' = cbn_mp_value cbn_kc v ->
    cbn_g_value nctx Q G v (mkApps H T) -> cbn_g_addrs G (cbn_spine_of v) T ->
    cbn_g_addrs G' (cbn_spine_of v') (map (lift0 (Q' - Q)) T).
  Proof.
    intros hk hs hw hT.
    destruct (cbn_g_value_spine _ _ _ _ (hk _ hw)) as (H' & T' & e & hT').
    rewrite lift_mkApps in e.
    pose proof (f_equal (@length _) (f_equal cbn_spine_of hs)) as hl.
    rewrite !cbn_mp_spine_of, !length_map in hl.
    assert (hl' : #|map (lift0 (Q' - Q)) T| = #|T'|).
    { rewrite length_map, (cbn_g_addrs_length _ _ _ hT), (cbn_g_addrs_length _ _ _ hT'). lia. }
    destruct (cbn_mkApps_inj_len _ _ _ _ hl' e) as [_ <-]. exact hT'.
  Qed.

  Lemma cbn_lift_conv_mkApps L Q pb H1 H2 T1 T2 :
    nctx <= L -> cbn_lift_conv L Q pb H1 H2 -> cbn_lift_conv_s L Q T1 T2 ->
      cbn_lift_conv L Q pb (mkApps H1 T1) (mkApps H2 T2).
  Proof.
    intros hL hh hs u1 u2 e1 e2 s1 s2.
    apply cbn_mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply cbn_mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    unfold cbn_scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    apply cbn_cv_spine; [exact hL| |exact (hs us1 us2 eq_refl eq_refl sus1 sus2)].
    exact (hh h1' h2' eh1 eh2 sh1 sh2).
  Qed.

  Definition cbn_cv_same (d : cbn_fuel) (L : nat) (le : conv_pb) (v1 v2 : cbn_value)
      (e1 : cbn_env) (c1 : cbn_code) (e2 : cbn_env) (c2 : cbn_code) (spines : bool)
      (rs : list cbn_root) (s : cbn_state) :=
    match cbn_conv_same_code X_type X Γ nctx d L e1 c1 e2 c2 (CbnRV v1 :: CbnRV v2 :: rs) s with
    | CbnCOk (b, rs, s) =>
      match rs with
      | CbnRV v1 :: CbnRV v2 :: rs =>
        if b then
          if spines then cbn_conv_cells X_type X Γ nctx d L (cbn_spine_of v1) (cbn_spine_of v2) rs s
          else CbnCOk (true, rs, s)
        else cbn_conv_rows X_type X Γ nctx d L le v1 v2 rs s
      | _ => CbnCFail CbnWRoots
      end
    | CbnCFail w => CbnCFail w
    end.

  Lemma cbn_conv_value_eq k L le v1 v2 rs s :
    cbn_conv_value X_type X Γ nctx (CbnFS k) L le v1 v2 rs s =
    match cbn_tick s with
    | None => CbnCFail CbnWSteps
    | Some s =>
      match v1, v2 with
      | CbnVLam e1 c1, CbnVLam e2 c2 | CbnVOpen e1 c1, CbnVOpen e2 c2 =>
        cbn_cv_same (k tt) L le v1 v2 e1 c1 e2 c2 false rs s
      | CbnVStuck e1 c1 sp1, CbnVStuck e2 c2 sp2 =>
        if #|sp1| == #|sp2| then cbn_cv_same (k tt) L le v1 v2 e1 c1 e2 c2 true rs s
        else cbn_conv_rows X_type X Γ nctx (k tt) L le v1 v2 rs s
      | CbnVFix e1 c1 i1 sp1, CbnVFix e2 c2 i2 sp2
      | CbnVStuckFix e1 c1 i1 sp1, CbnVStuckFix e2 c2 i2 sp2 =>
        if (i1 == i2) && (#|sp1| == #|sp2|) then cbn_cv_same (k tt) L le v1 v2 e1 c1 e2 c2 true rs s
        else cbn_conv_rows X_type X Γ nctx (k tt) L le v1 v2 rs s
      | _, _ => cbn_conv_rows X_type X Γ nctx (k tt) L le v1 v2 rs s
      end
    end.
  Proof. cbn. destruct (cbn_tick s); [|reflexivity]. destruct v1, v2; reflexivity. Qed.

  (** Closures and open values: the same code makes the two readings convertible. *)
  Lemma cbn_cv_same_flat (k : unit -> cbn_fuel) :
    cbn_spec_same (k tt) -> cbn_spec_rows (k tt) ->
    forall L Q lo G pb v1 v2 w1 w2 e1 c1 e2 c2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> cbn_vwf Q v1 -> cbn_vwf Q v2 ->
      cbn_g_value nctx Q G v1 w1 -> cbn_g_value nctx Q G v2 w2 ->
      cbn_g_susp nctx Q G e1 c1.(cbn_c_term) w1 -> cbn_gcok G c1 ->
      cbn_g_susp nctx Q G e2 c2.(cbn_c_term) w2 -> cbn_gcok G c2 ->
      cbn_cv_same (k tt) L pb v1 v2 e1 c1 e2 c2 false rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb w1 w2).
  Proof.
    intros hS hR L Q lo G pb v1 v2 w1 w2 e1 c1 e2 c2 rs s b rs' s' hm hr hv1 hv2 hw1 hw2
      hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    unfold cbn_cv_same in he.
    destruct (cbn_conv_same_code X_type X Γ nctx (k tt) L e1 c1 e2 c2
      (CbnRV v1 :: CbnRV v2 :: rs) s)
      as [[[b0 rs0] s0]|w] eqn:E; [|discriminate he].
    destruct (cbn_conv_same_code_sound_ghost (k tt) hS L Q lo G pb e1 c1 e2 c2 w1 w2 _ s b0 rs0 s0
                hm (Forall_cons (CbnRV v1) hv1 (Forall_cons (CbnRV v2) hv2 hr)) hs1 hc1 hs2 hc2 E)
      as [hp0 hc0].
    destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
    destruct (cbn_gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
    destruct (cbn_gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbv beta iota in he.
    destruct b0.
    - injection he as <- <- <-. split; [|intros _; exact (hc0 eq_refl)].
      exists Q1, lo1, G1. split; [exact hq1|]. split; [exact hm1|].
      split; [exact (Forall_inv_tail (Forall_inv_tail hr1))|exact hgB].
    - destruct (hR L Q1 lo1 G1 pb v1' v2' _ _ rsB s0 b rs' s' I hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) (Forall_inv hr1)
                  (Forall_inv (Forall_inv_tail hr1)) (hk1 _ hw1) (hk2 _ hw2) he) as [hp hc].
      split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. exact (cbn_lift_conv_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  (** Stuck terms and fixpoints: the same code makes the heads convertible, then the spines are
    compared; the renamed values keep their shape, so their spines read as before. *)
  Lemma cbn_cv_same_spine (k : unit -> cbn_fuel) :
    cbn_spec_same (k tt) -> cbn_spec_cells (k tt) -> cbn_spec_rows (k tt) ->
    forall L Q lo G pb v1 v2 H1 H2 T1 T2 e1 c1 e2 c2 ts1 ts2 rs s b rs' s',
      cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs -> cbn_vwf Q v1 -> cbn_vwf Q v2 ->
      cbn_g_value nctx Q G v1 (mkApps H1 T1) -> cbn_g_value nctx Q G v2 (mkApps H2 T2) ->
      cbn_g_addrs G (cbn_spine_of v1) T1 -> cbn_g_addrs G (cbn_spine_of v2) T2 ->
      cbn_gcok G c1 -> cbn_gcok G c2 ->
      cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 ->
      (e1.(cbn_ev_goff) = e2.(cbn_ev_goff) -> e1.(cbn_ev_nvals) = e2.(cbn_ev_nvals) ->
       cbn_samec c1.(cbn_c_term) c2.(cbn_c_term) -> cbn_cagree L Q c1.(cbn_c_term) 0 ts1 ts2 ->
         cbn_lift_conv L Q pb H1 H2) ->
      cbn_cv_same (k tt) L pb v1 v2 e1 c1 e2 c2 true rs s = CbnCOk (b, rs', s') ->
      cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb (mkApps H1 T1) (mkApps H2 T2)).
  Proof.
    intros hS hC hR L Q lo G pb v1 v2 H1 H2 T1 T2 e1 c1 e2 c2 ts1 ts2 rs s b rs' s'
      hm hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2 hhead he.
    pose proof hm as [hL hLQ _ _].
    unfold cbn_cv_same in he.
    destruct (cbn_conv_same_code X_type X Γ nctx (k tt) L e1 c1 e2 c2
      (CbnRV v1 :: CbnRV v2 :: rs) s)
      as [[[b0 rs0] s0]|w] eqn:E; [|discriminate he].
    destruct (hS L Q lo G e1 c1 e2 c2 ts1 ts2 _ s b0 rs0 s0 hm
                (Forall_cons (CbnRV v1) hv1 (Forall_cons (CbnRV v2) hv2 hr)) hc1 hc2 hts1 hts2 E)
      as [hp0 hc0].
    destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
    destruct (cbn_grq_cons_inv_skel _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA & hsk1).
    destruct (cbn_gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (cbn_grq_cons_inv_skel _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB & hsk2).
    destruct (cbn_gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbn in hsk1, hsk2. injection hsk1 as hsk1. injection hsk2 as hsk2.
    cbv beta iota in he.
    destruct b0.
    - destruct (hc0 eq_refl) as (hgo & hnv & hsame & hag).
      destruct (hC L Q1 lo1 G1 (cbn_spine_of v1') (cbn_spine_of v2') _ _ rsB s0 b rs' s' hm1
                  (Forall_inv_tail (Forall_inv_tail hr1))
                  (cbn_spine_reads Q Q1 G G1 v1 v1' H1 T1 hk1 hsk1 hw1 hT1)
                  (cbn_spine_reads Q Q1 G G1 v2 v2' H2 T2 hk2 hsk2 hw2 hT2) he) as [hp hc].
      split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cbn_lift_conv_mkApps L Q pb H1 H2 T1 T2 hL (hhead hgo hnv hsame hag)).
      exact (cbn_lift_conv_s_lift _ _ _ _ _ hLQ hq1 (hc hb)).
    - destruct (hR L Q1 lo1 G1 pb v1' v2' _ _ rsB s0 b rs' s' I hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) (Forall_inv hr1)
                  (Forall_inv (Forall_inv_tail hr1)) (hk1 _ hw1) (hk2 _ hw2) he) as [hp hc].
      split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. exact (cbn_lift_conv_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  Lemma cbn_conv_value_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_same (k tt) -> cbn_spec_cells (k tt) -> cbn_spec_rows (k tt) ->
      cbn_spec_value (CbnFS k).
  Proof.
    intros hS hC hR L Q lo G pb v1 v2 w1 w2 rs s b rs' s' hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ hok _].
    rewrite cbn_conv_value_eq in he.
    destruct (cbn_tick s) as [s0|] eqn:Et; [|discriminate he].
    pose proof (cbn_minv_tick _ _ _ _ _ _ Et hm) as hm0.
    pose proof (cbn_gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    assert (hrows : cbn_conv_rows X_type X Γ nctx (k tt) L pb v1 v2 rs s0 = CbnCOk (b, rs', s') ->
              cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb w1 w2))
      by (intros h; exact (hR L Q lo G pb v1 v2 w1 w2 rs s0 b rs' s' I hm0 hr hv1 hv2 hw1 hw2 h)).
    destruct v1 as [h1 sp1|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|n1 sp1|e1 c1|e1 c1 sp1];
    destruct v2 as [h2 sp2|e2 c2|e2 c2 i2 sp2|e2 c2 i2 sp2|n2 sp2|e2 c2|e2 c2 sp2];
      cbv beta iota in he; try exact (hrows he).
    - (* closures *)
      exact (cbn_cv_same_flat k hS hR L Q lo G pb _ _ w1 w2 e1 c1 e2 c2 rs s0 b rs' s'
        hm0 hr hv1 hv2
               hw1 hw2 (cbn_g_value_VLam_inv _ _ _ _ _ _ hw1) (cbn_g_value_VLam_cok _ _ _ _ _ _ hw1)
               (cbn_g_value_VLam_inv _ _ _ _ _ _ hw2) (cbn_g_value_VLam_cok _ _ _ _ _ _ hw2) he).
    - (* fixpoints *)
      destruct ((i1 == i2) && (#|sp1| == #|sp2|)) eqn:Ei; [|exact (hrows he)].
      apply andb_true_iff in Ei as [Ei _]. apply eqb_eq in Ei. subst i2.
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply cbn_g_value_VFix_inv in hw1' as (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->).
      apply cbn_g_value_VFix_inv in hw2' as (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->).
      destruct (cbn_g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (cbn_g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      apply (cbn_cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2
        rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag. rewrite hct1, hct2 in hsame. rewrite hct1 in hag.
      pose proof (cbn_g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (cbn_g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (cbn_same_code_lift_conv L Q pb (cbn_ev_nvals e1) (cbn_ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia| | |exact (cbn_samec_fix _ _ _ _ _ hsame)|exact
          (cbn_cagree_fix _ _ _ _ _ _ _ _ hag)].
      + apply (cbn_hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
      + apply (cbn_hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
    - (* stuck fixpoints *)
      destruct ((i1 == i2) && (#|sp1| == #|sp2|)) eqn:Ei; [|exact (hrows he)].
      apply andb_true_iff in Ei as [Ei _]. apply eqb_eq in Ei. subst i2.
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply cbn_g_value_VStuckFix_inv in hw1' as
        (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->).
      apply cbn_g_value_VStuckFix_inv in hw2' as
        (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->).
      destruct (cbn_g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (cbn_g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      apply (cbn_cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2
        rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag. rewrite hct1, hct2 in hsame. rewrite hct1 in hag.
      pose proof (cbn_g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (cbn_g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (cbn_same_code_lift_conv L Q pb (cbn_ev_nvals e1) (cbn_ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia| | |exact (cbn_samec_fix _ _ _ _ _ hsame)|exact
          (cbn_cagree_fix _ _ _ _ _ _ _ _ hag)].
      + apply (cbn_hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
      + apply (cbn_hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
    - (* open values *)
      exact (cbn_cv_same_flat k hS hR L Q lo G pb _ _ w1 w2 e1 c1 e2 c2 rs s0 b rs' s'
        hm0 hr hv1 hv2
               hw1 hw2 (cbn_g_value_VOpen_inv _ _ _ _ _ _ hw1) ltac:(inversion hw1; assumption)
               (cbn_g_value_VOpen_inv _ _ _ _ _ _ hw2) ltac:(inversion hw2; assumption) he).
    - (* stuck matches and projections *)
      destruct (#|sp1| == #|sp2|) eqn:Ei; [|exact (hrows he)].
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply cbn_g_value_VStuck_inv in hw1' as (H1 & T1 & hh1 & hT1 & ->).
      apply cbn_g_value_VStuck_inv in hw2' as (H2 & T2 & hh2 & hT2 & ->).
      destruct (cbn_g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (cbn_g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      pose proof (cbn_g_value_VStuck_cok _ _ _ _ _ _ _ hw1) as hc1.
      pose proof (cbn_g_value_VStuck_cok _ _ _ _ _ _ _ hw2) as hc2.
      apply (cbn_cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2
        rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag.
      pose proof (cbn_g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (cbn_g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (cbn_same_code_lift_conv L Q pb (cbn_ev_nvals e1) (cbn_ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia|exact (hch _ hc1)|exact (hch _ hc2)|exact hsame|exact hag].
  Qed.

  (** ** The stuck-match rule: the branches *)

  Lemma cbn_rbody_lift d ts N br :
    cbn_rbody (map (lift0 d) ts) (d + N) br = lift d #|br.(bcontext)| (cbn_rbody ts N br).
  Proof. unfold cbn_rbody. rewrite length_map. apply cbn_lift_bodyk. reflexivity. Qed.

  (** A branch body read through [n] fresh variables pushed on its environment, at the master
    level, is the lift of the logical body. *)
  Lemma cbn_fresh_branch_read L Q n N ts t U :
    L <= Q ->
    subst ts n (lift N (n + #|ts|) t) = lift (Q - L) n U ->
    subst (map (lift0 (Q - L)) (idsn n) ++ map (lift0 n) ts) 0 (lift (n + N) (n + #|ts|) t)
    = lift0 (Q - L) U.
  Proof.
    intros hLQ e.
    rewrite subst_app_simpl, length_map, idsn_length. cbn [Nat.add].
    rewrite (cbn_lift_bodyk n ts N #|ts| n t eq_refl), e.
    rewrite simpl_lift by lia.
    replace (n + (Q - L)) with ((Q - L) + n) by lia. apply cbn_cg_subst_fresh_lift.
  Qed.

  Lemma cbn_branches_lift L Q QC ts1 ts2 N1 N2 l1 l2 :
    L <= Q -> Q <= QC ->
    Forall2 (fun br1 br2 => cbn_case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cbn_lift_conv_b L QC #|br1.(bcontext)| Conv
        (cbn_rbody (map (lift0 (QC - Q)) ts1) ((QC - Q) + N1) br1)
                                         (cbn_rbody (map (lift0 (QC - Q)) ts2) ((QC - Q) + N2) br2))
      l1 l2 ->
    Forall2 (fun br1 br2 => cbn_case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cbn_lift_conv_b L Q #|br1.(bcontext)| Conv (cbn_rbody ts1 N1 br1) (cbn_rbody ts2 N2 br2))
        l1 l2.
  Proof.
    intros hLQ hQ h. induction h as [|br1 br2 l1 l2 [hc hq] _ ih]; constructor; [|exact ih].
    split; [exact hc|]. apply (cbn_lift_conv_b_lift L Q QC _ Conv _ _ hLQ hQ).
    rewrite !cbn_rbody_lift in hq. destruct (cbn_case_ctx_ok_spec _ _ hc) as [hx _ _].
    rewrite <- (All2_length hx) in hq. exact hq.
  Qed.

  Lemma cbn_case_branches_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_term (k tt) -> cbn_spec_branches (k tt) -> cbn_spec_branches (CbnFS k).
  Proof.
    intros hT hB L Q lo G e1 c1 e2 c2 i l1 l2 ts1 ts2 rs s b rs' s'
      hm hr hb1 hb2 hs1 hn1 hs2 hn2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_case_branches_eq in he.
    destruct l1 as [|br1 l1]; destruct l2 as [|br2 l2].
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros _. constructor.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hb1 as [|i1 z1 m1 hc1 hb1']; subst.
      inversion hb2 as [|i2 z2 m2 hc2 hb2']; subst.
      cbv beta iota in he.
      destruct (cbn_case_ctx_ok (bcontext br1) (bcontext br2)) eqn:Ectx;
        [|injection he as <- <- <-;
          split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
      destruct (cbn_case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
      pose proof (All2_length hctx) as hn12.
      assert (hr0 : Forall (cbn_rwf Q) (CbnRE e1 :: CbnRE e2 :: rs))
        by (constructor; [exact I|constructor; [exact I|exact hr]]).
      pose proof (cbn_minv_raise L Q #|bcontext br1| lo G s hm) as hmR.
      pose proof (cbn_rwfs_mono Q (Q + #|bcontext br1|) _ ltac:(lia) hr0) as hrR.
      pose proof (cbn_grq_raise Q #|bcontext br1| G _ ltac:(lia) hr0) as hgR.
      pose proof (proj2 (cbn_g_slot_shift nctx Q #|bcontext br1| ltac:(lia) G) _ _ hs1) as [hs1R _].
      pose proof (proj2 (cbn_g_slot_shift nctx Q #|bcontext br1| ltac:(lia) G) _ _ hs2) as [hs2R _].
      destruct (cbn_push_fresh #|bcontext br1| L e1 e2 (CbnRE e1 :: CbnRE e2 :: rs) s)
        as [[[r rsP] sP]|w] eqn:EP; [|discriminate he].
      destruct (cbn_push_fresh_g #|bcontext br1| L (Q + #|bcontext br1|) lo
        (cbn_gshift #|bcontext br1| G)
                  L e1 e2 _ _ _ s r rsP sP hmR hrR ltac:(lia) hs1R hn1 hs2R hn2 EP)
        as (loP & GP & f1 & f2 & -> & hmP & hrP & hgP & hnf1 & hgf1 & hnf2 & hgf2 & hf1 & hf2).
      pose proof (cbn_push_fresh_skel _ _ _ _ _ _ _ _ _ EP) as hkP.
      cbv beta iota in he.
      pose proof (cbn_g_susp_of_slots nctx _ GP f1 (bbody br1) _ hf1 hnf1) as hB1.
      pose proof (cbn_g_susp_of_slots nctx _ GP f2 (bbody br2) _ hf2 hnf2) as hB2.
      destruct (cbn_conv_term X_type X Γ nctx (k tt) (L + #|bcontext br1|) Conv
                  f1 (cbn_child c1 (cbn_case_branch_step i) (bbody br1))
                  f2 (cbn_child c2 (cbn_case_branch_step i) (bbody br2)) rsP sP)
        as [[[bC rsC] sC]|w] eqn:EC; [|discriminate he].
      destruct (hT (L + #|bcontext br1|) (Q + #|bcontext br1|) loP GP Conv
                  f1 (cbn_child c1 (cbn_case_branch_step i) (bbody br1))
                  f2 (cbn_child c2 (cbn_case_branch_step i) (bbody br2)) _ _ rsP sP bC rsC sC
                  (cbn_minv_level L (L + #|bcontext br1|) (Q + #|bcontext br1|) loP GP sP hmP
                     ltac:(lia) ltac:(lia)) hrP hB1
                  (cbn_cok_gcx _ _ (proj1 hgP) _ hc1) hB2 (cbn_cok_gcx _ _ (proj1 hgP) _ hc2) EC)
        as [hpC hcC].
      (* the roots [cbn_push_fresh] handed back *)
      destruct (cbn_gren_cons_inv _ _ _ _ _ _ hgP) as (p1 & rsP1 & -> & hp1 & hgP1).
      destruct (cbn_gpres_RE_inv _ _ _ _ _ hp1) as (e1' & -> & (hne1 & hge1 & hke1)).
      destruct (cbn_gren_cons_inv _ _ _ _ _ _ hgP1) as (p2 & rsP' & -> & hp2 & hgP').
      destruct (cbn_gpres_RE_inv _ _ _ _ _ hp2) as (e2' & -> & (hne2 & hge2 & hke2)).
      assert (hgR' : cbn_grq Q (Q + #|bcontext br1|) G (cbn_gshift #|bcontext br1| G) rs rs).
      { destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgR) as (a1 & ra & ea & _ & hga).
        injection ea as <- <-.
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hga) as (a2 & rb & eb & _ & hgb).
        injection eb as <- <-. exact hgb. }
      assert (hgP'' : cbn_grq (Q + #|bcontext br1|) (Q + #|bcontext br1|)
        (cbn_gshift #|bcontext br1| G)
                        GP rs rsP').
      { apply cbn_grq_of_gren; [exact hgP'|exact (cbn_sk_tl _ _ _ _ (cbn_sk_tl _ _ _ _ hkP))]. }
      destruct bC.
      + destruct hpC as (QC & loC & GC & hqC & hmC & hrC & hgC).
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgC) as (q1 & rsC1 & -> & hqa & hgC1).
        destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqa) as (g1 & -> & hng1 & hgg1 & hkg1).
        destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgC1) as (q2 & rsC' & -> & hqb & hgC').
        destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqb) as (g2 & -> & hng2 & hgg2 & hkg2).
        cbv beta iota in he.
        pose proof (hkg1 _ (hke1 _ hs1R)) as hg1s. pose proof (hkg2 _ (hke2 _ hs2R)) as hg2s.
        rewrite cbn_map_lift0_lift0 in hg1s, hg2s.
        replace (QC - (Q + #|bcontext br1|) + #|bcontext br1|) with (QC - Q) in hg1s, hg2s
          by lia.
        pose proof (cbn_g_slots_length _ _ _ _ _ hs1) as hl1.
        pose proof (cbn_g_slots_length _ _ _ _ _ hs2) as hl2.
        pose proof (cbn_g_slots_length _ _ _ _ _ hg1s) as hl1'. rewrite length_map in hl1'.
        pose proof (cbn_g_slots_length _ _ _ _ _ hg2s) as hl2'. rewrite length_map in hl2'.
        destruct (hB L QC loC GC g1 c1 g2 c2 (N.succ i) l1 l2 _ _ rsC' sC b rs' s'
                    (cbn_minv_level _ L _ _ _ _ hmC ltac:(lia) ltac:(lia))
                    (Forall_inv_tail (Forall_inv_tail hrC))
                    (cbn_bcodes_gcx _ _ _ _ _ (proj1 hgC)
                       (cbn_bcodes_gcx _ _ _ _ _ (proj1 hgP)
                          (cbn_bcodes_gcx G (cbn_gshift #|bcontext br1| G) _ _ _
                            (fun _ _ h => h) hb1')))
                    (cbn_bcodes_gcx _ _ _ _ _ (proj1 hgC)
                       (cbn_bcodes_gcx _ _ _ _ _ (proj1 hgP)
                          (cbn_bcodes_gcx G (cbn_gshift #|bcontext br1| G) _ _ _
                            (fun _ _ h => h) hb2')))
                    hg1s ltac:(lia) hg2s ltac:(lia) he) as [hp hc].
        split.
        * apply (cbn_post_compose L Q (Q + #|bcontext br1|) G _ rs rs s' rs' ltac:(lia) hgR').
          apply (cbn_post_compose L _ _ _ GP rs rsP' s' rs' (le_n _) hgP'').
          exact (cbn_post_compose L _ QC GP GC rsP' rsC' s' rs' hqC hgC' hp).
        * intros hb. constructor.
          -- split; [exact Ectx|]. intros U1 U2 eU1 eU2 sU1 sU2.
             apply (hcC eq_refl U1 U2); [| |exact sU1|exact sU2].
             ++ replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                rewrite hgf1, hnf1.
                pose proof (cbn_g_slots_length _ _ _ _ _ hf1) as hlf.
                rewrite length_app, length_map, idsn_length, length_map in hlf.
                rewrite <- hlf.
                replace (Q + #|bcontext br1| - nctx + cbn_ev_goff e1)
                  with (#|bcontext br1| + (Q - nctx + cbn_ev_goff e1)) by lia.
                replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                apply cbn_fresh_branch_read; [lia|]. exact eU1.
             ++ replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                rewrite hgf2, hnf2.
                pose proof (cbn_g_slots_length _ _ _ _ _ hf2) as hlf.
                rewrite length_app, length_map, idsn_length, length_map in hlf.
                rewrite <- hlf.
                replace (Q + #|bcontext br1| - nctx + cbn_ev_goff e2)
                  with (#|bcontext br1| + (Q - nctx + cbn_ev_goff e2)) by lia.
                replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                apply cbn_fresh_branch_read; [lia|]. unfold cbn_rbody in eU2.
                rewrite <- hn12 in eU2.
                exact eU2.
          -- apply (cbn_branches_lift L Q QC ts1 ts2 _ _ l1 l2 hLQ ltac:(lia)).
             rewrite hgg1, hge1, hgg2, hge2 in hc.
             replace (QC - nctx + cbn_ev_goff e1) with
               ((QC - Q) + (Q - nctx + cbn_ev_goff e1)) in hc
               by lia.
             replace (QC - nctx + cbn_ev_goff e2) with
               ((QC - Q) + (Q - nctx + cbn_ev_goff e2)) in hc
               by lia.
             exact (hc hb).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [|intros hb; discriminate hb].
        apply (cbn_post_compose L Q (Q + #|bcontext br1|) G _ rs rs _ _ ltac:(lia) hgR').
        apply (cbn_post_compose L _ _ _ GP rs rsP' _ _ (le_n _) hgP'').
        apply (cbn_post_drop2 L _ GP (CbnRE e1') (CbnRE e2') rsP').
        exact (cbn_post_level L (L + #|bcontext br1|) (Q + #|bcontext br1|) GP _ _ _ hL
                 ltac:(lia) hpC).
  Qed.

  (** ** The read-back: the machine side

    The read-back functions [cbn_rb_cell], [cbn_rb_slot], [cbn_rb_susp] and [cbn_rb_value] only read
    the heap and [cbn_tick]: they leave the heap, the next address, the context map and the memo
    alone ([cbn_rb_state]), so they keep [cbn_minv] whatever the readings are ([cbn_rb_minv]). *)

  #[local] Definition cbn_sst (s s' : cbn_state) : Prop :=
    s'.(cbn_st_heap) = s.(cbn_st_heap) /\ s'.(cbn_st_next) = s.(cbn_st_next) /\
      s'.(cbn_st_gam) = s.(cbn_st_gam)
    /\ s'.(cbn_st_memo) = s.(cbn_st_memo).

  Lemma cbn_sst_refl s : cbn_sst s s.
  Proof. repeat split. Qed.

  Lemma cbn_sst_trans s1 s2 s3 : cbn_sst s1 s2 -> cbn_sst s2 s3 -> cbn_sst s1 s3.
  Proof. intros (a1 & b1 & c1 & d1) (a2 & b2 & c2 & d2). repeat split; congruence. Qed.

  Lemma cbn_map_st_sst {A B : Type} (f : A -> cbn_state -> cbn_res (B * cbn_state)) :
    (forall x s y s', f x s = CbnCOk (y, s') -> cbn_sst s s') ->
    forall l s ys s', cbn_map_st f l s = CbnCOk (ys, s') -> cbn_sst s s'.
  Proof.
    intros hf. induction l as [|x l ih]; intros s ys s' h; cbn in h.
    - injection h as _ <-. apply cbn_sst_refl.
    - destruct (f x s) as [[y s1]|w] eqn:E1; [|discriminate h].
      destruct (cbn_map_st f l s1) as [[ys1 s2]|w] eqn:E2; [|discriminate h].
      injection h as _ <-. exact (cbn_sst_trans _ _ _ (hf _ _ _ _ E1) (ih _ _ _ E2)).
  Qed.

  Lemma cbn_rb_state (n : nat) (d : cbn_fuel) :
    (forall lvl a s t s', cbn_rb_cell n d lvl a s = CbnCOk (t, s') -> cbn_sst s s')
    /\ (forall lvl x s t s', cbn_rb_slot n d lvl x s = CbnCOk (t, s') -> cbn_sst s s')
    /\ (forall lvl e u s t s', cbn_rb_susp n d lvl e u s = CbnCOk (t, s') -> cbn_sst s s')
    /\ (forall lvl v s t s', cbn_rb_value n d lvl v s = CbnCOk (t, s') -> cbn_sst s s').
  Proof.
    induction d as [|k ih].
    { repeat split; intros; match goal with h : _ = CbnCOk _ |- _ => cbn in h; discriminate h end. }
    destruct (ih tt) as (hc & hsl & hsu & hv).
    assert (hsp : forall lvl h0 sp s t s',
               match cbn_map_st (cbn_rb_cell n (k tt) lvl) sp s with
               | CbnCOk (ts, s) => CbnCOk (mkApps h0 ts, s)
               | CbnCFail w => CbnCFail w
               end = CbnCOk (t, s') -> cbn_sst s s').
    { intros lvl h0 sp s t s' h.
      destruct (cbn_map_st (cbn_rb_cell n (k tt) lvl) sp s) as [[ts s1]|w] eqn:Em;
        [|discriminate h].
      injection h as _ <-. exact (cbn_map_st_sst _ (fun x s0 y s0' hh => hc _ _ _ _ _ hh) _
        _ _ _ Em). }
    split; [|split; [|split]].
    - intros lvl a s t s' h. cbn [cbn_rb_cell] in h.
      destruct (cbn_heap_get a s) as [[vs nv o c|v| |b]|]; try discriminate h.
      + exact (hsu _ _ _ _ _ _ h).
      + exact (hv _ _ _ _ _ h).
    - intros lvl x s t s' h. cbn [cbn_rb_slot] in h.
      destruct x as [a|vs nv o c]; [exact (hc _ _ _ _ _ h)|exact (hsu _ _ _ _ _ _ h)].
    - intros lvl e u s t s' h. cbn [cbn_rb_susp] in h.
      destruct (cbn_tick s) as [s0|] eqn:Et; [|discriminate h].
      destruct (cbn_map_st (cbn_rb_slot n (k tt) lvl) (cbn_ev_vals e) s0) as [[ts s1]|w] eqn:Em;
        [|discriminate h].
      injection h as _ <-.
      destruct (cbn_tick_shape s s0 Et) as (th & tn & _ & tg & tm).
      apply (cbn_sst_trans s s0 s1); [repeat split; assumption|].
      exact (cbn_map_st_sst _ (fun x s2 y s2' hh => hsl _ _ _ _ _ hh) _ _ _ _ Em).
    - intros lvl v s t s' h. cbn [cbn_rb_value] in h.
      destruct v as [h0 sp|e c|e c i sp|e c i sp|[l|h0] sp|e c|e c sp].
      + exact (hsp _ _ _ _ _ _ h).
      + exact (hsu _ _ _ _ _ _ h).
      + destruct (cbn_c_term c); try discriminate h.
        destruct (cbn_rb_susp n (k tt) lvl e _ s) as [[h1 s1]|w] eqn:E1; [|discriminate h].
        exact (cbn_sst_trans _ _ _ (hsu _ _ _ _ _ _ E1) (hsp _ _ _ _ _ _ h)).
      + destruct (cbn_c_term c); try discriminate h.
        destruct (cbn_rb_susp n (k tt) lvl e _ s) as [[h1 s1]|w] eqn:E1; [|discriminate h].
        exact (cbn_sst_trans _ _ _ (hsu _ _ _ _ _ _ E1) (hsp _ _ _ _ _ _ h)).
      + exact (hsp _ _ _ _ _ _ h).
      + exact (hsp _ _ _ _ _ _ h).
      + exact (hsu _ _ _ _ _ _ h).
      + destruct (cbn_rb_susp n (k tt) lvl e (cbn_c_term c) s) as [[h1 s1]|w] eqn:E1;
        [|discriminate h].
        exact (cbn_sst_trans _ _ _ (hsu _ _ _ _ _ _ E1) (hsp _ _ _ _ _ _ h)).
  Qed.

  Lemma cbn_rb_minv L Q lo G d lvl e t s u s' :
    cbn_rb_susp nctx d lvl e t s = CbnCOk (u, s') -> cbn_MI L Q lo G s -> cbn_MI L Q lo G s'.
  Proof.
    intros h hm. destruct (proj1 (proj2 (proj2 (cbn_rb_state nctx d))) _ _ _ _ _ _ h)
      as (e1 & e2 & e3 & e4).
    eapply cbn_minv_same; [exact hm|exact e1|exact e2|exact e3|exact e4].
  Qed.

  (** ** The read-back: the conversion side

    [cbn_rb_sound] of [PCUICCallByNeedSoundLevel], which
    [PCUICCallByNeedSoundReadBack.cbn_rb_sound_holds] proves. *)
  Context (hrb : cbn_rb_sound X_type X Γ nctx Σ).

  (** Two heads that reduce to terms equal up to universes at [Conv] (with [napp] arguments),
    applied to convertible spines, are convertible at any [conv_pb]. *)
  Lemma cbn_cv_rb_spine L pb h1 h2 r1 r2 us1 us2 :
    nctx <= L -> cbn_scl L h1 -> cbn_scl L h2 -> forallb (cbn_scl L) us1 ->
      forallb (cbn_scl L) us2 ->
    (forall Δ, #|Δ| = L - nctx -> ∥ PCUICReduction.red Σ (Γ ,,, Δ) h1 r1 ∥) ->
    (forall Δ, #|Δ| = L - nctx -> ∥ PCUICReduction.red Σ (Γ ,,, Δ) h2 r2 ∥) ->
    compare_term_napp Σ Σ Conv #|us1| r1 r2 -> cbn_cvs L us1 us2 ->
    cbn_cv L pb (mkApps h1 us1) (mkApps h2 us2).
  Proof.
    intros hL sh1 sh2 sus1 sus2 hd1 hd2 hcmp hcs Δ hΔ hcl.
    destruct (hd1 Δ hΔ) as [rd1]. destruct (hd2 Δ hΔ) as [rd2].
    destruct (hcs Δ hΔ hcl) as [hs].
    pose proof (cbn_red_scl L Δ h1 r1 hL hΔ hcl sh1 rd1) as sr1.
    pose proof (cbn_red_scl L Δ h2 r2 hL hΔ hcl sh2 rd2) as sr2.
    assert (ho1 : is_open_term (Γ ,,, Δ) (mkApps h1 us1)).
    { apply (cbn_scl_open L Δ _ hL hΔ). unfold cbn_scl. rewrite on_free_vars_mkApps.
      apply andb_true_iff. split; assumption. }
    assert (ho2 : is_open_term (Γ ,,, Δ) (mkApps h2 us2)).
    { apply (cbn_scl_open L Δ _ hL hΔ). unfold cbn_scl. rewrite on_free_vars_mkApps.
      apply andb_true_iff. split; assumption. }
    constructor.
    eapply (cbn_ws_cumul_pb_closed_red (wfΣ := wfΣ)).
    - apply into_closed_red; [|exact hcl|exact ho1].
      apply PCUICReduction.red_mkApps_f. exact rd1.
    - apply into_closed_red; [|exact hcl|exact ho2].
      apply PCUICReduction.red_mkApps_f. exact rd2.
    - apply (ws_cumul_eq_pb (wfΣ := wfΣ)).
      apply (cbn_ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
        [exact hcl|exact (cbn_scl_open L Δ r1 hL hΔ sr1)|exact (cbn_scl_open L Δ r2 hL hΔ sr2)
        |exact hcmp|exact hs].
  Qed.

  (** Read back two heads, compare them syntactically, then compare the spines: the fallback
    of the stuck-term row and the fixpoint rows. *)
  Definition cbn_head_rb (d : cbn_fuel) (L : nat) (e1 : cbn_env) (a1 : term) (e2 : cbn_env)
      (a2 : term) (n : nat) (sp1 sp2 : list cbn_haddr) (rs : list cbn_root) (s : cbn_state) :=
    match cbn_rb_susp nctx d L e1 a1 s with
    | CbnCOk (t1, s) =>
      match cbn_rb_susp nctx d L e2 a2 s with
      | CbnCOk (t2, s) =>
        if cbn_cmp_term X_type X Conv n t1 t2 then cbn_conv_cells X_type X Γ nctx d L sp1 sp2 rs s
        else CbnCOk (false, rs, s)
      | CbnCFail w => CbnCFail w
      end
    | CbnCFail w => CbnCFail w
    end.

  Lemma cbn_head_rb_g (k : unit -> cbn_fuel) (hC : cbn_spec_cells (k tt))
      L Q lo G pb e1 a1 e2 a2 sp1 sp2 H1 H2 T1 T2 rs s b rs' s' :
    cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
    on_free_vars cbn_xpredT a1 -> on_free_vars cbn_xpredT a2 ->
    cbn_g_susp nctx Q G e1 a1 H1 -> cbn_g_susp nctx Q G e2 a2 H2 ->
    cbn_g_addrs G sp1 T1 -> cbn_g_addrs G sp2 T2 ->
    cbn_head_rb (k tt) L e1 a1 e2 a2 #|sp1| sp1 sp2 rs s = CbnCOk (b, rs', s') ->
    cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb (mkApps H1 T1) (mkApps H2 T2)).
  Proof.
    intros hm hr hy1 hy2 hs1 hs2 hT1 hT2 he.
    pose proof hm as [hL hLQ _ _].
    unfold cbn_head_rb in he.
    destruct (cbn_rb_susp nctx (k tt) L e1 a1 s) as [[r1 s1]|w] eqn:E1; [|discriminate he].
    destruct (cbn_rb_susp nctx (k tt) L e2 a2 s1) as [[r2 s2]|w] eqn:E2; [|discriminate he].
    pose proof (cbn_rb_minv L Q lo G _ _ _ _ _ _ _ E1 hm) as hm1.
    pose proof (cbn_rb_minv L Q lo G _ _ _ _ _ _ _ E2 hm1) as hm2.
    destruct (cbn_cmp_term X_type X Conv #|sp1| r1 r2) eqn:Ecmp;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm2 hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G sp1 sp2 T1 T2 rs s2 b rs' s' hm2 hr hT1 hT2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 eu1 eu2 su1 su2.
    apply cbn_mkApps_lift0_inv in eu1 as (h1' & us1 & -> & eh1 & ->).
    apply cbn_mkApps_lift0_inv in eu2 as (h2' & us2 & -> & eh2 & ->).
    unfold cbn_scl in su1, su2. rewrite on_free_vars_mkApps in su1, su2.
    apply andb_true_iff in su1 as [sh1 sus1]. apply andb_true_iff in su2 as [sh2 sus2].
    subst H1 H2.
    destruct (hrb (k tt) L Q lo G e1 a1 h1' s hm hy1 (cbn_scl_hyg L h1' sh1) hs1 r1 s1 E1)
      as [_ hd1].
    destruct (hrb (k tt) L Q lo G e2 a2 h2' s1 hm1 hy2 (cbn_scl_hyg L h2' sh2) hs2 r2 s2 E2)
      as [_ hd2].
    apply (cbn_cv_rb_spine L pb h1' h2' r1 r2 us1 us2 hL sh1 sh2 sus1 sus2 hd1 hd2).
    - pose proof (cbn_cmp_term_sound X_type X Σ hΣ Conv _ r1 r2 Ecmp) as hcmp.
      rewrite <- (cbn_g_addrs_length _ _ _ hT1), length_map in hcmp. exact hcmp.
    - exact (hc hb us1 us2 eq_refl eq_refl sus1 sus2).
  Qed.

  (** *** The primitive row *)

  Lemma cbn_conv_rows_prim_eq k L le e1 c1 e2 c2 p1 p2 rs s :
    c1.(cbn_c_term) = tPrim p1 -> c2.(cbn_c_term) = tPrim p2 ->
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVOpen e1 c1) (CbnVOpen e2 c2) rs s =
    match cbn_rb_susp nctx (k tt) L e1 (tPrim p1) s with
    | CbnCOk (t1, s) =>
      match cbn_rb_susp nctx (k tt) L e2 (tPrim p2) s with
      | CbnCOk (t2, s) => CbnCOk (cbn_cmp_term X_type X Conv 0 t1 t2, rs, s)
      | CbnCFail w => CbnCFail w
      end
    | CbnCFail w => CbnCFail w
    end.
  Proof. destruct c1 as [i1 q1 t1], c2 as [i2 q2 t2]. cbn [cbn_c_term]. intros -> ->.
    reflexivity. Qed.

  Lemma cbn_conv_rows_prim_g (k : unit -> cbn_fuel) :
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists e1 c1 e2 c2 p1 p2,
                           v1 = CbnVOpen e1 c1 /\ v2 = CbnVOpen e2 c2
                           /\ c1.(cbn_c_term) = tPrim p1 /\ c2.(cbn_c_term) = tPrim p2).
  Proof.
    intros L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & e2 & c2 & p1 & p2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ hok _].
    pose proof (cbn_gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    assert (hc1 : cbn_gcok G c1) by (inversion hw1; assumption).
    assert (hc2 : cbn_gcok G c2) by (inversion hw2; assumption).
    apply cbn_g_value_VOpen_inv in hw1. apply cbn_g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    assert (hy1 : on_free_vars cbn_xpredT (tPrim p1)) by (rewrite <- h1; exact (hch _ hc1)).
    assert (hy2 : on_free_vars cbn_xpredT (tPrim p2)) by (rewrite <- h2; exact (hch _ hc2)).
    rewrite (cbn_conv_rows_prim_eq k L pb e1 c1 e2 c2 p1 p2 rs s h1 h2) in he.
    destruct (cbn_rb_susp nctx (k tt) L e1 (tPrim p1) s) as [[r1 s1]|w] eqn:E1; [|discriminate he].
    destruct (cbn_rb_susp nctx (k tt) L e2 (tPrim p2) s1) as [[r2 s2]|w] eqn:E2; [|discriminate he].
    pose proof (cbn_rb_minv L Q lo G _ _ _ _ _ _ _ E1 hm) as hm1.
    pose proof (cbn_rb_minv L Q lo G _ _ _ _ _ _ _ E2 hm1) as hm2.
    injection he as <- <- <-.
    split; [exact (cbn_post_refl _ _ _ _ _ _ hm2 hr)|].
    intros hb u1 u2 eu1 eu2 su1 su2. subst w1 w2.
    destruct (hrb (k tt) L Q lo G e1 _ u1 s hm hy1 (cbn_scl_hyg L u1 su1) hw1 r1 s1 E1) as [_ hd1].
    destruct (hrb (k tt) L Q lo G e2 _ u2 s1 hm1 hy2 (cbn_scl_hyg L u2 su2) hw2 r2 s2 E2) as
      [_ hd2].
    exact (cbn_cv_rb_spine L pb u1 u2 r1 r2 [] [] hL su1 su2 eq_refl eq_refl hd1 hd2
             (cbn_cmp_term_sound X_type X Σ hΣ Conv 0 r1 r2 hb)
             (fun Δ _ _ => sq All2_nil)).
  Qed.

  (** *** The fixpoint rows *)

  Lemma cbn_conv_rows_fix_eq k L le e1 c1 i1 sp1 e2 c2 i2 sp2 rs s :
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVFix e1 c1 i1 sp1)
      (CbnVFix e2 c2 i2 sp2) rs s =
    if (i1 == i2) && (#|sp1| == #|sp2|) then
      match c1.(cbn_c_term), c2.(cbn_c_term) with
      | tFix m1 _, tFix m2 _ => cbn_head_rb (k tt) L e1 (tFix m1 i1) e2 (tFix m2 i2) #|sp1|
        sp1 sp2 rs s
      | _, _ => CbnCOk (false, rs, s)
      end
    else CbnCOk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_conv_rows_sfix_eq k L le e1 c1 i1 sp1 e2 c2 i2 sp2 rs s :
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVStuckFix e1 c1 i1 sp1)
      (CbnVStuckFix e2 c2 i2 sp2) rs s =
    if (i1 == i2) && (#|sp1| == #|sp2|) then
      match c1.(cbn_c_term), c2.(cbn_c_term) with
      | tFix m1 _, tFix m2 _ => cbn_head_rb (k tt) L e1 (tFix m1 i1) e2 (tFix m2 i2) #|sp1|
        sp1 sp2 rs s
      | _, _ => CbnCOk (false, rs, s)
      end
    else CbnCOk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_fix_rows_core (k : unit -> cbn_fuel) (hC : cbn_spec_cells (k tt))
      L Q lo G pb e1 c1 i1 sp1 e2 c2 i2 sp2 w1 w2 rs s b rs' s' :
    cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
    (exists m1 idx1 H1 T1, c1.(cbn_c_term) = tFix m1 idx1 /\ cbn_g_susp nctx Q G e1 (tFix m1 i1) H1
       /\ cbn_gcok G c1 /\ cbn_g_addrs G sp1 T1 /\ w1 = mkApps H1 T1) ->
    (exists m2 idx2 H2 T2, c2.(cbn_c_term) = tFix m2 idx2 /\ cbn_g_susp nctx Q G e2 (tFix m2 i2) H2
       /\ cbn_gcok G c2 /\ cbn_g_addrs G sp2 T2 /\ w2 = mkApps H2 T2) ->
    (if (i1 == i2) && (#|sp1| == #|sp2|) then
       match c1.(cbn_c_term), c2.(cbn_c_term) with
       | tFix m1 _, tFix m2 _ =>
         cbn_head_rb (k tt) L e1 (tFix m1 i1) e2 (tFix m2 i2) #|sp1| sp1 sp2 rs s
       | _, _ => CbnCOk (false, rs, s)
       end
     else CbnCOk (false, rs, s)) = CbnCOk (b, rs', s') ->
    cbn_post L Q G rs s' rs' /\ (b = true -> cbn_lift_conv L Q pb w1 w2).
  Proof.
    intros hm hr (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->)
      (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->) he.
    pose proof hm as [hL hLQ hok _].
    pose proof (cbn_gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    destruct ((i1 == i2) && (#|sp1| == #|sp2|));
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    rewrite hct1, hct2 in he.
    apply (cbn_head_rb_g k hC L Q lo G pb e1 (tFix m1 i1) e2 (tFix m2 i2) sp1 sp2 H1 H2 T1 T2 rs s b
      rs' s' hm hr);
      [| |exact hh1|exact hh2|exact hT1|exact hT2|exact he].
    - apply (cbn_hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
    - apply (cbn_hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
  Qed.

  (** *** The stuck-term row: the case congruence, then the read-back of the heads *)

  Lemma cbn_conv_rows_stuck_eq k L le e1 c1 sp1 e2 c2 sp2 rs s :
    cbn_conv_rows X_type X Γ nctx (CbnFS k) L le (CbnVStuck e1 c1 sp1) (CbnVStuck e2 c2 sp2) rs s =
    if #|sp1| == #|sp2| then
      match match c1.(cbn_c_term), c2.(cbn_c_term) with
            | tCase _ _ _ _, tCase _ _ _ _ =>
              cbn_case_cong X_type X Γ nctx (k tt) L e1 c1 e2 c2
                (CbnRV (CbnVStuck e1 c1 sp1) :: CbnRV (CbnVStuck e2 c2 sp2) :: rs) s
            | _, _ => CbnCOk (false, CbnRV (CbnVStuck e1 c1 sp1)
              :: CbnRV (CbnVStuck e2 c2 sp2) :: rs, s)
            end with
      | CbnCOk (b, rs, s) =>
        match rs with
        | CbnRV (CbnVStuck e1 c1 sp1) :: CbnRV (CbnVStuck e2 c2 sp2) :: rs =>
          if b then cbn_conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s
          else cbn_head_rb (k tt) L e1 c1.(cbn_c_term) e2 c2.(cbn_c_term) #|sp1| sp1 sp2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | CbnCFail w => CbnCFail w
      end
    else CbnCOk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma cbn_conv_rows_stuck_g (k : unit -> cbn_fuel) :
    cbn_spec_cells (k tt) -> cbn_spec_case (k tt) ->
    cbn_spec_rows_on (CbnFS k) (fun v1 v2 => exists e1 c1 sp1 e2 c2 sp2,
                           v1 = CbnVStuck e1 c1 sp1 /\ v2 = CbnVStuck e2 c2 sp2).
  Proof.
    intros hC hK L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & sp1 & e2 & c2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_conv_rows_stuck_eq in he.
    destruct (#|sp1| == #|sp2|);
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    pose proof hw1 as hw1'. pose proof hw2 as hw2'.
    apply cbn_g_value_VStuck_inv in hw1' as (H1 & T1 & hh1 & hT1 & ->).
    apply cbn_g_value_VStuck_inv in hw2' as (H2 & T2 & hh2 & hT2 & ->).
    pose proof (cbn_g_value_VStuck_cok _ _ _ _ _ _ _ hw1) as hc1.
    pose proof (cbn_g_value_VStuck_cok _ _ _ _ _ _ _ hw2) as hc2.
    assert (hr0 : Forall (cbn_rwf Q) (CbnRV (CbnVStuck e1 c1 sp1)
      :: CbnRV (CbnVStuck e2 c2 sp2) :: rs))
      by (constructor; [exact hv1|constructor; [exact hv2|exact hr]]).
    destruct (match c1.(cbn_c_term), c2.(cbn_c_term) with
              | tCase _ _ _ _, tCase _ _ _ _ =>
                cbn_case_cong X_type X Γ nctx (k tt) L e1 c1 e2 c2
                  (CbnRV (CbnVStuck e1 c1 sp1) :: CbnRV (CbnVStuck e2 c2 sp2) :: rs) s
              | _, _ => CbnCOk (false, CbnRV (CbnVStuck e1 c1 sp1)
                :: CbnRV (CbnVStuck e2 c2 sp2) :: rs, s)
              end) as [[[bK rsK] sK]|w] eqn:EK; [|discriminate he].
    assert (hK' : cbn_post L Q G (CbnRV (CbnVStuck e1 c1 sp1) :: CbnRV (CbnVStuck e2 c2 sp2) :: rs)
      sK rsK /\ (bK = true -> cbn_lift_conv L Q pb H1 H2)).
    { destruct (cbn_c_term c1) eqn:Ec1;
        try (injection EK as <- <- <-;
             split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr0)|intros hb; discriminate hb]).
      destruct (cbn_c_term c2) eqn:Ec2;
        try (injection EK as <- <- <-;
             split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr0)|intros hb; discriminate hb]).
      rewrite <- Ec1 in hh1. rewrite <- Ec2 in hh2.
      exact (hK L Q lo G pb e1 c1 e2 c2 H1 H2 _ s bK rsK sK hm hr0 hh1 hc1 hh2 hc2 EK). }
    destruct hK' as [(Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1) hcK].
    destruct (cbn_grq_cons_inv_skel _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA & hsk1).
    destruct (cbn_gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (cbn_grq_cons_inv_skel _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB & hsk2).
    destruct (cbn_gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbn in hsk1, hsk2. injection hsk1 as hsk1. injection hsk2 as hsk2.
    pose proof (cbn_spine_reads Q Q1 G G1 _ v1' H1 T1 hk1 hsk1 hw1 hT1) as hT1'.
    pose proof (cbn_spine_reads Q Q1 G G1 _ v2' H2 T2 hk2 hsk2 hw2 hT2) as hT2'.
    pose proof (hk1 _ hw1) as hw1''. pose proof (hk2 _ hw2) as hw2''.
    destruct v1' as [| | | | | |e1' c1' sp1']; cbv beta iota in he; try discriminate he.
    destruct v2' as [| | | | | |e2' c2' sp2']; cbv beta iota in he; try discriminate he.
    cbn [cbn_spine_of] in hT1', hT2'.
    pose proof (Forall_inv_tail (Forall_inv_tail hr1)) as hrB.
    destruct bK.
    - destruct (hC L Q1 lo1 G1 sp1' sp2' _ _ rsB sK b rs' s' hm1 hrB hT1' hT2' he) as [hp hc].
      split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cbn_lift_conv_mkApps L Q pb H1 H2 T1 T2 hL (hcK eq_refl)).
      exact (cbn_lift_conv_s_lift _ _ _ _ _ hLQ hq1 (hc hb)).
    - pose proof (cbn_g_value_VStuck_cok _ _ _ _ _ _ _ hw1'') as hc1'.
      pose proof (cbn_g_value_VStuck_cok _ _ _ _ _ _ _ hw2'') as hc2'.
      apply cbn_g_value_VStuck_inv in hw1'' as (H1' & T1' & hh1' & hT1'' & eh1).
      apply cbn_g_value_VStuck_inv in hw2'' as (H2' & T2' & hh2' & hT2'' & eh2).
      rewrite lift_mkApps in eh1, eh2.
      assert (hl1 : #|map (lift0 (Q1 - Q)) T1| = #|T1'|).
      { rewrite (cbn_g_addrs_length _ _ _ hT1'), (cbn_g_addrs_length _ _ _ hT1''). reflexivity. }
      assert (hl2 : #|map (lift0 (Q1 - Q)) T2| = #|T2'|).
      { rewrite (cbn_g_addrs_length _ _ _ hT2'), (cbn_g_addrs_length _ _ _ hT2''). reflexivity. }
      destruct (cbn_mkApps_inj_len _ _ _ _ hl1 eh1) as [<- _].
      destruct (cbn_mkApps_inj_len _ _ _ _ hl2 eh2) as [<- _].
      pose proof hm1 as [_ _ hok1 _].
      pose proof (cbn_gok_codes_hyg X_type X Γ nctx Σ _ Q1 lo1 G1 sK hok1 hhyg) as hch1.
      destruct (cbn_head_rb_g k hC L Q1 lo1 G1 pb e1' _ e2' _ sp1' sp2' _ _ _ _ rsB sK b rs' s'
                  hm1 hrB (hch1 _ hc1') (hch1 _ hc2') hh1' hh2' hT1' hT2' he) as [hp hc].
      split; [exact (cbn_post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cbn_lift_conv_lift L Q Q1 pb _ _ hLQ hq1).
      rewrite !lift_mkApps. exact (hc hb).
  Qed.

  (** *** All the rows *)

  Local Ltac cbn_rows_false hm hr he :=
    match type of he with
    | cbn_conv_rows ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 = _ =>
      change (cbn_conv_rows a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) with
        (CbnCOk (false, a10, a11)) in he
    end;
    injection he as <- <- <-;
    split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb].

  Lemma cbn_conv_rows_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_cells (k tt) -> cbn_spec_term (k tt) -> cbn_spec_case (k tt) ->
      cbn_spec_rows (CbnFS k).
  Proof.
    intros hC hT hK L Q lo G pb v1 v2 w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he.
    destruct v1 as [h1 sp1|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|[l1|h1] sp1|e1 c1|e1 c1 sp1];
    destruct v2 as [h2 sp2|e2 c2|e2 c2 i2 sp2|e2 c2 i2 sp2|[l2|h2] sp2|e2 c2|e2 c2 sp2];
      try (cbn_rows_false hm hr he).
    - refine (cbn_conv_rows_con_g k hC L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
      hw1 hw2 he).
      do 4 eexists. repeat split.
    - destruct c1 as [ci1 cp1 ct1], c2 as [ci2 cp2 ct2].
      destruct ct1; try (cbn_rows_false hm hr he).
      destruct ct2; try (cbn_rows_false hm hr he).
      refine (cbn_conv_rows_lam_g k hT L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
        hw1 hw2 he).
      do 10 eexists. repeat split.
    - rewrite cbn_conv_rows_fix_eq in he.
      pose proof hw1 as hf1. apply cbn_g_value_VFix_inv in hf1.
      pose proof hw2 as hf2. apply cbn_g_value_VFix_inv in hf2.
      exact (cbn_fix_rows_core k hC L Q lo G pb e1 c1 i1 sp1 e2 c2 i2 sp2 w1 w2 rs s b rs' s'
               hm hr hf1 hf2 he).
    - rewrite cbn_conv_rows_sfix_eq in he.
      pose proof hw1 as hf1. apply cbn_g_value_VStuckFix_inv in hf1.
      pose proof hw2 as hf2. apply cbn_g_value_VStuckFix_inv in hf2.
      exact (cbn_fix_rows_core k hC L Q lo G pb e1 c1 i1 sp1 e2 c2 i2 sp2 w1 w2 rs s b rs' s'
               hm hr hf1 hf2 he).
    - refine (cbn_conv_rows_var_g k hC L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
      hw1 hw2 he).
      do 4 eexists. repeat split.
    - refine (cbn_conv_rows_const_g k hC L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
      hw1 hw2 he).
      do 4 eexists. repeat split.
    - destruct c1 as [ci1 cp1 ct1], c2 as [ci2 cp2 ct2].
      destruct ct1; try (cbn_rows_false hm hr he).
      all: destruct ct2; try (cbn_rows_false hm hr he).
      + refine (cbn_conv_rows_sort_g k L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
        hw1 hw2 he).
        do 6 eexists. repeat split.
      + refine (cbn_conv_rows_prod_g k hT L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
        hw1 hw2 he).
        do 10 eexists. repeat split.
      + refine (cbn_conv_rows_prim_g k L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
        hw1 hw2 he).
        do 6 eexists. repeat split.
    - refine (cbn_conv_rows_stuck_g k hC hK L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2
      hw1 hw2 he).
      do 6 eexists. repeat split.
  Qed.

  (** ** The stuck-match rule: the whole rule

    [cbn_case_cong] compares the parameters ([cbn_case_params]), the return clauses under
    [#|pcontext|] fresh variables ([cbn_fresh_tail]), the scrutinees, and the branches
    ([cbn_case_branches]). [cbn_case_lift_conv] is the conversion: two [tCase] readings whose
    components agree in the sense of [cbn_lift_conv_s], [cbn_lift_conv_b] and [cbn_lift_conv] are
    convertible ([cbn_ws_cumul_pb_tCase]). *)

  Lemma cbn_pcodes_of_case G c ci p sc brs :
    cbn_gcok G c -> c.(cbn_c_term) = tCase ci p sc brs -> cbn_pcodes G c 0 p.(pparams).
  Proof.
    intros hc ht.
    assert (h : forall l i, (forall j t, nth_error l j = Some t ->
                  nth_error p.(pparams) (N.to_nat i + j) = Some t) -> cbn_pcodes G c i l).
    { induction l as [|t l ih]; intros i hl; constructor.
      - apply cbn_cok_child; [exact hc|rewrite ht]. apply cbn_cs_case_param.
        rewrite <- (Nat.add_0_r (N.to_nat i)). exact (hl 0 t eq_refl).
      - apply ih. intros j u hu. replace (N.to_nat (N.succ i)) with (S (N.to_nat i)) by lia.
        replace (S (N.to_nat i) + j) with (N.to_nat i + S j) by lia. exact (hl (S j) u hu). }
    apply h. intros j t hj. exact hj.
  Qed.

  Lemma cbn_bcodes_of_case G c ci p sc brs :
    cbn_gcok G c -> c.(cbn_c_term) = tCase ci p sc brs -> cbn_bcodes G c 0 brs.
  Proof.
    intros hc ht.
    assert (h : forall l i, (forall j br, nth_error l j = Some br ->
                  nth_error brs (N.to_nat i + j) = Some br) -> cbn_bcodes G c i l).
    { induction l as [|br l ih]; intros i hl; constructor.
      - apply cbn_cok_child; [exact hc|rewrite ht]. apply cbn_cs_case_branch.
        rewrite <- (Nat.add_0_r (N.to_nat i)). exact (hl 0 br eq_refl).
      - apply ih. intros j u hu. replace (N.to_nat (N.succ i)) with (S (N.to_nat i)) by lia.
        replace (S (N.to_nat i) + j) with (N.to_nat i + S j) by lia. exact (hl (S j) u hu). }
    apply h. intros j br hj. exact hj.
  Qed.

  Lemma cbn_susps_of_slots Q G e ts l :
    cbn_g_slots nctx Q G e.(cbn_ev_vals) ts -> e.(cbn_ev_nvals) = #|e.(cbn_ev_vals)| ->
    Forall2 (cbn_g_susp nctx Q G e) l
      (map (fun t => subst ts 0 (lift (Q - nctx + e.(cbn_ev_goff)) #|ts| t)) l).
  Proof.
    intros hs hn. pose proof (cbn_g_slots_length _ _ _ _ _ hs) as hl.
    induction l as [|t l ih]; constructor; [|exact ih].
    replace #|ts| with e.(cbn_ev_nvals) by lia. exact (cbn_g_susp_of_slots _ _ _ e t ts hs hn).
  Qed.

  Lemma cbn_lift_body0 d ts N t :
    subst (map (lift0 d) ts) 0 (lift (d + N) #|ts| t) = lift0 d (subst ts 0 (lift N #|ts| t)).
  Proof. exact (cbn_lift_bodyk d ts N #|ts| 0 t eq_refl). Qed.

  Lemma cbn_lift0_tCase_inv m ci p c brs u :
    tCase ci p c brs = lift0 m u ->
    exists p' c' brs', u = tCase ci p' c' brs'
      /\ p.(pparams) = map (lift0 m) p'.(pparams) /\ p.(puinst) = p'.(puinst)
      /\ p.(pcontext) = p'.(pcontext)
      /\ p.(preturn) = lift m #|p'.(pcontext)| p'.(preturn)
      /\ c = lift0 m c'
      /\ Forall2 (fun br br' => br.(bcontext) = br'.(bcontext)
                  /\ br.(bbody) = lift m #|br'.(bcontext)| br'.(bbody)) brs brs'.
  Proof.
    intros e. destruct u as [| | | | | | | | | | |ci' p' c' brs'| | | |]; cbn in e;
      try discriminate e.
    injection e as -> -> -> ->.
    exists p', c', brs'. split; [reflexivity|].
    cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite Nat.add_0_r; reflexivity|]. split; [reflexivity|].
    induction brs' as [|br brs ih]; cbn; constructor; [|exact ih].
    cbn. split; [reflexivity|]. rewrite Nat.add_0_r. reflexivity.
  Qed.

  Lemma cbn_open_scl (Ξ : context) L t : #|Ξ| = L -> is_open_term Ξ t -> cbn_scl L t.
  Proof. intros <- h. exact h. Qed.

  Lemma cbn_case_brs_cv L Q Δ (q1 : predicate term) ts1 ts2 N1 N2 brs1 brs2 bs1 bs2 :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    forallb (is_open_term (Γ ,,, Δ)) q1.(pparams) ->
    Forall2 (fun br1 br2 => cbn_case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cbn_lift_conv_b L Q #|br1.(bcontext)| Conv (cbn_rbody ts1 N1 br1) (cbn_rbody ts2 N2 br2))
        brs1 brs2 ->
    Forall2 (fun br br' => br.(bcontext) = br'.(bcontext)
               /\ br.(bbody) = lift (Q - L) #|br'.(bcontext)| br'.(bbody))
      (map (cbn_rd_br ts1 N1) brs1) bs1 ->
    Forall2 (fun br br' => br.(bcontext) = br'.(bcontext)
               /\ br.(bbody) = lift (Q - L) #|br'.(bcontext)| br'.(bbody))
      (map (cbn_rd_br ts2 N2) brs2) bs2 ->
    Forall (fun br => on_free_vars_ctx (closedP #|q1.(pparams)| cbn_xpredT) br.(bcontext)
              /\ on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Γ ,,, Δ| cbn_xpred0)) br.(bbody))
      bs1 ->
    Forall (fun br => on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Γ ,,, Δ| cbn_xpred0))
                        br.(bbody)) bs2 ->
    ∥ All2 (fun br br' => eq_context_upto_names br.(bcontext) br'.(bcontext)
              × Σ ;;; (Γ ,,, Δ) ,,, inst_case_branch_context q1 br ⊢ br.(bbody) = br'.(bbody))
        bs1 bs2 ∥.
  Proof.
    intros hL hΔ hcl hop hbrs. revert bs1 bs2.
    induction hbrs as [|br1 br2 l1 l2 [hc hq] _ ih]; intros bs1 bs2 hi1 hi2 hf1 hf2.
    - inversion hi1; subst. inversion hi2; subst. constructor. constructor.
    - cbn [map] in hi1, hi2.
      inversion hi1 as [|? b1 ? m1 [ec1 eb1] hi1']; subst.
      inversion hi2 as [|? b2 ? m2 [ec2 eb2] hi2']; subst.
      inversion hf1 as [|? ? [hfc1 hfb1] hf1']; subst.
      inversion hf2 as [|? ? hfb2 hf2']; subst.
      destruct (ih _ _ hi1' hi2' hf1' hf2') as [hall].
      cbn [cbn_rd_br bcontext bbody] in ec1, eb1, ec2, eb2.
      destruct (cbn_case_ctx_ok_spec _ _ hc) as [hx _ _]. pose proof (All2_length hx) as hk.
      unfold cbn_rbody in hq.
      assert (e1' : subst ts1 #|bcontext br1| (lift N1 (#|bcontext br1| + #|ts1|) (bbody br1))
                    = lift (Q - L) #|bcontext br1| (bbody b1))
        by (rewrite eb1, <- ec1; reflexivity).
      assert (e2' : subst ts2 #|bcontext br2| (lift N2 (#|bcontext br2| + #|ts2|) (bbody br2))
                    = lift (Q - L) #|bcontext br1| (bbody b2))
        by (rewrite eb2, <- ec2, <- hk; reflexivity).
      assert (hΞ : #|Γ ,,, Δ| = L) by (rewrite app_context_length, hΔ, <- hnctx; lia).
      rewrite hΞ, <- ec1 in hfb1. rewrite hΞ, <- ec2, <- hk in hfb2.
      assert (hlen : #|Δ ,,, inst_case_branch_context q1 b1| = L + #|bcontext br1| - nctx).
      { rewrite app_context_length, inst_case_branch_context_length, <- ec1. lia. }
      assert (hclo : is_closed_context (Γ ,,, (Δ ,,, inst_case_branch_context q1 b1))).
      { rewrite app_context_assoc.
        exact (PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context cbn_xpred0 (Γ ,,, Δ) _ _ _
                 hop hfc1 hcl). }
      destruct (hq _ _ e1' e2' (cbn_scl_binder_n L _ _ hfb1) (cbn_scl_binder_n L _ _ hfb2)
        _ hlen hclo)
        as [hcv].
      rewrite app_context_assoc in hcv.
      constructor. constructor; [|exact hall]. split; [|exact hcv].
      rewrite <- ec1, <- ec2. exact hx.
  Qed.

  Lemma cbn_case_lift_conv L Q pb ci p1 p2 sc1 sc2 brs1 brs2 ts1 ts2 N1 N2 :
    nctx <= L -> L <= Q ->
    forallb2 (cbn_cmp_level_conv X_type X) p1.(puinst) p2.(puinst) = true ->
    cbn_case_ctx_ok p1.(pcontext) p2.(pcontext) = true ->
    cbn_lift_conv_s L Q (map (fun t => subst ts1 0 (lift N1 #|ts1| t)) p1.(pparams))
            (map (fun t => subst ts2 0 (lift N2 #|ts2| t)) p2.(pparams)) ->
    cbn_lift_conv_b L Q #|p1.(pcontext)| Conv
      (subst ts1 #|p1.(pcontext)| (lift N1 (#|p1.(pcontext)| + #|ts1|) p1.(preturn)))
      (subst ts2 #|p1.(pcontext)| (lift N2 (#|p1.(pcontext)| + #|ts2|) p2.(preturn))) ->
    cbn_lift_conv L Q Conv (subst ts1 0 (lift N1 #|ts1| sc1)) (subst ts2 0 (lift N2 #|ts2| sc2)) ->
    Forall2 (fun br1 br2 => cbn_case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cbn_lift_conv_b L Q #|br1.(bcontext)| Conv (cbn_rbody ts1 N1 br1) (cbn_rbody ts2 N2 br2))
        brs1 brs2 ->
    cbn_lift_conv L Q pb (subst ts1 0 (lift N1 #|ts1| (tCase ci p1 sc1 brs1)))
              (subst ts2 0 (lift N2 #|ts2| (tCase ci p2 sc2 brs2))).
  Proof.
    intros hL hLQ Einst Ectx hpar hret hsc hbrs u1 u2 e1 e2 s1 s2 Δ hΔ hcl.
    rewrite cbn_rsusp_case in e1, e2.
    destruct (cbn_lift0_tCase_inv _ _ _ _ _ _ e1)
      as (q1 & d1 & bs1 & -> & ep1 & ei1 & ec1 & er1 & ed1 & eb1).
    destruct (cbn_lift0_tCase_inv _ _ _ _ _ _ e2)
      as (q2 & d2 & bs2 & -> & ep2 & ei2 & ec2 & er2 & ed2 & eb2).
    cbn [cbn_rd_pred pparams puinst pcontext preturn] in ep1, ei1, ec1, er1, ep2, ei2, ec2, er2.
    assert (hΞ : #|Γ ,,, Δ| = L) by (rewrite app_context_length, hΔ, <- hnctx; lia).
    pose proof (cbn_scl_open L Δ _ hL hΔ s1) as ho1.
    pose proof (cbn_scl_open L Δ _ hL hΔ s2) as ho2.
    destruct (cbn_open_case_inv _ _ _ _ _ ho1) as (hop1 & hor1 & hoc1 & hos1 & hob1).
    destruct (cbn_open_case_inv _ _ _ _ _ ho2) as (hop2 & hor2 & hoc2 & hos2 & hob2).
    destruct (cbn_case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
    pose proof (All2_length hctx) as hn12.
    (* parameters *)
    assert (sp1 : forallb (cbn_scl L) (pparams q1)) by (rewrite <- hΞ; exact hop1).
    assert (sp2 : forallb (cbn_scl L) (pparams q2)) by (rewrite <- hΞ; exact hop2).
    destruct (hpar _ _ ep1 ep2 sp1 sp2 Δ hΔ hcl) as [hpars].
    (* return clauses *)
    assert (er1' : subst ts1 #|pcontext p1| (lift N1 (#|pcontext p1| + #|ts1|) (preturn p1))
                   = lift (Q - L) #|pcontext p1| (preturn q1)) by
                     (rewrite er1, <- ec1; reflexivity).
    assert (er2' : subst ts2 #|pcontext p1| (lift N2 (#|pcontext p1| + #|ts2|) (preturn p2))
                   = lift (Q - L) #|pcontext p1| (preturn q2))
      by (rewrite hn12, er2, <- ec2; reflexivity).
    rewrite hΞ, <- ec1 in hor1. rewrite hΞ, <- ec2, <- hn12 in hor2.
    assert (hlenR : #|Δ ,,, inst_case_predicate_context q1| = L + #|pcontext p1| - nctx).
    { rewrite app_context_length, inst_case_predicate_context_length, <- ec1. lia. }
    assert (hcloR : is_closed_context (Γ ,,, (Δ ,,, inst_case_predicate_context q1))).
    { rewrite app_context_assoc.
      exact (PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context cbn_xpred0 (Γ ,,, Δ) _ _ _
               hop1 hoc1 hcl). }
    destruct (hret _ _ er1' er2' (cbn_scl_binder_n L _ _ hor1) (cbn_scl_binder_n L _ _ hor2) _
                hlenR hcloR) as [hR].
    rewrite app_context_assoc in hR.
    (* scrutinees *)
    destruct (hsc _ _ ed1 ed2 (cbn_open_scl _ _ _ hΞ hos1) (cbn_open_scl _ _ _ hΞ hos2) Δ hΔ hcl)
      as [hS].
    (* branches *)
    destruct (cbn_case_brs_cv L Q Δ q1 ts1 ts2 N1 N2 brs1 brs2 bs1 bs2 hL hΔ hcl hop1 hbrs eb1 eb2
                hob1 (Forall_impl hob2 (fun br h => proj2 h))) as [hB].
    constructor.
    apply (cbn_ws_cumul_pb_tCase (wfΣ := wfΣ) ho1 ho2 hpars).
    - rewrite <- ei1, <- ei2. exact (cbn_cmp_level_conv_instance X_type X Σ hΣ _ _ Einst).
    - rewrite <- ec1, <- ec2. exact hctx.
    - exact hR.
    - exact hS.
    - exact hB.
  Qed.

  (** [cbn_push_fresh n] fresh variables on both environments, then the two codes at [L + n]. *)
  Definition cbn_fresh_tail (d : cbn_fuel) (n L : nat) (e1 e2 : cbn_env) (cb1 cb2 : cbn_code)
      (rs : list cbn_root) (s : cbn_state) :=
    match cbn_push_fresh n L e1 e2 (CbnRE e1 :: CbnRE e2 :: rs) s with
    | CbnCOk (r, rs, s) =>
      let '(lvlr, er1, er2) := r in
      cbn_conv_term X_type X Γ nctx d lvlr Conv er1 cb1 er2 cb2 rs s
    | CbnCFail w => CbnCFail w
    end.

  Lemma cbn_fresh_tail_g (k : unit -> cbn_fuel) (hT : cbn_spec_term (k tt))
      L Q lo G n e1 e2 cb1 cb2 ts1 ts2 rs s b rs' s' :
    cbn_MI L Q lo G s -> Forall (cbn_rwf Q) rs ->
    cbn_g_slots nctx Q G e1.(cbn_ev_vals) ts1 -> e1.(cbn_ev_nvals) = #|e1.(cbn_ev_vals)| ->
    cbn_g_slots nctx Q G e2.(cbn_ev_vals) ts2 -> e2.(cbn_ev_nvals) = #|e2.(cbn_ev_vals)| ->
    cbn_gcok G cb1 -> cbn_gcok G cb2 ->
    cbn_fresh_tail (k tt) n L e1 e2 cb1 cb2 rs s = CbnCOk (b, rs', s') ->
    cbn_post L Q G (CbnRE e1 :: CbnRE e2 :: rs) s' rs' /\
    (b = true -> cbn_lift_conv_b L Q n Conv
       (subst ts1 n (lift (Q - nctx + e1.(cbn_ev_goff)) (n + #|ts1|) cb1.(cbn_c_term)))
       (subst ts2 n (lift (Q - nctx + e2.(cbn_ev_goff)) (n + #|ts2|) cb2.(cbn_c_term)))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hc1 hc2 he.
    pose proof hm as [hL hLQ _ _].
    assert (hr0 : Forall (cbn_rwf Q) (CbnRE e1 :: CbnRE e2 :: rs))
      by (constructor; [exact I|constructor; [exact I|exact hr]]).
    pose proof (cbn_minv_raise L Q n lo G s hm) as hmR.
    pose proof (cbn_rwfs_mono Q (Q + n) _ ltac:(lia) hr0) as hrR.
    pose proof (cbn_grq_raise Q n G _ ltac:(lia) hr0) as hgR.
    pose proof (proj2 (cbn_g_slot_shift nctx Q n ltac:(lia) G) _ _ hs1) as [hs1R _].
    pose proof (proj2 (cbn_g_slot_shift nctx Q n ltac:(lia) G) _ _ hs2) as [hs2R _].
    unfold cbn_fresh_tail in he.
    destruct (cbn_push_fresh n L e1 e2 (CbnRE e1 :: CbnRE e2 :: rs) s)
      as [[[r rsP] sP]|w] eqn:EP; [|discriminate he].
    destruct (cbn_push_fresh_g n L (Q + n) lo (cbn_gshift n G) L e1 e2 _ _ _ s r rsP sP hmR hrR
                ltac:(lia) hs1R hn1 hs2R hn2 EP)
      as (loP & GP & f1 & f2 & -> & hmP & hrP & hgP & hnf1 & hgf1 & hnf2 & hgf2 & hf1 & hf2).
    pose proof (cbn_push_fresh_skel _ _ _ _ _ _ _ _ _ EP) as hkP.
    cbv beta iota in he.
    pose proof (cbn_g_susp_of_slots nctx _ GP f1 cb1.(cbn_c_term) _ hf1 hnf1) as hB1.
    pose proof (cbn_g_susp_of_slots nctx _ GP f2 cb2.(cbn_c_term) _ hf2 hnf2) as hB2.
    destruct (hT (L + n) (Q + n) loP GP Conv f1 cb1 f2 cb2 _ _ rsP sP b rs' s'
                (cbn_minv_level L (L + n) (Q + n) loP GP sP hmP ltac:(lia) ltac:(lia)) hrP hB1
                (cbn_cok_gcx _ _ (proj1 hgP) _ hc1) hB2 (cbn_cok_gcx _ _ (proj1 hgP) _ hc2) he)
      as [hpC hcC].
    split.
    - apply (cbn_post_compose L Q (Q + n) G (cbn_gshift n G) _ _ s' rs' ltac:(lia) hgR).
      apply (cbn_post_compose L _ _ _ GP _ rsP s' rs' (le_n _) (cbn_grq_of_gren _ _ _ _ _ hgP hkP)).
      exact (cbn_post_level L (L + n) (Q + n) GP rsP s' rs' hL ltac:(lia) hpC).
    - intros hb U1 U2 eU1 eU2 sU1 sU2.
      apply (hcC hb U1 U2); [| |exact sU1|exact sU2].
      + replace (Q + n - (L + n)) with (Q - L) by lia.
        rewrite hgf1, hnf1.
        pose proof (cbn_g_slots_length _ _ _ _ _ hf1) as hlf.
        rewrite length_app, length_map, idsn_length, length_map in hlf.
        rewrite <- hlf.
        replace (Q + n - nctx + cbn_ev_goff e1) with (n + (Q - nctx + cbn_ev_goff e1)) by lia.
        replace (Q + n - (L + n)) with (Q - L) by lia.
        apply cbn_fresh_branch_read; [lia|]. exact eU1.
      + replace (Q + n - (L + n)) with (Q - L) by lia.
        rewrite hgf2, hnf2.
        pose proof (cbn_g_slots_length _ _ _ _ _ hf2) as hlf.
        rewrite length_app, length_map, idsn_length, length_map in hlf.
        rewrite <- hlf.
        replace (Q + n - nctx + cbn_ev_goff e2) with (n + (Q - nctx + cbn_ev_goff e2)) by lia.
        replace (Q + n - (L + n)) with (Q - L) by lia.
        apply cbn_fresh_branch_read; [lia|]. exact eU2.
  Qed.

  Lemma cbn_case_cong_sound_g (k : unit -> cbn_fuel) :
    cbn_spec_term (k tt) -> cbn_spec_params (k tt) -> cbn_spec_branches (k tt) ->
      cbn_spec_case (CbnFS k).
  Proof.
    intros hT hP hB L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite cbn_case_cong_eq in he.
    destruct (cbn_c_term c1) as [| | | | | | | | | | |ci1 p1 sc1 brs1| | | |] eqn:Ec1;
      try (cbv beta iota in he; injection he as <- <- <-;
           split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]).
    destruct (cbn_c_term c2) as [| | | | | | | | | | |ci2 p2 sc2 brs2| | | |] eqn:Ec2;
      try (cbv beta iota in he; injection he as <- <- <-;
           split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]).
    cbv beta iota in he.
    destruct (cbn_case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|) && (#|pparams p1| == #|pparams p2|)
              && forallb2 (cbn_cmp_level_conv X_type X) (puinst p1) (puinst p2)
              && cbn_case_ctx_ok (pcontext p1) (pcontext p2)) eqn:Etest;
      [|injection he as <- <- <-;
        split; [exact (cbn_post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Etest as [Etest Ectx].
    apply andb_true_iff in Etest as [Etest Einst].
    apply andb_true_iff in Etest as [Etest _].
    apply andb_true_iff in Etest as [Eci _].
    apply cbn_case_info_eqb_eq in Eci. subst ci2.
    destruct (cbn_case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
    pose proof (All2_length hctx) as hn12.
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hs1) as (ts1 & hts1 & hn1 & ->).
    destruct (cbn_g_susp_inv _ _ _ _ _ _ hs2) as (ts2 & hts2 & hn2 & ->).
    pose proof (cbn_g_slots_length _ _ _ _ _ hts1) as hl1.
    pose proof (cbn_g_slots_length _ _ _ _ _ hts2) as hl2.
    assert (hk1 : cbn_ev_nvals e1 = #|ts1|) by lia.
    assert (hk2 : cbn_ev_nvals e2 = #|ts2|) by lia.
    rewrite hk1, hk2.
    (* the parameters *)
    assert (hr0 : Forall (cbn_rwf Q) (CbnRE e1 :: CbnRE e2 :: rs))
      by (constructor; [exact I|constructor; [exact I|exact hr]]).
    destruct (cbn_case_params X_type X Γ nctx (k tt) L e1 c1 e2 c2 0%N
                (pparams p1) (pparams p2) (CbnRE e1 :: CbnRE e2 :: rs) s)
      as [[[bA rsA] sA]|w] eqn:EA; [|discriminate he].
    destruct (hP L Q lo G e1 c1 e2 c2 0%N (pparams p1) (pparams p2) _ _ _ s bA rsA sA hm hr0
                (cbn_pcodes_of_case G c1 ci1 p1 sc1 brs1 hc1 Ec1)
                (cbn_pcodes_of_case G c2 ci1 p2 sc2 brs2 hc2 Ec2)
                (cbn_susps_of_slots Q G e1 ts1 _ hts1 hn1)
                  (cbn_susps_of_slots Q G e2 ts2 _ hts2 hn2) EA)
      as [hpA hcA].
    destruct bA;
      [|cbv beta iota in he; injection he as <- <- <-;
        split; [exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hpA)|intros hb; discriminate hb]].
    destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA) as (qa1 & rsA1 & -> & hqa1 & hgA1).
    destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqa1) as (f1 & -> & hnf1 & hgf1 & hkf1).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgA1) as (qa2 & rsB & -> & hqa2 & hgB).
    destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqa2) as (f2 & -> & hnf2 & hgf2 & hkf2).
    cbv beta iota in he.
    pose proof (hkf1 _ hts1) as hfs1. pose proof (hkf2 _ hts2) as hfs2.
    pose proof (cbn_g_slots_length _ _ _ _ _ hfs1) as hlf1. rewrite length_map in hlf1.
    pose proof (cbn_g_slots_length _ _ _ _ _ hfs2) as hlf2. rewrite length_map in hlf2.
    (* the return clauses *)
    destruct (cbn_push_fresh #|pcontext p1| L f1 f2 (CbnRE f1 :: CbnRE f2 :: rsB) sA)
      as [[[[[lvlr er1] er2] rsP] sP]|w] eqn:EP; [|discriminate he].
    cbv beta iota in he.
    destruct (cbn_conv_term X_type X Γ nctx (k tt) lvlr Conv er1 (cbn_child c1 1 (preturn p1))
                er2 (cbn_child c2 1 (preturn p2)) rsP sP) as [[[bC rsC] sC]|w] eqn:EC;
      [|discriminate he].
    assert (EF : cbn_fresh_tail (k tt) #|pcontext p1| L f1 f2 (cbn_child c1 1 (preturn p1))
                   (cbn_child c2 1 (preturn p2)) rsB sA = CbnCOk (bC, rsC, sC))
      by (unfold cbn_fresh_tail; rewrite EP; exact EC).
    destruct (cbn_fresh_tail_g k hT L QA loA GA #|pcontext p1| f1 f2 _ _ _ _ rsB sA bC rsC sC hmA
                (Forall_inv_tail (Forall_inv_tail hrA)) hfs1 ltac:(lia) hfs2 ltac:(lia)
                (cbn_cok_gcx _ _ (proj1 hgA) _
                   (cbn_cok_child G c1 1 (preturn p1) hc1 ltac:(rewrite Ec1; constructor)))
                (cbn_cok_gcx _ _ (proj1 hgA) _
                   (cbn_cok_child G c2 1 (preturn p2) hc2 ltac:(rewrite Ec2; constructor)))
                EF) as [hpC hcC].
    destruct bC;
      [|cbv beta iota in he; injection he as <- <- <-; split; [|intros hb; discriminate hb];
        apply (cbn_post_compose L Q QA G GA rs rsB _ _ hqA hgB);
        exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hpC)].
    destruct hpC as (QB & loB & GB & hqB & hmB & hrB & hgBB).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgBB) as (qb1 & rsC1 & -> & hqb1 & hgB1).
    destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqb1) as (g1 & -> & hng1 & hgg1 & hkg1).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgB1) as (qb2 & rsC' & -> & hqb2 & hgC).
    destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqb2) as (g2 & -> & hng2 & hgg2 & hkg2).
    cbv beta iota in he.
    pose proof (hkg1 _ hfs1) as hgs1. pose proof (hkg2 _ hfs2) as hgs2.
    rewrite cbn_map_lift0_lift0 in hgs1, hgs2.
    replace (QB - QA + (QA - Q)) with (QB - Q) in hgs1, hgs2 by lia.
    pose proof (cbn_g_slots_length _ _ _ _ _ hgs1) as hlg1. rewrite length_map in hlg1.
    pose proof (cbn_g_slots_length _ _ _ _ _ hgs2) as hlg2. rewrite length_map in hlg2.
    assert (hgcx : cbn_gcx G GB) by (intros i x h; exact (proj1 hgBB _ _ (proj1 hgA _ _ h))).
    (* the scrutinees *)
    destruct (cbn_conv_term X_type X Γ nctx (k tt) L Conv g1 (cbn_child c1 0 sc1)
                g2 (cbn_child c2 0 sc2) (CbnRE g1 :: CbnRE g2 :: rsC') sC)
      as [[[bD rsD] sD]|w] eqn:ED; [|discriminate he].
    assert (hng1' : cbn_ev_nvals g1 = #|cbn_ev_vals g1|) by lia.
    assert (hng2' : cbn_ev_nvals g2 = #|cbn_ev_vals g2|) by lia.
    destruct (hT L QB loB GB Conv g1 (cbn_child c1 0 sc1) g2 (cbn_child c2 0 sc2) _ _ _ sC bD rsD sD
                hmB hrB (cbn_g_susp_of_slots _ _ _ g1 _ _ hgs1 hng1')
                (cbn_cok_gcx _ _ hgcx _ (cbn_cok_child G c1 0 sc1 hc1
                  ltac:(rewrite Ec1; constructor)))
                (cbn_g_susp_of_slots _ _ _ g2 _ _ hgs2 hng2')
                (cbn_cok_gcx _ _ hgcx _ (cbn_cok_child G c2 0 sc2 hc2
                  ltac:(rewrite Ec2; constructor)))
                ED) as [hpD hcD].
    destruct bD;
      [|cbv beta iota in he; injection he as <- <- <-; split; [|intros hb; discriminate hb];
        apply (cbn_post_compose L Q QA G GA rs rsB _ _ hqA hgB);
        apply (cbn_post_compose L QA QB GA GB rsB rsC' _ _ hqB hgC);
        exact (cbn_post_drop2 _ _ _ _ _ _ _ _ hpD)].
    destruct hpD as (QD & loD & GD & hqD & hmD & hrD & hgDD).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgDD) as (qd1 & rsD1 & -> & hqd1 & hgD1).
    destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqd1) as (h1 & -> & hnh1 & hgh1 & hkh1).
    destruct (cbn_grq_cons_inv _ _ _ _ _ _ _ hgD1) as (qd2 & rsD' & -> & hqd2 & hgD).
    destruct (cbn_gpq_RE_inv _ _ _ _ _ _ hqd2) as (h2 & -> & hnh2 & hgh2 & hkh2).
    cbv beta iota in he.
    pose proof (hkh1 _ hgs1) as hhs1. pose proof (hkh2 _ hgs2) as hhs2.
    rewrite cbn_map_lift0_lift0 in hhs1, hhs2.
    replace (QD - QB + (QB - Q)) with (QD - Q) in hhs1, hhs2 by lia.
    pose proof (cbn_g_slots_length _ _ _ _ _ hhs1) as hlh1. rewrite length_map in hlh1.
    pose proof (cbn_g_slots_length _ _ _ _ _ hhs2) as hlh2. rewrite length_map in hlh2.
    assert (hgcx' : cbn_gcx G GD) by (intros i x h; exact (proj1 hgDD _ _ (hgcx _ _ h))).
    (* the branches *)
    destruct (hB L QD loD GD h1 c1 h2 c2 0%N brs1 brs2 _ _ rsD' sD b rs' s' hmD
                (Forall_inv_tail (Forall_inv_tail hrD))
                (cbn_bcodes_of_case GD c1 ci1 p1 sc1 brs1 (cbn_cok_gcx _ _ hgcx' _ hc1) Ec1)
                (cbn_bcodes_of_case GD c2 ci1 p2 sc2 brs2 (cbn_cok_gcx _ _ hgcx' _ hc2) Ec2)
                hhs1 ltac:(lia) hhs2 ltac:(lia) he) as [hpE hcE].
    split.
    - apply (cbn_post_compose L Q QA G GA rs rsB _ _ hqA hgB).
      apply (cbn_post_compose L QA QB GA GB rsB rsC' _ _ hqB hgC).
      exact (cbn_post_compose L QB QD GB GD rsC' rsD' _ _ hqD hgD hpE).
    - intros hb.
      apply (cbn_case_lift_conv L Q pb ci1 p1 p2 sc1 sc2 brs1 brs2 ts1 ts2
               (Q - nctx + cbn_ev_goff e1) (Q - nctx + cbn_ev_goff e2) hL hLQ Einst Ectx).
      + exact (hcA eq_refl).
      + pose proof (hcC eq_refl) as hR. cbn [cbn_child cbn_c_term] in hR.
        rewrite hgf1, hgf2, !length_map in hR.
        replace (QA - nctx + cbn_ev_goff e1) with ((QA - Q) + (Q - nctx + cbn_ev_goff e1))
          in hR by lia.
        replace (QA - nctx + cbn_ev_goff e2) with ((QA - Q) + (Q - nctx + cbn_ev_goff e2))
          in hR by lia.
        rewrite !cbn_lift_bodyk in hR by reflexivity.
        exact (cbn_lift_conv_b_lift L Q QA _ Conv _ _ hLQ hqA hR).
      + pose proof (hcD eq_refl) as hS. cbn [cbn_child cbn_c_term] in hS.
        rewrite hgg1, hgf1, hgg2, hgf2, hng1, hnf1, hng2, hnf2, hk1, hk2 in hS.
        replace (QB - nctx + cbn_ev_goff e1) with ((QB - Q) + (Q - nctx + cbn_ev_goff e1))
          in hS by lia.
        replace (QB - nctx + cbn_ev_goff e2) with ((QB - Q) + (Q - nctx + cbn_ev_goff e2))
          in hS by lia.
        rewrite !cbn_lift_body0 in hS.
        exact (cbn_lift_conv_lift L Q QB Conv _ _ hLQ ltac:(lia) hS).
      + pose proof (hcE hb) as hc.
        rewrite hgh1, hgg1, hgf1, hgh2, hgg2, hgf2 in hc.
        replace (QD - nctx + cbn_ev_goff e1) with ((QD - Q) + (Q - nctx + cbn_ev_goff e1))
          in hc by lia.
        replace (QD - nctx + cbn_ev_goff e2) with ((QD - Q) + (Q - nctx + cbn_ev_goff e2))
          in hc by lia.
        exact (cbn_branches_lift L Q QD ts1 ts2 _ _ brs1 brs2 hLQ ltac:(lia) hc).
  Qed.

  (** ** The induction *)

  Lemma cbn_spec_all_step (k : unit -> cbn_fuel) : cbn_spec_all (k tt) -> cbn_spec_all (CbnFS k).
  Proof.
    intros (hS & hE & hC & hT & hM & hSC & hK & hP & hB & hR & hV).
    split; [exact (cbn_conv_slot_sound_g k hE hM)|].
    split; [exact (cbn_conv_eval_sound_g k hV)|].
    split; [exact (cbn_conv_cells_sound_g k hS hC)|].
    split; [exact (cbn_conv_term_sound_g k hV)|].
    split; [exact (cbn_conv_same_code_sound_g k hSC)|].
    split; [exact (cbn_same_code_cells_sound_g k hS hSC)|].
    split; [exact (cbn_case_cong_sound_g k hT hP hB)|].
    split; [exact (cbn_case_params_sound_g k hT hP)|].
    split; [exact (cbn_case_branches_sound_g k hT hB)|].
    split; [exact (cbn_conv_rows_sound_g k hC hT hK)|].
    exact (cbn_conv_value_sound_g k hM hC hR).
  Qed.

  Lemma cbn_spec_all_ind : forall d, cbn_spec_all d.
  Proof. induction d as [|k ih]; [exact cbn_spec_all_FO|exact (cbn_spec_all_step k (ih tt))]. Qed.

End ConvGhost.

(** * The comparison is sound at every fuel

  [cbn_spec_all_holds] closes [ConvGhost] with its parameters in their declaration order. Its
  hypotheses are the section's: [wf Σ] and [abstract_env_ext_rel X Σ], the context facts
  [hnctx], [hΓ], [hhyg] and [hcio] ([PCUICCallByNeedSoundHookFrame.cbn_eval_section_instance]
  gives them for any well-formed context, and [cbn_w_section] and [cbn_v_section] below at concrete
  ones), and [hrb], the read-back interface [cbn_rb_sound] that
  [PCUICCallByNeedSoundReadBack.cbn_rb_sound_holds] proves from [wf Σ], [hΓ] and [hhyg]. *)
Theorem cbn_spec_all_holds {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) (Σ : global_env_ext)
    (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ)
    (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : cbn_ctx_hyg Γ)
    (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
              PCUICCallByNeedSoundHook.cbn_consts_okb Σ b)
    (hrb : cbn_rb_sound X_type X Γ nctx Σ) :
  forall d, cbn_spec_all X_type X Γ nctx Σ d.
Proof. intros d. eapply cbn_spec_all_ind; eassumption. Qed.

(** * Non-vacuity witnesses for the statements of [ConvGhost]

  Two concrete runs of [cbn_conv_term] at the real fuel [cbn_depth], from the state [cbn_run]
  starts in. Each theorem shows that the premises of [cbn_spec_term] hold at the run's inputs (the
  start state satisfies [cbn_minv], the inputs have readings, their codes are in the ghost's
  table), that the call returns, and that the conclusion holds: the state part [cbn_post] by the
  machine lemma [cbn_whnf_master] and, for the run that answers [true], the conversion part
  [cbn_lift_conv] by hand, not by the fuel induction. The answers and final states are obtained by
  computation. The only hypotheses are [wf Σ] and [abstract_env_ext_rel X Σ]: the start
  invariant is [cbn_run_s2_gok] of [PCUICCallByNeedSoundLevel], the context hypotheses of
  [ConvGhost] hold at both contexts ([cbn_w_section], [cbn_v_section]), and [hrb] follows from them
  by [PCUICCallByNeedSoundReadBack.cbn_rb_sound_holds].
  - [cbn_witness_seam_run]: [x := (fun n : nat => n) O] against [fun n : nat => n], the run
    [PCUICCallByNeedCounterexamples.cbn_term_seam_false] uses. It answers [false], and [cbn_post]
    holds after it.
  - [cbn_witness_true_run]: [x := (fun n : y => n) y] against [y], at [Conv]. It answers [true]
    and [cbn_lift_conv] holds. *)

(** [cbn_at_depth F dflt] runs [F] at the fuel one unit below [cbn_depth]. Stating the machine
  calls of a run this way lets [vm_compute] evaluate them at the real fuel with no equation
  between fuels to prove. *)
#[local] Definition cbn_at_depth {A : Type} (F : cbn_fuel -> A) (dflt : A) : A :=
  match cbn_depth with CbnFS k => F (k tt) | CbnFO => dflt end.

(** The concrete contexts and terms. *)
#[local] Definition cbn_w_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition cbn_w_nat : inductive :=
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
Definition cbn_w_O : term := tConstruct cbn_w_nat 0 [].
Definition cbn_w_body : term := tApp (tLambda cbn_w_na (tInd cbn_w_nat []) (tRel 0)) cbn_w_O.
Definition cbn_w_Γ : context := [vdef cbn_w_na cbn_w_body (tInd cbn_w_nat [])].
Definition cbn_w_t : term := tRel 0.
Definition cbn_w_u : term := tLambda cbn_w_na (tInd cbn_w_nat []) (tRel 0).

Definition cbn_v_Γ : context :=
  [vdef cbn_w_na (tApp (tLambda cbn_w_na (tRel 0) (tRel 0)) (tRel 0)) (tRel 0);
    vass cbn_w_na (tSort sProp)].
#[local] Definition cbn_v_t : term := tRel 0.
#[local] Definition cbn_v_u : term := tRel 1.

Section Witness.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).

  (** A start state of a run that satisfies [cbn_gok] satisfies [cbn_minv] at [L = Q = nctx]. *)
  Lemma cbn_r_minv_start (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|) :
    cbn_gok X_type X Γ nctx Σ [] nctx xH (cbn_run_ghost X_type X t u) (cbn_run_s2 X_type X t u) ->
    cbn_minv X_type X Γ nctx Σ nctx nctx xH (cbn_run_ghost X_type X t u) (cbn_run_s2 X_type X t u).
  Proof.
    intros hok. apply (cbn_minv_start X_type X Γ nctx Σ hnctx xH
      (cbn_run_ghost X_type X t u) _ hok).
    intros a cl h. unfold cbn_heap_get in h. rewrite cbn_run_s2_heap, cbn_bh_get_holes in h.
    discriminate h.
  Qed.

  (** The start state of a run satisfies [cbn_minv] at [L = Q = nctx], from facts about [t]
    and [u] alone. *)
  Lemma cbn_r_minv_start_terms (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|) :
    cbn_consts_okb Σ t -> cbn_consts_okb Σ u -> on_free_vars cbn_xpredT t ->
    on_free_vars cbn_xpredT u ->
    cbn_minv X_type X Γ nctx Σ nctx nctx xH (cbn_run_ghost X_type X t u) (cbn_run_s2 X_type X t u).
  Proof.
    intros ht hu hht hhu.
    exact (cbn_r_minv_start Γ nctx t u hnctx
             (cbn_run_s2_gok X_type X Γ nctx Σ [] nctx t u ht hu hht hhu)).
  Qed.

  (** A run of [cbn_conv_term] at [cbn_depth] from [cbn_run]'s start state, split at its three
    machine calls. *)
  Lemma cbn_r_split (Γ : context) (nctx : nat) (t u : term) (v1 v2 : cbn_value)
      (s1 s2 s3 : cbn_state) (b : bool) :
    cbn_at_depth (fun d => cbn_whnf X_type X Γ nctx d cbn_env_empty (cbn_run_c1 X_type X t) []
                         [CbnRE cbn_env_empty] (cbn_run_s2 X_type X t u)) (CbnCFail CbnWDepth)
      = CbnCOk (v1, [CbnRE cbn_env_empty], s1) ->
    cbn_at_depth (fun d => cbn_whnf X_type X Γ nctx d cbn_env_empty (cbn_run_c2 X_type X t u) []
                         [CbnRV v1] s1) (CbnCFail CbnWDepth)
      = CbnCOk (v2, [CbnRV v1], s2) ->
    cbn_at_depth (fun d => cbn_conv_value X_type X Γ nctx d nctx Conv v1 v2 [] s2)
      (CbnCFail CbnWDepth)
      = CbnCOk (b, [], s3) ->
    cbn_conv_term X_type X Γ nctx cbn_depth nctx Conv cbn_env_empty (cbn_run_c1 X_type X t)
      cbn_env_empty (cbn_run_c2 X_type X t u) [] (cbn_run_s2 X_type X t u) = CbnCOk (b, [], s3)
    /\ exists d,
         cbn_whnf X_type X Γ nctx d cbn_env_empty (cbn_run_c1 X_type X t) [] [CbnRE cbn_env_empty]
           (cbn_run_s2 X_type X t u) = CbnCOk (v1, [CbnRE cbn_env_empty], s1)
         /\ cbn_whnf X_type X Γ nctx d cbn_env_empty (cbn_run_c2 X_type X t u) [] [CbnRV v1] s1
              = CbnCOk (v2, [CbnRV v1], s2).
  Proof.
    unfold cbn_at_depth. destruct cbn_depth as [|k]; intros E1 E2 E3; [discriminate E1|].
    cbv beta in E1, E2, E3.
    split; [|exists (k tt); split; assumption].
    rewrite cbn_conv_term_eq, E1. cbv beta iota. rewrite E2. cbv beta iota. exact E3.
  Qed.

  (** The state part: [cbn_post] holds after the two [cbn_whnf] calls and the [cbn_tick] of
    [cbn_conv_value], by [cbn_whnf_master]. *)
  Lemma cbn_r_post (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|)
      (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                PCUICCallByNeedSoundHook.cbn_consts_okb Σ b)
      (d : cbn_fuel) (v1 v2 : cbn_value) (s1 s2 s3 : cbn_state) :
    cbn_minv X_type X Γ nctx Σ nctx nctx xH (cbn_run_ghost X_type X t u)
      (cbn_run_s2 X_type X t u) ->
    cbn_whnf X_type X Γ nctx d cbn_env_empty (cbn_run_c1 X_type X t) [] [CbnRE cbn_env_empty]
      (cbn_run_s2 X_type X t u) = CbnCOk (v1, [CbnRE cbn_env_empty], s1) ->
    cbn_whnf X_type X Γ nctx d cbn_env_empty (cbn_run_c2 X_type X t u) [] [CbnRV v1] s1
      = CbnCOk (v2, [CbnRV v1], s2) ->
    cbn_tick s2 = Some s3 ->
    cbn_post X_type X Γ nctx Σ nctx nctx (cbn_run_ghost X_type X t u) [] s3 [].
  Proof.
    intros hm0 E1 E2 E3.
    destruct (cbn_whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio d nctx nctx xH
                (cbn_run_ghost X_type X t u) cbn_env_empty (cbn_run_c1 X_type X t) [] [] t
                  [CbnRE cbn_env_empty]
                (cbn_run_s2 X_type X t u) v1 [CbnRE cbn_env_empty] s1 hm0
                (Forall_cons (CbnRE cbn_env_empty) I (Forall_nil _))
                  (cbn_run_c1_g_susp X_type X nctx t u)
                (cbn_run_c1_gcok X_type X t u) (cbn_g_slots_nil nctx nctx _) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & _ & _).
    assert (hs2 : cbn_g_susp nctx nctx G1 cbn_env_empty (cbn_run_c2 X_type X t u).(cbn_c_term) u).
    { rewrite cbn_run_c2_term. apply cbn_g_susp_env_empty. }
    destruct (cbn_whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio d nctx nctx lo1 G1
                cbn_env_empty (cbn_run_c2 X_type X t u) [] [] u [CbnRV v1] s1 v2 [CbnRV v1] s2 hm1
                (Forall_cons (CbnRV v1) hv1 (Forall_inv_tail hr1)) hs2
                (cbn_cok_gcx _ _ (proj1 hg1) _ (cbn_run_c2_gcok X_type X t u))
                (cbn_g_slots_nil nctx nctx _) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & _ & _).
    exists nctx, lo2, G2. split; [lia|].
    split; [exact (cbn_minv_tick X_type X Γ nctx Σ _ _ _ _ _ _ E3 hm2)|].
    split; [constructor|]. split; [|split; [constructor|reflexivity]].
    intros i e hi. exact (proj1 hg2 _ _ (proj1 hg1 _ _ hi)).
  Qed.

  (** ** A run that answers [false], and [cbn_post] holds after it *)

  #[local] Definition cbn_w_G0 : cbn_ghost := cbn_run_ghost X_type X cbn_w_t cbn_w_u.

  (** The section hypotheses of [ConvGhost] at [cbn_w_Γ]. *)
  Lemma cbn_w_section :
    1 = #|cbn_w_Γ| /\ is_closed_context cbn_w_Γ /\ cbn_ctx_hyg cbn_w_Γ
    /\ (forall j decl b, nth_error cbn_w_Γ j = Some decl -> decl.(decl_body) = Some b ->
          PCUICCallByNeedSoundHook.cbn_consts_okb Σ b).
  Proof.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros [|j] decl b hj hb; [|destruct j; discriminate hj].
      injection hj as <-. injection hb as <-. reflexivity.
    - intros [|j] decl b hj hb; [|destruct j; discriminate hj].
      injection hj as <-. injection hb as <-. reflexivity.
  Qed.

  #[local] Definition cbn_w_R1 :=
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_w_Γ 1 d cbn_env_empty
      (cbn_run_c1 X_type X cbn_w_t) []
                         [CbnRE cbn_env_empty] (cbn_run_s2 X_type X cbn_w_t cbn_w_u))
                           (CbnCFail CbnWDepth).
  #[local] Definition cbn_w_s1 : cbn_state := match cbn_w_R1 with CbnCOk (_, _, s) =>
    s | CbnCFail _ => cbn_init end.
  #[local] Definition cbn_w_R2 :=
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_w_Γ 1 d cbn_env_empty
      (cbn_run_c2 X_type X cbn_w_t cbn_w_u) []
                         [CbnRV (CbnVCon cbn_w_O [])] cbn_w_s1) (CbnCFail CbnWDepth).
  #[local] Definition cbn_w_v2 : cbn_value := match cbn_w_R2 with CbnCOk (v, _, _) =>
    v | CbnCFail _ => CbnVCon cbn_w_O [] end.
  #[local] Definition cbn_w_s2 : cbn_state := match cbn_w_R2 with CbnCOk (_, _, s) =>
    s | CbnCFail _ => cbn_init end.
  #[local] Definition cbn_w_s3 : cbn_state := match cbn_tick cbn_w_s2 with Some s => s | None =>
    cbn_init end.

  #[local] Lemma cbn_w_E1 :
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_w_Γ 1 d cbn_env_empty
      (cbn_run_c1 X_type X cbn_w_t) []
                         [CbnRE cbn_env_empty] (cbn_run_s2 X_type X cbn_w_t cbn_w_u))
                           (CbnCFail CbnWDepth)
    = CbnCOk (CbnVCon cbn_w_O [], [CbnRE cbn_env_empty], cbn_w_s1).
  Proof. vm_compute. reflexivity. Qed.

  #[local] Lemma cbn_w_E2 :
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_w_Γ 1 d cbn_env_empty
      (cbn_run_c2 X_type X cbn_w_t cbn_w_u) []
                         [CbnRV (CbnVCon cbn_w_O [])] cbn_w_s1) (CbnCFail CbnWDepth)
    = CbnCOk (cbn_w_v2, [CbnRV (CbnVCon cbn_w_O [])], cbn_w_s2).
  Proof. vm_compute. reflexivity. Qed.

  #[local] Lemma cbn_w_E3 :
    cbn_at_depth (fun d => cbn_conv_value X_type X cbn_w_Γ 1 d 1 Conv (CbnVCon cbn_w_O []) cbn_w_v2
      [] cbn_w_s2)
      (CbnCFail CbnWDepth) = CbnCOk (false, [], cbn_w_s3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma cbn_w_tick : cbn_tick cbn_w_s2 = Some cbn_w_s3.
  Proof. vm_compute. reflexivity. Qed.

  (** Satisfying instance of the premises of [cbn_spec_term] at [cbn_depth], with its
    conclusion: a run that answers [false]. *)
  Theorem cbn_witness_seam_run :
    cbn_minv X_type X cbn_w_Γ 1 Σ 1 1 xH cbn_w_G0 (cbn_run_s2 X_type X cbn_w_t cbn_w_u)
    /\ cbn_g_susp 1 1 cbn_w_G0 cbn_env_empty (cbn_run_c1 X_type X cbn_w_t).(cbn_c_term) cbn_w_t
    /\ PCUICCallByNeedSoundEval.cbn_cok cbn_w_G0 (cbn_run_c1 X_type X cbn_w_t)
    /\ cbn_g_susp 1 1 cbn_w_G0 cbn_env_empty
      (cbn_run_c2 X_type X cbn_w_t cbn_w_u).(cbn_c_term) cbn_w_u
    /\ PCUICCallByNeedSoundEval.cbn_cok cbn_w_G0 (cbn_run_c2 X_type X cbn_w_t cbn_w_u)
    /\ exists s',
         cbn_conv_term X_type X cbn_w_Γ 1 cbn_depth 1 Conv cbn_env_empty
           (cbn_run_c1 X_type X cbn_w_t)
           cbn_env_empty (cbn_run_c2 X_type X cbn_w_t cbn_w_u) []
             (cbn_run_s2 X_type X cbn_w_t cbn_w_u) = CbnCOk (false, [], s')
         /\ cbn_post X_type X cbn_w_Γ 1 Σ 1 1 cbn_w_G0 [] s' [].
  Proof.
    assert (hm0 : cbn_minv X_type X cbn_w_Γ 1 Σ 1 1 xH cbn_w_G0
      (cbn_run_s2 X_type X cbn_w_t cbn_w_u))
      by exact (cbn_r_minv_start_terms cbn_w_Γ 1 cbn_w_t cbn_w_u eq_refl eq_refl eq_refl
        eq_refl eq_refl).
    split; [exact hm0|].
    split; [exact (cbn_run_c1_g_susp X_type X 1 cbn_w_t cbn_w_u)|].
    split; [exact (cbn_run_c1_gcok X_type X cbn_w_t cbn_w_u)|].
    split; [exact (cbn_run_c2_g_susp X_type X 1 cbn_w_t cbn_w_u)|].
    split; [exact (cbn_run_c2_gcok X_type X cbn_w_t cbn_w_u)|].
    destruct (cbn_r_split cbn_w_Γ 1 cbn_w_t cbn_w_u (CbnVCon cbn_w_O []) cbn_w_v2 cbn_w_s1 cbn_w_s2
      cbn_w_s3 false
                cbn_w_E1 cbn_w_E2 cbn_w_E3) as [hrun (d & hd1 & hd2)].
    exists cbn_w_s3. split; [exact hrun|].
    destruct cbn_w_section as (_ & _ & _ & hcio).
    exact (cbn_r_post cbn_w_Γ 1 cbn_w_t cbn_w_u eq_refl hcio d _ _ _ _ _ hm0 hd1 hd2 cbn_w_tick).
  Qed.

  (** ** A run that answers [true], with its conversion claim *)

  #[local] Definition cbn_v_G0 : cbn_ghost := cbn_run_ghost X_type X cbn_v_t cbn_v_u.

  (** The section hypotheses of [ConvGhost] at [cbn_v_Γ]. *)
  Lemma cbn_v_section :
    2 = #|cbn_v_Γ| /\ is_closed_context cbn_v_Γ /\ cbn_ctx_hyg cbn_v_Γ
    /\ (forall j decl b, nth_error cbn_v_Γ j = Some decl -> decl.(decl_body) = Some b ->
          PCUICCallByNeedSoundHook.cbn_consts_okb Σ b).
  Proof.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros [|[|j]] decl b hj hb; [| |destruct j; discriminate hj].
      + injection hj as <-. injection hb as <-. reflexivity.
      + injection hj as <-. discriminate hb.
    - intros [|[|j]] decl b hj hb; [| |destruct j; discriminate hj].
      + injection hj as <-. injection hb as <-. reflexivity.
      + injection hj as <-. discriminate hb.
  Qed.

  #[local] Definition cbn_v_R1 :=
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_v_Γ 2 d cbn_env_empty
      (cbn_run_c1 X_type X cbn_v_t) []
                         [CbnRE cbn_env_empty] (cbn_run_s2 X_type X cbn_v_t cbn_v_u))
                           (CbnCFail CbnWDepth).
  #[local] Definition cbn_v_v1 : cbn_value := match cbn_v_R1 with CbnCOk (v, _, _) =>
    v | CbnCFail _ => CbnVCon cbn_w_O [] end.
  #[local] Definition cbn_v_s1 : cbn_state := match cbn_v_R1 with CbnCOk (_, _, s) =>
    s | CbnCFail _ => cbn_init end.
  #[local] Definition cbn_v_R2 :=
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_v_Γ 2 d cbn_env_empty
      (cbn_run_c2 X_type X cbn_v_t cbn_v_u) []
                         [CbnRV cbn_v_v1] cbn_v_s1) (CbnCFail CbnWDepth).
  #[local] Definition cbn_v_v2 : cbn_value := match cbn_v_R2 with CbnCOk (v, _, _) =>
    v | CbnCFail _ => CbnVCon cbn_w_O [] end.
  #[local] Definition cbn_v_s2 : cbn_state := match cbn_v_R2 with CbnCOk (_, _, s) =>
    s | CbnCFail _ => cbn_init end.
  #[local] Definition cbn_v_s3 : cbn_state := match cbn_tick cbn_v_s2 with Some s => s | None =>
    cbn_init end.

  #[local] Lemma cbn_v_E1 :
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_v_Γ 2 d cbn_env_empty
      (cbn_run_c1 X_type X cbn_v_t) []
                         [CbnRE cbn_env_empty] (cbn_run_s2 X_type X cbn_v_t cbn_v_u))
                           (CbnCFail CbnWDepth)
    = CbnCOk (cbn_v_v1, [CbnRE cbn_env_empty], cbn_v_s1).
  Proof. vm_compute. reflexivity. Qed.

  #[local] Lemma cbn_v_E2 :
    cbn_at_depth (fun d => cbn_whnf X_type X cbn_v_Γ 2 d cbn_env_empty
      (cbn_run_c2 X_type X cbn_v_t cbn_v_u) []
                         [CbnRV cbn_v_v1] cbn_v_s1) (CbnCFail CbnWDepth)
    = CbnCOk (cbn_v_v2, [CbnRV cbn_v_v1], cbn_v_s2).
  Proof. vm_compute. reflexivity. Qed.

  #[local] Lemma cbn_v_E3 :
    cbn_at_depth (fun d => cbn_conv_value X_type X cbn_v_Γ 2 d 2 Conv cbn_v_v1 cbn_v_v2 [] cbn_v_s2)
      (CbnCFail CbnWDepth) = CbnCOk (true, [], cbn_v_s3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma cbn_v_tick : cbn_tick cbn_v_s2 = Some cbn_v_s3.
  Proof. vm_compute. reflexivity. Qed.

  (** The claim, by hand: [x] unfolds to [(fun n : y => n) y], which beta-reduces to [y]. *)
  Lemma cbn_v_red : PCUICReduction.red Σ cbn_v_Γ cbn_v_t cbn_v_u.
  Proof.
    eapply PCUICReduction.red_trans.
    - apply PCUICReduction.red1_red.
      exact (PCUICReduction.red_rel Σ cbn_v_Γ 0
        (tApp (tLambda cbn_w_na (tRel 0) (tRel 0)) (tRel 0)) eq_refl).
    - apply PCUICReduction.red1_red. exact
      (PCUICReduction.red_beta Σ cbn_v_Γ cbn_w_na (tRel 1) (tRel 0) (tRel 1)).
  Qed.

  #[local] Lemma cbn_v_lift_conv : cbn_lift_conv cbn_v_Γ 2 Σ 2 2 Conv cbn_v_t cbn_v_u.
  Proof.
    intros u1 u2 e1 e2 _ _. rewrite Nat.sub_diag, lift0_id in e1, e2. subst u1 u2.
    intros Δ hΔ hcl. destruct Δ as [|? Δ]; [|discriminate hΔ].
    constructor. apply (red_ws_cumul_pb (wfΣ := wfΣ)).
    apply into_closed_red; [exact cbn_v_red|exact hcl|reflexivity].
  Qed.

  (** Satisfying instance of the premises of [cbn_spec_term] at [cbn_depth], with its
    conclusion: a run that answers [true]. *)
  Theorem cbn_witness_true_run :
    cbn_minv X_type X cbn_v_Γ 2 Σ 2 2 xH cbn_v_G0 (cbn_run_s2 X_type X cbn_v_t cbn_v_u)
    /\ cbn_g_susp 2 2 cbn_v_G0 cbn_env_empty (cbn_run_c1 X_type X cbn_v_t).(cbn_c_term) cbn_v_t
    /\ PCUICCallByNeedSoundEval.cbn_cok cbn_v_G0 (cbn_run_c1 X_type X cbn_v_t)
    /\ cbn_g_susp 2 2 cbn_v_G0 cbn_env_empty
      (cbn_run_c2 X_type X cbn_v_t cbn_v_u).(cbn_c_term) cbn_v_u
    /\ PCUICCallByNeedSoundEval.cbn_cok cbn_v_G0 (cbn_run_c2 X_type X cbn_v_t cbn_v_u)
    /\ exists s',
         cbn_conv_term X_type X cbn_v_Γ 2 cbn_depth 2 Conv cbn_env_empty
           (cbn_run_c1 X_type X cbn_v_t)
           cbn_env_empty (cbn_run_c2 X_type X cbn_v_t cbn_v_u) []
             (cbn_run_s2 X_type X cbn_v_t cbn_v_u) = CbnCOk (true, [], s')
         /\ cbn_post X_type X cbn_v_Γ 2 Σ 2 2 cbn_v_G0 [] s' []
         /\ cbn_lift_conv cbn_v_Γ 2 Σ 2 2 Conv cbn_v_t cbn_v_u.
  Proof.
    assert (hm0 : cbn_minv X_type X cbn_v_Γ 2 Σ 2 2 xH cbn_v_G0
      (cbn_run_s2 X_type X cbn_v_t cbn_v_u))
      by exact (cbn_r_minv_start_terms cbn_v_Γ 2 cbn_v_t cbn_v_u eq_refl eq_refl eq_refl
        eq_refl eq_refl).
    split; [exact hm0|].
    split; [exact (cbn_run_c1_g_susp X_type X 2 cbn_v_t cbn_v_u)|].
    split; [exact (cbn_run_c1_gcok X_type X cbn_v_t cbn_v_u)|].
    split; [exact (cbn_run_c2_g_susp X_type X 2 cbn_v_t cbn_v_u)|].
    split; [exact (cbn_run_c2_gcok X_type X cbn_v_t cbn_v_u)|].
    destruct (cbn_r_split cbn_v_Γ 2 cbn_v_t cbn_v_u cbn_v_v1 cbn_v_v2 cbn_v_s1 cbn_v_s2
      cbn_v_s3 true
                cbn_v_E1 cbn_v_E2 cbn_v_E3) as [hrun (d & hd1 & hd2)].
    exists cbn_v_s3. split; [exact hrun|].
    destruct cbn_v_section as (_ & _ & _ & hcio).
    split; [exact (cbn_r_post cbn_v_Γ 2 cbn_v_t cbn_v_u eq_refl hcio d _ _ _ _ _ hm0 hd1 hd2
      cbn_v_tick)|].
    exact cbn_v_lift_conv.
  Qed.
End Witness.
