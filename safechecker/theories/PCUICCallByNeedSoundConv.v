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

Import CanonicalTries.

Set Default Goal Selector "1".

(** * The comparison is sound on ghost readings

  The comparison of [PCUICCallByNeed] is the mutual block [conv_slot], [conv_eval],
  [conv_term], [conv_same_code], [same_code_cells], [case_cong], [case_params],
  [case_branches], [conv_rows], [conv_value], [conv_cells]. Each function answers
  [COk (true, _, _)] for "convertible", [COk (false, _, _)] for "this rule does not apply,
  try the next one" and [CFail w] for "give up". Only the [true] answer is a claim.

  The file has six parts.
  - The soundness of the machine's syntactic tests ([cmp_term_sound] and its companions),
    and the substitution fact the same-code rule rests on ([subst_agree_lift]).
  - The bodies of the comparison's functions at a successor fuel, with the functions' own
    names ([same_code_cells_eq], [case_cong_eq], ...), and the syntax of a [tCase] reading
    ([rsusp_case], [open_case_inv]).
  - Syntactic facts about codes and readings ([cg_occ_inv], [cg_subst_fresh_lift], ...).
  - The shape of the roots a machine call returns ([sk_*], [machine_skel]): renamed, never
    reshaped.
  - [Section ConvGhost]: one statement [spec_f d] per function [f], read against the ghost
    reading of [PCUICCallByNeedSoundEval.machine_sound] at the master level of
    [PCUICCallByNeedSoundLevel]; one step lemma per function; and [spec_all_ind], every
    statement at every fuel, by induction on the fuel. Its hypotheses are the section's,
    including [hrb], the read-back interface [PCUICCallByNeedSoundLevel.rb_sound] that
    [PCUICCallByNeedSoundReadBack.rb_sound_holds] proves. [spec_all_holds], after the
    section, states the result with the section's parameters.
  - Two concrete runs at the real fuel [cbn_depth] that meet the premises of [spec_term] and
    satisfy its conclusion ([witness_seam_run], [witness_true_run]).

  The comparison's inputs are read with the ghost read-back, not with one that follows the
  heap: a statement with a heap-following read-back is false at the fuel [cbn_run] uses
  ([PCUICCallByNeedCounterexamples.term_seam_false]). Conversion is squashed ([∥ _ ∥])
  because [ws_cumul_pb] lives in [Type] and the readings in [Prop]; that is also the shape
  of the hook's obligation in [PCUICTypeChecker.convert]. *)

(** ** Soundness of the machine's syntactic tests

  [cmp_term], [cmp_sort], [cmp_level_conv] and [wf_term_univs] ([PCUICCallByNeed]) and
  [cbn_ceq_term] ([PCUICCallByNeedSoundMemo]) read the abstract environment [X]; here they
  are shown sound for every [Σ] that [X] stands for ([abstract_env_ext_rel X Σ]). The proofs
  replay [PCUICSafeConversion.cmpb_term_correct] and its local lemmas without importing that
  file, whose section assumes [normalization_in] — a hypothesis the fast path must not
  depend on. [wf_term_univs_correct] uses the pointwise congruence [cs_on_universes_ext],
  not functional extensionality. *)

Lemma cs_forallb_ext {A} (f g : A -> bool) (l : list A) :
  (forall x, f x = g x) -> forallb f l = forallb g l.
Proof.
  intros h. induction l as [|x l IH]; cbn; [reflexivity|]. now rewrite h, IH.
Qed.

(** [on_universes] depends only on the values of its universe test. *)
Lemma cs_on_universes_ext (f g : Universe.t -> bool) (fc : nat -> term -> bool) :
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
  - now apply cs_forallb_ext.
  - now apply cs_forallb_ext.
  - now apply cs_forallb_ext.
  - destruct X as [hpar [_ hret]].
    rewrite (cs_forallb_ext f g _ hfg).
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

Lemma cs_reflectT_true {P : Type} {b : bool} : reflectT P b -> b = true -> P.
Proof.
  intros r e. destruct r as [p|np]; [exact p|discriminate e].
Qed.

Section CmpSound.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (hΣ : abstract_env_ext_rel X Σ).

  Lemma wf_term_univs_correct (t : term) : wf_term_univs X_type X t = wf_universes Σ t.
  Proof.
    unfold wf_term_univs, wf_universes.
    apply cs_on_universes_ext. intros u.
    symmetry. exact (abstract_env_ext_wf_universeb_correct X hΣ u).
  Qed.

  Lemma cs_iff_reflect (P : Prop) (b : bool) :
    P <-> b -> reflect P b.
  Proof.
    intro H. apply iff_reflect. exact H.
  Qed.

  Lemma cs_wf_universe_iff u :
    wf_universeb Σ u <-> wf_universe Σ u.
  Proof.
    symmetry; apply reflect_iff. eapply wf_universe_reflect.
  Qed.

  Lemma cs_wf_sort_iff s :
    wf_sortb Σ s <-> wf_sort Σ s.
  Proof.
    symmetry; apply reflect_iff. eapply wf_sort_reflect.
  Qed.

  Lemma cs_wf_instance_iff u :
    wf_instanceb Σ u <-> wf_instance Σ u.
  Proof.
    symmetry; apply reflect_iff. eapply wf_instanceP.
  Qed.

  Lemma cs_compare_global_instance_correct pb ref n l l' :
    wf_instance Σ l ->
    wf_instance Σ l' ->
    cmp_global_instance Σ (compare_universe Σ) pb ref n l l' <->
    compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X)
      pb ref n l l'.
  Proof.
    intros hl hl'. apply reflect_iff.
    apply (reflect_cmp_global_instance Σ (abstract_env_lookup X) (wf_universeb Σ)).
    - intros u u' hu hu'. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros u u' hu hu'. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros kn. exact (abstract_env_lookup_correct' X kn hΣ).
    - rewrite wf_universeb_instance_forall. now apply cs_wf_instance_iff.
    - rewrite wf_universeb_instance_forall. now apply cs_wf_instance_iff.
  Qed.

  Lemma cs_cmpb_term_reflect pb napp t u :
    wf_universes Σ t ->
    wf_universes Σ u ->
    reflectT (compare_term_napp Σ Σ pb napp t u)
      (eqb_term_upto_univ_napp (abstract_env_compare_universe X) (abstract_env_compare_sort X)
        (compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X))
        pb napp t u).
  Proof.
    intros ht hu. unfold compare_term_napp.
    apply (reflect_eq_term_upto_univ Σ (wf_universeb Σ) closedu).
    - intros u1 u2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros u1 u2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_universe_correct X hΣ); now apply cs_wf_universe_iff.
    - intros s1 s2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_sort_correct X hΣ); now apply cs_wf_sort_iff.
    - intros s1 s2 h1 h2. apply cs_iff_reflect.
      apply (abstract_env_compare_sort_correct X hΣ); now apply cs_wf_sort_iff.
    - intros gr n ui ui' h1 h2. apply cs_iff_reflect.
      rewrite wf_universeb_instance_forall in h1.
      rewrite wf_universeb_instance_forall in h2.
      apply cs_compare_global_instance_correct; now apply cs_wf_instance_iff.
    - intros gr n ui ui' h1 h2. apply cs_iff_reflect.
      rewrite wf_universeb_instance_forall in h1.
      rewrite wf_universeb_instance_forall in h2.
      apply cs_compare_global_instance_correct; now apply cs_wf_instance_iff.
    - exact ht.
    - exact hu.
  Qed.

  Lemma cmp_term_wf (pb : conv_pb) (napp : nat) (t u : term) :
    cmp_term X_type X pb napp t u = true -> wf_universes Σ t /\ wf_universes Σ u.
  Proof.
    unfold cmp_term. intros h.
    apply andb_true_iff in h as [h _].
    apply andb_true_iff in h as [ht hu].
    split; rewrite <- wf_term_univs_correct; assumption.
  Qed.

  Lemma cmp_term_sound (pb : conv_pb) (napp : nat) (t u : term) :
    cmp_term X_type X pb napp t u = true -> compare_term_napp Σ Σ pb napp t u.
  Proof.
    intros h. destruct (cmp_term_wf pb napp t u h) as [ht hu].
    unfold cmp_term in h. apply andb_true_iff in h as [_ h].
    exact (cs_reflectT_true (cs_cmpb_term_reflect pb napp t u ht hu) h).
  Qed.

  Lemma cbn_ceq_term_sound (t u : term) :
    wf_universes Σ t -> wf_universes Σ u ->
    cbn_ceq_term X_type X t u = true -> compare_term Σ Σ Conv t u.
  Proof.
    intros ht hu h.
    exact (cs_reflectT_true (cs_cmpb_term_reflect Conv 0 t u ht hu) h).
  Qed.

  Lemma cmp_sort_sound (pb : conv_pb) (s1 s2 : sort) :
    cmp_sort X_type X pb s1 s2 = true -> compare_sort Σ pb s1 s2.
  Proof.
    unfold cmp_sort. intros h.
    apply andb_true_iff in h as [h12 h].
    apply andb_true_iff in h12 as [h1 h2].
    rewrite <- (abstract_env_ext_wf_sortb_correct X hΣ) in h1.
    rewrite <- (abstract_env_ext_wf_sortb_correct X hΣ) in h2.
    assert (w1 : wf_sort Σ s1) by (apply cs_wf_sort_iff; exact h1).
    assert (w2 : wf_sort Σ s2) by (apply cs_wf_sort_iff; exact h2).
    exact (proj2 (abstract_env_compare_sort_correct X hΣ pb s1 s2 w1 w2) h).
  Qed.

  Lemma cmp_level_conv_sound (l1 l2 : Level.t) :
    cmp_level_conv X_type X l1 l2 = true ->
    compare_universe Σ Conv (Universe.make' l1) (Universe.make' l2).
  Proof.
    unfold cmp_level_conv; cbv zeta. intros h.
    apply andb_true_iff in h as [h12 h].
    apply andb_true_iff in h12 as [h1 h2].
    rewrite <- (abstract_env_ext_wf_universeb_correct X hΣ) in h1.
    rewrite <- (abstract_env_ext_wf_universeb_correct X hΣ) in h2.
    assert (w1 : wf_universe Σ (Universe.make' l1)) by (apply cs_wf_universe_iff; exact h1).
    assert (w2 : wf_universe Σ (Universe.make' l2)) by (apply cs_wf_universe_iff; exact h2).
    exact (proj2 (abstract_env_compare_universe_correct X hΣ Conv _ _ w1 w2) h).
  Qed.

  Lemma cmp_level_conv_instance (u1 u2 : Instance.t) :
    forallb2 (cmp_level_conv X_type X) u1 u2 = true ->
    cmp_universe_instance (compare_universe Σ Conv) u1 u2.
  Proof.
    unfold cmp_universe_instance.
    revert u2. induction u1 as [|l1 u1 IH]; intros u2; destruct u2 as [|l2 u2]; cbn;
      try (intros e; discriminate e).
    - intros _. constructor.
    - intros h. apply andb_true_iff in h as [h hs]. constructor.
      + exact (cmp_level_conv_sound l1 l2 h).
      + exact (IH u2 hs).
  Qed.
End CmpSound.

(** ** A substitution does not look at an index the term does not use

  The same-code rule skips a position whose index does not occur in the code
  ([noccur_between i 1 t]), so what it establishes of the two environments is weaker than
  "pairwise convertible". [subst_noccur_irrel] says that this is enough: two substitutions
  that agree at every index the term uses give the same term. [subst_agree_lift] is the
  instance the read-back shape [subst ts 0 (lift N #|ts| t)] meets, where the cut of the
  lift sits above every substituted index, so the occurrence test is made on [t] itself
  ([noccur_between_lift]). *)

Lemma noccA_forallb_map {A B : Type} (P : A -> Type) (p : A -> bool) (q : B -> bool)
  (f : A -> B) (l : list A) :
  All P l -> (forall x, P x -> p x = true -> q (f x) = true) ->
  forallb p l = true -> forallb q (map f l) = true.
Proof.
  intros HA Hf. induction HA as [|x l Px HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff. split.
  - exact (Hf x Px H1).
  - exact (IH H2).
Qed.

Lemma noccA_map_ext {A B : Type} (P : A -> Type) (f g : A -> B) (l : list A) :
  All P l -> (forall x, In x l -> P x -> f x = g x) -> map f l = map g l.
Proof.
  intros HA. induction HA as [|x l Px HA IH]; cbn; intros H; [reflexivity|].
  f_equal.
  - apply H; [left; reflexivity | exact Px].
  - apply IH. intros y Hy Py. apply H; [right; exact Hy | exact Py].
Qed.

Lemma noccA_forallb_false {A : Type} (p : A -> bool) (l : list A) (x : A) :
  In x l -> p x = false -> forallb p l = false.
Proof.
  intros Hin Hx. induction l as [|y l IH]; cbn in Hin |- *; [contradiction|].
  destruct Hin as [Hy|Hin].
  - subst y. rewrite Hx. reflexivity.
  - rewrite (IH Hin). apply Bool.andb_false_r.
Qed.

(* [noccA_false H] closes a goal [c = false] where [c] is a conjunction ([andb]) one of
   whose conjuncts is, up to conversion, the left side of [H : _ = false]. *)
Local Ltac noccA_false H :=
  first [ exact H
        | apply Bool.andb_false_iff;
          first [ left; noccA_false H | right; noccA_false H ] ].

(* [noccA_sub Hj] moves the agreement hypothesis [Hj] of a term to one of its direct
   subterms: if the subterm uses an index then so does the term. *)
Local Ltac noccA_sub Hj :=
  let j := fresh "j" in
  let Hj1 := fresh "Hj1" in
  let Hj2 := fresh "Hj2" in
  intros j Hj1 Hj2; apply Hj; [exact Hj1 | cbn [noccur_between]; noccA_false Hj2].

Lemma noccur_between_lift (n k i : nat) (t : term) :
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
    refine (noccA_forallb_map _ _ _ _ _ Hl _ H). intros x Px Hx. apply Px; assumption.
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
    2:{ refine (noccA_forallb_map _ _ _ _ _ Hbrs _ Hbr).
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
    refine (noccA_forallb_map _ _ _ _ _ Hpar _ Hpa). intros x Px Hx. apply Px; assumption.
  - (* tProj *)
    intros pr c IHc N K I HIK H. cbn [lift noccur_between] in H |- *.
    apply IHc; assumption.
  - (* tFix *)
    intros mfix idx Hm N K I HIK H. cbn [lift noccur_between] in H |- *.
    rewrite length_map.
    refine (noccA_forallb_map _ _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def, map_def in Hd |- *. simpl in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; first [assumption | lia].
  - (* tCoFix *)
    intros mfix idx Hm N K I HIK H. cbn [lift noccur_between] in H |- *.
    rewrite length_map.
    refine (noccA_forallb_map _ _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def, map_def in Hd |- *. simpl in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; first [assumption | lia].
  - (* tPrim *)
    intros prim Hprim N K I HIK H. cbn [lift noccur_between] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (noccA_forallb_map _ _ _ _ _ Hval _ H1). intros y Py Hy. apply Py; assumption.
    + apply Hdef; assumption.
    + apply Hty; assumption.
Qed.

Lemma subst_noccur_irrel (l1 l2 : list term) :
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
    f_equal. apply (noccA_map_ext _ _ _ _ Hl). intros x Hin Px. apply Px.
    intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
    exact (noccA_forallb_false _ _ _ Hin Hj2).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k Hj. cbn [subst].
    f_equal; [apply IHA | apply IHB]; noccA_sub Hj.
  - (* tLambda *)
    intros na A IHA B IHB k Hj. cbn [subst].
    f_equal; [apply IHA | apply IHB]; noccA_sub Hj.
  - (* tLetIn *)
    intros na t IHt ty IHty B IHB k Hj. cbn [subst].
    f_equal; [apply IHt | apply IHty | apply IHB]; noccA_sub Hj.
  - (* tApp *)
    intros u v IHu IHv k Hj. cbn [subst].
    f_equal; [apply IHu | apply IHv]; noccA_sub Hj.
  - (* tConst *) intros; reflexivity.
  - (* tInd *) intros; reflexivity.
  - (* tConstruct *) intros; reflexivity.
  - (* tCase *)
    intros ci p Hp c IHc brs Hbrs k Hj. cbn [subst].
    destruct Hp as [Hpar [Hctx Hret]].
    f_equal; [unfold map_predicate_k; f_equal | apply IHc; noccA_sub Hj | ].
    + (* pparams *)
      apply (noccA_map_ext _ _ _ _ Hpar). intros x Hin Px. apply Px.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      unfold test_predicate_k.
      pose proof (noccA_forallb_false _ _ _ Hin Hj2) as Hf. noccA_false Hf.
    + (* preturn *)
      apply Hret. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      unfold test_predicate_k.
      rewrite <- Nat.add_assoc in Hj2. noccA_false Hj2.
    + (* branches *)
      apply (noccA_map_ext _ _ _ _ Hbrs). intros br Hin [Pctx Pbody].
      unfold map_branch_k. f_equal. apply Pbody.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hb : test_branch_k p (fun k0 => noccur_between k0 1) (k + j) br = false)
        by (unfold test_branch_k; noccA_false Hj2).
      pose proof (noccA_forallb_false _ _ _ Hin Hb) as Hf. noccA_false Hf.
  - (* tProj *)
    intros pr c IHc k Hj. cbn [subst].
    f_equal; apply IHc; noccA_sub Hj.
  - (* tFix *)
    intros mfix idx Hm k Hj. cbn [subst].
    f_equal. apply (noccA_map_ext _ _ _ _ Hm). intros d Hin [Pty Pbody].
    unfold map_def. f_equal.
    + apply Pty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
    + apply Pbody. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
  - (* tCoFix *)
    intros mfix idx Hm k Hj. cbn [subst].
    f_equal. apply (noccA_map_ext _ _ _ _ Hm). intros d Hin [Pty Pbody].
    unfold map_def. f_equal.
    + apply Pty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
    + apply Pbody. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn [noccur_between].
      rewrite <- Nat.add_assoc in Hj2.
      assert (Hd : test_def (noccur_between (k + j) 1)
                     (noccur_between (#|mfix| + (k + j)) 1) d = false)
        by (unfold test_def; noccA_false Hj2).
      exact (noccA_forallb_false _ _ _ Hin Hd).
  - (* tPrim *)
    intros prim Hprim k Hj. cbn [subst].
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    assert (E1 : subst l1 k (array_type a) = subst l2 k (array_type a)).
    { apply Hty. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn. noccA_false Hj2. }
    assert (E2 : subst l1 k (array_default a) = subst l2 k (array_default a)).
    { apply Hdef. intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn. noccA_false Hj2. }
    assert (E3 : map (subst l1 k) (array_value a) = map (subst l2 k) (array_value a)).
    { apply (noccA_map_ext _ _ _ _ Hval). intros y Hin Py. apply Py.
      intros j Hj1 Hj2. apply Hj; [exact Hj1|]. cbn.
      pose proof (noccA_forallb_false _ _ _ Hin Hj2) as Hf. noccA_false Hf. }
    unfold mapu_array_model.
    rewrite E1. rewrite E2. rewrite E3. reflexivity.
Qed.

Lemma subst_agree_lift (l1 l2 : list term) (N m : nat) (t : term) :
  #|l1| = #|l2| -> m = #|l1| ->
  (forall j, j < #|l1| -> noccur_between j 1 t = false ->
             nth_error l1 j = nth_error l2 j) ->
  subst l1 0 (lift N m t) = subst l2 0 (lift N m t).
Proof.
  intros Hlen Hm Hag.
  apply subst_noccur_irrel; [exact Hlen|].
  intros j Hj Hnoc. apply Hag; [exact Hj|].
  destruct (noccur_between j 1 t) eqn:E; [|reflexivity].
  exfalso.
  assert (Hl : noccur_between (0 + j) 1 (lift N m t) = true)
    by (apply noccur_between_lift; [lia | exact E]).
  rewrite Hl in Hnoc. discriminate.
Qed.

(** ** The comparison's bodies at a successor fuel, and the syntax of a [tCase] reading

  The bodies are written with the names of the comparison's functions: [cbn] would replace
  them by the raw mutual fixpoint. *)

Section ConvEqs.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat).

  Local Notation xpred0 := (fun _ : nat => false) (only parsing).
  Local Notation xpredT := (fun _ : nat => true) (only parsing).

  Lemma pfd_push_fresh_O (lvl : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state) :
    push_fresh 0 lvl e1 e2 rs s = COk ((lvl, e1, e2), rs, s).
  Proof. reflexivity. Qed.

  Lemma pfd_push_fresh_S (m lvl : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state) :
    push_fresh (S m) lvl e1 e2 rs s =
    match alloc (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s with
    | COk (x, rs1, s1) =>
      match rs1 with
      | RE e1' :: RE e2' :: rs2 =>
        push_fresh m (S lvl) (env_push (SAddr x) e1') (env_push (SAddr x) e2') rs2 s1
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma haddr_eqb_eq (a b : haddr) : haddr_eqb a b = true -> a = b.
  Proof.
    destruct a as [p], b as [q]. unfold haddr_eqb. cbn. intros h.
    apply Pos.eqb_eq in h. rewrite h. reflexivity.
  Qed.

  Lemma same_code_cells_eq (k : unit -> cbn_fuel) (lvl : nat) (t : term) (i : nat)
      (l1 l2 : list cbn_slot) (rs : list root) (s : cbn_state) :
    same_code_cells X_type X Γ nctx (FS k) lvl t i l1 l2 rs s
    = match l1, l2 with
      | [], [] => COk (true, rs, s)
      | x1 :: l1, x2 :: l2 =>
        if slot_same x1 x2 || noccur_between i 1 t
        then same_code_cells X_type X Γ nctx (k tt) lvl t (S i) l1 l2 rs s
        else
          match conv_slot X_type X Γ nctx (k tt) lvl Conv x1 x2
                  (RSk l1 :: RSk l2 :: rs) s with
          | COk (true, rs, s) =>
            match rs with
            | RSk l1 :: RSk l2 :: rs =>
              same_code_cells X_type X Γ nctx (k tt) lvl t (S i) l1 l2 rs s
            | _ => CFail WRoots
            end
          | COk (false, rs, s) => COk (false, skipn 2 rs, s)
          | CFail w => CFail w
          end
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma conv_same_code_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) :
    conv_same_code X_type X Γ nctx (FS k) lvl e1 c1 e2 c2 rs s
    = (if (e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals)) then
         let (b, s) := code_eq X_type X c1 c2 s in
         if b then same_code_cells X_type X Γ nctx (k tt) lvl (c1.(c_term)) 0
                     (e1.(ev_vals)) (e2.(ev_vals)) rs s
         else COk (false, rs, s)
       else COk (false, rs, s)).
  Proof. reflexivity. Qed.

  Lemma case_params_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (i : N) (l1 l2 : list term) (rs : list root)
      (s : cbn_state) :
    case_params X_type X Γ nctx (FS k) lvl e1 c1 e2 c2 i l1 l2 rs s
    = match l1, l2 with
      | [], [] => COk (true, rs, s)
      | t1 :: l1, t2 :: l2 =>
        match conv_term X_type X Γ nctx (k tt) lvl Conv
                e1 (child c1 (case_param_step i) t1)
                e2 (child c2 (case_param_step i) t2) (RE e1 :: RE e2 :: rs) s with
        | COk (true, rs, s) =>
          match rs with
          | RE e1 :: RE e2 :: rs =>
            case_params X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 (N.succ i)
              l1 l2 rs s
          | _ => CFail WRoots
          end
        | COk (false, rs, s) => COk (false, skipn 2 rs, s)
        | CFail w => CFail w
        end
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma case_branches_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (i : N) (l1 l2 : list (branch term)) (rs : list root)
      (s : cbn_state) :
    case_branches X_type X Γ nctx (FS k) lvl e1 c1 e2 c2 i l1 l2 rs s
    = match l1, l2 with
      | [], [] => COk (true, rs, s)
      | b1 :: l1, b2 :: l2 =>
        if case_ctx_ok b1.(bcontext) b2.(bcontext) then
          match push_fresh #|b1.(bcontext)| lvl e1 e2 (RE e1 :: RE e2 :: rs) s with
          | COk (r, rs, s) =>
            let '(lvlb, eb1, eb2) := r in
            match conv_term X_type X Γ nctx (k tt) lvlb Conv
                    eb1 (child c1 (case_branch_step i) b1.(bbody))
                    eb2 (child c2 (case_branch_step i) b2.(bbody)) rs s with
            | COk (true, rs, s) =>
              match rs with
              | RE e1 :: RE e2 :: rs =>
                case_branches X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 (N.succ i)
                  l1 l2 rs s
              | _ => CFail WRoots
              end
            | COk (false, rs, s) => COk (false, skipn 2 rs, s)
            | CFail w => CFail w
            end
          | CFail w => CFail w
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma case_cong_eq (k : unit -> cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code)
      (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) :
    case_cong X_type X Γ nctx (FS k) lvl e1 c1 e2 c2 rs s
    = match c1.(c_term), c2.(c_term) with
      | tCase ci1 p1 sc1 brs1, tCase ci2 p2 sc2 brs2 =>
        if case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|)
           && (#|p1.(pparams)| == #|p2.(pparams)|)
           && forallb2 (cmp_level_conv X_type X) p1.(puinst) p2.(puinst)
           && case_ctx_ok p1.(pcontext) p2.(pcontext)
        then
          match case_params X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 0%N
                  p1.(pparams) p2.(pparams) (RE e1 :: RE e2 :: rs) s with
          | COk (true, rs, s) =>
            match rs with
            | RE e1 :: RE e2 :: rs =>
              match push_fresh #|p1.(pcontext)| lvl e1 e2 (RE e1 :: RE e2 :: rs) s with
              | COk (r, rs, s) =>
                let '(lvlr, er1, er2) := r in
                match conv_term X_type X Γ nctx (k tt) lvlr Conv
                        er1 (child c1 1 p1.(preturn)) er2 (child c2 1 p2.(preturn)) rs s with
                | COk (true, rs, s) =>
                  match rs with
                  | RE e1 :: RE e2 :: rs =>
                    match conv_term X_type X Γ nctx (k tt) lvl Conv
                            e1 (child c1 0 sc1) e2 (child c2 0 sc2) (RE e1 :: RE e2 :: rs) s with
                    | COk (true, rs, s) =>
                      match rs with
                      | RE e1 :: RE e2 :: rs =>
                        case_branches X_type X Γ nctx (k tt) lvl e1 c1 e2 c2 0%N
                          brs1 brs2 rs s
                      | _ => CFail WRoots
                      end
                    | COk (false, rs, s) => COk (false, skipn 2 rs, s)
                    | CFail w => CFail w
                    end
                  | _ => CFail WRoots
                  end
                | COk (false, rs, s) => COk (false, skipn 2 rs, s)
                | CFail w => CFail w
                end
              | CFail w => CFail w
              end
            | _ => CFail WRoots
            end
          | COk (false, rs, s) => COk (false, skipn 2 rs, s)
          | CFail w => CFail w
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end.
  Proof. reflexivity. Qed.

  Lemma cc_forallb_Forall {A : Type} (f : A -> bool) (l : list A) :
    forallb f l = true -> Forall (fun x => f x = true) l.
  Proof.
    induction l as [|x l ih]; cbn; intros h; [constructor|].
    apply andb_true_iff in h as [h1 h2]. constructor; [exact h1|exact (ih h2)].
  Qed.

  Lemma cc_Forall_impl {A : Type} (P Q : A -> Prop) (l : list A) :
    Forall P l -> (forall x, P x -> Q x) -> Forall Q l.
  Proof. intros h himp. induction h; constructor; auto. Qed.

  Definition rd_pred (ts : list term) (N : nat) (p : predicate term) : predicate term :=
    {| pparams := map (fun t => subst ts 0 (lift N #|ts| t)) p.(pparams);
       puinst := p.(puinst);
       pcontext := p.(pcontext);
       preturn := subst ts #|p.(pcontext)| (lift N (#|p.(pcontext)| + #|ts|) p.(preturn)) |}.

  Definition rd_br (ts : list term) (N : nat) (br : branch term) : branch term :=
    {| bcontext := br.(bcontext);
       bbody := subst ts #|br.(bcontext)| (lift N (#|br.(bcontext)| + #|ts|) br.(bbody)) |}.

  Lemma rsusp_case (ts : list term) (N : nat) (ci : case_info) (p : predicate term)
      (c : term) (brs : list (branch term)) :
    subst ts 0 (lift N #|ts| (tCase ci p c brs))
    = tCase ci (rd_pred ts N p) (subst ts 0 (lift N #|ts| c)) (map (rd_br ts N) brs).
  Proof.
    cbn [lift subst]. f_equal.
    - unfold rd_pred, map_predicate_k. cbn [pparams puinst pcontext preturn]. cbv [id].
      rewrite map_map. rewrite Nat.add_0_r. reflexivity.
    - rewrite map_map. apply map_ext. intros br. unfold rd_br, map_branch_k.
      cbn [bcontext bbody]. cbv [id]. rewrite Nat.add_0_r. reflexivity.
  Qed.

  Lemma open_case_inv (Ξ : context) (ci : case_info) (p : predicate term) (c : term)
      (brs : list (branch term)) :
    is_open_term Ξ (tCase ci p c brs) ->
    forallb (is_open_term Ξ) p.(pparams)
    /\ on_free_vars (shiftnP #|p.(pcontext)| (shiftnP #|Ξ| xpred0)) p.(preturn)
    /\ on_free_vars_ctx (closedP #|p.(pparams)| xpredT) p.(pcontext)
    /\ is_open_term Ξ c
    /\ Forall (fun br => on_free_vars_ctx (closedP #|p.(pparams)| xpredT) br.(bcontext)
                 /\ on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Ξ| xpred0)) br.(bbody))
         brs.
  Proof.
    intros h. cbn [on_free_vars is_true] in h.
    apply andb_true_iff in h as [h1 h]. apply andb_true_iff in h as [h2 h].
    apply andb_true_iff in h as [h3 h]. apply andb_true_iff in h as [h4 h5].
    rewrite test_context_k_closed_on_free_vars_ctx in h3.
    split; [exact h1|]. split; [exact h2|]. split; [exact h3|]. split; [exact h4|].
    refine (cc_Forall_impl _ _ _ (cc_forallb_Forall _ _ h5) _).
    intros br hb. cbv beta in hb. apply andb_true_iff in hb as [hb1 hb2].
    rewrite test_context_k_closed_on_free_vars_ctx in hb1. split; [exact hb1|exact hb2].
  Qed.

End ConvEqs.

(** * Syntactic facts the ghost-reading comparison needs

  [cg_occ_inv]: a slot the code really uses is a subterm of the reading, so the reading's
  free-variable property passes to it (hygiene rules out an occurrence that is only in a
  [tCase] context). [cg_subst_scope_inv]: the free variables of a term above a substituted
  block. [cg_subst_fresh_lift]: fresh variables pushed at the top of an environment read
  back the lifted body. [cg_code_inv_wf_universes]: a code of a universe-checked entry is
  universe-checked. *)

Local Notation xpred0 := (fun _ : nat => false) (only parsing).
Local Notation xpredT := (fun _ : nat => true) (only parsing).

(** ** List helpers *)

Lemma cg_forallb_In {A} (p : A -> bool) (l : list A) (x : A) :
  forallb p l = true -> In x l -> p x = true.
Proof. intros H Hin. rewrite forallb_forall in H. exact (H x Hin). Qed.

Lemma cg_forallb_nth_some {A} (p : A -> bool) (l : list A) n x :
  forallb p l = true -> nth_error l n = Some x -> p x = true.
Proof. intros h hn. apply nth_error_In in hn. exact (cg_forallb_In p l x h hn). Qed.

Lemma cg_All_forallb_false {A} (Q : A -> Type) (p : A -> bool) (G : Prop) (l : list A) :
  All Q l -> forallb p l = false -> (forall x, In x l -> Q x -> p x = false -> G) -> G.
Proof.
  intros HA. induction HA as [|x l Qx HA IH]; cbn; intros H K; [discriminate H|].
  apply Bool.andb_false_iff in H as [H|H].
  - exact (K x (or_introl eq_refl) Qx H).
  - apply IH; [exact H|]. intros y Hy Qy Hpy. exact (K y (or_intror Hy) Qy Hpy).
Qed.

Lemma cg_forallb_All_impl {A} (Q : A -> Type) (p q : A -> bool) (l : list A) :
  All Q l -> (forall x, Q x -> p x = true -> q x = true) ->
  forallb p l = true -> forallb q l = true.
Proof.
  intros HA Hf. induction HA as [|x l Qx HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff; split; [exact (Hf x Qx H1) | exact (IH H2)].
Qed.

Lemma cg_forallb_map_inv {A B} (Q : A -> Type) (p : A -> bool) (q : B -> bool) (f : A -> B)
  (l : list A) :
  All Q l -> (forall x, Q x -> q (f x) = true -> p x = true) ->
  forallb q (map f l) = true -> forallb p l = true.
Proof.
  intros HA Hf. induction HA as [|x l Qx HA IH]; cbn; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2].
  apply Bool.andb_true_iff; split; [exact (Hf x Qx H1) | exact (IH H2)].
Qed.

Lemma cg_test_context_k_impl_on (Q : term -> Type) (f g : nat -> term -> bool) (m : nat)
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

Lemma cg_closedn_noccur : forall (t : term) (k n : nat), closedn k t -> noccur_between k n t.
Proof.
  intros t. elim t using term_forall_list_ind.
  - (* tRel *)
    intros r k n H. cbn [closedn noccur_between] in H |- *.
    apply Bool.orb_true_iff; left; exact H.
  - (* tVar *) intros; reflexivity.
  - (* tEvar *)
    intros ev l Hl k n H. cbn [closedn noccur_between] in H |- *.
    refine (cg_forallb_All_impl _ _ _ _ Hl _ H). intros x Px Hx. apply Px; exact Hx.
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
    2:{ refine (cg_forallb_All_impl _ _ _ _ Hbrs _ Hbr).
        intros br [Pctx Pbody] Hb. unfold test_branch_k in Hb |- *.
        apply Bool.andb_true_iff in Hb as [Hb1 Hb2].
        apply Bool.andb_true_iff; split.
        - refine (cg_test_context_k_impl_on _ _ _ _ _ Pctx _ Hb1).
          intros i t' Qt Ht. apply Qt; exact Ht.
        - apply Pbody; exact Hb2. }
    apply Bool.andb_true_iff; split.
    2:{ apply IHc; exact Hc. }
    apply Bool.andb_true_iff; split.
    2:{ apply Hret; exact Hr. }
    apply Bool.andb_true_iff; split.
    2:{ refine (cg_test_context_k_impl_on _ _ _ _ _ Hctx _ Hcx).
        intros i t' Qt Ht. apply Qt; exact Ht. }
    apply Bool.andb_true_iff; split; [reflexivity|].
    refine (cg_forallb_All_impl _ _ _ _ Hpar _ Hpa). intros x Px Hx. apply Px; exact Hx.
  - (* tProj *)
    intros pr c IHc k n H. cbn [closedn noccur_between] in H |- *. apply IHc; exact H.
  - (* tFix *)
    intros mfix idx Hm k n H. cbn [closedn noccur_between] in H |- *.
    refine (cg_forallb_All_impl _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; assumption.
  - (* tCoFix *)
    intros mfix idx Hm k n H. cbn [closedn noccur_between] in H |- *.
    refine (cg_forallb_All_impl _ _ _ _ Hm _ H).
    intros d [Pty Pbody] Hd. unfold test_def in Hd |- *.
    apply Bool.andb_true_iff in Hd as [Hd1 Hd2].
    apply Bool.andb_true_iff; split; [apply Pty | apply Pbody]; assumption.
  - (* tPrim *)
    intros prim Hprim k n H. cbn [closedn noccur_between] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cg_forallb_All_impl _ _ _ _ Hval _ H1). intros y Py Hy. apply Py; exact Hy.
    + apply Hdef; exact H2.
    + apply Hty; exact H3.
Qed.

(** ** Free-variable helpers *)

Lemma cg_hyg_shift n t : on_free_vars (shiftnP n xpredT) t = on_free_vars xpredT t.
Proof. apply on_free_vars_ext. apply shiftnP_xpredT. Qed.

Lemma cg_ofv_shiftn (P : nat -> bool) n k t :
  on_free_vars (shiftnP n (shiftnP k P)) t = on_free_vars (shiftnP (n + k) P) t.
Proof. apply on_free_vars_ext. apply shiftnP_add. Qed.

Lemma cg_ofv_lift0 (P : nat -> bool) k u :
  on_free_vars (shiftnP k P) (lift0 k u) = on_free_vars P u.
Proof.
  rewrite lift_rename. rewrite PCUICOnFreeVarsConv.on_free_vars_rename.
  apply on_free_vars_ext. intros i. cbv [shiftnP lift_renaming].
  replace (0 <=? i) with true by (symmetry; apply Nat.leb_le; lia).
  replace (k + i <? k) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (k + i - k) with i by lia. reflexivity.
Qed.

(** Hygiene closes every [tCase] context, so no index occurs in one. *)
Lemma cg_ctx_hyg_noccur (n m : nat) (ctx : context) :
  test_context_k (fun k => on_free_vars (closedP k xpredT)) m ctx = true ->
  test_context_k (fun k' => noccur_between k' n) m ctx = true.
Proof.
  induction ctx as [|d ctx IH]; cbn [test_context_k]; intros H; [reflexivity|].
  apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff; split; [exact (IH H1)|].
  destruct d as [na [b|] ty]; unfold test_decl in H2 |- *;
    cbn [option_default decl_body decl_type andb] in H2 |- *.
  - apply Bool.andb_true_iff in H2 as [H2 H3].
    apply Bool.andb_true_iff; split; apply cg_closedn_noccur; rewrite closedP_on_free_vars;
      assumption.
  - apply cg_closedn_noccur; rewrite closedP_on_free_vars; assumption.
Qed.

(** ** 2. An index the term really uses *)

Lemma cg_occ_inv (P : nat -> bool) (ts : list term) (N j : nat) (u : term) :
  nth_error ts j = Some u ->
  forall (t : term) (k : nat),
    on_free_vars xpredT t ->
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
    rewrite cg_ofv_lift0 in Hf. exact Hf.
  - (* tVar *) intros i k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tEvar *)
    intros ev l Hl k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply (cg_All_forallb_false _ _ _ _ Hl Hn). intros x Hin IH Hx.
    apply (IH k); [exact (cg_forallb_In _ _ _ Hh Hin) | exact Hx |].
    apply (cg_forallb_In _ _ _ Hf). apply in_map. apply in_map. exact Hin.
  - (* tSort *) intros s k _ Hn _. cbn in Hn. discriminate Hn.
  - (* tProd *)
    intros na A IHA B IHB k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [HhA HhB]. rewrite cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [HfA HfB]. rewrite cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHA k HhA Hn HfA).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tLambda *)
    intros na A IHA B IHB k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [HhA HhB]. rewrite cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [HfA HfB]. rewrite cg_ofv_shiftn in HfB.
    apply Bool.andb_false_iff in Hn as [Hn|Hn].
    + exact (IHA k HhA Hn HfA).
    + exact (IHB (S k) HhB Hn HfB).
  - (* tLetIn *)
    intros na b IHb ty IHty B IHB k Hh Hn Hf.
    cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    apply Bool.andb_true_iff in Hh as [Hhb Hh]. apply Bool.andb_true_iff in Hh as [Hhty HhB].
    rewrite cg_hyg_shift in HhB.
    apply Bool.andb_true_iff in Hf as [Hfb Hf]. apply Bool.andb_true_iff in Hf as [Hfty HfB].
    rewrite cg_ofv_shiftn in HfB.
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
      apply (cg_All_forallb_false _ _ _ _ Hpar Hn). intros x Hin IH Hx.
      apply (IH k); [exact (cg_forallb_In _ _ _ Hhpa Hin) | exact Hx |].
      apply (cg_forallb_In _ _ _ Hfpa). apply in_map. apply in_map. exact Hin.
    + (* pcontext *)
      rewrite (cg_ctx_hyg_noccur 1 _ _ Hhcx) in Hn. discriminate Hn.
    + (* preturn *)
      apply (Hret (#|pcontext p| + k)).
      * rewrite cg_hyg_shift in Hhr. exact Hhr.
      * rewrite <- Nat.add_assoc. exact Hn.
      * rewrite cg_ofv_shiftn in Hfr. rewrite <- Nat.add_assoc. exact Hfr.
    + (* scrutinee *) exact (IHc k Hhc Hn Hfc).
    + (* branches *)
      apply (cg_All_forallb_false _ _ _ _ Hbrs Hn). intros br Hin [Pctx Pbody] Hx.
      unfold test_branch_k in Hx.
      pose proof (cg_forallb_In _ _ _ Hhbr Hin) as Hhb. cbn beta in Hhb.
      apply Bool.andb_true_iff in Hhb as [Hhbcx Hhbb].
      apply Bool.andb_false_iff in Hx as [Hx|Hx].
      * rewrite (cg_ctx_hyg_noccur 1 _ _ Hhbcx) in Hx. discriminate Hx.
      * pose proof (cg_forallb_In _ _ _ Hfbr (in_map _ _ _ (in_map _ _ _ Hin))) as Hfb.
        cbn [map_branch_k bcontext bbody id] in Hfb.
        apply Bool.andb_true_iff in Hfb as [_ Hfb].
        apply (Pbody (#|bcontext br| + k)).
        -- rewrite cg_hyg_shift in Hhbb. exact Hhbb.
        -- rewrite <- Nat.add_assoc. exact Hx.
        -- rewrite cg_ofv_shiftn in Hfb. rewrite <- Nat.add_assoc. exact Hfb.
  - (* tProj *)
    intros pr c IHc k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    exact (IHc k Hh Hn Hf).
  - (* tFix *)
    intros mfix idx Hm k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    rewrite !length_map in Hf.
    apply (cg_All_forallb_false _ _ _ _ Hm Hn). intros d Hin [Pty Pbody] Hx.
    unfold test_def in Hx.
    pose proof (cg_forallb_In _ _ _ Hh Hin) as Hhd. unfold test_def in Hhd.
    apply Bool.andb_true_iff in Hhd as [Hhty Hhbody].
    pose proof (cg_forallb_In _ _ _ Hf (in_map _ _ _ (in_map _ _ _ Hin))) as Hfd.
    unfold test_def in Hfd. cbn [map_def dtype dbody] in Hfd.
    apply Bool.andb_true_iff in Hfd as [Hfty Hfbody].
    apply Bool.andb_false_iff in Hx as [Hx|Hx].
    + exact (Pty k Hhty Hx Hfty).
    + apply (Pbody (#|mfix| + k)).
      * rewrite cg_hyg_shift in Hhbody. exact Hhbody.
      * rewrite <- Nat.add_assoc. exact Hx.
      * rewrite cg_ofv_shiftn in Hfbody. rewrite <- Nat.add_assoc. exact Hfbody.
  - (* tCoFix *)
    intros mfix idx Hm k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    rewrite !length_map in Hf.
    apply (cg_All_forallb_false _ _ _ _ Hm Hn). intros d Hin [Pty Pbody] Hx.
    unfold test_def in Hx.
    pose proof (cg_forallb_In _ _ _ Hh Hin) as Hhd. unfold test_def in Hhd.
    apply Bool.andb_true_iff in Hhd as [Hhty Hhbody].
    pose proof (cg_forallb_In _ _ _ Hf (in_map _ _ _ (in_map _ _ _ Hin))) as Hfd.
    unfold test_def in Hfd. cbn [map_def dtype dbody] in Hfd.
    apply Bool.andb_true_iff in Hfd as [Hfty Hfbody].
    apply Bool.andb_false_iff in Hx as [Hx|Hx].
    + exact (Pty k Hhty Hx Hfty).
    + apply (Pbody (#|mfix| + k)).
      * rewrite cg_hyg_shift in Hhbody. exact Hhbody.
      * rewrite <- Nat.add_assoc. exact Hx.
      * rewrite cg_ofv_shiftn in Hfbody. rewrite <- Nat.add_assoc. exact Hfbody.
  - (* tPrim *)
    intros prim Hprim k Hh Hn Hf. cbn [on_free_vars noccur_between lift subst] in Hh, Hn, Hf.
    destruct prim as [tg [? | ? | ? | a]]; cbn -[shiftnP] in Hprim, Hh, Hn, Hf;
      try discriminate Hn.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in Hh as [Hh Hhty]. apply Bool.andb_true_iff in Hh as [Hhval Hhdef].
    apply Bool.andb_true_iff in Hf as [Hf Hfty]. apply Bool.andb_true_iff in Hf as [Hfval Hfdef].
    apply Bool.andb_false_iff in Hn as [Hn|Hn]; [apply Bool.andb_false_iff in Hn as [Hn|Hn]|].
    + apply (cg_All_forallb_false _ _ _ _ Hval Hn). intros x Hin IH Hx.
      apply (IH k); [exact (cg_forallb_In _ _ _ Hhval Hin) | exact Hx |].
      apply (cg_forallb_In _ _ _ Hfval). apply in_map. apply in_map. exact Hin.
    + exact (Hdef k Hhdef Hn Hfdef).
    + exact (Hty k Hhty Hn Hfty).
Qed.

(** ** 3. The free variables above a substituted block *)

Lemma cg_subst_scope_inv (P : nat -> bool) (ws : list term) :
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
    refine (cg_forallb_map_inv _ _ _ _ _ Hl _ H). intros x Px Hx. exact (Px k Hx).
  - (* tSort *) intros; reflexivity.
  - (* tProd *)
    intros na A IHA B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite cg_ofv_shiftn in H2 |- *.
    apply Bool.andb_true_iff; split; [exact (IHA k H1) | exact (IHB (S k) H2)].
  - (* tLambda *)
    intros na A IHA B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite cg_ofv_shiftn in H2 |- *.
    apply Bool.andb_true_iff; split; [exact (IHA k H1) | exact (IHB (S k) H2)].
  - (* tLetIn *)
    intros na b0 IHb ty IHty B IHB k H. cbn [subst on_free_vars] in H |- *.
    apply Bool.andb_true_iff in H as [H1 H]. apply Bool.andb_true_iff in H as [H2 H3].
    rewrite cg_ofv_shiftn in H3 |- *.
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
    { refine (cg_forallb_map_inv _ _ _ _ _ Hpar _ Hpa). intros x Px Hx. exact (Px k Hx). }
    apply Bool.andb_true_iff; split.
    { rewrite cg_ofv_shiftn in Hr |- *. rewrite Nat.add_assoc. exact (Hret _ Hr). }
    apply Bool.andb_true_iff; split; [exact Hcx|].
    apply Bool.andb_true_iff; split; [exact (IHc k Hc)|].
    refine (cg_forallb_map_inv _ _ _ _ _ Hbrs _ Hbr). intros br [Pctx Pbody] Hx.
    cbn [map_branch_k bcontext bbody id] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2]. apply Bool.andb_true_iff; split; [exact Hx1|].
    rewrite cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tProj *)
    intros pr c IHc k H. cbn [subst on_free_vars] in H |- *. exact (IHc k H).
  - (* tFix *)
    intros mfix idx Hm k H. cbn [subst on_free_vars] in H |- *. rewrite !length_map in H.
    refine (cg_forallb_map_inv _ _ _ _ _ Hm _ H). intros d [Pty Pbody] Hx.
    unfold test_def in Hx |- *. cbn [map_def dtype dbody] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
    apply Bool.andb_true_iff; split; [exact (Pty k Hx1)|].
    rewrite cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tCoFix *)
    intros mfix idx Hm k H. cbn [subst on_free_vars] in H |- *. rewrite !length_map in H.
    refine (cg_forallb_map_inv _ _ _ _ _ Hm _ H). intros d [Pty Pbody] Hx.
    unfold test_def in Hx |- *. cbn [map_def dtype dbody] in Hx.
    apply Bool.andb_true_iff in Hx as [Hx1 Hx2].
    apply Bool.andb_true_iff; split; [exact (Pty k Hx1)|].
    rewrite cg_ofv_shiftn in Hx2 |- *. rewrite Nat.add_assoc. exact (Pbody _ Hx2).
  - (* tPrim *)
    intros prim Hprim k H. cbn [subst on_free_vars] in H |- *.
    destruct prim as [tg [? | ? | ? | a]]; cbn -[shiftnP] in Hprim, H |- *; try reflexivity.
    destruct Hprim as [Hty [Hdef Hval]].
    apply Bool.andb_true_iff in H as [H H3]. apply Bool.andb_true_iff in H as [H1 H2].
    apply Bool.andb_true_iff; split; [apply Bool.andb_true_iff; split|].
    + refine (cg_forallb_map_inv _ _ _ _ _ Hval _ H1). intros y Py Hy. exact (Py k Hy).
    + exact (Hdef k H2).
    + exact (Hty k H3).
Qed.

(** ** 4. Substituting the identity readings back *)

Lemma cg_subst_idsn_lift (k : nat) (t : term) : subst (idsn k) 0 (lift k k t) = t.
Proof.
  revert t. induction k as [|k IH]; intros t.
  - cbn [idsn]. rewrite subst_empty. apply lift0_id.
  - cbn [idsn]. rewrite subst_app_simpl. rewrite idsn_length. cbn [Nat.add].
    rewrite (subst_reli_lift_id k k t (le_n k)). exact (IH t).
Qed.

(** ** 5. Substituting lifted identity readings *)

Lemma cg_subst_fresh_lift (m k : nat) (t : term) :
  subst (map (lift0 m) (idsn k)) 0 (lift (m + k) k t) = lift0 m t.
Proof.
  pose proof (distr_lift_subst (lift k k t) (idsn k) m 0) as E.
  rewrite cg_subst_idsn_lift in E. rewrite idsn_length, Nat.add_0_r in E.
  rewrite (simpl_lift t k k m k) in E by lia.
  symmetry; exact E.
Qed.

(** ** 6. Universe well-formedness of a code's term *)

Lemma cg_code_inv_wf_universes {cf : checker_flags} (Σ : global_env_ext) (e : code_entry) (c : code) :
  code_inv e c -> wf_universes Σ (inst_code e.(ce_inst) e.(ce_term)) ->
  wf_universes Σ c.(c_term).
Proof.
  unfold code_inv; cbv zeta. intros [ks [_ ht]] hr. revert ht.
  generalize (c_term c) as t.
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
          pose proof (cg_forallb_nth_some _ _ _ _ H Eb) as hb end.
        unfold test_branch in hb. apply andb_true_iff in hb as [_ hb]. exact hb.
      * match goal with H : forallb _ (pparams _) = true |- _ =>
          exact (cg_forallb_nth_some _ _ _ _ H ht) end.
      * injection ht as <-. assumption.
    + (* tProj *)
      destruct k as [|q]; cbn in ht; [injection ht as <-; assumption|discriminate ht].
    + (* tFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cg_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      cbn beta in hd. apply andb_true_iff in hd. exact (proj2 hd).
    + (* tCoFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cg_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      cbn beta in hd. apply andb_true_iff in hd. exact (proj2 hd).
Qed.

(** * A machine call returns the caller's roots renamed, never reshaped

  The shape of a root is the root with every heap address replaced by one constant address
  ([mp_root kc]). A renaming ([rn_*]), a collection, an allocation and every function of the
  machine give back roots of the shape of the roots they were given: each function pops
  exactly the frames it pushes, and threads the rest through calls that keep their shape. *)

Definition kc : haddr -> haddr := fun _ => HAddr xH.

(** Two root lists of one shape, less their first root. *)
Lemma sk_tl r r' rs rs' :
  mp_roots kc (r' :: rs') = mp_roots kc (r :: rs) -> mp_roots kc rs' = mp_roots kc rs.
Proof. intros h. exact (f_equal (@tl root) h). Qed.

(** Strip the frames a call pushed and popped, then chain the equations of the calls. *)
Local Ltac sk_fin :=
  repeat match goal with
         | h : mp_roots kc (_ :: _) = mp_roots kc (_ :: _) |- _ => apply sk_tl in h
         end;
  repeat match goal with
         | h : mp_roots kc ?a = mp_roots kc ?b |- mp_roots kc ?a = _ => rewrite h; clear h
         end;
  reflexivity.

(** ** A renaming keeps the shape of what it renames *)

Section SkRename.
  Context {G : Type} (f : haddr -> G -> cbn_res (haddr * G)).

  Lemma sk_rn_addrs : forall l g l' g', rn_addrs f l g = COk (l', g') -> map kc l' = map kc l.
  Proof.
    induction l as [|a l ih]; intros g l' g' he; simpl in he.
    - injection he as <- <-. reflexivity.
    - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      destruct (rn_addrs f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. cbn [map]. rewrite (ih _ _ _ e2). reflexivity.
  Qed.

  Lemma sk_rn_slot : forall x g x' g', rn_slot f x g = COk (x', g') -> mp_slot kc x' = mp_slot kc x.
  Proof.
    intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' he.
    - simpl in he. destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. reflexivity.
    - rewrite rn_slot_SInl in he.
      destruct (rn_slots f vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_slot]. f_equal.
      revert g vs' g1 e1.
      induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 e1; simpl in e1.
      + injection e1 as <- <-. reflexivity.
      + destruct (rn_slot f y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
        destruct (rn_slots f vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
        injection e1 as <- <-. cbn [map]. rewrite (hy _ _ _ ea), (ihl _ _ _ eb). reflexivity.
  Qed.

  Lemma sk_rn_slots : forall l g l' g',
    rn_slots f l g = COk (l', g') -> mp_slots kc l' = mp_slots kc l.
  Proof.
    unfold mp_slots. induction l as [|y l ih]; intros g l' g' he; simpl in he.
    - injection he as <- <-. reflexivity.
    - destruct (rn_slot f y g) as [[y' g1]|w] eqn:e1; [|discriminate].
      destruct (rn_slots f l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
      injection he as <- <-. cbn [map].
      rewrite (sk_rn_slot _ _ _ _ e1), (ih _ _ _ e2). reflexivity.
  Qed.

  Lemma sk_rn_env e g e' g' : rn_env f e g = COk (e', g') -> mp_env kc e' = mp_env kc e.
  Proof.
    intros he. unfold rn_env in he.
    destruct (rn_slots f (ev_vals e) g) as [[vs g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. unfold mp_env. cbn [ev_vals ev_nvals ev_goff].
    rewrite (sk_rn_slots _ _ _ _ e1). reflexivity.
  Qed.

  Lemma sk_rn_value v g v' g' : rn_value f v g = COk (v', g') -> mp_value kc v' = mp_value kc v.
  Proof.
    intros he. unfold rn_value in he.
    destruct v as [h sp|e c|e c i sp|e c i sp|h sp|e c|e c sp].
    - destruct (rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_addrs _ _ _ _ e1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_env _ _ _ _ E1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [mp_value].
      rewrite (sk_rn_env _ _ _ _ E1), (sk_rn_addrs _ _ _ _ E2). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [mp_value].
      rewrite (sk_rn_env _ _ _ _ E1), (sk_rn_addrs _ _ _ _ E2). reflexivity.
    - destruct (rn_addrs f sp g) as [[sp1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_addrs _ _ _ _ e1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      injection he as <- <-. cbn [mp_value]. rewrite (sk_rn_env _ _ _ _ E1). reflexivity.
    - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
      destruct (rn_addrs f sp g1) as [[sp1 g2]|w] eqn:E2; [|discriminate].
      injection he as <- <-. cbn [mp_value].
      rewrite (sk_rn_env _ _ _ _ E1), (sk_rn_addrs _ _ _ _ E2). reflexivity.
  Qed.

  Lemma sk_rn_cell cl g cl' g' : rn_cell f cl g = COk (cl', g') -> mp_cell kc cl' = mp_cell kc cl.
  Proof.
    intros he. unfold rn_cell in he. destruct cl as [vs n o c|v| |b].
    - destruct (rn_slots f vs g) as [[vs1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_cell]. rewrite (sk_rn_slots _ _ _ _ e1). reflexivity.
    - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. cbn [mp_cell]. rewrite (sk_rn_value _ _ _ _ e1). reflexivity.
    - injection he as <- <-. reflexivity.
    - destruct (f b g) as [[b1 g1]|w] eqn:e1; [|discriminate].
      injection he as <- <-. reflexivity.
  Qed.
End SkRename.

Lemma rn_root_skel {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (r : root) (g : G) r' g' :
  rn_root f r g = COk (r', g') -> mp_root kc r' = mp_root kc r.
Proof.
  intros he. unfold rn_root in he. destruct r as [a|x|e|v|l|l|cl].
  - destruct (f a g) as [[b g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. reflexivity.
  - destruct (rn_slot f x g) as [[x1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_slot f _ _ _ _ e1). reflexivity.
  - destruct (rn_env f e g) as [[e1 g1]|w] eqn:E1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_env f _ _ _ _ E1). reflexivity.
  - destruct (rn_value f v g) as [[v1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_value f _ _ _ _ e1). reflexivity.
  - destruct (rn_slots f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_slots f _ _ _ _ e1). reflexivity.
  - destruct (rn_addrs f l g) as [[l1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_addrs f _ _ _ _ e1). reflexivity.
  - destruct (rn_cell f cl g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
    injection he as <- <-. cbn [mp_root]. rewrite (sk_rn_cell f _ _ _ _ e1). reflexivity.
Qed.

Lemma rn_roots_skel {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (rs : list root) (g : G)
    rs' g' :
  rn_roots f rs g = COk (rs', g') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  revert g rs' g'. induction rs as [|r rs ih]; intros g rs' g' he; simpl in he.
  - injection he as <- <-. reflexivity.
  - destruct (rn_root f r g) as [[r1 g1]|w] eqn:e1; [|discriminate].
    destruct (rn_roots f rs g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
    injection he as <- <-. unfold mp_roots in *. cbn [map].
    rewrite (rn_root_skel f _ _ _ _ e1), (ih _ _ _ e2). reflexivity.
Qed.

(** ** A collection, and an allocation *)

Lemma collect_skel (rs : list root) (s : cbn_state) rs' s' :
  collect rs s = COk (rs', s') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  intros he. rewrite collect_eq in he.
  destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
              (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm g1]|w] eqn:e1;
    [|discriminate he].
  destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
    as [[rs2 g2]|w] eqn:e2; [|discriminate he].
  injection he as <- <-. exact (rn_roots_skel _ _ _ _ _ e2).
Qed.

Lemma alloc_skel cl rs s a rs' s' :
  alloc cl rs s = COk (a, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  intros he. destruct (gc_due s) eqn:eg.
  - rewrite (alloc_gc cl rs s eg) in he.
    destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate he].
    pose proof (collect_skel _ _ _ _ ec) as h1.
    destruct rs2 as [|[| | | | | |cl2] rs2]; try discriminate he.
    injection he as <- <- <-. exact (sk_tl _ _ _ _ h1).
  - rewrite (alloc_no_gc cl rs s eg) in he. injection he as <- <- <-. reflexivity.
Qed.

(** ** The machine *)

(** The first call whose answer [he] matches on: its answer is [COk (x, y, z)], named by [e]. *)
Local Ltac dcall he e x y z :=
  lazymatch type of he with
  | context [match ?t with COk _ => _ | CFail _ => _ end] =>
      destruct t as [[[x y] z]|?] eqn:e; [|discriminate he]
  end.

(** The decisions of a match or projection on a constructor: each test that fails fails. *)
Local Ltac dtests he :=
  repeat (match type of he with
          | context [if ?b then _ else _] => destruct b
          | context [match ?o with Some _ => _ | None => _ end] => destruct o
          | context [match ?m with O => _ | S _ => _ end] => destruct m
          end; try discriminate he).

Lemma push_fresh_skel : forall n lvl e1 e2 rs s r rs' s',
  push_fresh n lvl e1 e2 rs s = COk (r, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
Proof.
  induction n as [|n ih]; intros lvl e1 e2 rs s r rs' s' he; cbn [push_fresh] in he.
  - injection he as <- <- <-. reflexivity.
  - dcall he ea x1 rs1 s1.
    destruct rs1 as [|[| |f1| | | |] [|[| |f2| | | |] rs1]]; try discriminate he.
    pose proof (alloc_skel _ _ _ _ _ _ ea) as h1.
    pose proof (ih _ _ _ _ _ _ _ _ he) as h2. sk_fin.
Qed.

Section SkMachine.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat).

  Lemma gam_skel j rs s a rs' s' :
    gam X_type X Γ nctx j rs s = COk (a, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold gam in he. cbv zeta in he.
    destruct (PTree.get (key_of_succ_nat j) s.(st_gam)) as [a0|].
    { injection he as <- <- <-. reflexivity. }
    destruct (nth_error Γ j) as [decl|]; [|discriminate he].
    destruct (decl_body decl) as [b|].
    - destruct (new_entry X_type X b [] s) as [c s1].
      cbv beta iota in he. dcall he ea a1 rs1 s2.
      injection he as <- <- <-. exact (alloc_skel _ _ _ _ _ _ ea).
    - cbv beta iota in he. dcall he ea a1 rs1 s2.
      injection he as <- <- <-. exact (alloc_skel _ _ _ _ _ _ ea).
  Qed.

  Lemma env_var_skel n e rs s x rs' s' :
    env_var X_type X Γ nctx n e rs s = COk (x, rs', s') ->
    mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold env_var in he.
    destruct (nth_error e.(ev_vals) n) as [y|].
    - injection he as <- <- <-. reflexivity.
    - dcall he eg a1 rs1 s1. injection he as <- <- <-. exact (gam_skel _ _ _ _ _ _ eg).
  Qed.

  Lemma arg_slot_skel e c rs s x rs' s' :
    arg_slot X_type X Γ nctx e c rs s = COk (x, rs', s') ->
    mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold arg_slot in he.
    destruct (c_term c); try (injection he as <- <- <-; reflexivity).
    exact (env_var_skel _ _ _ _ _ _ _ he).
  Qed.

  Lemma materialize_skel x rs s a rs' s' :
    materialize X_type X x rs s = COk (a, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold materialize in he.
    destruct x as [a0|vs n o c]; [injection he as <- <- <-; reflexivity|].
    destruct (c_term c) eqn:ec; try exact (alloc_skel _ _ _ _ _ _ he).
    - lazymatch type of he with
      | context [delta X_type X ?kn ?ui s] =>
        destruct (delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
      end; exact (alloc_skel _ _ _ _ _ _ he).
    - lazymatch type of he with
      | context [nth_error ?m ?i] => destruct (nth_error m i)
      end; exact (alloc_skel _ _ _ _ _ _ he).
  Qed.

  Lemma bind_skel x body rs s y rs' s' :
    bind X_type X x body rs s = COk (y, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros he. unfold bind in he. destruct x as [a0|vals n o c].
    - injection he as <- <- <-. reflexivity.
    - destruct (once_body body s) as [b s1]. destruct b.
      + injection he as <- <- <-. reflexivity.
      + dcall he em a1 rs1 s2. injection he as <- <- <-.
        exact (materialize_skel _ _ _ _ _ _ em).
  Qed.

  Lemma mat_all_skel : forall d l rs s al rs' s',
    mat_all X_type X d l rs s = COk (al, rs', s') -> mp_roots kc rs' = mp_roots kc rs.
  Proof.
    intros d. induction d as [|k ih]; intros l rs s al rs' s' he;
      destruct l as [|x l]; cbn [mat_all] in he.
    1,3: injection he as <- <- <-; reflexivity.
    - discriminate he.
    - dcall he em a1 rs1 s1.
      destruct rs1 as [|[| | | |l1| |] rs1]; try discriminate he.
      pose proof (materialize_skel _ _ _ _ _ _ em) as h1.
      dcall he em2 al1 rs2 s2.
      destruct rs2 as [|[a0| | | | | |] rs2]; try discriminate he.
      injection he as <- <- <-.
      pose proof (ih tt _ _ _ _ _ _ em2) as h2. sk_fin.
  Qed.

  Lemma push_fix_cells_skel : forall n e c i acc rs s e' rs' s',
    push_fix_cells e c i n acc rs s = COk (e', rs', s') ->
    mp_roots kc rs' = mp_roots kc rs.
  Proof.
    induction n as [|n ih]; intros e c i acc rs s e' rs' s' he;
      cbn [push_fix_cells] in he.
    - injection he as <- <- <-. reflexivity.
    - dcall he ea a1 rs1 s1.
      destruct rs1 as [|[| |e1| | | |] [|[| |acc1| | | |] rs1]]; try discriminate he.
      pose proof (alloc_skel _ _ _ _ _ _ ea) as h1.
      pose proof (ih _ _ _ _ _ _ _ _ _ he) as h2. sk_fin.
  Qed.

  (** The five functions of the machine at one fuel. *)
  Definition sk_m (d : cbn_fuel) : Prop :=
    (forall a rs s v rs' s', force X_type X Γ nctx d a rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall x stk rs s v rs' s', eval_slot X_type X Γ nctx d x stk rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall e c stk rs s v rs' s', whnf X_type X Γ nctx d e c stk rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall e c mfix idx stk rs s v rs' s',
         whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = COk (v, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs)
    /\ (forall v stk rs s w rs' s', apply X_type X Γ nctx d v stk rs s = COk (w, rs', s') ->
       mp_roots kc rs' = mp_roots kc rs).

  Lemma sk_machine : forall d, sk_m d.
  Proof.
    intros d. induction d as [|k ih].
    - (* FO: every call fails, except [apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros a rs s v rs' s' he. cbn [force] in he. discriminate he.
      + intros x stk rs s v rs' s' he. cbn [eval_slot] in he. discriminate he.
      + intros e c stk rs s v rs' s' he. cbn [whnf] in he. discriminate he.
      + intros e c mfix idx stk rs s v rs' s' he. cbn [whnf_fix] in he. discriminate he.
      + intros v stk rs s w rs' s' he. cbn [apply] in he.
        destruct stk; [injection he as <- <- <-; reflexivity|discriminate he].
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      split; [|split; [|split; [|split]]].
      + (* force *)
        intros a0 rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [force] in he.
        destruct (heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct cl as [vs n o c|vd| |b]; try discriminate he.
        * (* a suspension: evaluate it, then write the value back *)
          destruct (heap_upd a0 CBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          dcall he ew vw rsw sw.
          destruct rsw as [|[ar| | | | | |] rsw]; try discriminate he.
          destruct (heap_upd ar (CDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as <- <- <-.
          pose proof (IHw _ _ _ _ _ _ _ _ ew) as h1. sk_fin.
        * (* a value: the heap has it *)
          injection he as <- <- <-. reflexivity.
      + (* eval_slot *)
        intros x stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [eval_slot] in he.
        destruct x as [a|vs n o c].
        * dcall he ef vf rsf sf.
          destruct rsf as [|[| | | |lk| |] rsf]; try discriminate he.
          pose proof (IHf _ _ _ _ _ _ ef) as h1.
          pose proof (IHa _ _ _ _ _ _ _ he) as h2. sk_fin.
        * exact (IHw _ _ _ _ _ _ _ _ he).
      + (* whnf *)
        intros e c stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [whnf] in he.
        destruct (tick s0) as [st|] eqn:etick; [|discriminate he].
        destruct (c_term c) as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|kn ui
                               |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
          eqn:ec; try solve [discriminate he].
        * (* tRel *)
          dcall he ev xr rsr sr.
          destruct rsr as [|[| | | |lk| |] rsr]; try discriminate he.
          pose proof (env_var_skel _ _ _ _ _ _ _ ev) as h1.
          pose proof (IHs _ _ _ _ _ _ _ he) as h2. sk_fin.
        * (* tSort *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
        * (* tProd *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
        * (* tLambda *)
          destruct stk as [|xh stk'].
          -- injection he as <- <- <-. reflexivity.
          -- dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             pose proof (bind_skel _ _ _ _ _ _ _ eb) as h1.
             pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin.
        * (* tLetIn *)
          dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          pose proof (arg_slot_skel _ _ _ _ _ _ _ ea) as h1.
          dcall he eb xb rsb sb.
          destruct rsb as [|[| |e2| | | |] [|[| | | |k2| |] rsb]]; try discriminate he.
          pose proof (bind_skel _ _ _ _ _ _ _ eb) as h2.
          pose proof (IHw _ _ _ _ _ _ _ _ he) as h3. sk_fin.
        * (* tApp *)
          dcall he ea xa rsa sa.
          destruct rsa as [|[| |e1| | | |] [|[| | | |k1| |] rsa]]; try discriminate he.
          pose proof (arg_slot_skel _ _ _ _ _ _ _ ea) as h1.
          pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin.
        * (* tConst *)
          destruct (delta X_type X kn ui st) as [[r s1]|w] eqn:ed; [|discriminate he].
          destruct r as [c'|].
          -- exact (IHw _ _ _ _ _ _ _ _ he).
          -- dcall he em sp rs1 s2.
             pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
             injection he as <- <- <-. exact h1.
        * (* tInd *)
          dcall he em sp rs1 s1.
          pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. exact h1.
        * (* tConstruct *)
          dcall he em sp rs1 s1.
          pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. exact h1.
        * (* tCase *)
          dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          pose proof (IHw _ _ _ _ _ _ _ _ ewc) as h1.
          destruct vc as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { destruct hd; try discriminate he. dtests he.
               pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin. }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h2;
               injection he as <- <- <-; sk_fin.
        * (* tProj *)
          dcall he ewc vc rsc sc.
          destruct rsc as [|[| |e1| | | |] [|[| | | |k1| |] rsc]]; try discriminate he.
          pose proof (IHw _ _ _ _ _ _ _ _ ewc) as h1.
          destruct vc as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { destruct hd; try discriminate he. dtests he.
               pose proof (IHs _ _ _ _ _ _ _ he) as h2. sk_fin. }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h2;
               injection he as <- <- <-; sk_fin.
        * (* tFix *)
          exact (IHx _ _ _ _ _ _ _ _ _ _ he).
        * (* tPrim *)
          destruct stk; [|discriminate he]. injection he as <- <- <-. reflexivity.
      + (* whnf_fix *)
        intros e c mfix idx stk rs0 s0 v0 rs' s' he.
        cbv beta iota zeta delta [whnf_fix] in he.
        destruct (nth_error mfix idx) as [def|]; [|discriminate he].
        destruct (nth_error stk (rarg def)) as [x|].
        * dcall he ea a1 rs1 s1.
          destruct rs1 as [|[| |e1| | | |] [|[| | | |k1| |] rs1]]; try discriminate he.
          pose proof (materialize_skel _ _ _ _ _ _ ea) as h1.
          dcall he ef vf rsf sf.
          destruct rsf as [|[| |e2| | | |] [|[| | | |k2| |] rsf]]; try discriminate he.
          pose proof (IHf _ _ _ _ _ _ ef) as h2.
          destruct vf as [hd sp| | | |nn sp| |]; try discriminate he.
          1: { (* the guard holds: the forced constructor goes to a fresh cell *)
               destruct hd; try discriminate he.
               dcall he ea2 a2 rs2 s2.
               destruct rs2 as [|[| |e3| | | |] [|[| | | |k3| |] rs2]]; try discriminate he.
               pose proof (alloc_skel _ _ _ _ _ _ ea2) as h3.
               dcall he ep e4 rs3 s3.
               destruct rs3 as [|[| | | |k4| |] rs3]; try discriminate he.
               pose proof (push_fix_cells_skel _ _ _ _ _ _ _ _ _ _ ep) as h4.
               pose proof (IHw _ _ _ _ _ _ _ _ he) as h5. sk_fin. }
          all: dcall he em sp1 rsm sm;
               destruct rsm as [|[| |e5| | | |] rsm]; try discriminate he;
               pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h3;
               injection he as <- <- <-; sk_fin.
        * dcall he em sp rs1 s1.
          destruct rs1 as [|[| |e1| | | |] rs1]; try discriminate he.
          pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1.
          injection he as <- <- <-. sk_fin.
      + (* apply *)
        intros v stk rs0 s0 w rs' s' he.
        cbv beta iota zeta delta [apply] in he.
        destruct stk as [|y stk']; [injection he as <- <- <-; reflexivity|].
        destruct v as [hd sp|e c|e c idx sp|e c idx sp|nn sp|e c|e c sp]; try discriminate he.
        2: { (* a lambda: beta *)
             destruct (c_term c); try discriminate he.
             dcall he eb xb rsb sb.
             destruct rsb as [|[| |e1| | | |] [|[| | | |k1| |] rsb]]; try discriminate he.
             pose proof (bind_skel _ _ _ _ _ _ _ eb) as h1.
             pose proof (IHw _ _ _ _ _ _ _ _ he) as h2. sk_fin. }
        2: { (* a fixpoint: its spine goes back on the stack *)
             destruct (c_term c); try discriminate he.
             exact (IHx _ _ _ _ _ _ _ _ _ _ he). }
        all: (* the spine grows *)
             dcall he em sp1 rsm sm;
             destruct rsm as [|[| | |v1| | |] rsm]; try discriminate he;
             pose proof (mat_all_skel _ _ _ _ _ _ _ em) as h1;
             destruct (add_spine v1 sp1) as [v2|] eqn:eadd; [|discriminate he];
             injection he as <- <- <-; sk_fin.
  Qed.
End SkMachine.

Lemma machine_skel {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) : forall d,
  (forall a rs s v rs' s', force X_type X Γ nctx d a rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall x stk rs s v rs' s', eval_slot X_type X Γ nctx d x stk rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall e c stk rs s v rs' s', whnf X_type X Γ nctx d e c stk rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall e c mfix idx stk rs s v rs' s',
       whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = COk (v, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs)
  /\ (forall v stk rs s w rs' s', apply X_type X Γ nctx d v stk rs s = COk (w, rs', s') ->
     mp_roots kc rs' = mp_roots kc rs).
Proof. exact (sk_machine X_type X Γ nctx). Qed.


(** * The comparison on ghost readings

  A statement that reads the comparison's inputs with a heap-following read-back is false
  ([PCUICCallByNeedCounterexamples.term_seam_false]). This part states the comparison
  against the ghost reading of [machine_sound]
  ([PCUICCallByNeedSoundEval]) at the master level of [PCUICCallByNeedSoundLevel]: the state
  satisfies [minv L Q], where [L <= Q] is the comparison's logical level and [Q] the level of
  the ghost.

  Every function [f] of the comparison gets a statement [spec_f d], made of two parts.
  - The state part ([post]): from [minv L Q lo G s] and readings of the inputs under [G] at
    [Q], an answer [COk (b, rs', s')] comes with a master level [Q' >= Q] and a ghost [G'] such
    that [minv L Q' lo' G' s'] holds and every root of the caller keeps its reading, lifted by
    [Q' - Q] ([grq]). The master level rises when the comparison crosses binders: a fresh
    variable at level [L] must be below [Q] ([hwf]), and [gok_raise] lifts the ghost.
  - The conversion part ([cq]): if [b = true], whenever each of the two readings is the lift
    by [Q - L] of a term scoped at [L], those two terms are convertible at the comparison's
    [conv_pb] in [Γ ,,, Δ] for every [Δ] of length [L - nctx]. Nothing is said of [false].
  The lifts are a premise of the conversion part, not of the call: the state part needs
  nothing of the readings beyond their existence. That matters for [same_code_cells], which
  compares environment slots whose readings are lifts only where the code uses them. *)

Section ConvGhost.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (Σ : global_env_ext).
  Context (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).
  Context (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : ctx_hyg Γ).
  Context (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                    PCUICCallByNeedSoundHook.consts_okb Σ b).

  Local Notation xpred0 := (fun _ : nat => false) (only parsing).
  Local Notation xpredT := (fun _ : nat => true) (only parsing).
  Local Notation gcok := PCUICCallByNeedSoundEval.cok.
  Local Notation MI := (minv X_type X Γ nctx Σ).

  (** ** Lifts *)

  Lemma lift0_lift0 (a b : nat) (t : term) : lift0 a (lift0 b t) = lift0 (a + b) t.
  Proof. apply simpl_lift; lia. Qed.

  Lemma map_lift0_lift0 (a b : nat) (ts : list term) :
    map (lift0 a) (map (lift0 b) ts) = map (lift0 (a + b)) ts.
  Proof. rewrite map_map. apply map_ext. intros t. apply lift0_lift0. Qed.

  Lemma map_lift0_0 (ts : list term) : map (lift0 0) ts = ts.
  Proof. induction ts as [|t ts ih]; cbn; [reflexivity|]. rewrite lift0_id, ih. reflexivity. Qed.

  Lemma rn_comp (f g : nat -> nat) (t : term) :
    rename f (rename g t) = rename (fun i => f (g i)) t.
  Proof. exact (rename_compose f g t). Qed.

  Lemma rn_id (t : term) : rename ren_id t = t.
  Proof. exact (rename_ren_id t). Qed.

  (** [unl m] undoes a lift by [m]. *)
  Definition unl (m : nat) (t : term) : term := rename (fun i => i - m) t.

  Lemma unl_lift0 (m : nat) (u : term) : unl m (lift0 m u) = u.
  Proof.
    unfold unl. rewrite lift_rename, rn_comp.
    transitivity (rename ren_id u); [|apply rn_id].
    apply rename_ext. intros i. unfold lift_renaming, ren_id. cbn. lia.
  Qed.

  Lemma lift0_inj (m : nat) (a b : term) : lift0 m a = lift0 m b -> a = b.
  Proof. intros h. rewrite <- (unl_lift0 m a), <- (unl_lift0 m b), h. reflexivity. Qed.

  (** [scl L u]: [u] is scoped at level [L], so open in [Γ ,,, Δ] when [#|Δ| = L - nctx].
    [inq m Q]: the free variables of the lift by [m] of a term scoped at [Q - m]. *)
  Definition scl (L : nat) (u : term) : bool := on_free_vars (shiftnP L xpred0) u.

  Definition inq (m Q : nat) (i : nat) : bool := (m <=? i) && (i <? Q).

  Lemma inq_lift0 (m L : nat) (u : term) : scl L u -> on_free_vars (inq m (L + m)) (lift0 m u).
  Proof.
    unfold scl. intros h. rewrite lift_rename, PCUICOnFreeVarsConv.on_free_vars_rename.
    eapply on_free_vars_impl; [|exact h].
    intros i hi. unfold shiftnP in hi. cbv beta. unfold inq, lift_renaming. cbn.
    destruct (Nat.ltb_spec i L) as [hl|hl]; cbn in hi; [|discriminate hi].
    apply andb_true_iff. split; [apply Nat.leb_le; lia|apply Nat.ltb_lt; lia].
  Qed.

  Lemma inq_unl (m Q : nat) (t : term) :
    on_free_vars (inq m Q) t -> t = lift0 m (unl m t) /\ scl (Q - m) (unl m t).
  Proof.
    intros h. split.
    - unfold unl. rewrite lift_rename, rn_comp.
      transitivity (rename ren_id t); [symmetry; apply rn_id|].
      apply (PCUICOnFreeVarsConv.rename_ext_cond (inq m Q)); [|exact h].
      intros i hi. unfold inq in hi. apply andb_true_iff in hi as [h1 _].
      apply Nat.leb_le in h1. unfold lift_renaming, ren_id. cbn. lia.
    - unfold unl, scl. rewrite PCUICOnFreeVarsConv.on_free_vars_rename.
      eapply on_free_vars_impl; [|exact h].
      intros i hi. unfold inq in hi. apply andb_true_iff in hi as [h1 h2].
      apply Nat.leb_le in h1. apply Nat.ltb_lt in h2. unfold shiftnP. cbv beta.
      destruct (Nat.ltb_spec (i - m) (Q - m)); [reflexivity|lia].
  Qed.

  (** ** What a [true] claims *)

  Definition cv (L : nat) (pb : conv_pb) (u1 u2 : term) : Prop :=
    forall Δ : context, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
      ∥ Σ ;;; Γ ,,, Δ ⊢ u1 ≤[pb] u2 ∥.

  Definition cq (L Q : nat) (pb : conv_pb) (t1 t2 : term) : Prop :=
    forall u1 u2 : term, t1 = lift0 (Q - L) u1 -> t2 = lift0 (Q - L) u2 ->
      scl L u1 -> scl L u2 -> cv L pb u1 u2.

  Definition cvs (L : nat) (us1 us2 : list term) : Prop :=
    forall Δ : context, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
      ∥ ws_cumul_pb_terms Σ (Γ ,,, Δ) us1 us2 ∥.

  Definition cqs (L Q : nat) (ts1 ts2 : list term) : Prop :=
    forall us1 us2 : list term,
      ts1 = map (lift0 (Q - L)) us1 -> ts2 = map (lift0 (Q - L)) us2 ->
      forallb (scl L) us1 -> forallb (scl L) us2 -> cvs L us1 us2.

  Lemma scl_open (L : nat) (Δ : context) (u : term) :
    nctx <= L -> #|Δ| = L - nctx -> scl L u -> is_open_term (Γ ,,, Δ) u.
  Proof.
    intros hL hΔ h. rewrite app_context_length, hΔ, <- hnctx.
    replace (L - nctx + nctx) with L by lia. exact h.
  Qed.

  Lemma cq_refl (L Q : nat) (pb : conv_pb) (t : term) : nctx <= L -> cq L Q pb t t.
  Proof.
    intros hL u1 u2 e1 e2 h1 h2 Δ hΔ hcl. rewrite e1 in e2. apply lift0_inj in e2. subst u2.
    constructor. apply ws_cumul_pb_refl; [exact hcl|exact (scl_open L Δ u1 hL hΔ h1)].
  Qed.

  Lemma cq_lift (L Q Q' : nat) (pb : conv_pb) (t1 t2 : term) :
    L <= Q -> Q <= Q' ->
    cq L Q' pb (lift0 (Q' - Q) t1) (lift0 (Q' - Q) t2) -> cq L Q pb t1 t2.
  Proof.
    intros hLQ hQ h u1 u2 e1 e2 h1 h2. apply h; [| |exact h1|exact h2].
    - rewrite e1, lift0_lift0. f_equal. lia.
    - rewrite e2, lift0_lift0. f_equal. lia.
  Qed.

  Lemma cqs_lift (L Q Q' : nat) (ts1 ts2 : list term) :
    L <= Q -> Q <= Q' ->
    cqs L Q' (map (lift0 (Q' - Q)) ts1) (map (lift0 (Q' - Q)) ts2) -> cqs L Q ts1 ts2.
  Proof.
    intros hLQ hQ h us1 us2 e1 e2 h1 h2. apply h; [| |exact h1|exact h2].
    - rewrite e1, map_lift0_lift0. f_equal. f_equal. lia.
    - rewrite e2, map_lift0_lift0. f_equal. f_equal. lia.
  Qed.

  (** ** The caller's roots across a call that may raise the master level *)

  Definition gpq (Q Q' : nat) (G G' : ghost) (r r' : root) : Prop :=
    match r, r' with
    | RA a, RA a' => forall t, G a = Some t -> G' a' = Some (lift0 (Q' - Q) t)
    | RSl x, RSl x' =>
      forall t, g_slot nctx Q G x t -> g_slot nctx Q' G' x' (lift0 (Q' - Q) t)
    | RE e, RE e' =>
      e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
      /\ forall ts, g_slots nctx Q G e.(ev_vals) ts ->
           g_slots nctx Q' G' e'.(ev_vals) (map (lift0 (Q' - Q)) ts)
    | RV v, RV v' =>
      forall t, g_value nctx Q G v t -> g_value nctx Q' G' v' (lift0 (Q' - Q) t)
    | RSk l, RSk l' =>
      forall ts, g_slots nctx Q G l ts -> g_slots nctx Q' G' l' (map (lift0 (Q' - Q)) ts)
    | RSp l, RSp l' => forall ts, g_addrs G l ts -> g_addrs G' l' (map (lift0 (Q' - Q)) ts)
    | RC cl, RC cl' =>
      forall t, g_cell nctx Q G cl t -> g_cell nctx Q' G' cl' (lift0 (Q' - Q) t)
    | _, _ => False
    end.

  (** Every root keeps its reading, lifted by [Q' - Q], and its shape ([machine_skel]): only
    its addresses change. *)
  Definition grq (Q Q' : nat) (G G' : ghost) (rs rs' : list root) : Prop :=
    gcx G G' /\ Forall2 (gpq Q Q' G G') rs rs' /\ mp_roots kc rs' = mp_roots kc rs.

  Lemma gpq_of_gpres Q G G' r r' : gpres nctx Q G G' r r' -> gpq Q Q G G' r r'.
  Proof.
    intros h. destruct r, r'; cbn in h |- *; try contradiction; rewrite Nat.sub_diag.
    all: first
      [ intros t ht; rewrite lift0_id; exact (h _ ht)
      | intros ts ht; rewrite map_lift0_0; exact (h _ ht)
      | destruct h as (a1 & b1 & c1); split; [exact a1|]; split; [exact b1|];
        intros ts ht; rewrite map_lift0_0; exact (c1 _ ht) ].
  Qed.

  Lemma grq_of_gren Q G G' rs rs' :
    gren nctx Q G G' rs rs' -> mp_roots kc rs' = mp_roots kc rs -> grq Q Q G G' rs rs'.
  Proof.
    intros [hc hf] hk. split; [exact hc|]. split; [|exact hk]. clear hk.
    induction hf; constructor; [apply gpq_of_gpres; assumption|assumption].
  Qed.

  Lemma grq_refl Q G rs : grq Q Q G G rs rs.
  Proof. apply grq_of_gren; [apply gren_refl|reflexivity]. Qed.

  Lemma gpq_trans Q Q1 Q2 G G1 G2 r r1 r2 :
    Q <= Q1 -> Q1 <= Q2 ->
    gpq Q Q1 G G1 r r1 -> gpq Q1 Q2 G1 G2 r1 r2 -> gpq Q Q2 G G2 r r2.
  Proof.
    intros hq1 hq2 h1 h2.
    assert (e : Q2 - Q = (Q2 - Q1) + (Q1 - Q)) by lia.
    destruct r, r1; cbn in h1; try contradiction; destruct r2; cbn in h2 |- *;
      try contradiction; rewrite e.
    all: first
      [ intros t ht; rewrite <- lift0_lift0; exact (h2 _ (h1 _ ht))
      | intros ts ht; rewrite <- map_lift0_lift0; exact (h2 _ (h1 _ ht))
      | destruct h1 as (a1 & b1 & c1), h2 as (a2 & b2 & c2);
        split; [congruence|]; split; [congruence|];
        intros ts ht; rewrite <- map_lift0_lift0; exact (c2 _ (c1 _ ht)) ].
  Qed.

  Lemma grq_trans Q Q1 Q2 G G1 G2 rs rs1 rs2 :
    Q <= Q1 -> Q1 <= Q2 ->
    grq Q Q1 G G1 rs rs1 -> grq Q1 Q2 G1 G2 rs1 rs2 -> grq Q Q2 G G2 rs rs2.
  Proof.
    intros hq1 hq2 [hc1 [hf1 hk1]] [hc2 [hf2 hk2]].
    split; [intros i e hi; exact (hc2 _ _ (hc1 _ _ hi))|].
    split; [|congruence].
    clear hk1 hk2.
    revert rs2 hf2. induction hf1 as [|r r1 l l1 hp hf ih]; intros rs2 hf2;
      inversion hf2; subst; constructor.
    - eapply gpq_trans; eassumption.
    - apply ih. assumption.
  Qed.

  Lemma grq_cons_inv_skel Q Q' G G' r rs rs1 :
    grq Q Q' G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ gpq Q Q' G G' r r' /\ grq Q Q' G G' rs rs'
      /\ mp_root kc r' = mp_root kc r.
  Proof.
    intros [hc [hf hk]]. destruct rs1 as [|r' rs']; [inversion hf|].
    exists r', rs'. split; [reflexivity|]. cbn in hk. injection hk as hk1 hk2.
    inversion hf; subst. split; [assumption|]. split; [|exact hk1].
    split; [exact hc|split; assumption].
  Qed.

  Lemma grq_cons_inv Q Q' G G' r rs rs1 :
    grq Q Q' G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ gpq Q Q' G G' r r' /\ grq Q Q' G G' rs rs'.
  Proof.
    intros h. destruct (grq_cons_inv_skel _ _ _ _ _ _ _ h) as (r' & rs' & e & h1 & h2 & _).
    exists r', rs'. split; [exact e|split; assumption].
  Qed.

  Lemma gpq_RSk_inv Q Q' G G' l r :
    gpq Q Q' G G' (RSk l) r ->
    exists l', r = RSk l'
      /\ forall ts, g_slots nctx Q G l ts -> g_slots nctx Q' G' l' (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RSp_inv Q Q' G G' l r :
    gpq Q Q' G G' (RSp l) r ->
    exists l', r = RSp l' /\ forall ts, g_addrs G l ts -> g_addrs G' l' (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RSl_inv Q Q' G G' x r :
    gpq Q Q' G G' (RSl x) r ->
    exists x', r = RSl x'
      /\ forall t, g_slot nctx Q G x t -> g_slot nctx Q' G' x' (lift0 (Q' - Q) t).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RV_inv Q Q' G G' v r :
    gpq Q Q' G G' (RV v) r ->
    exists v', r = RV v'
      /\ forall t, g_value nctx Q G v t -> g_value nctx Q' G' v' (lift0 (Q' - Q) t).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpq_RE_inv Q Q' G G' e r :
    gpq Q Q' G G' (RE e) r ->
    exists e', r = RE e' /\ e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
      /\ forall ts, g_slots nctx Q G e.(ev_vals) ts ->
           g_slots nctx Q' G' e'.(ev_vals) (map (lift0 (Q' - Q)) ts).
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  (** ** Raising the master level *)

  Lemma rwf_mono Q Q' r : Q <= Q' -> rwf Q r -> rwf Q' r.
  Proof.
    intros h. destruct r; cbn; intros hw; try exact I;
      [exact (vwf_mono _ _ _ h hw)|exact (cwf_mono _ _ _ h hw)].
  Qed.

  Lemma rwfs_mono Q Q' rs : Q <= Q' -> Forall (rwf Q) rs -> Forall (rwf Q') rs.
  Proof.
    intros h hr. induction hr as [|r rs hr0 _ ih]; constructor; [|exact ih].
    exact (rwf_mono _ _ _ h hr0).
  Qed.

  Lemma gpq_raise Q n G r : nctx <= Q -> rwf Q r -> gpq Q (Q + n) G (gshift n G) r r.
  Proof.
    intros hQ hw. unfold gpq. replace (Q + n - Q) with n by lia.
    destruct r; cbn in hw.
    - intros t ht. cbn. rewrite ht. reflexivity.
    - intros t ht. exact (proj1 (g_slot_shift nctx Q n hQ G) _ _ ht).
    - split; [reflexivity|]. split; [reflexivity|].
      intros ts ht. exact (proj1 (proj2 (g_slot_shift nctx Q n hQ G) _ _ ht)).
    - intros t ht. exact (g_value_shift nctx Q n hQ G _ _ hw ht).
    - intros ts ht. exact (proj1 (proj2 (g_slot_shift nctx Q n hQ G) _ _ ht)).
    - intros ts ht. apply g_addrs_shift. exact ht.
    - intros t ht. eapply g_cell_shift; eassumption.
  Qed.

  Lemma grq_raise Q n G rs : nctx <= Q -> Forall (rwf Q) rs -> grq Q (Q + n) G (gshift n G) rs rs.
  Proof.
    intros hQ hw. split; [intros i e hi; exact hi|]. split; [|reflexivity].
    induction hw; constructor; [apply gpq_raise; assumption|assumption].
  Qed.

  Lemma minv_raise L Q n lo G s : MI L Q lo G s -> MI L (Q + n) lo (gshift n G) s.
  Proof.
    intros [hL hQ hok hw].
    constructor; [exact hL|lia| |exact (hwf_mono Q (Q + n) s ltac:(lia) hw)].
    exact (gok_raise X_type X Γ nctx Σ wfΣ hnctx hΓ hhyg Q n lo G s ltac:(lia) hw hok).
  Qed.

  (** ** The state part of every statement *)

  Definition post (L Q : nat) (G : ghost) (rs : list root) (s' : cbn_state) (rs' : list root)
    : Prop :=
    exists Q' lo' G', Q <= Q' /\ MI L Q' lo' G' s' /\ Forall (rwf Q') rs'
      /\ grq Q Q' G G' rs rs'.

  Lemma post_refl L Q lo G rs s : MI L Q lo G s -> Forall (rwf Q) rs -> post L Q G rs s rs.
  Proof.
    intros hm hr. exists Q, lo, G. split; [lia|]. split; [exact hm|].
    split; [exact hr|apply grq_refl].
  Qed.

  Lemma post_compose L Q Q1 G G1 rs rs1 s' rs' :
    Q <= Q1 -> grq Q Q1 G G1 rs rs1 -> post L Q1 G1 rs1 s' rs' -> post L Q G rs s' rs'.
  Proof.
    intros hq hg (Q2 & lo2 & G2 & hq2 & hm & hr & hg2). exists Q2, lo2, G2.
    split; [lia|]. split; [exact hm|]. split; [exact hr|]. eapply grq_trans; eassumption.
  Qed.

  (** A sub-call answered [false]: the caller drops the two roots it pushed. *)
  Lemma post_drop2 L Q G r1 r2 rs s' rs' :
    post L Q G (r1 :: r2 :: rs) s' rs' -> post L Q G rs s' (skipn 2 rs').
  Proof.
    intros (Q1 & lo1 & G1 & hq & hm & hr & hg).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hg) as (q1 & rsA & -> & _ & hgA).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & _ & hgB).
    exists Q1, lo1, G1. split; [exact hq|]. split; [exact hm|]. cbn [skipn].
    split; [exact (Forall_inv_tail (Forall_inv_tail hr))|exact hgB].
  Qed.

  (** ** The same-code rule, cell by cell

    [cagree L Q a i ts1 ts2]: at each position of the two slot lists, either the code [a]
    does not use the slot, or the two readings are convertible in the sense of [cq]. *)
  Inductive cagree (L Q : nat) (a : term) : nat -> list term -> list term -> Prop :=
  | cagree_nil i : cagree L Q a i [] []
  | cagree_cons i u1 u2 l1 l2 :
      (noccur_between i 1 a = true \/ cq L Q Conv u1 u2) ->
      cagree L Q a (S i) l1 l2 -> cagree L Q a i (u1 :: l1) (u2 :: l2).

  Lemma cagree_lift L Q Q' a i l1 l2 :
    L <= Q -> Q <= Q' ->
    cagree L Q' a i (map (lift0 (Q' - Q)) l1) (map (lift0 (Q' - Q)) l2) -> cagree L Q a i l1 l2.
  Proof.
    intros hL hQ. revert i l2. induction l1 as [|u1 l1 ih]; intros i [|u2 l2] h; cbn in h;
      inversion h as [i0|i0 v1 v2 m1 m2 hd hl]; subst.
    - constructor.
    - constructor; [|exact (ih _ _ hl)].
      destruct hd as [hd|hd]; [left; exact hd|right; exact (cq_lift _ _ _ _ _ _ hL hQ hd)].
  Qed.

  Definition spec_slot (d : cbn_fuel) : Prop :=
    forall L Q lo G pb x1 x2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_slot nctx Q G x1 t1 -> g_slot nctx Q G x2 t2 ->
      conv_slot X_type X Γ nctx d L pb x1 x2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  Definition spec_scc (d : cbn_fuel) : Prop :=
    forall L Q lo G a i l1 l2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_slots nctx Q G l1 ts1 -> g_slots nctx Q G l2 ts2 ->
      same_code_cells X_type X Γ nctx d L a i l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cagree L Q a i ts1 ts2).

  (** [same_code_cells] skips a position whose two slots are one address (one reading) or
    whose slot the code does not use, and compares every other position with [conv_slot]. *)
  Lemma same_code_cells_sound_g (k : unit -> cbn_fuel) :
    spec_slot (k tt) -> spec_scc (k tt) -> spec_scc (FS k).
  Proof.
    intros hS hC L Q lo G a i l1 l2 ts1 ts2 rs s b rs' s' hm hr hl1 hl2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite same_code_cells_eq in he.
    destruct l1 as [|x1 l1]; destruct l2 as [|x2 l2].
    - injection he as <- <- <-. inversion hl1; subst. inversion hl2; subst.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. constructor.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hl1 as [|y1 m1 u1 us1 hx1 hm1]; subst.
      inversion hl2 as [|y2 m2 u2 us2 hx2 hm2]; subst.
      destruct (slot_same x1 x2 || noccur_between i 1 a) eqn:Esk.
      + destruct (hC L Q lo G a (S i) l1 l2 us1 us2 rs s b rs' s' hm hr hm1 hm2 he)
          as [hp hc].
        split; [exact hp|]. intros hb. constructor; [|exact (hc hb)].
        apply orb_true_iff in Esk as [Esame|Enocc]; [right|left; exact Enocc].
        destruct x1 as [a1|]; destruct x2 as [a2|]; cbn in Esame; try discriminate Esame.
        apply haddr_eqb_eq in Esame. subst a2.
        apply g_slot_addr_inv in hx1. apply g_slot_addr_inv in hx2.
        rewrite hx1 in hx2. injection hx2 as <-. exact (cq_refl _ _ _ _ hL).
      + destruct (conv_slot X_type X Γ nctx (k tt) L Conv x1 x2
                    (RSk l1 :: RSk l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
          [|discriminate he].
        assert (hr' : Forall (rwf Q) (RSk l1 :: RSk l2 :: rs))
          by (constructor; [exact I|constructor; [exact I|exact hr]]).
        destruct (hS L Q lo G Conv x1 x2 u1 u2 _ s b2 rs2 s2 hm hr' hx1 hx2 Ecs)
          as [hp1 hc1].
        destruct b2.
        * destruct hp1 as (Q1 & lo1 & G1 & hq1 & hm1' & hr1 & hg1).
          destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
          destruct (gpq_RSk_inv _ _ _ _ _ _ hqa) as (l1' & -> & hk1).
          destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
          destruct (gpq_RSk_inv _ _ _ _ _ _ hqb) as (l2' & -> & hk2).
          cbv beta iota in he.
          destruct (hC L Q1 lo1 G1 a (S i) l1' l2' _ _ rsB s2 b rs' s' hm1'
                      (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hm1) (hk2 _ hm2) he)
            as [hp hc].
          split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
          intros hb. constructor; [right; exact (hc1 eq_refl)|].
          exact (cagree_lift _ _ _ _ _ _ _ hLQ hq1 (hc hb)).
        * cbv beta iota in he. injection he as <- <- <-.
          split; [exact (post_drop2 _ _ _ _ _ _ _ _ hp1)|]. intros hb; discriminate hb.
  Qed.

  (** ** The statements of the other functions *)

  Definition spec_eval (d : cbn_fuel) : Prop :=
    forall L Q lo G pb x1 x2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_slot nctx Q G x1 t1 -> g_slot nctx Q G x2 t2 ->
      conv_eval X_type X Γ nctx d L pb x1 x2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  Definition spec_cells (d : cbn_fuel) : Prop :=
    forall L Q lo G l1 l2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_addrs G l1 ts1 -> g_addrs G l2 ts2 ->
      conv_cells X_type X Γ nctx d L l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cqs L Q ts1 ts2).

  Definition spec_term (d : cbn_fuel) : Prop :=
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      conv_term X_type X Γ nctx d L pb e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  (** Two codes [code_eq] accepts: one term, or equal up to universes at [Conv]. *)
  Definition samec (a1 a2 : term) : Prop := a1 = a2 \/ ∥ compare_term Σ Σ Conv a1 a2 ∥.

  (** [conv_same_code] answers [true] with the facts the same-code rule rests on; the
    conversion of the two readings follows from them ([same_code_cq] below). *)
  Definition spec_same (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> gcok G c1 -> gcok G c2 ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> g_slots nctx Q G e2.(ev_vals) ts2 ->
      conv_same_code X_type X Γ nctx d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\
      (b = true -> e1.(ev_goff) = e2.(ev_goff) /\ e1.(ev_nvals) = e2.(ev_nvals)
                   /\ samec c1.(c_term) c2.(c_term) /\ cagree L Q c1.(c_term) 0 ts1 ts2).

  Definition spec_case (d : cbn_fuel) : Prop :=
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      case_cong X_type X Γ nctx d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).

  (** The parameter codes [case_params] walks: child [case_param_step i] onwards. *)
  Inductive pcodes (G : ghost) (c : code) : N -> list term -> Prop :=
  | pcodes_nil i : pcodes G c i []
  | pcodes_cons i t l :
      gcok G (child c (case_param_step i) t) -> pcodes G c (N.succ i) l ->
      pcodes G c i (t :: l).

  Definition spec_params (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 i l1 l2 us1 us2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      pcodes G c1 i l1 -> pcodes G c2 i l2 ->
      Forall2 (g_susp nctx Q G e1) l1 us1 -> Forall2 (g_susp nctx Q G e2) l2 us2 ->
      case_params X_type X Γ nctx d L e1 c1 e2 c2 i l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cqs L Q us1 us2).

  (** A branch body read at [Q] through slots [ts], under its own [#|bcontext|] binders, and
    what a [true] claims of two of them: the lifts by [Q - L] at the cut [#|bcontext|] of two
    terms scoped at [L + #|bcontext|] are convertible. *)
  Definition rbody (ts : list term) (N : nat) (br : branch term) : term :=
    subst ts #|br.(bcontext)| (lift N (#|br.(bcontext)| + #|ts|) br.(bbody)).

  Definition cqb (L Q k : nat) (pb : conv_pb) (B1 B2 : term) : Prop :=
    forall U1 U2 : term, B1 = lift (Q - L) k U1 -> B2 = lift (Q - L) k U2 ->
      scl (L + k) U1 -> scl (L + k) U2 -> cv (L + k) pb U1 U2.

  Inductive bcodes (G : ghost) (c : code) : N -> list (branch term) -> Prop :=
  | bcodes_nil i : bcodes G c i []
  | bcodes_cons i br l :
      gcok G (child c (case_branch_step i) br.(bbody)) -> bcodes G c (N.succ i) l ->
      bcodes G c i (br :: l).

  Definition spec_branches (d : cbn_fuel) : Prop :=
    forall L Q lo G e1 c1 e2 c2 i l1 l2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      bcodes G c1 i l1 -> bcodes G c2 i l2 ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
      g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
      case_branches X_type X Γ nctx d L e1 c1 e2 c2 i l1 l2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\
      (b = true -> Forall2 (fun br1 br2 =>
          case_ctx_ok br1.(bcontext) br2.(bcontext) = true
          /\ cqb L Q #|br1.(bcontext)| Conv (rbody ts1 (Q - nctx + e1.(ev_goff)) br1)
                 (rbody ts2 (Q - nctx + e2.(ev_goff)) br2)) l1 l2).

  Definition spec_rows_on (d : cbn_fuel) (R : cbn_value -> cbn_value -> Prop) : Prop :=
    forall L Q lo G pb v1 v2 w1 w2 rs s b rs' s',
      R v1 v2 -> MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 w1 -> g_value nctx Q G v2 w2 ->
      conv_rows X_type X Γ nctx d L pb v1 v2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).

  Definition spec_rows (d : cbn_fuel) : Prop := spec_rows_on d (fun _ _ => True).

  Definition spec_value (d : cbn_fuel) : Prop :=
    forall L Q lo G pb v1 v2 w1 w2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 w1 -> g_value nctx Q G v2 w2 ->
      conv_value X_type X Γ nctx d L pb v1 v2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).

  (** All eleven functions at one fuel: the induction hypothesis of the comparison. *)
  Definition spec_all (d : cbn_fuel) : Prop :=
    spec_slot d /\ spec_eval d /\ spec_cells d /\ spec_term d /\ spec_same d /\ spec_scc d
    /\ spec_case d /\ spec_params d /\ spec_branches d /\ spec_rows d /\ spec_value d.

  (** The base case of the induction: at [FO] every function of the comparison answers
    [CFail WDepth]. This is not evidence that the statements say anything; see the witness
    lemmas for that. *)
  Lemma spec_all_FO : spec_all FO.
  Proof.
    repeat split; repeat intro;
      match goal with h : _ = COk _ |- _ => cbn in h; discriminate h end.
  Qed.

  (** ** Helpers for the step lemmas *)

  Lemma post_level L L' Q G rs s' rs' :
    nctx <= L -> L <= L' -> post L' Q G rs s' rs' -> post L Q G rs s' rs'.
  Proof.
    intros h1 h2 (Q' & lo' & G' & hq & [hL hLQ hok hw] & hr & hg).
    exists Q', lo', G'. split; [exact hq|]. split; [constructor; [exact h1|lia|exact hok|exact hw]|].
    split; assumption.
  Qed.

  Lemma gren_cons_inv Q G G' r rs rs1 :
    gren nctx Q G G' (r :: rs) rs1 ->
    exists r' rs', rs1 = r' :: rs' /\ gpres nctx Q G G' r r' /\ gren nctx Q G G' rs rs'.
  Proof.
    intros [hc hf]. destruct rs1 as [|r' rs']; [inversion hf|].
    exists r', rs'. split; [reflexivity|].
    inversion hf; subst. split; [assumption|split; assumption].
  Qed.

  Lemma gpres_RE_inv Q G G' e r :
    gpres nctx Q G G' (RE e) r -> exists e', r = RE e' /\ genv nctx Q G G' e e'.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpres_RV_inv Q G G' v r :
    gpres nctx Q G G' (RV v) r ->
    exists v', r = RV v' /\ forall t, g_value nctx Q G v t -> g_value nctx Q G' v' t.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma gpres_RSl_inv Q G G' x r :
    gpres nctx Q G G' (RSl x) r ->
    exists x', r = RSl x' /\ forall t, g_slot nctx Q G x t -> g_slot nctx Q G' x' t.
  Proof. destruct r; cbn; intros h; try contradiction. eexists; split; [reflexivity|exact h]. Qed.

  Lemma ctx_closed_jctx n : is_closed_context (Γ ,,, jctx n).
  Proof. rewrite on_free_vars_ctx_app, hΓ. apply jctx_closed. Qed.

  Lemma red_scl L Δ v u :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) -> scl L v ->
    PCUICReduction.red Σ (Γ ,,, Δ) v u -> scl L u.
  Proof.
    intros hL hΔ hcl hv hr. unfold scl in *.
    assert (e : #|Γ ,,, Δ| = L) by (rewrite app_context_length, hΔ, <- hnctx; lia).
    assert (hc : on_ctx_free_vars (shiftnP L xpred0) (Γ ,,, Δ)).
    { rewrite <- e, on_free_vars_ctx_on_ctx_free_vars. exact hcl. }
    exact (PCUICRenameConv.red_on_free_vars (wfΣ := wfΣ) hc hv hr).
  Qed.

  Lemma scl_hyg L u : scl L u -> on_free_vars xpredT u.
  Proof. intros h. eapply on_free_vars_impl; [|exact h]. intros; reflexivity. Qed.

  (** The readings of the inputs reduce, at the master level, to the readings of their values:
    a [true] about the values is a [true] about the inputs. *)
  Lemma cq_red L Q pb t1 t2 w1 w2 :
    nctx <= L -> L <= Q ->
    cred Γ Σ (jctx (Q - nctx)) t1 w1 -> cred Γ Σ (jctx (Q - nctx)) t2 w2 ->
    cq L Q pb w1 w2 -> cq L Q pb t1 t2.
  Proof.
    intros hL hQ hr1 hr2 h u1 u2 e1 e2 s1 s2 Δ hΔ hcl. subst t1 t2.
    destruct (cred_unlift Γ nctx Σ wfΣ hnctx hΓ L Q u1 w1 hL hQ (scl_hyg L u1 s1) hr1)
      as (w1' & -> & hd1).
    destruct (cred_unlift Γ nctx Σ wfΣ hnctx hΓ L Q u2 w2 hL hQ (scl_hyg L u2 s2) hr2)
      as (w2' & -> & hd2).
    assert (hj : #|jctx (L - nctx)| = L - nctx) by apply jctx_length.
    destruct (hd1 _ hj) as [rj1]. destruct (hd2 _ hj) as [rj2].
    pose proof (red_scl L _ u1 w1' hL hj (ctx_closed_jctx _) s1 rj1) as sw1.
    pose proof (red_scl L _ u2 w2' hL hj (ctx_closed_jctx _) s2 rj2) as sw2.
    destruct (h w1' w2' eq_refl eq_refl sw1 sw2 Δ hΔ hcl) as [hc].
    destruct (hd1 Δ hΔ) as [r1]. destruct (hd2 Δ hΔ) as [r2].
    constructor.
    eapply (ws_cumul_pb_closed_red (wfΣ := wfΣ)); [| |exact hc].
    - exact (into_closed_red r1 hcl (scl_open L Δ u1 hL hΔ s1)).
    - exact (into_closed_red r2 hcl (scl_open L Δ u2 hL hΔ s2)).
  Qed.

  Lemma cqs_nil L Q : cqs L Q [] [].
  Proof.
    intros us1 us2 e1 e2 _ _ Δ _ _.
    destruct us1; [|discriminate e1]. destruct us2; [|discriminate e2].
    constructor. constructor.
  Qed.

  Lemma cqs_cons L Q t1 t2 ts1 ts2 :
    cq L Q Conv t1 t2 -> cqs L Q ts1 ts2 -> cqs L Q (t1 :: ts1) (t2 :: ts2).
  Proof.
    intros h hs us1 us2 e1 e2 s1 s2 Δ hΔ hcl.
    destruct us1 as [|u1 us1]; [discriminate e1|]. destruct us2 as [|u2 us2]; [discriminate e2|].
    cbn in e1, e2. injection e1 as e1 e1'. injection e2 as e2 e2'.
    cbn in s1, s2. apply andb_true_iff in s1 as [s1 s1']. apply andb_true_iff in s2 as [s2 s2'].
    destruct (h u1 u2 e1 e2 s1 s2 Δ hΔ hcl) as [hc].
    destruct (hs us1 us2 e1' e2' s1' s2' Δ hΔ hcl) as [hcs].
    constructor. constructor; assumption.
  Qed.

  Lemma mkApps_lift0_inv m h ts u :
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

  Lemma lift0_closed_inv m h h' : closedn 0 h -> h = lift0 m h' -> h' = h.
  Proof.
    intros hc e. apply (lift0_inj m).
    transitivity h; [symmetry; exact e|symmetry; exact (lift_closed _ _ _ hc)].
  Qed.

  (** ** [conv_cells] *)

  Lemma conv_cells_eq k L l1 l2 rs s :
    conv_cells X_type X Γ nctx (FS k) L l1 l2 rs s =
    match l1, l2 with
    | [], [] => COk (true, rs, s)
    | a1 :: l1, a2 :: l2 =>
      match conv_slot X_type X Γ nctx (k tt) L Conv (SAddr a1) (SAddr a2)
              (RSp l1 :: RSp l2 :: rs) s with
      | COk (true, rs, s) =>
        match rs with
        | RSp l1 :: RSp l2 :: rs => conv_cells X_type X Γ nctx (k tt) L l1 l2 rs s
        | _ => CFail WRoots
        end
      | COk (false, rs, s) => COk (false, skipn 2 rs, s)
      | CFail w => CFail w
      end
    | _, _ => COk (false, rs, s)
    end.
  Proof. reflexivity. Qed.

  Lemma conv_cells_sound_g (k : unit -> cbn_fuel) :
    spec_slot (k tt) -> spec_cells (k tt) -> spec_cells (FS k).
  Proof.
    intros hS hC L Q lo G l1 l2 ts1 ts2 rs s b rs' s' hm hr hl1 hl2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_cells_eq in he.
    destruct l1 as [|a1 l1]; destruct l2 as [|a2 l2].
    - injection he as <- <- <-. inversion hl1; subst. inversion hl2; subst.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. apply cqs_nil.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hl1 as [|y1 u1 m1 us1 hx1 hm1]; subst.
      inversion hl2 as [|y2 u2 m2 us2 hx2 hm2]; subst.
      destruct (conv_slot X_type X Γ nctx (k tt) L Conv (SAddr a1) (SAddr a2)
                  (RSp l1 :: RSp l2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ecs;
        [|discriminate he].
      assert (hr' : Forall (rwf Q) (RSp l1 :: RSp l2 :: rs))
        by (constructor; [exact I|constructor; [exact I|exact hr]]).
      destruct (hS L Q lo G Conv (SAddr a1) (SAddr a2) u1 u2 _ s b2 rs2 s2 hm hr'
                  ltac:(constructor; exact hx1) ltac:(constructor; exact hx2) Ecs) as [hp1 hc1].
      destruct b2.
      + destruct hp1 as (Q1 & lo1 & G1 & hq1 & hm1' & hr1 & hg1).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
        destruct (gpq_RSp_inv _ _ _ _ _ _ hqa) as (l1' & -> & hk1).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
        destruct (gpq_RSp_inv _ _ _ _ _ _ hqb) as (l2' & -> & hk2).
        cbv beta iota in he.
        destruct (hC L Q1 lo1 G1 l1' l2' _ _ rsB s2 b rs' s' hm1'
                    (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hm1) (hk2 _ hm2) he)
          as [hp hc].
        split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
        intros hb. apply cqs_cons; [exact (hc1 eq_refl)|].
        exact (cqs_lift _ _ _ _ _ hLQ hq1 (hc hb)).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [exact (post_drop2 _ _ _ _ _ _ _ _ hp1)|]. intros hb; discriminate hb.
  Qed.

  (** ** [conv_eval] and [conv_term]: the machine, then the values *)

  Lemma conv_eval_eq k L le x1 x2 rs s :
    conv_eval X_type X Γ nctx (FS k) L le x1 x2 rs s =
    match eval_slot X_type X Γ nctx (k tt) x1 [] (RSl x2 :: rs) s with
    | COk (v1, rs, s) =>
      match rs with
      | RSl x2 :: rs =>
        match eval_slot X_type X Γ nctx (k tt) x2 [] (RV v1 :: rs) s with
        | COk (v2, rs, s) =>
          match rs with
          | RV v1 :: rs => conv_value X_type X Γ nctx (k tt) L le v1 v2 rs s
          | _ => CFail WRoots
          end
        | CFail w => CFail w
        end
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma conv_term_eq k L le e1 c1 e2 c2 rs s :
    conv_term X_type X Γ nctx (FS k) L le e1 c1 e2 c2 rs s =
    match whnf X_type X Γ nctx (k tt) e1 c1 [] (RE e2 :: rs) s with
    | COk (v1, rs, s) =>
      match rs with
      | RE e2 :: rs =>
        match whnf X_type X Γ nctx (k tt) e2 c2 [] (RV v1 :: rs) s with
        | COk (v2, rs, s) =>
          match rs with
          | RV v1 :: rs => conv_value X_type X Γ nctx (k tt) L le v1 v2 rs s
          | _ => CFail WRoots
          end
        | CFail w => CFail w
        end
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.
  Proof. reflexivity. Qed.

  Lemma conv_eval_sound_g (k : unit -> cbn_fuel) : spec_value (k tt) -> spec_eval (FS k).
  Proof.
    intros hV L Q lo G pb x1 x2 t1 t2 rs s b rs' s' hm hr hx1 hx2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_eval_eq in he.
    destruct (eval_slot X_type X Γ nctx (k tt) x1 [] (RSl x2 :: rs) s)
      as [[[v1 rs1] s1]|w] eqn:E1; [|discriminate he].
    destruct (eval_slot_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo G
                x1 [] [] t1 _ s v1 rs1 s1 hm (Forall_cons (RSl x2) I hr) hx1 ltac:(constructor) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & hw1 & hd1).
    destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rs1' & -> & hq1 & hg1').
    destruct (gpres_RSl_inv _ _ _ _ _ hq1) as (x2' & -> & hk1).
    cbv beta iota in he.
    destruct (eval_slot X_type X Γ nctx (k tt) x2' [] (RV v1 :: rs1') s1)
      as [[[v2 rs2] s2]|w] eqn:E2; [|discriminate he].
    destruct (eval_slot_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo1 G1
                x2' [] [] t2 _ s1 v2 rs2 s2 hm1 (Forall_cons (RV v1) hv1 (Forall_inv_tail hr1))
                (hk1 _ hx2) ltac:(constructor) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & hw2 & hd2).
    destruct (gren_cons_inv _ _ _ _ _ _ hg2) as (q2 & rs2' & -> & hq2 & hg2').
    destruct (gpres_RV_inv _ _ _ _ _ hq2) as (v1' & -> & hk2).
    cbv beta iota in he.
    destruct (hV L Q lo2 G2 pb v1' v2 w1 w2 rs2' s2 b rs' s' hm2 (Forall_inv_tail hr2)
                (Forall_inv hr2) hv2 (hk2 _ hw1) hw2 he) as [hp hc].
    pose proof (proj1 (proj2 (machine_skel X_type X Γ nctx (k tt))) _ _ _ _ _ _ _ E1)
      as hK1.
    pose proof (proj1 (proj2 (machine_skel X_type X Γ nctx (k tt))) _ _ _ _ _ _ _ E2)
      as hK2.
    split.
    - apply (post_compose L Q Q G G2 rs rs2' s' rs' (le_n Q)); [|exact hp].
      apply (grq_trans Q Q Q G G1 G2 rs rs1' rs2' (le_n Q) (le_n Q));
        (apply grq_of_gren; [assumption|eapply sk_tl; eassumption]).
    - intros hb. exact (cq_red L Q pb t1 t2 w1 w2 hL hLQ hd1 hd2 (hc hb)).
  Qed.

  Lemma conv_term_sound_g (k : unit -> cbn_fuel) : spec_value (k tt) -> spec_term (FS k).
  Proof.
    intros hV L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_term_eq in he.
    destruct (whnf X_type X Γ nctx (k tt) e1 c1 [] (RE e2 :: rs) s)
      as [[[v1 rs1] s1]|w] eqn:E1; [|discriminate he].
    destruct (whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo G
                e1 c1 [] [] t1 _ s v1 rs1 s1 hm (Forall_cons (RE e2) I hr) hs1 hc1 ltac:(constructor) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & hw1 & hd1).
    destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rs1' & -> & hq1 & hg1').
    destruct (gpres_RE_inv _ _ _ _ _ hq1) as (e2' & -> & hk1).
    cbv beta iota in he.
    destruct (whnf X_type X Γ nctx (k tt) e2' c2 [] (RV v1 :: rs1') s1)
      as [[[v2 rs2] s2]|w] eqn:E2; [|discriminate he].
    destruct (whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio (k tt) L Q lo1 G1
                e2' c2 [] [] t2 _ s1 v2 rs2 s2 hm1 (Forall_cons (RV v1) hv1 (Forall_inv_tail hr1))
                (genv_susp _ _ _ _ _ _ _ _ hk1 hs2) (cok_gcx _ _ (proj1 hg1) _ hc2)
                ltac:(constructor) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & hw2 & hd2).
    destruct (gren_cons_inv _ _ _ _ _ _ hg2) as (q2 & rs2' & -> & hq2 & hg2').
    destruct (gpres_RV_inv _ _ _ _ _ hq2) as (v1' & -> & hk2).
    cbv beta iota in he.
    destruct (hV L Q lo2 G2 pb v1' v2 w1 w2 rs2' s2 b rs' s' hm2 (Forall_inv_tail hr2)
                (Forall_inv hr2) hv2 (hk2 _ hw1) hw2 he) as [hp hc].
    pose proof (proj1 (proj2 (proj2 (machine_skel X_type X Γ nctx (k tt))))
                  _ _ _ _ _ _ _ _ E1) as hK1.
    pose proof (proj1 (proj2 (proj2 (machine_skel X_type X Γ nctx (k tt))))
                  _ _ _ _ _ _ _ _ E2) as hK2.
    split.
    - apply (post_compose L Q Q G G2 rs rs2' s' rs' (le_n Q)); [|exact hp].
      apply (grq_trans Q Q Q G G1 G2 rs rs1' rs2' (le_n Q) (le_n Q));
        (apply grq_of_gren; [assumption|eapply sk_tl; eassumption]).
    - intros hb. exact (cq_red L Q pb t1 t2 w1 w2 hL hLQ hd1 hd2 (hc hb)).
  Qed.

  (** ** The rows that compare heads and spines *)

  Lemma conv_rows_con_eq k L le h1 sp1 h2 sp2 rs s :
    conv_rows X_type X Γ nctx (FS k) L le (VCon h1 sp1) (VCon h2 sp2) rs s =
    if (#|sp1| == #|sp2|) && cmp_term X_type X le #|sp1| h1 h2
    then conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_var_eq k L le l1 sp1 l2 sp2 rs s :
    conv_rows X_type X Γ nctx (FS k) L le (VNeu (NVar l1) sp1) (VNeu (NVar l2) sp2) rs s =
    if l1 == l2 then conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s
    else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_const_eq k L le h1 sp1 h2 sp2 rs s :
    conv_rows X_type X Γ nctx (FS k) L le (VNeu (NConst h1) sp1) (VNeu (NConst h2) sp2)
      rs s =
    if cmp_term X_type X Conv #|sp1| h1 h2
    then conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_sort_eq k L le e1 c1 e2 c2 s1 s2 rs s :
    c1.(c_term) = tSort s1 -> c2.(c_term) = tSort s2 ->
    conv_rows X_type X Γ nctx (FS k) L le (VOpen e1 c1) (VOpen e2 c2) rs s
    = COk (cmp_sort X_type X le s1 s2, rs, s).
  Proof.
    destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity.
  Qed.

  (** Shared tail of the spine rows: equal heads (up to the head test) and convertible
    spines give convertible applications. *)
  Lemma cv_spine L pb h1 h2 us1 us2 :
    nctx <= L -> (forall Δ, #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
                    ∥ Σ ;;; Γ ,,, Δ ⊢ h1 ≤[pb] h2 ∥) ->
    cvs L us1 us2 -> cv L pb (mkApps h1 us1) (mkApps h2 us2).
  Proof.
    intros hL hh hs Δ hΔ hcl. destruct (hh Δ hΔ hcl) as [h]. destruct (hs Δ hΔ hcl) as [hs'].
    constructor. exact (ws_cumul_pb_mkApps (wfΣ := wfΣ) h hs').
  Qed.

  Lemma conv_rows_con_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists h1 sp1 h2 sp2, v1 = VCon h1 sp1 /\ v2 = VCon h2 sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (h1 & sp1 & h2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_con_eq in he.
    apply g_value_VCon_inv in hw1 as (ts1 & -> & ha1).
    apply g_value_VCon_inv in hw2 as (ts2 & -> & ha2).
    cbn in hv1, hv2.
    destruct ((#|sp1| == #|sp2|) && cmp_term X_type X pb #|sp1| h1 h2) eqn:Et;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Et as [_ Ecmp].
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    pose proof (lift0_closed_inv _ _ _ hv1 eh1) as ->.
    pose proof (lift0_closed_inv _ _ _ hv2 eh2) as ->.
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    intros Δ hΔ hcl.
    destruct (hc hb us1 us2 eq_refl eq_refl sus1 sus2 Δ hΔ hcl) as [hcs].
    constructor.
    apply (ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
      [exact hcl|exact (scl_open L Δ h1 hL hΔ sh1)|exact (scl_open L Δ h2 hL hΔ sh2)| |exact hcs].
    pose proof (cmp_term_sound X_type X Σ hΣ pb _ h1 h2 Ecmp) as hcmp.
    rewrite <- (g_addrs_length _ _ _ ha1), length_map in hcmp. exact hcmp.
  Qed.

  Lemma conv_rows_const_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists h1 sp1 h2 sp2,
                           v1 = VNeu (NConst h1) sp1 /\ v2 = VNeu (NConst h2) sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (h1 & sp1 & h2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_const_eq in he.
    apply g_value_VNeu_inv in hw1 as [(l & ts & e & _)|(h1' & ts1 & e & -> & ha1)];
      [discriminate e|injection e as <-].
    apply g_value_VNeu_inv in hw2 as [(l & ts & e & _)|(h2' & ts2 & e & -> & ha2)];
      [discriminate e|injection e as <-].
    cbn in hv1, hv2.
    destruct (cmp_term X_type X Conv #|sp1| h1 h2) eqn:Ecmp;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    pose proof (lift0_closed_inv _ _ _ hv1 eh1) as ->.
    pose proof (lift0_closed_inv _ _ _ hv2 eh2) as ->.
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    intros Δ hΔ hcl.
    destruct (hc hb us1 us2 eq_refl eq_refl sus1 sus2 Δ hΔ hcl) as [hcs].
    constructor. apply (ws_cumul_eq_pb (wfΣ := wfΣ)).
    apply (ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
      [exact hcl|exact (scl_open L Δ h1 hL hΔ sh1)|exact (scl_open L Δ h2 hL hΔ sh2)| |exact hcs].
    pose proof (cmp_term_sound X_type X Σ hΣ Conv _ h1 h2 Ecmp) as hcmp.
    rewrite <- (g_addrs_length _ _ _ ha1), length_map in hcmp. exact hcmp.
  Qed.

  Lemma conv_rows_var_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists l1 sp1 l2 sp2,
                           v1 = VNeu (NVar l1) sp1 /\ v2 = VNeu (NVar l2) sp2).
  Proof.
    intros hC L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (l1 & sp1 & l2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_var_eq in he.
    apply g_value_VNeu_inv in hw1 as [(l1' & ts1 & e & -> & ha1)|(h & ts & e & _)];
      [injection e as <-|discriminate e].
    apply g_value_VNeu_inv in hw2 as [(l2' & ts2 & e & -> & ha2)|(h & ts & e & _)];
      [injection e as <-|discriminate e].
    destruct (l1 == l2) eqn:El;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply eqb_eq in El. subst l2.
    destruct (hC L Q lo G sp1 sp2 ts1 ts2 rs s b rs' s' hm hr ha1 ha2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    rewrite eh1 in eh2. apply lift0_inj in eh2. subst h2'.
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [_ sus2].
    apply cv_spine; [exact hL| |exact (hc hb us1 us2 eq_refl eq_refl sus1 sus2)].
    intros Δ hΔ hcl. constructor. apply ws_cumul_pb_refl; [exact hcl|exact (scl_open L Δ h1' hL hΔ sh1)].
  Qed.

  Lemma conv_rows_sort_g (k : unit -> cbn_fuel) :
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 s1 s2,
                           v1 = VOpen e1 c1 /\ v2 = VOpen e2 c2
                           /\ c1.(c_term) = tSort s1 /\ c2.(c_term) = tSort s2).
  Proof.
    intros L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & e2 & c2 & s1 & s2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (conv_rows_sort_eq k L pb e1 c1 e2 c2 s1 s2 rs s h1 h2) in he.
    injection he as <- <- <-.
    split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hcs u1 u2 e1' e2' _ _ Δ hΔ hcl.
    apply g_value_VOpen_inv in hw1. apply g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & _ & _ & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & _ & _ & ->).
    cbn in e1', e2'.
    destruct u1; cbn in e1'; try discriminate e1'. injection e1' as <-.
    destruct u2; cbn in e2'; try discriminate e2'. injection e2' as <-.
    constructor. apply ws_cumul_pb_compare_term; [exact hcl|reflexivity|reflexivity|].
    constructor. exact (cmp_sort_sound X_type X Σ hΣ pb s1 s2 hcs).
  Qed.

  (** ** Fresh variables at the master level *)

  (** A fresh-variable cell for level [lvl < Q] reads [tRel (Q - S lvl)]; allocating it keeps
    [minv] ([alloc_sound], [alloc_hwf_holds]). *)
  Lemma alloc_fresh_g L Q lo G lvl rs s x rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs -> lvl < Q ->
    alloc (CDone (VNeu (NVar lvl) [])) rs s = COk (x, rs', s') ->
    exists lo' G', MI L Q lo' G' s' /\ Forall (rwf Q) rs' /\ gren nctx Q G G' rs rs'
      /\ G' x = Some (tRel (Q - S lvl)).
  Proof.
    intros [hL hLQ hok hw] hr hlt he.
    assert (hj : #|jctx (Q - nctx)| = Q - nctx) by apply jctx_length.
    assert (hc : g_cell nctx Q G (CDone (VNeu (NVar lvl) [])) (tRel (Q - S lvl))).
    { apply g_cell_done. apply (g_VNeuVar _ _ _ lvl [] []). constructor. }
    destruct (alloc_sound X_type X Γ nctx Σ (jctx (Q - nctx)) Q hj hnctx ltac:(lia) lo G
                _ _ rs s x rs' s' hok hc (fun _ => eq_refl) he)
      as (lo' & G' & hg & hok' & hx).
    destruct (alloc_hwf_holds nctx Q (CDone (VNeu (NVar lvl) [])) rs s x rs' s'
                ltac:(lia) hw hlt hr he) as [hw' hr'].
    exists lo', G'. split; [constructor; assumption|]. split; [exact hr'|]. split; assumption.
  Qed.

  Lemma fresh_reads_S Q lvl n ts :
    lvl + S n <= Q ->
    map (lift0 (Q - (S lvl + n))) (idsn n) ++ tRel (Q - S lvl) :: ts
    = map (lift0 (Q - (lvl + S n))) (idsn (S n)) ++ ts.
  Proof.
    intros h. replace (Q - (lvl + S n)) with (Q - (S lvl + n)) by lia.
    cbn [idsn]. rewrite map_app, <- app_assoc. cbn [map app]. f_equal. f_equal.
    cbn. f_equal. lia.
  Qed.

  (** [push_fresh n lvl] pushes [n] fresh variables, levels [lvl] to [lvl + n - 1], on both
    environments; at the master level they read as the lift of [idsn n]. *)
  Lemma push_fresh_g (n : nat) :
    forall L Q lo G lvl e1 e2 ts1 ts2 rs s r rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> lvl + n <= Q ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
      g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
      push_fresh n lvl e1 e2 rs s = COk (r, rs', s') ->
      exists lo' G' f1 f2,
        r = (lvl + n, f1, f2) /\ MI L Q lo' G' s' /\ Forall (rwf Q) rs'
        /\ gren nctx Q G G' rs rs'
        /\ f1.(ev_nvals) = #|f1.(ev_vals)| /\ f1.(ev_goff) = e1.(ev_goff)
        /\ f2.(ev_nvals) = #|f2.(ev_vals)| /\ f2.(ev_goff) = e2.(ev_goff)
        /\ g_slots nctx Q G' f1.(ev_vals) (map (lift0 (Q - (lvl + n))) (idsn n) ++ ts1)
        /\ g_slots nctx Q G' f2.(ev_vals) (map (lift0 (Q - (lvl + n))) (idsn n) ++ ts2).
  Proof.
    induction n as [|n ih];
      intros L Q lo G lvl e1 e2 ts1 ts2 rs s r rs' s' hm hr hq hs1 hn1 hs2 hn2 he.
    - rewrite pfd_push_fresh_O in he. injection he as <- <- <-.
      exists lo, G, e1, e2. rewrite Nat.add_0_r. split; [reflexivity|].
      split; [exact hm|]. split; [exact hr|]. split; [apply gren_refl|].
      cbn [idsn map app]. repeat split; assumption.
    - rewrite pfd_push_fresh_S in he.
      destruct (alloc (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s)
        as [[[x rs1] s1]|w] eqn:Ea; [|discriminate he].
      destruct (alloc_fresh_g L Q lo G lvl _ s x rs1 s1 hm
                  (Forall_cons (RE e1) I (Forall_cons (RE e2) I hr)) ltac:(lia) Ea)
        as (lo1 & G1 & hm1 & hr1 & hg1 & hx).
      destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hq1 & hgA).
      destruct (gpres_RE_inv _ _ _ _ _ hq1) as (e1' & -> & (hn1' & hg1' & hk1)).
      destruct (gren_cons_inv _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hq2 & hgB).
      destruct (gpres_RE_inv _ _ _ _ _ hq2) as (e2' & -> & (hn2' & hg2' & hk2)).
      cbv beta iota in he.
      pose proof (hk1 _ hs1) as hs1'. pose proof (hk2 _ hs2) as hs2'.
      pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hs1') as hl1'.
      pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
      pose proof (g_slots_length _ _ _ _ _ hs2') as hl2'.
      destruct (ih L Q lo1 G1 (S lvl) (env_push (SAddr x) e1') (env_push (SAddr x) e2')
                  (tRel (Q - S lvl) :: ts1) (tRel (Q - S lvl) :: ts2) rsB s1 r rs' s' hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) ltac:(lia)
                  ltac:(constructor; [constructor; exact hx|exact hs1'])
                  ltac:(cbn; lia)
                  ltac:(constructor; [constructor; exact hx|exact hs2'])
                  ltac:(cbn; lia) he)
        as (lo' & G' & f1 & f2 & -> & hm' & hr' & hg' & hf1 & hgo1 & hf2 & hgo2 & hr1' & hr2').
      exists lo', G', f1, f2.
      split; [do 2 f_equal; lia|]. split; [exact hm'|]. split; [exact hr'|].
      split; [exact (gren_trans _ _ _ _ _ _ _ _ hgB hg')|].
      split; [exact hf1|]. split; [rewrite hgo1; exact hg1'|].
      split; [exact hf2|]. split; [rewrite hgo2; exact hg2'|].
      rewrite <- !(fresh_reads_S Q lvl n) by lia. split; assumption.
  Qed.

  (** ** Environments across a call *)

  Lemma gsusp_q Q Q' G G' e e' t u :
    nctx <= Q -> Q <= Q' -> gpq Q Q' G G' (RE e) (RE e') ->
    g_susp nctx Q G e t u -> g_susp nctx Q' G' e' t (lift0 (Q' - Q) u).
  Proof.
    intros hQ hQ' (hn & hg & hk) hs.
    destruct (g_susp_inv _ _ _ _ _ _ hs) as (ts & hts & hnv & ->).
    pose proof (hk _ hts) as hts'.
    pose proof (g_slots_length _ _ _ _ _ hts) as hl.
    pose proof (g_slots_length _ _ _ _ _ hts') as hl'. rewrite length_map in hl'.
    rewrite (lift_susp_read nctx Q (Q' - Q) hQ (Q - nctx + ev_goff e) (ev_nvals e) t ts
               ltac:(lia)).
    replace (Q' - Q + (Q - nctx + ev_goff e)) with (Q' - nctx + ev_goff e') by lia.
    rewrite <- hn. apply g_susp_of_slots; [exact hts'|lia].
  Qed.

  Lemma gsusps_q Q Q' G G' e e' l us :
    nctx <= Q -> Q <= Q' -> gpq Q Q' G G' (RE e) (RE e') ->
    Forall2 (g_susp nctx Q G e) l us -> Forall2 (g_susp nctx Q' G' e') l (map (lift0 (Q' - Q)) us).
  Proof.
    intros hQ hQ' hp h. induction h; constructor; [|exact IHh].
    exact (gsusp_q _ _ _ _ _ _ _ _ hQ hQ' hp H).
  Qed.

  Lemma pcodes_gcx G G' c i l : gcx G G' -> pcodes G c i l -> pcodes G' c i l.
  Proof.
    intros hc h. induction h; constructor; [exact (cok_gcx _ _ hc _ H)|exact IHh].
  Qed.

  Lemma bcodes_gcx G G' c i l : gcx G G' -> bcodes G c i l -> bcodes G' c i l.
  Proof.
    intros hc h. induction h; constructor; [exact (cok_gcx _ _ hc _ H)|exact IHh].
  Qed.

  (** ** [case_params] *)

  Lemma case_params_sound_g (k : unit -> cbn_fuel) :
    spec_term (k tt) -> spec_params (k tt) -> spec_params (FS k).
  Proof.
    intros hT hP L Q lo G e1 c1 e2 c2 i l1 l2 us1 us2 rs s b rs' s' hm hr hp1 hp2 hu1 hu2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite case_params_eq in he.
    destruct l1 as [|t1 l1]; destruct l2 as [|t2 l2].
    - injection he as <- <- <-. inversion hu1; subst. inversion hu2; subst.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. apply cqs_nil.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hu1 as [|y1 v1 m1 vs1 hv1 hvs1]; subst.
      inversion hu2 as [|y2 v2 m2 vs2 hv2 hvs2]; subst.
      inversion hp1 as [|i1 z1 n1 hc1 hp1']; subst.
      inversion hp2 as [|i2 z2 n2 hc2 hp2']; subst.
      destruct (conv_term X_type X Γ nctx (k tt) L Conv
                  e1 (child c1 (case_param_step i) t1) e2 (child c2 (case_param_step i) t2)
                  (RE e1 :: RE e2 :: rs) s) as [[[b2 rs2] s2]|w] eqn:Ect; [|discriminate he].
      destruct (hT L Q lo G Conv e1 (child c1 (case_param_step i) t1)
                  e2 (child c2 (case_param_step i) t2) v1 v2 _ s b2 rs2 s2 hm
                  (Forall_cons (RE e1) I (Forall_cons (RE e2) I hr)) hv1 hc1 hv2 hc2 Ect)
        as [hpA hcA].
      destruct b2.
      + destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q1 & rsA & -> & hqa & hgA1).
        destruct (gpq_RE_inv _ _ _ _ _ _ hqa) as (f1 & -> & hfa).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgA1) as (q2 & rsB & -> & hqb & hgB).
        destruct (gpq_RE_inv _ _ _ _ _ _ hqb) as (f2 & -> & hfb).
        cbv beta iota in he.
        destruct (hP L QA loA GA f1 c1 f2 c2 (N.succ i) l1 l2 _ _ rsB s2 b rs' s' hmA
                    (Forall_inv_tail (Forall_inv_tail hrA))
                    (pcodes_gcx _ _ _ _ _ (proj1 hgA) hp1') (pcodes_gcx _ _ _ _ _ (proj1 hgA) hp2')
                    (gsusps_q Q QA G GA e1 f1 l1 vs1 ltac:(lia) hqA hqa hvs1)
                    (gsusps_q Q QA G GA e2 f2 l2 vs2 ltac:(lia) hqA hqb hvs2) he) as [hp hc].
        split; [exact (post_compose _ _ _ _ _ _ _ _ _ hqA hgB hp)|].
        intros hb. apply cqs_cons; [exact (hcA eq_refl)|].
        exact (cqs_lift _ _ _ _ _ hLQ hqA (hc hb)).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [exact (post_drop2 _ _ _ _ _ _ _ _ hpA)|]. intros hb; discriminate hb.
  Qed.

  (** ** The same-code rule on ghost readings *)

  Lemma shiftnP0 (P : nat -> bool) : shiftnP 0 P =1 P.
  Proof. intros i. unfold shiftnP. cbn. rewrite Nat.sub_0_r. reflexivity. Qed.

  (** The slots of an environment unlifted where the code uses them, a closed filler
    elsewhere: the logical slots the same-code rule substitutes. *)
  Fixpoint pickw (m : nat) (a : term) (i : nat) (ts : list term) : list term :=
    match ts with
    | [] => []
    | t :: ts => (if noccur_between i 1 a then tSort sProp else unl m t) :: pickw m a (S i) ts
    end.

  Lemma pickw_length m a i ts : #|pickw m a i ts| = #|ts|.
  Proof.
    revert i. induction ts as [|t ts ih]; intros i; cbn; [reflexivity|]. rewrite ih. reflexivity.
  Qed.

  Lemma pickw_lift m a i ts :
    (forall j u, nth_error ts j = Some u -> noccur_between (i + j) 1 a = false ->
       u = lift0 m (unl m u)) ->
    forall j, j < #|ts| -> noccur_between (i + j) 1 a = false ->
      nth_error (map (lift0 m) (pickw m a i ts)) j = nth_error ts j.
  Proof.
    revert i. induction ts as [|t ts ih]; intros i h j hj hn; cbn in hj |- *; [lia|].
    destruct j as [|j]; cbn.
    - rewrite Nat.add_0_r in hn. rewrite hn. f_equal. symmetry. apply (h 0 t eq_refl).
      rewrite Nat.add_0_r. exact hn.
    - apply ih; [|lia|replace (S i + j) with (i + S j) by lia; exact hn].
      intros j' u hu hn'. apply (h (S j') u hu). replace (i + S j') with (S i + j') by lia.
      exact hn'.
  Qed.

  Lemma pick_all2 L Q a i ts1 ts2 Δ :
    nctx <= L -> L <= Q -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    cagree L Q a i ts1 ts2 ->
    (forall j u, nth_error ts1 j = Some u -> noccur_between (i + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    (forall j u, nth_error ts2 j = Some u -> noccur_between (i + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    ∥ ws_cumul_pb_terms Σ (Γ ,,, Δ) (pickw (Q - L) a i ts1) (pickw (Q - L) a i ts2) ∥.
  Proof.
    intros hL hQ hΔ hcl h. induction h as [i|i u1 u2 l1 l2 hd hag ih]; intros h1 h2.
    - constructor. constructor.
    - assert (h1' : forall j u, nth_error l1 j = Some u -> noccur_between (S i + j) 1 a = false ->
                      on_free_vars (inq (Q - L) Q) u).
      { intros j u hu hn. apply (h1 (S j) u hu). replace (i + S j) with (S i + j) by lia.
        exact hn. }
      assert (h2' : forall j u, nth_error l2 j = Some u -> noccur_between (S i + j) 1 a = false ->
                      on_free_vars (inq (Q - L) Q) u).
      { intros j u hu hn. apply (h2 (S j) u hu). replace (i + S j) with (S i + j) by lia.
        exact hn. }
      destruct (ih h1' h2') as [hall].
      cbn [pickw]. destruct (noccur_between i 1 a) eqn:En.
      + constructor. constructor; [|exact hall].
        apply ws_cumul_pb_refl; [exact hcl|reflexivity].
      + destruct hd as [hd|hd]; [discriminate hd|].
        pose proof (h1 0 u1 eq_refl ltac:(rewrite Nat.add_0_r; exact En)) as o1.
        pose proof (h2 0 u2 eq_refl ltac:(rewrite Nat.add_0_r; exact En)) as o2.
        destruct (inq_unl _ _ _ o1) as [e1 s1]. destruct (inq_unl _ _ _ o2) as [e2 s2].
        replace (Q - (Q - L)) with L in s1, s2 by lia.
        destruct (hd _ _ e1 e2 s1 s2 Δ hΔ hcl) as [hc].
        constructor. constructor; [exact hc|exact hall].
  Qed.

  Lemma same_code_cv L Q pb n goff ts1 ts2 a Δ :
    nctx <= L -> L <= Q -> #|ts1| = n -> #|ts2| = n ->
    #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    cagree L Q a 0 ts1 ts2 ->
    (forall j u, nth_error ts1 j = Some u -> noccur_between (0 + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    (forall j u, nth_error ts2 j = Some u -> noccur_between (0 + j) 1 a = false ->
       on_free_vars (inq (Q - L) Q) u) ->
    scl L (subst (pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a)) ->
    ∥ Σ ;;; Γ ,,, Δ ⊢ subst (pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a) ≤[pb]
                     subst (pickw (Q - L) a 0 ts2) 0 (lift (L - nctx + goff) n a) ∥.
  Proof.
    intros hL hQ hl1 hl2 hΔ hcl hag h1 h2 hs.
    destruct (pick_all2 L Q a 0 ts1 ts2 Δ hL hQ hΔ hcl hag h1 h2) as [hall].
    constructor. apply (ws_cumul_pb_subst_open (wfΣ := wfΣ)); [exact hcl|exact hall|].
    pose proof (cg_subst_scope_inv (shiftnP L xpred0) (pickw (Q - L) a 0 ts1)
                  (lift (L - nctx + goff) n a) 0) as hsc.
    rewrite pickw_length, hl1 in hsc.
    assert (h0 : on_free_vars (shiftnP 0 (shiftnP L xpred0))
                   (subst (pickw (Q - L) a 0 ts1) 0 (lift (L - nctx + goff) n a))).
    { rewrite (on_free_vars_ext _ _ _ (shiftnP0 _)). exact hs. }
    specialize (hsc h0). rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in hsc.
    rewrite !app_context_length, fresh_context_length, pickw_length, hl1, hΔ, <- hnctx.
    assert (E : n + (L - nctx + nctx) = 0 + n + L) by lia. rewrite E. exact hsc.
  Qed.

  (** Two readings of codes [code_eq] accepts, through environments with the same counts whose
    used slots agree in the sense of [cq], are convertible at any [conv_pb]. The used slots of a
    lifted reading are lifts ([cg_occ_inv]); the unused ones do not matter
    ([subst_agree_lift]). *)
  Lemma same_code_cq L Q pb n goff ts1 ts2 a1 a2 :
    nctx <= L -> L <= Q -> #|ts1| = n -> #|ts2| = n ->
    on_free_vars xpredT a1 -> on_free_vars xpredT a2 ->
    samec a1 a2 -> cagree L Q a1 0 ts1 ts2 ->
    cq L Q pb (subst ts1 0 (lift (Q - nctx + goff) n a1))
              (subst ts2 0 (lift (Q - nctx + goff) n a2)).
  Proof.
    intros hL hQ hl1 hl2 hy1 hy2 hsame hag u1 u2 e1 e2 s1 s2 Δ hΔ hcl.
    assert (hQm : L + (Q - L) = Q) by lia.
    assert (hN : Q - nctx + goff = (Q - L) + (L - nctx + goff)) by lia.
    assert (hinv : forall ts a, on_free_vars xpredT a -> #|ts| = n ->
              on_free_vars (inq (Q - L) Q) (subst ts 0 (lift (Q - nctx + goff) n a)) ->
              forall j u, nth_error ts j = Some u -> noccur_between (0 + j) 1 a = false ->
                on_free_vars (inq (Q - L) Q) u).
    { intros ts a hy hl hT j u hu hn.
      apply (cg_occ_inv (inq (Q - L) Q) ts (Q - nctx + goff) j u hu a 0 hy hn).
      rewrite (on_free_vars_ext _ _ _ (shiftnP0 _)). cbn [Nat.add]. rewrite hl. exact hT. }
    assert (hU : forall ts a U, on_free_vars xpredT a -> #|ts| = n ->
              subst ts 0 (lift (Q - nctx + goff) n a) = lift0 (Q - L) U ->
              on_free_vars (inq (Q - L) Q) (subst ts 0 (lift (Q - nctx + goff) n a)) ->
              U = subst (pickw (Q - L) a 0 ts) 0 (lift (L - nctx + goff) n a)).
    { intros ts a U hy hl eU hT. apply (lift0_inj (Q - L)). rewrite <- eU.
      rewrite (lift_susp_read nctx L (Q - L) hL (L - nctx + goff) n a (pickw (Q - L) a 0 ts)
                 ltac:(rewrite pickw_length; exact hl)).
      rewrite <- hN.
      apply subst_agree_lift; [rewrite length_map, pickw_length; reflexivity|symmetry; exact hl|].
      intros j hj hn. symmetry. apply pickw_lift; [|exact hj|exact hn].
      intros j' u hu hn'. exact (proj1 (inq_unl _ _ u (hinv ts a hy hl hT j' u hu hn'))). }
    pose proof (inq_lift0 (Q - L) L u1 s1) as hT1. rewrite hQm, <- e1 in hT1.
    pose proof (inq_lift0 (Q - L) L u2 s2) as hT2. rewrite hQm, <- e2 in hT2.
    pose proof (hU ts1 a1 u1 hy1 hl1 e1 hT1) as hU1.
    destruct hsame as [<-|[hc12]].
    - pose proof (hU ts2 a1 u2 hy1 hl2 e2 hT2) as hU2.
      rewrite hU1 in s1 |- *. rewrite hU2.
      exact (same_code_cv L Q pb n goff ts1 ts2 a1 Δ hL hQ hl1 hl2 hΔ hcl hag
               (hinv ts1 a1 hy1 hl1 hT1) (hinv ts2 a1 hy1 hl2 hT2) s1).
    - set (T2' := subst ts2 0 (lift (Q - nctx + goff) n a1)).
      assert (h12 : compare_term Σ Σ Conv T2' (subst ts2 0 (lift (Q - nctx + goff) n a2))).
      { apply subst_eq_term.
        exact (eq_term_upto_univ_lift Σ (compare_universe Σ) (compare_sort Σ) Conv
                 (Q - nctx + goff) 0 n _ _ hc12). }
      assert (h21 : compare_term Σ Σ Conv (subst ts2 0 (lift (Q - nctx + goff) n a2)) T2')
        by (symmetry; exact h12).
      pose proof (PCUICConfluence.eq_term_upto_univ_napp_on_free_vars h21 hT2) as hT2'.
      destruct (inq_unl (Q - L) Q T2' hT2') as [eT2' sT2'].
      replace (Q - (Q - L)) with L in sT2' by lia.
      pose proof (hU ts2 a1 (unl (Q - L) T2') hy1 hl2 eT2' hT2') as hU2'.
      assert (hc2 : compare_term Σ Σ Conv (unl (Q - L) T2') u2).
      { rewrite <- (unl_lift0 (Q - L) u2), <- e2.
        exact (PCUICRenameConv.eq_term_upto_univ_rename Σ _ _ Conv 0 _ _ _ h12). }
      rewrite hU1 in s1 |- *.
      destruct (same_code_cv L Q pb n goff ts1 ts2 a1 Δ hL hQ hl1 hl2 hΔ hcl hag
                  (hinv ts1 a1 hy1 hl1 hT1) (hinv ts2 a1 hy1 hl2 hT2') s1) as [h1].
      constructor. refine (@ws_cumul_pb_conv_trans_r cf Σ wfΣ pb (Γ ,,, Δ) _ _ _ h1 _).
      rewrite <- hU2'.
      apply ws_cumul_pb_compare_term; [exact hcl|exact (scl_open L Δ _ hL hΔ sT2')|
                                       exact (scl_open L Δ u2 hL hΔ s2)|exact hc2].
  Qed.

  (** [code_eq_sound], with the universe checks [code_eq] ran on the way to a syntactic
    comparison. *)
  Lemma code_eq_sound_wf (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) :
    ceq_ok X_type X (s.(st_memo)) ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 -> code_inv e2 c2 ->
    fst (code_eq X_type X c1 c2 s) = true ->
    c1.(c_term) = c2.(c_term)
    \/ (cbn_ceq_term X_type X c1.(c_term) c2.(c_term) = true
        /\ entry_wf c1.(c_entry) s = true /\ entry_wf c2.(c_entry) s = true).
  Proof.
    intros hq g1 hi1 g2 hi2 hE.
    destruct (code_eq_sound X_type X c1 c2 e1 e2 s hq g1 hi1 g2 hi2 hE) as [h|h];
      [left; exact h|].
    destruct (same_id c1 c2) eqn:Esid.
    { left. exact (same_id_sound_table _ e1 e2 c1 c2 Esid g1 hi1 g2 hi2). }
    right. split; [exact h|].
    unfold code_eq in hE. rewrite Esid in hE.
    destruct (entry_wf c1.(c_entry) s && entry_wf c2.(c_entry) s) eqn:Ew;
      [apply andb_true_iff in Ew; exact Ew|cbn in hE; discriminate hE].
  Qed.

  Lemma conv_same_code_sound_g (k : unit -> cbn_fuel) : spec_scc (k tt) -> spec_same (FS k).
  Proof.
    intros hC L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s' hm hr hc1 hc2 hs1 hs2 he.
    pose proof hm as [hL hLQ hok hw].
    rewrite conv_same_code_eq in he.
    destruct ((e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals))) eqn:Eeq;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Eeq as [Eg En]. apply eqb_eq in Eg. apply eqb_eq in En.
    destruct hc1 as [ce1 [hg1 hi1]]. destruct hc2 as [ce2 [hg2 hi2]].
    destruct (gk_memo _ _ _ _ _ _ _ _ _ _ hok) as (hmi & hmo & hK & hcons & hhy).
    pose proof (hK _ _ hg1) as hg1'. pose proof (hK _ _ hg2) as hg2'.
    destruct (memo_inv_code_eq X_type X c1 c2 ce1 ce2 s hmi hg1' hi1 hg2' hi2)
      as (hmi' & hcodes & hheap & hnext & _ & _ & hgam).
    assert (hm0 : MI L Q lo G (snd (code_eq X_type X c1 c2 s))).
    { constructor; [exact hL|exact hLQ| |exact (hwf_heap Q s _ hheap hw)].
      apply (gok_same X_type X Γ nctx Σ _ Q lo G s); [exact hok|exact hheap|exact hnext|exact hgam|].
      split; [exact hmi'|]. split; [exact (memo_ok_codes X_type X s _ hcodes hmo)|].
      rewrite hcodes. split; [exact hK|]. split; [exact hcons|exact hhy]. }
    assert (hE : forall b0, fst (code_eq X_type X c1 c2 s) = b0 -> b0 = true ->
                   samec c1.(c_term) c2.(c_term)).
    { intros b0 Eb0 ->.
      destruct (code_eq_sound_wf c1 c2 ce1 ce2 s (proj1 (proj2 (proj2 (proj2 hmi))))
                  hg1' hi1 hg2' hi2 Eb0) as [h|(hceq & hw1 & hw2)]; [left; exact h|right].
      rewrite (memo_entry_wf X_type X s _ ce1 hmo hg1') in hw1.
      rewrite (memo_entry_wf X_type X s _ ce2 hmo hg2') in hw2.
      rewrite (wf_term_univs_correct X_type X Σ hΣ) in hw1, hw2.
      constructor.
      exact (cbn_ceq_term_sound X_type X Σ hΣ _ _ (cg_code_inv_wf_universes Σ ce1 c1 hi1 hw1)
               (cg_code_inv_wf_universes Σ ce2 c2 hi2 hw2) hceq). }
    destruct (code_eq X_type X c1 c2 s) as [b0 s0] eqn:Ece. cbn [fst snd] in hm0, hE.
    destruct b0;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm0 hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G c1.(c_term) 0 _ _ ts1 ts2 rs s0 b rs' s' hm0 hr hs1 hs2 he) as [hp hc].
    split; [exact hp|]. intros hb. split; [exact Eg|]. split; [exact En|].
    split; [exact (hE true eq_refl eq_refl)|exact (hc hb)].
  Qed.

  (** A [true] of [conv_same_code] makes the two readings of the codes convertible at any
    [conv_pb]. *)
  Lemma conv_same_code_sound_ghost (d : cbn_fuel) : spec_same d ->
    forall L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs ->
      g_susp nctx Q G e1 c1.(c_term) t1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) t2 -> gcok G c2 ->
      conv_same_code X_type X Γ nctx d L e1 c1 e2 c2 rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb t1 t2).
  Proof.
    intros hS L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ hok _].
    destruct (g_susp_inv _ _ _ _ _ _ hs1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hs2) as (ts2 & hts2 & hn2 & ->).
    destruct (hS L Q lo G e1 c1 e2 c2 ts1 ts2 rs s b rs' s' hm hr hc1 hc2 hts1 hts2 he)
      as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as (hgo & hnv & hsame & hag).
    pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
    pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
    rewrite <- hgo, <- hnv.
    apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
      [lia|lia|exact (hch _ hc1)|exact (hch _ hc2)|exact hsame|exact hag].
  Qed.

  Lemma cagree_fix L Q m idx idx' i l1 l2 :
    cagree L Q (tFix m idx) i l1 l2 -> cagree L Q (tFix m idx') i l1 l2.
  Proof. induction 1; constructor; [exact H|exact IHcagree]. Qed.

  Lemma samec_fix m1 m2 idx1 idx2 i :
    samec (tFix m1 idx1) (tFix m2 idx2) -> samec (tFix m1 i) (tFix m2 i).
  Proof.
    intros [e|[h]]; [injection e as -> _; left; reflexivity|right; constructor].
    inversion h; subst. constructor. assumption.
  Qed.

  (** ** [conv_slot] *)

  Lemma conv_slot_eq k L le x1 x2 rs s :
    conv_slot X_type X Γ nctx (FS k) L le x1 x2 rs s =
    match x1, x2 with
    | SAddr a1, SAddr a2 =>
      if haddr_eqb a1 a2 then COk (true, rs, s)
      else conv_eval X_type X Γ nctx (k tt) L le x1 x2 rs s
    | SInl vs1 n1 o1 c1, SInl vs2 n2 o2 c2 =>
      match conv_same_code X_type X Γ nctx (k tt) L (mkEnv vs1 n1 o1) c1
              (mkEnv vs2 n2 o2) c2 (RSl x1 :: RSl x2 :: rs) s with
      | COk (b, rs, s) =>
        match rs with
        | RSl x1 :: RSl x2 :: rs =>
          if b then COk (true, rs, s)
          else conv_eval X_type X Γ nctx (k tt) L le x1 x2 rs s
        | _ => CFail WRoots
        end
      | CFail w => CFail w
      end
    | _, _ => conv_eval X_type X Γ nctx (k tt) L le x1 x2 rs s
    end.
  Proof. reflexivity. Qed.

  Lemma conv_slot_sound_g (k : unit -> cbn_fuel) :
    spec_eval (k tt) -> spec_same (k tt) -> spec_slot (FS k).
  Proof.
    intros hE hS L Q lo G pb x1 x2 t1 t2 rs s b rs' s' hm hr hx1 hx2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_slot_eq in he.
    destruct x1 as [a1|vs1 n1 o1 c1]; destruct x2 as [a2|vs2 n2 o2 c2];
      cbv beta iota in he;
      try exact (hE L Q lo G pb _ _ t1 t2 rs s b rs' s' hm hr hx1 hx2 he).
    - destruct (haddr_eqb a1 a2) eqn:Ea;
        [|exact (hE L Q lo G pb _ _ t1 t2 rs s b rs' s' hm hr hx1 hx2 he)].
      injection he as <- <- <-. split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _.
      apply haddr_eqb_eq in Ea. subst a2.
      apply g_slot_addr_inv in hx1. apply g_slot_addr_inv in hx2.
      rewrite hx1 in hx2. injection hx2 as <-. exact (cq_refl _ _ _ _ hL).
    - assert (hs1 : g_susp nctx Q G (mkEnv vs1 n1 o1) c1.(c_term) t1)
        by (eapply g_slot_inl_inv; exact hx1).
      assert (hc1 : gcok G c1) by (eapply g_slot_inl_cok; exact hx1).
      assert (hs2 : g_susp nctx Q G (mkEnv vs2 n2 o2) c2.(c_term) t2)
        by (eapply g_slot_inl_inv; exact hx2).
      assert (hc2 : gcok G c2) by (eapply g_slot_inl_cok; exact hx2).
      destruct (conv_same_code X_type X Γ nctx (k tt) L (mkEnv vs1 n1 o1) c1
                  (mkEnv vs2 n2 o2) c2 (RSl (SInl vs1 n1 o1 c1) :: RSl (SInl vs2 n2 o2 c2) :: rs) s)
        as [[[b0 rs0] s0]|w] eqn:Ecs; [|discriminate he].
      destruct (conv_same_code_sound_ghost (k tt) hS L Q lo G pb _ c1 _ c2 t1 t2 _ s b0 rs0 s0
                  hm (Forall_cons (RSl _) I (Forall_cons (RSl _) I hr)) hs1 hc1 hs2 hc2 Ecs)
        as [hp0 hc0].
      destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
      destruct (gpq_RSl_inv _ _ _ _ _ _ hqa) as (y1 & -> & hk1).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
      destruct (gpq_RSl_inv _ _ _ _ _ _ hqb) as (y2 & -> & hk2).
      cbv beta iota in he.
      destruct b0.
      + injection he as <- <- <-.
        split; [|intros _; exact (hc0 eq_refl)].
        exists Q1, lo1, G1. split; [exact hq1|]. split; [exact hm1|].
        split; [exact (Forall_inv_tail (Forall_inv_tail hr1))|exact hgB].
      + destruct (hE L Q1 lo1 G1 pb y1 y2 _ _ rsB s0 b rs' s' hm1
                    (Forall_inv_tail (Forall_inv_tail hr1)) (hk1 _ hx1) (hk2 _ hx2) he)
          as [hp hc].
        split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
        intros hb. exact (cq_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  (** ** Crossing a binder: the lambda and product rows *)

  Lemma minv_level L L' Q lo G s : MI L Q lo G s -> nctx <= L' -> L' <= Q -> MI L' Q lo G s.
  Proof. intros [hL hQ hok hw] h1 h2. constructor; assumption. Qed.

  (** The body of a code read through slots lifted by [d] is the lift by [d] at the cut [k]. *)
  Lemma lift_bodyk d ts N n k t :
    #|ts| = n ->
    subst (map (lift0 d) ts) k (lift (d + N) (k + n) t) = lift d k (subst ts k (lift N (k + n) t)).
  Proof.
    intros hl. pose proof (distr_lift_subst_rec (lift N (k + n) t) ts d k 0) as h.
    rewrite !Nat.add_0_r in h. rewrite h. f_equal. rewrite hl.
    symmetry. apply simpl_lift; lia.
  Qed.

  Lemma subst_rel_lift1 j U : subst [tRel j] 0 (lift (S j) 1 U) = lift0 j U.
  Proof.
    pose proof (cg_subst_fresh_lift j 1 U) as h.
    replace (map (lift0 j) (idsn 1)) with [tRel j] in h
      by (cbn; rewrite Nat.add_0_r; reflexivity).
    rewrite Nat.add_1_r in h. exact h.
  Qed.

  (** After the domains: one fresh variable at level [L], pushed on both environments, then
    the bodies at [S L]. *)
  Definition binder_tail (d : cbn_fuel) (L : nat) (pb : conv_pb) (e1 e2 : cbn_env)
      (cb1 cb2 : code) (rs : list root) (s : cbn_state) :=
    match alloc (CDone (VNeu (NVar L) [])) (RE e1 :: RE e2 :: rs) s with
    | COk (x, rs, s) =>
      match rs with
      | RE e1 :: RE e2 :: rs =>
        conv_term X_type X Γ nctx d (S L) pb (env_push (SAddr x) e1) cb1
          (env_push (SAddr x) e2) cb2 rs s
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.

  Lemma binder_tail_g (k : unit -> cbn_fuel) (hT : spec_term (k tt))
      L Q lo G pb e1 e2 cb1 cb2 ts1 ts2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
    g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
    gcok G cb1 -> gcok G cb2 ->
    binder_tail (k tt) L pb e1 e2 cb1 cb2 rs s = COk (b, rs', s') ->
    post L Q G rs s' rs' /\
    (b = true -> cqb L Q 1 pb
       (subst ts1 1 (lift (Q - nctx + e1.(ev_goff)) (S e1.(ev_nvals)) cb1.(c_term)))
       (subst ts2 1 (lift (Q - nctx + e2.(ev_goff)) (S e2.(ev_nvals)) cb2.(c_term)))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hc1 hc2 he.
    pose proof hm as [hL hLQ _ _].
    pose proof (minv_raise L Q 1 lo G s hm) as hmR.
    pose proof (rwfs_mono Q (Q + 1) rs ltac:(lia) hr) as hrR.
    pose proof (grq_raise Q 1 G rs ltac:(lia) hr) as hgR.
    pose proof (proj2 (g_slot_shift nctx Q 1 ltac:(lia) G) _ _ hs1) as [hs1R _].
    pose proof (proj2 (g_slot_shift nctx Q 1 ltac:(lia) G) _ _ hs2) as [hs2R _].
    unfold binder_tail in he.
    destruct (alloc (CDone (VNeu (NVar L) [])) (RE e1 :: RE e2 :: rs) s)
      as [[[x rs1] s1]|w] eqn:Ea; [|discriminate he].
    destruct (alloc_fresh_g L (Q + 1) lo (gshift 1 G) L _ s x rs1 s1 hmR
                (Forall_cons (RE e1) I (Forall_cons (RE e2) I hrR)) ltac:(lia) Ea)
      as (lo1 & G1 & hm1 & hr1 & hg1 & hx).
    destruct (gren_cons_inv _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hq1 & hgA).
    destruct (gpres_RE_inv _ _ _ _ _ hq1) as (f1 & -> & (hn1' & hg1' & hk1)).
    destruct (gren_cons_inv _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hq2 & hgB).
    destruct (gpres_RE_inv _ _ _ _ _ hq2) as (f2 & -> & (hn2' & hg2' & hk2)).
    cbv beta iota in he.
    pose proof (hk1 _ hs1R) as hf1. pose proof (hk2 _ hs2R) as hf2.
    pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
    pose proof (g_slots_length _ _ _ _ _ hf1) as hl1'. rewrite length_map in hl1'.
    pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
    pose proof (g_slots_length _ _ _ _ _ hf2) as hl2'. rewrite length_map in hl2'.
    set (j := Q + 1 - S L).
    assert (hb1 : g_susp nctx (Q + 1) G1 (env_push (SAddr x) f1) cb1.(c_term)
                    (subst (tRel j :: map (lift0 1) ts1) 0
                       (lift (Q + 1 - nctx + ev_goff e1) (S (ev_nvals e1)) cb1.(c_term)))).
    { rewrite <- hg1', <- hn1'. apply (g_susp_of_slots _ _ _ (env_push (SAddr x) f1)).
      - cbn. constructor; [constructor; exact hx|exact hf1].
      - cbn. lia. }
    assert (hb2 : g_susp nctx (Q + 1) G1 (env_push (SAddr x) f2) cb2.(c_term)
                    (subst (tRel j :: map (lift0 1) ts2) 0
                       (lift (Q + 1 - nctx + ev_goff e2) (S (ev_nvals e2)) cb2.(c_term)))).
    { rewrite <- hg2', <- hn2'. apply (g_susp_of_slots _ _ _ (env_push (SAddr x) f2)).
      - cbn. constructor; [constructor; exact hx|exact hf2].
      - cbn. lia. }
    destruct (hT (S L) (Q + 1) lo1 G1 pb _ cb1 _ cb2 _ _ rsB s1 b rs' s'
                (minv_level L (S L) (Q + 1) lo1 G1 s1 hm1 ltac:(lia) ltac:(lia))
                (Forall_inv_tail (Forall_inv_tail hr1)) hb1 (cok_gcx _ _ (proj1 hg1) _ hc1)
                hb2 (cok_gcx _ _ (proj1 hg1) _ hc2) he) as [hp hc].
    split.
    - apply (post_compose L Q (Q + 1) G (gshift 1 G) rs rs s' rs' ltac:(lia) hgR).
      apply (post_compose L (Q + 1) (Q + 1) (gshift 1 G) G1 rs rsB s' rs' (le_n _)
               (grq_of_gren _ _ _ _ _ hgB
                  (sk_tl _ _ _ _ (sk_tl _ _ _ _ (alloc_skel _ _ _ _ _ _ Ea))))).
      exact (post_level L (S L) (Q + 1) G1 rsB s' rs' hL ltac:(lia) hp).
    - intros hbt U1 U2 eU1 eU2 sU1 sU2.
      rewrite Nat.add_1_r in sU1, sU2 |- *.
      apply (hc hbt U1 U2); [| |exact sU1|exact sU2].
      + rewrite subst_cons_app.
        replace (Q + 1 - nctx + ev_goff e1) with (1 + (Q - nctx + ev_goff e1)) by lia.
        replace (S (ev_nvals e1)) with (1 + #|ts1|) by lia.
        rewrite lift_bodyk by reflexivity.
        replace (1 + #|ts1|) with (S (ev_nvals e1)) by lia. rewrite eU1.
        rewrite simpl_lift by lia. subst j.
        replace (1 + (Q - L)) with (S (Q + 1 - S L)) by lia. apply subst_rel_lift1.
      + rewrite subst_cons_app.
        replace (Q + 1 - nctx + ev_goff e2) with (1 + (Q - nctx + ev_goff e2)) by lia.
        replace (S (ev_nvals e2)) with (1 + #|ts2|) by lia.
        rewrite lift_bodyk by reflexivity.
        replace (1 + #|ts2|) with (S (ev_nvals e2)) by lia. rewrite eU2.
        rewrite simpl_lift by lia. subst j.
        replace (1 + (Q - L)) with (S (Q + 1 - S L)) by lia. apply subst_rel_lift1.
  Qed.

  Lemma cqb_lift (L Q Q' k : nat) (pb : conv_pb) (B1 B2 : term) :
    L <= Q -> Q <= Q' ->
    cqb L Q' k pb (lift (Q' - Q) k B1) (lift (Q' - Q) k B2) -> cqb L Q k pb B1 B2.
  Proof.
    intros hLQ hQ h U1 U2 e1 e2 s1 s2. apply h; [| |exact s1|exact s2].
    - rewrite e1, simpl_lift by lia. f_equal. lia.
    - rewrite e2, simpl_lift by lia. f_equal. lia.
  Qed.

  (** Domains at [Conv], then one fresh variable and the bodies at [pbb]. *)
  Lemma binder_step (k : unit -> cbn_fuel) (hT : spec_term (k tt))
      L Q lo G pbb e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
    g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
    gcok G (child c1 0 A1) -> gcok G (child c2 0 A2) ->
    gcok G (child c1 1 b1) -> gcok G (child c2 1 b2) ->
    match conv_term X_type X Γ nctx (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
            (RE e1 :: RE e2 :: rs) s with
    | COk (true, rs, s) =>
      match rs with
      | RE e1 :: RE e2 :: rs => binder_tail (k tt) L pbb e1 e2 (child c1 1 b1) (child c2 1 b2) rs s
      | _ => CFail WRoots
      end
    | COk (false, rs, s) => COk (false, skipn 2 rs, s)
    | CFail w => CFail w
    end = COk (b, rs', s') ->
    post L Q G rs s' rs' /\
    (b = true ->
     cq L Q Conv (subst ts1 0 (lift (Q - nctx + e1.(ev_goff)) e1.(ev_nvals) A1))
                 (subst ts2 0 (lift (Q - nctx + e2.(ev_goff)) e2.(ev_nvals) A2))
     /\ cqb L Q 1 pbb (subst ts1 1 (lift (Q - nctx + e1.(ev_goff)) (S e1.(ev_nvals)) b1))
                      (subst ts2 1 (lift (Q - nctx + e2.(ev_goff)) (S e2.(ev_nvals)) b2))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hcA1 hcA2 hcB1 hcB2 he.
    pose proof hm as [hL hLQ _ _].
    destruct (conv_term X_type X Γ nctx (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
                (RE e1 :: RE e2 :: rs) s) as [[[bA rsA] sA]|w] eqn:EA; [|discriminate he].
    destruct (hT L Q lo G Conv e1 (child c1 0 A1) e2 (child c2 0 A2) _ _ _ s bA rsA sA hm
                (Forall_cons (RE e1) I (Forall_cons (RE e2) I hr))
                (g_susp_of_slots _ _ _ e1 A1 ts1 hs1 hn1) hcA1
                (g_susp_of_slots _ _ _ e2 A2 ts2 hs2 hn2) hcA2 EA) as [hpA hcA].
    destruct bA.
    - destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q1 & rsA1 & -> & hqa & hgA1).
      destruct (gpq_RE_inv _ _ _ _ _ _ hqa) as (f1 & -> & hnf1 & hgf1 & hkf1).
      destruct (grq_cons_inv _ _ _ _ _ _ _ hgA1) as (q2 & rsB & -> & hqb & hgB).
      destruct (gpq_RE_inv _ _ _ _ _ _ hqb) as (f2 & -> & hnf2 & hgf2 & hkf2).
      cbv beta iota in he.
      pose proof (hkf1 _ hs1) as hf1. pose proof (hkf2 _ hs2) as hf2.
      pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hf1) as hl1'. rewrite length_map in hl1'.
      pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
      pose proof (g_slots_length _ _ _ _ _ hf2) as hl2'. rewrite length_map in hl2'.
      destruct (binder_tail_g k hT L QA loA GA pbb f1 f2 (child c1 1 b1) (child c2 1 b2)
                  _ _ rsB sA b rs' s' hmA (Forall_inv_tail (Forall_inv_tail hrA)) hf1
                  ltac:(lia) hf2 ltac:(lia)
                  (cok_gcx _ _ (proj1 hgA) _ hcB1) (cok_gcx _ _ (proj1 hgA) _ hcB2) he)
        as [hpB hcB].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hqA hgB hpB)|].
      intros hb. split; [exact (hcA eq_refl)|].
      apply (cqb_lift L Q QA 1 pbb _ _ hLQ hqA).
      rewrite hnf1, hgf1, hnf2, hgf2 in hcB.
      replace (QA - nctx + ev_goff e1) with ((QA - Q) + (Q - nctx + ev_goff e1)) in hcB by lia.
      replace (QA - nctx + ev_goff e2) with ((QA - Q) + (Q - nctx + ev_goff e2)) in hcB by lia.
      replace (S (ev_nvals e1)) with (1 + #|ts1|) in hcB |- * by lia.
      replace (S (ev_nvals e2)) with (1 + #|ts2|) in hcB |- * by lia.
      rewrite !lift_bodyk in hcB by reflexivity. exact (hcB hb).
    - cbv beta iota in he. injection he as <- <- <-.
      split; [exact (post_drop2 _ _ _ _ _ _ _ _ hpA)|]. intros hb; discriminate hb.
  Qed.

  Lemma conv_rows_lam_eq k L le e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s :
    c1.(c_term) = tLambda na1 A1 b1 -> c2.(c_term) = tLambda na2 A2 b2 ->
    conv_rows X_type X Γ nctx (FS k) L le (VLam e1 c1) (VLam e2 c2) rs s =
    if eqb_binder_annot na1 na2 then
      match conv_term X_type X Γ nctx (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
              (RE e1 :: RE e2 :: rs) s with
      | COk (true, rs, s) =>
        match rs with
        | RE e1 :: RE e2 :: rs =>
          binder_tail (k tt) L Conv e1 e2 (child c1 1 b1) (child c2 1 b2) rs s
        | _ => CFail WRoots
        end
      | COk (false, rs, s) => COk (false, skipn 2 rs, s)
      | CFail w => CFail w
      end
    else COk (false, rs, s).
  Proof. destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity. Qed.

  Lemma conv_rows_prod_eq k L le e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s :
    c1.(c_term) = tProd na1 A1 b1 -> c2.(c_term) = tProd na2 A2 b2 ->
    conv_rows X_type X Γ nctx (FS k) L le (VOpen e1 c1) (VOpen e2 c2) rs s =
    if eqb_binder_annot na1 na2 then
      match conv_term X_type X Γ nctx (k tt) L Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
              (RE e1 :: RE e2 :: rs) s with
      | COk (true, rs, s) =>
        match rs with
        | RE e1 :: RE e2 :: rs =>
          binder_tail (k tt) L le e1 e2 (child c1 1 b1) (child c2 1 b2) rs s
        | _ => CFail WRoots
        end
      | COk (false, rs, s) => COk (false, skipn 2 rs, s)
      | CFail w => CFail w
      end
    else COk (false, rs, s).
  Proof. destruct c1 as [i1 p1 t1], c2 as [i2 p2 t2]. cbn. intros -> ->. reflexivity. Qed.

  (** The logical context of a body: one more assumption. *)
  Lemma snoc_closed L Δ na A :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) -> scl L A ->
    is_closed_context (Γ ,,, (Δ ,, vass na A)).
  Proof.
    intros hL hΔ hcl hA.
    change (Γ ,,, (Δ ,, vass na A)) with ((Γ ,,, Δ) ,, vass na A).
    rewrite on_free_vars_ctx_snoc, hcl. cbn. rewrite ?andb_true_r.
    exact (scl_open L Δ A hL hΔ hA).
  Qed.

  Lemma scl_binder L B : on_free_vars (shiftnP 1 (shiftnP L xpred0)) B -> scl (L + 1) B.
  Proof.
    intros h. unfold scl. rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in h.
    rewrite Nat.add_comm. exact h.
  Qed.

  Lemma conv_rows_lam_g (k : unit -> cbn_fuel) :
    spec_term (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 na1 A1 b1 na2 A2 b2,
                           v1 = VLam e1 c1 /\ v2 = VLam e2 c2
                           /\ c1.(c_term) = tLambda na1 A1 b1 /\ c2.(c_term) = tLambda na2 A2 b2).
  Proof.
    intros hT L Q lo G pb v1 v2 w1 w2 rs s b rs' s'
      (e1 & c1 & e2 & c2 & na1 & A1 & b1 & na2 & A2 & b2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (conv_rows_lam_eq k L pb e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s h1 h2) in he.
    assert (hc1 : gcok G c1) by (eapply g_value_VLam_cok; exact hw1).
    assert (hc2 : gcok G c2) by (eapply g_value_VLam_cok; exact hw2).
    apply g_value_VLam_inv in hw1. apply g_value_VLam_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & hts2 & hn2 & ->).
    destruct (eqb_binder_annot na1 na2) eqn:Ena;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (binder_step k hT L Q lo G Conv e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s'
                hm hr hts1 hn1 hts2 hn2
                (cok_child G c1 0 A1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 0 A2 hc2 ltac:(rewrite h2; constructor))
                (cok_child G c1 1 b1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 1 b2 hc2 ltac:(rewrite h2; constructor)) he) as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as [hdom hbody].
    intros u1 u2 e1u e2u s1 s2 Δ hΔ hcl.
    cbn [lift subst] in e1u, e2u.
    destruct u1 as [| | | | |na1' A1u B1u| | | | | | | | | |]; cbn in e1u; try discriminate e1u.
    injection e1u as <- eA1 eB1.
    destruct u2 as [| | | | |na2' A2u B2u| | | | | | | | | |]; cbn in e2u; try discriminate e2u.
    injection e2u as <- eA2 eB2.
    unfold scl in s1, s2. cbn [on_free_vars] in s1, s2.
    apply andb_true_iff in s1 as [sA1 sB1]. apply andb_true_iff in s2 as [sA2 sB2].
    destruct (hdom A1u A2u eA1 eA2 sA1 sA2 Δ hΔ hcl) as [hd].
    assert (hΔ' : #|Δ ,, vass na1 A1u| = L + 1 - nctx) by (cbn; lia).
    destruct (hbody B1u B2u eB1 eB2 (scl_binder L B1u sB1) (scl_binder L B2u sB2)
                (Δ ,, vass na1 A1u) hΔ' (snoc_closed L Δ na1 A1u hL hΔ hcl sA1)) as [hbd].
    constructor.
    exact (ws_cumul_pb_Lambda (wfΣ := wfΣ) (eqb_binder_annot_spec _ _ Ena) hd hbd).
  Qed.

  Lemma conv_rows_prod_g (k : unit -> cbn_fuel) :
    spec_term (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 na1 A1 b1 na2 A2 b2,
                           v1 = VOpen e1 c1 /\ v2 = VOpen e2 c2
                           /\ c1.(c_term) = tProd na1 A1 b1 /\ c2.(c_term) = tProd na2 A2 b2).
  Proof.
    intros hT L Q lo G pb v1 v2 w1 w2 rs s b rs' s'
      (e1 & c1 & e2 & c2 & na1 & A1 & b1 & na2 & A2 & b2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite (conv_rows_prod_eq k L pb e1 c1 e2 c2 na1 A1 b1 na2 A2 b2 rs s h1 h2) in he.
    assert (hc1 : gcok G c1) by (inversion hw1; assumption).
    assert (hc2 : gcok G c2) by (inversion hw2; assumption).
    apply g_value_VOpen_inv in hw1. apply g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    destruct (g_susp_inv _ _ _ _ _ _ hw1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hw2) as (ts2 & hts2 & hn2 & ->).
    destruct (eqb_binder_annot na1 na2) eqn:Ena;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    destruct (binder_step k hT L Q lo G pb e1 e2 c1 c2 A1 A2 b1 b2 ts1 ts2 rs s b rs' s'
                hm hr hts1 hn1 hts2 hn2
                (cok_child G c1 0 A1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 0 A2 hc2 ltac:(rewrite h2; constructor))
                (cok_child G c1 1 b1 hc1 ltac:(rewrite h1; constructor))
                (cok_child G c2 1 b2 hc2 ltac:(rewrite h2; constructor)) he) as [hp hc].
    split; [exact hp|]. intros hb. destruct (hc hb) as [hdom hbody].
    intros u1 u2 e1u e2u s1 s2 Δ hΔ hcl.
    cbn [lift subst] in e1u, e2u.
    destruct u1 as [| | | |na1' A1u B1u| | | | | | | | | | |]; cbn in e1u; try discriminate e1u.
    injection e1u as <- eA1 eB1.
    destruct u2 as [| | | |na2' A2u B2u| | | | | | | | | | |]; cbn in e2u; try discriminate e2u.
    injection e2u as <- eA2 eB2.
    unfold scl in s1, s2. cbn [on_free_vars] in s1, s2.
    apply andb_true_iff in s1 as [sA1 sB1]. apply andb_true_iff in s2 as [sA2 sB2].
    destruct (hdom A1u A2u eA1 eA2 sA1 sA2 Δ hΔ hcl) as [hd].
    assert (hΔ' : #|Δ ,, vass na1 A1u| = L + 1 - nctx) by (cbn; lia).
    destruct (hbody B1u B2u eB1 eB2 (scl_binder L B1u sB1) (scl_binder L B2u sB2)
                (Δ ,, vass na1 A1u) hΔ' (snoc_closed L Δ na1 A1u hL hΔ hcl sA1)) as [hbd].
    constructor.
    exact (ws_cumul_pb_Prod (wfΣ := wfΣ) pb (eqb_binder_annot_spec _ _ Ena) hd hbd).
  Qed.

  (** ** [conv_value]: same code first, then the rows *)

  Lemma minv_tick L Q lo G s s' : tick s = Some s' -> MI L Q lo G s -> MI L Q lo G s'.
  Proof.
    intros ht [hL hQ hok hw]. destruct (tick_shape s s' ht) as (h1 & h2 & _ & h4 & h5).
    constructor; [exact hL|exact hQ| |exact (hwf_heap Q s s' h1 hw)].
    apply (gok_same X_type X Γ nctx Σ _ Q lo G s); [exact hok|exact h1|exact h2|exact h4|].
    eapply mok_memo; [exact h5|exact (gk_memo _ _ _ _ _ _ _ _ _ _ hok)].
  Qed.

  Lemma mkApps_inj_len f f' l l' : #|l| = #|l'| -> mkApps f l = mkApps f' l' -> f = f' /\ l = l'.
  Proof.
    revert l'. induction l as [|a l ih] using rev_ind; intros l' hl e.
    - destruct l'; [|discriminate hl]. split; [exact e|reflexivity].
    - destruct l' as [|a' l' _] using rev_ind; [rewrite length_app in hl; cbn in hl; lia|].
      rewrite !mkApps_app in e. cbn in e. injection e as e1 e2.
      rewrite !length_app in hl. cbn in hl.
      destruct (ih l' ltac:(lia) e1) as [-> ->]. subst a'. split; reflexivity.
  Qed.

  (** Every value reads as a head applied to the readings of its spine. *)
  Lemma g_value_spine Q G v t :
    g_value nctx Q G v t -> exists H T, t = mkApps H T /\ g_addrs G (spine_of v) T.
  Proof.
    intros h. destruct h;
      first [ eexists _, _; split; [reflexivity|eassumption]
            | exists t, []; split; [reflexivity|constructor] ].
  Qed.

  (** A value renamed without reshaping keeps the readings of its spine. *)
  Lemma spine_reads Q Q' G G' v v' H T :
    (forall t, g_value nctx Q G v t -> g_value nctx Q' G' v' (lift0 (Q' - Q) t)) ->
    mp_value kc v' = mp_value kc v ->
    g_value nctx Q G v (mkApps H T) -> g_addrs G (spine_of v) T ->
    g_addrs G' (spine_of v') (map (lift0 (Q' - Q)) T).
  Proof.
    intros hk hs hw hT.
    destruct (g_value_spine _ _ _ _ (hk _ hw)) as (H' & T' & e & hT').
    rewrite lift_mkApps in e.
    pose proof (f_equal (@length _) (f_equal spine_of hs)) as hl.
    rewrite !mp_spine_of, !length_map in hl.
    assert (hl' : #|map (lift0 (Q' - Q)) T| = #|T'|).
    { rewrite length_map, (g_addrs_length _ _ _ hT), (g_addrs_length _ _ _ hT'). lia. }
    destruct (mkApps_inj_len _ _ _ _ hl' e) as [_ <-]. exact hT'.
  Qed.

  Lemma cq_mkApps L Q pb H1 H2 T1 T2 :
    nctx <= L -> cq L Q pb H1 H2 -> cqs L Q T1 T2 -> cq L Q pb (mkApps H1 T1) (mkApps H2 T2).
  Proof.
    intros hL hh hs u1 u2 e1 e2 s1 s2.
    apply mkApps_lift0_inv in e1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in e2 as (h2' & us2 & -> & eh2 & ->).
    unfold scl in s1, s2. rewrite on_free_vars_mkApps in s1, s2.
    apply andb_true_iff in s1 as [sh1 sus1]. apply andb_true_iff in s2 as [sh2 sus2].
    apply cv_spine; [exact hL| |exact (hs us1 us2 eq_refl eq_refl sus1 sus2)].
    exact (hh h1' h2' eh1 eh2 sh1 sh2).
  Qed.

  Definition cv_same (d : cbn_fuel) (L : nat) (le : conv_pb) (v1 v2 : cbn_value)
      (e1 : cbn_env) (c1 : code) (e2 : cbn_env) (c2 : code) (spines : bool)
      (rs : list root) (s : cbn_state) :=
    match conv_same_code X_type X Γ nctx d L e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s with
    | COk (b, rs, s) =>
      match rs with
      | RV v1 :: RV v2 :: rs =>
        if b then
          if spines then conv_cells X_type X Γ nctx d L (spine_of v1) (spine_of v2) rs s
          else COk (true, rs, s)
        else conv_rows X_type X Γ nctx d L le v1 v2 rs s
      | _ => CFail WRoots
      end
    | CFail w => CFail w
    end.

  Lemma conv_value_eq k L le v1 v2 rs s :
    conv_value X_type X Γ nctx (FS k) L le v1 v2 rs s =
    match tick s with
    | None => CFail WSteps
    | Some s =>
      match v1, v2 with
      | VLam e1 c1, VLam e2 c2 | VOpen e1 c1, VOpen e2 c2 =>
        cv_same (k tt) L le v1 v2 e1 c1 e2 c2 false rs s
      | VStuck e1 c1 sp1, VStuck e2 c2 sp2 =>
        if #|sp1| == #|sp2| then cv_same (k tt) L le v1 v2 e1 c1 e2 c2 true rs s
        else conv_rows X_type X Γ nctx (k tt) L le v1 v2 rs s
      | VFix e1 c1 i1 sp1, VFix e2 c2 i2 sp2
      | VStuckFix e1 c1 i1 sp1, VStuckFix e2 c2 i2 sp2 =>
        if (i1 == i2) && (#|sp1| == #|sp2|) then cv_same (k tt) L le v1 v2 e1 c1 e2 c2 true rs s
        else conv_rows X_type X Γ nctx (k tt) L le v1 v2 rs s
      | _, _ => conv_rows X_type X Γ nctx (k tt) L le v1 v2 rs s
      end
    end.
  Proof. cbn. destruct (tick s); [|reflexivity]. destruct v1, v2; reflexivity. Qed.

  (** Closures and open values: the same code makes the two readings convertible. *)
  Lemma cv_same_flat (k : unit -> cbn_fuel) :
    spec_same (k tt) -> spec_rows (k tt) ->
    forall L Q lo G pb v1 v2 w1 w2 e1 c1 e2 c2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 w1 -> g_value nctx Q G v2 w2 ->
      g_susp nctx Q G e1 c1.(c_term) w1 -> gcok G c1 ->
      g_susp nctx Q G e2 c2.(c_term) w2 -> gcok G c2 ->
      cv_same (k tt) L pb v1 v2 e1 c1 e2 c2 false rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).
  Proof.
    intros hS hR L Q lo G pb v1 v2 w1 w2 e1 c1 e2 c2 rs s b rs' s' hm hr hv1 hv2 hw1 hw2
      hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    unfold cv_same in he.
    destruct (conv_same_code X_type X Γ nctx (k tt) L e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s)
      as [[[b0 rs0] s0]|w] eqn:E; [|discriminate he].
    destruct (conv_same_code_sound_ghost (k tt) hS L Q lo G pb e1 c1 e2 c2 w1 w2 _ s b0 rs0 s0
                hm (Forall_cons (RV v1) hv1 (Forall_cons (RV v2) hv2 hr)) hs1 hc1 hs2 hc2 E)
      as [hp0 hc0].
    destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbv beta iota in he.
    destruct b0.
    - injection he as <- <- <-. split; [|intros _; exact (hc0 eq_refl)].
      exists Q1, lo1, G1. split; [exact hq1|]. split; [exact hm1|].
      split; [exact (Forall_inv_tail (Forall_inv_tail hr1))|exact hgB].
    - destruct (hR L Q1 lo1 G1 pb v1' v2' _ _ rsB s0 b rs' s' I hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) (Forall_inv hr1)
                  (Forall_inv (Forall_inv_tail hr1)) (hk1 _ hw1) (hk2 _ hw2) he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. exact (cq_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  (** Stuck terms and fixpoints: the same code makes the heads convertible, then the spines are
    compared; the renamed values keep their shape, so their spines read as before. *)
  Lemma cv_same_spine (k : unit -> cbn_fuel) :
    spec_same (k tt) -> spec_cells (k tt) -> spec_rows (k tt) ->
    forall L Q lo G pb v1 v2 H1 H2 T1 T2 e1 c1 e2 c2 ts1 ts2 rs s b rs' s',
      MI L Q lo G s -> Forall (rwf Q) rs -> vwf Q v1 -> vwf Q v2 ->
      g_value nctx Q G v1 (mkApps H1 T1) -> g_value nctx Q G v2 (mkApps H2 T2) ->
      g_addrs G (spine_of v1) T1 -> g_addrs G (spine_of v2) T2 ->
      gcok G c1 -> gcok G c2 ->
      g_slots nctx Q G e1.(ev_vals) ts1 -> g_slots nctx Q G e2.(ev_vals) ts2 ->
      (e1.(ev_goff) = e2.(ev_goff) -> e1.(ev_nvals) = e2.(ev_nvals) ->
       samec c1.(c_term) c2.(c_term) -> cagree L Q c1.(c_term) 0 ts1 ts2 -> cq L Q pb H1 H2) ->
      cv_same (k tt) L pb v1 v2 e1 c1 e2 c2 true rs s = COk (b, rs', s') ->
      post L Q G rs s' rs' /\ (b = true -> cq L Q pb (mkApps H1 T1) (mkApps H2 T2)).
  Proof.
    intros hS hC hR L Q lo G pb v1 v2 H1 H2 T1 T2 e1 c1 e2 c2 ts1 ts2 rs s b rs' s'
      hm hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2 hhead he.
    pose proof hm as [hL hLQ _ _].
    unfold cv_same in he.
    destruct (conv_same_code X_type X Γ nctx (k tt) L e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s)
      as [[[b0 rs0] s0]|w] eqn:E; [|discriminate he].
    destruct (hS L Q lo G e1 c1 e2 c2 ts1 ts2 _ s b0 rs0 s0 hm
                (Forall_cons (RV v1) hv1 (Forall_cons (RV v2) hv2 hr)) hc1 hc2 hts1 hts2 E)
      as [hp0 hc0].
    destruct hp0 as (Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1).
    destruct (grq_cons_inv_skel _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA & hsk1).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (grq_cons_inv_skel _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB & hsk2).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbn in hsk1, hsk2. injection hsk1 as hsk1. injection hsk2 as hsk2.
    cbv beta iota in he.
    destruct b0.
    - destruct (hc0 eq_refl) as (hgo & hnv & hsame & hag).
      destruct (hC L Q1 lo1 G1 (spine_of v1') (spine_of v2') _ _ rsB s0 b rs' s' hm1
                  (Forall_inv_tail (Forall_inv_tail hr1))
                  (spine_reads Q Q1 G G1 v1 v1' H1 T1 hk1 hsk1 hw1 hT1)
                  (spine_reads Q Q1 G G1 v2 v2' H2 T2 hk2 hsk2 hw2 hT2) he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cq_mkApps L Q pb H1 H2 T1 T2 hL (hhead hgo hnv hsame hag)).
      exact (cqs_lift _ _ _ _ _ hLQ hq1 (hc hb)).
    - destruct (hR L Q1 lo1 G1 pb v1' v2' _ _ rsB s0 b rs' s' I hm1
                  (Forall_inv_tail (Forall_inv_tail hr1)) (Forall_inv hr1)
                  (Forall_inv (Forall_inv_tail hr1)) (hk1 _ hw1) (hk2 _ hw2) he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. exact (cq_lift _ _ _ _ _ _ hLQ hq1 (hc hb)).
  Qed.

  Lemma conv_value_sound_g (k : unit -> cbn_fuel) :
    spec_same (k tt) -> spec_cells (k tt) -> spec_rows (k tt) -> spec_value (FS k).
  Proof.
    intros hS hC hR L Q lo G pb v1 v2 w1 w2 rs s b rs' s' hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ hok _].
    rewrite conv_value_eq in he.
    destruct (tick s) as [s0|] eqn:Et; [|discriminate he].
    pose proof (minv_tick _ _ _ _ _ _ Et hm) as hm0.
    pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    assert (hrows : conv_rows X_type X Γ nctx (k tt) L pb v1 v2 rs s0 = COk (b, rs', s') ->
              post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2))
      by (intros h; exact (hR L Q lo G pb v1 v2 w1 w2 rs s0 b rs' s' I hm0 hr hv1 hv2 hw1 hw2 h)).
    destruct v1 as [h1 sp1|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|n1 sp1|e1 c1|e1 c1 sp1];
    destruct v2 as [h2 sp2|e2 c2|e2 c2 i2 sp2|e2 c2 i2 sp2|n2 sp2|e2 c2|e2 c2 sp2];
      cbv beta iota in he; try exact (hrows he).
    - (* closures *)
      exact (cv_same_flat k hS hR L Q lo G pb _ _ w1 w2 e1 c1 e2 c2 rs s0 b rs' s' hm0 hr hv1 hv2
               hw1 hw2 (g_value_VLam_inv _ _ _ _ _ _ hw1) (g_value_VLam_cok _ _ _ _ _ _ hw1)
               (g_value_VLam_inv _ _ _ _ _ _ hw2) (g_value_VLam_cok _ _ _ _ _ _ hw2) he).
    - (* fixpoints *)
      destruct ((i1 == i2) && (#|sp1| == #|sp2|)) eqn:Ei; [|exact (hrows he)].
      apply andb_true_iff in Ei as [Ei _]. apply eqb_eq in Ei. subst i2.
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply g_value_VFix_inv in hw1' as (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->).
      apply g_value_VFix_inv in hw2' as (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      apply (cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2 rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag. rewrite hct1, hct2 in hsame. rewrite hct1 in hag.
      pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia| | |exact (samec_fix _ _ _ _ _ hsame)|exact (cagree_fix _ _ _ _ _ _ _ _ hag)].
      + apply (hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
      + apply (hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
    - (* stuck fixpoints *)
      destruct ((i1 == i2) && (#|sp1| == #|sp2|)) eqn:Ei; [|exact (hrows he)].
      apply andb_true_iff in Ei as [Ei _]. apply eqb_eq in Ei. subst i2.
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply g_value_VStuckFix_inv in hw1' as (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->).
      apply g_value_VStuckFix_inv in hw2' as (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      apply (cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2 rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag. rewrite hct1, hct2 in hsame. rewrite hct1 in hag.
      pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia| | |exact (samec_fix _ _ _ _ _ hsame)|exact (cagree_fix _ _ _ _ _ _ _ _ hag)].
      + apply (hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
      + apply (hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
    - (* open values *)
      exact (cv_same_flat k hS hR L Q lo G pb _ _ w1 w2 e1 c1 e2 c2 rs s0 b rs' s' hm0 hr hv1 hv2
               hw1 hw2 (g_value_VOpen_inv _ _ _ _ _ _ hw1) ltac:(inversion hw1; assumption)
               (g_value_VOpen_inv _ _ _ _ _ _ hw2) ltac:(inversion hw2; assumption) he).
    - (* stuck matches and projections *)
      destruct (#|sp1| == #|sp2|) eqn:Ei; [|exact (hrows he)].
      pose proof hw1 as hw1'. pose proof hw2 as hw2'.
      apply g_value_VStuck_inv in hw1' as (H1 & T1 & hh1 & hT1 & ->).
      apply g_value_VStuck_inv in hw2' as (H2 & T2 & hh2 & hT2 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh1) as (ts1 & hts1 & hn1 & ->).
      destruct (g_susp_inv _ _ _ _ _ _ hh2) as (ts2 & hts2 & hn2 & ->).
      pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw1) as hc1.
      pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw2) as hc2.
      apply (cv_same_spine k hS hC hR L Q lo G pb _ _ _ _ T1 T2 e1 c1 e2 c2 ts1 ts2 rs s0 b rs' s'
               hm0 hr hv1 hv2 hw1 hw2 hT1 hT2 hc1 hc2 hts1 hts2); [|exact he].
      intros hgo hnv hsame hag.
      pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
      pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
      rewrite <- hgo, <- hnv.
      apply (same_code_cq L Q pb (ev_nvals e1) (ev_goff e1) ts1 ts2 _ _ hL hLQ);
        [lia|lia|exact (hch _ hc1)|exact (hch _ hc2)|exact hsame|exact hag].
  Qed.

  (** ** The stuck-match rule: the branches *)

  Lemma rbody_lift d ts N br :
    rbody (map (lift0 d) ts) (d + N) br = lift d #|br.(bcontext)| (rbody ts N br).
  Proof. unfold rbody. rewrite length_map. apply lift_bodyk. reflexivity. Qed.

  (** A branch body read through [n] fresh variables pushed on its environment, at the master
    level, is the lift of the logical body. *)
  Lemma fresh_branch_read L Q n N ts t U :
    L <= Q ->
    subst ts n (lift N (n + #|ts|) t) = lift (Q - L) n U ->
    subst (map (lift0 (Q - L)) (idsn n) ++ map (lift0 n) ts) 0 (lift (n + N) (n + #|ts|) t)
    = lift0 (Q - L) U.
  Proof.
    intros hLQ e.
    rewrite subst_app_simpl, length_map, idsn_length. cbn [Nat.add].
    rewrite (lift_bodyk n ts N #|ts| n t eq_refl), e.
    rewrite simpl_lift by lia.
    replace (n + (Q - L)) with ((Q - L) + n) by lia. apply cg_subst_fresh_lift.
  Qed.

  Lemma branches_lift L Q QC ts1 ts2 N1 N2 l1 l2 :
    L <= Q -> Q <= QC ->
    Forall2 (fun br1 br2 => case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cqb L QC #|br1.(bcontext)| Conv (rbody (map (lift0 (QC - Q)) ts1) ((QC - Q) + N1) br1)
                                         (rbody (map (lift0 (QC - Q)) ts2) ((QC - Q) + N2) br2))
      l1 l2 ->
    Forall2 (fun br1 br2 => case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cqb L Q #|br1.(bcontext)| Conv (rbody ts1 N1 br1) (rbody ts2 N2 br2)) l1 l2.
  Proof.
    intros hLQ hQ h. induction h as [|br1 br2 l1 l2 [hc hq] _ ih]; constructor; [|exact ih].
    split; [exact hc|]. apply (cqb_lift L Q QC _ Conv _ _ hLQ hQ).
    rewrite !rbody_lift in hq. destruct (case_ctx_ok_spec _ _ hc) as [hx _ _].
    rewrite <- (All2_length hx) in hq. exact hq.
  Qed.

  Lemma case_branches_sound_g (k : unit -> cbn_fuel) :
    spec_term (k tt) -> spec_branches (k tt) -> spec_branches (FS k).
  Proof.
    intros hT hB L Q lo G e1 c1 e2 c2 i l1 l2 ts1 ts2 rs s b rs' s'
      hm hr hb1 hb2 hs1 hn1 hs2 hn2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite case_branches_eq in he.
    destruct l1 as [|br1 l1]; destruct l2 as [|br2 l2].
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros _. constructor.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - injection he as <- <- <-.
      split; [exact (post_refl _ _ _ _ _ _ hm hr)|]. intros hb; discriminate hb.
    - inversion hb1 as [|i1 z1 m1 hc1 hb1']; subst.
      inversion hb2 as [|i2 z2 m2 hc2 hb2']; subst.
      cbv beta iota in he.
      destruct (case_ctx_ok (bcontext br1) (bcontext br2)) eqn:Ectx;
        [|injection he as <- <- <-;
          split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
      destruct (case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
      pose proof (All2_length hctx) as hn12.
      assert (hr0 : Forall (rwf Q) (RE e1 :: RE e2 :: rs))
        by (constructor; [exact I|constructor; [exact I|exact hr]]).
      pose proof (minv_raise L Q #|bcontext br1| lo G s hm) as hmR.
      pose proof (rwfs_mono Q (Q + #|bcontext br1|) _ ltac:(lia) hr0) as hrR.
      pose proof (grq_raise Q #|bcontext br1| G _ ltac:(lia) hr0) as hgR.
      pose proof (proj2 (g_slot_shift nctx Q #|bcontext br1| ltac:(lia) G) _ _ hs1) as [hs1R _].
      pose proof (proj2 (g_slot_shift nctx Q #|bcontext br1| ltac:(lia) G) _ _ hs2) as [hs2R _].
      destruct (push_fresh #|bcontext br1| L e1 e2 (RE e1 :: RE e2 :: rs) s)
        as [[[r rsP] sP]|w] eqn:EP; [|discriminate he].
      destruct (push_fresh_g #|bcontext br1| L (Q + #|bcontext br1|) lo (gshift #|bcontext br1| G)
                  L e1 e2 _ _ _ s r rsP sP hmR hrR ltac:(lia) hs1R hn1 hs2R hn2 EP)
        as (loP & GP & f1 & f2 & -> & hmP & hrP & hgP & hnf1 & hgf1 & hnf2 & hgf2 & hf1 & hf2).
      pose proof (push_fresh_skel _ _ _ _ _ _ _ _ _ EP) as hkP.
      cbv beta iota in he.
      pose proof (g_susp_of_slots nctx _ GP f1 (bbody br1) _ hf1 hnf1) as hB1.
      pose proof (g_susp_of_slots nctx _ GP f2 (bbody br2) _ hf2 hnf2) as hB2.
      destruct (conv_term X_type X Γ nctx (k tt) (L + #|bcontext br1|) Conv
                  f1 (child c1 (case_branch_step i) (bbody br1))
                  f2 (child c2 (case_branch_step i) (bbody br2)) rsP sP)
        as [[[bC rsC] sC]|w] eqn:EC; [|discriminate he].
      destruct (hT (L + #|bcontext br1|) (Q + #|bcontext br1|) loP GP Conv
                  f1 (child c1 (case_branch_step i) (bbody br1))
                  f2 (child c2 (case_branch_step i) (bbody br2)) _ _ rsP sP bC rsC sC
                  (minv_level L (L + #|bcontext br1|) (Q + #|bcontext br1|) loP GP sP hmP
                     ltac:(lia) ltac:(lia)) hrP hB1
                  (cok_gcx _ _ (proj1 hgP) _ hc1) hB2 (cok_gcx _ _ (proj1 hgP) _ hc2) EC)
        as [hpC hcC].
      (* the roots [push_fresh] handed back *)
      destruct (gren_cons_inv _ _ _ _ _ _ hgP) as (p1 & rsP1 & -> & hp1 & hgP1).
      destruct (gpres_RE_inv _ _ _ _ _ hp1) as (e1' & -> & (hne1 & hge1 & hke1)).
      destruct (gren_cons_inv _ _ _ _ _ _ hgP1) as (p2 & rsP' & -> & hp2 & hgP').
      destruct (gpres_RE_inv _ _ _ _ _ hp2) as (e2' & -> & (hne2 & hge2 & hke2)).
      assert (hgR' : grq Q (Q + #|bcontext br1|) G (gshift #|bcontext br1| G) rs rs).
      { destruct (grq_cons_inv _ _ _ _ _ _ _ hgR) as (a1 & ra & ea & _ & hga).
        injection ea as <- <-.
        destruct (grq_cons_inv _ _ _ _ _ _ _ hga) as (a2 & rb & eb & _ & hgb).
        injection eb as <- <-. exact hgb. }
      assert (hgP'' : grq (Q + #|bcontext br1|) (Q + #|bcontext br1|) (gshift #|bcontext br1| G)
                        GP rs rsP').
      { apply grq_of_gren; [exact hgP'|exact (sk_tl _ _ _ _ (sk_tl _ _ _ _ hkP))]. }
      destruct bC.
      + destruct hpC as (QC & loC & GC & hqC & hmC & hrC & hgC).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgC) as (q1 & rsC1 & -> & hqa & hgC1).
        destruct (gpq_RE_inv _ _ _ _ _ _ hqa) as (g1 & -> & hng1 & hgg1 & hkg1).
        destruct (grq_cons_inv _ _ _ _ _ _ _ hgC1) as (q2 & rsC' & -> & hqb & hgC').
        destruct (gpq_RE_inv _ _ _ _ _ _ hqb) as (g2 & -> & hng2 & hgg2 & hkg2).
        cbv beta iota in he.
        pose proof (hkg1 _ (hke1 _ hs1R)) as hg1s. pose proof (hkg2 _ (hke2 _ hs2R)) as hg2s.
        rewrite map_lift0_lift0 in hg1s, hg2s.
        replace (QC - (Q + #|bcontext br1|) + #|bcontext br1|) with (QC - Q) in hg1s, hg2s
          by lia.
        pose proof (g_slots_length _ _ _ _ _ hs1) as hl1.
        pose proof (g_slots_length _ _ _ _ _ hs2) as hl2.
        pose proof (g_slots_length _ _ _ _ _ hg1s) as hl1'. rewrite length_map in hl1'.
        pose proof (g_slots_length _ _ _ _ _ hg2s) as hl2'. rewrite length_map in hl2'.
        destruct (hB L QC loC GC g1 c1 g2 c2 (N.succ i) l1 l2 _ _ rsC' sC b rs' s'
                    (minv_level _ L _ _ _ _ hmC ltac:(lia) ltac:(lia))
                    (Forall_inv_tail (Forall_inv_tail hrC))
                    (bcodes_gcx _ _ _ _ _ (proj1 hgC)
                       (bcodes_gcx _ _ _ _ _ (proj1 hgP)
                          (bcodes_gcx G (gshift #|bcontext br1| G) _ _ _ (fun _ _ h => h) hb1')))
                    (bcodes_gcx _ _ _ _ _ (proj1 hgC)
                       (bcodes_gcx _ _ _ _ _ (proj1 hgP)
                          (bcodes_gcx G (gshift #|bcontext br1| G) _ _ _ (fun _ _ h => h) hb2')))
                    hg1s ltac:(lia) hg2s ltac:(lia) he) as [hp hc].
        split.
        * apply (post_compose L Q (Q + #|bcontext br1|) G _ rs rs s' rs' ltac:(lia) hgR').
          apply (post_compose L _ _ _ GP rs rsP' s' rs' (le_n _) hgP'').
          exact (post_compose L _ QC GP GC rsP' rsC' s' rs' hqC hgC' hp).
        * intros hb. constructor.
          -- split; [exact Ectx|]. intros U1 U2 eU1 eU2 sU1 sU2.
             apply (hcC eq_refl U1 U2); [| |exact sU1|exact sU2].
             ++ replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                rewrite hgf1, hnf1.
                pose proof (g_slots_length _ _ _ _ _ hf1) as hlf.
                rewrite length_app, length_map, idsn_length, length_map in hlf.
                rewrite <- hlf.
                replace (Q + #|bcontext br1| - nctx + ev_goff e1)
                  with (#|bcontext br1| + (Q - nctx + ev_goff e1)) by lia.
                replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                apply fresh_branch_read; [lia|]. exact eU1.
             ++ replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                rewrite hgf2, hnf2.
                pose proof (g_slots_length _ _ _ _ _ hf2) as hlf.
                rewrite length_app, length_map, idsn_length, length_map in hlf.
                rewrite <- hlf.
                replace (Q + #|bcontext br1| - nctx + ev_goff e2)
                  with (#|bcontext br1| + (Q - nctx + ev_goff e2)) by lia.
                replace (Q + #|bcontext br1| - (L + #|bcontext br1|)) with (Q - L) by lia.
                apply fresh_branch_read; [lia|]. unfold rbody in eU2. rewrite <- hn12 in eU2.
                exact eU2.
          -- apply (branches_lift L Q QC ts1 ts2 _ _ l1 l2 hLQ ltac:(lia)).
             rewrite hgg1, hge1, hgg2, hge2 in hc.
             replace (QC - nctx + ev_goff e1) with ((QC - Q) + (Q - nctx + ev_goff e1)) in hc
               by lia.
             replace (QC - nctx + ev_goff e2) with ((QC - Q) + (Q - nctx + ev_goff e2)) in hc
               by lia.
             exact (hc hb).
      + cbv beta iota in he. injection he as <- <- <-.
        split; [|intros hb; discriminate hb].
        apply (post_compose L Q (Q + #|bcontext br1|) G _ rs rs _ _ ltac:(lia) hgR').
        apply (post_compose L _ _ _ GP rs rsP' _ _ (le_n _) hgP'').
        apply (post_drop2 L _ GP (RE e1') (RE e2') rsP').
        exact (post_level L (L + #|bcontext br1|) (Q + #|bcontext br1|) GP _ _ _ hL
                 ltac:(lia) hpC).
  Qed.

  (** ** The read-back: the machine side

    The read-back functions [rb_cell], [rb_slot], [rb_susp] and [rb_value] only read the heap
    and [tick]: they leave the heap, the next address, the context map and the memo alone
    ([rb_state]), so they keep [minv] whatever the readings are ([rb_minv]). *)

  Definition sst (s s' : cbn_state) : Prop :=
    s'.(st_heap) = s.(st_heap) /\ s'.(st_next) = s.(st_next) /\ s'.(st_gam) = s.(st_gam)
    /\ s'.(st_memo) = s.(st_memo).

  Lemma sst_refl s : sst s s.
  Proof. repeat split. Qed.

  Lemma sst_trans s1 s2 s3 : sst s1 s2 -> sst s2 s3 -> sst s1 s3.
  Proof. intros (a1 & b1 & c1 & d1) (a2 & b2 & c2 & d2). repeat split; congruence. Qed.

  Lemma map_st_sst {A B : Type} (f : A -> cbn_state -> cbn_res (B * cbn_state)) :
    (forall x s y s', f x s = COk (y, s') -> sst s s') ->
    forall l s ys s', map_st f l s = COk (ys, s') -> sst s s'.
  Proof.
    intros hf. induction l as [|x l ih]; intros s ys s' h; cbn in h.
    - injection h as _ <-. apply sst_refl.
    - destruct (f x s) as [[y s1]|w] eqn:E1; [|discriminate h].
      destruct (map_st f l s1) as [[ys1 s2]|w] eqn:E2; [|discriminate h].
      injection h as _ <-. exact (sst_trans _ _ _ (hf _ _ _ _ E1) (ih _ _ _ E2)).
  Qed.

  Lemma rb_state (n : nat) (d : cbn_fuel) :
    (forall lvl a s t s', rb_cell n d lvl a s = COk (t, s') -> sst s s')
    /\ (forall lvl x s t s', rb_slot n d lvl x s = COk (t, s') -> sst s s')
    /\ (forall lvl e u s t s', rb_susp n d lvl e u s = COk (t, s') -> sst s s')
    /\ (forall lvl v s t s', rb_value n d lvl v s = COk (t, s') -> sst s s').
  Proof.
    induction d as [|k ih].
    { repeat split; intros; match goal with h : _ = COk _ |- _ => cbn in h; discriminate h end. }
    destruct (ih tt) as (hc & hsl & hsu & hv).
    assert (hsp : forall lvl h0 sp s t s',
               match map_st (rb_cell n (k tt) lvl) sp s with
               | COk (ts, s) => COk (mkApps h0 ts, s)
               | CFail w => CFail w
               end = COk (t, s') -> sst s s').
    { intros lvl h0 sp s t s' h.
      destruct (map_st (rb_cell n (k tt) lvl) sp s) as [[ts s1]|w] eqn:Em; [|discriminate h].
      injection h as _ <-. exact (map_st_sst _ (fun x s0 y s0' hh => hc _ _ _ _ _ hh) _ _ _ _ Em). }
    split; [|split; [|split]].
    - intros lvl a s t s' h. cbn [rb_cell] in h.
      destruct (heap_get a s) as [[vs nv o c|v| |b]|]; try discriminate h.
      + exact (hsu _ _ _ _ _ _ h).
      + exact (hv _ _ _ _ _ h).
    - intros lvl x s t s' h. cbn [rb_slot] in h.
      destruct x as [a|vs nv o c]; [exact (hc _ _ _ _ _ h)|exact (hsu _ _ _ _ _ _ h)].
    - intros lvl e u s t s' h. cbn [rb_susp] in h.
      destruct (tick s) as [s0|] eqn:Et; [|discriminate h].
      destruct (map_st (rb_slot n (k tt) lvl) (ev_vals e) s0) as [[ts s1]|w] eqn:Em;
        [|discriminate h].
      injection h as _ <-.
      destruct (tick_shape s s0 Et) as (th & tn & _ & tg & tm).
      apply (sst_trans s s0 s1); [repeat split; assumption|].
      exact (map_st_sst _ (fun x s2 y s2' hh => hsl _ _ _ _ _ hh) _ _ _ _ Em).
    - intros lvl v s t s' h. cbn [rb_value] in h.
      destruct v as [h0 sp|e c|e c i sp|e c i sp|[l|h0] sp|e c|e c sp].
      + exact (hsp _ _ _ _ _ _ h).
      + exact (hsu _ _ _ _ _ _ h).
      + destruct (c_term c); try discriminate h.
        destruct (rb_susp n (k tt) lvl e _ s) as [[h1 s1]|w] eqn:E1; [|discriminate h].
        exact (sst_trans _ _ _ (hsu _ _ _ _ _ _ E1) (hsp _ _ _ _ _ _ h)).
      + destruct (c_term c); try discriminate h.
        destruct (rb_susp n (k tt) lvl e _ s) as [[h1 s1]|w] eqn:E1; [|discriminate h].
        exact (sst_trans _ _ _ (hsu _ _ _ _ _ _ E1) (hsp _ _ _ _ _ _ h)).
      + exact (hsp _ _ _ _ _ _ h).
      + exact (hsp _ _ _ _ _ _ h).
      + exact (hsu _ _ _ _ _ _ h).
      + destruct (rb_susp n (k tt) lvl e (c_term c) s) as [[h1 s1]|w] eqn:E1; [|discriminate h].
        exact (sst_trans _ _ _ (hsu _ _ _ _ _ _ E1) (hsp _ _ _ _ _ _ h)).
  Qed.

  Lemma rb_minv L Q lo G d lvl e t s u s' :
    rb_susp nctx d lvl e t s = COk (u, s') -> MI L Q lo G s -> MI L Q lo G s'.
  Proof.
    intros h hm. destruct (proj1 (proj2 (proj2 (rb_state nctx d))) _ _ _ _ _ _ h)
      as (e1 & e2 & e3 & e4).
    eapply minv_same; [exact hm|exact e1|exact e2|exact e3|exact e4].
  Qed.

  (** ** The read-back: the conversion side

    [rb_sound] of [PCUICCallByNeedSoundLevel], which
    [PCUICCallByNeedSoundReadBack.rb_sound_holds] proves. *)
  Context (hrb : rb_sound X_type X Γ nctx Σ).

  (** Two heads that reduce to terms equal up to universes at [Conv] (with [napp] arguments),
    applied to convertible spines, are convertible at any [conv_pb]. *)
  Lemma cv_rb_spine L pb h1 h2 r1 r2 us1 us2 :
    nctx <= L -> scl L h1 -> scl L h2 -> forallb (scl L) us1 -> forallb (scl L) us2 ->
    (forall Δ, #|Δ| = L - nctx -> ∥ PCUICReduction.red Σ (Γ ,,, Δ) h1 r1 ∥) ->
    (forall Δ, #|Δ| = L - nctx -> ∥ PCUICReduction.red Σ (Γ ,,, Δ) h2 r2 ∥) ->
    compare_term_napp Σ Σ Conv #|us1| r1 r2 -> cvs L us1 us2 ->
    cv L pb (mkApps h1 us1) (mkApps h2 us2).
  Proof.
    intros hL sh1 sh2 sus1 sus2 hd1 hd2 hcmp hcs Δ hΔ hcl.
    destruct (hd1 Δ hΔ) as [rd1]. destruct (hd2 Δ hΔ) as [rd2].
    destruct (hcs Δ hΔ hcl) as [hs].
    pose proof (red_scl L Δ h1 r1 hL hΔ hcl sh1 rd1) as sr1.
    pose proof (red_scl L Δ h2 r2 hL hΔ hcl sh2 rd2) as sr2.
    assert (ho1 : is_open_term (Γ ,,, Δ) (mkApps h1 us1)).
    { apply (scl_open L Δ _ hL hΔ). unfold scl. rewrite on_free_vars_mkApps.
      apply andb_true_iff. split; assumption. }
    assert (ho2 : is_open_term (Γ ,,, Δ) (mkApps h2 us2)).
    { apply (scl_open L Δ _ hL hΔ). unfold scl. rewrite on_free_vars_mkApps.
      apply andb_true_iff. split; assumption. }
    constructor.
    eapply (ws_cumul_pb_closed_red (wfΣ := wfΣ)).
    - apply into_closed_red; [|exact hcl|exact ho1].
      apply PCUICReduction.red_mkApps_f. exact rd1.
    - apply into_closed_red; [|exact hcl|exact ho2].
      apply PCUICReduction.red_mkApps_f. exact rd2.
    - apply (ws_cumul_eq_pb (wfΣ := wfΣ)).
      apply (ws_cumul_pb_mkApps_napp (wfΣ := wfΣ));
        [exact hcl|exact (scl_open L Δ r1 hL hΔ sr1)|exact (scl_open L Δ r2 hL hΔ sr2)
        |exact hcmp|exact hs].
  Qed.

  (** Read back two heads, compare them syntactically, then compare the spines: the fallback
    of the stuck-term row and the fixpoint rows. *)
  Definition head_rb (d : cbn_fuel) (L : nat) (e1 : cbn_env) (a1 : term) (e2 : cbn_env)
      (a2 : term) (n : nat) (sp1 sp2 : list haddr) (rs : list root) (s : cbn_state) :=
    match rb_susp nctx d L e1 a1 s with
    | COk (t1, s) =>
      match rb_susp nctx d L e2 a2 s with
      | COk (t2, s) =>
        if cmp_term X_type X Conv n t1 t2 then conv_cells X_type X Γ nctx d L sp1 sp2 rs s
        else COk (false, rs, s)
      | CFail w => CFail w
      end
    | CFail w => CFail w
    end.

  Lemma head_rb_g (k : unit -> cbn_fuel) (hC : spec_cells (k tt))
      L Q lo G pb e1 a1 e2 a2 sp1 sp2 H1 H2 T1 T2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    on_free_vars xpredT a1 -> on_free_vars xpredT a2 ->
    g_susp nctx Q G e1 a1 H1 -> g_susp nctx Q G e2 a2 H2 ->
    g_addrs G sp1 T1 -> g_addrs G sp2 T2 ->
    head_rb (k tt) L e1 a1 e2 a2 #|sp1| sp1 sp2 rs s = COk (b, rs', s') ->
    post L Q G rs s' rs' /\ (b = true -> cq L Q pb (mkApps H1 T1) (mkApps H2 T2)).
  Proof.
    intros hm hr hy1 hy2 hs1 hs2 hT1 hT2 he.
    pose proof hm as [hL hLQ _ _].
    unfold head_rb in he.
    destruct (rb_susp nctx (k tt) L e1 a1 s) as [[r1 s1]|w] eqn:E1; [|discriminate he].
    destruct (rb_susp nctx (k tt) L e2 a2 s1) as [[r2 s2]|w] eqn:E2; [|discriminate he].
    pose proof (rb_minv L Q lo G _ _ _ _ _ _ _ E1 hm) as hm1.
    pose proof (rb_minv L Q lo G _ _ _ _ _ _ _ E2 hm1) as hm2.
    destruct (cmp_term X_type X Conv #|sp1| r1 r2) eqn:Ecmp;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm2 hr)|intros hb; discriminate hb]].
    destruct (hC L Q lo G sp1 sp2 T1 T2 rs s2 b rs' s' hm2 hr hT1 hT2 he) as [hp hc].
    split; [exact hp|]. intros hb u1 u2 eu1 eu2 su1 su2.
    apply mkApps_lift0_inv in eu1 as (h1' & us1 & -> & eh1 & ->).
    apply mkApps_lift0_inv in eu2 as (h2' & us2 & -> & eh2 & ->).
    unfold scl in su1, su2. rewrite on_free_vars_mkApps in su1, su2.
    apply andb_true_iff in su1 as [sh1 sus1]. apply andb_true_iff in su2 as [sh2 sus2].
    subst H1 H2.
    destruct (hrb (k tt) L Q lo G e1 a1 h1' s hm hy1 (scl_hyg L h1' sh1) hs1 r1 s1 E1)
      as [_ hd1].
    destruct (hrb (k tt) L Q lo G e2 a2 h2' s1 hm1 hy2 (scl_hyg L h2' sh2) hs2 r2 s2 E2)
      as [_ hd2].
    apply (cv_rb_spine L pb h1' h2' r1 r2 us1 us2 hL sh1 sh2 sus1 sus2 hd1 hd2).
    - pose proof (cmp_term_sound X_type X Σ hΣ Conv _ r1 r2 Ecmp) as hcmp.
      rewrite <- (g_addrs_length _ _ _ hT1), length_map in hcmp. exact hcmp.
    - exact (hc hb us1 us2 eq_refl eq_refl sus1 sus2).
  Qed.

  (** *** The primitive row *)

  Lemma conv_rows_prim_eq k L le e1 c1 e2 c2 p1 p2 rs s :
    c1.(c_term) = tPrim p1 -> c2.(c_term) = tPrim p2 ->
    conv_rows X_type X Γ nctx (FS k) L le (VOpen e1 c1) (VOpen e2 c2) rs s =
    match rb_susp nctx (k tt) L e1 (tPrim p1) s with
    | COk (t1, s) =>
      match rb_susp nctx (k tt) L e2 (tPrim p2) s with
      | COk (t2, s) => COk (cmp_term X_type X Conv 0 t1 t2, rs, s)
      | CFail w => CFail w
      end
    | CFail w => CFail w
    end.
  Proof. destruct c1 as [i1 q1 t1], c2 as [i2 q2 t2]. cbn [c_term]. intros -> ->. reflexivity. Qed.

  Lemma conv_rows_prim_g (k : unit -> cbn_fuel) :
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 e2 c2 p1 p2,
                           v1 = VOpen e1 c1 /\ v2 = VOpen e2 c2
                           /\ c1.(c_term) = tPrim p1 /\ c2.(c_term) = tPrim p2).
  Proof.
    intros L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & e2 & c2 & p1 & p2 & -> & -> & h1 & h2)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ hok _].
    pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    assert (hc1 : gcok G c1) by (inversion hw1; assumption).
    assert (hc2 : gcok G c2) by (inversion hw2; assumption).
    apply g_value_VOpen_inv in hw1. apply g_value_VOpen_inv in hw2.
    rewrite h1 in hw1. rewrite h2 in hw2.
    assert (hy1 : on_free_vars xpredT (tPrim p1)) by (rewrite <- h1; exact (hch _ hc1)).
    assert (hy2 : on_free_vars xpredT (tPrim p2)) by (rewrite <- h2; exact (hch _ hc2)).
    rewrite (conv_rows_prim_eq k L pb e1 c1 e2 c2 p1 p2 rs s h1 h2) in he.
    destruct (rb_susp nctx (k tt) L e1 (tPrim p1) s) as [[r1 s1]|w] eqn:E1; [|discriminate he].
    destruct (rb_susp nctx (k tt) L e2 (tPrim p2) s1) as [[r2 s2]|w] eqn:E2; [|discriminate he].
    pose proof (rb_minv L Q lo G _ _ _ _ _ _ _ E1 hm) as hm1.
    pose proof (rb_minv L Q lo G _ _ _ _ _ _ _ E2 hm1) as hm2.
    injection he as <- <- <-.
    split; [exact (post_refl _ _ _ _ _ _ hm2 hr)|].
    intros hb u1 u2 eu1 eu2 su1 su2. subst w1 w2.
    destruct (hrb (k tt) L Q lo G e1 _ u1 s hm hy1 (scl_hyg L u1 su1) hw1 r1 s1 E1) as [_ hd1].
    destruct (hrb (k tt) L Q lo G e2 _ u2 s1 hm1 hy2 (scl_hyg L u2 su2) hw2 r2 s2 E2) as [_ hd2].
    exact (cv_rb_spine L pb u1 u2 r1 r2 [] [] hL su1 su2 eq_refl eq_refl hd1 hd2
             (cmp_term_sound X_type X Σ hΣ Conv 0 r1 r2 hb)
             (fun Δ _ _ => sq All2_nil)).
  Qed.

  (** *** The fixpoint rows *)

  Lemma conv_rows_fix_eq k L le e1 c1 i1 sp1 e2 c2 i2 sp2 rs s :
    conv_rows X_type X Γ nctx (FS k) L le (VFix e1 c1 i1 sp1) (VFix e2 c2 i2 sp2) rs s =
    if (i1 == i2) && (#|sp1| == #|sp2|) then
      match c1.(c_term), c2.(c_term) with
      | tFix m1 _, tFix m2 _ => head_rb (k tt) L e1 (tFix m1 i1) e2 (tFix m2 i2) #|sp1| sp1 sp2 rs s
      | _, _ => COk (false, rs, s)
      end
    else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_sfix_eq k L le e1 c1 i1 sp1 e2 c2 i2 sp2 rs s :
    conv_rows X_type X Γ nctx (FS k) L le (VStuckFix e1 c1 i1 sp1)
      (VStuckFix e2 c2 i2 sp2) rs s =
    if (i1 == i2) && (#|sp1| == #|sp2|) then
      match c1.(c_term), c2.(c_term) with
      | tFix m1 _, tFix m2 _ => head_rb (k tt) L e1 (tFix m1 i1) e2 (tFix m2 i2) #|sp1| sp1 sp2 rs s
      | _, _ => COk (false, rs, s)
      end
    else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma fix_rows_core (k : unit -> cbn_fuel) (hC : spec_cells (k tt))
      L Q lo G pb e1 c1 i1 sp1 e2 c2 i2 sp2 w1 w2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    (exists m1 idx1 H1 T1, c1.(c_term) = tFix m1 idx1 /\ g_susp nctx Q G e1 (tFix m1 i1) H1
       /\ gcok G c1 /\ g_addrs G sp1 T1 /\ w1 = mkApps H1 T1) ->
    (exists m2 idx2 H2 T2, c2.(c_term) = tFix m2 idx2 /\ g_susp nctx Q G e2 (tFix m2 i2) H2
       /\ gcok G c2 /\ g_addrs G sp2 T2 /\ w2 = mkApps H2 T2) ->
    (if (i1 == i2) && (#|sp1| == #|sp2|) then
       match c1.(c_term), c2.(c_term) with
       | tFix m1 _, tFix m2 _ =>
         head_rb (k tt) L e1 (tFix m1 i1) e2 (tFix m2 i2) #|sp1| sp1 sp2 rs s
       | _, _ => COk (false, rs, s)
       end
     else COk (false, rs, s)) = COk (b, rs', s') ->
    post L Q G rs s' rs' /\ (b = true -> cq L Q pb w1 w2).
  Proof.
    intros hm hr (m1 & idx1 & H1 & T1 & hct1 & hh1 & hc1 & hT1 & ->)
      (m2 & idx2 & H2 & T2 & hct2 & hh2 & hc2 & hT2 & ->) he.
    pose proof hm as [hL hLQ hok _].
    pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q lo G s hok hhyg) as hch.
    destruct ((i1 == i2) && (#|sp1| == #|sp2|));
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    rewrite hct1, hct2 in he.
    apply (head_rb_g k hC L Q lo G pb e1 (tFix m1 i1) e2 (tFix m2 i2) sp1 sp2 H1 H2 T1 T2 rs s b rs' s' hm hr);
      [| |exact hh1|exact hh2|exact hT1|exact hT2|exact he].
    - apply (hyg_tFix_idx _ idx1). rewrite <- hct1. exact (hch _ hc1).
    - apply (hyg_tFix_idx _ idx2). rewrite <- hct2. exact (hch _ hc2).
  Qed.

  (** *** The stuck-term row: the case congruence, then the read-back of the heads *)

  Lemma conv_rows_stuck_eq k L le e1 c1 sp1 e2 c2 sp2 rs s :
    conv_rows X_type X Γ nctx (FS k) L le (VStuck e1 c1 sp1) (VStuck e2 c2 sp2) rs s =
    if #|sp1| == #|sp2| then
      match match c1.(c_term), c2.(c_term) with
            | tCase _ _ _ _, tCase _ _ _ _ =>
              case_cong X_type X Γ nctx (k tt) L e1 c1 e2 c2
                (RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs) s
            | _, _ => COk (false, RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs, s)
            end with
      | COk (b, rs, s) =>
        match rs with
        | RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs =>
          if b then conv_cells X_type X Γ nctx (k tt) L sp1 sp2 rs s
          else head_rb (k tt) L e1 c1.(c_term) e2 c2.(c_term) #|sp1| sp1 sp2 rs s
        | _ => CFail WRoots
        end
      | CFail w => CFail w
      end
    else COk (false, rs, s).
  Proof. reflexivity. Qed.

  Lemma conv_rows_stuck_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) -> spec_case (k tt) ->
    spec_rows_on (FS k) (fun v1 v2 => exists e1 c1 sp1 e2 c2 sp2,
                           v1 = VStuck e1 c1 sp1 /\ v2 = VStuck e2 c2 sp2).
  Proof.
    intros hC hK L Q lo G pb v1 v2 w1 w2 rs s b rs' s' (e1 & c1 & sp1 & e2 & c2 & sp2 & -> & ->)
      hm hr hv1 hv2 hw1 hw2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite conv_rows_stuck_eq in he.
    destruct (#|sp1| == #|sp2|);
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    pose proof hw1 as hw1'. pose proof hw2 as hw2'.
    apply g_value_VStuck_inv in hw1' as (H1 & T1 & hh1 & hT1 & ->).
    apply g_value_VStuck_inv in hw2' as (H2 & T2 & hh2 & hT2 & ->).
    pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw1) as hc1.
    pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw2) as hc2.
    assert (hr0 : Forall (rwf Q) (RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs))
      by (constructor; [exact hv1|constructor; [exact hv2|exact hr]]).
    destruct (match c1.(c_term), c2.(c_term) with
              | tCase _ _ _ _, tCase _ _ _ _ =>
                case_cong X_type X Γ nctx (k tt) L e1 c1 e2 c2
                  (RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs) s
              | _, _ => COk (false, RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs, s)
              end) as [[[bK rsK] sK]|w] eqn:EK; [|discriminate he].
    assert (hK' : post L Q G (RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs) sK rsK
                  /\ (bK = true -> cq L Q pb H1 H2)).
    { destruct (c_term c1) eqn:Ec1;
        try (injection EK as <- <- <-;
             split; [exact (post_refl _ _ _ _ _ _ hm hr0)|intros hb; discriminate hb]).
      destruct (c_term c2) eqn:Ec2;
        try (injection EK as <- <- <-;
             split; [exact (post_refl _ _ _ _ _ _ hm hr0)|intros hb; discriminate hb]).
      rewrite <- Ec1 in hh1. rewrite <- Ec2 in hh2.
      exact (hK L Q lo G pb e1 c1 e2 c2 H1 H2 _ s bK rsK sK hm hr0 hh1 hc1 hh2 hc2 EK). }
    destruct hK' as [(Q1 & lo1 & G1 & hq1 & hm1 & hr1 & hg1) hcK].
    destruct (grq_cons_inv_skel _ _ _ _ _ _ _ hg1) as (q1 & rsA & -> & hqa & hgA & hsk1).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqa) as (v1' & -> & hk1).
    destruct (grq_cons_inv_skel _ _ _ _ _ _ _ hgA) as (q2 & rsB & -> & hqb & hgB & hsk2).
    destruct (gpq_RV_inv _ _ _ _ _ _ hqb) as (v2' & -> & hk2).
    cbn in hsk1, hsk2. injection hsk1 as hsk1. injection hsk2 as hsk2.
    pose proof (spine_reads Q Q1 G G1 _ v1' H1 T1 hk1 hsk1 hw1 hT1) as hT1'.
    pose proof (spine_reads Q Q1 G G1 _ v2' H2 T2 hk2 hsk2 hw2 hT2) as hT2'.
    pose proof (hk1 _ hw1) as hw1''. pose proof (hk2 _ hw2) as hw2''.
    destruct v1' as [| | | | | |e1' c1' sp1']; cbv beta iota in he; try discriminate he.
    destruct v2' as [| | | | | |e2' c2' sp2']; cbv beta iota in he; try discriminate he.
    cbn [spine_of] in hT1', hT2'.
    pose proof (Forall_inv_tail (Forall_inv_tail hr1)) as hrB.
    destruct bK.
    - destruct (hC L Q1 lo1 G1 sp1' sp2' _ _ rsB sK b rs' s' hm1 hrB hT1' hT2' he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cq_mkApps L Q pb H1 H2 T1 T2 hL (hcK eq_refl)).
      exact (cqs_lift _ _ _ _ _ hLQ hq1 (hc hb)).
    - pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw1'') as hc1'.
      pose proof (g_value_VStuck_cok _ _ _ _ _ _ _ hw2'') as hc2'.
      apply g_value_VStuck_inv in hw1'' as (H1' & T1' & hh1' & hT1'' & eh1).
      apply g_value_VStuck_inv in hw2'' as (H2' & T2' & hh2' & hT2'' & eh2).
      rewrite lift_mkApps in eh1, eh2.
      assert (hl1 : #|map (lift0 (Q1 - Q)) T1| = #|T1'|).
      { rewrite (g_addrs_length _ _ _ hT1'), (g_addrs_length _ _ _ hT1''). reflexivity. }
      assert (hl2 : #|map (lift0 (Q1 - Q)) T2| = #|T2'|).
      { rewrite (g_addrs_length _ _ _ hT2'), (g_addrs_length _ _ _ hT2''). reflexivity. }
      destruct (mkApps_inj_len _ _ _ _ hl1 eh1) as [<- _].
      destruct (mkApps_inj_len _ _ _ _ hl2 eh2) as [<- _].
      pose proof hm1 as [_ _ hok1 _].
      pose proof (gok_codes_hyg X_type X Γ nctx Σ _ Q1 lo1 G1 sK hok1 hhyg) as hch1.
      destruct (head_rb_g k hC L Q1 lo1 G1 pb e1' _ e2' _ sp1' sp2' _ _ _ _ rsB sK b rs' s'
                  hm1 hrB (hch1 _ hc1') (hch1 _ hc2') hh1' hh2' hT1' hT2' he) as [hp hc].
      split; [exact (post_compose _ _ _ _ _ _ _ _ _ hq1 hgB hp)|].
      intros hb. apply (cq_lift L Q Q1 pb _ _ hLQ hq1).
      rewrite !lift_mkApps. exact (hc hb).
  Qed.

  (** *** All the rows *)

  Local Ltac rows_false hm hr he :=
    match type of he with
    | conv_rows ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 = _ =>
      change (conv_rows a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) with (COk (false, a10, a11)) in he
    end;
    injection he as <- <- <-;
    split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb].

  Lemma conv_rows_sound_g (k : unit -> cbn_fuel) :
    spec_cells (k tt) -> spec_term (k tt) -> spec_case (k tt) -> spec_rows (FS k).
  Proof.
    intros hC hT hK L Q lo G pb v1 v2 w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he.
    destruct v1 as [h1 sp1|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|[l1|h1] sp1|e1 c1|e1 c1 sp1];
    destruct v2 as [h2 sp2|e2 c2|e2 c2 i2 sp2|e2 c2 i2 sp2|[l2|h2] sp2|e2 c2|e2 c2 sp2];
      try (rows_false hm hr he).
    - refine (conv_rows_con_g k hC L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
      do 4 eexists. repeat split.
    - destruct c1 as [ci1 cp1 ct1], c2 as [ci2 cp2 ct2].
      destruct ct1; try (rows_false hm hr he).
      destruct ct2; try (rows_false hm hr he).
      refine (conv_rows_lam_g k hT L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
      do 10 eexists. repeat split.
    - rewrite conv_rows_fix_eq in he.
      pose proof hw1 as hf1. apply g_value_VFix_inv in hf1.
      pose proof hw2 as hf2. apply g_value_VFix_inv in hf2.
      exact (fix_rows_core k hC L Q lo G pb e1 c1 i1 sp1 e2 c2 i2 sp2 w1 w2 rs s b rs' s'
               hm hr hf1 hf2 he).
    - rewrite conv_rows_sfix_eq in he.
      pose proof hw1 as hf1. apply g_value_VStuckFix_inv in hf1.
      pose proof hw2 as hf2. apply g_value_VStuckFix_inv in hf2.
      exact (fix_rows_core k hC L Q lo G pb e1 c1 i1 sp1 e2 c2 i2 sp2 w1 w2 rs s b rs' s'
               hm hr hf1 hf2 he).
    - refine (conv_rows_var_g k hC L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
      do 4 eexists. repeat split.
    - refine (conv_rows_const_g k hC L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
      do 4 eexists. repeat split.
    - destruct c1 as [ci1 cp1 ct1], c2 as [ci2 cp2 ct2].
      destruct ct1; try (rows_false hm hr he).
      all: destruct ct2; try (rows_false hm hr he).
      + refine (conv_rows_sort_g k L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
        do 6 eexists. repeat split.
      + refine (conv_rows_prod_g k hT L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
        do 10 eexists. repeat split.
      + refine (conv_rows_prim_g k L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
        do 6 eexists. repeat split.
    - refine (conv_rows_stuck_g k hC hK L Q lo G pb _ _ w1 w2 rs s b rs' s' _ hm hr hv1 hv2 hw1 hw2 he).
      do 6 eexists. repeat split.
  Qed.

  (** ** The stuck-match rule: the whole rule

    [case_cong] compares the parameters ([case_params]), the return clauses under
    [#|pcontext|] fresh variables ([fresh_tail]), the scrutinees, and the branches
    ([case_branches]). [case_cq] is the conversion: two [tCase] readings whose components
    agree in the sense of [cqs], [cqb] and [cq] are convertible ([ws_cumul_pb_tCase]). *)

  Lemma pcodes_of_case G c ci p sc brs :
    gcok G c -> c.(c_term) = tCase ci p sc brs -> pcodes G c 0 p.(pparams).
  Proof.
    intros hc ht.
    assert (h : forall l i, (forall j t, nth_error l j = Some t ->
                  nth_error p.(pparams) (N.to_nat i + j) = Some t) -> pcodes G c i l).
    { induction l as [|t l ih]; intros i hl; constructor.
      - apply cok_child; [exact hc|rewrite ht]. apply cs_case_param.
        rewrite <- (Nat.add_0_r (N.to_nat i)). exact (hl 0 t eq_refl).
      - apply ih. intros j u hu. replace (N.to_nat (N.succ i)) with (S (N.to_nat i)) by lia.
        replace (S (N.to_nat i) + j) with (N.to_nat i + S j) by lia. exact (hl (S j) u hu). }
    apply h. intros j t hj. exact hj.
  Qed.

  Lemma bcodes_of_case G c ci p sc brs :
    gcok G c -> c.(c_term) = tCase ci p sc brs -> bcodes G c 0 brs.
  Proof.
    intros hc ht.
    assert (h : forall l i, (forall j br, nth_error l j = Some br ->
                  nth_error brs (N.to_nat i + j) = Some br) -> bcodes G c i l).
    { induction l as [|br l ih]; intros i hl; constructor.
      - apply cok_child; [exact hc|rewrite ht]. apply cs_case_branch.
        rewrite <- (Nat.add_0_r (N.to_nat i)). exact (hl 0 br eq_refl).
      - apply ih. intros j u hu. replace (N.to_nat (N.succ i)) with (S (N.to_nat i)) by lia.
        replace (S (N.to_nat i) + j) with (N.to_nat i + S j) by lia. exact (hl (S j) u hu). }
    apply h. intros j br hj. exact hj.
  Qed.

  Lemma susps_of_slots Q G e ts l :
    g_slots nctx Q G e.(ev_vals) ts -> e.(ev_nvals) = #|e.(ev_vals)| ->
    Forall2 (g_susp nctx Q G e) l
      (map (fun t => subst ts 0 (lift (Q - nctx + e.(ev_goff)) #|ts| t)) l).
  Proof.
    intros hs hn. pose proof (g_slots_length _ _ _ _ _ hs) as hl.
    induction l as [|t l ih]; constructor; [|exact ih].
    replace #|ts| with e.(ev_nvals) by lia. exact (g_susp_of_slots _ _ _ e t ts hs hn).
  Qed.

  Lemma lift_body0 d ts N t :
    subst (map (lift0 d) ts) 0 (lift (d + N) #|ts| t) = lift0 d (subst ts 0 (lift N #|ts| t)).
  Proof. exact (lift_bodyk d ts N #|ts| 0 t eq_refl). Qed.

  Lemma scl_binder_n L n B : on_free_vars (shiftnP n (shiftnP L xpred0)) B -> scl (L + n) B.
  Proof.
    intros h. unfold scl. rewrite (on_free_vars_ext _ _ _ (shiftnP_add _ _ _)) in h.
    rewrite Nat.add_comm. exact h.
  Qed.

  Lemma lift0_tCase_inv m ci p c brs u :
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

  Lemma open_scl (Ξ : context) L t : #|Ξ| = L -> is_open_term Ξ t -> scl L t.
  Proof. intros <- h. exact h. Qed.

  Lemma case_brs_cv L Q Δ (q1 : predicate term) ts1 ts2 N1 N2 brs1 brs2 bs1 bs2 :
    nctx <= L -> #|Δ| = L - nctx -> is_closed_context (Γ ,,, Δ) ->
    forallb (is_open_term (Γ ,,, Δ)) q1.(pparams) ->
    Forall2 (fun br1 br2 => case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cqb L Q #|br1.(bcontext)| Conv (rbody ts1 N1 br1) (rbody ts2 N2 br2)) brs1 brs2 ->
    Forall2 (fun br br' => br.(bcontext) = br'.(bcontext)
               /\ br.(bbody) = lift (Q - L) #|br'.(bcontext)| br'.(bbody))
      (map (rd_br ts1 N1) brs1) bs1 ->
    Forall2 (fun br br' => br.(bcontext) = br'.(bcontext)
               /\ br.(bbody) = lift (Q - L) #|br'.(bcontext)| br'.(bbody))
      (map (rd_br ts2 N2) brs2) bs2 ->
    Forall (fun br => on_free_vars_ctx (closedP #|q1.(pparams)| xpredT) br.(bcontext)
              /\ on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Γ ,,, Δ| xpred0)) br.(bbody))
      bs1 ->
    Forall (fun br => on_free_vars (shiftnP #|br.(bcontext)| (shiftnP #|Γ ,,, Δ| xpred0))
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
      cbn [rd_br bcontext bbody] in ec1, eb1, ec2, eb2.
      destruct (case_ctx_ok_spec _ _ hc) as [hx _ _]. pose proof (All2_length hx) as hk.
      unfold rbody in hq.
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
        exact (PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context xpred0 (Γ ,,, Δ) _ _ _
                 hop hfc1 hcl). }
      destruct (hq _ _ e1' e2' (scl_binder_n L _ _ hfb1) (scl_binder_n L _ _ hfb2) _ hlen hclo)
        as [hcv].
      rewrite app_context_assoc in hcv.
      constructor. constructor; [|exact hall]. split; [|exact hcv].
      rewrite <- ec1, <- ec2. exact hx.
  Qed.

  Lemma case_cq L Q pb ci p1 p2 sc1 sc2 brs1 brs2 ts1 ts2 N1 N2 :
    nctx <= L -> L <= Q ->
    forallb2 (cmp_level_conv X_type X) p1.(puinst) p2.(puinst) = true ->
    case_ctx_ok p1.(pcontext) p2.(pcontext) = true ->
    cqs L Q (map (fun t => subst ts1 0 (lift N1 #|ts1| t)) p1.(pparams))
            (map (fun t => subst ts2 0 (lift N2 #|ts2| t)) p2.(pparams)) ->
    cqb L Q #|p1.(pcontext)| Conv
      (subst ts1 #|p1.(pcontext)| (lift N1 (#|p1.(pcontext)| + #|ts1|) p1.(preturn)))
      (subst ts2 #|p1.(pcontext)| (lift N2 (#|p1.(pcontext)| + #|ts2|) p2.(preturn))) ->
    cq L Q Conv (subst ts1 0 (lift N1 #|ts1| sc1)) (subst ts2 0 (lift N2 #|ts2| sc2)) ->
    Forall2 (fun br1 br2 => case_ctx_ok br1.(bcontext) br2.(bcontext) = true
      /\ cqb L Q #|br1.(bcontext)| Conv (rbody ts1 N1 br1) (rbody ts2 N2 br2)) brs1 brs2 ->
    cq L Q pb (subst ts1 0 (lift N1 #|ts1| (tCase ci p1 sc1 brs1)))
              (subst ts2 0 (lift N2 #|ts2| (tCase ci p2 sc2 brs2))).
  Proof.
    intros hL hLQ Einst Ectx hpar hret hsc hbrs u1 u2 e1 e2 s1 s2 Δ hΔ hcl.
    rewrite rsusp_case in e1, e2.
    destruct (lift0_tCase_inv _ _ _ _ _ _ e1)
      as (q1 & d1 & bs1 & -> & ep1 & ei1 & ec1 & er1 & ed1 & eb1).
    destruct (lift0_tCase_inv _ _ _ _ _ _ e2)
      as (q2 & d2 & bs2 & -> & ep2 & ei2 & ec2 & er2 & ed2 & eb2).
    cbn [rd_pred pparams puinst pcontext preturn] in ep1, ei1, ec1, er1, ep2, ei2, ec2, er2.
    assert (hΞ : #|Γ ,,, Δ| = L) by (rewrite app_context_length, hΔ, <- hnctx; lia).
    pose proof (scl_open L Δ _ hL hΔ s1) as ho1. pose proof (scl_open L Δ _ hL hΔ s2) as ho2.
    destruct (open_case_inv _ _ _ _ _ ho1) as (hop1 & hor1 & hoc1 & hos1 & hob1).
    destruct (open_case_inv _ _ _ _ _ ho2) as (hop2 & hor2 & hoc2 & hos2 & hob2).
    destruct (case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
    pose proof (All2_length hctx) as hn12.
    (* parameters *)
    assert (sp1 : forallb (scl L) (pparams q1)) by (rewrite <- hΞ; exact hop1).
    assert (sp2 : forallb (scl L) (pparams q2)) by (rewrite <- hΞ; exact hop2).
    destruct (hpar _ _ ep1 ep2 sp1 sp2 Δ hΔ hcl) as [hpars].
    (* return clauses *)
    assert (er1' : subst ts1 #|pcontext p1| (lift N1 (#|pcontext p1| + #|ts1|) (preturn p1))
                   = lift (Q - L) #|pcontext p1| (preturn q1)) by (rewrite er1, <- ec1; reflexivity).
    assert (er2' : subst ts2 #|pcontext p1| (lift N2 (#|pcontext p1| + #|ts2|) (preturn p2))
                   = lift (Q - L) #|pcontext p1| (preturn q2))
      by (rewrite hn12, er2, <- ec2; reflexivity).
    rewrite hΞ, <- ec1 in hor1. rewrite hΞ, <- ec2, <- hn12 in hor2.
    assert (hlenR : #|Δ ,,, inst_case_predicate_context q1| = L + #|pcontext p1| - nctx).
    { rewrite app_context_length, inst_case_predicate_context_length, <- ec1. lia. }
    assert (hcloR : is_closed_context (Γ ,,, (Δ ,,, inst_case_predicate_context q1))).
    { rewrite app_context_assoc.
      exact (PCUICOnFreeVarsConv.on_free_vars_ctx_inst_case_context xpred0 (Γ ,,, Δ) _ _ _
               hop1 hoc1 hcl). }
    destruct (hret _ _ er1' er2' (scl_binder_n L _ _ hor1) (scl_binder_n L _ _ hor2) _
                hlenR hcloR) as [hR].
    rewrite app_context_assoc in hR.
    (* scrutinees *)
    destruct (hsc _ _ ed1 ed2 (open_scl _ _ _ hΞ hos1) (open_scl _ _ _ hΞ hos2) Δ hΔ hcl)
      as [hS].
    (* branches *)
    destruct (case_brs_cv L Q Δ q1 ts1 ts2 N1 N2 brs1 brs2 bs1 bs2 hL hΔ hcl hop1 hbrs eb1 eb2
                hob1 (cc_Forall_impl _ _ _ hob2 (fun br h => proj2 h))) as [hB].
    constructor.
    apply (ws_cumul_pb_tCase (wfΣ := wfΣ) ho1 ho2 hpars).
    - rewrite <- ei1, <- ei2. exact (cmp_level_conv_instance X_type X Σ hΣ _ _ Einst).
    - rewrite <- ec1, <- ec2. exact hctx.
    - exact hR.
    - exact hS.
    - exact hB.
  Qed.

  (** [push_fresh n] fresh variables on both environments, then the two codes at [L + n]. *)
  Definition fresh_tail (d : cbn_fuel) (n L : nat) (e1 e2 : cbn_env) (cb1 cb2 : code)
      (rs : list root) (s : cbn_state) :=
    match push_fresh n L e1 e2 (RE e1 :: RE e2 :: rs) s with
    | COk (r, rs, s) =>
      let '(lvlr, er1, er2) := r in
      conv_term X_type X Γ nctx d lvlr Conv er1 cb1 er2 cb2 rs s
    | CFail w => CFail w
    end.

  Lemma fresh_tail_g (k : unit -> cbn_fuel) (hT : spec_term (k tt))
      L Q lo G n e1 e2 cb1 cb2 ts1 ts2 rs s b rs' s' :
    MI L Q lo G s -> Forall (rwf Q) rs ->
    g_slots nctx Q G e1.(ev_vals) ts1 -> e1.(ev_nvals) = #|e1.(ev_vals)| ->
    g_slots nctx Q G e2.(ev_vals) ts2 -> e2.(ev_nvals) = #|e2.(ev_vals)| ->
    gcok G cb1 -> gcok G cb2 ->
    fresh_tail (k tt) n L e1 e2 cb1 cb2 rs s = COk (b, rs', s') ->
    post L Q G (RE e1 :: RE e2 :: rs) s' rs' /\
    (b = true -> cqb L Q n Conv
       (subst ts1 n (lift (Q - nctx + e1.(ev_goff)) (n + #|ts1|) cb1.(c_term)))
       (subst ts2 n (lift (Q - nctx + e2.(ev_goff)) (n + #|ts2|) cb2.(c_term)))).
  Proof.
    intros hm hr hs1 hn1 hs2 hn2 hc1 hc2 he.
    pose proof hm as [hL hLQ _ _].
    assert (hr0 : Forall (rwf Q) (RE e1 :: RE e2 :: rs))
      by (constructor; [exact I|constructor; [exact I|exact hr]]).
    pose proof (minv_raise L Q n lo G s hm) as hmR.
    pose proof (rwfs_mono Q (Q + n) _ ltac:(lia) hr0) as hrR.
    pose proof (grq_raise Q n G _ ltac:(lia) hr0) as hgR.
    pose proof (proj2 (g_slot_shift nctx Q n ltac:(lia) G) _ _ hs1) as [hs1R _].
    pose proof (proj2 (g_slot_shift nctx Q n ltac:(lia) G) _ _ hs2) as [hs2R _].
    unfold fresh_tail in he.
    destruct (push_fresh n L e1 e2 (RE e1 :: RE e2 :: rs) s)
      as [[[r rsP] sP]|w] eqn:EP; [|discriminate he].
    destruct (push_fresh_g n L (Q + n) lo (gshift n G) L e1 e2 _ _ _ s r rsP sP hmR hrR
                ltac:(lia) hs1R hn1 hs2R hn2 EP)
      as (loP & GP & f1 & f2 & -> & hmP & hrP & hgP & hnf1 & hgf1 & hnf2 & hgf2 & hf1 & hf2).
    pose proof (push_fresh_skel _ _ _ _ _ _ _ _ _ EP) as hkP.
    cbv beta iota in he.
    pose proof (g_susp_of_slots nctx _ GP f1 cb1.(c_term) _ hf1 hnf1) as hB1.
    pose proof (g_susp_of_slots nctx _ GP f2 cb2.(c_term) _ hf2 hnf2) as hB2.
    destruct (hT (L + n) (Q + n) loP GP Conv f1 cb1 f2 cb2 _ _ rsP sP b rs' s'
                (minv_level L (L + n) (Q + n) loP GP sP hmP ltac:(lia) ltac:(lia)) hrP hB1
                (cok_gcx _ _ (proj1 hgP) _ hc1) hB2 (cok_gcx _ _ (proj1 hgP) _ hc2) he)
      as [hpC hcC].
    split.
    - apply (post_compose L Q (Q + n) G (gshift n G) _ _ s' rs' ltac:(lia) hgR).
      apply (post_compose L _ _ _ GP _ rsP s' rs' (le_n _) (grq_of_gren _ _ _ _ _ hgP hkP)).
      exact (post_level L (L + n) (Q + n) GP rsP s' rs' hL ltac:(lia) hpC).
    - intros hb U1 U2 eU1 eU2 sU1 sU2.
      apply (hcC hb U1 U2); [| |exact sU1|exact sU2].
      + replace (Q + n - (L + n)) with (Q - L) by lia.
        rewrite hgf1, hnf1.
        pose proof (g_slots_length _ _ _ _ _ hf1) as hlf.
        rewrite length_app, length_map, idsn_length, length_map in hlf.
        rewrite <- hlf.
        replace (Q + n - nctx + ev_goff e1) with (n + (Q - nctx + ev_goff e1)) by lia.
        replace (Q + n - (L + n)) with (Q - L) by lia.
        apply fresh_branch_read; [lia|]. exact eU1.
      + replace (Q + n - (L + n)) with (Q - L) by lia.
        rewrite hgf2, hnf2.
        pose proof (g_slots_length _ _ _ _ _ hf2) as hlf.
        rewrite length_app, length_map, idsn_length, length_map in hlf.
        rewrite <- hlf.
        replace (Q + n - nctx + ev_goff e2) with (n + (Q - nctx + ev_goff e2)) by lia.
        replace (Q + n - (L + n)) with (Q - L) by lia.
        apply fresh_branch_read; [lia|]. exact eU2.
  Qed.

  Lemma case_cong_sound_g (k : unit -> cbn_fuel) :
    spec_term (k tt) -> spec_params (k tt) -> spec_branches (k tt) -> spec_case (FS k).
  Proof.
    intros hT hP hB L Q lo G pb e1 c1 e2 c2 t1 t2 rs s b rs' s' hm hr hs1 hc1 hs2 hc2 he.
    pose proof hm as [hL hLQ _ _].
    rewrite case_cong_eq in he.
    destruct (c_term c1) as [| | | | | | | | | | |ci1 p1 sc1 brs1| | | |] eqn:Ec1;
      try (cbv beta iota in he; injection he as <- <- <-;
           split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]).
    destruct (c_term c2) as [| | | | | | | | | | |ci2 p2 sc2 brs2| | | |] eqn:Ec2;
      try (cbv beta iota in he; injection he as <- <- <-;
           split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]).
    cbv beta iota in he.
    destruct (case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|) && (#|pparams p1| == #|pparams p2|)
              && forallb2 (cmp_level_conv X_type X) (puinst p1) (puinst p2)
              && case_ctx_ok (pcontext p1) (pcontext p2)) eqn:Etest;
      [|injection he as <- <- <-;
        split; [exact (post_refl _ _ _ _ _ _ hm hr)|intros hb; discriminate hb]].
    apply andb_true_iff in Etest as [Etest Ectx].
    apply andb_true_iff in Etest as [Etest Einst].
    apply andb_true_iff in Etest as [Etest _].
    apply andb_true_iff in Etest as [Eci _].
    apply case_info_eqb_eq in Eci. subst ci2.
    destruct (case_ctx_ok_spec _ _ Ectx) as [hctx _ _].
    pose proof (All2_length hctx) as hn12.
    destruct (g_susp_inv _ _ _ _ _ _ hs1) as (ts1 & hts1 & hn1 & ->).
    destruct (g_susp_inv _ _ _ _ _ _ hs2) as (ts2 & hts2 & hn2 & ->).
    pose proof (g_slots_length _ _ _ _ _ hts1) as hl1.
    pose proof (g_slots_length _ _ _ _ _ hts2) as hl2.
    assert (hk1 : ev_nvals e1 = #|ts1|) by lia.
    assert (hk2 : ev_nvals e2 = #|ts2|) by lia.
    rewrite hk1, hk2.
    (* the parameters *)
    assert (hr0 : Forall (rwf Q) (RE e1 :: RE e2 :: rs))
      by (constructor; [exact I|constructor; [exact I|exact hr]]).
    destruct (case_params X_type X Γ nctx (k tt) L e1 c1 e2 c2 0%N
                (pparams p1) (pparams p2) (RE e1 :: RE e2 :: rs) s)
      as [[[bA rsA] sA]|w] eqn:EA; [|discriminate he].
    destruct (hP L Q lo G e1 c1 e2 c2 0%N (pparams p1) (pparams p2) _ _ _ s bA rsA sA hm hr0
                (pcodes_of_case G c1 ci1 p1 sc1 brs1 hc1 Ec1)
                (pcodes_of_case G c2 ci1 p2 sc2 brs2 hc2 Ec2)
                (susps_of_slots Q G e1 ts1 _ hts1 hn1) (susps_of_slots Q G e2 ts2 _ hts2 hn2) EA)
      as [hpA hcA].
    destruct bA;
      [|cbv beta iota in he; injection he as <- <- <-;
        split; [exact (post_drop2 _ _ _ _ _ _ _ _ hpA)|intros hb; discriminate hb]].
    destruct hpA as (QA & loA & GA & hqA & hmA & hrA & hgA).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgA) as (qa1 & rsA1 & -> & hqa1 & hgA1).
    destruct (gpq_RE_inv _ _ _ _ _ _ hqa1) as (f1 & -> & hnf1 & hgf1 & hkf1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgA1) as (qa2 & rsB & -> & hqa2 & hgB).
    destruct (gpq_RE_inv _ _ _ _ _ _ hqa2) as (f2 & -> & hnf2 & hgf2 & hkf2).
    cbv beta iota in he.
    pose proof (hkf1 _ hts1) as hfs1. pose proof (hkf2 _ hts2) as hfs2.
    pose proof (g_slots_length _ _ _ _ _ hfs1) as hlf1. rewrite length_map in hlf1.
    pose proof (g_slots_length _ _ _ _ _ hfs2) as hlf2. rewrite length_map in hlf2.
    (* the return clauses *)
    destruct (push_fresh #|pcontext p1| L f1 f2 (RE f1 :: RE f2 :: rsB) sA)
      as [[[[[lvlr er1] er2] rsP] sP]|w] eqn:EP; [|discriminate he].
    cbv beta iota in he.
    destruct (conv_term X_type X Γ nctx (k tt) lvlr Conv er1 (child c1 1 (preturn p1))
                er2 (child c2 1 (preturn p2)) rsP sP) as [[[bC rsC] sC]|w] eqn:EC;
      [|discriminate he].
    assert (EF : fresh_tail (k tt) #|pcontext p1| L f1 f2 (child c1 1 (preturn p1))
                   (child c2 1 (preturn p2)) rsB sA = COk (bC, rsC, sC))
      by (unfold fresh_tail; rewrite EP; exact EC).
    destruct (fresh_tail_g k hT L QA loA GA #|pcontext p1| f1 f2 _ _ _ _ rsB sA bC rsC sC hmA
                (Forall_inv_tail (Forall_inv_tail hrA)) hfs1 ltac:(lia) hfs2 ltac:(lia)
                (cok_gcx _ _ (proj1 hgA) _
                   (cok_child G c1 1 (preturn p1) hc1 ltac:(rewrite Ec1; constructor)))
                (cok_gcx _ _ (proj1 hgA) _
                   (cok_child G c2 1 (preturn p2) hc2 ltac:(rewrite Ec2; constructor)))
                EF) as [hpC hcC].
    destruct bC;
      [|cbv beta iota in he; injection he as <- <- <-; split; [|intros hb; discriminate hb];
        apply (post_compose L Q QA G GA rs rsB _ _ hqA hgB);
        exact (post_drop2 _ _ _ _ _ _ _ _ hpC)].
    destruct hpC as (QB & loB & GB & hqB & hmB & hrB & hgBB).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgBB) as (qb1 & rsC1 & -> & hqb1 & hgB1).
    destruct (gpq_RE_inv _ _ _ _ _ _ hqb1) as (g1 & -> & hng1 & hgg1 & hkg1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgB1) as (qb2 & rsC' & -> & hqb2 & hgC).
    destruct (gpq_RE_inv _ _ _ _ _ _ hqb2) as (g2 & -> & hng2 & hgg2 & hkg2).
    cbv beta iota in he.
    pose proof (hkg1 _ hfs1) as hgs1. pose proof (hkg2 _ hfs2) as hgs2.
    rewrite map_lift0_lift0 in hgs1, hgs2.
    replace (QB - QA + (QA - Q)) with (QB - Q) in hgs1, hgs2 by lia.
    pose proof (g_slots_length _ _ _ _ _ hgs1) as hlg1. rewrite length_map in hlg1.
    pose proof (g_slots_length _ _ _ _ _ hgs2) as hlg2. rewrite length_map in hlg2.
    assert (hgcx : gcx G GB) by (intros i x h; exact (proj1 hgBB _ _ (proj1 hgA _ _ h))).
    (* the scrutinees *)
    destruct (conv_term X_type X Γ nctx (k tt) L Conv g1 (child c1 0 sc1)
                g2 (child c2 0 sc2) (RE g1 :: RE g2 :: rsC') sC)
      as [[[bD rsD] sD]|w] eqn:ED; [|discriminate he].
    assert (hng1' : ev_nvals g1 = #|ev_vals g1|) by lia.
    assert (hng2' : ev_nvals g2 = #|ev_vals g2|) by lia.
    destruct (hT L QB loB GB Conv g1 (child c1 0 sc1) g2 (child c2 0 sc2) _ _ _ sC bD rsD sD
                hmB hrB (g_susp_of_slots _ _ _ g1 _ _ hgs1 hng1')
                (cok_gcx _ _ hgcx _ (cok_child G c1 0 sc1 hc1 ltac:(rewrite Ec1; constructor)))
                (g_susp_of_slots _ _ _ g2 _ _ hgs2 hng2')
                (cok_gcx _ _ hgcx _ (cok_child G c2 0 sc2 hc2 ltac:(rewrite Ec2; constructor)))
                ED) as [hpD hcD].
    destruct bD;
      [|cbv beta iota in he; injection he as <- <- <-; split; [|intros hb; discriminate hb];
        apply (post_compose L Q QA G GA rs rsB _ _ hqA hgB);
        apply (post_compose L QA QB GA GB rsB rsC' _ _ hqB hgC);
        exact (post_drop2 _ _ _ _ _ _ _ _ hpD)].
    destruct hpD as (QD & loD & GD & hqD & hmD & hrD & hgDD).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgDD) as (qd1 & rsD1 & -> & hqd1 & hgD1).
    destruct (gpq_RE_inv _ _ _ _ _ _ hqd1) as (h1 & -> & hnh1 & hgh1 & hkh1).
    destruct (grq_cons_inv _ _ _ _ _ _ _ hgD1) as (qd2 & rsD' & -> & hqd2 & hgD).
    destruct (gpq_RE_inv _ _ _ _ _ _ hqd2) as (h2 & -> & hnh2 & hgh2 & hkh2).
    cbv beta iota in he.
    pose proof (hkh1 _ hgs1) as hhs1. pose proof (hkh2 _ hgs2) as hhs2.
    rewrite map_lift0_lift0 in hhs1, hhs2.
    replace (QD - QB + (QB - Q)) with (QD - Q) in hhs1, hhs2 by lia.
    pose proof (g_slots_length _ _ _ _ _ hhs1) as hlh1. rewrite length_map in hlh1.
    pose proof (g_slots_length _ _ _ _ _ hhs2) as hlh2. rewrite length_map in hlh2.
    assert (hgcx' : gcx G GD) by (intros i x h; exact (proj1 hgDD _ _ (hgcx _ _ h))).
    (* the branches *)
    destruct (hB L QD loD GD h1 c1 h2 c2 0%N brs1 brs2 _ _ rsD' sD b rs' s' hmD
                (Forall_inv_tail (Forall_inv_tail hrD))
                (bcodes_of_case GD c1 ci1 p1 sc1 brs1 (cok_gcx _ _ hgcx' _ hc1) Ec1)
                (bcodes_of_case GD c2 ci1 p2 sc2 brs2 (cok_gcx _ _ hgcx' _ hc2) Ec2)
                hhs1 ltac:(lia) hhs2 ltac:(lia) he) as [hpE hcE].
    split.
    - apply (post_compose L Q QA G GA rs rsB _ _ hqA hgB).
      apply (post_compose L QA QB GA GB rsB rsC' _ _ hqB hgC).
      exact (post_compose L QB QD GB GD rsC' rsD' _ _ hqD hgD hpE).
    - intros hb.
      apply (case_cq L Q pb ci1 p1 p2 sc1 sc2 brs1 brs2 ts1 ts2
               (Q - nctx + ev_goff e1) (Q - nctx + ev_goff e2) hL hLQ Einst Ectx).
      + exact (hcA eq_refl).
      + pose proof (hcC eq_refl) as hR. cbn [child c_term] in hR.
        rewrite hgf1, hgf2, !length_map in hR.
        replace (QA - nctx + ev_goff e1) with ((QA - Q) + (Q - nctx + ev_goff e1)) in hR by lia.
        replace (QA - nctx + ev_goff e2) with ((QA - Q) + (Q - nctx + ev_goff e2)) in hR by lia.
        rewrite !lift_bodyk in hR by reflexivity.
        exact (cqb_lift L Q QA _ Conv _ _ hLQ hqA hR).
      + pose proof (hcD eq_refl) as hS. cbn [child c_term] in hS.
        rewrite hgg1, hgf1, hgg2, hgf2, hng1, hnf1, hng2, hnf2, hk1, hk2 in hS.
        replace (QB - nctx + ev_goff e1) with ((QB - Q) + (Q - nctx + ev_goff e1)) in hS by lia.
        replace (QB - nctx + ev_goff e2) with ((QB - Q) + (Q - nctx + ev_goff e2)) in hS by lia.
        rewrite !lift_body0 in hS.
        exact (cq_lift L Q QB Conv _ _ hLQ ltac:(lia) hS).
      + pose proof (hcE hb) as hc.
        rewrite hgh1, hgg1, hgf1, hgh2, hgg2, hgf2 in hc.
        replace (QD - nctx + ev_goff e1) with ((QD - Q) + (Q - nctx + ev_goff e1)) in hc by lia.
        replace (QD - nctx + ev_goff e2) with ((QD - Q) + (Q - nctx + ev_goff e2)) in hc by lia.
        exact (branches_lift L Q QD ts1 ts2 _ _ brs1 brs2 hLQ ltac:(lia) hc).
  Qed.

  (** ** The induction *)

  Lemma spec_all_step (k : unit -> cbn_fuel) : spec_all (k tt) -> spec_all (FS k).
  Proof.
    intros (hS & hE & hC & hT & hM & hSC & hK & hP & hB & hR & hV).
    split; [exact (conv_slot_sound_g k hE hM)|].
    split; [exact (conv_eval_sound_g k hV)|].
    split; [exact (conv_cells_sound_g k hS hC)|].
    split; [exact (conv_term_sound_g k hV)|].
    split; [exact (conv_same_code_sound_g k hSC)|].
    split; [exact (same_code_cells_sound_g k hS hSC)|].
    split; [exact (case_cong_sound_g k hT hP hB)|].
    split; [exact (case_params_sound_g k hT hP)|].
    split; [exact (case_branches_sound_g k hT hB)|].
    split; [exact (conv_rows_sound_g k hC hT hK)|].
    exact (conv_value_sound_g k hM hC hR).
  Qed.

  Lemma spec_all_ind : forall d, spec_all d.
  Proof. induction d as [|k ih]; [exact spec_all_FO|exact (spec_all_step k (ih tt))]. Qed.

End ConvGhost.

(** * The comparison is sound at every fuel

  [spec_all_holds] closes [ConvGhost] with its parameters in their declaration order. Its
  hypotheses are the section's: [wf Σ] and [abstract_env_ext_rel X Σ], the context facts
  [hnctx], [hΓ], [hhyg] and [hcio] ([PCUICCallByNeedSoundHookFrame.eval_section_instance]
  gives them for any well-formed context, and [w_section] and [v_section] below at concrete
  ones), and [hrb], the read-back interface [rb_sound] that
  [PCUICCallByNeedSoundReadBack.rb_sound_holds] proves from [wf Σ], [hΓ] and [hhyg]. *)
Theorem spec_all_holds {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (Γ : context) (nctx : nat) (Σ : global_env_ext)
    (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ)
    (hnctx : nctx = #|Γ|) (hΓ : is_closed_context Γ) (hhyg : ctx_hyg Γ)
    (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
              PCUICCallByNeedSoundHook.consts_okb Σ b)
    (hrb : rb_sound X_type X Γ nctx Σ) :
  forall d, spec_all X_type X Γ nctx Σ d.
Proof. intros d. eapply spec_all_ind; eassumption. Qed.

(** * Non-vacuity witnesses for the statements of [ConvGhost]

  Two concrete runs of [conv_term] at the real fuel [cbn_depth], from the state [cbn_run]
  starts in. Each theorem shows that the premises of [spec_term] hold at the run's inputs (the
  start state satisfies [minv], the inputs have readings, their codes are in the ghost's
  table), that the call returns, and that the conclusion holds: the state part [post] by the
  machine lemma [whnf_master] and, for the run that answers [true], the conversion part
  [cq] by hand, not by the fuel induction. The answers and final states are obtained by
  computation. The only hypotheses are [wf Σ] and [abstract_env_ext_rel X Σ]: the start
  invariant is [run_s2_gok] of [PCUICCallByNeedSoundLevel], the context hypotheses of
  [ConvGhost] hold at both contexts ([w_section], [v_section]), and [hrb] follows from them
  by [PCUICCallByNeedSoundReadBack.rb_sound_holds].
  - [witness_seam_run]: [x := (fun n : nat => n) O] against [fun n : nat => n], the run
    [PCUICCallByNeedCounterexamples.term_seam_false] uses. It answers [false], and [post]
    holds after it.
  - [witness_true_run]: [x := (fun n : y => n) y] against [y], at [Conv]. It answers [true]
    and [cq] holds. *)

(** [at_depth F dflt] runs [F] at the fuel one unit below [cbn_depth]. Stating the machine
  calls of a run this way lets [vm_compute] evaluate them at the real fuel with no equation
  between fuels to prove. *)
Definition at_depth {A : Type} (F : cbn_fuel -> A) (dflt : A) : A :=
  match cbn_depth with FS k => F (k tt) | FO => dflt end.

(** The concrete contexts and terms. *)
Definition w_na : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition w_nat : inductive :=
  {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}.
Definition w_O : term := tConstruct w_nat 0 [].
Definition w_body : term := tApp (tLambda w_na (tInd w_nat []) (tRel 0)) w_O.
Definition w_Γ : context := [vdef w_na w_body (tInd w_nat [])].
Definition w_t : term := tRel 0.
Definition w_u : term := tLambda w_na (tInd w_nat []) (tRel 0).

Definition v_Γ : context :=
  [vdef w_na (tApp (tLambda w_na (tRel 0) (tRel 0)) (tRel 0)) (tRel 0); vass w_na (tSort sProp)].
Definition v_t : term := tRel 0.
Definition v_u : term := tRel 1.

Section Witness.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Σ : global_env_ext) (wfΣ : wf Σ) (hΣ : abstract_env_ext_rel X Σ).

  (** [tick] keeps [minv]. *)
  Lemma r_minv_tick (Γ : context) (nctx L Q : nat) (lo : positive) (G : ghost)
      (s s' : cbn_state) :
    minv X_type X Γ nctx Σ L Q lo G s -> tick s = Some s' ->
    minv X_type X Γ nctx Σ L Q lo G s'.
  Proof.
    intros [hL hQ hok hw] e. destruct (tick_shape s s' e) as (th & tn & _ & tg & tm).
    constructor; [exact hL|exact hQ| |exact (hwf_heap Q s s' th hw)].
    apply (gok_same X_type X Γ nctx Σ _ Q lo G s s' hok th tn tg).
    exact (mok_memo X_type X Γ Σ _ s s' tm (@gk_memo _ X_type X Γ nctx Σ _ _ _ _ _ hok)).
  Qed.

  (** The start state of a run satisfies [minv] at [L = Q = nctx]. *)
  Lemma r_minv_start (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|) :
    consts_okb Σ t -> consts_okb Σ u -> on_free_vars xpredT t -> on_free_vars xpredT u ->
    minv X_type X Γ nctx Σ nctx nctx xH (run_ghost X_type X t u) (run_s2 X_type X t u).
  Proof.
    intros ht hu hht hhu.
    apply (minv_start X_type X Γ nctx Σ hnctx xH (run_ghost X_type X t u) _
             (run_s2_gok X_type X Γ nctx Σ [] nctx t u ht hu hht hhu)).
    intros a cl h. unfold heap_get in h. rewrite run_s2_heap, bh_get_holes in h.
    discriminate h.
  Qed.

  (** A run of [conv_term] at [cbn_depth] from [cbn_run]'s start state, split at its three
    machine calls. *)
  Lemma r_split (Γ : context) (nctx : nat) (t u : term) (v1 v2 : cbn_value)
      (s1 s2 s3 : cbn_state) (b : bool) :
    at_depth (fun d => whnf X_type X Γ nctx d env_empty (run_c1 X_type X t) []
                         [RE env_empty] (run_s2 X_type X t u)) (CFail WDepth)
      = COk (v1, [RE env_empty], s1) ->
    at_depth (fun d => whnf X_type X Γ nctx d env_empty (run_c2 X_type X t u) []
                         [RV v1] s1) (CFail WDepth)
      = COk (v2, [RV v1], s2) ->
    at_depth (fun d => conv_value X_type X Γ nctx d nctx Conv v1 v2 [] s2) (CFail WDepth)
      = COk (b, [], s3) ->
    conv_term X_type X Γ nctx cbn_depth nctx Conv env_empty (run_c1 X_type X t)
      env_empty (run_c2 X_type X t u) [] (run_s2 X_type X t u) = COk (b, [], s3)
    /\ exists d,
         whnf X_type X Γ nctx d env_empty (run_c1 X_type X t) [] [RE env_empty]
           (run_s2 X_type X t u) = COk (v1, [RE env_empty], s1)
         /\ whnf X_type X Γ nctx d env_empty (run_c2 X_type X t u) [] [RV v1] s1
              = COk (v2, [RV v1], s2).
  Proof.
    unfold at_depth. destruct cbn_depth as [|k]; intros E1 E2 E3; [discriminate E1|].
    cbv beta in E1, E2, E3.
    split; [|exists (k tt); split; assumption].
    rewrite conv_term_eq, E1. cbv beta iota. rewrite E2. cbv beta iota. exact E3.
  Qed.

  (** The state part: [post] holds after the two [whnf] calls and the [tick] of
    [conv_value], by [whnf_master]. *)
  Lemma r_post (Γ : context) (nctx : nat) (t u : term) (hnctx : nctx = #|Γ|)
      (hcio : forall j decl b, nth_error Γ j = Some decl -> decl.(decl_body) = Some b ->
                PCUICCallByNeedSoundHook.consts_okb Σ b)
      (d : cbn_fuel) (v1 v2 : cbn_value) (s1 s2 s3 : cbn_state) :
    minv X_type X Γ nctx Σ nctx nctx xH (run_ghost X_type X t u) (run_s2 X_type X t u) ->
    whnf X_type X Γ nctx d env_empty (run_c1 X_type X t) [] [RE env_empty]
      (run_s2 X_type X t u) = COk (v1, [RE env_empty], s1) ->
    whnf X_type X Γ nctx d env_empty (run_c2 X_type X t u) [] [RV v1] s1
      = COk (v2, [RV v1], s2) ->
    tick s2 = Some s3 ->
    post X_type X Γ nctx Σ nctx nctx (run_ghost X_type X t u) [] s3 [].
  Proof.
    intros hm0 E1 E2 E3.
    destruct (whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio d nctx nctx xH
                (run_ghost X_type X t u) env_empty (run_c1 X_type X t) [] [] t [RE env_empty]
                (run_s2 X_type X t u) v1 [RE env_empty] s1 hm0
                (Forall_cons (RE env_empty) I (Forall_nil _)) (run_c1_g_susp X_type X nctx t u)
                (run_c1_gcok X_type X t u) (g_slots_nil nctx nctx _) E1)
      as (lo1 & G1 & w1 & hm1 & hr1 & hv1 & hg1 & _ & _).
    assert (hs2 : g_susp nctx nctx G1 env_empty (run_c2 X_type X t u).(c_term) u).
    { rewrite run_c2_term. apply g_susp_env_empty. }
    destruct (whnf_master X_type X Γ nctx Σ wfΣ hΣ hnctx hcio d nctx nctx lo1 G1
                env_empty (run_c2 X_type X t u) [] [] u [RV v1] s1 v2 [RV v1] s2 hm1
                (Forall_cons (RV v1) hv1 (Forall_inv_tail hr1)) hs2
                (cok_gcx _ _ (proj1 hg1) _ (run_c2_gcok X_type X t u))
                (g_slots_nil nctx nctx _) E2)
      as (lo2 & G2 & w2 & hm2 & hr2 & hv2 & hg2 & _ & _).
    exists nctx, lo2, G2. split; [lia|]. split; [exact (r_minv_tick _ _ _ _ _ _ _ _ hm2 E3)|].
    split; [constructor|]. split; [|split; [constructor|reflexivity]].
    intros i e hi. exact (proj1 hg2 _ _ (proj1 hg1 _ _ hi)).
  Qed.

  (** ** A run that answers [false], and [post] holds after it *)

  Definition w_G0 : ghost := run_ghost X_type X w_t w_u.

  (** The section hypotheses of [ConvGhost] at [w_Γ]. *)
  Lemma w_section :
    1 = #|w_Γ| /\ is_closed_context w_Γ /\ ctx_hyg w_Γ
    /\ (forall j decl b, nth_error w_Γ j = Some decl -> decl.(decl_body) = Some b ->
          PCUICCallByNeedSoundHook.consts_okb Σ b).
  Proof.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros [|j] decl b hj hb; [|destruct j; discriminate hj].
      injection hj as <-. injection hb as <-. reflexivity.
    - intros [|j] decl b hj hb; [|destruct j; discriminate hj].
      injection hj as <-. injection hb as <-. reflexivity.
  Qed.

  Definition w_R1 :=
    at_depth (fun d => whnf X_type X w_Γ 1 d env_empty (run_c1 X_type X w_t) []
                         [RE env_empty] (run_s2 X_type X w_t w_u)) (CFail WDepth).
  Definition w_s1 : cbn_state := match w_R1 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition w_R2 :=
    at_depth (fun d => whnf X_type X w_Γ 1 d env_empty (run_c2 X_type X w_t w_u) []
                         [RV (VCon w_O [])] w_s1) (CFail WDepth).
  Definition w_v2 : cbn_value := match w_R2 with COk (v, _, _) => v | CFail _ => VCon w_O [] end.
  Definition w_s2 : cbn_state := match w_R2 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition w_s3 : cbn_state := match tick w_s2 with Some s => s | None => cbn_init end.

  Lemma w_E1 :
    at_depth (fun d => whnf X_type X w_Γ 1 d env_empty (run_c1 X_type X w_t) []
                         [RE env_empty] (run_s2 X_type X w_t w_u)) (CFail WDepth)
    = COk (VCon w_O [], [RE env_empty], w_s1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_E2 :
    at_depth (fun d => whnf X_type X w_Γ 1 d env_empty (run_c2 X_type X w_t w_u) []
                         [RV (VCon w_O [])] w_s1) (CFail WDepth)
    = COk (w_v2, [RV (VCon w_O [])], w_s2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_E3 :
    at_depth (fun d => conv_value X_type X w_Γ 1 d 1 Conv (VCon w_O []) w_v2 [] w_s2)
      (CFail WDepth) = COk (false, [], w_s3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma w_tick : tick w_s2 = Some w_s3.
  Proof. vm_compute. reflexivity. Qed.

  (** Satisfying instance of the premises of [spec_term] at [cbn_depth], with its
    conclusion: a run that answers [false]. *)
  Theorem witness_seam_run :
    minv X_type X w_Γ 1 Σ 1 1 xH w_G0 (run_s2 X_type X w_t w_u)
    /\ g_susp 1 1 w_G0 env_empty (run_c1 X_type X w_t).(c_term) w_t
    /\ PCUICCallByNeedSoundEval.cok w_G0 (run_c1 X_type X w_t)
    /\ g_susp 1 1 w_G0 env_empty (run_c2 X_type X w_t w_u).(c_term) w_u
    /\ PCUICCallByNeedSoundEval.cok w_G0 (run_c2 X_type X w_t w_u)
    /\ exists s',
         conv_term X_type X w_Γ 1 cbn_depth 1 Conv env_empty (run_c1 X_type X w_t)
           env_empty (run_c2 X_type X w_t w_u) [] (run_s2 X_type X w_t w_u) = COk (false, [], s')
         /\ post X_type X w_Γ 1 Σ 1 1 w_G0 [] s' [].
  Proof.
    assert (hm0 : minv X_type X w_Γ 1 Σ 1 1 xH w_G0 (run_s2 X_type X w_t w_u))
      by exact (r_minv_start w_Γ 1 w_t w_u eq_refl eq_refl eq_refl eq_refl eq_refl).
    split; [exact hm0|].
    split; [exact (run_c1_g_susp X_type X 1 w_t w_u)|].
    split; [exact (run_c1_gcok X_type X w_t w_u)|].
    split; [exact (run_c2_g_susp X_type X 1 w_t w_u)|].
    split; [exact (run_c2_gcok X_type X w_t w_u)|].
    destruct (r_split w_Γ 1 w_t w_u (VCon w_O []) w_v2 w_s1 w_s2 w_s3 false
                w_E1 w_E2 w_E3) as [hrun (d & hd1 & hd2)].
    exists w_s3. split; [exact hrun|].
    destruct w_section as (_ & _ & _ & hcio).
    exact (r_post w_Γ 1 w_t w_u eq_refl hcio d _ _ _ _ _ hm0 hd1 hd2 w_tick).
  Qed.

  (** ** A run that answers [true], with its conversion claim *)

  Definition v_G0 : ghost := run_ghost X_type X v_t v_u.

  (** The section hypotheses of [ConvGhost] at [v_Γ]. *)
  Lemma v_section :
    2 = #|v_Γ| /\ is_closed_context v_Γ /\ ctx_hyg v_Γ
    /\ (forall j decl b, nth_error v_Γ j = Some decl -> decl.(decl_body) = Some b ->
          PCUICCallByNeedSoundHook.consts_okb Σ b).
  Proof.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - intros [|[|j]] decl b hj hb; [| |destruct j; discriminate hj].
      + injection hj as <-. injection hb as <-. reflexivity.
      + injection hj as <-. discriminate hb.
    - intros [|[|j]] decl b hj hb; [| |destruct j; discriminate hj].
      + injection hj as <-. injection hb as <-. reflexivity.
      + injection hj as <-. discriminate hb.
  Qed.

  Definition v_R1 :=
    at_depth (fun d => whnf X_type X v_Γ 2 d env_empty (run_c1 X_type X v_t) []
                         [RE env_empty] (run_s2 X_type X v_t v_u)) (CFail WDepth).
  Definition v_v1 : cbn_value := match v_R1 with COk (v, _, _) => v | CFail _ => VCon w_O [] end.
  Definition v_s1 : cbn_state := match v_R1 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition v_R2 :=
    at_depth (fun d => whnf X_type X v_Γ 2 d env_empty (run_c2 X_type X v_t v_u) []
                         [RV v_v1] v_s1) (CFail WDepth).
  Definition v_v2 : cbn_value := match v_R2 with COk (v, _, _) => v | CFail _ => VCon w_O [] end.
  Definition v_s2 : cbn_state := match v_R2 with COk (_, _, s) => s | CFail _ => cbn_init end.
  Definition v_s3 : cbn_state := match tick v_s2 with Some s => s | None => cbn_init end.

  Lemma v_E1 :
    at_depth (fun d => whnf X_type X v_Γ 2 d env_empty (run_c1 X_type X v_t) []
                         [RE env_empty] (run_s2 X_type X v_t v_u)) (CFail WDepth)
    = COk (v_v1, [RE env_empty], v_s1).
  Proof. vm_compute. reflexivity. Qed.

  Lemma v_E2 :
    at_depth (fun d => whnf X_type X v_Γ 2 d env_empty (run_c2 X_type X v_t v_u) []
                         [RV v_v1] v_s1) (CFail WDepth)
    = COk (v_v2, [RV v_v1], v_s2).
  Proof. vm_compute. reflexivity. Qed.

  Lemma v_E3 :
    at_depth (fun d => conv_value X_type X v_Γ 2 d 2 Conv v_v1 v_v2 [] v_s2)
      (CFail WDepth) = COk (true, [], v_s3).
  Proof. vm_compute. reflexivity. Qed.

  Lemma v_tick : tick v_s2 = Some v_s3.
  Proof. vm_compute. reflexivity. Qed.

  (** The claim, by hand: [x] unfolds to [(fun n : y => n) y], which beta-reduces to [y]. *)
  Lemma v_red : PCUICReduction.red Σ v_Γ v_t v_u.
  Proof.
    eapply PCUICReduction.red_trans.
    - apply PCUICReduction.red1_red.
      exact (PCUICReduction.red_rel Σ v_Γ 0 (tApp (tLambda w_na (tRel 0) (tRel 0)) (tRel 0)) eq_refl).
    - apply PCUICReduction.red1_red. exact (PCUICReduction.red_beta Σ v_Γ w_na (tRel 1) (tRel 0) (tRel 1)).
  Qed.

  Lemma v_cq : cq v_Γ 2 Σ 2 2 Conv v_t v_u.
  Proof.
    intros u1 u2 e1 e2 _ _. rewrite Nat.sub_diag, lift0_id in e1, e2. subst u1 u2.
    intros Δ hΔ hcl. destruct Δ as [|? Δ]; [|discriminate hΔ].
    constructor. apply (red_ws_cumul_pb (wfΣ := wfΣ)).
    apply into_closed_red; [exact v_red|exact hcl|reflexivity].
  Qed.

  (** Satisfying instance of the premises of [spec_term] at [cbn_depth], with its
    conclusion: a run that answers [true]. *)
  Theorem witness_true_run :
    minv X_type X v_Γ 2 Σ 2 2 xH v_G0 (run_s2 X_type X v_t v_u)
    /\ g_susp 2 2 v_G0 env_empty (run_c1 X_type X v_t).(c_term) v_t
    /\ PCUICCallByNeedSoundEval.cok v_G0 (run_c1 X_type X v_t)
    /\ g_susp 2 2 v_G0 env_empty (run_c2 X_type X v_t v_u).(c_term) v_u
    /\ PCUICCallByNeedSoundEval.cok v_G0 (run_c2 X_type X v_t v_u)
    /\ exists s',
         conv_term X_type X v_Γ 2 cbn_depth 2 Conv env_empty (run_c1 X_type X v_t)
           env_empty (run_c2 X_type X v_t v_u) [] (run_s2 X_type X v_t v_u) = COk (true, [], s')
         /\ post X_type X v_Γ 2 Σ 2 2 v_G0 [] s' []
         /\ cq v_Γ 2 Σ 2 2 Conv v_t v_u.
  Proof.
    assert (hm0 : minv X_type X v_Γ 2 Σ 2 2 xH v_G0 (run_s2 X_type X v_t v_u))
      by exact (r_minv_start v_Γ 2 v_t v_u eq_refl eq_refl eq_refl eq_refl eq_refl).
    split; [exact hm0|].
    split; [exact (run_c1_g_susp X_type X 2 v_t v_u)|].
    split; [exact (run_c1_gcok X_type X v_t v_u)|].
    split; [exact (run_c2_g_susp X_type X 2 v_t v_u)|].
    split; [exact (run_c2_gcok X_type X v_t v_u)|].
    destruct (r_split v_Γ 2 v_t v_u v_v1 v_v2 v_s1 v_s2 v_s3 true
                v_E1 v_E2 v_E3) as [hrun (d & hd1 & hd2)].
    exists v_s3. split; [exact hrun|].
    destruct v_section as (_ & _ & _ & hcio).
    split; [exact (r_post v_Γ 2 v_t v_u eq_refl hcio d _ _ _ _ _ hm0 hd1 hd2 v_tick)|].
    exact v_cq.
  Qed.
End Witness.
