(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Nnat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICReduction
  PCUICTyping PCUICUnivSubst PCUICClosed PCUICClosedTyp PCUICInduction PCUICSigmaCalculus
  PCUICContexts PCUICOnFreeVars PCUICPrimitiveRed.
From MetaRocq.PCUIC Require PCUICInductiveInversion.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook.

Import CanonicalTries.

Local Notation cbn_xpredT := (fun _ : nat => true) (only parsing).

(** * The evaluator of the call-by-need machine against PCUIC reduction

  [cbn_whnf], [cbn_whnf_fix], [cbn_eval_slot], [cbn_force] and [cbn_apply] turn a suspension into a
  weak-head value. This file proves that the term the input stands for reduces, in PCUIC, to the
  term the value stands for, for every rule the machine has: beta, zeta, rel (including the
  forcing of a cell and its write-back), delta, primitive operations ([red_prim_op], once the
  arguments read as literals), iota, fixpoint unfolding, projection, and
  the stuck forms of a match, a projection and a fixpoint whose scrutinee or recursive
  argument is neutral or stuck. The machine has no rule for a cofixpoint, a [tVar] or a
  [tEvar]: on those [cbn_whnf] gives up ([CbnCFail CbnWShape]), so there is nothing to prove.

  ** What a structure stands for

  The read-back used here is a ghost read-back [cbn_g_value], which reads an address [a] as the
  term [G a] of a ghost map [G : cbn_haddr -> option term] instead of following the heap. A
  read-back that follows the heap and this one differ exactly on a cell the machine has
  already forced: the first reads such a cell as the value now in it, the ghost map keeps
  the term the cell was allocated for.

  The ghost map is what makes the write-back compositional. With a read-back that follows
  the heap, forcing an address changes what *every* other structure that names it stands
  for: the reading of a cell is a term built out of the readings of the addresses below it,
  so a write-back turns a third party's reading [u] into some reduct [u']. To put a value
  [v] back into a forced cell one then has to know that [v] is a reduct of the cell's
  reading *as it is when the forcing ends*, not of its reading when the forcing started,
  and the two are only joinable, not ordered: that is a confluence argument, not an
  induction. With the ghost map, [G] only ever grows at fresh addresses ([cbn_gext]), so a
  write-back changes no reading at all, and the heap invariant [cbn_gk_cells] — "the cell at
  [a] stands for a reduct of [G a]" — is restored at the forced address by transitivity and
  is untouched everywhere else.

  The fixpoint rule is why the machine puts the forced recursive argument in a *fresh*
  cell: the old cell still stands for the unforced argument, and the unfolded body must see
  the constructor the guard tested, or its result is not a reduct of the input.

  ** What is assumed

  The theorem's hypotheses, each a premise of [cbn_machine_sound]:
  - [wfΣ], [hΣ]: [Σ] is well formed and is the environment [X] stands for.
  - [hΔ]: the readings live in [Γ ,,, Δ], and [Δ] has [lvl - nctx] entries.
  - [hnctx], [hlvl]: what the machine's comment says of its own parameters.
  - [const_instance_ok]: every constant a let-body of [Γ] names carries an instance of the
    right length ([PCUICCallByNeedSoundHook.cbn_consts_okb]). [cbn_delta_red1] needs this of the
    constant it unfolds, because the machine's [cbn_inst_code []] is the identity where PCUIC
    substitutes the empty instance. For the entries of the code table it is part of the
    state invariant [cbn_gok]: a constant body has it by [cbn_declared_constant_consts_okb], an
    input term by [cbn_typing_consts_okb']. Only the let-bodies of the context come from outside
    the table.

  The memo facts are proved, not assumed: [cbn_gok] carries [cbn_memo_inv] of
  [PCUICCallByNeedSoundMemo] and [cbn_memo_ok] of [PCUICCallByNeedSoundCtx], and every reading
  of a code says the code is in the code table ([cbn_cok]), which is what [cbn_once_body] needs to
  keep its cache sound.

  ** Hygiene

  [cbn_gok] also says that every ghost term, and every entry of the code table, is hygienic
  ([on_free_vars cbn_xpredT]: its variables are anything, but the contexts of its matches are
  closed), under the premise [cbn_ctx_hyg] that the let-bodies of [Γ] are. [cbn_machine_sound]
  itself never uses it. The comparison needs it to change level: red weakening and red under
  substitution are false for a term whose match contexts are not closed, because [lift]
  leaves those contexts alone while [iota_red] expands their let-bodies. [cbn_machine_sound]
  returns its ghost existentially, so only its own invariant can carry the clause. The hook
  establishes [cbn_ctx_hyg] and both clauses ([cbn_run_gok_frame]); every new ghost term is a
  reading of hygienic ghost terms and codes ([cbn_g_slot_hyg], [cbn_g_susp_hyg]), which is the
  premise [cbn_alloc_sound] asks of the reading it allocates.

  ** Collections

  A run may collect when [cbn_st_room] is spent. A collection renames every address, so the ghost a
  call ends with is not an extension of the one it started with: every clause of
  [cbn_machine_sound] says instead that the roots come back renamed and stand, under the new ghost,
  for what they stood for ([cbn_gren]). The ghost of the new heap is built along the collector's
  walk, at each fresh address from the ghost term of the old address copied there
  ([cbn_collect_ghost]). It needs nothing of the collector beyond its invariant [cbn_gc_inv] and
  [cbn_gc_copy_ok] ([PCUICCallByNeedSoundGC]). *)

Lemma cbn_forallb_map_All {A B} (f : A -> B) (p : B -> bool) (q : A -> bool) (l : list A) :
  All (fun x => p (f x) = q x) l -> forallb p (map f l) = forallb q l.
Proof. induction 1 as [|x l hx hl ih]; cbn; [reflexivity|]. rewrite hx, ih. reflexivity. Qed.

(** ** Instances, closedness and the instance condition on the codes of the table *)

(** [cbn_consts_okb] reads only instance lengths, which [subst_instance] keeps. *)
Lemma cbn_consts_subst_instance (Σ : global_env) (u : Instance.t) (t : term) :
  cbn_consts_okb Σ (subst_instance u t) = cbn_consts_okb Σ t.
Proof.
  induction t using term_forall_list_ind; cbn; try reflexivity.
  all: try solve [rewrite IHt1, IHt2, IHt3; reflexivity].
  all: try solve [rewrite IHt1, IHt2; reflexivity].
  all: try solve [rewrite IHt; reflexivity].
  all: try solve [unfold cbn_inst_okb; destruct (lookup_env Σ _) as [[]|]; try reflexivity;
                  now rewrite ?length_map, ?subst_instance_instance_length].
  all: try solve [apply cbn_forallb_map_All; exact X].
  all: try solve [apply cbn_forallb_map_All; eapply All_impl; [exact X|];
                  intros d [h1 h2]; cbn; rewrite h1, h2; reflexivity].
  destruct X as (hpar & _ & hret). rewrite IHt, hret, (cbn_forallb_map_All _ _ _ _ hpar).
  erewrite (cbn_forallb_map_All _ (fun br => cbn_consts_okb Σ (bbody br))); [reflexivity|].
  eapply All_impl; [exact X0|]. intros br [_ hb]. exact hb.
Qed.

Lemma cbn_consts_inst_code (Σ : global_env) (u : Instance.t) (t : term) :
  cbn_consts_okb Σ (cbn_inst_code u t) = cbn_consts_okb Σ t.
Proof.
  destruct u as [|l u]; [reflexivity|]. rewrite cbn_inst_code_cons. apply cbn_consts_subst_instance.
Qed.

Lemma cbn_closed_inst_code (u : Instance.t) (t : term) : closedn 0 t ->
  closedn 0 (cbn_inst_code u t).
Proof.
  intros h. destruct u as [|l u]; [exact h|]. rewrite cbn_inst_code_cons, closedn_subst_instance.
  exact h.
Qed.

(** ** Fixpoints: the reading of a [tFix] code and its unfolding *)

Lemma cbn_fix_subst_seq (l : mfixpoint term) :
  fix_subst l = List.rev (map (tFix l) (seq 0 #|l|)).
Proof.
  unfold fix_subst. generalize #|l| as n. induction n as [|n ih]; [reflexivity|].
  transitivity (tFix l n :: List.rev (map (tFix l) (seq 0 n))).
  - simpl. f_equal. exact ih.
  - rewrite seq_S, map_app, rev_app_distr. reflexivity.
Qed.

(** The fixpoints of a [tFix] code read through an environment: [subst ts 0] of
  [lift K n] of each definition, under the [#|mfix|] binders of the block. *)
#[local] Definition cbn_rfix (ts : list term) (K n : nat) (mfix : mfixpoint term)
  : mfixpoint term :=
  map (map_def (subst ts 0) (subst ts (#|mfix| + 0)))
    (map (map_def (lift K n) (lift K (#|mfix| + n))) mfix).

Lemma cbn_rfix_eq ts K n mfix j : subst ts 0 (lift K n (tFix mfix j))
  = tFix (cbn_rfix ts K n mfix) j.
Proof. cbn [lift subst]. unfold cbn_rfix. rewrite length_map. reflexivity. Qed.

Lemma cbn_rfix_length ts K n mfix : #|cbn_rfix ts K n mfix| = #|mfix|.
Proof. unfold cbn_rfix. now rewrite !length_map. Qed.

(** Unfolding the read fixpoint is reading its body in the environment extended by the
  [#|mfix|] fixpoints, the last one first: exactly the environment [cbn_push_fix_cells] builds. *)
Lemma cbn_unfold_fix_rfix ts K n mfix idx d :
  nth_error mfix idx = Some d ->
  unfold_fix (cbn_rfix ts K n mfix) idx
  = Some (rarg d, subst (List.rev (map (tFix (cbn_rfix ts K n mfix)) (seq 0 #|mfix|)) ++ ts) 0
                    (lift K (#|mfix| + n) (dbody d))).
Proof.
  intros hd. unfold unfold_fix.
  assert (hn : nth_error (cbn_rfix ts K n mfix) idx
               = Some (map_def (subst ts 0) (subst ts (#|mfix| + 0))
                         (map_def (lift K n) (lift K (#|mfix| + n)) d))).
  { unfold cbn_rfix. rewrite !nth_error_map, hd. reflexivity. }
  rewrite hn. cbn [rarg dbody map_def]. rewrite cbn_fix_subst_seq, cbn_rfix_length.
  rewrite subst_app_simpl, List.length_rev, length_map, length_seq, Nat.add_0_r.
  reflexivity.
Qed.

(** ** Setting one element of a list *)

Lemma cbn_nth_error_list_set_same {A} (l : list A) n x :
  n < #|l| -> nth_error (cbn_list_set l n x) n = Some x.
Proof.
  revert n. induction l as [|y l ih]; intros [|n] h; cbn in *; try lia; try reflexivity.
  apply ih. lia.
Qed.

Lemma cbn_list_set_nth_id {A} (l : list A) n x : nth_error l n = Some x -> cbn_list_set l n x = l.
Proof.
  revert n. induction l as [|y l ih]; intros [|n] h; cbn in *; try discriminate.
  - injection h as ->. reflexivity.
  - now rewrite (ih n h).
Qed.

Lemma cbn_All2_red_list_set {cf : checker_flags} (Σ : global_env_ext) Γ (l : list term) n t u :
  nth_error l n = Some t -> red Σ Γ t u -> All2 (red Σ Γ) l (cbn_list_set l n u).
Proof.
  revert n. induction l as [|y l ih]; intros [|n] h hr; cbn in *; try discriminate.
  - injection h as ->. constructor; [exact hr|]. apply All2_same. intros; apply refl_red.
  - constructor; [apply refl_red|]. exact (ih n h hr).
Qed.

Lemma cbn_is_constructor_list_set n (l : list term) i k u ts :
  n < #|l| -> is_constructor n (cbn_list_set l n (mkApps (tConstruct i k u) ts)) = true.
Proof.
  intros h. unfold is_constructor. rewrite cbn_nth_error_list_set_same by exact h.
  unfold isConstruct_app. rewrite decompose_app_mkApps by reflexivity. reflexivity.
Qed.

(** ** Matches: the reading of a [tCase] code and its iota step *)

Lemma cbn_forallb_is_assum_ctx (ctx : context) :
  forallb cbn_is_assum ctx = true -> assumption_context ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx ih]; cbn; intros h; [constructor|discriminate|].
  constructor. apply ih. exact h.
Qed.

(** A branch whose context has no let-in needs no [expand_lets]. *)
Lemma cbn_iota_red_assum npar p args br :
  assumption_context br.(bcontext) ->
  iota_red npar p args br = subst (List.rev (skipn npar args)) 0 br.(bbody).
Proof.
  intros h. unfold iota_red. rewrite expand_lets_assumption_context; [reflexivity|].
  unfold inst_case_branch_context, inst_case_context.
  apply assumption_context_fold. apply PCUICInductiveInversion.assumption_context_map.
  exact h.
Qed.

(** A branch read through an environment: its body under the branch's own binders. *)
#[local] Definition cbn_rbr (ts : list term) (K n : nat) (br : branch term) : branch term :=
  {| bcontext := br.(bcontext);
     bbody := subst ts #|br.(bcontext)| (lift K (#|br.(bcontext)| + n) br.(bbody)) |}.

Lemma cbn_subst_lift_case ts K n ci p scrut brs :
  subst ts 0 (lift K n (tCase ci p scrut brs))
  = tCase ci (map_predicate_k id (subst ts) 0 (map_predicate_k id (lift K) n p))
      (subst ts 0 (lift K n scrut)) (map (cbn_rbr ts K n) brs).
Proof.
  cbn [lift subst]. f_equal. rewrite map_map. apply map_ext. intros br.
  unfold map_branch_k, cbn_rbr, id. cbn. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma cbn_forallb_nth_some {A} (p : A -> bool) (l : list A) n x :
  forallb p l = true -> nth_error l n = Some x -> p x = true.
Proof. intros h hn. apply nth_error_In in hn. rewrite forallb_forall in h. exact (h x hn). Qed.

(** [cbn_consts_okb] recurses through every subterm [cbn_code_inv]'s step takes, so a code of an
  entry whose instantiated term satisfies it satisfies it too. *)
Lemma cbn_code_inv_consts_okb (Σ : global_env) (e : cbn_code_entry) (c : cbn_code) :
  cbn_code_inv e c -> cbn_consts_okb Σ (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)) = true ->
  cbn_consts_okb Σ c.(cbn_c_term) = true.
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [_ ht]] hr. revert ht.
  generalize (cbn_c_term c) as t.
  induction ks as [|k ks IH]; cbn [fold_right]; intros t ht.
  - injection ht as <-. exact hr.
  - destruct (fold_right _ _ ks) as [t0|] eqn:E; [|discriminate ht].
    pose proof (IH t0 eq_refl) as h0. clear IH E.
    destruct t0; cbn in ht, h0; try discriminate ht;
      repeat match goal with H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?] end.
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
        exact (cbn_forallb_nth_some (fun br => cbn_consts_okb Σ br.(bbody)) _ _ _
                 ltac:(eassumption) Eb).
      * exact (cbn_forallb_nth_some (cbn_consts_okb Σ) _ _ _ ltac:(eassumption) ht).
      * injection ht as <-. assumption.
    + (* tProj *)
      destruct k as [|q]; cbn in ht; [injection ht as <-; assumption|discriminate ht].
    + (* tFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cbn_forallb_nth_some
                    (fun d => cbn_consts_okb Σ d.(dtype) && cbn_consts_okb Σ d.(dbody)) _ _ _ h0 Ed)
        as hd.
      cbn in hd. apply andb_true_iff in hd. exact (proj2 hd).
    + (* tCoFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cbn_forallb_nth_some
                    (fun d => cbn_consts_okb Σ d.(dtype) && cbn_consts_okb Σ d.(dbody)) _ _ _ h0 Ed)
        as hd.
      cbn in hd. apply andb_true_iff in hd. exact (proj2 hd).
Qed.

(** ** Hygiene: [on_free_vars cbn_xpredT] *)

Lemma cbn_hyg_shift n t : on_free_vars (shiftnP n cbn_xpredT) t = on_free_vars cbn_xpredT t.
Proof. apply on_free_vars_ext. apply shiftnP_xpredT. Qed.

Lemma cbn_hyg_lift n k t : on_free_vars cbn_xpredT t -> on_free_vars cbn_xpredT (lift n k t).
Proof.
  intros h. rewrite <- (on_free_vars_lift cbn_xpredT n k t) in h.
  eapply on_free_vars_impl; [|exact h]. intros; reflexivity.
Qed.

Lemma cbn_hyg_subst s k t :
  forallb (on_free_vars cbn_xpredT) s -> on_free_vars cbn_xpredT t ->
    on_free_vars cbn_xpredT (subst s k t).
Proof.
  intros hs ht. eapply on_free_vars_impl; [|exact (on_free_vars_subst_gen _ _ s k t hs ht)].
  intros; reflexivity.
Qed.

Lemma cbn_hyg_mkApps h ts :
  on_free_vars cbn_xpredT h -> forallb (on_free_vars cbn_xpredT) ts ->
  on_free_vars cbn_xpredT (mkApps h ts).
Proof. intros hh hts. rewrite on_free_vars_mkApps, hh, hts. reflexivity. Qed.

Lemma cbn_hyg_subst_instance u t : on_free_vars cbn_xpredT (subst_instance u t)
  = on_free_vars cbn_xpredT t.
Proof. apply on_free_vars_subst_instance. Qed.

Lemma cbn_hyg_inst_code u t : on_free_vars cbn_xpredT (cbn_inst_code u t)
  = on_free_vars cbn_xpredT t.
Proof. destruct u as [|l u]; [reflexivity|]. rewrite cbn_inst_code_cons.
  apply cbn_hyg_subst_instance. Qed.

(** Hygiene recurses through every subterm [cbn_code_inv]'s step takes, as [cbn_consts_okb] does. *)
Lemma cbn_code_inv_hyg (e : cbn_code_entry) (c : cbn_code) :
  cbn_code_inv e c -> on_free_vars cbn_xpredT (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)) ->
  on_free_vars cbn_xpredT c.(cbn_c_term).
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [_ ht]] hr. revert ht.
  generalize (cbn_c_term c) as t.
  induction ks as [|k ks IH]; cbn [fold_right]; intros t ht.
  - injection ht as <-. exact hr.
  - destruct (fold_right _ _ ks) as [t0|] eqn:E; [|discriminate ht].
    pose proof (IH t0 eq_refl) as h0. clear IH E.
    destruct t0; cbn [on_free_vars] in h0; cbn in ht; try discriminate ht;
      repeat match goal with
             | H : is_true (_ && _) |- _ => apply andb_true_iff in H as [? ?]
             | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
             end;
      rewrite ?cbn_hyg_shift in *.
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
          pose proof (cbn_forallb_nth_some _ _ _ _ H Eb) as hb end.
        cbn beta in hb. apply andb_true_iff in hb as [_ hb]. rewrite cbn_hyg_shift in hb.
        exact hb.
      * match goal with H : forallb _ (pparams _) = true |- _ =>
          exact (cbn_forallb_nth_some _ _ _ _ H ht) end.
      * injection ht as <-. assumption.
    + (* tProj *)
      destruct k as [|q]; cbn in ht; [injection ht as <-; assumption|discriminate ht].
    + (* tFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cbn_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      unfold test_def in hd. apply andb_true_iff in hd as [_ hd]. rewrite cbn_hyg_shift in hd.
      exact hd.
    + (* tCoFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (cbn_forallb_nth_some _ _ _ _ h0 Ed) as hd.
      unfold test_def in hd. apply andb_true_iff in hd as [_ hd]. rewrite cbn_hyg_shift in hd.
      exact hd.
Qed.

(** *** Primitive literals *)

(** A literal is closed: every reading of it is itself. *)
Lemma cbn_lit_subst_lift (l : prim_lit) ts k n m :
  subst ts k (lift n m (term_of_lit l)) = term_of_lit l.
Proof. destruct l; reflexivity. Qed.

Lemma cbn_slot_lits_inr s : forall l i x, cbn_slot_lits l s = inr (i, x) -> nth_error l i = Some x.
Proof.
  induction l as [|y l ih]; intros i x h; cbn [cbn_slot_lits] in h; [discriminate h|].
  destruct (cbn_slot_lit y s) as [lt|].
  - destruct (cbn_slot_lits l s) as [ls|[j z]] eqn:el; [discriminate h|].
    injection h as <- <-. exact (ih j z eq_refl).
  - injection h as <- <-. reflexivity.
Qed.

Lemma cbn_nth_error_firstn_some {A} n (l : list A) i x :
  nth_error (firstn n l) i = Some x -> nth_error l i = Some x.
Proof.
  revert l i. induction n as [|n ih]; intros [|y l] [|i] h; cbn in h |- *;
    try discriminate h; auto.
Qed.

(** The first call whose answer [he] matches on: its answer is [CbnCOk (x, y, z)], named by [e]. *)
Ltac cbn_dcall he e x y z :=
  lazymatch type of he with
  | context [match ?t with CbnCOk _ => _ | CbnCFail _ => _ end] =>
      destruct t as [[[x y] z]|?] eqn:e; [|discriminate he]
  end.

Section Eval.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat).

  (** The environment the readings live in: [Γ] under [lvl - nctx] fresh variables. [Σ] is
     the well-formed environment the abstract one [X] stands for; the hook has both, and the
     delta rule needs them for the body it unfolds. *)
  Context (Σ : global_env_ext) (Δ : context) (lvl : nat).
  Hypothesis wfΣ : wf Σ.
  Hypothesis hΣ : abstract_env_ext_rel X Σ.
  Hypothesis hΔ : #|Δ| = lvl - nctx.

  Local Notation cbn_ΓΔ := (Γ ,,, Δ).

  (** Reduction, squashed: [red1] lives in [Type], the readings here in [Prop]. *)
  Definition cbn_cred (t u : term) : Prop := ∥ red Σ cbn_ΓΔ t u ∥.

  Lemma cbn_cred_refl t : cbn_cred t t.
  Proof. constructor. apply refl_red. Qed.

  Lemma cbn_cred_trans t u v : cbn_cred t u -> cbn_cred u v -> cbn_cred t v.
  Proof. intros [h1] [h2]. constructor. exact (red_trans _ _ _ _ _ h1 h2). Qed.

  Lemma cbn_cred_one t u : red1 Σ cbn_ΓΔ t u -> cbn_cred t u.
  Proof. intros h. constructor. exact (red1_red _ _ _ _ h). Qed.

  Lemma cbn_cred_mkApps t u ts : cbn_cred t u -> cbn_cred (mkApps t ts) (mkApps u ts).
  Proof. intros [h]. constructor. exact (red_mkApps_f _ _ _ h). Qed.

  Lemma cbn_cred_app_r f t u : cbn_cred t u -> cbn_cred (tApp f t) (tApp f u).
  Proof. intros [h]. constructor. exact (red_app_r _ _ _ h). Qed.

  Lemma cbn_cred_letin na d0 d1 T b : cbn_cred d0 d1 ->
    cbn_cred (tLetIn na d0 T b) (tLetIn na d1 T b).
  Proof.
    intros [h]. constructor.
    exact (red_letin na d0 d1 T T b b h (refl_red _ _ _) (refl_red _ _ _)).
  Qed.

  (** ** The ghost

    A ghost is a map [cbn_gm] from addresses to the terms their cells were allocated for, and a
    code table [cbn_gc]: the table every code of a reading is checked against. Both only grow
    ([cbn_gext]). *)

  Record cbn_ghost := cbn_mkGhost { cbn_gm : cbn_haddr -> option term;
    cbn_gc : PTree.t cbn_code_entry }.
  Coercion cbn_gm : cbn_ghost >-> Funclass.

  (** A code is in the table: its index holds an entry it satisfies [cbn_code_inv] for. *)
  Definition cbn_cok (G : cbn_ghost) (c : cbn_code) : Prop :=
    exists e, PTree.get c.(cbn_c_entry) (cbn_gc G) = Some e /\ cbn_code_inv e c.

  Lemma cbn_cok_child G c k t : cbn_cok G c -> cbn_child_step c.(cbn_c_term) k t ->
    cbn_cok G (cbn_child c k t).
  Proof.
    intros [e [he hi]] hs. exists e.
    split; [exact he|exact (cbn_code_inv_child_step e c k t hi hs)].
  Qed.

  (** ** The ghost read-back

    [G a] is the term the cell at [a] was allocated for. An inline suspension is read by
    reading its slots, then substituting them into the code lifted over the environment's
    own variables. *)

  Inductive cbn_g_slot (G : cbn_ghost) : cbn_slot -> term -> Prop :=
  | cbn_g_slot_addr a t : G a = Some t -> cbn_g_slot G (CbnSAddr a) t
  | cbn_g_slot_inl vals nvals goff c ts :
      cbn_g_slots G vals ts -> nvals = #|vals| -> cbn_cok G c ->
      cbn_g_slot G (CbnSInl vals nvals goff c)
        (subst ts 0 (lift (lvl - nctx + goff) nvals c.(cbn_c_term)))

  with cbn_g_slots (G : cbn_ghost) : list cbn_slot -> list term -> Prop :=
  | cbn_g_slots_nil : cbn_g_slots G [] []
  | cbn_g_slots_cons x l t ts :
      cbn_g_slot G x t -> cbn_g_slots G l ts -> cbn_g_slots G (x :: l) (t :: ts).

  Scheme cbn_g_slot_min := Minimality for cbn_g_slot Sort Prop
  with cbn_g_slots_min := Minimality for cbn_g_slots Sort Prop.
  Combined Scheme cbn_g_slot_mutind from cbn_g_slot_min, cbn_g_slots_min.

  Inductive cbn_g_susp (G : cbn_ghost) : cbn_env -> term -> term -> Prop :=
  | cbn_g_susp_intro vals nvals goff t ts :
      cbn_g_slots G vals ts -> nvals = #|vals| ->
      cbn_g_susp G (cbn_mkEnv vals nvals goff) t (subst ts 0 (lift (lvl - nctx + goff) nvals t)).

  Definition cbn_g_addrs (G : cbn_ghost) (l : list cbn_haddr) (ts : list term) : Prop :=
    Forall2 (fun a t => G a = Some t) l ts.

  (** A fixpoint value reads like [cbn_rb_value]: fixpoint [i] of its [tFix] code, read through
    its environment, applied to its spine. *)
  Inductive cbn_g_value (G : cbn_ghost) : cbn_value -> term -> Prop :=
  | cbn_g_VCon h sp ts : cbn_g_addrs G sp ts -> cbn_g_value G (CbnVCon h sp) (mkApps h ts)
  | cbn_g_VLam e c t : cbn_g_susp G e c.(cbn_c_term) t -> cbn_cok G c ->
    cbn_g_value G (CbnVLam e c) t
  | cbn_g_VOpen e c t : cbn_g_susp G e c.(cbn_c_term) t -> cbn_cok G c ->
    cbn_g_value G (CbnVOpen e c) t
  | cbn_g_VNeuVar l sp ts :
      cbn_g_addrs G sp ts -> cbn_g_value G (CbnVNeu (CbnNVar l) sp) (mkApps (tRel (lvl - S l)) ts)
  | cbn_g_VNeuConst h sp ts :
      cbn_g_addrs G sp ts -> cbn_g_value G (CbnVNeu (CbnNConst h) sp) (mkApps h ts)
  | cbn_g_VStuck e c sp h ts :
      cbn_g_susp G e c.(cbn_c_term) h -> cbn_cok G c -> cbn_g_addrs G sp ts ->
      cbn_g_value G (CbnVStuck e c sp) (mkApps h ts)
  | cbn_g_VFix e c mfix idx i sp h ts :
      c.(cbn_c_term) = tFix mfix idx -> cbn_g_susp G e (tFix mfix i) h -> cbn_cok G c ->
        cbn_g_addrs G sp ts ->
      cbn_g_value G (CbnVFix e c i sp) (mkApps h ts)
  | cbn_g_VStuckFix e c mfix idx i sp h ts :
      c.(cbn_c_term) = tFix mfix idx -> cbn_g_susp G e (tFix mfix i) h -> cbn_cok G c ->
        cbn_g_addrs G sp ts ->
      cbn_g_value G (CbnVStuckFix e c i sp) (mkApps h ts).

  Inductive cbn_g_cell (G : cbn_ghost) : cbn_cell -> term -> Prop :=
  | cbn_g_cell_susp vals nvals goff c t :
      cbn_g_susp G (cbn_mkEnv vals nvals goff) c.(cbn_c_term) t -> cbn_cok G c ->
      cbn_g_cell G (CbnCSusp vals nvals goff c) t
  | cbn_g_cell_done v t : cbn_g_value G v t -> cbn_g_cell G (CbnCDone v) t.

  (** ** The ghost map only grows, and every reading survives *)

  Record cbn_gext (G G' : cbn_ghost) : Prop := cbn_mkGext {
    cbn_gx_map : forall a t, G a = Some t -> G' a = Some t;
    cbn_gx_codes : forall i e, PTree.get i (cbn_gc G) = Some e ->
      PTree.get i (cbn_gc G') = Some e }.
  Arguments cbn_gx_map {G G'} _ _ _ _.
  Arguments cbn_gx_codes {G G'} _ _ _ _.
  Coercion cbn_gx_map : cbn_gext >-> Funclass.

  Lemma cbn_gext_refl G : cbn_gext G G.
  Proof. split; intros; assumption. Qed.

  Lemma cbn_gext_trans G1 G2 G3 : cbn_gext G1 G2 -> cbn_gext G2 G3 -> cbn_gext G1 G3.
  Proof.
    intros h1 h2. split.
    - intros a t h. exact (cbn_gx_map h2 _ _ (cbn_gx_map h1 _ _ h)).
    - intros i e h. exact (cbn_gx_codes h2 _ _ (cbn_gx_codes h1 _ _ h)).
  Qed.

  Lemma cbn_cok_mono G G' (h : cbn_gext G G') c : cbn_cok G c -> cbn_cok G' c.
  Proof. intros [e [he hi]]. exists e. split; [exact (cbn_gx_codes h _ _ he)|exact hi]. Qed.

  Lemma cbn_g_slot_ext G G' (h : cbn_gext G G') :
    (forall x t, cbn_g_slot G x t -> cbn_g_slot G' x t)
    /\ (forall l ts, cbn_g_slots G l ts -> cbn_g_slots G' l ts).
  Proof using.
    apply (cbn_g_slot_mutind G (fun x t => cbn_g_slot G' x t) (fun l ts => cbn_g_slots G' l ts)).
    - intros a t ha. constructor. exact (cbn_gx_map h _ _ ha).
    - intros vals nvals goff c ts _ ih hn hc.
      constructor; [exact ih|exact hn|exact (cbn_cok_mono G G' h c hc)].
    - constructor.
    - intros x l t ts _ ih1 _ ih2. constructor; [exact ih1|exact ih2].
  Qed.

  Definition cbn_g_slot_mono G G' (h : cbn_gext G G') := proj1 (cbn_g_slot_ext G G' h).
  Definition cbn_g_slots_mono G G' (h : cbn_gext G G') := proj2 (cbn_g_slot_ext G G' h).

  Lemma cbn_g_susp_mono G G' (h : cbn_gext G G') e t u : cbn_g_susp G e t u -> cbn_g_susp G' e t u.
  Proof.
    intros hs. inversion hs; subst. constructor; try reflexivity; try assumption.
    eapply (cbn_g_slots_mono G G' h). eassumption.
  Qed.

  Lemma cbn_g_addrs_mono G G' (h : cbn_gext G G') l ts : cbn_g_addrs G l ts -> cbn_g_addrs G' l ts.
  Proof.
    intros ha. induction ha as [|a t l ts hat hl ih]; constructor;
      [exact (cbn_gx_map h _ _ hat)|exact ih].
  Qed.

  Lemma cbn_g_value_mono G G' (h : cbn_gext G G') v t : cbn_g_value G v t -> cbn_g_value G' v t.
  Proof.
    intros hv. destruct hv; econstructor;
      eauto using cbn_g_addrs_mono, cbn_g_susp_mono, cbn_cok_mono.
  Qed.

  Lemma cbn_g_cell_mono G G' (h : cbn_gext G G') cl t : cbn_g_cell G cl t -> cbn_g_cell G' cl t.
  Proof.
    intros hc. destruct hc; econstructor; eauto using cbn_g_value_mono, cbn_g_susp_mono,
      cbn_cok_mono.
  Qed.

  (** ** Every address a reading names has a ghost term *)

  #[local] Definition cbn_gdef (G : cbn_haddr -> option term) (a : cbn_haddr) : Prop := exists t,
    G a = Some t.

  Lemma cbn_g_slot_ad G :
    (forall x t, cbn_g_slot G x t -> Forall (cbn_gdef G) (cbn_ad_slot x))
    /\ (forall l ts, cbn_g_slots G l ts -> Forall (cbn_gdef G) (cbn_ad_slots l)).
  Proof using.
    apply (cbn_g_slot_mutind G
      (fun x t => Forall (cbn_gdef G) (cbn_ad_slot x))
      (fun l ts => Forall (cbn_gdef G) (cbn_ad_slots l))).
    - intros a t ha. constructor; [exists t; exact ha|constructor].
    - intros vals nvals goff c ts _ ih _ _. exact ih.
    - constructor.
    - intros x l t ts _ ih1 _ ih2. unfold cbn_ad_slots. cbn [flat_map].
      apply app_Forall; [exact ih1|exact ih2].
  Qed.

  Lemma cbn_g_addrs_ad G l ts : cbn_g_addrs G l ts -> Forall (cbn_gdef G) l.
  Proof. intros h. induction h; constructor; [eexists; eassumption|assumption]. Qed.

  Lemma cbn_g_susp_ad G e t u : cbn_g_susp G e t u -> Forall (cbn_gdef G) (cbn_ad_env e).
  Proof.
    intros h. inversion h; subst. unfold cbn_ad_env. cbn [cbn_ev_vals].
    eapply (proj2 (cbn_g_slot_ad G)). eassumption.
  Qed.

  Lemma cbn_g_value_ad G v t : cbn_g_value G v t -> Forall (cbn_gdef G) (cbn_ad_value v).
  Proof.
    intros h. destruct h; cbn [cbn_ad_value];
      try (eapply cbn_g_addrs_ad; eassumption);
      try (eapply cbn_g_susp_ad; eassumption).
    all: apply app_Forall;
      [eapply cbn_g_susp_ad; eassumption|eapply cbn_g_addrs_ad; eassumption].
  Qed.

  Lemma cbn_g_cell_ad G cl t : cbn_g_cell G cl t -> Forall (cbn_gdef G) (cbn_ad_cell cl).
  Proof.
    intros h. destruct h; cbn [cbn_ad_cell].
    - inversion H; subst. eapply (proj2 (cbn_g_slot_ad G)). eassumption.
    - exact (cbn_g_value_ad _ _ _ H).
  Qed.

  (** ** The state operations that leave the heap shape alone

    What [cbn_heap_upd], [cbn_tick], [cbn_new_entry], [cbn_once_body] and [cbn_delta] change of a
    state. *)

  Lemma cbn_heap_upd_shape a cl s s' :
    cbn_heap_upd a cl s = Some s' ->
    s'.(cbn_st_next) = s.(cbn_st_next) /\ s'.(cbn_st_room) = s.(cbn_st_room)
    /\ s'.(cbn_st_steps) = s.(cbn_st_steps) /\ s'.(cbn_st_gam) = s.(cbn_st_gam)
    /\ s'.(cbn_st_memo) = s.(cbn_st_memo) /\
      cbn_bh_upd a cl s.(cbn_st_heap) = Some s'.(cbn_st_heap).
  Proof.
    unfold cbn_heap_upd. destruct (cbn_bh_upd a cl s.(cbn_st_heap)) as [h'|] eqn:e; cbn;
      [|discriminate].
    intros he. inversion he; subst. cbn. repeat split; try reflexivity.
  Qed.

  Lemma cbn_tick_shape s s' :
    cbn_tick s = Some s' ->
    s'.(cbn_st_heap) = s.(cbn_st_heap) /\ s'.(cbn_st_next) = s.(cbn_st_next)
    /\ s'.(cbn_st_room) = s.(cbn_st_room) /\ s'.(cbn_st_gam) = s.(cbn_st_gam)
    /\ s'.(cbn_st_memo) = s.(cbn_st_memo).
  Proof.
    unfold cbn_tick. destruct s.(cbn_st_steps) eqn:e; [discriminate|].
    intros he. inversion he; subst. cbn. repeat split; reflexivity.
  Qed.

  (** [cbn_new_entry], [cbn_once_body] and [cbn_delta] touch only the memo. *)

  Lemma cbn_new_entry_shape t u s :
    (snd (cbn_new_entry X_type X t u s)).(cbn_st_heap) = s.(cbn_st_heap)
    /\ (snd (cbn_new_entry X_type X t u s)).(cbn_st_next) = s.(cbn_st_next)
    /\ (snd (cbn_new_entry X_type X t u s)).(cbn_st_room) = s.(cbn_st_room)
    /\ (snd (cbn_new_entry X_type X t u s)).(cbn_st_steps) = s.(cbn_st_steps)
    /\ (snd (cbn_new_entry X_type X t u s)).(cbn_st_gam) = s.(cbn_st_gam)
    /\ ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).(cbn_m_delta)
       = (s.(cbn_st_memo)).(cbn_m_delta).
  Proof. repeat split; reflexivity. Qed.

  Lemma cbn_once_body_shape c s :
    (snd (cbn_once_body c s)).(cbn_st_heap) = s.(cbn_st_heap)
    /\ (snd (cbn_once_body c s)).(cbn_st_next) = s.(cbn_st_next)
    /\ (snd (cbn_once_body c s)).(cbn_st_room) = s.(cbn_st_room)
    /\ (snd (cbn_once_body c s)).(cbn_st_steps) = s.(cbn_st_steps)
    /\ (snd (cbn_once_body c s)).(cbn_st_gam) = s.(cbn_st_gam)
    /\ ((snd (cbn_once_body c s)).(cbn_st_memo)).(cbn_m_delta) = (s.(cbn_st_memo)).(cbn_m_delta).
  Proof.
    unfold cbn_once_body.
    destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) ((s.(cbn_st_memo)).(cbn_m_once))) as [b|];
      cbn; repeat split; reflexivity.
  Qed.

  Lemma cbn_delta_shape kn u s r s' :
    cbn_delta X_type X kn u s = CbnCOk (r, s') ->
    s'.(cbn_st_heap) = s.(cbn_st_heap) /\ s'.(cbn_st_next) = s.(cbn_st_next)
    /\ s'.(cbn_st_room) = s.(cbn_st_room) /\ s'.(cbn_st_steps) = s.(cbn_st_steps)
    /\ s'.(cbn_st_gam) = s.(cbn_st_gam).
  Proof.
    intros he.
    destruct (cbn_delta_cases X_type X kn u s r s' he)
      as [[-> _]|[(body & insts & _ & _ & ->)|(cb & _ & _ & _ & ->)]].
    - repeat split; reflexivity.
    - rewrite cbn_delta_new_spec.
      destruct (cbn_new_entry_shape body u s) as (p1 & p2 & p3 & p4 & p5 & _).
      exact (conj p1 (conj p2 (conj p3 (conj p4 p5)))).
    - repeat split; reflexivity.
  Qed.

  (** ** What the machine assumes of a state

    Beside the heap laws of [cbn_state_ok] and the absence of forwarding pointers, the state
    carries a ghost map: every cell has a ghost term, and the cell stands for a reduct of
    it, unless the cell is being forced, in which case its caller carries the reading. *)

  (** Hygiene: a term passes [on_free_vars cbn_xpredT], which beside its variables tests that
    the contexts of its matches are closed. Red weakening ([weakening_red1]) and red under
    substitution ([red_red]) need it of the terms they move: [lift] does not touch the
    contexts of a match while [iota_red] expands their let-bodies, so without it a lifted
    term can reduce to the unlifted reduct. The machine never looks at it; the comparison
    needs it of every ghost term to change level. Every ghost term is a reading built from
    codes and older ghost terms, and every code comes from a typed term, except that the
    let-bodies of [Γ] come from outside the code table: so the clauses below hold under
    [cbn_ctx_hyg], which the hook has from [wf_local]. *)
  Definition cbn_ctx_hyg : Prop := forall j decl b,
    nth_error Γ j = Some decl -> decl.(decl_body) = Some b -> on_free_vars cbn_xpredT b.

  (** The memo of the state: the invariants of the memo files ([cbn_memo_inv], [cbn_memo_ok]); the
    ghost's code table [K] is part of the real one; every entry of the real one names its
    constants at the right instance length; and, under [cbn_ctx_hyg], every entry is hygienic. *)
  #[local] Definition cbn_mok (K : PTree.t cbn_code_entry) (s : cbn_state) : Prop :=
    cbn_memo_inv X_type X s /\ cbn_memo_ok X_type X s
    /\ (forall i e, PTree.get i K = Some e ->
      PTree.get i ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e)
    /\ (forall i e, PTree.get i ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
          cbn_consts_okb Σ (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)) = true)
    /\ (cbn_ctx_hyg -> forall i e, PTree.get i ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
          on_free_vars cbn_xpredT (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term))).

  Record cbn_gok (lo : positive) (G : cbn_ghost) (s : cbn_state) : Prop := cbn_mkGok {
    cbn_gk_state : cbn_state_ok lo s;
    cbn_gk_nofwd : cbn_heap_nofwd s.(cbn_st_heap);
    cbn_gk_cells : forall a cl, cbn_heap_get a s = Some cl ->
      exists t, G a = Some t
        /\ (cl = CbnCBusy \/ exists u, cbn_g_cell G cl u /\ cbn_cred t u);
    cbn_gk_dom : forall a t, G a = Some t ->
      (lo <= cbn_ha_p a)%positive /\ (cbn_ha_p a < s.(cbn_st_next))%positive;
    cbn_gk_gam : forall j a, PTree.get (cbn_key_of_succ_nat j) s.(cbn_st_gam) = Some a ->
      exists t, cbn_ctx_den Γ nctx lvl j = Some t /\ G a = Some t;
    cbn_gk_memo : cbn_mok (cbn_gc G) s;
    cbn_gk_hyg : cbn_ctx_hyg -> forall a t, G a = Some t -> on_free_vars cbn_xpredT t }.

  (** *** Readings of hygienic ghost terms and codes are hygienic *)

  Definition cbn_hygG (G : cbn_ghost) : Prop := forall a t, G a = Some t ->
    on_free_vars cbn_xpredT t.
  Definition cbn_codes_hyg (G : cbn_ghost) : Prop := forall c, cbn_cok G c ->
    on_free_vars cbn_xpredT c.(cbn_c_term).

  Lemma cbn_gok_codes_hyg lo G s : cbn_gok lo G s -> cbn_ctx_hyg -> cbn_codes_hyg G.
  Proof.
    intros hok hc c [e [he hi]].
    destruct (cbn_gk_memo _ _ _ hok) as (_ & _ & hK & _ & hh).
    exact (cbn_code_inv_hyg e c hi (hh hc _ _ (hK _ _ he))).
  Qed.

  Lemma cbn_g_slot_hyg G (hG : cbn_hygG G) (hC : cbn_codes_hyg G) :
    (forall x t, cbn_g_slot G x t -> on_free_vars cbn_xpredT t)
    /\ (forall l ts, cbn_g_slots G l ts -> forallb (on_free_vars cbn_xpredT) ts).
  Proof using.
    apply (cbn_g_slot_mutind G (fun x t => on_free_vars cbn_xpredT t)
             (fun l ts => forallb (on_free_vars cbn_xpredT) ts)).
    - intros a t ha. exact (hG _ _ ha).
    - intros vals nvals goff c ts _ ih _ hc.
      apply cbn_hyg_subst; [exact ih|apply cbn_hyg_lift; exact (hC c hc)].
    - reflexivity.
    - intros x l t ts _ ih1 _ ih2. cbn. rewrite ih1, ih2. reflexivity.
  Qed.

  Lemma cbn_g_susp_hyg G (hG : cbn_hygG G) (hC : cbn_codes_hyg G) e t u :
    on_free_vars cbn_xpredT t -> cbn_g_susp G e t u -> on_free_vars cbn_xpredT u.
  Proof.
    intros ht hs. inversion hs; subst.
    apply cbn_hyg_subst; [exact (proj2 (cbn_g_slot_hyg G hG hC) _ _ H)|apply
      cbn_hyg_lift; exact ht].
  Qed.

  Lemma cbn_g_addrs_hyg G (hG : cbn_hygG G) l ts : cbn_g_addrs G l ts ->
    forallb (on_free_vars cbn_xpredT) ts.
  Proof.
    induction 1 as [|a t l ts ha hl ih]; [reflexivity|]. cbn. rewrite (hG _ _ ha), ih.
    reflexivity.
  Qed.

  Lemma cbn_hyg_tFix_idx mfix i j :
    on_free_vars cbn_xpredT (tFix mfix i) -> on_free_vars cbn_xpredT (tFix mfix j).
  Proof. cbn [on_free_vars]. exact (fun h => h). Qed.

  (** ** The algebra of ghost readings *)

  Lemma cbn_g_susp_inv G e t u :
    cbn_g_susp G e t u ->
    exists ts, cbn_g_slots G e.(cbn_ev_vals) ts /\ e.(cbn_ev_nvals) = #|e.(cbn_ev_vals)|
      /\ u = subst ts 0 (lift (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals) t).
  Proof.
    intros h. inversion h; subst. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff].
    exists ts. repeat split; assumption.
  Qed.

  Lemma cbn_g_slots_length G l ts : cbn_g_slots G l ts -> #|ts| = #|l|.
  Proof. induction 1; cbn; [reflexivity|]. rewrite IHcbn_g_slots. reflexivity. Qed.

  Lemma cbn_g_slots_nth G l ts n x :
    cbn_g_slots G l ts -> nth_error l n = Some x ->
    exists t, nth_error ts n = Some t /\ cbn_g_slot G x t.
  Proof.
    intros h. revert n. induction h as [|y l t ts hy hl ih]; intros n hn.
    - destruct n; discriminate.
    - destruct n as [|n]; cbn in hn.
      + injection hn as <-. exists t. split; [reflexivity|exact hy].
      + exact (ih n hn).
  Qed.

  (** The reading of a suspension whose code is an application, a lambda, a let or a
    constant: the machine's own decomposition, with [subst] and [lift] computed. *)

  Lemma cbn_subst_cons_app (tx : term) (ts : list term) (b : term) :
    subst (tx :: ts) 0 b = subst [tx] 0 (subst ts 1 b).
  Proof. pose proof (subst_app_simpl [tx] ts 0 b) as h. cbn in h. exact h. Qed.

  Lemma cbn_g_susp_app G e f a u :
    cbn_g_susp G e (tApp f a) u ->
    exists uf ua, u = tApp uf ua /\ cbn_g_susp G e f uf /\ cbn_g_susp G e a ua.
  Proof.
    intros h. destruct (cbn_g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; split; [reflexivity|].
    split; constructor; (exact h1 || reflexivity || assumption).
  Qed.

  (** A [tConst] has no free variables, so a [lift] followed by a [subst] leaves it
    alone: the reading of a suspension whose code is a constant is that constant, whatever
    the environment. *)
  Lemma cbn_subst_lift_const ts n m p kn ui :
    subst ts n (lift m p (tConst kn ui)) = tConst kn ui.
  Proof. reflexivity. Qed.

  Lemma cbn_g_susp_const G e kn ui u : cbn_g_susp G e (tConst kn ui) u -> u = tConst kn ui.
  Proof.
    intros h. destruct (cbn_g_susp_inv _ _ _ _ h) as [ts (_ & _ & ->)]. reflexivity.
  Qed.

  Lemma cbn_g_susp_tind G e i ui u : cbn_g_susp G e (tInd i ui) u -> u = tInd i ui.
  Proof.
    intros h. destruct (cbn_g_susp_inv _ _ _ _ h) as [ts (_ & _ & ->)]. reflexivity.
  Qed.

  Lemma cbn_g_susp_construct G e i n ui u :
    cbn_g_susp G e (tConstruct i n ui) u -> u = tConstruct i n ui.
  Proof.
    intros h. destruct (cbn_g_susp_inv _ _ _ _ h) as [ts (_ & _ & ->)]. reflexivity.
  Qed.

  (** Pushing a slot on the environment is PCUIC's substitution on the reading: this is
    the substitution-composition the beta and zeta rules need. *)

  Lemma cbn_g_susp_lam G e na A b u :
    cbn_g_susp G e (tLambda na A b) u ->
    exists A' B, u = tLambda na A' B
      /\ (forall x tx, cbn_g_slot G x tx -> cbn_g_susp G (cbn_env_push x e) b (subst [tx] 0 B)).
  Proof.
    intros h. destruct (cbn_g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; split; [reflexivity|].
    intros x tx hx.
    rewrite <- (cbn_subst_cons_app tx ts (lift (lvl - nctx + goff) (S #|vals|) b)).
    unfold cbn_env_push. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff].
    exact (cbn_g_susp_intro G (x :: vals) (S #|vals|) goff b (tx :: ts)
             (cbn_g_slots_cons G x vals tx ts hx h1) eq_refl).
  Qed.

  Lemma cbn_g_susp_letin G e na d T b u :
    cbn_g_susp G e (tLetIn na d T b) u ->
    exists d' T' B, u = tLetIn na d' T' B /\ cbn_g_susp G e d d'
      /\ (forall x tx, cbn_g_slot G x tx -> cbn_g_susp G (cbn_env_push x e) b (subst [tx] 0 B)).
  Proof.
    intros h. destruct (cbn_g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; eexists; split; [reflexivity|].
    split.
    - constructor; (exact h1 || reflexivity || assumption).
    - intros x tx hx.
      rewrite <- (cbn_subst_cons_app tx ts (lift (lvl - nctx + goff) (S #|vals|) b)).
      unfold cbn_env_push. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff].
      exact (cbn_g_susp_intro G (x :: vals) (S #|vals|) goff b (tx :: ts)
               (cbn_g_slots_cons G x vals tx ts hx h1) eq_refl).
  Qed.

  Lemma cbn_g_slots_list_set G l ts n x t :
    cbn_g_slots G l ts -> cbn_g_slot G x t ->
      cbn_g_slots G (cbn_list_set l n x) (cbn_list_set ts n t).
  Proof.
    intros h hx. revert n. induction h as [|y l u us hy hl ih]; intros [|n]; cbn;
      constructor; try assumption. apply ih.
  Qed.

  Lemma cbn_g_slots_addrs G l ts : cbn_g_addrs G l ts -> cbn_g_slots G (map CbnSAddr l) ts.
  Proof. induction 1; cbn; constructor; [constructor; assumption|assumption]. Qed.

  Lemma cbn_g_slots_app G l1 ts1 l2 ts2 :
    cbn_g_slots G l1 ts1 -> cbn_g_slots G l2 ts2 -> cbn_g_slots G (l1 ++ l2) (ts1 ++ ts2).
  Proof. induction 1; cbn; [trivial|]. intros h2. constructor; auto. Qed.

  Lemma cbn_g_addrs_nth G l ts n a :
    cbn_g_addrs G l ts -> nth_error l n = Some a -> exists t, nth_error ts n = Some t /\
      G a = Some t.
  Proof.
    intros h. revert n. induction h as [|b t l ts hb hl ih]; intros [|n] hn; cbn in hn;
      try discriminate.
    - injection hn as <-. exists t. split; [reflexivity|exact hb].
    - exact (ih n hn).
  Qed.

  Lemma cbn_g_addrs_length G l ts : cbn_g_addrs G l ts -> #|ts| = #|l|.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma cbn_g_slots_firstn_skipn G : forall n l ts, cbn_g_slots G l ts ->
    cbn_g_slots G (firstn n l) (firstn n ts) /\ cbn_g_slots G (skipn n l) (skipn n ts).
  Proof.
    intros n. induction n as [|n ih]; intros l ts h.
    - cbn [firstn skipn]. split; [constructor|exact h].
    - destruct h as [|x l t ts hx hl].
      + cbn [firstn skipn]. split; constructor.
      + cbn [firstn skipn]. destruct (ih l ts hl) as [h1 h2].
        split; [constructor; assumption|exact h2].
  Qed.

  (** ** What this file assumes

    [hnctx] and [hlvl] say what the machine's comment says of its own parameters.
    [const_instance_ok] is the instance condition [cbn_delta_red1] needs, for the constants the
    context's let-bodies name; for the rest it is proved (see the file header). *)

  Hypothesis hnctx : nctx = #|Γ|.
  Hypothesis hlvl : nctx <= lvl.
  Hypothesis const_instance_ok : forall j decl b,
    nth_error Γ j = Some decl -> decl.(decl_body) = Some b -> cbn_consts_okb Σ b = true.

  (** *** The primitive-operation rule's oracle against [Σ] *)

  Lemma cbn_readback_correct sh r : cbn_readback X_type X sh r = readback Σ sh r.
  Proof.
    destruct sh, r; cbn; try reflexivity.
    rewrite (abstract_primitive_bool_correct X Σ hΣ). reflexivity.
  Qed.

  (** A read-back result is closed and hygienic, and names no constant. *)
  Lemma cbn_readback_term sh r t : cbn_readback X_type X sh r = Some t ->
    closedn 0 t /\ on_free_vars cbn_xpredT t /\ cbn_consts_okb Σ t = true.
  Proof.
    destruct sh, r; cbn; try (intros h; discriminate h).
    - intros [= <-]. split; [reflexivity|split; reflexivity].
    - destruct (abstract_primitive_bool X) as [ind|]; [|intros h; discriminate h].
      intros [= <-]. split; [reflexivity|split; reflexivity].
  Qed.

  Lemma cbn_prim_step_fire kn stk s t rest :
    cbn_prim_step_of X_type X kn stk s = CbnPFire t rest ->
    exists p ls r, abstract_prim_op_of X kn = Some p
      /\ cbn_slot_lits (firstn (arity p) stk) s = inl ls /\ prim_op_denote p ls = Some r
      /\ cbn_readback X_type X (po_shape (info p)) r = Some t /\ rest = skipn (arity p) stk.
  Proof.
    unfold cbn_prim_step_of.
    destruct (abstract_prim_op_of X kn) as [p|] eqn:hop; [|intros h; discriminate h].
    destruct (Nat.leb (arity p) #|stk|); [|intros h; discriminate h].
    destruct (cbn_slot_lits (firstn (arity p) stk) s) as [ls|[i x]] eqn:hls;
      [|intros h; discriminate h].
    destruct (prim_op_denote p ls) as [r|] eqn:hden; [|intros h; discriminate h].
    destruct (cbn_readback X_type X (po_shape (info p)) r) as [t'|] eqn:hrb;
      [|intros h; discriminate h].
    intros h. injection h as <- <-. exists p, ls, r.
    split; [reflexivity|]. split; [exact hls|]. split; [exact hden|].
    split; [exact hrb|reflexivity].
  Qed.

  Lemma cbn_prim_step_force kn stk s i x :
    cbn_prim_step_of X_type X kn stk s = CbnPForce i x -> nth_error stk i = Some x.
  Proof.
    unfold cbn_prim_step_of.
    destruct (abstract_prim_op_of X kn) as [p|]; [|intros h; discriminate h].
    destruct (Nat.leb (arity p) #|stk|); [|intros h; discriminate h].
    destruct (cbn_slot_lits (firstn (arity p) stk) s) as [ls|[j y]] eqn:el.
    - destruct (prim_op_denote p ls) as [r|]; [|intros h; discriminate h].
      destruct (cbn_readback X_type X (po_shape (info p)) r); intros h; discriminate h.
    - intros h. injection h as <- <-.
      exact (cbn_nth_error_firstn_some _ _ _ _ (cbn_slot_lits_inr s _ _ _ el)).
  Qed.

  (** ** The state operations against the ghost map *)

  Lemma cbn_haddr_eqb_eq a b : cbn_haddr_eqb a b = true -> a = b.
  Proof.
    destruct a as [p], b as [q]. unfold cbn_haddr_eqb. cbn. intros h.
    apply Pos.eqb_eq in h. rewrite h. reflexivity.
  Qed.

  Lemma cbn_haddr_eqb_refl a : cbn_haddr_eqb a a = true.
  Proof. destruct a as [p]. unfold cbn_haddr_eqb. cbn. apply Pos.eqb_refl. Qed.

  Lemma cbn_gdom_addrs_in lo G s l :
    (forall a t, G a = Some t -> (lo <= cbn_ha_p a)%positive /\
      (cbn_ha_p a < s.(cbn_st_next))%positive) ->
    Forall (cbn_gdef G) l -> cbn_addrs_in lo s.(cbn_st_next) l.
  Proof.
    intros hd. induction 1 as [|b l hb hl ih]; constructor; [|exact ih].
    destruct hb as [t ht]. exact (hd _ _ ht).
  Qed.

  Lemma cbn_mok_memo K s s1 : s1.(cbn_st_memo) = s.(cbn_st_memo) -> cbn_mok K s -> cbn_mok K s1.
  Proof. intros he h. unfold cbn_mok, cbn_memo_inv, cbn_memo_ok in *. rewrite he. exact h. Qed.

  Lemma cbn_mok_widen K s : cbn_mok K s -> cbn_mok ((s.(cbn_st_memo)).(cbn_m_codes)) s.
  Proof.
    intros (h1 & h2 & _ & h4). split; [exact h1|]. split; [exact h2|].
    split; [intros i e hi; exact hi|exact h4].
  Qed.

  Lemma cbn_mok_once_body K c e s :
    cbn_mok K s -> PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
      cbn_code_inv e c ->
    cbn_mok K (snd (cbn_once_body c s)).
  Proof.
    intros (h1 & h2 & h3 & h4 & h5) hg hi.
    destruct (cbn_once_body_memo c s) as (q1 & _).
    split; [exact (cbn_memo_inv_once_body X_type X c e s h1 hg hi)|].
    split; [exact (cbn_memo_ok_codes X_type X s _ q1 h2)|].
    split; [intros i e' he'; rewrite q1; exact (h3 i e' he')|].
    split; [intros i e' he'; rewrite q1 in he'; exact (h4 i e' he')|].
    intros hc i e' he'. rewrite q1 in he'. exact (h5 hc i e' he').
  Qed.

  (** [cbn_delta] leaves the code table alone, or adds the body of [kn] at the next index. *)
  Lemma cbn_delta_codes kn ui s r s1 :
    cbn_delta_ok X_type X (s.(cbn_st_memo)) -> cbn_delta X_type X kn ui s = CbnCOk (r, s1) ->
    (s1.(cbn_st_memo)).(cbn_m_codes) = (s.(cbn_st_memo)).(cbn_m_codes)
    \/ exists cb body, abstract_env_lookup X kn = Some (ConstantDecl cb)
         /\ cb.(cst_body) = Some body
         /\ (s1.(cbn_st_memo)).(cbn_m_codes)
            = PTree.set ((s.(cbn_st_memo)).(cbn_m_ncode))
                (cbn_mkEntry body ui (cbn_wf_term_univs X_type X (cbn_inst_code ui body)))
                ((s.(cbn_st_memo)).(cbn_m_codes)).
  Proof.
    intros hd he.
    destruct (cbn_delta_cases X_type X kn ui s r s1 he)
      as [[-> _]|[(body & insts & hsrc & _ & ->)|(cb & _ & _ & _ & ->)]].
    - left. reflexivity.
    - right. destruct (cbn_delta_new_source X_type X kn _ body insts hd hsrc) as [[cb [hl hb]] _].
      exists cb, body. split; [exact hl|]. split; [exact hb|].
      rewrite cbn_delta_new_codes. apply cbn_new_entry_codes.
    - left. reflexivity.
  Qed.

  Lemma cbn_gok_same lo G s s1 :
    cbn_gok lo G s -> s1.(cbn_st_heap) = s.(cbn_st_heap) -> s1.(cbn_st_next) = s.(cbn_st_next) ->
    s1.(cbn_st_gam) = s.(cbn_st_gam) -> cbn_mok (cbn_gc G) s1 -> cbn_gok lo G s1.
  Proof.
    intros [h1 h2 h3 h4 h5 _ h7] e1 e2 e3 hd. split.
    - destruct h1 as [p1 p2 p3]. split.
      + rewrite e1, e2. exact p1.
      + intros a cl hc. rewrite e1 in hc. rewrite e2. exact (p2 _ _ hc).
      + intros k a hk. rewrite e3 in hk. rewrite e2. exact (p3 _ _ hk).
    - rewrite e1. exact h2.
    - intros a cl hc. unfold cbn_heap_get in hc. rewrite e1 in hc. exact (h3 _ _ hc).
    - intros a t ht. rewrite e2. exact (h4 _ _ ht).
    - intros j a hj. rewrite e3 in hj. exact (h5 _ _ hj).
    - exact hd.
    - exact h7.
  Qed.

  (** The same state shape, with the ghost's table replaced by a larger one. *)
  Lemma cbn_gok_recode lo G s s1 K :
    cbn_gok lo G s -> s1.(cbn_st_heap) = s.(cbn_st_heap) -> s1.(cbn_st_next) = s.(cbn_st_next) ->
    s1.(cbn_st_gam) = s.(cbn_st_gam) ->
    (forall i e, PTree.get i (cbn_gc G) = Some e -> PTree.get i K = Some e) ->
    cbn_mok K s1 -> cbn_gok lo (cbn_mkGhost (cbn_gm G) K) s1.
  Proof.
    intros hok e1 e2 e3 hK hm.
    assert (hx : cbn_gext G (cbn_mkGhost (cbn_gm G) K)) by
      (split; [intros a t h; exact h|exact hK]).
    destruct hok as [h1 h2 h3 h4 h5 _ h7]. split.
    - destruct h1 as [p1 p2 p3]. split.
      + rewrite e1, e2. exact p1.
      + intros a cl hc. rewrite e1 in hc. rewrite e2. exact (p2 _ _ hc).
      + intros k a hk. rewrite e3 in hk. rewrite e2. exact (p3 _ _ hk).
    - rewrite e1. exact h2.
    - intros a cl hc. unfold cbn_heap_get in hc. rewrite e1 in hc.
      destruct (h3 _ _ hc) as [t [ht hr]]. exists t. split; [exact ht|].
      destruct hr as [hb|[u [hu hred]]]; [left; exact hb|].
      right. exists u. split; [exact (cbn_g_cell_mono _ _ hx _ _ hu)|exact hred].
    - intros a t ht. rewrite e2. exact (h4 _ _ ht).
    - intros j a hj. rewrite e3 in hj. exact (h5 _ _ hj).
    - exact hm.
    - exact h7.
  Qed.

  Lemma cbn_delta_gok lo G kn ui s r s1 :
    cbn_gok lo G s -> cbn_delta X_type X kn ui s = CbnCOk (r, s1) -> cbn_gok lo G s1.
  Proof.
    intros hok hd. destruct (cbn_delta_shape _ _ _ _ _ hd) as (e1 & e2 & _ & _ & e5).
    destruct (cbn_gk_memo _ _ _ hok) as (hmi & hmo & hcodes & hokb & hhyg).
    pose proof hmi as (hf & _ & _ & _ & hdo).
    apply (cbn_gok_same lo G s); [exact hok|exact e1|exact e2|exact e5|].
    split; [exact (cbn_memo_inv_delta X_type X kn ui s r s1 hmi hd)|].
    split; [exact (cbn_delta_memo_ok X_type X kn ui s r s1 hmo hd)|].
    destruct (cbn_delta_codes kn ui s r s1 hdo hd) as [hc|(cb & body & hl & hb & hc)];
      rewrite hc.
    - split; [exact hcodes|]. split; [exact hokb|exact hhyg].
    - split.
      + intros i e hi. exact (cbn_memo_add_entry_codes_mono _ _ hf i e (hcodes i e hi)).
      + split.
        * intros i e hi.
          destruct (cbn_key_eqb i ((s.(cbn_st_memo)).(cbn_m_ncode))) eqn:E.
          -- apply cbn_key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
             injection hi as <-. cbn [cbn_ce_inst cbn_ce_term].
             pose proof (cbn_lookup_declared X_type X Σ kn cb hΣ hl) as hdecl.
             rewrite (cbn_consts_inst_code Σ ui body).
             exact (cbn_declared_constant_consts_okb Σ kn cb body wfΣ hdecl hb).
          -- rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E). exact (hokb i e hi).
        * intros hcx i e hi.
          destruct (cbn_key_eqb i ((s.(cbn_st_memo)).(cbn_m_ncode))) eqn:E.
          -- apply cbn_key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
             injection hi as <-. cbn [cbn_ce_inst cbn_ce_term].
             pose proof (cbn_lookup_declared X_type X Σ kn cb hΣ hl) as hdecl.
             rewrite cbn_hyg_inst_code.
             pose proof (declared_constant_closed_body Σ kn cb body wfΣ hdecl hb) as hcl.
             eapply on_free_vars_impl; [|exact (closedn_on_free_vars (P := cbn_xpredT) hcl)].
             intros; reflexivity.
          -- rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E). exact (hhyg hcx i e hi).
  Qed.

  (** Satisfying instance of the state invariant [cbn_gok], the premise of [cbn_machine_sound]: the
    machine's initial state has it, with the empty ghost. A call adds its input codes to the
    table with [cbn_new_entry] before it starts. *)
  Lemma cbn_gok_init : cbn_gok xH (cbn_mkGhost (fun _ => None) (PTree.empty _)) cbn_init.
  Proof.
    split.
    - apply cbn_state_ok_init.
    - intros a a' h. unfold cbn_init in h. cbn [cbn_st_heap] in h.
      rewrite cbn_bh_get_holes in h. discriminate.
    - intros a cl h. unfold cbn_heap_get, cbn_init in h. cbn [cbn_st_heap] in h.
      rewrite cbn_bh_get_holes in h. discriminate.
    - intros a t h. discriminate h.
    - intros j a h. unfold cbn_init in h. cbn [cbn_st_gam] in h.
      rewrite PTree.gempty in h. discriminate.
    - split; [apply cbn_memo_inv_init|]. split; [apply cbn_memo_ok_init|]. split.
      + intros i e h. cbn [cbn_gc] in h. rewrite PTree.gempty in h. discriminate.
      + split.
        * intros i e h. unfold cbn_init, cbn_memo_empty in h. cbn [cbn_st_memo cbn_m_codes] in h.
          rewrite PTree.gempty in h. discriminate.
        * intros _ i e h. unfold cbn_init, cbn_memo_empty in h. cbn [cbn_st_memo cbn_m_codes] in h.
          rewrite PTree.gempty in h. discriminate.
    - intros _ a t h. discriminate h.
  Qed.

  (** *** The context map *)

  Lemma cbn_ctx_den_red j t : cbn_ctx_den Γ nctx lvl j = Some t ->
    cbn_cred (tRel (lvl - nctx + j)) t.
  Proof.
    unfold cbn_ctx_den. destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
    destruct decl.(decl_body) as [b|] eqn:eb; intros h; injection h as <-.
    - apply cbn_cred_one.
      assert (hn : nth_error (Γ ,,, Δ) (lvl - nctx + j) = Some decl).
      { unfold app_context. rewrite nth_error_app_ge; [|lia].
        replace (lvl - nctx + j - #|Δ|) with j by lia. exact ed. }
      pose proof (red_rel Σ cbn_ΓΔ (lvl - nctx + j) b) as hr.
      replace (lvl - nctx + S j) with (S (lvl - nctx + j)) by lia.
      apply hr. rewrite hn. cbn. rewrite eb. reflexivity.
    - apply nth_error_Some_length in ed.
      replace (lvl - S (nctx - S j)) with (lvl - nctx + j) by lia.
      apply cbn_cred_refl.
  Qed.

  (** *** The write-back

    Forcing a cell marks it [CbnCBusy], evaluates, then writes the value back. Because the
    ghost map [G] is unchanged, the cell at [a] still stands for a reduct of [G a] after each
    write: [CbnCBusy] trivially (it stands for nothing), and [CbnCDone v] because [v] is a reduct
    of the cell's reading which is a reduct of [G a]. *)

  Lemma cbn_gok_heap_upd_busy lo G a s s' :
    cbn_gok lo G s -> cbn_heap_upd a CbnCBusy s = Some s' -> cbn_gok lo G s'.
  Proof.
    intros hok he.
    destruct (cbn_heap_upd_shape _ _ _ _ he) as (he1 & he2 & he3 & he4 & he5 & hu).
    split.
    - apply (cbn_heap_upd_state_ok lo a CbnCBusy s s' (cbn_gk_state _ _ _ hok));
      [cbn; constructor|exact he].
    - apply (cbn_heap_nofwd_heap_upd a CbnCBusy s s' (cbn_gk_nofwd _ _ _ hok));
        [intros b; discriminate|exact he].
    - intros b cl hb. unfold cbn_heap_get in hb.
      destruct (cbn_haddr_dec b a) as [->|hne].
      + rewrite (cbn_bh_get_upd_same _ _ _ _ hu) in hb. inversion hb; subst cl.
        assert (ha_in : exists cl0, cbn_bh_get a s.(cbn_st_heap) = Some cl0).
        { destruct (cbn_bh_get a s.(cbn_st_heap)) eqn:E; [eexists; reflexivity|].
          exfalso. apply (proj2 (cbn_bh_upd_none a CbnCBusy s.(cbn_st_heap))) in E.
          rewrite E in hu; discriminate. }
        destruct ha_in as [cl0 h0].
        destruct (cbn_gk_cells _ _ _ hok a cl0 h0) as [t [hGa _]].
        exists t. split; [exact hGa|left; reflexivity].
      + rewrite (cbn_bh_get_upd_other _ _ _ _ _ hu hne) in hb.
        exact (cbn_gk_cells _ _ _ hok b cl hb).
    - intros b t ht. rewrite he1. exact (cbn_gk_dom _ _ _ hok b t ht).
    - intros j b hj. rewrite he4 in hj. exact (cbn_gk_gam _ _ _ hok j b hj).
    - exact (cbn_mok_memo _ s s' he5 (cbn_gk_memo _ _ _ hok)).
    - exact (cbn_gk_hyg _ _ _ hok).
  Qed.

  Lemma cbn_gok_heap_upd_done lo G a v u t s s' :
    cbn_gok lo G s -> G a = Some t -> cbn_g_value G v u -> cbn_cred t u ->
    cbn_heap_upd a (CbnCDone v) s = Some s' -> cbn_gok lo G s'.
  Proof.
    intros hok hGa hv hred he.
    destruct (cbn_heap_upd_shape _ _ _ _ he) as (he1 & he2 & he3 & he4 & he5 & hu).
    split.
    - apply (cbn_heap_upd_state_ok lo a (CbnCDone v) s s' (cbn_gk_state _ _ _ hok)); [|exact he].
      cbn [cbn_ad_cell]. apply (cbn_gdom_addrs_in lo G s); [exact (cbn_gk_dom _ _ _ hok)|].
      exact (cbn_g_value_ad G v u hv).
    - apply (cbn_heap_nofwd_heap_upd a (CbnCDone v) s s' (cbn_gk_nofwd _ _ _ hok));
        [intros b; discriminate|exact he].
    - intros b cl hb. unfold cbn_heap_get in hb.
      destruct (cbn_haddr_dec b a) as [->|hne].
      + rewrite (cbn_bh_get_upd_same _ _ _ _ hu) in hb. inversion hb; subst cl.
        exists t. split; [exact hGa|].
        right. exists u. split; [constructor; exact hv|exact hred].
      + rewrite (cbn_bh_get_upd_other _ _ _ _ _ hu hne) in hb.
        exact (cbn_gk_cells _ _ _ hok b cl hb).
    - intros b t0 ht0. rewrite he1. exact (cbn_gk_dom _ _ _ hok b t0 ht0).
    - intros j b hj. rewrite he4 in hj. exact (cbn_gk_gam _ _ _ hok j b hj).
    - exact (cbn_mok_memo _ s s' he5 (cbn_gk_memo _ _ _ hok)).
    - exact (cbn_gk_hyg _ _ _ hok).
  Qed.

  (** *** Inversions of the ghost value reading, by case on the value shape *)

  Lemma cbn_g_value_VCon_inv G h sp t :
    cbn_g_value G (CbnVCon h sp) t -> exists ts, t = mkApps h ts /\ cbn_g_addrs G sp ts.
  Proof. intros hv; inversion hv; subst; eexists; split; [reflexivity|eassumption]. Qed.

  Lemma cbn_g_value_VLam_inv G e c t :
    cbn_g_value G (CbnVLam e c) t -> cbn_g_susp G e c.(cbn_c_term) t.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma cbn_g_value_VOpen_inv G e c t :
    cbn_g_value G (CbnVOpen e c) t -> cbn_g_susp G e c.(cbn_c_term) t.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma cbn_g_value_VNeu_inv G nn sp t :
    cbn_g_value G (CbnVNeu nn sp) t ->
    (exists l ts, nn = CbnNVar l /\ t = mkApps (tRel (lvl - S l)) ts /\ cbn_g_addrs G sp ts)
    \/ (exists h ts, nn = CbnNConst h /\ t = mkApps h ts /\ cbn_g_addrs G sp ts).
  Proof.
    intros hv; inversion hv; subst.
    - left. eexists; eexists; split; [reflexivity|split; [reflexivity|eassumption]].
    - right. eexists; eexists; split; [reflexivity|split; [reflexivity|eassumption]].
  Qed.

  Lemma cbn_g_value_VStuck_inv G e c sp t :
    cbn_g_value G (CbnVStuck e c sp) t ->
    exists h ts, cbn_g_susp G e c.(cbn_c_term) h /\ cbn_g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    eexists; eexists; split; [eassumption|split; [eassumption|reflexivity]].
  Qed.

  Lemma cbn_g_value_VFix_inv G e c i sp t :
    cbn_g_value G (CbnVFix e c i sp) t ->
    exists mfix idx h ts, c.(cbn_c_term) = tFix mfix idx /\ cbn_g_susp G e (tFix mfix i) h
      /\ cbn_cok G c /\ cbn_g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    do 4 eexists; repeat split; first [eassumption|reflexivity].
  Qed.

  Lemma cbn_g_value_VStuckFix_inv G e c i sp t :
    cbn_g_value G (CbnVStuckFix e c i sp) t ->
    exists mfix idx h ts, c.(cbn_c_term) = tFix mfix idx /\ cbn_g_susp G e (tFix mfix i) h
      /\ cbn_cok G c /\ cbn_g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    do 4 eexists; repeat split; first [eassumption|reflexivity].
  Qed.

  (** The reading of any code through an environment whose slots are read. *)
  Lemma cbn_g_susp_of_slots G e t ts :
    cbn_g_slots G e.(cbn_ev_vals) ts -> e.(cbn_ev_nvals) = #|e.(cbn_ev_vals)| ->
    cbn_g_susp G e t (subst ts 0 (lift (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals) t)).
  Proof.
    destruct e as [vals nvals goff]; cbn; intros h1 h2; subst nvals.
    constructor; [exact h1|reflexivity].
  Qed.

  Lemma cbn_g_slot_addr_inv G a t : cbn_g_slot G (CbnSAddr a) t -> G a = Some t.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma cbn_g_slot_inl_inv G vs n o c t :
    cbn_g_slot G (CbnSInl vs n o c) t -> cbn_g_susp G (cbn_mkEnv vs n o) c.(cbn_c_term) t.
  Proof. intros h; inversion h; subst; econstructor; eauto. Qed.

  Lemma cbn_g_cell_susp_inv G vs n o c u :
    cbn_g_cell G (CbnCSusp vs n o c) u -> cbn_g_susp G (cbn_mkEnv vs n o) c.(cbn_c_term) u.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma cbn_g_cell_done_inv G v u : cbn_g_cell G (CbnCDone v) u -> cbn_g_value G v u.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma cbn_g_value_VLam_cok G e c t : cbn_g_value G (CbnVLam e c) t -> cbn_cok G c.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma cbn_g_value_VStuck_cok G e c sp t : cbn_g_value G (CbnVStuck e c sp) t -> cbn_cok G c.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma cbn_g_slot_inl_cok G vs n o c t : cbn_g_slot G (CbnSInl vs n o c) t -> cbn_cok G c.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma cbn_g_cell_susp_cok G vs n o c u : cbn_g_cell G (CbnCSusp vs n o c) u -> cbn_cok G c.
  Proof. intros h; inversion h; subst; assumption. Qed.

  (** *** The congruences of reduction the new rules need *)

  Lemma cbn_cred_case_c ci p c c' brs : cbn_cred c c' ->
    cbn_cred (tCase ci p c brs) (tCase ci p c' brs).
  Proof. intros [h]. constructor. exact (red_case_c _ _ _ _ _ h). Qed.

  Lemma cbn_cred_proj_c pr c c' : cbn_cred c c' -> cbn_cred (tProj pr c) (tProj pr c').
  Proof. intros [h]. constructor. exact (red_proj_c _ _ _ h). Qed.

  Lemma cbn_cred_mkApps_list_set f l n t u :
    nth_error l n = Some t -> cbn_cred t u -> cbn_cred (mkApps f l) (mkApps f (cbn_list_set l n u)).
  Proof.
    intros hn [h]. constructor. apply red_mkApps; [apply refl_red|].
    exact (cbn_All2_red_list_set Σ cbn_ΓΔ l n t u hn h).
  Qed.

  (** ** What a call does to the structures its caller holds

    A call may collect, and a collection renames every address. So a call does not promise
    that the roots come back unchanged or that the ghost map only grows. It promises
    [cbn_gren G G' rs rs']: the code table only grows ([cbn_gcx]), and every root comes back as a
    root of the same shape that stands, under the new ghost [G'], for what the old root stood for
    under [G] ([cbn_gpres], one clause per shape of root).
    Without a collection the roots come back as they went in and [G'] extends [G]
    ([cbn_gren_ext]); a collection renames them ([cbn_collect_ghost]). *)

  Definition cbn_gcx (G G' : cbn_ghost) : Prop :=
    forall i e, PTree.get i (cbn_gc G) = Some e -> PTree.get i (cbn_gc G') = Some e.

  (** An environment keeps its counts and its slots keep their readings. *)
  Definition cbn_genv (G G' : cbn_ghost) (e e' : cbn_env) : Prop :=
    e'.(cbn_ev_nvals) = e.(cbn_ev_nvals) /\ e'.(cbn_ev_goff) = e.(cbn_ev_goff)
    /\ forall ts, cbn_g_slots G e.(cbn_ev_vals) ts -> cbn_g_slots G' e'.(cbn_ev_vals) ts.

  Definition cbn_gpres (G G' : cbn_ghost) (r r' : cbn_root) : Prop :=
    match r, r' with
    | CbnRA a, CbnRA a' => forall t, G a = Some t -> G' a' = Some t
    | CbnRSl x, CbnRSl x' => forall t, cbn_g_slot G x t -> cbn_g_slot G' x' t
    | CbnRE e, CbnRE e' => cbn_genv G G' e e'
    | CbnRV v, CbnRV v' => forall t, cbn_g_value G v t -> cbn_g_value G' v' t
    | CbnRSk l, CbnRSk l' => forall ts, cbn_g_slots G l ts -> cbn_g_slots G' l' ts
    | CbnRSp l, CbnRSp l' => forall ts, cbn_g_addrs G l ts -> cbn_g_addrs G' l' ts
    | CbnRC cl, CbnRC cl' => forall t, cbn_g_cell G cl t -> cbn_g_cell G' cl' t
    | _, _ => False
    end.

  Definition cbn_gren (G G' : cbn_ghost) (rs rs' : list cbn_root) : Prop :=
    cbn_gcx G G' /\ Forall2 (cbn_gpres G G') rs rs'.

  Lemma cbn_cok_gcx G G' (h : cbn_gcx G G') c : cbn_cok G c -> cbn_cok G' c.
  Proof. intros [e [he hi]]. exists e. split; [exact (h _ _ he)|exact hi]. Qed.

  Lemma cbn_cok_eqc G G' c : cbn_gc G' = cbn_gc G -> cbn_cok G c -> cbn_cok G' c.
  Proof. intros he [e [h1 h2]]. exists e. rewrite he. split; assumption. Qed.

  Lemma cbn_genv_trans G1 G2 G3 e1 e2 e3 :
    cbn_genv G1 G2 e1 e2 -> cbn_genv G2 G3 e2 e3 -> cbn_genv G1 G3 e1 e3.
  Proof.
    intros (a1 & b1 & c1) (a2 & b2 & c2). split; [congruence|]. split; [congruence|].
    intros ts h. exact (c2 _ (c1 _ h)).
  Qed.

  Lemma cbn_genv_ext_r G G1 G2 e e' : cbn_genv G G1 e e' -> cbn_gext G1 G2 -> cbn_genv G G2 e e'.
  Proof.
    intros (a & b & c) hx. split; [exact a|]. split; [exact b|].
    intros ts h. exact (cbn_g_slots_mono _ _ hx _ _ (c _ h)).
  Qed.

  Lemma cbn_genv_susp G G' e e' t u : cbn_genv G G' e e' -> cbn_g_susp G e t u ->
    cbn_g_susp G' e' t u.
  Proof.
    intros (h1 & h2 & h3) hs. destruct (cbn_g_susp_inv _ _ _ _ hs) as (ts & hts & hnv & ->).
    rewrite <- h1, <- h2. apply cbn_g_susp_of_slots; [exact (h3 _ hts)|].
    rewrite h1, hnv, <- (cbn_g_slots_length _ _ _ hts), (cbn_g_slots_length _ _ _ (h3 _ hts)).
    reflexivity.
  Qed.

  Lemma cbn_gpres_ext G G' (h : cbn_gext G G') r : cbn_gpres G G' r r.
  Proof.
    destruct r; cbn [cbn_gpres].
    - intros t ht. exact (h _ _ ht).
    - intros t ht. exact (cbn_g_slot_mono _ _ h _ _ ht).
    - split; [reflexivity|]. split; [reflexivity|].
      intros ts ht. exact (cbn_g_slots_mono _ _ h _ _ ht).
    - intros t ht. exact (cbn_g_value_mono _ _ h _ _ ht).
    - intros ts ht. exact (cbn_g_slots_mono _ _ h _ _ ht).
    - intros ts ht. exact (cbn_g_addrs_mono _ _ h _ _ ht).
    - intros t ht. exact (cbn_g_cell_mono _ _ h _ _ ht).
  Qed.

  Lemma cbn_gpres_trans G1 G2 G3 r1 r2 r3 :
    cbn_gpres G1 G2 r1 r2 -> cbn_gpres G2 G3 r2 r3 -> cbn_gpres G1 G3 r1 r3.
  Proof.
    intros h1 h2.
    destruct r1, r2; cbn [cbn_gpres] in h1; try contradiction;
      destruct r3; cbn [cbn_gpres] in h2 |- *; try contradiction.
    all: first [ exact (cbn_genv_trans _ _ _ _ _ _ h1 h2)
               | let hx := fresh "hx" in intros ? hx; exact (h2 _ (h1 _ hx)) ].
  Qed.

  Lemma cbn_gpres_r_ext G G1 G2 r r' : cbn_gpres G G1 r r' -> cbn_gext G1 G2 -> cbn_gpres G G2 r r'.
  Proof. intros h hx. exact (cbn_gpres_trans _ _ _ _ _ _ h (cbn_gpres_ext _ _ hx r')). Qed.

  Lemma cbn_Forall2_gpres_r_ext G G1 G2 l l' :
    Forall2 (cbn_gpres G G1) l l' -> cbn_gext G1 G2 -> Forall2 (cbn_gpres G G2) l l'.
  Proof.
    intros h hx. induction h as [|r r' l l' hp hl ih]; constructor;
      [exact (cbn_gpres_r_ext _ _ _ _ _ hp hx)|exact ih].
  Qed.

  Lemma cbn_gren_ext G G' rs : cbn_gext G G' -> cbn_gren G G' rs rs.
  Proof.
    intros h. split; [exact (cbn_gx_codes h)|].
    induction rs as [|r rs ih]; constructor; [exact (cbn_gpres_ext _ _ h r)|exact ih].
  Qed.

  Lemma cbn_gren_refl G rs : cbn_gren G G rs rs.
  Proof. exact (cbn_gren_ext G G rs (cbn_gext_refl G)). Qed.

  Lemma cbn_gren_trans G1 G2 G3 rs1 rs2 rs3 :
    cbn_gren G1 G2 rs1 rs2 -> cbn_gren G2 G3 rs2 rs3 -> cbn_gren G1 G3 rs1 rs3.
  Proof.
    intros [hc1 hf1] [hc2 hf2]. split; [intros i e hi; exact (hc2 _ _ (hc1 _ _ hi))|].
    revert rs3 hf2. induction hf1 as [|r1 r2 l1 l2 hp hl ih]; intros rs3 hf2.
    - inversion hf2; subst. constructor.
    - inversion hf2 as [|r2' r3 l2' l3 hp2 hl2]; subst. constructor.
      + exact (cbn_gpres_trans _ _ _ _ _ _ hp hp2).
      + exact (ih _ hl2).
  Qed.

  Lemma cbn_gren_cons G G' r rs r' rs' :
    cbn_gren G G' (r :: rs) (r' :: rs') -> cbn_gpres G G' r r' /\ cbn_gren G G' rs rs'.
  Proof. intros [hc hf]. inversion hf; subst. split; [assumption|split; assumption]. Qed.

  Lemma cbn_gren_cok G G' rs rs' c : cbn_gren G G' rs rs' -> cbn_cok G c -> cbn_cok G' c.
  Proof. intros [hc _]. exact (cbn_cok_gcx _ _ hc c). Qed.

  (** ** A collection, against the ghost map

    The collector's walk ([cbn_gc_copy]) is followed with a second ghost [Gn] for the new heap,
    built as the walk goes: when the cell at old address [a] is copied to the new address
    [cbn_g_next], [Gn] is extended at that fresh address by [G a]. So nothing about the map the
    collector builds needs to be recovered afterwards, and no injectivity is needed: every
    forwarding pointer [a ↦ b] of the old heap has [Gn b = G a] ([cbn_gg_fwd]), which is all
    the renaming of a reading looks at, and every cell of the new heap is the renaming of
    the old cell it was copied from, so it stands for what that cell stood for
    ([cbn_gg_cells]). A [CbnCBusy] cell is copied as [CbnCBusy]. *)

  Section GhostCollect.
    Context (lo : positive) (G : cbn_ghost) (s : cbn_state) (hok : cbn_gok lo G s).

    Record cbn_gcg (Gn : cbn_ghost) (g : cbn_gc_state) : Prop := cbn_mkGcg {
      cbn_gg_inv : cbn_gc_inv s.(cbn_st_heap) s.(cbn_st_next) g;
      cbn_gg_codes : cbn_gc Gn = cbn_gc G;
      cbn_gg_fwd : forall x b t, cbn_bh_get x g.(cbn_g_old) = Some (CbnCFwd b) -> G x = Some t ->
        Gn b = Some t;
      cbn_gg_cells : forall b cl, cbn_bh_get b g.(cbn_g_heap) = Some cl ->
        exists t, Gn b = Some t /\ (cl = CbnCBusy \/ exists u, cbn_g_cell Gn cl u /\ cbn_cred t u);
      cbn_gg_dom : forall b t, Gn b = Some t ->
        (s.(cbn_st_next) <= cbn_ha_p b)%positive /\ (cbn_ha_p b < g.(cbn_g_next))%positive;
      cbn_gg_rng : forall b t, Gn b = Some t -> exists x, G x = Some t }.

    (** What the walk asks of the address map it threads through the renamings. *)
    #[local] Definition cbn_cpg (cp : cbn_haddr -> cbn_gc_state ->
      cbn_res (cbn_haddr * cbn_gc_state)) : Prop :=
      forall a g a' g' Gn, cbn_gcg Gn g -> cp a g = CbnCOk (a', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\
          (forall t, G a = Some t -> Gn' a' = Some t).

    Section Walk.
      Context (cp : cbn_haddr -> cbn_gc_state -> cbn_res (cbn_haddr * cbn_gc_state))
        (hcp : cbn_cpg cp).

      Lemma cbn_rn_addrs_g : forall l g l' g' Gn, cbn_gcg Gn g ->
        cbn_rn_addrs cp l g = CbnCOk (l', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn'
          /\ (forall ts, cbn_g_addrs G l ts -> cbn_g_addrs Gn' l' ts).
      Proof.
        induction l as [|a l ih]; intros g l' g' Gn hg he; simpl in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
          intros ts h. inversion h; subst. constructor.
        - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_addrs cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          destruct (ih _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hl2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros ts h. inversion h as [|a0 t l0 ts0 hat hl]; subst.
          constructor; [exact (hx2 _ _ (ha1 _ hat))|exact (hl2 _ hl)].
      Qed.

      Lemma cbn_rn_slot_g : forall x g x' g' Gn, cbn_gcg Gn g ->
        cbn_rn_slot cp x g = CbnCOk (x', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\
          (forall t, cbn_g_slot G x t -> cbn_g_slot Gn' x' t).
      Proof.
        intros x. induction x as [a|vs n o c ihvs] using cbn_slot_ind'; intros g x' g' Gn hg he.
        - simpl in he. destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          intros t h. constructor. exact (ha1 _ (cbn_g_slot_addr_inv _ _ _ h)).
        - rewrite cbn_rn_slot_SInl in he.
          destruct (cbn_rn_slots cp vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          assert (hl : exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn'
                    /\ (forall ts, cbn_g_slots G vs ts -> cbn_g_slots Gn' vs' ts)).
          { revert g vs' g' Gn hg e1.
            induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 Gn hg e1; simpl in e1.
            - inversion e1; subst; clear e1.
              exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
              intros ts h. inversion h; subst. constructor.
            - destruct (cbn_rn_slot cp y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
              destruct (cbn_rn_slots cp vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
              inversion e1; subst; clear e1.
              destruct (hy _ _ _ _ hg ea) as (Gna & hga & hxa & hra).
              destruct (ihl _ _ _ _ hga eb) as (Gnb & hgb & hxb & hrb).
              exists Gnb. split; [exact hgb|]. split; [exact (cbn_gext_trans _ _ _ hxa hxb)|].
              intros ts h. inversion h as [|y0 l0 t ts0 hy1 hl1]; subst.
              constructor; [exact (cbn_g_slot_mono _ _ hxb _ _ (hra _ hy1))|exact (hrb _ hl1)]. }
          destruct hl as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h as [|vals nvals goff c0 ts hts hnv hcok]; subst.
          rewrite <- (cbn_rn_slots_length _ _ _ _ _ e1).
          apply cbn_g_slot_inl; [exact (hr _ hts)|reflexivity|].
          exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg') hcok).
      Qed.

      Lemma cbn_rn_slots_g : forall l g l' g' Gn, cbn_gcg Gn g ->
        cbn_rn_slots cp l g = CbnCOk (l', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn'
          /\ (forall ts, cbn_g_slots G l ts -> cbn_g_slots Gn' l' ts).
      Proof.
        induction l as [|y l ih]; intros g l' g' Gn hg he; simpl in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
          intros ts h. inversion h; subst. constructor.
        - destruct (cbn_rn_slot cp y g) as [[y' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_slots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_slot_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (ih _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros ts h. inversion h as [|y0 l0 t ts0 hy1 hl1]; subst.
          constructor; [exact (cbn_g_slot_mono _ _ hx2 _ _ (hr1 _ hy1))|exact (hr2 _ hl1)].
      Qed.

      Lemma cbn_rn_env_g e g e' g' Gn : cbn_gcg Gn g -> cbn_rn_env cp e g = CbnCOk (e', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\ cbn_genv G Gn' e e'.
      Proof.
        destruct e as [vals n o]. intros hg he.
        unfold cbn_rn_env in he. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff] in he.
        destruct (cbn_rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (cbn_rn_slots_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
        exists Gn'. split; [exact hg'|]. split; [exact hx'|].
        split; [reflexivity|]. split; [reflexivity|]. exact hr.
      Qed.

      Lemma cbn_rn_value_g v g v' g' Gn : cbn_gcg Gn g -> cbn_rn_value cp v g = CbnCOk (v', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\
          (forall t, cbn_g_value G v t -> cbn_g_value Gn' v' t).
      Proof.
        destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; intros hg he;
          unfold cbn_rn_value in he.
        - (* CbnVCon *)
          destruct (cbn_rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_addrs_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst. constructor. apply hr. assumption.
        - (* CbnVLam *)
          destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_env_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst. constructor.
          + exact (cbn_genv_susp _ _ _ _ _ _ hr ltac:(eassumption)).
          + exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg') ltac:(eassumption)).
        - (* CbnVFix *)
          destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_env_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (cbn_rn_addrs_g _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros t h. inversion h; subst.
          eapply cbn_g_VFix; [eassumption| | |apply hr2; assumption].
          + exact (cbn_genv_susp _ _ _ _ _ _ (cbn_genv_ext_r _ _ _ _ _ hr1 hx2) ltac:(eassumption)).
          + exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg2) ltac:(eassumption)).
        - (* CbnVStuckFix *)
          destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_env_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (cbn_rn_addrs_g _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros t h. inversion h; subst.
          eapply cbn_g_VStuckFix; [eassumption| | |apply hr2; assumption].
          + exact (cbn_genv_susp _ _ _ _ _ _ (cbn_genv_ext_r _ _ _ _ _ hr1 hx2) ltac:(eassumption)).
          + exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg2) ltac:(eassumption)).
        - (* CbnVNeu *)
          destruct (cbn_rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_addrs_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst; constructor; apply hr; assumption.
        - (* CbnVOpen *)
          destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_env_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst. constructor.
          + exact (cbn_genv_susp _ _ _ _ _ _ hr ltac:(eassumption)).
          + exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg') ltac:(eassumption)).
        - (* CbnVStuck *)
          destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_env_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (cbn_rn_addrs_g _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros t h. inversion h; subst.
          eapply cbn_g_VStuck; [| |apply hr2; assumption].
          + exact (cbn_genv_susp _ _ _ _ _ _ (cbn_genv_ext_r _ _ _ _ _ hr1 hx2) ltac:(eassumption)).
          + exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg2) ltac:(eassumption)).
      Qed.

      Lemma cbn_rn_cell_g cl g cl' g' Gn : cbn_gcg Gn g -> cbn_rn_cell cp cl g = CbnCOk (cl', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\ (cl = CbnCBusy -> cl' = CbnCBusy)
          /\ (forall t, cbn_g_cell G cl t -> cbn_g_cell Gn' cl' t).
      Proof.
        destruct cl as [vals n o c|v| |b]; intros hg he; unfold cbn_rn_cell in he.
        - destruct (cbn_rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_slots_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          split; [intros hb; discriminate hb|].
          intros t h. pose proof (cbn_g_cell_susp_inv _ _ _ _ _ _ h) as hs.
          pose proof (cbn_g_cell_susp_cok _ _ _ _ _ _ h) as hc.
          constructor.
          + refine (cbn_genv_susp G Gn' (cbn_mkEnv vals n o) (cbn_mkEnv vs' n o) _ _ _ hs).
            split; [reflexivity|]. split; [reflexivity|]. exact hr.
          + exact (cbn_cok_eqc _ _ _ (cbn_gg_codes _ _ hg') hc).
        - destruct (cbn_rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_value_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          split; [intros hb; discriminate hb|].
          intros t h. constructor. exact (hr _ (cbn_g_cell_done_inv _ _ _ h)).
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
          split; [reflexivity|]. intros t h. inversion h.
        - destruct (cp b g) as [[b' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & _).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          split; [intros hb; discriminate hb|]. intros t h. inversion h.
      Qed.

      Lemma cbn_rn_root_g r g r' g' Gn : cbn_gcg Gn g -> cbn_rn_root cp r g = CbnCOk (r', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\ cbn_gpres G Gn' r r'.
      Proof.
        destruct r as [a|x|e|v|l|l|cl]; intros hg he; unfold cbn_rn_root in he.
        - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|]. exact ha1.
        - destruct (cbn_rn_slot cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_slot_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (cbn_rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_env_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (cbn_rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_value_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (cbn_rn_slots cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_slots_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (cbn_rn_addrs cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_addrs_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (cbn_rn_cell cp cl g) as [[cl' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_cell_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & _ & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
      Qed.

      Lemma cbn_rn_roots_g : forall l g l' g' Gn, cbn_gcg Gn g ->
        cbn_rn_roots cp l g = CbnCOk (l', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn' /\ Forall2 (cbn_gpres G Gn') l l'.
      Proof.
        induction l as [|r l ih]; intros g l' g' Gn hg he; simpl in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|]. constructor.
        - destruct (cbn_rn_root cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_roots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_root_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hp1).
          destruct (ih _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hp2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          constructor; [exact (cbn_gpres_r_ext _ _ _ _ _ hp1 hx2)|exact hp2].
      Qed.

      Lemma cbn_rn_tree'_g : forall m g m' g' Gn, cbn_gcg Gn g ->
        cbn_rn_tree' cp m g = CbnCOk (m', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn'
          /\ (forall p a', PTree.get' p m' = Some a' ->
                exists a, PTree.get' p m = Some a
                  /\ (forall t, G a = Some t -> Gn' a' = Some t)).
      Proof.
        induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
          intros g m' g' Gn hg he; simpl in he.
        - (* Node001 *)
          destruct (cbn_rn_tree' cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihr _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          exact (hr1 _ _ hb).
        - (* Node010 *)
          destruct (cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          injection hb as <-. exists x. split; [reflexivity|exact ha1].
        - (* Node011 *)
          destruct (cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          destruct (ihr _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          + exact (hr2 _ _ hb).
          + injection hb as <-. exists x. split; [reflexivity|].
            intros t ht. exact (hx2 _ _ (ha1 _ ht)).
        - (* Node100 *)
          destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          exact (hr1 _ _ hb).
        - (* Node101 *)
          destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          destruct (cbn_rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (ihr _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          + exact (hr2 _ _ hb).
          + destruct (hr1 _ _ hb) as [a [ha hr]]. exists a. split; [exact ha|].
            intros t ht. exact (hx2 _ _ (hr _ ht)).
        - (* Node110 *)
          destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (hcp _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & ha2).
          exists Gn2. split; [exact hg2|]. split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          + destruct (hr1 _ _ hb) as [a [ha hr]]. exists a. split; [exact ha|].
            intros t ht. exact (hx2 _ _ (hr _ ht)).
          + injection hb as <-. exists x. split; [reflexivity|exact ha2].
        - (* Node111 *)
          destruct (cbn_rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
          destruct (cbn_rn_tree' cp r g2) as [[r' g3]|w] eqn:e3; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (hcp _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & ha2).
          destruct (ihr _ _ _ _ hg2 e3) as (Gn3 & hg3 & hx3 & hr3).
          exists Gn3. split; [exact hg3|].
          split; [exact (cbn_gext_trans _ _ _ hx1 (cbn_gext_trans _ _ _ hx2 hx3))|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *.
          + exact (hr3 _ _ hb).
          + destruct (hr1 _ _ hb) as [a [ha hr]]. exists a. split; [exact ha|].
            intros t ht. exact (hx3 _ _ (hx2 _ _ (hr _ ht))).
          + injection hb as <-. exists x. split; [reflexivity|].
            intros t ht. exact (hx3 _ _ (ha2 _ ht)).
      Qed.

      Lemma cbn_rn_ptree_g m g m' g' Gn : cbn_gcg Gn g -> cbn_rn_ptree cp m g = CbnCOk (m', g') ->
        exists Gn', cbn_gcg Gn' g' /\ cbn_gext Gn Gn'
          /\ (forall p a', PTree.get p m' = Some a' ->
                exists a, PTree.get p m = Some a
                  /\ (forall t, G a = Some t -> Gn' a' = Some t)).
      Proof.
        destruct m as [|m]; intros hg he; unfold cbn_rn_ptree in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
          intros p b hb. discriminate hb.
        - destruct (cbn_rn_tree' cp m g) as [[m2 g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (cbn_rn_tree'_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros p b hb. exact (hr p b hb).
      Qed.
    End Walk.

    (** One copied cell: its children are renamed, the copy goes to the fresh address
      [cbn_g_next], and the ghost of the new heap is extended there by the old ghost term. *)
    Lemma cbn_gc_copy_g_write k a g cl cl1 g1 old Gn :
      cbn_cpg (cbn_gc_copy k) -> cbn_gcg Gn g -> cbn_bh_get a g.(cbn_g_old) = Some cl ->
        cbn_cell_fwd cl = None ->
      cbn_rn_cell (cbn_gc_copy k) cl g = CbnCOk (cl1, g1) ->
      cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old) = Some old ->
      cbn_gc_inv s.(cbn_st_heap) s.(cbn_st_next)
        (cbn_mkGc old (cbn_bh_cons cl1 g1.(cbn_g_heap)) (Pos.succ g1.(cbn_g_next))) ->
      exists Gn', cbn_gcg Gn' (cbn_mkGc old (cbn_bh_cons cl1 g1.(cbn_g_heap))
        (Pos.succ g1.(cbn_g_next)))
        /\ cbn_gext Gn Gn' /\ (forall t, G a = Some t -> Gn' (CbnHAddr g1.(cbn_g_next)) = Some t).
    Proof.
      intros hk hg ha hf e1 e2 hinv2.
      assert (hcl : cbn_bh_get a s.(cbn_st_heap) = Some cl)
        by exact (cbn_inv_keep _ _ _ (cbn_gg_inv _ _ hg) _ _ ha hf).
      destruct (cbn_gk_cells _ _ _ hok a cl hcl) as [t0 [hGa hc0]].
      destruct (cbn_rn_cell_g _ hk _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hbusy & hr1).
      pose proof (cbn_inv_heap _ _ _ (cbn_gg_inv _ _ hg1)) as hok1.
      pose (Gn' := cbn_mkGhost (fun b =>
        if cbn_haddr_eqb b (CbnHAddr g1.(cbn_g_next)) then Some t0 else Gn1 b)
                     (cbn_gc Gn1)).
      assert (hfresh : forall b t, Gn1 b = Some t -> b <> CbnHAddr g1.(cbn_g_next)).
      { intros b t hb ->. destruct (cbn_gg_dom _ _ hg1 _ _ hb) as [_ hlt]. cbn in hlt. lia. }
      assert (hx2 : cbn_gext Gn1 Gn').
      { split; [|intros i e hi; exact hi].
        intros b t hb. unfold Gn'. cbn [cbn_gm].
        destruct (cbn_haddr_eqb b (CbnHAddr g1.(cbn_g_next))) eqn:eb; [|exact hb].
        apply cbn_haddr_eqb_eq in eb. exfalso. exact (hfresh _ _ hb eb). }
      assert (hnew : Gn' (CbnHAddr g1.(cbn_g_next)) = Some t0).
      { unfold Gn'. cbn [cbn_gm]. rewrite cbn_haddr_eqb_refl. reflexivity. }
      exists Gn'. split; [|split; [exact (cbn_gext_trans _ _ _ hx1 hx2)|]].
      2: { intros t ht. rewrite hGa in ht. injection ht as <-. exact hnew. }
      split; cbn [cbn_g_old cbn_g_heap cbn_g_next].
      - exact hinv2.
      - unfold Gn'. cbn [cbn_gc]. exact (cbn_gg_codes _ _ hg1).
      - intros x b t hx ht. destruct (cbn_haddr_dec x a) as [->|hne].
        + rewrite (cbn_bh_get_upd_same _ _ _ _ e2) in hx. injection hx as <-.
          rewrite hGa in ht. injection ht as <-. exact hnew.
        + rewrite (cbn_bh_get_upd_other _ _ _ _ _ e2 hne) in hx.
          exact (hx2 _ _ (cbn_gg_fwd _ _ hg1 _ _ _ hx ht)).
      - intros b cl' hb. destruct (cbn_haddr_dec b (CbnHAddr g1.(cbn_g_next))) as [->|hne].
        + rewrite (cbn_bh_get_cons_new _ _ _ _ hok1) in hb. injection hb as <-.
          exists t0. split; [exact hnew|].
          destruct hc0 as [->|[u [hu hred]]]; [left; exact (hbusy eq_refl)|].
          right. exists u. split; [exact (cbn_g_cell_mono _ _ hx2 _ _ (hr1 _ hu))|exact hred].
        + rewrite (cbn_bh_get_cons_old _ _ _ _ _ hok1 hne) in hb.
          destruct (cbn_gg_cells _ _ hg1 _ _ hb) as [t [ht hc]].
          exists t. split; [exact (hx2 _ _ ht)|].
          destruct hc as [hb'|[u [hu hred]]]; [left; exact hb'|].
          right. exists u. split; [exact (cbn_g_cell_mono _ _ hx2 _ _ hu)|exact hred].
      - intros b t hb. unfold Gn' in hb. cbn [cbn_gm] in hb.
        destruct (cbn_haddr_eqb b (CbnHAddr g1.(cbn_g_next))) eqn:eb.
        + apply cbn_haddr_eqb_eq in eb. subst b. cbn.
          split; [exact (cbn_bh_ok_le _ _ _ hok1)|lia].
        + destruct (cbn_gg_dom _ _ hg1 _ _ hb) as [h1 h2]. split; [exact h1|]. cbn. lia.
      - intros b t hb. unfold Gn' in hb. cbn [cbn_gm] in hb.
        destruct (cbn_haddr_eqb b (CbnHAddr g1.(cbn_g_next)));
          [injection hb as <-; exists a; exact hGa|].
        exact (cbn_gg_rng _ _ hg1 _ _ hb).
    Qed.

    Lemma cbn_gc_copy_g : forall f, cbn_cpg (cbn_gc_copy f).
    Proof.
      intros f. induction f as [|k ih]; intros a g a' g' Gn hg he.
      - rewrite cbn_gc_copy_FO in he.
        destruct (cbn_bh_get a g.(cbn_g_old)) as [cl|] eqn:ea; [|discriminate].
        destruct cl as [vals n o c|v| |b]; try discriminate.
        inversion he; subst; clear he.
        exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
        intros t ht. exact (cbn_gg_fwd _ _ hg _ _ _ ea ht).
      - pose proof he as he0.
        destruct (cbn_gc_copy_ok s.(cbn_st_heap) s.(cbn_st_next) (CbnFS k) a g a' g'
          (cbn_gg_inv _ _ hg) he0)
          as [hst _].
        rewrite cbn_gc_copy_FS in he.
        destruct (cbn_bh_get a g.(cbn_g_old)) as [cl|] eqn:ea; [|discriminate].
        destruct cl as [vals n o c|v| |b].
        + destruct (cbn_rn_cell (cbn_gc_copy (k tt)) (CbnCSusp vals n o c) g) as
          [[cl1 g1]|w] eqn:e1;
            [|discriminate].
          destruct (cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old)) as
            [old|] eqn:e2;
            [|discriminate].
          inversion he; subst; clear he.
          exact (cbn_gc_copy_g_write _ _ _ _ _ _ _ _ (ih tt) hg ea eq_refl e1 e2
                   (cbn_step_inv _ _ _ _ hst)).
        + destruct (cbn_rn_cell (cbn_gc_copy (k tt)) (CbnCDone v) g) as [[cl1 g1]|w] eqn:e1;
            [|discriminate].
          destruct (cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old)) as
            [old|] eqn:e2;
            [|discriminate].
          inversion he; subst; clear he.
          exact (cbn_gc_copy_g_write _ _ _ _ _ _ _ _ (ih tt) hg ea eq_refl e1 e2
                   (cbn_step_inv _ _ _ _ hst)).
        + destruct (cbn_rn_cell (cbn_gc_copy (k tt)) CbnCBusy g) as [[cl1 g1]|w] eqn:e1;
          [|discriminate].
          destruct (cbn_bh_upd a (CbnCFwd (CbnHAddr g1.(cbn_g_next))) g1.(cbn_g_old)) as
            [old|] eqn:e2;
            [|discriminate].
          inversion he; subst; clear he.
          exact (cbn_gc_copy_g_write _ _ _ _ _ _ _ _ (ih tt) hg ea eq_refl e1 e2
                   (cbn_step_inv _ _ _ _ hst)).
        + inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply cbn_gext_refl|].
          intros t ht. exact (cbn_gg_fwd _ _ hg _ _ _ ea ht).
    Qed.

    (** The ghost invariant survives a collection: the state after it is [cbn_gok] at the old
      [cbn_st_next] for the ghost of the new heap, and every root comes back renamed with the
      reading it had. *)
    Lemma cbn_collect_ghost rs rs' s' :
      cbn_collect rs s = CbnCOk (rs', s') ->
      exists G', cbn_gc G' = cbn_gc G /\ Forall2 (cbn_gpres G G') rs rs' /\
        cbn_gok s.(cbn_st_next) G' s'.
    Proof.
      intros he.
      destruct (cbn_collect_sound rs s rs' s' (cbn_gk_nofwd _ _ _ hok) he) as (hso & hnf & _ & _).
      rewrite cbn_collect_eq in he.
      destruct (cbn_rn_ptree (cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO)))
        s.(cbn_st_gam)
                  (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next))) as
                    [[gm1 g1]|w1] eqn:e1;
        [|discriminate].
      destruct (cbn_rn_roots (cbn_gc_copy (cbn_fuel_of_pos s.(cbn_st_next) (fun _ => CbnFO))) rs g1)
        as [[rs2 g2]|w2] eqn:e2; [|discriminate].
      inversion he; subst; clear he.
      assert (hg0 : cbn_gcg (cbn_mkGhost (fun _ => None) (cbn_gc G))
                      (cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes s.(cbn_st_next)) s.(cbn_st_next))).
      { split; cbn [cbn_g_old cbn_g_heap cbn_g_next cbn_gc cbn_gm].
        - constructor; cbn.
          + intros a cl hc _. exact hc.
          + intros a a' hc. destruct (cbn_gk_nofwd _ _ _ hok _ _ hc).
          + apply cbn_bh_ok_holes.
          + intros b cl hc. rewrite cbn_bh_get_holes in hc. discriminate.
          + intros b b' hc. rewrite cbn_bh_get_holes in hc. discriminate.
        - reflexivity.
        - intros x b t hx _. destruct (cbn_gk_nofwd _ _ _ hok _ _ hx).
        - intros b cl hc. rewrite cbn_bh_get_holes in hc. discriminate.
        - intros b t hb. discriminate hb.
        - intros b t hb. discriminate hb. }
      destruct (cbn_rn_ptree_g _ (cbn_gc_copy_g _) _ _ _ _ _ hg0 e1) as (Gn1 & hg1 & hx1 & hgam).
      destruct (cbn_rn_roots_g _ (cbn_gc_copy_g _) _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hroots).
      exists Gn2. split; [exact (cbn_gg_codes _ _ hg2)|]. split; [exact hroots|].
      split.
      - exact hso.
      - exact hnf.
      - intros a cl hc. exact (cbn_gg_cells _ _ hg2 _ _ hc).
      - intros a t ht. exact (cbn_gg_dom _ _ hg2 _ _ ht).
      - intros j a' hj. cbn [cbn_st_gam] in hj. destruct (hgam _ _ hj) as [a [ha hr]].
        destruct (cbn_gk_gam _ _ _ hok _ _ ha) as [t [hden hGa]].
        exists t. split; [exact hden|]. exact (hx2 _ _ (hr _ hGa)).
      - rewrite (cbn_gg_codes _ _ hg2).
        apply (cbn_mok_memo _ s); [reflexivity|exact (cbn_gk_memo _ _ _ hok)].
      - intros hc a t ht. destruct (cbn_gg_rng _ _ hg2 _ _ ht) as [x hx].
        exact (cbn_gk_hyg _ _ _ hok hc _ _ hx).
    Qed.
  End GhostCollect.

  (** *** Allocation, which may collect first *)

  (** The new cell's reading becomes its ghost term, so it must be hygienic (under
    [cbn_ctx_hyg]); every caller allocates a reading of hygienic ghosts and codes. *)
  Lemma cbn_alloc_now_sound lo G cl u s :
    cbn_gok lo G s -> cbn_g_cell G cl u -> (cbn_ctx_hyg -> on_free_vars cbn_xpredT u) ->
    exists G', cbn_gext G G' /\ cbn_gok lo G' (snd (cbn_alloc_now cl s))
      /\ G' (fst (cbn_alloc_now cl s)) = Some u.
  Proof.
    intros hok hcl hhu. cbn [cbn_alloc_now fst snd].
    pose (G' := cbn_mkGhost (fun b => if cbn_haddr_eqb b (CbnHAddr s.(cbn_st_next)) then
      Some u else G b)
                  (cbn_gc G)).
    assert (hnew : G' (CbnHAddr s.(cbn_st_next)) = Some u).
    { unfold G'. cbn [cbn_gm]. rewrite cbn_haddr_eqb_refl. reflexivity. }
    assert (hold : cbn_gext G G').
    { split; [|intros i e hi; exact hi].
      intros b t hb. unfold G'. cbn [cbn_gm].
      destruct (cbn_haddr_eqb b (CbnHAddr s.(cbn_st_next))) eqn:eb;
        [|exact hb].
      apply cbn_haddr_eqb_eq in eb. subst b.
      destruct (cbn_gk_dom _ _ _ hok _ _ hb) as [_ hlt]. cbn in hlt. lia. }
    assert (hbok : cbn_bh_ok lo s.(cbn_st_next) s.(cbn_st_heap))
      by exact (cbn_so_heap _ _ (cbn_gk_state _ _ _ hok)).
    exists G'. split; [exact hold|].
    split; [|exact hnew].
    split.
    - apply (cbn_alloc_now_state_ok lo cl s (cbn_gk_state _ _ _ hok)).
      apply (cbn_addrs_in_grow lo s.(cbn_st_next) (Pos.succ s.(cbn_st_next))); [lia|].
      apply (cbn_gdom_addrs_in lo G s); [exact (cbn_gk_dom _ _ _ hok)|].
      exact (cbn_g_cell_ad G cl u hcl).
    - intros b b' hb. cbn in hb.
      destruct (cbn_haddr_dec b (CbnHAddr s.(cbn_st_next))) as [->|hne].
      + rewrite (cbn_bh_get_cons_new _ _ _ _ hbok) in hb. injection hb as ->. inversion hcl.
      + rewrite (cbn_bh_get_cons_old _ _ _ _ _ hbok hne) in hb.
        exact (cbn_gk_nofwd _ _ _ hok _ _ hb).
    - intros b cl2 hb. unfold cbn_heap_get in hb. cbn in hb.
      destruct (cbn_haddr_dec b (CbnHAddr s.(cbn_st_next))) as [->|hne].
      + rewrite (cbn_bh_get_cons_new _ _ _ _ hbok) in hb.
        inversion hb; subst cl2. exists u. split; [exact hnew|].
        right. exists u. split; [exact (cbn_g_cell_mono G G' hold cl u hcl)|apply cbn_cred_refl].
      + rewrite (cbn_bh_get_cons_old _ _ _ _ _ hbok hne) in hb.
        destruct (cbn_gk_cells _ _ _ hok _ _ hb) as [t [ht hrest]].
        exists t. split; [exact (hold _ _ ht)|].
        destruct hrest as [hbusy|[u1 [hu1 hred]]]; [left; exact hbusy|].
        right. exists u1. split; [exact (cbn_g_cell_mono G G' hold _ _ hu1)|exact hred].
    - intros b t hb. unfold G' in hb. cbn [cbn_gm] in hb. cbn.
      destruct (cbn_haddr_eqb b (CbnHAddr s.(cbn_st_next))) eqn:eb.
      + apply cbn_haddr_eqb_eq in eb. subst b. cbn.
        split; [exact (cbn_bh_ok_le _ _ _ hbok)|lia].
      + destruct (cbn_gk_dom _ _ _ hok _ _ hb) as [h1 h2]. split; [exact h1|]. cbn. lia.
    - intros j b hj. cbn in hj.
      destruct (cbn_gk_gam _ _ _ hok _ _ hj) as [t [ht hg]].
      exists t. split; [exact ht|exact (hold _ _ hg)].
    - exact (cbn_gk_memo _ _ _ hok).
    - intros hc b t hb. unfold G' in hb. cbn [cbn_gm] in hb.
      destruct (cbn_haddr_eqb b (CbnHAddr s.(cbn_st_next))); [injection hb as <-; exact (hhu hc)|].
      exact (cbn_gk_hyg _ _ _ hok hc _ _ hb).
  Qed.

  (** [cbn_alloc] collects when [cbn_gc_due] says so: the roots come back renamed
    ([cbn_collect_ghost]) and the new cell is allocated in the new heap. *)
  Lemma cbn_alloc_sound lo G cl u rs s a rs' s' :
    cbn_gok lo G s -> cbn_g_cell G cl u -> (cbn_ctx_hyg -> on_free_vars cbn_xpredT u) ->
    cbn_alloc cl rs s = CbnCOk (a, rs', s') ->
    exists lo' G', cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ G' a = Some u.
  Proof.
    intros hok hcl hhu he.
    destruct (cbn_gc_due s) eqn:eg.
    - rewrite (cbn_alloc_gc cl rs s eg) in he.
      destruct (cbn_collect (CbnRC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate].
      destruct (cbn_collect_ghost lo G s hok _ _ _ ec) as (G1 & hc1 & hf1 & hok1).
      inversion hf1 as [|r1 r1' l1 l1' hp1 hf1']; subst.
      destruct r1' as [| | | | | |cl1]; try discriminate he.
      cbn [cbn_gpres] in hp1.
      destruct (cbn_alloc_now_sound _ _ _ _ _ hok1 (hp1 _ hcl) hhu) as (G2 & hx2 & hok2 & ha2).
      cbn [cbn_alloc_now] in he. inversion he; subst; clear he.
      exists s.(cbn_st_next), G2. split; [|split; [exact hok2|exact ha2]].
      split.
      + intros i e hi. apply (cbn_gx_codes hx2). rewrite hc1. exact hi.
      + exact (cbn_Forall2_gpres_r_ext _ _ _ _ _ hf1' hx2).
    - rewrite (cbn_alloc_no_gc cl rs s eg) in he. inversion he; subst; clear he.
      destruct (cbn_alloc_now_sound _ _ _ _ _ hok hcl hhu) as (G2 & hx2 & hok2 & ha2).
      exists lo, G2. split; [exact (cbn_gren_ext _ _ _ hx2)|]. split; [exact hok2|exact ha2].
  Qed.

  (** *** The context map *)

  (** A new entry of the code table, for a term that names its constants at the right instance
    length, and is hygienic under [cbn_ctx_hyg]: the ghost's code table grows to the new
    state's, and the new code is in it. *)
  Lemma cbn_new_entry_sound lo G t s :
    cbn_gok lo G s -> cbn_consts_okb Σ t = true -> (cbn_ctx_hyg -> on_free_vars cbn_xpredT t) ->
    exists G1, cbn_gext G G1 /\ cbn_gok lo G1 (snd (cbn_new_entry X_type X t [] s))
      /\ cbn_cok G1 (fst (cbn_new_entry X_type X t [] s)).
  Proof.
    intros hok hokt hhygt.
    destruct (cbn_new_entry_shape t [] s) as (q1 & q2 & q3 & _ & q5 & _).
    destruct (cbn_gk_memo _ _ _ hok) as (hmi & hmo & hcodes & hokb & hhyg).
    pose proof hmi as (hf & _).
    assert (hgrow : forall i e, PTree.get i (cbn_gc G) = Some e ->
      PTree.get i (((snd (cbn_new_entry X_type X t [] s)).(cbn_st_memo)).(cbn_m_codes)) = Some e).
    { intros i e hi. rewrite cbn_new_entry_codes.
      exact (cbn_memo_add_entry_codes_mono _ _ hf i e (hcodes i e hi)). }
    assert (hm1 : cbn_mok (((snd (cbn_new_entry X_type X t [] s)).(cbn_st_memo)).(cbn_m_codes))
                    (snd (cbn_new_entry X_type X t [] s))).
    { split; [exact (cbn_memo_inv_new_entry X_type X t [] s hmi)|].
      split; [exact (cbn_new_entry_memo_ok X_type X t [] s hmo)|].
      split; [intros i e hi; exact hi|].
      split.
      - intros i e hi. rewrite cbn_new_entry_codes in hi.
        destruct (cbn_key_eqb i ((s.(cbn_st_memo)).(cbn_m_ncode))) eqn:E.
        + apply cbn_key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
          injection hi as <-. cbn [cbn_ce_inst cbn_ce_term cbn_inst_code]. exact hokt.
        + rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E). exact (hokb i e hi).
      - intros hcx i e hi. rewrite cbn_new_entry_codes in hi.
        destruct (cbn_key_eqb i ((s.(cbn_st_memo)).(cbn_m_ncode))) eqn:E.
        + apply cbn_key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
          injection hi as <-. cbn [cbn_ce_inst cbn_ce_term cbn_inst_code]. exact (hhygt hcx).
        + rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E). exact (hhyg hcx i e hi). }
    exists (cbn_mkGhost (cbn_gm G)
              (((snd (cbn_new_entry X_type X t [] s)).(cbn_st_memo)).(cbn_m_codes))).
    split; [split; [intros a1 t1 h; exact h|exact hgrow]|].
    split.
    - apply (cbn_gok_recode lo G s); [exact hok|exact q1|exact q2|exact q5|exact hgrow|exact hm1].
    - exists (cbn_mkEntry t [] (cbn_wf_term_univs X_type X (cbn_inst_code [] t))).
      split; [cbn [cbn_gc]; apply cbn_new_entry_in_table|apply cbn_new_entry_code_inv].
  Qed.

  Lemma cbn_gam_sound lo G j rs s a rs' s' :
    cbn_gok lo G s ->
    cbn_gam X_type X Γ nctx j rs s = CbnCOk (a, rs', s') ->
    exists lo' G' t, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ G' a = Some t
                     /\ cbn_cred (tRel (lvl - nctx + j)) t.
  Proof.
    intros hok he. unfold cbn_gam in he. cbv zeta in he.
    destruct (PTree.get (cbn_key_of_succ_nat j) s.(cbn_st_gam)) as [a0|] eqn:eg.
    - inversion he; subst. clear he.
      destruct (cbn_gk_gam _ _ _ hok _ _ eg) as [t [ht hg]].
      exists lo, G, t. split; [apply cbn_gren_refl|].
      split; [exact hok|]. split; [exact hg|exact (cbn_ctx_den_red j t ht)].
    - destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
      assert (hmain : forall G0 cl t s1,
        cbn_gext G G0 ->
        cbn_ctx_den Γ nctx lvl j = Some t -> cbn_g_cell G0 cl t ->
          (cbn_ctx_hyg -> on_free_vars cbn_xpredT t) ->
        cbn_gok lo G0 s1 ->
        (match cbn_alloc cl rs s1 with
         | CbnCOk (a2, rs2, s2) =>
             CbnCOk (a2, rs2, cbn_set_gam (PTree.set (cbn_key_of_succ_nat j) a2 (cbn_st_gam s2)) s2)
         | CbnCFail w => CbnCFail w
         end) = CbnCOk (a, rs', s') ->
        exists lo' G' t2, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ G' a = Some t2
                          /\ cbn_cred (tRel (lvl - nctx + j)) t2).
      { intros G0 cl t s1 hx0 hden hcl hht hok1 hm.
        destruct (cbn_alloc cl rs s1) as [[[a1 rs1] s2]|w] eqn:ea; [|discriminate].
        inversion hm; subst. clear hm.
        destruct (cbn_alloc_sound lo G0 cl t rs s1 _ _ _ hok1 hcl hht ea)
          as (lo2 & G' & hren & hok2 & hga).
        destruct (cbn_gk_dom _ _ _ hok2 _ _ hga) as [hlo hlt].
        exists lo2, G', t. split; [exact
          (cbn_gren_trans _ _ _ _ _ _ (cbn_gren_ext _ _ _ hx0) hren)|].
        split; [|split; [exact hga|exact (cbn_ctx_den_red j t hden)]].
        split; cbn.
        - exact (cbn_state_ok_set_gam lo2 j _ _ (cbn_gk_state _ _ _ hok2) hlo hlt).
        - exact (cbn_gk_nofwd _ _ _ hok2).
        - exact (cbn_gk_cells _ _ _ hok2).
        - exact (cbn_gk_dom _ _ _ hok2).
        - intros j2 a2 hj2.
          destruct (cbn_key_eqb (cbn_key_of_succ_nat j2) (cbn_key_of_succ_nat j)) eqn:ek.
          + apply cbn_key_eqb_spec, cbn_key_of_succ_nat_inj in ek. subst j2.
            rewrite PTree.gss in hj2. injection hj2 as <-.
            exists t. split; [exact hden|exact hga].
          + rewrite PTree.gso in hj2 by (apply cbn_key_neq_of_eqb, ek).
            exact (cbn_gk_gam _ _ _ hok2 _ _ hj2).
        - exact (cbn_gk_memo _ _ _ hok2).
        - exact (cbn_gk_hyg _ _ _ hok2). }
      destruct decl.(decl_body) as [b|] eqn:eb.
      + destruct (cbn_new_entry X_type X b [] s) as [c s1] eqn:e1.
        destruct (cbn_new_entry_sound lo G b s hok (const_instance_ok j decl b ed eb)
                    (fun hcx => hcx j decl b ed eb)) as (G1 & hx1 & hok1 & hcok).
        rewrite e1 in hok1, hcok. cbn [fst snd] in hok1, hcok.
        assert (hct : c.(cbn_c_term) = b).
        { pose proof (cbn_new_entry_term X_type X b [] s) as h. rewrite e1 in h. exact h. }
        apply (hmain G1 (CbnCSusp [] 0 (S j) c) (lift (lvl - nctx + S j) 0 c.(cbn_c_term)) s1 hx1).
        * unfold cbn_ctx_den. rewrite ed, eb, hct. reflexivity.
        * constructor; [|exact hcok].
          rewrite <- (subst_empty 0 (lift (lvl - nctx + S j) 0 c.(cbn_c_term))).
          exact (cbn_g_susp_intro G1 [] 0 (S j) c.(cbn_c_term) [] (cbn_g_slots_nil G1) eq_refl).
        * intros hcx. rewrite hct. apply cbn_hyg_lift. exact (hcx j decl b ed eb).
        * exact hok1.
        * exact he.
      + apply (hmain G (CbnCDone (CbnVNeu (CbnNVar (nctx - S j)) []))
        (tRel (lvl - S (nctx - S j))) s
                 (cbn_gext_refl G)).
        * unfold cbn_ctx_den. rewrite ed, eb. reflexivity.
        * constructor. exact (cbn_g_VNeuVar G (nctx - S j) [] [] (Forall2_nil _)).
        * intros _. reflexivity.
        * exact hok.
        * exact he.
  Qed.

  (** *** Reading a variable of the environment *)

  Lemma cbn_env_var_sound lo G n e rs s x rs' s' tu :
    cbn_gok lo G s -> cbn_g_susp G e (tRel n) tu ->
    cbn_env_var X_type X Γ nctx n e rs s = CbnCOk (x, rs', s') ->
    exists lo' G' t, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_slot G' x t /\
      cbn_cred tu t.
  Proof.
    intros hok hsusp he. unfold cbn_env_var in he.
    destruct (cbn_g_susp_inv _ _ _ _ hsusp) as [ts (h1 & h2 & ->)].
    destruct (nth_error e.(cbn_ev_vals) n) as [x0|] eqn:en.
    - inversion he; subst. clear he.
      assert (hlt : n < #|e.(cbn_ev_vals)|) by (apply nth_error_Some_length in en; exact en).
      destruct (cbn_g_slots_nth _ _ _ _ _ h1 en) as [t [hnt hgt]].
      exists lo, G, t. split; [apply cbn_gren_refl|]. split; [exact hok|].
      split; [exact hgt|].
      rewrite h2, (lift_rel_lt (lvl - nctx + e.(cbn_ev_goff)) n #|e.(cbn_ev_vals)|); [|lia].
      rewrite (subst_rel_eq ts 0 n t n hnt eq_refl), lift0_id. apply cbn_cred_refl.
    - destruct (cbn_gam X_type X Γ nctx (n - e.(cbn_ev_nvals) + e.(cbn_ev_goff)) rs s)
        as [[[a1 rs1] s1]|w] eqn:eg; [|discriminate].
      inversion he; subst. clear he.
      destruct (cbn_gam_sound lo G (n - e.(cbn_ev_nvals) + e.(cbn_ev_goff)) rs s _ _ _ hok eg)
        as (lo1 & G' & t & hren & hok1 & hga & hred).
      assert (hge : #|e.(cbn_ev_vals)| <= n) by (apply nth_error_None in en; exact en).
      exists lo1, G', t. split; [exact hren|]. split; [exact hok1|].
      split; [constructor; exact hga|].
      rewrite h2.
      rewrite (lift_rel_ge (lvl - nctx + e.(cbn_ev_goff)) n #|e.(cbn_ev_vals)|); [|lia].
      rewrite (subst_rel_gt ts (lvl - nctx + e.(cbn_ev_goff) + n) 0);
        [|rewrite (cbn_g_slots_length _ _ _ h1); lia].
      rewrite (cbn_g_slots_length _ _ _ h1).
      replace (lvl - nctx + e.(cbn_ev_goff) + n - #|e.(cbn_ev_vals)|)
        with (lvl - nctx + (n - e.(cbn_ev_nvals) + e.(cbn_ev_goff))) by lia.
      exact hred.
  Qed.

  (** *** The slot of an argument *)

  Lemma cbn_arg_slot_sound lo G e c rs s x rs' s' tu :
    cbn_gok lo G s -> cbn_g_susp G e c.(cbn_c_term) tu -> cbn_cok G c ->
    cbn_arg_slot X_type X Γ nctx e c rs s = CbnCOk (x, rs', s') ->
    exists lo' G' t, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_slot G' x t /\
      cbn_cred tu t.
  Proof.
    intros hok hsusp hcok he. unfold cbn_arg_slot in he.
    destruct (cbn_g_susp_inv _ _ _ _ hsusp) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [cbn_ev_vals cbn_ev_nvals cbn_ev_goff] in *.
    destruct (cbn_c_term c) eqn:ec;
      [ refine (cbn_env_var_sound lo G n (cbn_mkEnv vals nvals goff) rs s x rs' s' _ hok _ he);
        exact hsusp | .. ].
    all: inversion he; subst; clear he.
    all: exists lo, G; eexists; split; [apply cbn_gren_refl|]; split; [exact hok|];
         split; [|apply cbn_cred_refl].
    all: rewrite <- ec; constructor; [exact h1|try reflexivity; try assumption|exact hcok].
  Qed.

  (** *** Putting a slot in the heap *)

  Lemma cbn_materialize_sound lo G x rs s a rs' s' t :
    cbn_gok lo G s -> cbn_g_slot G x t ->
    cbn_materialize X_type X x rs s = CbnCOk (a, rs', s') ->
    exists lo' G', cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ G' a = Some t.
  Proof.
    intros hok hx he.
    assert (hht : cbn_ctx_hyg -> on_free_vars cbn_xpredT t).
    { intros hc. exact (proj1 (cbn_g_slot_hyg G (cbn_gk_hyg _ _ _ hok hc)
      (cbn_gok_codes_hyg _ _ _ hok hc))
                          _ _ hx). }
    unfold cbn_materialize in he.
    destruct x as [a0|vals n o c].
    - inversion hx; subst. inversion he; subst. clear he.
      exists lo, G. split; [apply cbn_gren_refl|]. split; [exact hok|assumption].
    - inversion hx; subst. clear hx.
      match goal with h1 : cbn_g_slots G vals ?ts0 |- _ =>
        assert (hsusp : cbn_g_susp G (cbn_mkEnv vals #|vals| o) c.(cbn_c_term)
                          (subst ts0 0 (lift (lvl - nctx + o) #|vals| c.(cbn_c_term))))
          by (constructor; [exact h1|reflexivity])
      end.
      remember (subst _ 0 (lift (lvl - nctx + o) #|vals| c.(cbn_c_term))) as t0 eqn:ht0.
      rename hht into hht0.
      destruct (cbn_c_term c) eqn:ec.
      all: try (assert (hcl : cbn_g_cell G (CbnCSusp vals #|vals| o c) t0)
                  by (constructor; [rewrite ec; exact hsusp|assumption]);
                exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he)).
      + (* tSort *)
        assert (hcl : cbn_g_cell G (CbnCDone (CbnVOpen (cbn_mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
      + (* tProd *)
        assert (hcl : cbn_g_cell G (CbnCDone (CbnVOpen (cbn_mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
      + (* tLambda *)
        assert (hcl : cbn_g_cell G (CbnCDone (CbnVLam (cbn_mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
      + (* tConst: the memo may add an entry first *)
        match type of he with context [cbn_delta X_type X ?kn ?ui s] =>
          destruct (cbn_delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
        end.
        * pose proof (cbn_delta_gok lo G _ _ s _ s1 hok ed) as hok1.
          assert (hcl : cbn_g_cell G (CbnCSusp vals #|vals| o c) t0)
            by (constructor; [rewrite ec; exact hsusp|assumption]).
          exact (cbn_alloc_sound lo G _ _ rs s1 a rs' s' hok1 hcl hht0 he).
        * pose proof (cbn_delta_gok lo G _ _ s _ s1 hok ed) as hok1.
          assert (hcl : cbn_g_cell G (CbnCDone (CbnVNeu (CbnNConst (tConst k ui)) [])) t0).
          { constructor. rewrite ht0, cbn_subst_lift_const.
            exact (cbn_g_VNeuConst G (tConst k ui) [] [] (Forall2_nil _)). }
          exact (cbn_alloc_sound lo G _ _ rs s1 a rs' s' hok1 hcl hht0 he).
        * assert (hcl : cbn_g_cell G (CbnCSusp vals #|vals| o c) t0)
            by (constructor; [rewrite ec; exact hsusp|assumption]).
          exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
      + (* tFix: a fixpoint value, or a suspension if the index is out of range *)
        match goal with ec' : cbn_c_term c = tFix ?m ?i |- _ =>
          destruct (nth_error m i) as [def|] eqn:enth
        end.
        * match goal with ec' : cbn_c_term c = tFix ?m ?i |- _ =>
            assert (hcl : cbn_g_cell G (CbnCDone (CbnVFix (cbn_mkEnv vals #|vals| o) c i [])) t0)
          end.
          { constructor. change t0 with (mkApps t0 []).
            eapply cbn_g_VFix; [exact ec| |assumption|constructor].
            first [exact hsusp|rewrite <- ec; exact hsusp|rewrite ec in hsusp; exact hsusp]. }
          exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
        * assert (hcl : cbn_g_cell G (CbnCSusp vals #|vals| o c) t0)
            by (constructor; [rewrite ec; exact hsusp|assumption]).
          exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
      + (* tPrim *)
        assert (hcl : cbn_g_cell G (CbnCDone (CbnVOpen (cbn_mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (cbn_alloc_sound lo G _ _ rs s a rs' s' hok hcl hht0 he).
  Qed.

  (** *** Binding a slot to a binder *)

  Lemma cbn_bind_sound lo G x body rs s y rs' s' t :
    cbn_gok lo G s -> cbn_g_slot G x t -> cbn_cok G body ->
    cbn_bind X_type X x body rs s = CbnCOk (y, rs', s') ->
    exists lo' G', cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_slot G' y t.
  Proof.
    intros hok hx hcb he. unfold cbn_bind in he.
    destruct x as [a0|vals n o c].
    - inversion he; subst. clear he.
      exists lo, G. split; [apply cbn_gren_refl|]. split; [exact hok|exact hx].
    - destruct (cbn_once_body body s) as [b s1] eqn:eo.
      destruct (cbn_once_body_shape body s) as (q1 & q2 & q3 & _ & q5 & _).
      assert (hs1 : s1 = snd (cbn_once_body body s)) by (rewrite eo; reflexivity).
      assert (hok1 : cbn_gok lo G s1).
      { destruct hcb as [e [hge hci]].
        apply (cbn_gok_same lo G s);
          [exact hok|rewrite hs1; exact q1|rewrite hs1; exact q2|rewrite hs1; exact q5|].
        rewrite hs1. destruct (cbn_gk_memo _ _ _ hok) as (_ & _ & h3 & _).
        exact (cbn_mok_once_body _ body e s (cbn_gk_memo _ _ _ hok) (h3 _ _ hge) hci). }
      clear hs1.
      destruct b.
      + inversion he; subst. clear he.
        exists lo, G. split; [apply cbn_gren_refl|]. split; [exact hok1|exact hx].
      + destruct (cbn_materialize X_type X (CbnSInl vals n o c) rs s1)
          as [[[a1 rs1] s2]|w] eqn:em; [|discriminate].
        destruct (cbn_materialize_sound lo G (CbnSInl vals n o c) rs s1 a1 rs1 s2 t hok1 hx em)
          as (lo2 & G2 & hren & hok2 & hga).
        inversion he; subst. clear he.
        exists lo2, G2. split; [exact hren|]. split; [exact hok2|constructor; exact hga].
  Qed.

  (** *** A whole stack put in the heap *)

  Lemma cbn_mat_all_sound : forall d lo G l ts rs s al rs' s',
    cbn_gok lo G s -> cbn_g_slots G l ts ->
    cbn_mat_all X_type X d l rs s = CbnCOk (al, rs', s') ->
    exists lo' G', cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_addrs G' al ts.
  Proof.
    intros d. induction d as [|k ih]; intros lo G l ts rs s al rs' s' hok hl he;
      destruct l as [|x l]; cbn [cbn_mat_all] in he.
    1,3: inversion he; subst; clear he; inversion hl; subst;
         exists lo, G; (split; [apply cbn_gren_refl|]); (split; [exact hok|constructor]).
    - discriminate.
    - inversion hl as [|x' l' tx ts0 hgx hgl hex hets]; subst; clear hl.
      destruct (cbn_materialize X_type X x (CbnRSk l :: rs) s) as [[[a1 rs1] s1]|w] eqn:em;
        [|discriminate].
      destruct (cbn_materialize_sound lo G x (CbnRSk l :: rs) s a1 rs1 s1 tx hok hgx em)
        as (lo1 & G1 & hren1 & hok1 & hga1).
      destruct rs1 as [|r rs1t]; [discriminate he|].
      destruct r as [| | | |l1| |]; try discriminate he.
      destruct (cbn_gren_cons _ _ _ _ _ _ hren1) as [hpk hren1']. cbn [cbn_gpres] in hpk.
      destruct (cbn_mat_all X_type X (k tt) l1 (CbnRA a1 :: rs1t) s1)
        as [[[al1 rs2] s2]|w] eqn:em2; [|discriminate].
      destruct rs2 as [|r rs2t]; [discriminate he|].
      destruct r as [a0| | | | | |]; try discriminate he.
      injection he as hal hrs' hs'; subst al rs' s'.
      destruct (ih tt lo1 G1 l1 ts0 (CbnRA a1 :: rs1t) s1 al1 (CbnRA a0 :: rs2t) s2 hok1
                  (hpk _ hgl) em2)
        as (lo2 & G2 & hren2 & hok2 & haddr2).
      destruct (cbn_gren_cons _ _ _ _ _ _ hren2) as [hpa hren2']. cbn [cbn_gpres] in hpa.
      exists lo2, G2. split; [exact (cbn_gren_trans _ _ _ _ _ _ hren1' hren2')|].
      split; [exact hok2|].
      constructor; [exact (hpa _ hga1)|exact haddr2].
  Qed.

  (** A value grows its spine: what [cbn_apply] does to a constructor, a neutral, a stuck match
    or projection, and a stuck fixpoint once the stack is in the heap. *)
  Lemma cbn_g_value_add_spine G v t l ts v' :
    cbn_g_value G v t -> cbn_g_addrs G l ts -> cbn_add_spine v l = Some v' ->
      cbn_g_value G v' (mkApps t ts).
  Proof.
    intros hv hl ha. destruct hv; cbn in ha; try discriminate ha; injection ha as <-.
    all: rewrite <- mkApps_app; econstructor; try eassumption; apply Forall2_app; assumption.
  Qed.

  (** *** The cells of a fixpoint block

    [cbn_push_fix_cells] allocates fixpoint [i], ..., [i + m - 1] of the [tFix] code [c] as
    values over [e] and pushes them on [acc]: the new slots stand for those fixpoints read
    through [e], the last one first, which is [fix_subst]'s order. *)

  Lemma cbn_push_fix_cells_sound : forall m lo G e c mfix idx0 ts i acc tacc rs s e' rs' s',
    cbn_gok lo G s -> c.(cbn_c_term) = tFix mfix idx0 -> cbn_cok G c ->
    cbn_g_slots G e.(cbn_ev_vals) ts -> e.(cbn_ev_nvals) = #|e.(cbn_ev_vals)| ->
    cbn_g_slots G acc.(cbn_ev_vals) tacc -> acc.(cbn_ev_nvals) = #|acc.(cbn_ev_vals)| ->
    cbn_push_fix_cells e c i m acc rs s = CbnCOk (e', rs', s') ->
    exists lo' G', cbn_gren G G' rs rs' /\ cbn_gok lo' G' s'
       /\ cbn_g_slots G' e'.(cbn_ev_vals)
            (List.rev (map (fun j => subst ts 0
              (lift (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals)
                                                     (tFix mfix j))) (seq i m)) ++ tacc)
       /\ e'.(cbn_ev_nvals) = #|e'.(cbn_ev_vals)| /\ e'.(cbn_ev_goff) = acc.(cbn_ev_goff).
  Proof.
    intros m. induction m as [|m ih];
      intros lo G e c mfix idx0 ts i acc tacc rs s e' rs' s'
        hok hc hcok hts hnv hacc hnacc he.
    - cbn [cbn_push_fix_cells] in he. inversion he; subst. clear he.
      exists lo, G. split; [apply cbn_gren_refl|]. split; [exact hok|].
      cbn [seq map List.rev app]. split; [exact hacc|]. split; [exact hnacc|reflexivity].
    - cbn [cbn_push_fix_cells] in he.
      destruct (cbn_alloc (CbnCDone (CbnVFix e c i [])) (CbnRE e :: CbnRE acc :: rs) s)
        as [[[a1 rs1] s1]|w] eqn:ea; [|discriminate he].
      set (tf := fun j => subst ts 0 (lift (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals)
        (tFix mfix j))).
      assert (hcl : cbn_g_cell G (CbnCDone (CbnVFix e c i [])) (tf i)).
      { constructor. exact (cbn_g_VFix G e c mfix idx0 i [] (tf i) [] hc
                              (cbn_g_susp_of_slots G e _ ts hts hnv) hcok (Forall2_nil _)). }
      assert (hhf : cbn_ctx_hyg -> on_free_vars cbn_xpredT (tf i)).
      { intros hx. apply (cbn_g_susp_hyg G (cbn_gk_hyg _ _ _ hok hx)
        (cbn_gok_codes_hyg _ _ _ hok hx) e
                          (tFix mfix i)).
        - apply (cbn_hyg_tFix_idx mfix idx0 i). rewrite <- hc.
          exact (cbn_gok_codes_hyg _ _ _ hok hx c hcok).
        - exact (cbn_g_susp_of_slots G e _ ts hts hnv). }
      destruct (cbn_alloc_sound lo G _ _ _ s a1 rs1 s1 hok hcl hhf ea)
        as (lo1 & G1 & hren1 & hok1 & hga1).
      destruct rs1 as [|r1 rs1a]; [discriminate he|].
      destruct r1 as [| |e1| | | |]; try discriminate he.
      destruct rs1a as [|r2 rs1b]; [discriminate he|].
      destruct r2 as [| |acc1| | | |]; try discriminate he.
      destruct (cbn_gren_cons _ _ _ _ _ _ hren1) as [hpe hren1a].
      destruct (cbn_gren_cons _ _ _ _ _ _ hren1a) as [hpa hren1b].
      cbn [cbn_gpres] in hpe, hpa.
      destruct hpe as (hnv1 & hgo1 & hsl1). destruct hpa as (hnva & hgoa & hsla).
      assert (hts1 : cbn_g_slots G1 e1.(cbn_ev_vals) ts) by exact (hsl1 _ hts).
      assert (hnv1' : e1.(cbn_ev_nvals) = #|e1.(cbn_ev_vals)|).
      { rewrite hnv1, hnv, <- (cbn_g_slots_length _ _ _ hts), (cbn_g_slots_length _ _ _ hts1).
        reflexivity. }
      assert (hacc1 : cbn_g_slots G1 acc1.(cbn_ev_vals) tacc) by exact (hsla _ hacc).
      assert (hnacc1 : (cbn_env_push (CbnSAddr a1) acc1).(cbn_ev_nvals)
                       = #|(cbn_env_push (CbnSAddr a1) acc1).(cbn_ev_vals)|).
      { cbn [cbn_env_push cbn_ev_vals cbn_ev_nvals].
        rewrite hnva, hnacc, <- (cbn_g_slots_length _ _ _ hacc), (cbn_g_slots_length _ _ _ hacc1).
        reflexivity. }
      destruct (ih lo1 G1 e1 c mfix idx0 ts (S i) (cbn_env_push (CbnSAddr a1) acc1) (tf i :: tacc)
                  rs1b s1 e' rs' s' hok1 hc (cbn_gren_cok _ _ _ _ c hren1 hcok) hts1 hnv1'
                  (cbn_g_slots_cons G1 (CbnSAddr a1) _ (tf i) tacc
                    (cbn_g_slot_addr G1 a1 (tf i) hga1)
                     hacc1)
                  hnacc1 he)
        as (lo2 & G2 & hren2 & hok2 & hsl & hnv' & hgoff).
      exists lo2, G2. split; [exact (cbn_gren_trans _ _ _ _ _ _ hren1b hren2)|].
      split; [exact hok2|].
      rewrite hnv1, hgo1 in hsl.
      split; [|split; [exact hnv'|rewrite hgoff; cbn [cbn_env_push cbn_ev_goff]; exact hgoa]].
      cbn [seq map List.rev]. rewrite <- app_assoc. exact hsl.
  Qed.

  (** *** The arguments of a primitive operation *)

  (** A slot that holds a literal stands for a term that reduces to it. *)
  Lemma cbn_slot_lit_sound lo G x t s l :
    cbn_gok lo G s -> cbn_g_slot G x t -> cbn_slot_lit x s = Some l ->
    cbn_cred t (term_of_lit l).
  Proof.
    intros hok hx hl. destruct x as [a|vs n o c]; cbn [cbn_slot_lit] in hl.
    - pose proof (cbn_g_slot_addr_inv _ _ _ hx) as hGa.
      destruct (cbn_heap_get a s) as [cl|] eqn:ehc; [|discriminate hl].
      destruct cl as [vs n o c|vd| |b]; try discriminate hl.
      destruct vd as [h sp|e c|e c i sp|e c i sp|nn sp|e c|e c sp]; try discriminate hl.
      destruct (cbn_gk_cells _ _ _ hok a _ ehc) as [t1 [hGa1 [hbusy|[u [hgc hcred]]]]];
        [discriminate hbusy|].
      rewrite hGa in hGa1. injection hGa1 as <-.
      pose proof (cbn_g_value_VOpen_inv _ _ _ _ (cbn_g_cell_done_inv _ _ _ hgc)) as hsusp.
      destruct (cbn_g_susp_inv _ _ _ _ hsusp) as (ts & _ & _ & ->).
      rewrite (lit_of_term_inv _ _ hl), cbn_lit_subst_lift in hcred. exact hcred.
    - pose proof (cbn_g_slot_inl_inv _ _ _ _ _ _ hx) as hsusp.
      destruct (cbn_g_susp_inv _ _ _ _ hsusp) as (ts & _ & _ & ->).
      cbn [cbn_ev_goff cbn_ev_nvals].
      rewrite (lit_of_term_inv _ _ hl), cbn_lit_subst_lift. apply cbn_cred_refl.
  Qed.

  (** Slots that all hold literals: the application to the terms they stand for reduces to
    the application to the literals. *)
  Lemma cbn_slot_lits_sound lo G s : forall l ts ls f us,
    cbn_gok lo G s -> cbn_g_slots G l ts -> cbn_slot_lits l s = inl ls ->
    cbn_cred (mkApps f (ts ++ us)) (mkApps f (map term_of_lit ls ++ us)).
  Proof.
    intros l. induction l as [|x l ih]; intros ts ls f us hok hts hl; cbn [cbn_slot_lits] in hl.
    - injection hl as <-. inversion hts; subst. apply cbn_cred_refl.
    - destruct (cbn_slot_lit x s) as [lt|] eqn:ex; [|discriminate hl].
      destruct (cbn_slot_lits l s) as [ls'|[i y]] eqn:el; [|discriminate hl].
      injection hl as <-. inversion hts as [|x0 l0 t ts' hx hts']; subst.
      cbn [app map mkApps].
      eapply cbn_cred_trans.
      + apply cbn_cred_mkApps. apply cbn_cred_app_r.
        exact (cbn_slot_lit_sound lo G x t s lt hok hx ex).
      + exact (ih ts' ls' (tApp f (term_of_lit lt)) us hok hts' eq_refl).
  Qed.

  (** ** The evaluator against PCUIC reduction

    The input stands (through the ghost map) for a term that reduces, in PCUIC, to the term
    the output value stands for, and the state invariant is re-established. A call may
    collect: the ghost it ends with is not an extension of the one it started with, and the
    roots come back renamed, standing for what they stood for ([cbn_gren]). A caller takes the
    structures it holds back out of the returned roots, as the machine does. The five
    functions are proved together by induction on the fuel ([cbn_machine_sound]): each lemma
    below proves one step of one function, or one rule of [cbn_whnf], from the clauses at the
    fuel below. [cbn_whnf_fix] takes the code of a whole [tFix] block and the index [idx] of the
    fixpoint it applies, which need not be the index the code was written with: [cbn_apply]
    calls it on the fixpoint cells [cbn_push_fix_cells] made.

    The machine answers [CbnCFail] on every shape but one of the roots a call gives back, of the
    value a call returns and of the head of that value. [destruct x as [...]; try discriminate
    he] closes the goals of the other shapes. The [try] is needed because one branch of the
    [destruct] is not contradictory, and it cannot stop firing unnoticed: a branch it leaves
    open fails the next tactic or the bullet. *)

  (** [hw] runs [cbn_whnf] at [CbnFS k]: past the step [htick] takes, keep the rule for the code
    [hct] names. *)
  Local Ltac cbn_whnf_rule hw htick hct :=
    cbn [cbn_whnf] in hw; rewrite htick, hct in hw; cbv beta iota in hw.

  (** The answer of a call stands for a reduct of [t]. *)
  Definition cbn_res_sound (G : cbn_ghost) (rs rs' : list cbn_root) (s' : cbn_state) (v : cbn_value)
      (t : term) : Prop :=
    exists lo' G' u, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_value G' v u /\
      cbn_cred t u.

  (** The five clauses of [cbn_machine_sound], at fuel [d]. *)
  Definition cbn_force_sound_at (d : cbn_fuel) : Prop :=
    forall lo G a rs s v rs' s' t,
      cbn_gok lo G s -> G a = Some t ->
      cbn_force X_type X Γ nctx d a rs s = CbnCOk (v, rs', s') -> cbn_res_sound G rs rs' s' v t.

  Definition cbn_eval_slot_sound_at (d : cbn_fuel) : Prop :=
    forall lo G x stk sts tx rs s v rs' s',
      cbn_gok lo G s -> cbn_g_slot G x tx -> cbn_g_slots G stk sts ->
      cbn_eval_slot X_type X Γ nctx d x stk rs s = CbnCOk (v, rs', s') ->
      cbn_res_sound G rs rs' s' v (mkApps tx sts).

  Definition cbn_whnf_sound_at (d : cbn_fuel) : Prop :=
    forall lo G e c stk sts tc rs s v rs' s',
      cbn_gok lo G s -> cbn_g_susp G e c.(cbn_c_term) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
      cbn_whnf X_type X Γ nctx d e c stk rs s = CbnCOk (v, rs', s') ->
      cbn_res_sound G rs rs' s' v (mkApps tc sts).

  Definition cbn_whnf_fix_sound_at (d : cbn_fuel) : Prop :=
    forall lo G e c mfix idx0 idx stk sts tc rs s v rs' s',
      cbn_gok lo G s -> c.(cbn_c_term) = tFix mfix idx0 ->
      cbn_g_susp G e (tFix mfix idx) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
      cbn_whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = CbnCOk (v, rs', s') ->
      cbn_res_sound G rs rs' s' v (mkApps tc sts).

  Definition cbn_apply_sound_at (d : cbn_fuel) : Prop :=
    forall lo G v stk sts tv rs s w rs' s',
      cbn_gok lo G s -> cbn_g_value G v tv -> cbn_g_slots G stk sts ->
      cbn_apply X_type X Γ nctx d v stk rs s = CbnCOk (w, rs', s') ->
      cbn_res_sound G rs rs' s' w (mkApps tv sts).

  (** The value is already there. *)
  Lemma cbn_res_sound_here lo G G' rs rs' s' v t :
    cbn_gren G G' rs rs' -> cbn_gok lo G' s' -> cbn_g_value G' v t -> cbn_res_sound G rs rs' s' v t.
  Proof.
    intros hr hok hv. exists lo, G', t. split; [exact hr|]. split; [exact hok|].
    split; [exact hv|apply cbn_cred_refl].
  Qed.

  (** A call made after a renaming and a reduction answers for the term before them. *)
  Lemma cbn_res_sound_pre G G1 rs rs1 rs' s' v t t1 :
    cbn_gren G G1 rs rs1 -> cbn_cred t t1 -> cbn_res_sound G1 rs1 rs' s' v t1 ->
    cbn_res_sound G rs rs' s' v t.
  Proof.
    intros hr hc (lo' & G' & u & hr' & hok & hv & hc').
    exists lo', G', u. split; [exact (cbn_gren_trans _ _ _ _ _ _ hr hr')|].
    split; [exact hok|]. split; [exact hv|exact (cbn_cred_trans _ _ _ hc hc')].
  Qed.

  (** *** Shapes several rules share *)

  (** A sort, a product or a primitive with an empty stack: the code is its own value. *)
  Lemma cbn_open_sound lo G e c stk sts tc rs s v rs' s' :
    cbn_gok lo G s -> cbn_g_susp G e c.(cbn_c_term) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    match stk with [] => CbnCOk (CbnVOpen e c, rs, s) | _ :: _ => CbnCFail CbnWShape end
      = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hok hsusp hcok hsts he. destruct stk as [|xh stk']; [|discriminate he].
    injection he as <- <- <-. inversion hsts; subst.
    exact (cbn_res_sound_here lo G G rs rs s (CbnVOpen e c) tc (cbn_gren_refl G rs) hok
             (cbn_g_VOpen G e c tc hsusp hcok)).
  Qed.

  (** A head with its stack put in the heap: an inductive, a constructor, or a constant
    without a body. *)
  Lemma cbn_head_sound d lo G stk sts rs s v rs' s' (mk : list cbn_haddr -> cbn_value) t :
    cbn_gok lo G s -> cbn_g_slots G stk sts ->
    (forall G' sp, cbn_g_addrs G' sp sts -> cbn_g_value G' (mk sp) t) ->
    match cbn_mat_all X_type X d stk rs s with
    | CbnCOk (sp, rs, s) => CbnCOk (mk sp, rs, s)
    | CbnCFail w => CbnCFail w
    end = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v t.
  Proof.
    intros hok hsts hmk he.
    cbn_dcall he em sp rsm sm.
    injection he as <- <- <-.
    destruct (cbn_mat_all_sound d lo G stk sts rs s sp rsm sm hok hsts em)
      as (lom & G' & hrenm & hokm & haddrm).
    exact (cbn_res_sound_here lom G G' rs rsm sm (mk sp) t hrenm hokm (hmk G' sp haddrm)).
  Qed.

  (** A stuck form: the stack put in the heap, the environment kept as a root. A match or a
    projection on a neutral or stuck scrutinee, and a fixpoint short of its recursive
    argument or applied to a neutral or stuck one. *)
  Lemma cbn_stuck_sound d lo G e stk sts rs s v rs' s' (mk : cbn_env -> list cbn_haddr -> cbn_value)
      t :
    cbn_gok lo G s -> cbn_g_slots G stk sts ->
    (forall G' e' sp, cbn_gcx G G' -> cbn_genv G G' e e' -> cbn_g_addrs G' sp sts ->
       cbn_g_value G' (mk e' sp) t) ->
    match cbn_mat_all X_type X d stk (CbnRE e :: rs) s with
    | CbnCOk (sp, rs, s) =>
        match rs with
        | CbnRE e :: rs => CbnCOk (mk e sp, rs, s)
        | _ => CbnCFail CbnWRoots
        end
    | CbnCFail w => CbnCFail w
    end = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v t.
  Proof.
    intros hok hsts hmk he.
    cbn_dcall he em sp rsm sm.
    destruct rsm as [|[| |ee| | | |] rsm]; try discriminate he.
    injection he as <- <- <-.
    destruct (cbn_mat_all_sound d lo G stk sts (CbnRE e :: rs) s sp (CbnRE ee :: rsm) sm
      hok hsts em)
      as (lom & G' & hrenm & hokm & haddrm).
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenm) as [hpe hrenm1].
    cbn [cbn_gpres] in hpe.
    exact (cbn_res_sound_here lom G G' rs rsm sm (mk ee sp) t hrenm1 hokm
             (hmk G' ee sp (proj1 hrenm) hpe haddrm)).
  Qed.

  (** Beta: the argument bound in the environment, then the body. [cbn_whnf] on a [tLambda]
    code and [cbn_apply] on a [CbnVLam] value run the same code. *)
  Lemma cbn_beta_sound d (IHw : cbn_whnf_sound_at d) lo G e c na A b xh stk txh sts tc rs s v rs'
      s' :
    cbn_gok lo G s -> c.(cbn_c_term) = tLambda na A b -> cbn_g_susp G e (tLambda na A b) tc ->
    cbn_cok G c -> cbn_g_slot G xh txh -> cbn_g_slots G stk sts ->
    match cbn_bind X_type X xh (cbn_child c 1 b) (CbnRE e :: CbnRSk stk :: rs) s with
    | CbnCOk (x, rs, s) =>
        match rs with
        | CbnRE e :: CbnRSk stk :: rs =>
            cbn_whnf X_type X Γ nctx d (cbn_env_push x e) (cbn_child c 1 b) stk rs s
        | _ => CbnCFail CbnWRoots
        end
    | CbnCFail w => CbnCFail w
    end = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc (txh :: sts)).
  Proof.
    intros hok ect hsusp hcok hsloth hslots he.
    assert (hcb : cbn_cok G (cbn_child c 1 b))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    cbn_dcall he eb xb rsb sb.
    destruct rsb as [|[| |ee| | | |] [|[| | | |lk| |] rsb]]; try discriminate he.
    destruct (cbn_bind_sound lo G xh (cbn_child c 1 b) (CbnRE e :: CbnRSk stk :: rs) s xb
                (CbnRE ee :: CbnRSk lk :: rsb) sb txh hok hsloth hcb eb)
      as (lob & Gv & hrenb & hokb & hslotb).
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenb) as [hpe hrenb1].
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenb1) as [hpk hrenb2].
    cbn [cbn_gpres] in hpe, hpk.
    destruct (cbn_g_susp_lam Gv ee na A b tc (cbn_genv_susp _ _ _ _ _ _ hpe hsusp))
      as (A' & B & htc & hlamprop).
    subst tc.
    refine (cbn_res_sound_pre G Gv rs rsb rs' s' v _ (mkApps (subst [txh] 0 B) sts) hrenb2 _
              (IHw lob Gv (cbn_env_push xb ee) (cbn_child c 1 b) lk sts (subst [txh] 0 B)
                rsb sb v rs'
                 s' hokb (hlamprop xb txh hslotb) (cbn_gren_cok _ _ _ _ _ hrenb hcb)
                 (hpk _ hslots) he)).
    change (mkApps (tLambda na A' B) (txh :: sts))
      with (mkApps (tApp (tLambda na A' B) txh) sts).
    apply cbn_cred_mkApps. apply cbn_cred_one. apply red_beta.
  Qed.

  (** *** The rules of [cbn_whnf] *)

  Lemma cbn_whnf_tick k e c stk rs s r :
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk r -> exists st, cbn_tick s = Some st.
  Proof.
    cbn [cbn_whnf].
    destruct (cbn_tick s) as [st|]; [intros _; exists st; reflexivity|intros h; discriminate h].
  Qed.

  Lemma cbn_gok_tick lo G s st : cbn_gok lo G s -> cbn_tick s = Some st -> cbn_gok lo G st.
  Proof.
    intros hok etick. destruct (cbn_tick_shape _ _ etick) as (th & tn & _ & tg & tm).
    exact (cbn_gok_same lo G s st hok th tn tg (cbn_mok_memo _ s st tm (cbn_gk_memo _ _ _ hok))).
  Qed.

  (** A variable: its slot, evaluated against the stack. *)
  Lemma cbn_whnf_rel_sound k (IHs : cbn_eval_slot_sound_at (k tt)) lo G e c n stk sts tc rs s st v
      rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tRel n ->
      cbn_g_susp G e (tRel n) tc ->
    cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hsts hw. cbn_whnf_rule hw etick ect.
    cbn_dcall hw ev xr rsr sr.
    destruct rsr as [|[| | | |lk| |] rsr]; try discriminate hw.
    destruct (cbn_env_var_sound lo G n e (CbnRSk stk :: rs) st xr (CbnRSk lk :: rsr) sr tc
                hokt hsusp ev)
      as (lov & Gv & tv1 & hrenv & hokv & hslotv & hcredv).
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenv) as [hpk hrenv'].
    cbn [cbn_gpres] in hpk.
    exact (cbn_res_sound_pre G Gv rs rsr rs' s' v (mkApps tc sts) (mkApps tv1 sts) hrenv'
             (cbn_cred_mkApps tc tv1 sts hcredv)
             (IHs lov Gv xr lk sts tv1 rsr sr v rs' s' hokv hslotv (hpk _ hsts) hw)).
  Qed.

  (** A lambda: a value on an empty stack, else beta. *)
  Lemma cbn_whnf_lambda_sound k (IHw : cbn_whnf_sound_at (k tt)) lo G e c na A b stk sts tc rs s st
      v rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tLambda na A b ->
    cbn_g_susp G e (tLambda na A b) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hcok hsts hw. cbn_whnf_rule hw etick ect.
    destruct stk as [|xh stk'].
    - injection hw as <- <- <-. inversion hsts; subst.
      rewrite <- ect in hsusp.
      exact (cbn_res_sound_here lo G G rs rs st (CbnVLam e c) tc (cbn_gren_refl G rs) hokt
               (cbn_g_VLam G e c tc hsusp hcok)).
    - inversion hsts as [|x0 l0 txh sts' hsloth hslots']; subst.
      exact (cbn_beta_sound (k tt) IHw lo G e c na A b xh stk' txh sts' tc rs st v rs' s'
               hokt ect hsusp hcok hsloth hslots' hw).
  Qed.

  (** Zeta: the definition bound in the environment, then the body. *)
  Lemma cbn_whnf_letin_sound k (IHw : cbn_whnf_sound_at (k tt)) lo G e c na b T body stk sts tc rs s
      st v rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tLetIn na b T body ->
    cbn_g_susp G e (tLetIn na b T body) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hcok hsts hw. cbn_whnf_rule hw etick ect.
    destruct (cbn_g_susp_letin _ _ _ _ _ _ _ hsusp) as (d' & T' & B & htc & hsb & hletprop).
    assert (hc0 : cbn_cok G (cbn_child c 0 b))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    assert (hc2 : cbn_cok G (cbn_child c 2 body))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    cbn_dcall hw ea xa rsa sa.
    destruct rsa as [|[| |ee| | | |] [|[| | | |lk| |] rsa]]; try discriminate hw.
    destruct (cbn_arg_slot_sound lo G e (cbn_child c 0 b) (CbnRE e :: CbnRSk stk :: rs) st xa
                (CbnRE ee :: CbnRSk lk :: rsa) sa d' hokt hsb hc0 ea)
      as (loa & Ga & tb & hrena & hoka & hslota & hcreda).
    destruct (cbn_gren_cons _ _ _ _ _ _ hrena) as [hpe hrena1].
    destruct (cbn_gren_cons _ _ _ _ _ _ hrena1) as [hpk hrena2].
    cbn [cbn_gpres] in hpe, hpk.
    cbn_dcall hw eb xbnd rsb sb.
    destruct rsb as [|[| |ee2| | | |] [|[| | | |lk2| |] rsb]]; try discriminate hw.
    destruct (cbn_bind_sound loa Ga xa (cbn_child c 2 body) (CbnRE ee :: CbnRSk lk :: rsa) sa xbnd
                (CbnRE ee2 :: CbnRSk lk2 :: rsb) sb tb hoka hslota
                (cbn_gren_cok _ _ _ _ _ hrena hc2) eb)
      as (lob & Gb & hrenb & hokb & hslotb).
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenb) as [hpe2 hrenb1].
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenb1) as [hpk2 hrenb2].
    cbn [cbn_gpres] in hpe2, hpk2.
    destruct (cbn_g_susp_letin Gb ee2 na b T body tc
                (cbn_genv_susp _ _ _ _ _ _ (cbn_genv_trans _ _ _ _ _ _ hpe hpe2) hsusp))
      as (d'2 & T'2 & B2 & htc2 & hsb2 & hletprop2).
    assert (heqlet : tLetIn na d' T' B = tLetIn na d'2 T'2 B2)
      by (rewrite <- htc; exact htc2).
    inversion heqlet; subst d'2 T'2 B2.
    subst tc.
    refine (cbn_res_sound_pre G Gb rs rsb rs' s' v _ (mkApps (subst [tb] 0 B) sts)
              (cbn_gren_trans _ _ _ _ _ _ hrena2 hrenb2) _
              (IHw lob Gb (cbn_env_push xbnd ee2) (cbn_child c 2 body) lk2 sts (subst [tb] 0 B)
                 rsb sb v rs' s' hokb (hletprop2 xbnd tb hslotb)
                 (cbn_gren_cok _ _ _ _ _ hrenb (cbn_gren_cok _ _ _ _ _ hrena hc2))
                 (hpk2 _ (hpk _ hsts)) hw)).
    apply cbn_cred_mkApps.
    apply (cbn_cred_trans (tLetIn na d' T' B) (tLetIn na tb T' B) (subst [tb] 0 B)).
    - exact (cbn_cred_letin na d' tb T' B hcreda).
    - apply cbn_cred_one. apply red_zeta.
  Qed.

  (** An application: the argument in a slot, pushed on the stack. *)
  Lemma cbn_whnf_app_sound k (IHw : cbn_whnf_sound_at (k tt)) lo G e c f arg stk sts tc rs s st v
      rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tApp f arg ->
    cbn_g_susp G e (tApp f arg) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hcok hsts hw. cbn_whnf_rule hw etick ect.
    destruct (cbn_g_susp_app _ _ _ _ _ hsusp) as (uf & ua & htc & hsf & hsa).
    assert (hc1 : cbn_cok G (cbn_child c 1 arg))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    assert (hc0f : cbn_cok G (cbn_child c 0 f))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    cbn_dcall hw ea xr rsr sr.
    destruct rsr as [|[| |ee| | | |] [|[| | | |lk| |] rsr]]; try discriminate hw.
    destruct (cbn_arg_slot_sound lo G e (cbn_child c 1 arg) (CbnRE e :: CbnRSk stk :: rs) st xr
                (CbnRE ee :: CbnRSk lk :: rsr) sr ua hokt hsa hc1 ea)
      as (loa & Gv & ta & hrena & hoka & hslota & hcreda).
    destruct (cbn_gren_cons _ _ _ _ _ _ hrena) as [hpe hrena1].
    destruct (cbn_gren_cons _ _ _ _ _ _ hrena1) as [hpk hrena2].
    cbn [cbn_gpres] in hpe, hpk.
    subst tc.
    exact (cbn_res_sound_pre G Gv rs rsr rs' s' v _ (mkApps (tApp uf ta) sts) hrena2
             (cbn_cred_mkApps (tApp uf ua) (tApp uf ta) sts (cbn_cred_app_r uf ua ta hcreda))
             (IHw loa Gv ee (cbn_child c 0 f) (xr :: lk) (ta :: sts) uf rsr sr v rs' s' hoka
                (cbn_genv_susp _ _ _ _ _ _ hpe hsf) (cbn_gren_cok _ _ _ _ _ hrena hc0f)
                (cbn_g_slots_cons Gv xr lk ta sts hslota (hpk _ hsts)) hw)).
  Qed.

  (** A constant: delta; or, without a body, the primitive-operation rule or a neutral
    constant. *)
  Lemma cbn_whnf_const_sound k (IHf : cbn_force_sound_at (k tt)) (IHw : cbn_whnf_sound_at (k tt))
      lo G e c kn ui stk sts tc rs s st v
      rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tConst kn ui ->
    cbn_g_susp G e (tConst kn ui) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hcok hsts hw. cbn_whnf_rule hw etick ect.
    rewrite (cbn_g_susp_const _ _ _ _ _ hsusp).
    destruct (cbn_delta X_type X kn ui st) as [[[c'| ] sd]|w] eqn:ed; [| |discriminate hw].
    - (* the body of [kn] at [ui], by [cbn_delta_body] and [cbn_delta_red1] *)
      destruct (cbn_gk_memo _ _ _ hokt) as (hmi & _ & hcodes & hokb & _).
      destruct hmi as (hf & _ & _ & _ & hdo).
      destruct (cbn_delta_body X_type X Σ kn ui st sd c' hΣ hf hdo ed)
        as (cb & body & ce & hdecl & hb & hct & _ & hce & _ & _ & hci).
      assert (hclosed : closedn 0 c'.(cbn_c_term)).
      { rewrite hct. apply cbn_closed_inst_code.
        exact (declared_constant_closed_body Σ kn cb body wfΣ hdecl hb). }
      assert (hinst : forall cb0, abstract_env_lookup X kn = Some (ConstantDecl cb0) ->
                ui = [] -> #|polymorphic_instance cb0.(cst_universes)| = 0).
      { intros cb0 hl hu. subst ui.
        destruct hcok as [e0 [he0 hci0]].
        pose proof (cbn_code_inv_consts_okb Σ e0 c hci0 (hokb _ _ (hcodes _ _ he0))) as hco.
        rewrite ect in hco. cbn in hco.
        exact (cbn_inst_okb_nil Σ kn cb0 hco (cbn_lookup_env_of_abstract X_type X Σ kn _ hΣ hl)). }
      assert (hcredc : cbn_cred (tConst kn ui) (lift0 (lvl - nctx) c'.(cbn_c_term))).
      { rewrite (lift_closed (lvl - nctx) 0 c'.(cbn_c_term) hclosed).
        apply cbn_cred_one.
        exact (cbn_delta_red1 X_type X Σ cbn_ΓΔ kn ui st sd c' hΣ wfΣ hf hdo ed hinst). }
      pose proof (cbn_delta_gok lo G kn ui st (Some c') sd hokt ed) as hokd0.
      pose proof (proj1 (proj2 (proj2 (cbn_gk_memo _ _ _ hokd0)))) as hgd.
      pose (Gd := cbn_mkGhost (cbn_gm G) ((sd.(cbn_st_memo)).(cbn_m_codes))).
      assert (hxd : cbn_gext G Gd) by (split; [intros a1 t1 h; exact h|exact hgd]).
      assert (hokd : cbn_gok lo Gd sd).
      { apply (cbn_gok_recode lo G sd sd);
          [exact hokd0|reflexivity|reflexivity|reflexivity|exact hgd
          |exact (cbn_mok_widen _ _ (cbn_gk_memo _ _ _ hokd0))]. }
      assert (hcokc : cbn_cok Gd c') by (exists ce; split; [exact hce|exact hci]).
      assert (hsuspc : cbn_g_susp Gd cbn_env_empty c'.(cbn_c_term)
        (lift0 (lvl - nctx) c'.(cbn_c_term))).
      { unfold cbn_env_empty.
        replace (lift0 (lvl - nctx) c'.(cbn_c_term))
          with (subst [] 0 (lift (lvl - nctx + 0) 0 c'.(cbn_c_term)))
          by (rewrite subst_empty, Nat.add_0_r; reflexivity).
        exact (cbn_g_susp_intro Gd [] 0 0 c'.(cbn_c_term) [] (cbn_g_slots_nil Gd) eq_refl). }
      exact (cbn_res_sound_pre G Gd rs rs rs' s' v _ _ (cbn_gren_ext G Gd rs hxd)
               (cbn_cred_mkApps _ _ sts hcredc)
               (IHw lo Gd cbn_env_empty c' stk sts _ rs sd v rs' s' hokd hsuspc hcokc
                  (cbn_g_slots_mono G Gd hxd stk sts hsts) hw)).
    - (* no body: the primitive-operation rule, or a neutral constant *)
      pose proof (cbn_delta_gok lo G kn ui st None sd hokt ed) as hokd.
      cbv beta iota in hw.
      destruct (cbn_prim_step_of X_type X kn stk sd) as [|t rest|i x] eqn:ep.
      + (* no rule: a neutral constant *)
        exact (cbn_head_sound (k tt) lo G stk sts rs sd v rs' s'
          (CbnVNeu (CbnNConst (tConst kn ui))) _ hokd hsts
                 (fun G' sp ha => cbn_g_VNeuConst G' (tConst kn ui) sp sts ha) hw).
      + (* the operation fires: [red_prim_op] on the literals the arguments reduce to *)
        destruct (cbn_prim_step_fire kn stk sd t rest ep)
          as (p & ls & r & hop & hls & hden & hrb & ->).
        destruct (cbn_readback_term _ _ _ hrb) as (hcl & hhyg & hokt').
        destruct (cbn_gk_memo _ _ _ hokt) as ((_ & _ & _ & _ & hdo) & _).
        destruct (cbn_delta_axiom X_type X kn ui st sd hdo ed) as (cb & hl & hb).
        destruct (cbn_g_slots_firstn_skipn G (arity p) stk sts hsts) as [hfst hskp].
        destruct (cbn_new_entry X_type X t [] sd) as [c' s1] eqn:e1.
        destruct (cbn_new_entry_sound lo G t sd hokd hokt' (fun _ => hhyg))
          as (G1 & hx1 & hok1 & hcok1).
        rewrite e1 in hok1, hcok1. cbn [fst snd] in hok1, hcok1.
        assert (hct : c'.(cbn_c_term) = t).
        { pose proof (cbn_new_entry_term X_type X t [] sd) as h. rewrite e1 in h. exact h. }
        assert (hsusp1 : cbn_g_susp G1 cbn_env_empty c'.(cbn_c_term) t).
        { rewrite hct.
          pose proof (cbn_g_susp_intro G1 [] 0 0 t [] (cbn_g_slots_nil G1) eq_refl) as h.
          rewrite subst_empty, (lift_closed _ 0 t hcl) in h. exact h. }
        assert (hred : cbn_cred (mkApps (tConst kn ui) sts) (mkApps t (skipn (arity p) sts))).
        { assert (esp : sts = firstn (arity p) sts ++ skipn (arity p) sts)
            by (symmetry; apply firstn_skipn).
          rewrite esp at 1.
          eapply cbn_cred_trans;
            [exact (cbn_slot_lits_sound lo G sd _ _ ls (tConst kn ui) _ hokd hfst hls)|].
          rewrite mkApps_app. apply cbn_cred_mkApps. apply cbn_cred_one.
          eapply red_prim_op.
          - rewrite <- (abstract_prim_op_of_correct X kn Σ hΣ). exact hop.
          - exact (cbn_lookup_declared X_type X Σ kn cb hΣ hl).
          - exact hb.
          - exact hden.
          - rewrite <- cbn_readback_correct. exact hrb. }
        exact (cbn_res_sound_pre G G1 rs rs rs' s' v _ _ (cbn_gren_ext G G1 rs hx1) hred
                 (IHw lo G1 cbn_env_empty c' (skipn (arity p) stk) (skipn (arity p) sts) t rs s1
                    v rs' s' hok1 hsusp1 hcok1 (cbn_g_slots_mono G G1 hx1 _ _ hskp) hw)).
      + (* argument [i] first: put in a cell of the stack and forced, then the constant again,
           on a stack with the same reading *)
        pose proof (cbn_prim_step_force kn stk sd i x ep) as hnx.
        destruct (cbn_g_slots_nth _ _ _ _ _ hsts hnx) as (tx & htx & hgx).
        cbn_dcall hw ema a rsa sa.
        destruct (cbn_materialize_sound lo G x (CbnRSk stk :: rs) sd a rsa sa tx hokd hgx ema)
          as (loa & Ga & hrena & hoka & hGa).
        destruct rsa as [|[| | | |stka| |] rsa]; try discriminate hw.
        destruct (cbn_gren_cons _ _ _ _ _ _ hrena) as [hpka hrena1].
        cbn [cbn_gpres] in hpka.
        cbv beta iota in hw.
        assert (hstka : cbn_g_slots Ga (cbn_list_set stka i (CbnSAddr a)) sts).
        { rewrite <- (cbn_list_set_nth_id sts i tx htx).
          apply cbn_g_slots_list_set; [exact (hpka _ hsts)|]. constructor. exact hGa. }
        cbn_dcall hw ef vf rsf sf.
        destruct (IHf loa Ga a (CbnRSk (cbn_list_set stka i (CbnSAddr a)) :: rsa) sa vf rsf sf tx
                    hoka hGa ef)
          as (lof & Gf & uf & hrenf & hokf & hvf & hcredf).
        destruct rsf as [|[| | | |stkf| |] rsf]; try discriminate hw.
        destruct (cbn_gren_cons _ _ _ _ _ _ hrenf) as [hpkf hrenf1].
        cbn [cbn_gpres] in hpkf.
        cbv beta iota in hw.
        assert (hstkf : cbn_g_slots Gf stkf sts) by exact (hpkf _ hstka).
        assert (hren : cbn_gren G Gf rs rsf) by exact (cbn_gren_trans _ _ _ _ _ _ hrena1 hrenf1).
        destruct (cbn_value_is_lit vf).
        * (* a literal: the constant again *)
          assert (hcokf : cbn_cok Gf c)
            by exact (cbn_gren_cok _ _ _ _ _ hrenf (cbn_gren_cok _ _ _ _ _ hrena hcok)).
          assert (hsuspf : cbn_g_susp Gf cbn_env_empty c.(cbn_c_term) (tConst kn ui)).
          { rewrite ect.
            exact (cbn_g_susp_intro Gf [] 0 0 (tConst kn ui) [] (cbn_g_slots_nil Gf) eq_refl). }
          exact (cbn_res_sound_pre G Gf rs rsf rs' s' v _ _ hren (cbn_cred_refl _)
                   (IHw lof Gf cbn_env_empty c stkf sts (tConst kn ui) rsf sf v rs' s' hokf hsuspf
                      hcokf hstkf hw)).
        * (* not a literal: a neutral constant *)
          exact (cbn_res_sound_pre G Gf rs rsf rs' s' v _ _ hren (cbn_cred_refl _)
                   (cbn_head_sound (k tt) lof Gf stkf sts rsf sf v rs' s'
                      (CbnVNeu (CbnNConst (tConst kn ui))) _ hokf hstkf
                      (fun G' sp ha => cbn_g_VNeuConst G' (tConst kn ui) sp sts ha) hw)).
  Qed.

  (** A match: iota on a constructor, a stuck match on a neutral or stuck scrutinee. *)
  Lemma cbn_whnf_case_sound k (IHw : cbn_whnf_sound_at (k tt)) lo G e c ci p scrut brs stk sts tc rs
      s st v rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tCase ci p scrut brs ->
    cbn_g_susp G e (tCase ci p scrut brs) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hcok hsts hw. cbn_whnf_rule hw etick ect.
    assert (hcs : cbn_cok G (cbn_child c 0 scrut))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    destruct (cbn_g_susp_inv _ _ _ _ hsusp) as (ts & hts & hnv & htc).
    rewrite cbn_subst_lift_case in htc.
    cbn_dcall hw ews vs rss ss.
    destruct (IHw lo G e (cbn_child c 0 scrut) [] [] _ (CbnRE e :: CbnRSk stk :: rs) st vs rss ss
                hokt (cbn_g_susp_of_slots G e scrut ts hts hnv) hcs (cbn_g_slots_nil G) ews)
      as (lo1 & G1 & us & hren1 & hok1 & hvs & hcreds).
    destruct rss as [|[| |e2| | | |] [|[| | | |stk2| |] rss]]; try discriminate hw.
    destruct (cbn_gren_cons _ _ _ _ _ _ hren1) as [hpe hren1a].
    destruct (cbn_gren_cons _ _ _ _ _ _ hren1a) as [hpk hren1b].
    cbn [cbn_gpres] in hpe, hpk.
    pose proof hpe as (hnv2 & hgo2 & hsl2).
    assert (hts1 : cbn_g_slots G1 e2.(cbn_ev_vals) ts) by exact (hsl2 _ hts).
    assert (hsts1 : cbn_g_slots G1 stk2 sts) by exact (hpk _ hsts).
    cbv beta iota in hw.
    destruct vs as [h0 args|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|nn sp1|e1 c1|e1 c1 sp1];
      try discriminate hw.
    1: { (* CbnVCon: iota *)
       destruct h0 as [| | | | | | | | | |cind cn cu| | | | |]; try discriminate hw.
       lazymatch type of hw with
       | context [if cbn_inductive_eqb ?a ?b then _ else _] =>
         destruct (cbn_inductive_eqb a b) eqn:eind
       end; [|discriminate hw].
       apply cbn_inductive_eqb_eq in eind. subst cind.
       destruct (nth_error brs cn) as [br|] eqn:ebr; [|discriminate hw].
       lazymatch type of hw with
       | context [if ?b then _ else _] => destruct b eqn:eguard
       end; [|discriminate hw].
       apply andb_true_iff in eguard as [hassum hlen].
       apply eqb_eq in hlen. apply cbn_forallb_is_assum_ctx in hassum.
       destruct (cbn_g_value_VCon_inv _ _ _ _ hvs) as (targs & hus & hargs).
       pose proof (Forall2_skipn _ _ _ _ _ (ci_npar ci) hargs) as hcargs.
       assert (hlen' : #|skipn (ci_npar ci) args| = #|bcontext br|).
       { rewrite length_skipn, hlen, (assumption_context_length _ hassum). lia. }
       assert (htl : #|List.rev (skipn (ci_npar ci) targs)| = #|bcontext br|).
       { rewrite List.length_rev, (cbn_g_addrs_length _ _ _ hcargs). exact hlen'. }
       assert (hcb : cbn_cok G1 (cbn_child c (cbn_case_branch_step (N.of_nat cn)) br.(bbody))).
       { apply (cbn_gren_cok _ _ _ _ _ hren1). apply cbn_cok_child; [exact hcok|rewrite ect].
         apply cbn_cs_case_branch. rewrite Nat2N.id. exact ebr. }
       rewrite cbn_env_push_addrs_vals in hw.
       assert (hsb : cbn_g_susp G1
                 (cbn_mkEnv (map CbnSAddr (List.rev (skipn (ci_npar ci) args)) ++ e2.(cbn_ev_vals))
                    (#|skipn (ci_npar ci) args| + e2.(cbn_ev_nvals)) e2.(cbn_ev_goff))
                 br.(bbody)
                 (subst (List.rev (skipn (ci_npar ci) targs) ++ ts) 0
                    (lift (lvl - nctx + e.(cbn_ev_goff))
                       (#|skipn (ci_npar ci) args| + e.(cbn_ev_nvals)) br.(bbody)))).
       { rewrite <- hnv2, <- hgo2.
         refine (cbn_g_susp_of_slots G1 (cbn_mkEnv _ _ _) br.(bbody) _ _ _).
         - cbn [cbn_ev_vals]. apply cbn_g_slots_app.
           + apply cbn_g_slots_addrs. apply Forall2_rev. exact hcargs.
           + exact hts1.
         - cbn [cbn_ev_vals cbn_ev_nvals]. rewrite length_app, length_map, List.length_rev.
           rewrite hnv2, hnv, <- (cbn_g_slots_length _ _ _ hts), (cbn_g_slots_length _ _ _ hts1).
           reflexivity. }
       refine (cbn_res_sound_pre G G1 rs rss rs' s' v _ _ hren1b _
                 (IHw lo1 G1 _ (cbn_child c (cbn_case_branch_step (N.of_nat cn)) br.(bbody)) stk2
                   sts _
                    rss ss v rs' s' hok1 hsb hcb hsts1 hw)).
       apply cbn_cred_mkApps. rewrite htc.
       eapply cbn_cred_trans; [apply cbn_cred_case_c; exact hcreds|].
       rewrite hus. apply cbn_cred_one.
       match goal with
       | |- red1 _ _ (tCase ?ci0 ?p0 (mkApps (tConstruct _ _ _) ?targs0) _) ?t =>
         replace t with (iota_red ci0.(ci_npar) p0 targs0
                           (cbn_rbr ts (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals) br))
       end.
       - apply red_iota.
         + rewrite nth_error_map, ebr. reflexivity.
         + rewrite (cbn_g_addrs_length _ _ _ hargs). exact hlen.
       - rewrite cbn_iota_red_assum by exact hassum. unfold cbn_rbr; cbn [bbody bcontext].
         rewrite hlen', subst_app_simpl, htl. reflexivity.
    }
    (* CbnVStuckFix, CbnVNeu, CbnVStuck: a stuck match *)
    all: refine (cbn_res_sound_pre G G1 rs rss rs' s' v _ _ hren1b (cbn_cred_refl _)
                   (cbn_stuck_sound (k tt) lo1 G1 e2 stk2 sts rss ss v rs' s'
                      (fun e' sp => CbnVStuck e' c sp) _ hok1 hsts1 _ hw));
         intros G' e' sp hcx hpe' cbn_haddr;
         apply (cbn_g_VStuck G' e' c sp tc sts);
         [ rewrite ect; exact (cbn_genv_susp _ _ _ _ _ _
           (cbn_genv_trans _ _ _ _ _ _ hpe hpe') hsusp)
         | exact (cbn_cok_gcx _ _ hcx c (cbn_gren_cok _ _ _ _ _ hren1 hcok))
         | exact cbn_haddr ].
  Qed.

  (** A projection: the field of a constructor, a stuck projection on a neutral or stuck
    argument. *)
  Lemma cbn_whnf_proj_sound k (IHs : cbn_eval_slot_sound_at (k tt)) (IHw : cbn_whnf_sound_at (k tt))
      lo G e c pr arg stk sts tc rs s st v rs' s' :
    cbn_gok lo G st -> cbn_tick s = Some st -> c.(cbn_c_term) = tProj pr arg ->
    cbn_g_susp G e (tProj pr arg) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
    cbn_whnf X_type X Γ nctx (CbnFS k) e c stk rs s = CbnCOk (v, rs', s') ->
    cbn_res_sound G rs rs' s' v (mkApps tc sts).
  Proof.
    intros hokt etick ect hsusp hcok hsts hw. cbn_whnf_rule hw etick ect.
    assert (hca : cbn_cok G (cbn_child c 0 arg))
      by (apply cbn_cok_child; [exact hcok|rewrite ect; constructor]).
    destruct (cbn_g_susp_inv _ _ _ _ hsusp) as (ts & hts & hnv & htc).
    cbn_dcall hw ews vs rss ss.
    destruct (IHw lo G e (cbn_child c 0 arg) [] [] _ (CbnRE e :: CbnRSk stk :: rs) st vs rss ss
                hokt (cbn_g_susp_of_slots G e arg ts hts hnv) hca (cbn_g_slots_nil G) ews)
      as (lo1 & G1 & us & hren1 & hok1 & hvs & hcreds).
    destruct rss as [|[| |e2| | | |] [|[| | | |stk2| |] rss]]; try discriminate hw.
    destruct (cbn_gren_cons _ _ _ _ _ _ hren1) as [hpe hren1a].
    destruct (cbn_gren_cons _ _ _ _ _ _ hren1a) as [hpk hren1b].
    cbn [cbn_gpres] in hpe, hpk.
    assert (hsts1 : cbn_g_slots G1 stk2 sts) by exact (hpk _ hsts).
    cbv beta iota in hw.
    destruct vs as [h0 args|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|nn sp1|e1 c1|e1 c1 sp1];
      try discriminate hw.
    1: { (* CbnVCon: the projection rule *)
       destruct h0 as [| | | | | | | | | |cind cn cu| | | | |]; try discriminate hw.
       destruct cn as [|cn]; try discriminate hw.
       lazymatch type of hw with
       | context [if cbn_inductive_eqb ?a ?b then _ else _] =>
         destruct (cbn_inductive_eqb a b) eqn:eind
       end; [|discriminate hw].
       apply cbn_inductive_eqb_eq in eind. subst cind.
       destruct (nth_error args (proj_npars pr + proj_arg pr)) as [a|] eqn:ea;
         [|discriminate hw].
       destruct (cbn_g_value_VCon_inv _ _ _ _ hvs) as (targs & hus & hargs).
       destruct (cbn_g_addrs_nth _ _ _ _ _ hargs ea) as (ta & hta & hGa).
       refine (cbn_res_sound_pre G G1 rs rss rs' s' v _ _ hren1b _
                 (IHs lo1 G1 (CbnSAddr a) stk2 sts ta rss ss v rs' s' hok1
                    (cbn_g_slot_addr G1 a ta hGa) hsts1 hw)).
       apply cbn_cred_mkApps. rewrite htc.
       change (subst ts 0 (lift (lvl - nctx + cbn_ev_goff e) (cbn_ev_nvals e) (tProj pr arg)))
         with (tProj pr (subst ts 0 (lift (lvl - nctx + cbn_ev_goff e) (cbn_ev_nvals e) arg))).
       eapply cbn_cred_trans; [apply cbn_cred_proj_c; exact hcreds|].
       rewrite hus. apply cbn_cred_one. apply red_proj. exact hta.
    }
    (* CbnVStuckFix, CbnVNeu, CbnVStuck: a stuck projection *)
    all: refine (cbn_res_sound_pre G G1 rs rss rs' s' v _ _ hren1b (cbn_cred_refl _)
                   (cbn_stuck_sound (k tt) lo1 G1 e2 stk2 sts rss ss v rs' s'
                      (fun e' sp => CbnVStuck e' c sp) _ hok1 hsts1 _ hw));
         intros G' e' sp hcx hpe' cbn_haddr;
         apply (cbn_g_VStuck G' e' c sp tc sts);
         [ rewrite ect; exact (cbn_genv_susp _ _ _ _ _ _
           (cbn_genv_trans _ _ _ _ _ _ hpe hpe') hsusp)
         | exact (cbn_cok_gcx _ _ hcx c (cbn_gren_cok _ _ _ _ _ hren1 hcok))
         | exact cbn_haddr ].
  Qed.

  (** *** One step of each function *)

  Lemma cbn_force_step_sound k (IHw : cbn_whnf_sound_at (k tt)) : cbn_force_sound_at (CbnFS k).
  Proof.
    intros lo G a0 rs s v rs' s' t hok hGa he.
    cbv beta iota zeta delta [cbn_force] in he.
    destruct (cbn_heap_get a0 s) as [cl|] eqn:ehc; [|discriminate he].
    destruct (cbn_gk_cells _ _ _ hok a0 cl ehc) as [t1 [hGa1 hcell]].
    assert (t1 = t) by (rewrite hGa in hGa1; injection hGa1 as ->; reflexivity).
    subst t1.
    destruct cl as [vs n o c| vd | | b]; [| |discriminate he|discriminate he].
    - (* CbnCSusp: force, then write back *)
      destruct hcell as [hbusy|[u [hgc hcred]]]; [discriminate hbusy|].
      pose proof (cbn_g_cell_susp_inv _ _ _ _ _ _ hgc) as hsusp.
      pose proof (cbn_g_cell_susp_cok _ _ _ _ _ _ hgc) as hcok.
      destruct (cbn_heap_upd a0 CbnCBusy s) as [sb|] eqn:ebusy; [|discriminate he].
      cbn_dcall he ew vw rsw sw.
      destruct rsw as [|[ar| | | | | |] rsw]; try discriminate he.
      destruct (cbn_heap_upd ar (CbnCDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
      injection he as <- <- <-.
      assert (hokb : cbn_gok lo G sb) by exact (cbn_gok_heap_upd_busy lo G a0 s sb hok ebusy).
      destruct (IHw lo G (cbn_mkEnv vs n o) c [] [] u (CbnRA a0 :: rs) sb vw
                  (CbnRA ar :: rsw) sw hokb hsusp hcok (cbn_g_slots_nil G) ew)
        as (lo1 & G' & uw & hren & hokw & hvw & hcredw).
      destruct (cbn_gren_cons _ _ _ _ _ _ hren) as [hpa hren'].
      cbn [cbn_gpres] in hpa.
      assert (hG'a : G' ar = Some t) by exact (hpa t hGa).
      assert (hcred_t_uw : cbn_cred t uw) by exact (cbn_cred_trans t u uw hcred hcredw).
      exists lo1, G', uw. split; [exact hren'|].
      split; [exact (cbn_gok_heap_upd_done lo1 G' ar vw uw t sw sd hokw hG'a hvw
                       hcred_t_uw edone)|].
      split; [exact hvw|exact hcred_t_uw].
    - (* CbnCDone vd: the value is already there *)
      destruct hcell as [hbusy|[u [hgc hcred]]]; [discriminate hbusy|].
      injection he as <- <- <-.
      exists lo, G, u. split; [apply cbn_gren_refl|]. split; [exact hok|].
      split; [exact (cbn_g_cell_done_inv _ _ _ hgc)|exact hcred].
  Qed.

  Lemma cbn_eval_slot_step_sound k (IHf : cbn_force_sound_at (k tt))
    (IHw : cbn_whnf_sound_at (k tt))
      (IHa : cbn_apply_sound_at (k tt)) :
    cbn_eval_slot_sound_at (CbnFS k).
  Proof.
    intros lo G x stk sts tx rs s v rs' s' hok hslot hsts he.
    cbv beta iota zeta delta [cbn_eval_slot] in he.
    destruct x as [a|vs n o c].
    - (* CbnSAddr a: force then apply *)
      cbn_dcall he ef vf rsf sf.
      destruct rsf as [|[| | | |lk| |] rsf]; try discriminate he.
      destruct (IHf lo G a (CbnRSk stk :: rs) s vf (CbnRSk lk :: rsf) sf tx hok
                  (cbn_g_slot_addr_inv _ _ _ hslot) ef)
        as (lof & Gf & uf & hrenf & hokf & hvf & hcredf).
      destruct (cbn_gren_cons _ _ _ _ _ _ hrenf) as [hpk hrenf'].
      cbn [cbn_gpres] in hpk.
      exact (cbn_res_sound_pre G Gf rs rsf rs' s' v (mkApps tx sts) (mkApps uf sts) hrenf'
               (cbn_cred_mkApps tx uf sts hcredf)
               (IHa lof Gf vf lk sts uf rsf sf v rs' s' hokf hvf (hpk _ hsts) he)).
    - (* CbnSInl: whnf in place *)
      exact (IHw lo G (cbn_mkEnv vs n o) c stk sts tx rs s v rs' s' hok
               (cbn_g_slot_inl_inv _ _ _ _ _ _ hslot)
                 (cbn_g_slot_inl_cok _ _ _ _ _ _ hslot) hsts he).
  Qed.

  Lemma cbn_whnf_step_sound k (IHf : cbn_force_sound_at (k tt)) (IHs : cbn_eval_slot_sound_at (k tt))
      (IHw : cbn_whnf_sound_at (k tt)) (IHx : cbn_whnf_fix_sound_at (k tt)) :
    cbn_whnf_sound_at (CbnFS k).
  Proof.
    intros lo G e c stk sts tc rs s v rs' s' hok hsusp hcok hsts hw.
    destruct (cbn_whnf_tick _ _ _ _ _ _ _ hw) as [st etick].
    pose proof (cbn_gok_tick lo G s st hok etick) as hokt. clear hok.
    destruct (cbn_c_term c) as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|kn ui
                           |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
      eqn:ect.
    - exact (cbn_whnf_rel_sound k IHs lo G e c n stk sts tc rs s st v rs' s' hokt etick ect hsusp
               hsts hw).
    - (* tVar: no rule *) cbn_whnf_rule hw etick ect. discriminate hw.
    - (* tEvar: no rule *) cbn_whnf_rule hw etick ect. discriminate hw.
    - (* tSort *)
      cbn_whnf_rule hw etick ect. rewrite <- ect in hsusp.
      exact (cbn_open_sound lo G e c stk sts tc rs st v rs' s' hokt hsusp hcok hsts hw).
    - (* tProd *)
      cbn_whnf_rule hw etick ect. rewrite <- ect in hsusp.
      exact (cbn_open_sound lo G e c stk sts tc rs st v rs' s' hokt hsusp hcok hsts hw).
    - exact (cbn_whnf_lambda_sound k IHw lo G e c na A b stk sts tc rs s st v rs' s' hokt etick ect
               hsusp hcok hsts hw).
    - exact (cbn_whnf_letin_sound k IHw lo G e c na b T body stk sts tc rs s st v rs' s' hokt
               etick ect hsusp hcok hsts hw).
    - exact (cbn_whnf_app_sound k IHw lo G e c f arg stk sts tc rs s st v rs' s' hokt etick ect
               hsusp hcok hsts hw).
    - exact (cbn_whnf_const_sound k IHf IHw lo G e c kn ui stk sts tc rs s st v rs' s' hokt etick
               ect hsusp hcok hsts hw).
    - (* tInd *)
      cbn_whnf_rule hw etick ect. rewrite (cbn_g_susp_tind _ _ _ _ _ hsusp).
      exact (cbn_head_sound (k tt) lo G stk sts rs st v rs' s' (CbnVCon (tInd ind ui)) _ hokt hsts
               (fun G' sp ha => cbn_g_VCon G' (tInd ind ui) sp sts ha) hw).
    - (* tConstruct *)
      cbn_whnf_rule hw etick ect. rewrite (cbn_g_susp_construct _ _ _ _ _ _ hsusp).
      exact (cbn_head_sound (k tt) lo G stk sts rs st v rs' s'
        (CbnVCon (tConstruct ind n ui)) _ hokt
               hsts (fun G' sp ha => cbn_g_VCon G' (tConstruct ind n ui) sp sts ha) hw).
    - exact (cbn_whnf_case_sound k IHw lo G e c ci p scrut brs stk sts tc rs s st v rs' s' hokt
               etick ect hsusp hcok hsts hw).
    - exact (cbn_whnf_proj_sound k IHs IHw lo G e c pr arg stk sts tc rs s st v rs' s' hokt etick
               ect hsusp hcok hsts hw).
    - (* tFix *)
      cbn_whnf_rule hw etick ect.
      exact (IHx lo G e c mfix idx idx stk sts tc rs st v rs' s' hokt ect hsusp hcok hsts hw).
    - (* tCoFix: no rule *) cbn_whnf_rule hw etick ect. discriminate hw.
    - (* tPrim *)
      cbn_whnf_rule hw etick ect. rewrite <- ect in hsusp.
      exact (cbn_open_sound lo G e c stk sts tc rs st v rs' s' hokt hsusp hcok hsts hw).
  Qed.

  Lemma cbn_whnf_fix_step_sound k (IHf : cbn_force_sound_at (k tt))
    (IHw : cbn_whnf_sound_at (k tt)) :
    cbn_whnf_fix_sound_at (CbnFS k).
  Proof.
    intros lo G e c mfix idx0 idx stk sts tc rs s v rs' s' hok hcfix hsusp hcok hsts he.
    cbv beta iota zeta delta [cbn_whnf_fix] in he.
    destruct (nth_error mfix idx) as [def|] eqn:edef; [|discriminate he].
    destruct (cbn_g_susp_inv _ _ _ _ hsusp) as (ts & hts & hnv & htc).
    destruct (nth_error stk (rarg def)) as [x|] eqn:ex.
    2: { (* too few arguments: a fixpoint value *)
      exact (cbn_stuck_sound (k tt) lo G e stk sts rs s v rs' s'
        (fun e' sp => CbnVFix e' c idx sp) _
               hok hsts
               (fun G' e' sp hcx hpe cbn_haddr =>
                  cbn_g_VFix G' e' c mfix idx0 idx sp tc sts hcfix
                    (cbn_genv_susp _ _ _ _ _ _ hpe hsusp)
                    (cbn_cok_gcx _ _ hcx c hcok) cbn_haddr)
               he). }
    destruct (cbn_g_slots_nth _ _ _ _ _ hsts ex) as (tx & htx & hgx).
    assert (hrarg : rarg def < #|sts|).
    { apply nth_error_Some_length in htx. exact htx. }
    (* put the recursive argument in the heap *)
    cbn_dcall he ema a rsa sa.
    destruct (cbn_materialize_sound lo G x (CbnRE e :: CbnRSk stk :: rs) s a rsa sa tx hok hgx ema)
      as (loa & Ga & hrena & hoka & hGa).
    destruct rsa as [|[| |ea| | | |] [|[| | | |stka| |] rsa]]; try discriminate he.
    destruct (cbn_gren_cons _ _ _ _ _ _ hrena) as [hpea hrena1].
    destruct (cbn_gren_cons _ _ _ _ _ _ hrena1) as [hpka hrena2].
    cbn [cbn_gpres] in hpea, hpka.
    cbv beta iota in he.
    assert (hstka : cbn_g_slots Ga (cbn_list_set stka (rarg def) (CbnSAddr a)) sts).
    { rewrite <- (cbn_list_set_nth_id sts (rarg def) tx htx).
      apply cbn_g_slots_list_set; [exact (hpka _ hsts)|]. constructor. exact hGa. }
    (* force it *)
    cbn_dcall he ef vf rsf sf.
    destruct (IHf loa Ga a (CbnRE ea :: CbnRSk (cbn_list_set stka (rarg def) (CbnSAddr a)) :: rsa)
      sa vf rsf sf tx hoka hGa ef)
      as (lof & Gf & uf & hrenf & hokf & hvf & hcredf).
    destruct rsf as [|[| |e3| | | |] [|[| | | |stkf| |] rsf]]; try discriminate he.
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenf) as [hpef hrenf1].
    destruct (cbn_gren_cons _ _ _ _ _ _ hrenf1) as [hpkf hrenf2].
    cbn [cbn_gpres] in hpef, hpkf.
    cbv beta iota in he.
    assert (hstkf : cbn_g_slots Gf stkf sts) by exact (hpkf _ hstka).
    assert (hpe3 : cbn_genv G Gf e e3) by exact (cbn_genv_trans _ _ _ _ _ _ hpea hpef).
    assert (hcokf : cbn_cok Gf c)
      by exact (cbn_gren_cok _ _ _ _ _ hrenf (cbn_gren_cok _ _ _ _ _ hrena hcok)).
    destruct vf as [h0 args|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|nn sp1|e1 c1|e1 c1 sp1];
      try discriminate he.
    1: { (* CbnVCon: unfold the fixpoint *)
       destruct h0 as [| | | | | | | | | |cind cn cu| | | | |]; try discriminate he.
       destruct (cbn_g_value_VCon_inv _ _ _ _ hvf) as (targs & huf & hargs).
       cbn_dcall he ea2 a2 rs2 s2.
       assert (hhuf : cbn_ctx_hyg -> on_free_vars cbn_xpredT uf).
       { intros hc. rewrite huf. apply cbn_hyg_mkApps; [reflexivity|].
         exact (cbn_g_addrs_hyg Gf (cbn_gk_hyg _ _ _ hokf hc) _ _ hargs). }
       destruct (cbn_alloc_sound lof Gf _ uf _ sf a2 rs2 s2 hokf (cbn_g_cell_done Gf _ _ hvf) hhuf
                   ea2)
         as (lo2 & G2 & hren2 & hok2 & hGa2).
       destruct rs2 as [|[| |e4| | | |] [|[| | | |stk4| |] rs2]]; try discriminate he.
       destruct (cbn_gren_cons _ _ _ _ _ _ hren2) as [hpe2 hren2a].
       destruct (cbn_gren_cons _ _ _ _ _ _ hren2a) as [hpk2 hren2b].
       cbn [cbn_gpres] in hpe2, hpk2.
       cbv beta iota in he.
       pose proof (cbn_genv_trans _ _ _ _ _ _ hpe3 hpe2) as (hnv4 & hgo4 & hsl4).
       assert (hts4 : cbn_g_slots G2 e4.(cbn_ev_vals) ts) by exact (hsl4 _ hts).
       assert (hnv4' : e4.(cbn_ev_nvals) = #|e4.(cbn_ev_vals)|).
       { rewrite hnv4, hnv, <- (cbn_g_slots_length _ _ _ hts), (cbn_g_slots_length _ _ _ hts4).
         reflexivity. }
       assert (hcok2 : cbn_cok G2 c) by exact (cbn_gren_cok _ _ _ _ _ hren2 hcokf).
       cbn_dcall he ep e' rs3 s3.
       destruct (cbn_push_fix_cells_sound #|mfix| lo2 G2 e4 c mfix idx0 ts 0 e4 ts _ s2 e' rs3 s3
                   hok2 hcfix hcok2 hts4 hnv4' hts4 hnv4' ep)
         as (lo3 & G3 & hren3 & hok3 & hsl3 & hnv3 & hgoff3).
       destruct rs3 as [|[| | | |stk6| |] rs3]; try discriminate he.
       destruct (cbn_gren_cons _ _ _ _ _ _ hren3) as [hpk3 hren3b].
       cbn [cbn_gpres] in hpk3.
       cbv beta iota in he.
       assert (hstk6 : cbn_g_slots G3 stk6 (cbn_list_set sts (rarg def) uf)).
       { apply hpk3. apply cbn_g_slots_list_set; [exact (hpk2 _ hstkf)|].
         constructor. exact hGa2. }
       assert (hcb : cbn_cok G3 (cbn_child c (N.of_nat idx) def.(dbody))).
       { apply (cbn_gren_cok _ _ _ _ _ hren3). apply cbn_cok_child; [exact hcok2|rewrite hcfix].
         apply cbn_cs_fix. rewrite Nat2N.id. exact edef. }
       rewrite hgo4, hnv4 in hsl3. rewrite hgo4 in hgoff3.
       pose proof (cbn_g_susp_of_slots G3 e' def.(dbody) _ hsl3 hnv3) as hsb.
       (* the body read through the fixpoint cells is the unfolded body of [unfold_fix] *)
       rewrite hgoff3, hnv3, <- (cbn_g_slots_length _ _ _ hsl3), length_app, List.length_rev,
         length_map, length_seq, (cbn_g_slots_length _ _ _ hts), <- hnv in hsb.
       assert (hm : map (fun j => subst ts 0 (lift (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals)
                                               (tFix mfix j))) (seq 0 #|mfix|)
                    = map (tFix (cbn_rfix ts (lvl - nctx + cbn_ev_goff e) (cbn_ev_nvals e) mfix))
                        (seq 0 #|mfix|))
         by (apply map_ext; intros j; apply cbn_rfix_eq).
       rewrite hm in hsb.
       refine (cbn_res_sound_pre G G3 rs rs3 rs' s' v _ _
                 (cbn_gren_trans _ _ _ _ _ _ hrena2 (cbn_gren_trans _ _ _ _ _ _ hrenf2
                    (cbn_gren_trans _ _ _ _ _ _ hren2b hren3b))) _
                 (IHw lo3 G3 e' (cbn_child c (N.of_nat idx) def.(dbody))
                    stk6 (cbn_list_set sts (rarg def) uf) _ rs3 s3 v rs' s' hok3 hsb hcb hstk6 he)).
       rewrite htc, cbn_rfix_eq.
       eapply cbn_cred_trans; [exact (cbn_cred_mkApps_list_set _ _ _ _ _ htx hcredf)|].
       apply cbn_cred_one. rewrite huf.
       eapply red_fix.
       - exact (cbn_unfold_fix_rfix ts (lvl - nctx + cbn_ev_goff e) (cbn_ev_nvals e) mfix
         idx def edef).
       - apply cbn_is_constructor_list_set. exact hrarg.
    }
    (* CbnVStuckFix, CbnVNeu, CbnVStuck: a stuck fixpoint *)
    all: refine (cbn_res_sound_pre G Gf rs rsf rs' s' v _ _
      (cbn_gren_trans _ _ _ _ _ _ hrena2 hrenf2)
                   (cbn_cred_refl _)
                   (cbn_stuck_sound (k tt) lof Gf e3 stkf sts rsf sf v rs' s'
                      (fun e' sp => CbnVStuckFix e' c idx sp) _ hokf hstkf _ he));
         intros G' e' sp hcx hpe' cbn_haddr;
         exact (cbn_g_VStuckFix G' e' c mfix idx0 idx sp tc sts hcfix
                  (cbn_genv_susp _ _ _ _ _ _ (cbn_genv_trans _ _ _ _ _ _ hpe3 hpe') hsusp)
                  (cbn_cok_gcx _ _ hcx c hcokf) cbn_haddr).
  Qed.

  Lemma cbn_apply_step_sound k (IHw : cbn_whnf_sound_at (k tt))
    (IHx : cbn_whnf_fix_sound_at (k tt)) :
    cbn_apply_sound_at (CbnFS k).
  Proof.
    intros lo G vv stk sts tv rs s w rs' s' hok hv hsts he.
    cbv beta iota zeta delta [cbn_apply] in he.
    destruct stk as [|xh stk'].
    - (* empty stack: the value itself *)
      injection he as <- <- <-. inversion hsts; subst.
      exact (cbn_res_sound_here lo G G rs rs s vv tv (cbn_gren_refl G rs) hok hv).
    - destruct vv as [h sp|e c|e c i args|e c i sp|nn sp|e c|e c sp].
      2: { (* CbnVLam: beta *)
         pose proof (cbn_g_value_VLam_inv _ _ _ _ hv) as hsusp.
         pose proof (cbn_g_value_VLam_cok _ _ _ _ hv) as hcok.
         destruct (cbn_c_term c) as [n|vr|ev earg|srt|na A B|na A b|na bd T bo|f arg|k0 ui
                                |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm]
           eqn:ect; try discriminate he.
         inversion hsts as [|x0 l0 txh sts' hsloth hslots']; subst.
         exact (cbn_beta_sound (k tt) IHw lo G e c na A b xh stk' txh sts' tv rs s w rs' s' hok ect
                  hsusp hcok hsloth hslots' he). }
      2: { (* CbnVFix: the fixpoint applied to its spine, then to the stack *)
         destruct (cbn_g_value_VFix_inv _ _ _ _ _ _ hv)
           as (mfix0 & idx0 & h & ts & hc0 & hsf & hcok & hadd & htv).
         rewrite hc0 in he.
         subst tv. rewrite <- mkApps_app.
         exact (IHx lo G e c mfix0 idx0 i (map CbnSAddr args ++ xh :: stk') (ts ++ sts) h
                  rs s w rs' s' hok hc0 hsf hcok
                  (cbn_g_slots_app G _ _ _ _ (cbn_g_slots_addrs G _ _ hadd) hsts) he). }
      4: { (* CbnVOpen: cannot be applied *) discriminate he. }
      (* CbnVCon, CbnVStuckFix, CbnVNeu, CbnVStuck: the stack goes into the spine *)
      all: cbn_dcall he em sp2 rsm sm;
           destruct rsm as [|[| | |vc| | |] rsm]; try discriminate he;
           destruct (cbn_add_spine vc sp2) as [vres|] eqn:eadd; [|discriminate he];
           injection he as <- <- <-;
           destruct (cbn_mat_all_sound (k tt) lo G (xh :: stk') sts _ s sp2 _ sm hok hsts em)
             as (lom & G' & hrenm & hokm & haddrm);
           destruct (cbn_gren_cons _ _ _ _ _ _ hrenm) as [hpv hrenm1];
           cbn [cbn_gpres] in hpv;
           exact (cbn_res_sound_here lom G G' rs rsm sm vres (mkApps tv sts) hrenm1 hokm
                    (cbn_g_value_add_spine _ _ _ _ _ _ (hpv _ hv) haddrm eadd)).
  Qed.

  (** At fuel [CbnFO] every call fails, except [cbn_apply] with an empty stack. *)
  Lemma cbn_machine_sound_FO :
    cbn_force_sound_at CbnFO /\ cbn_eval_slot_sound_at CbnFO /\ cbn_whnf_sound_at CbnFO /\
      cbn_whnf_fix_sound_at CbnFO
    /\ cbn_apply_sound_at CbnFO.
  Proof.
    split; [|split; [|split; [|split]]].
    - intros lo G a rs s v rs' s' t hok hGa he. cbn [cbn_force] in he. discriminate he.
    - intros lo G x stk sts tx rs s v rs' s' hok hx hsts he.
      cbn [cbn_eval_slot] in he. discriminate he.
    - intros lo G e c stk sts tc rs s v rs' s' hok hsusp hcok hsts he.
      cbn [cbn_whnf] in he. discriminate he.
    - intros lo G e c mfix idx0 idx stk sts tc rs s v rs' s' hok hcfix hsusp hcok hsts he.
      cbn [cbn_whnf_fix] in he. discriminate he.
    - intros lo G v stk sts tv rs s w rs' s' hok hv hsts he.
      cbn [cbn_apply] in he. destruct stk as [|y stk]; [|discriminate he].
      injection he as <- <- <-. inversion hsts; subst.
      exact (cbn_res_sound_here lo G G rs rs s v tv (cbn_gren_refl G rs) hok hv).
  Qed.

  Lemma cbn_machine_sound : forall d,
    (forall lo G a rs s v rs' s' t,
        cbn_gok lo G s -> G a = Some t ->
        cbn_force X_type X Γ nctx d a rs s = CbnCOk (v, rs', s') ->
        exists lo' G' u, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_value G' v u /\
          cbn_cred t u)
    /\ (forall lo G x stk sts tx rs s v rs' s',
        cbn_gok lo G s -> cbn_g_slot G x tx -> cbn_g_slots G stk sts ->
        cbn_eval_slot X_type X Γ nctx d x stk rs s = CbnCOk (v, rs', s') ->
        exists lo' G' u, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_value G' v u
                         /\ cbn_cred (mkApps tx sts) u)
    /\ (forall lo G e c stk sts tc rs s v rs' s',
        cbn_gok lo G s -> cbn_g_susp G e c.(cbn_c_term) tc -> cbn_cok G c ->
          cbn_g_slots G stk sts ->
        cbn_whnf X_type X Γ nctx d e c stk rs s = CbnCOk (v, rs', s') ->
        exists lo' G' u, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_value G' v u
                         /\ cbn_cred (mkApps tc sts) u)
    /\ (forall lo G e c mfix idx0 idx stk sts tc rs s v rs' s',
        cbn_gok lo G s -> c.(cbn_c_term) = tFix mfix idx0 ->
        cbn_g_susp G e (tFix mfix idx) tc -> cbn_cok G c -> cbn_g_slots G stk sts ->
        cbn_whnf_fix X_type X Γ nctx d e c mfix idx stk rs s = CbnCOk (v, rs', s') ->
        exists lo' G' u, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_value G' v u
                         /\ cbn_cred (mkApps tc sts) u)
    /\ (forall lo G v stk sts tv rs s w rs' s',
        cbn_gok lo G s -> cbn_g_value G v tv -> cbn_g_slots G stk sts ->
        cbn_apply X_type X Γ nctx d v stk rs s = CbnCOk (w, rs', s') ->
        exists lo' G' u, cbn_gren G G' rs rs' /\ cbn_gok lo' G' s' /\ cbn_g_value G' w u
                         /\ cbn_cred (mkApps tv sts) u).
  Proof.
    intros d. induction d as [|k ih]; [exact cbn_machine_sound_FO|].
    destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
    exact (conj (cbn_force_step_sound k IHw)
             (conj (cbn_eval_slot_step_sound k IHf IHw IHa)
                (conj (cbn_whnf_step_sound k IHf IHs IHw IHx)
                   (conj (cbn_whnf_fix_step_sound k IHf IHw) (cbn_apply_step_sound k IHw IHx))))).
  Qed.

End Eval.

(** ** Satisfying instances of the hypotheses of [cbn_machine_sound]

  Every section hypothesis of [Section Eval] has a proved instance:
  - [wfΣ] and [hΣ]: for EVERY abstract environment [X] there is a [Σ] it stands for, and that
    [Σ] is well formed ([cbn_eval_env_instance]); both are fields of [abstract_env_impl].
  - [hΔ], [hnctx], [hlvl], [const_instance_ok] and the premise [cbn_ctx_hyg] of the hygiene
    clauses: for the empty context at level 0 with [Δ = []] ([cbn_eval_ctx_instance_nil]); for a
    well-formed context at its own length, [cbn_eval_section_instance] of
    [PCUICCallByNeedSoundHookFrame] (the hook's case).
  - [cbn_gok]: [cbn_gok_init], and [PCUICCallByNeedSoundLevel.cbn_run_s2_gok] for the state the hook
    starts in. *)

(** Satisfying instance of the hypotheses [wfΣ] and [hΣ] of [Section Eval]. *)
Lemma cbn_eval_env_instance {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1) :
  ∥ ∑ Σ : global_env_ext, abstract_env_ext_rel X Σ × wf Σ ∥.
Proof.
  destruct (abstract_env_ext_exists X) as [[Σ hΣ]].
  destruct (abstract_env_ext_wf X hΣ) as [[hw _]].
  constructor. exists Σ. split; [exact hΣ|exact hw].
Qed.

(** Satisfying instance of the hypotheses [hΔ], [hnctx], [hlvl] and [const_instance_ok] of
  [Section Eval], and of the premise [cbn_ctx_hyg], at the empty context. *)
Lemma cbn_eval_ctx_instance_nil (Σ : global_env_ext) :
  #|([] : context)| = 0 - 0 /\ 0 = #|([] : context)| /\ 0 <= 0
  /\ (forall j decl b, nth_error ([] : context) j = Some decl -> decl.(decl_body) = Some b ->
        cbn_consts_okb Σ b = true)
  /\ cbn_ctx_hyg [].
Proof.
  split; [reflexivity|]. split; [reflexivity|]. split; [constructor|].
  split; intros j decl b h; destruct j; discriminate h.
Qed.
