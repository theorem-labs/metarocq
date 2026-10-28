(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat Nnat Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICReduction
  PCUICTyping PCUICUnivSubst PCUICClosed PCUICClosedTyp PCUICInduction PCUICSigmaCalculus
  PCUICContexts.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx PCUICCallByNeedSoundMemo
  PCUICCallByNeedSoundHook.

Import CanonicalTries.

(** * The evaluator of the call-by-need machine against PCUIC reduction (BET-298, step 2d)

  [whnf], [whnf_fix], [eval_slot], [force] and [apply] turn a suspension into a weak-head
  value. This file proves that the term the input stands for reduces, in PCUIC, to the term
  the value stands for, for every rule the machine has: beta, zeta, rel (including the
  forcing of a cell and its write-back), delta, iota, fixpoint unfolding, projection, and
  the stuck forms of a match, a projection and a fixpoint whose scrutinee or recursive
  argument is neutral or stuck. The machine has no rule for a cofixpoint, a [tVar] or a
  [tEvar]: on those [whnf] gives up ([CFail WShape]), so there is nothing to prove.

  ** What a structure stands for

  The read-back used here is *not* [repr_value] of [PCUICCallByNeedSound]: it is a ghost
  read-back [g_value], which reads an address [a] as the term [G a] of a ghost map
  [G : haddr -> option term] instead of following the heap. The two differ exactly on a cell
  the machine has already forced: [repr] reads such a cell as the value now in it, the ghost
  map keeps the term the cell was allocated for.

  The ghost map is what makes the write-back compositional, and it is the "ghost allocation
  term" of REPORT-BET298 §4.3. With [repr], forcing an address changes what *every* other
  structure that names it stands for: the reading of a cell is a term built out of the
  readings of the addresses below it, so a write-back turns a third party's reading [u] into
  some reduct [u']. To put a value [v] back into a forced cell one then has to know that [v]
  is a reduct of the cell's reading *as it is when the forcing ends*, not of its reading when
  the forcing started, and the two are only joinable, not ordered: that is a confluence
  argument, not an induction. With the ghost map, [G] only ever grows at fresh addresses
  ([gext]), so a write-back changes no reading at all, and the heap invariant [gk_cells] —
  "the cell at [a] stands for a reduct of [G a]" — is restored at the forced address by
  transitivity and is untouched everywhere else.

  The fixpoint rule is why the machine puts the forced recursive argument in a *fresh*
  cell: the old cell still stands for the unforced argument, and the unfolded body must see
  the constructor the guard tested, or its result is not a reduct of the input.

  ** What is assumed

  The theorem's hypotheses, each a premise of [machine_sound]:
  - [hnctx], [hlvl]: what the machine's comment says of its own parameters.
  - [const_instance_ok]: every constant a let-body of [Γ] names carries an instance of the
    right length ([PCUICCallByNeedSoundHook.consts_okb]). [delta_red1] needs this of the
    constant it unfolds, because the machine's [inst_code []] is the identity where PCUIC
    substitutes the empty instance ([inst_code_nil_ne_subst_instance]). For the entries of
    the code table it is part of the state invariant [gok]: a constant body has it by
    [declared_constant_consts_okb], an input term by [typing_consts_okb']. Only the
    let-bodies of the context come from outside the table.

  The memo facts are proved, not assumed: [gok] carries [memo_inv] of
  [PCUICCallByNeedSoundMemo] and [memo_ok] of [PCUICCallByNeedSoundCtx], and every reading
  of a code says the code is in the code table ([cok]), which is what [once_body] needs to
  keep its cache sound. [wfΣ] and [hΣ] are the hook's own hypotheses: [Σ] is well formed
  and is the environment [X] stands for.

  ** Collections

  A run may collect, under [stress] or when [st_room] is spent. A collection renames every
  address, so the ghost a call ends with is not an extension of the one it started with:
  every clause of [machine_sound] says instead that the roots come back renamed and stand,
  under the new ghost, for what they stood for ([gren]). The ghost of the new heap is built
  along the collector's walk, at each fresh address from the ghost term of the old address
  copied there ([collect_ghost]); it is a ghost renaming in the sense of
  [PCUICCallByNeedSoundGC.root_pres], and it needs nothing of the collector beyond its
  invariant [gc_inv]. *)

Lemma forallb_map_All {A B} (f : A -> B) (p : B -> bool) (q : A -> bool) (l : list A) :
  All (fun x => p (f x) = q x) l -> forallb p (map f l) = forallb q l.
Proof. induction 1 as [|x l hx hl ih]; cbn; [reflexivity|]. rewrite hx, ih. reflexivity. Qed.

Lemma Forall_app_g {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  induction 1 as [|x l hx hl ih]; simpl; intros h2;
    [exact h2|constructor; [exact hx|exact (ih h2)]].
Qed.

(** ** Instances, closedness and the instance condition on the codes of the table *)

(** [consts_okb] reads only instance lengths, which [subst_instance] keeps. *)
Lemma consts_subst_instance (Σ : global_env) (u : Instance.t) (t : term) :
  consts_okb Σ (subst_instance u t) = consts_okb Σ t.
Proof.
  induction t using term_forall_list_ind; cbn; try reflexivity.
  all: try solve [rewrite IHt1, IHt2, IHt3; reflexivity].
  all: try solve [rewrite IHt1, IHt2; reflexivity].
  all: try solve [rewrite IHt; reflexivity].
  all: try solve [unfold inst_okb; destruct (lookup_env Σ _) as [[]|]; try reflexivity;
                  now rewrite ?length_map, ?subst_instance_instance_length].
  all: try solve [apply forallb_map_All; exact X].
  all: try solve [apply forallb_map_All; eapply All_impl; [exact X|];
                  intros d [h1 h2]; cbn; rewrite h1, h2; reflexivity].
  destruct X as (hpar & _ & hret). rewrite IHt, hret, (forallb_map_All _ _ _ _ hpar).
  erewrite (forallb_map_All _ (fun br => consts_okb Σ (bbody br))); [reflexivity|].
  eapply All_impl; [exact X0|]. intros br [_ hb]. exact hb.
Qed.

Lemma consts_inst_code (Σ : global_env) (u : Instance.t) (t : term) :
  consts_okb Σ (inst_code u t) = consts_okb Σ t.
Proof.
  destruct u as [|l u]; [reflexivity|]. rewrite inst_code_cons. apply consts_subst_instance.
Qed.

Lemma closed_inst_code (u : Instance.t) (t : term) : closedn 0 t -> closedn 0 (inst_code u t).
Proof.
  intros h. destruct u as [|l u]; [exact h|]. rewrite inst_code_cons, closedn_subst_instance.
  exact h.
Qed.

(** ** Fixpoints: the reading of a [tFix] code and its unfolding *)

Lemma fix_subst_seq (l : mfixpoint term) :
  fix_subst l = List.rev (map (tFix l) (seq 0 #|l|)).
Proof.
  unfold fix_subst. generalize #|l| as n. induction n as [|n ih]; [reflexivity|].
  transitivity (tFix l n :: List.rev (map (tFix l) (seq 0 n))).
  - simpl. f_equal. exact ih.
  - rewrite seq_S, map_app, rev_app_distr. reflexivity.
Qed.

(** The fixpoints of a [tFix] code read through an environment: [subst ts 0] of
  [lift K n] of each definition, under the [#|mfix|] binders of the block. *)
Definition rfix (ts : list term) (K n : nat) (mfix : mfixpoint term) : mfixpoint term :=
  map (map_def (subst ts 0) (subst ts (#|mfix| + 0)))
    (map (map_def (lift K n) (lift K (#|mfix| + n))) mfix).

Lemma rfix_eq ts K n mfix j : subst ts 0 (lift K n (tFix mfix j)) = tFix (rfix ts K n mfix) j.
Proof. cbn [lift subst]. unfold rfix. rewrite length_map. reflexivity. Qed.

Lemma rfix_length ts K n mfix : #|rfix ts K n mfix| = #|mfix|.
Proof. unfold rfix. now rewrite !length_map. Qed.

(** Unfolding the read fixpoint is reading its body in the environment extended by the
  [#|mfix|] fixpoints, the last one first: exactly the environment [push_fix_cells] builds. *)
Lemma unfold_fix_rfix ts K n mfix idx d :
  nth_error mfix idx = Some d ->
  unfold_fix (rfix ts K n mfix) idx
  = Some (rarg d, subst (List.rev (map (tFix (rfix ts K n mfix)) (seq 0 #|mfix|)) ++ ts) 0
                    (lift K (#|mfix| + n) (dbody d))).
Proof.
  intros hd. unfold unfold_fix.
  assert (hn : nth_error (rfix ts K n mfix) idx
               = Some (map_def (subst ts 0) (subst ts (#|mfix| + 0))
                         (map_def (lift K n) (lift K (#|mfix| + n)) d))).
  { unfold rfix. rewrite !nth_error_map, hd. reflexivity. }
  rewrite hn. cbn [rarg dbody map_def]. rewrite fix_subst_seq, rfix_length.
  rewrite subst_app_simpl, List.length_rev, length_map, length_seq, Nat.add_0_r.
  reflexivity.
Qed.

(** ** Setting one element of a list *)

Lemma list_set_length {A} (l : list A) n x : #|list_set l n x| = #|l|.
Proof.
  revert n. induction l as [|y l ih]; intros [|n]; cbn; try reflexivity. now rewrite ih.
Qed.

Lemma nth_error_list_set_same {A} (l : list A) n x :
  n < #|l| -> nth_error (list_set l n x) n = Some x.
Proof.
  revert n. induction l as [|y l ih]; intros [|n] h; cbn in *; try lia; try reflexivity.
  apply ih. lia.
Qed.

Lemma list_set_nth_id {A} (l : list A) n x : nth_error l n = Some x -> list_set l n x = l.
Proof.
  revert n. induction l as [|y l ih]; intros [|n] h; cbn in *; try discriminate.
  - injection h as ->. reflexivity.
  - now rewrite (ih n h).
Qed.

Lemma list_set_list_set {A} (l : list A) n x y : list_set (list_set l n x) n y = list_set l n y.
Proof.
  revert n. induction l as [|z l ih]; intros [|n]; cbn; try reflexivity. now rewrite ih.
Qed.

Lemma All2_red_list_set {cf : checker_flags} (Σ : global_env_ext) Γ (l : list term) n t u :
  nth_error l n = Some t -> red Σ Γ t u -> All2 (red Σ Γ) l (list_set l n u).
Proof.
  revert n. induction l as [|y l ih]; intros [|n] h hr; cbn in *; try discriminate.
  - injection h as ->. constructor; [exact hr|]. apply All2_same. intros; apply refl_red.
  - constructor; [apply refl_red|]. exact (ih n h hr).
Qed.

Lemma is_constructor_list_set n (l : list term) i k u ts :
  n < #|l| -> is_constructor n (list_set l n (mkApps (tConstruct i k u) ts)) = true.
Proof.
  intros h. unfold is_constructor. rewrite nth_error_list_set_same by exact h.
  unfold isConstruct_app. rewrite decompose_app_mkApps by reflexivity. reflexivity.
Qed.

(** ** Matches: the reading of a [tCase] code and its iota step *)

Lemma forallb_is_assum_ctx (ctx : context) :
  forallb is_assum ctx = true -> assumption_context ctx.
Proof.
  induction ctx as [|[na [b|] ty] ctx ih]; cbn; intros h; [constructor|discriminate|].
  constructor. apply ih. exact h.
Qed.

Lemma assumption_context_map_context (f : term -> term) (Γ : context) :
  assumption_context Γ -> assumption_context (map_context f Γ).
Proof. induction 1; cbn; constructor; assumption. Qed.

(** A branch whose context has no let-in needs no [expand_lets]. *)
Lemma iota_red_assum npar p args br :
  assumption_context br.(bcontext) ->
  iota_red npar p args br = subst (List.rev (skipn npar args)) 0 br.(bbody).
Proof.
  intros h. unfold iota_red. rewrite expand_lets_assumption_context; [reflexivity|].
  unfold inst_case_branch_context, inst_case_context.
  apply assumption_context_fold. apply assumption_context_map_context. exact h.
Qed.

(** A branch read through an environment: its body under the branch's own binders. *)
Definition rbr (ts : list term) (K n : nat) (br : branch term) : branch term :=
  {| bcontext := br.(bcontext);
     bbody := subst ts #|br.(bcontext)| (lift K (#|br.(bcontext)| + n) br.(bbody)) |}.

Lemma subst_lift_case ts K n ci p scrut brs :
  subst ts 0 (lift K n (tCase ci p scrut brs))
  = tCase ci (map_predicate_k id (subst ts) 0 (map_predicate_k id (lift K) n p))
      (subst ts 0 (lift K n scrut)) (map (rbr ts K n) brs).
Proof.
  cbn [lift subst]. f_equal. rewrite map_map. apply map_ext. intros br.
  unfold map_branch_k, rbr, id. cbn. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma forallb_nth_some {A} (p : A -> bool) (l : list A) n x :
  forallb p l = true -> nth_error l n = Some x -> p x = true.
Proof. intros h hn. apply nth_error_In in hn. rewrite forallb_forall in h. exact (h x hn). Qed.

(** [consts_okb] recurses through every subterm [code_inv]'s step takes, so a code of an
  entry whose instantiated term satisfies it satisfies it too. *)
Lemma code_inv_consts_okb (Σ : global_env) (e : code_entry) (c : code) :
  code_inv e c -> consts_okb Σ (inst_code e.(ce_inst) e.(ce_term)) = true ->
  consts_okb Σ c.(c_term) = true.
Proof.
  unfold code_inv; cbv zeta. intros [ks [_ ht]] hr. revert ht.
  generalize (c_term c) as t.
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
        exact (forallb_nth_some (fun br => consts_okb Σ br.(bbody)) _ _ _
                 ltac:(eassumption) Eb).
      * exact (forallb_nth_some (consts_okb Σ) _ _ _ ltac:(eassumption) ht).
      * injection ht as <-. assumption.
    + (* tProj *)
      destruct k as [|q]; cbn in ht; [injection ht as <-; assumption|discriminate ht].
    + (* tFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (forallb_nth_some
                    (fun d => consts_okb Σ d.(dtype) && consts_okb Σ d.(dbody)) _ _ _ h0 Ed)
        as hd.
      cbn in hd. apply andb_true_iff in hd. exact (proj2 hd).
    + (* tCoFix *)
      destruct (nth_error mfix _) as [d|] eqn:Ed; cbn in ht; [|discriminate ht].
      injection ht as <-.
      pose proof (forallb_nth_some
                    (fun d => consts_okb Σ d.(dtype) && consts_okb Σ d.(dbody)) _ _ _ h0 Ed)
        as hd.
      cbn in hd. apply andb_true_iff in hd. exact (proj2 hd).
Qed.

Section Eval.
  Context {cf : checker_flags}.
  Context (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat) (stress : bool).

  (** The environment the readings live in: [Γ] under [lvl - nctx] fresh variables. [Σ] is
     the well-formed environment the abstract one [X] stands for; the hook has both, and the
     delta rule needs them for the body it unfolds. *)
  Context (Σ : global_env_ext) (Δ : context) (lvl : nat).
  Hypothesis wfΣ : wf Σ.
  Hypothesis hΣ : abstract_env_ext_rel X Σ.
  Hypothesis hΔ : #|Δ| = lvl - nctx.

  Local Notation ΓΔ := (Γ ,,, Δ).

  (** Reduction, squashed: [red1] lives in [Type], the readings here in [Prop]. *)
  Definition cred (t u : term) : Prop := ∥ red Σ ΓΔ t u ∥.

  Lemma cred_refl t : cred t t.
  Proof. constructor. apply refl_red. Qed.

  Lemma cred_trans t u v : cred t u -> cred u v -> cred t v.
  Proof. intros [h1] [h2]. constructor. exact (red_trans _ _ _ _ _ h1 h2). Qed.

  Lemma cred_one t u : red1 Σ ΓΔ t u -> cred t u.
  Proof. intros h. constructor. exact (red1_red _ _ _ _ h). Qed.

  Lemma cred_mkApps t u ts : cred t u -> cred (mkApps t ts) (mkApps u ts).
  Proof. intros [h]. constructor. exact (red_mkApps_f _ _ _ h). Qed.

  Lemma cred_app_r f t u : cred t u -> cred (tApp f t) (tApp f u).
  Proof. intros [h]. constructor. exact (red_app_r _ _ _ h). Qed.

  Lemma cred_letin na d0 d1 T b : cred d0 d1 -> cred (tLetIn na d0 T b) (tLetIn na d1 T b).
  Proof.
    intros [h]. constructor.
    exact (red_letin na d0 d1 T T b b h (refl_red _ _ _) (refl_red _ _ _)).
  Qed.

  (** ** The ghost

    A ghost is a map [gm] from addresses to the terms their cells were allocated for, and a
    code table [gc]: the table every code of a reading is checked against. Both only grow
    ([gext]). *)

  Record ghost := mkGhost { gm : haddr -> option term; gc : PTree.t code_entry }.
  Coercion gm : ghost >-> Funclass.

  (** A code is in the table: its index holds an entry it satisfies [code_inv] for. *)
  Definition cok (G : ghost) (c : code) : Prop :=
    exists e, PTree.get c.(c_entry) (gc G) = Some e /\ code_inv e c.

  Lemma cok_child G c k t : cok G c -> child_step c.(c_term) k t -> cok G (child c k t).
  Proof.
    intros [e [he hi]] hs. exists e.
    split; [exact he|exact (code_inv_child_step e c k t hi hs)].
  Qed.

  (** ** The ghost read-back

    [G a] is the term the cell at [a] was allocated for. An inline suspension is read like
    [repr_susp]: the slots are read, then substituted into the code lifted over the
    environment's own variables. *)

  Inductive g_slot (G : ghost) : cbn_slot -> term -> Prop :=
  | g_slot_addr a t : G a = Some t -> g_slot G (SAddr a) t
  | g_slot_inl vals nvals goff c ts :
      g_slots G vals ts -> nvals = #|vals| -> cok G c ->
      g_slot G (SInl vals nvals goff c)
        (subst ts 0 (lift (lvl - nctx + goff) nvals c.(c_term)))

  with g_slots (G : ghost) : list cbn_slot -> list term -> Prop :=
  | g_slots_nil : g_slots G [] []
  | g_slots_cons x l t ts :
      g_slot G x t -> g_slots G l ts -> g_slots G (x :: l) (t :: ts).

  Scheme g_slot_min := Minimality for g_slot Sort Prop
  with g_slots_min := Minimality for g_slots Sort Prop.
  Combined Scheme g_slot_mutind from g_slot_min, g_slots_min.

  Inductive g_susp (G : ghost) : cbn_env -> term -> term -> Prop :=
  | g_susp_intro vals nvals goff t ts :
      g_slots G vals ts -> nvals = #|vals| ->
      g_susp G (mkEnv vals nvals goff) t (subst ts 0 (lift (lvl - nctx + goff) nvals t)).

  Definition g_addrs (G : ghost) (l : list haddr) (ts : list term) : Prop :=
    Forall2 (fun a t => G a = Some t) l ts.

  (** A fixpoint value reads like [rb_value]: fixpoint [i] of its [tFix] code, read through
    its environment, applied to its spine. *)
  Inductive g_value (G : ghost) : cbn_value -> term -> Prop :=
  | g_VCon h sp ts : g_addrs G sp ts -> g_value G (VCon h sp) (mkApps h ts)
  | g_VLam e c t : g_susp G e c.(c_term) t -> cok G c -> g_value G (VLam e c) t
  | g_VOpen e c t : g_susp G e c.(c_term) t -> cok G c -> g_value G (VOpen e c) t
  | g_VNeuVar l sp ts :
      g_addrs G sp ts -> g_value G (VNeu (NVar l) sp) (mkApps (tRel (lvl - S l)) ts)
  | g_VNeuConst h sp ts :
      g_addrs G sp ts -> g_value G (VNeu (NConst h) sp) (mkApps h ts)
  | g_VStuck e c sp h ts :
      g_susp G e c.(c_term) h -> cok G c -> g_addrs G sp ts ->
      g_value G (VStuck e c sp) (mkApps h ts)
  | g_VFix e c mfix idx i sp h ts :
      c.(c_term) = tFix mfix idx -> g_susp G e (tFix mfix i) h -> cok G c -> g_addrs G sp ts ->
      g_value G (VFix e c i sp) (mkApps h ts)
  | g_VStuckFix e c mfix idx i sp h ts :
      c.(c_term) = tFix mfix idx -> g_susp G e (tFix mfix i) h -> cok G c -> g_addrs G sp ts ->
      g_value G (VStuckFix e c i sp) (mkApps h ts).

  Inductive g_cell (G : ghost) : cbn_cell -> term -> Prop :=
  | g_cell_susp vals nvals goff c t :
      g_susp G (mkEnv vals nvals goff) c.(c_term) t -> cok G c ->
      g_cell G (CSusp vals nvals goff c) t
  | g_cell_done v t : g_value G v t -> g_cell G (CDone v) t.

  (** ** The ghost map only grows, and every reading survives *)

  Record gext (G G' : ghost) : Prop := mkGext {
    gx_map : forall a t, G a = Some t -> G' a = Some t;
    gx_codes : forall i e, PTree.get i (gc G) = Some e -> PTree.get i (gc G') = Some e }.
  Arguments gx_map {G G'} _ _ _ _.
  Arguments gx_codes {G G'} _ _ _ _.
  Coercion gx_map : gext >-> Funclass.

  Lemma gext_refl G : gext G G.
  Proof. split; intros; assumption. Qed.

  Lemma gext_trans G1 G2 G3 : gext G1 G2 -> gext G2 G3 -> gext G1 G3.
  Proof.
    intros h1 h2. split.
    - intros a t h. exact (gx_map h2 _ _ (gx_map h1 _ _ h)).
    - intros i e h. exact (gx_codes h2 _ _ (gx_codes h1 _ _ h)).
  Qed.

  Lemma cok_mono G G' (h : gext G G') c : cok G c -> cok G' c.
  Proof. intros [e [he hi]]. exists e. split; [exact (gx_codes h _ _ he)|exact hi]. Qed.

  Lemma g_slot_ext G G' (h : gext G G') :
    (forall x t, g_slot G x t -> g_slot G' x t)
    /\ (forall l ts, g_slots G l ts -> g_slots G' l ts).
  Proof using.
    apply (g_slot_mutind G (fun x t => g_slot G' x t) (fun l ts => g_slots G' l ts)).
    - intros a t ha. constructor. exact (gx_map h _ _ ha).
    - intros vals nvals goff c ts _ ih hn hc.
      constructor; [exact ih|exact hn|exact (cok_mono G G' h c hc)].
    - constructor.
    - intros x l t ts _ ih1 _ ih2. constructor; [exact ih1|exact ih2].
  Qed.

  Definition g_slot_mono G G' (h : gext G G') := proj1 (g_slot_ext G G' h).
  Definition g_slots_mono G G' (h : gext G G') := proj2 (g_slot_ext G G' h).

  Lemma g_susp_mono G G' (h : gext G G') e t u : g_susp G e t u -> g_susp G' e t u.
  Proof.
    intros hs. inversion hs; subst. constructor; try reflexivity; try assumption.
    eapply (g_slots_mono G G' h). eassumption.
  Qed.

  Lemma g_addrs_mono G G' (h : gext G G') l ts : g_addrs G l ts -> g_addrs G' l ts.
  Proof.
    intros ha. induction ha as [|a t l ts hat hl ih]; constructor;
      [exact (gx_map h _ _ hat)|exact ih].
  Qed.

  Lemma g_value_mono G G' (h : gext G G') v t : g_value G v t -> g_value G' v t.
  Proof.
    intros hv. destruct hv; econstructor;
      eauto using g_addrs_mono, g_susp_mono, cok_mono.
  Qed.

  Lemma g_cell_mono G G' (h : gext G G') cl t : g_cell G cl t -> g_cell G' cl t.
  Proof.
    intros hc. destruct hc; econstructor; eauto using g_value_mono, g_susp_mono, cok_mono.
  Qed.

  (** ** Every address a reading names has a ghost term *)

  Definition gdef (G : haddr -> option term) (a : haddr) : Prop := exists t, G a = Some t.

  Lemma g_slot_ad G :
    (forall x t, g_slot G x t -> Forall (gdef G) (ad_slot x))
    /\ (forall l ts, g_slots G l ts -> Forall (gdef G) (ad_slots l)).
  Proof using.
    apply (g_slot_mutind G
      (fun x t => Forall (gdef G) (ad_slot x))
      (fun l ts => Forall (gdef G) (ad_slots l))).
    - intros a t ha. constructor; [exists t; exact ha|constructor].
    - intros vals nvals goff c ts _ ih _ _. exact ih.
    - constructor.
    - intros x l t ts _ ih1 _ ih2. unfold ad_slots. cbn [flat_map].
      apply Forall_app_g; [exact ih1|exact ih2].
  Qed.

  Lemma g_addrs_ad G l ts : g_addrs G l ts -> Forall (gdef G) l.
  Proof. intros h. induction h; constructor; [eexists; eassumption|assumption]. Qed.

  Lemma g_susp_ad G e t u : g_susp G e t u -> Forall (gdef G) (ad_env e).
  Proof.
    intros h. inversion h; subst. unfold ad_env. cbn [ev_vals].
    eapply (proj2 (g_slot_ad G)). eassumption.
  Qed.

  Lemma g_value_ad G v t : g_value G v t -> Forall (gdef G) (ad_value v).
  Proof.
    intros h. destruct h; cbn [ad_value];
      try (eapply g_addrs_ad; eassumption);
      try (eapply g_susp_ad; eassumption).
    all: apply Forall_app_g;
      [eapply g_susp_ad; eassumption|eapply g_addrs_ad; eassumption].
  Qed.

  Lemma g_cell_ad G cl t : g_cell G cl t -> Forall (gdef G) (ad_cell cl).
  Proof.
    intros h. destruct h; cbn [ad_cell].
    - inversion H; subst. eapply (proj2 (g_slot_ad G)). eassumption.
    - exact (g_value_ad _ _ _ H).
  Qed.

  (** ** The state operations that leave the heap shape alone

    What [heap_upd], [tick], [new_entry], [once_body] and [delta] change of a state. *)

  Lemma heap_upd_shape a cl s s' :
    heap_upd a cl s = Some s' ->
    s'.(st_next) = s.(st_next) /\ s'.(st_room) = s.(st_room)
    /\ s'.(st_steps) = s.(st_steps) /\ s'.(st_gam) = s.(st_gam)
    /\ s'.(st_memo) = s.(st_memo) /\ bh_upd a cl s.(st_heap) = Some s'.(st_heap).
  Proof.
    unfold heap_upd. destruct (bh_upd a cl s.(st_heap)) as [h'|] eqn:e; cbn; [|discriminate].
    intros he. inversion he; subst. cbn. repeat split; try reflexivity.
  Qed.

  Lemma tick_shape s s' :
    tick s = Some s' ->
    s'.(st_heap) = s.(st_heap) /\ s'.(st_next) = s.(st_next)
    /\ s'.(st_room) = s.(st_room) /\ s'.(st_gam) = s.(st_gam)
    /\ s'.(st_memo) = s.(st_memo).
  Proof.
    unfold tick. destruct s.(st_steps) eqn:e; [discriminate|].
    intros he. inversion he; subst. cbn. repeat split; reflexivity.
  Qed.

  (** [new_entry], [once_body] and [delta] touch only the memo. *)

  Lemma new_entry_shape t u ns s :
    (snd (new_entry X_type X t u ns s)).(st_heap) = s.(st_heap)
    /\ (snd (new_entry X_type X t u ns s)).(st_next) = s.(st_next)
    /\ (snd (new_entry X_type X t u ns s)).(st_room) = s.(st_room)
    /\ (snd (new_entry X_type X t u ns s)).(st_steps) = s.(st_steps)
    /\ (snd (new_entry X_type X t u ns s)).(st_gam) = s.(st_gam)
    /\ ((snd (new_entry X_type X t u ns s)).(st_memo)).(m_delta)
       = (s.(st_memo)).(m_delta).
  Proof. repeat split; reflexivity. Qed.

  Lemma once_body_shape c s :
    (snd (once_body c s)).(st_heap) = s.(st_heap)
    /\ (snd (once_body c s)).(st_next) = s.(st_next)
    /\ (snd (once_body c s)).(st_room) = s.(st_room)
    /\ (snd (once_body c s)).(st_steps) = s.(st_steps)
    /\ (snd (once_body c s)).(st_gam) = s.(st_gam)
    /\ ((snd (once_body c s)).(st_memo)).(m_delta) = (s.(st_memo)).(m_delta).
  Proof.
    unfold once_body.
    destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_once))) as [b|];
      cbn; repeat split; reflexivity.
  Qed.

  Lemma delta_shape kn u s r s' :
    delta X_type X kn u s = COk (r, s') ->
    s'.(st_heap) = s.(st_heap) /\ s'.(st_next) = s.(st_next)
    /\ s'.(st_room) = s.(st_room) /\ s'.(st_steps) = s.(st_steps)
    /\ s'.(st_gam) = s.(st_gam).
  Proof.
    unfold delta, delta_new.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|].
    - intros he. inversion he; subst. repeat split; reflexivity.
    - destruct (find_inst u insts) as [[i t]|].
      + intros he. inversion he; subst. repeat split; reflexivity.
      + destruct (new_entry X_type X body u (NSConst kn) s) as [c s1] eqn:e1.
        intros he. inversion he; subst. cbn.
        change s1 with (snd (c, s1)). rewrite <- e1.
        destruct (new_entry_shape body u (NSConst kn) s) as (p1 & p2 & p3 & p4 & p5 & _).
        rewrite p1, p2, p3, p4, p5. repeat split; reflexivity.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|]; [|discriminate|discriminate].
      destruct cb.(cst_body) as [body|].
      + destruct (new_entry X_type X body u (NSConst kn) s) as [c s1] eqn:e1.
        intros he. inversion he; subst. cbn.
        change s1 with (snd (c, s1)). rewrite <- e1.
        destruct (new_entry_shape body u (NSConst kn) s) as (p1 & p2 & p3 & p4 & p5 & _).
        rewrite p1, p2, p3, p4, p5. repeat split; reflexivity.
      + intros he. inversion he; subst. repeat split; reflexivity.
  Qed.

  (** ** What the machine assumes of a state

    Beside the heap laws of [state_ok] and the absence of forwarding pointers, the state
    carries a ghost map: every cell has a ghost term, and the cell stands for a reduct of
    it, unless the cell is being forced, in which case its caller carries the reading. *)

  (** The memo of the state: the invariants of the memo files ([memo_inv], [memo_ok]); the
    ghost's code table [K] is part of the real one; and every entry of the real one names
    its constants at the right instance length. *)
  Definition mok (K : PTree.t code_entry) (s : cbn_state) : Prop :=
    memo_inv X_type X s /\ memo_ok X_type X s
    /\ (forall i e, PTree.get i K = Some e -> PTree.get i ((s.(st_memo)).(m_codes)) = Some e)
    /\ (forall i e, PTree.get i ((s.(st_memo)).(m_codes)) = Some e ->
          consts_okb Σ (inst_code e.(ce_inst) e.(ce_term)) = true).

  Record gok (lo : positive) (G : ghost) (s : cbn_state) : Prop := mkGok {
    gk_state : state_ok lo s;
    gk_nofwd : heap_nofwd s.(st_heap);
    gk_cells : forall a cl, heap_get a s = Some cl ->
      exists t, G a = Some t
        /\ (cl = CBusy \/ exists u, g_cell G cl u /\ cred t u);
    gk_dom : forall a t, G a = Some t ->
      (lo <= ha_p a)%positive /\ (ha_p a < s.(st_next))%positive;
    gk_gam : forall j a, PTree.get (key_of_succ_nat j) s.(st_gam) = Some a ->
      exists t, ctx_den Γ nctx lvl j = Some t /\ G a = Some t;
    gk_memo : mok (gc G) s }.

  (** ** The algebra of ghost readings *)

  Lemma g_susp_inv G e t u :
    g_susp G e t u ->
    exists ts, g_slots G e.(ev_vals) ts /\ e.(ev_nvals) = #|e.(ev_vals)|
      /\ u = subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals) t).
  Proof.
    intros h. inversion h; subst. cbn [ev_vals ev_nvals ev_goff].
    exists ts. repeat split; assumption.
  Qed.

  Lemma g_slots_length G l ts : g_slots G l ts -> #|ts| = #|l|.
  Proof. induction 1; cbn; [reflexivity|]. rewrite IHg_slots. reflexivity. Qed.

  Lemma g_slots_nth G l ts n x :
    g_slots G l ts -> nth_error l n = Some x ->
    exists t, nth_error ts n = Some t /\ g_slot G x t.
  Proof.
    intros h. revert n. induction h as [|y l t ts hy hl ih]; intros n hn.
    - destruct n; discriminate.
    - destruct n as [|n]; cbn in hn.
      + injection hn as <-. exists t. split; [reflexivity|exact hy].
      + exact (ih n hn).
  Qed.

  (** The reading of a suspension whose code is an application, a lambda, a let or a
    constant: the machine's own decomposition, with [subst] and [lift] computed. *)

  Lemma subst_cons_app (tx : term) (ts : list term) (b : term) :
    subst (tx :: ts) 0 b = subst [tx] 0 (subst ts 1 b).
  Proof. pose proof (subst_app_simpl [tx] ts 0 b) as h. cbn in h. exact h. Qed.

  Lemma g_susp_app G e f a u :
    g_susp G e (tApp f a) u ->
    exists uf ua, u = tApp uf ua /\ g_susp G e f uf /\ g_susp G e a ua.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; split; [reflexivity|].
    split; constructor; (exact h1 || reflexivity || assumption).
  Qed.

  (** A [tConst] has no free variables, so a [lift] followed by a [subst] leaves it
    alone: the reading of a suspension whose code is a constant is that constant, whatever
    the environment. *)
  Lemma subst_lift_const ts n m p kn ui :
    subst ts n (lift m p (tConst kn ui)) = tConst kn ui.
  Proof. reflexivity. Qed.

  Lemma g_susp_const G e kn ui u : g_susp G e (tConst kn ui) u -> u = tConst kn ui.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (_ & _ & ->)]. reflexivity.
  Qed.

  Lemma g_susp_tind G e i ui u : g_susp G e (tInd i ui) u -> u = tInd i ui.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (_ & _ & ->)]. reflexivity.
  Qed.

  Lemma g_susp_construct G e i n ui u :
    g_susp G e (tConstruct i n ui) u -> u = tConstruct i n ui.
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (_ & _ & ->)]. reflexivity.
  Qed.

  (** Pushing a slot on the environment is PCUIC's substitution on the reading: this is
    the substitution-composition the beta and zeta rules need. *)

  Lemma g_susp_lam G e na A b u :
    g_susp G e (tLambda na A b) u ->
    exists A' B, u = tLambda na A' B
      /\ (forall x tx, g_slot G x tx -> g_susp G (env_push x e) b (subst [tx] 0 B)).
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; split; [reflexivity|].
    intros x tx hx.
    rewrite <- (subst_cons_app tx ts (lift (lvl - nctx + goff) (S #|vals|) b)).
    unfold env_push. cbn [ev_vals ev_nvals ev_goff].
    exact (g_susp_intro G (x :: vals) (S #|vals|) goff b (tx :: ts)
             (g_slots_cons G x vals tx ts hx h1) eq_refl).
  Qed.

  Lemma g_susp_letin G e na d T b u :
    g_susp G e (tLetIn na d T b) u ->
    exists d' T' B, u = tLetIn na d' T' B /\ g_susp G e d d'
      /\ (forall x tx, g_slot G x tx -> g_susp G (env_push x e) b (subst [tx] 0 B)).
  Proof.
    intros h. destruct (g_susp_inv _ _ _ _ h) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *. subst nvals.
    cbn [lift subst].
    eexists; eexists; eexists; split; [reflexivity|].
    split.
    - constructor; (exact h1 || reflexivity || assumption).
    - intros x tx hx.
      rewrite <- (subst_cons_app tx ts (lift (lvl - nctx + goff) (S #|vals|) b)).
      unfold env_push. cbn [ev_vals ev_nvals ev_goff].
      exact (g_susp_intro G (x :: vals) (S #|vals|) goff b (tx :: ts)
               (g_slots_cons G x vals tx ts hx h1) eq_refl).
  Qed.

  Lemma g_slots_list_set G l ts n x t :
    g_slots G l ts -> g_slot G x t -> g_slots G (list_set l n x) (list_set ts n t).
  Proof.
    intros h hx. revert n. induction h as [|y l u us hy hl ih]; intros [|n]; cbn;
      constructor; try assumption. apply ih.
  Qed.

  Lemma g_slots_addrs G l ts : g_addrs G l ts -> g_slots G (map SAddr l) ts.
  Proof. induction 1; cbn; constructor; [constructor; assumption|assumption]. Qed.

  Lemma g_slots_app G l1 ts1 l2 ts2 :
    g_slots G l1 ts1 -> g_slots G l2 ts2 -> g_slots G (l1 ++ l2) (ts1 ++ ts2).
  Proof. induction 1; cbn; [trivial|]. intros h2. constructor; auto. Qed.

  Lemma g_addrs_nth G l ts n a :
    g_addrs G l ts -> nth_error l n = Some a -> exists t, nth_error ts n = Some t /\ G a = Some t.
  Proof.
    intros h. revert n. induction h as [|b t l ts hb hl ih]; intros [|n] hn; cbn in hn;
      try discriminate.
    - injection hn as <-. exists t. split; [reflexivity|exact hb].
    - exact (ih n hn).
  Qed.

  Lemma g_addrs_length G l ts : g_addrs G l ts -> #|ts| = #|l|.
  Proof. induction 1; cbn; congruence. Qed.

  (** ** What this file assumes

    [hnctx] and [hlvl] say what the machine's comment says of its own parameters.
    [const_instance_ok] is the instance condition [delta_red1] needs, for the constants the
    context's let-bodies name; for the rest it is proved (see the file header). *)

  Hypothesis hnctx : nctx = #|Γ|.
  Hypothesis hlvl : nctx <= lvl.
  Hypothesis const_instance_ok : forall j decl b,
    nth_error Γ j = Some decl -> decl.(decl_body) = Some b -> consts_okb Σ b = true.

  (** ** The state operations against the ghost map *)

  Lemma haddr_eqb_eq a b : haddr_eqb a b = true -> a = b.
  Proof.
    destruct a as [p], b as [q]. unfold haddr_eqb. cbn. intros h.
    apply Pos.eqb_eq in h. rewrite h. reflexivity.
  Qed.

  Lemma haddr_eqb_refl a : haddr_eqb a a = true.
  Proof. destruct a as [p]. unfold haddr_eqb. cbn. apply Pos.eqb_refl. Qed.

  Lemma gdom_addrs_in lo G s l :
    (forall a t, G a = Some t -> (lo <= ha_p a)%positive /\ (ha_p a < s.(st_next))%positive) ->
    Forall (gdef G) l -> addrs_in lo s.(st_next) l.
  Proof.
    intros hd. induction 1 as [|b l hb hl ih]; constructor; [|exact ih].
    destruct hb as [t ht]. exact (hd _ _ ht).
  Qed.

  Lemma mok_memo K s s1 : s1.(st_memo) = s.(st_memo) -> mok K s -> mok K s1.
  Proof. intros he h. unfold mok, memo_inv, memo_ok in *. rewrite he. exact h. Qed.

  Lemma mok_widen K s : mok K s -> mok ((s.(st_memo)).(m_codes)) s.
  Proof.
    intros (h1 & h2 & _ & h4). split; [exact h1|]. split; [exact h2|].
    split; [intros i e hi; exact hi|exact h4].
  Qed.

  Lemma mok_once_body K c e s :
    mok K s -> PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e -> code_inv e c ->
    mok K (snd (once_body c s)).
  Proof.
    intros (h1 & h2 & h3 & h4) hg hi.
    destruct (once_body_memo c s) as (q1 & _).
    split; [exact (memo_inv_once_body X_type X c e s h1 hg hi)|].
    split; [exact (memo_ok_codes X_type X s _ q1 h2)|].
    split; [intros i e' he'; rewrite q1; exact (h3 i e' he')|].
    intros i e' he'. rewrite q1 in he'. exact (h4 i e' he').
  Qed.

  (** An entry added at the next index leaves every existing entry in place. *)
  Lemma memo_codes_set_mono (m : cbn_memo) (e' : code_entry) i e :
    memo_fresh m -> PTree.get i m.(m_codes) = Some e ->
    PTree.get i (PTree.set m.(m_ncode) e' m.(m_codes)) = Some e.
  Proof.
    intros hf h. rewrite PTree.gso; [exact h|]. intros ->.
    destruct hf as [hc _].
    assert (hn : PTree.get (m_ncode m) (m_codes m) <> None) by congruence.
    exact (idx_lt_neq _ _ (hc _ hn) eq_refl).
  Qed.

  (** [delta] leaves the code table alone, or adds the body of [kn] at the next index. *)
  Lemma delta_codes kn ui s r s1 :
    delta_ok X_type X (s.(st_memo)) -> delta X_type X kn ui s = COk (r, s1) ->
    (s1.(st_memo)).(m_codes) = (s.(st_memo)).(m_codes)
    \/ exists cb body, abstract_env_lookup X kn = Some (ConstantDecl cb)
         /\ cb.(cst_body) = Some body
         /\ (s1.(st_memo)).(m_codes)
            = PTree.set ((s.(st_memo)).(m_ncode))
                (mkEntry body ui (NSConst kn) (wf_term_univs X_type X (inst_code ui body)))
                ((s.(st_memo)).(m_codes)).
  Proof.
    intros hd he. unfold delta in he.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - destruct (cbn_COk_pair_inj _ _ _ _ he) as [_ <-]. left. reflexivity.
    - destruct (hd kn _ Ed) as [[cb [hl hb]] _].
      destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + destruct (cbn_COk_pair_inj _ _ _ _ he) as [_ <-]. left. reflexivity.
      + destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s1 he)
          as [_ ->].
        right. exists cb, body. split; [exact hl|]. split; [exact hb|].
        rewrite delta_new_codes. apply new_entry_codes.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|discriminate he|discriminate he].
      destruct (cst_body cb) as [body|] eqn:Eb.
      + destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s1 he)
          as [_ ->].
        right. exists cb, body. split; [first [exact El|reflexivity]|].
        split; [first [exact Eb|reflexivity]|].
        rewrite delta_new_codes. apply new_entry_codes.
      + destruct (cbn_COk_pair_inj _ _ _ _ he) as [_ <-]. left. reflexivity.
  Qed.

  Lemma gok_same lo G s s1 :
    gok lo G s -> s1.(st_heap) = s.(st_heap) -> s1.(st_next) = s.(st_next) ->
    s1.(st_gam) = s.(st_gam) -> mok (gc G) s1 -> gok lo G s1.
  Proof.
    intros [h1 h2 h3 h4 h5 _] e1 e2 e3 hd. split.
    - destruct h1 as [p1 p2 p3]. split.
      + rewrite e1, e2. exact p1.
      + intros a cl hc. rewrite e1 in hc. rewrite e2. exact (p2 _ _ hc).
      + intros k a hk. rewrite e3 in hk. rewrite e2. exact (p3 _ _ hk).
    - rewrite e1. exact h2.
    - intros a cl hc. unfold heap_get in hc. rewrite e1 in hc. exact (h3 _ _ hc).
    - intros a t ht. rewrite e2. exact (h4 _ _ ht).
    - intros j a hj. rewrite e3 in hj. exact (h5 _ _ hj).
    - exact hd.
  Qed.

  (** The same state shape, with the ghost's table replaced by a larger one. *)
  Lemma gok_recode lo G s s1 K :
    gok lo G s -> s1.(st_heap) = s.(st_heap) -> s1.(st_next) = s.(st_next) ->
    s1.(st_gam) = s.(st_gam) ->
    (forall i e, PTree.get i (gc G) = Some e -> PTree.get i K = Some e) ->
    mok K s1 -> gok lo (mkGhost (gm G) K) s1.
  Proof.
    intros hok e1 e2 e3 hK hm.
    assert (hx : gext G (mkGhost (gm G) K)) by (split; [intros a t h; exact h|exact hK]).
    destruct hok as [h1 h2 h3 h4 h5 _]. split.
    - destruct h1 as [p1 p2 p3]. split.
      + rewrite e1, e2. exact p1.
      + intros a cl hc. rewrite e1 in hc. rewrite e2. exact (p2 _ _ hc).
      + intros k a hk. rewrite e3 in hk. rewrite e2. exact (p3 _ _ hk).
    - rewrite e1. exact h2.
    - intros a cl hc. unfold heap_get in hc. rewrite e1 in hc.
      destruct (h3 _ _ hc) as [t [ht hr]]. exists t. split; [exact ht|].
      destruct hr as [hb|[u [hu hred]]]; [left; exact hb|].
      right. exists u. split; [exact (g_cell_mono _ _ hx _ _ hu)|exact hred].
    - intros a t ht. rewrite e2. exact (h4 _ _ ht).
    - intros j a hj. rewrite e3 in hj. exact (h5 _ _ hj).
    - exact hm.
  Qed.

  Lemma delta_gok lo G kn ui s r s1 :
    gok lo G s -> delta X_type X kn ui s = COk (r, s1) -> gok lo G s1.
  Proof.
    intros hok hd. destruct (delta_shape _ _ _ _ _ hd) as (e1 & e2 & _ & _ & e5).
    destruct (gk_memo _ _ _ hok) as (hmi & hmo & hcodes & hokb).
    pose proof hmi as (hf & _ & _ & _ & hdo).
    apply (gok_same lo G s); [exact hok|exact e1|exact e2|exact e5|].
    split; [exact (memo_inv_delta X_type X kn ui s r s1 hmi hd)|].
    split; [exact (delta_memo_ok X_type X kn ui s r s1 hmo hd)|].
    destruct (delta_codes kn ui s r s1 hdo hd) as [hc|(cb & body & hl & hb & hc)];
      rewrite hc.
    - split; [exact hcodes|exact hokb].
    - split.
      + intros i e hi. exact (memo_codes_set_mono _ _ i e hf (hcodes i e hi)).
      + intros i e hi.
        destruct (key_eqb i ((s.(st_memo)).(m_ncode))) eqn:E.
        * apply key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
          injection hi as <-. cbn [ce_inst ce_term].
          pose proof (lookup_declared X_type X Σ kn cb hΣ hl) as hdecl.
          rewrite (consts_inst_code Σ ui body).
          exact (declared_constant_consts_okb Σ kn cb body wfΣ hdecl hb).
        * rewrite PTree.gso in hi by (apply key_neq_of_eqb, E). exact (hokb i e hi).
  Qed.

  (** The state invariant is not empty: the machine's initial state has it, with the empty
    ghost. A call adds its input codes to the table with [new_entry] before it starts. *)
  Lemma gok_init : gok xH (mkGhost (fun _ => None) (PTree.empty _)) cbn_init.
  Proof.
    split.
    - apply state_ok_init.
    - intros a a' h. unfold cbn_init in h. cbn [st_heap] in h.
      rewrite bh_get_holes in h. discriminate.
    - intros a cl h. unfold heap_get, cbn_init in h. cbn [st_heap] in h.
      rewrite bh_get_holes in h. discriminate.
    - intros a t h. discriminate h.
    - intros j a h. unfold cbn_init in h. cbn [st_gam] in h.
      rewrite PTree.gempty in h. discriminate.
    - split; [apply memo_inv_init|]. split; [apply memo_ok_init|]. split.
      + intros i e h. cbn [gc] in h. rewrite PTree.gempty in h. discriminate.
      + intros i e h. unfold cbn_init, memo_empty in h. cbn [st_memo m_codes] in h.
        rewrite PTree.gempty in h. discriminate.
  Qed.

  (** *** The context map *)

  Lemma ctx_den_red j t : ctx_den Γ nctx lvl j = Some t -> cred (tRel (lvl - nctx + j)) t.
  Proof.
    unfold ctx_den. destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
    destruct decl.(decl_body) as [b|] eqn:eb; intros h; injection h as <-.
    - apply cred_one.
      assert (hn : nth_error (Γ ,,, Δ) (lvl - nctx + j) = Some decl).
      { unfold app_context. rewrite nth_error_app_ge; [|lia].
        replace (lvl - nctx + j - #|Δ|) with j by lia. exact ed. }
      pose proof (red_rel Σ ΓΔ (lvl - nctx + j) b) as hr.
      replace (lvl - nctx + S j) with (S (lvl - nctx + j)) by lia.
      apply hr. rewrite hn. cbn. rewrite eb. reflexivity.
    - apply nth_error_Some_length in ed.
      replace (lvl - S (nctx - S j)) with (lvl - nctx + j) by lia.
      apply cred_refl.
  Qed.

  (** *** The write-back

    Forcing a cell marks it [CBusy], evaluates, then writes the value back. Because the
    ghost map [G] is unchanged, the cell at [a] still stands for a reduct of [G a] after each
    write: [CBusy] trivially (it stands for nothing), and [CDone v] because [v] is a reduct
    of the cell's reading which is a reduct of [G a]. *)

  Lemma gok_heap_upd_busy lo G a s s' :
    gok lo G s -> heap_upd a CBusy s = Some s' -> gok lo G s'.
  Proof.
    intros hok he.
    destruct (heap_upd_shape _ _ _ _ he) as (he1 & he2 & he3 & he4 & he5 & hu).
    split.
    - apply (heap_upd_state_ok lo a CBusy s s' (gk_state _ _ _ hok)); [cbn; constructor|exact he].
    - apply (heap_nofwd_heap_upd a CBusy s s' (gk_nofwd _ _ _ hok));
        [intros b; discriminate|exact he].
    - intros b cl hb. unfold heap_get in hb.
      destruct (haddr_dec b a) as [->|hne].
      + rewrite (bh_get_upd_same _ _ _ _ hu) in hb. inversion hb; subst cl.
        assert (ha_in : exists cl0, bh_get a s.(st_heap) = Some cl0).
        { destruct (bh_get a s.(st_heap)) eqn:E; [eexists; reflexivity|].
          exfalso. apply (proj2 (bh_upd_none a CBusy s.(st_heap))) in E.
          rewrite E in hu; discriminate. }
        destruct ha_in as [cl0 h0].
        destruct (gk_cells _ _ _ hok a cl0 h0) as [t [hGa _]].
        exists t. split; [exact hGa|left; reflexivity].
      + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb.
        exact (gk_cells _ _ _ hok b cl hb).
    - intros b t ht. rewrite he1. exact (gk_dom _ _ _ hok b t ht).
    - intros j b hj. rewrite he4 in hj. exact (gk_gam _ _ _ hok j b hj).
    - exact (mok_memo _ s s' he5 (gk_memo _ _ _ hok)).
  Qed.

  Lemma gok_heap_upd_done lo G a v u t s s' :
    gok lo G s -> G a = Some t -> g_value G v u -> cred t u ->
    heap_upd a (CDone v) s = Some s' -> gok lo G s'.
  Proof.
    intros hok hGa hv hred he.
    destruct (heap_upd_shape _ _ _ _ he) as (he1 & he2 & he3 & he4 & he5 & hu).
    split.
    - apply (heap_upd_state_ok lo a (CDone v) s s' (gk_state _ _ _ hok)); [|exact he].
      cbn [ad_cell]. apply (gdom_addrs_in lo G s); [exact (gk_dom _ _ _ hok)|].
      exact (g_value_ad G v u hv).
    - apply (heap_nofwd_heap_upd a (CDone v) s s' (gk_nofwd _ _ _ hok));
        [intros b; discriminate|exact he].
    - intros b cl hb. unfold heap_get in hb.
      destruct (haddr_dec b a) as [->|hne].
      + rewrite (bh_get_upd_same _ _ _ _ hu) in hb. inversion hb; subst cl.
        exists t. split; [exact hGa|].
        right. exists u. split; [constructor; exact hv|exact hred].
      + rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb.
        exact (gk_cells _ _ _ hok b cl hb).
    - intros b t0 ht0. rewrite he1. exact (gk_dom _ _ _ hok b t0 ht0).
    - intros j b hj. rewrite he4 in hj. exact (gk_gam _ _ _ hok j b hj).
    - exact (mok_memo _ s s' he5 (gk_memo _ _ _ hok)).
  Qed.

  (** *** Inversions of the ghost value reading, by case on the value shape *)

  Lemma g_value_VCon_inv G h sp t :
    g_value G (VCon h sp) t -> exists ts, t = mkApps h ts /\ g_addrs G sp ts.
  Proof. intros hv; inversion hv; subst; eexists; split; [reflexivity|eassumption]. Qed.

  Lemma g_value_VLam_inv G e c t :
    g_value G (VLam e c) t -> g_susp G e c.(c_term) t.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma g_value_VOpen_inv G e c t :
    g_value G (VOpen e c) t -> g_susp G e c.(c_term) t.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma g_value_VNeu_inv G nn sp t :
    g_value G (VNeu nn sp) t ->
    (exists l ts, nn = NVar l /\ t = mkApps (tRel (lvl - S l)) ts /\ g_addrs G sp ts)
    \/ (exists h ts, nn = NConst h /\ t = mkApps h ts /\ g_addrs G sp ts).
  Proof.
    intros hv; inversion hv; subst.
    - left. eexists; eexists; split; [reflexivity|split; [reflexivity|eassumption]].
    - right. eexists; eexists; split; [reflexivity|split; [reflexivity|eassumption]].
  Qed.

  Lemma g_value_VStuck_inv G e c sp t :
    g_value G (VStuck e c sp) t ->
    exists h ts, g_susp G e c.(c_term) h /\ g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    eexists; eexists; split; [eassumption|split; [eassumption|reflexivity]].
  Qed.

  Lemma g_value_VFix_inv G e c i sp t :
    g_value G (VFix e c i sp) t ->
    exists mfix idx h ts, c.(c_term) = tFix mfix idx /\ g_susp G e (tFix mfix i) h
      /\ cok G c /\ g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    do 4 eexists; repeat split; first [eassumption|reflexivity].
  Qed.

  Lemma g_value_VStuckFix_inv G e c i sp t :
    g_value G (VStuckFix e c i sp) t ->
    exists mfix idx h ts, c.(c_term) = tFix mfix idx /\ g_susp G e (tFix mfix i) h
      /\ cok G c /\ g_addrs G sp ts /\ t = mkApps h ts.
  Proof.
    intros hv; inversion hv; subst.
    do 4 eexists; repeat split; first [eassumption|reflexivity].
  Qed.

  (** The reading of any code through an environment whose slots are read. *)
  Lemma g_susp_of_slots G e t ts :
    g_slots G e.(ev_vals) ts -> e.(ev_nvals) = #|e.(ev_vals)| ->
    g_susp G e t (subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals) t)).
  Proof.
    destruct e as [vals nvals goff]; cbn; intros h1 h2; subst nvals.
    constructor; [exact h1|reflexivity].
  Qed.

  Lemma g_slot_addr_inv G a t : g_slot G (SAddr a) t -> G a = Some t.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma g_slot_inl_inv G vs n o c t :
    g_slot G (SInl vs n o c) t -> g_susp G (mkEnv vs n o) c.(c_term) t.
  Proof. intros h; inversion h; subst; econstructor; eauto. Qed.

  Lemma g_cell_susp_inv G vs n o c u :
    g_cell G (CSusp vs n o c) u -> g_susp G (mkEnv vs n o) c.(c_term) u.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma g_cell_done_inv G v u : g_cell G (CDone v) u -> g_value G v u.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma g_value_VLam_cok G e c t : g_value G (VLam e c) t -> cok G c.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma g_value_VStuck_cok G e c sp t : g_value G (VStuck e c sp) t -> cok G c.
  Proof. intros hv; inversion hv; subst; assumption. Qed.

  Lemma g_slot_inl_cok G vs n o c t : g_slot G (SInl vs n o c) t -> cok G c.
  Proof. intros h; inversion h; subst; assumption. Qed.

  Lemma g_cell_susp_cok G vs n o c u : g_cell G (CSusp vs n o c) u -> cok G c.
  Proof. intros h; inversion h; subst; assumption. Qed.

  (** *** The congruences of reduction the new rules need *)

  Lemma cred_case_c ci p c c' brs : cred c c' -> cred (tCase ci p c brs) (tCase ci p c' brs).
  Proof. intros [h]. constructor. exact (red_case_c _ _ _ _ _ h). Qed.

  Lemma cred_proj_c pr c c' : cred c c' -> cred (tProj pr c) (tProj pr c').
  Proof. intros [h]. constructor. exact (red_proj_c _ _ _ h). Qed.

  Lemma cred_mkApps_list_set f l n t u :
    nth_error l n = Some t -> cred t u -> cred (mkApps f l) (mkApps f (list_set l n u)).
  Proof.
    intros hn [h]. constructor. apply red_mkApps; [apply refl_red|].
    exact (All2_red_list_set Σ ΓΔ l n t u hn h).
  Qed.

  (** ** What a call does to the structures its caller holds

    A call may collect, and a collection renames every address. So a call does not promise
    that the roots come back unchanged or that the ghost map only grows. It promises
    [gren G G' rs rs']: the code table only grows ([gcx]), and every root comes back as a root
    of the same shape that stands, under the new ghost [G'], for what the old root stood for
    under [G] ([gpres], one clause per shape, like [PCUICCallByNeedSoundGC.root_pres]).
    Without a collection the roots come back as they went in and [G'] extends [G]
    ([gren_ext]); a collection renames them ([collect_ghost]). *)

  Definition gcx (G G' : ghost) : Prop :=
    forall i e, PTree.get i (gc G) = Some e -> PTree.get i (gc G') = Some e.

  (** An environment keeps its counts and its slots keep their readings. *)
  Definition genv (G G' : ghost) (e e' : cbn_env) : Prop :=
    e'.(ev_nvals) = e.(ev_nvals) /\ e'.(ev_goff) = e.(ev_goff)
    /\ forall ts, g_slots G e.(ev_vals) ts -> g_slots G' e'.(ev_vals) ts.

  Definition gpres (G G' : ghost) (r r' : root) : Prop :=
    match r, r' with
    | RA a, RA a' => forall t, G a = Some t -> G' a' = Some t
    | RSl x, RSl x' => forall t, g_slot G x t -> g_slot G' x' t
    | RE e, RE e' => genv G G' e e'
    | RV v, RV v' => forall t, g_value G v t -> g_value G' v' t
    | RSk l, RSk l' => forall ts, g_slots G l ts -> g_slots G' l' ts
    | RSp l, RSp l' => forall ts, g_addrs G l ts -> g_addrs G' l' ts
    | RC cl, RC cl' => forall t, g_cell G cl t -> g_cell G' cl' t
    | _, _ => False
    end.

  Definition gren (G G' : ghost) (rs rs' : list root) : Prop :=
    gcx G G' /\ Forall2 (gpres G G') rs rs'.

  Lemma cok_gcx G G' (h : gcx G G') c : cok G c -> cok G' c.
  Proof. intros [e [he hi]]. exists e. split; [exact (h _ _ he)|exact hi]. Qed.

  Lemma cok_eqc G G' c : gc G' = gc G -> cok G c -> cok G' c.
  Proof. intros he [e [h1 h2]]. exists e. rewrite he. split; assumption. Qed.

  Lemma genv_trans G1 G2 G3 e1 e2 e3 :
    genv G1 G2 e1 e2 -> genv G2 G3 e2 e3 -> genv G1 G3 e1 e3.
  Proof.
    intros (a1 & b1 & c1) (a2 & b2 & c2). split; [congruence|]. split; [congruence|].
    intros ts h. exact (c2 _ (c1 _ h)).
  Qed.

  Lemma genv_ext_r G G1 G2 e e' : genv G G1 e e' -> gext G1 G2 -> genv G G2 e e'.
  Proof.
    intros (a & b & c) hx. split; [exact a|]. split; [exact b|].
    intros ts h. exact (g_slots_mono _ _ hx _ _ (c _ h)).
  Qed.

  Lemma genv_susp G G' e e' t u : genv G G' e e' -> g_susp G e t u -> g_susp G' e' t u.
  Proof.
    intros (h1 & h2 & h3) hs. destruct (g_susp_inv _ _ _ _ hs) as (ts & hts & hnv & ->).
    rewrite <- h1, <- h2. apply g_susp_of_slots; [exact (h3 _ hts)|].
    rewrite h1, hnv, <- (g_slots_length _ _ _ hts), (g_slots_length _ _ _ (h3 _ hts)).
    reflexivity.
  Qed.

  Lemma gpres_ext G G' (h : gext G G') r : gpres G G' r r.
  Proof.
    destruct r; cbn [gpres].
    - intros t ht. exact (h _ _ ht).
    - intros t ht. exact (g_slot_mono _ _ h _ _ ht).
    - split; [reflexivity|]. split; [reflexivity|].
      intros ts ht. exact (g_slots_mono _ _ h _ _ ht).
    - intros t ht. exact (g_value_mono _ _ h _ _ ht).
    - intros ts ht. exact (g_slots_mono _ _ h _ _ ht).
    - intros ts ht. exact (g_addrs_mono _ _ h _ _ ht).
    - intros t ht. exact (g_cell_mono _ _ h _ _ ht).
  Qed.

  Lemma gpres_trans G1 G2 G3 r1 r2 r3 :
    gpres G1 G2 r1 r2 -> gpres G2 G3 r2 r3 -> gpres G1 G3 r1 r3.
  Proof.
    intros h1 h2.
    destruct r1, r2; cbn [gpres] in h1; try contradiction;
      destruct r3; cbn [gpres] in h2 |- *; try contradiction.
    all: first [ exact (genv_trans _ _ _ _ _ _ h1 h2)
               | let hx := fresh "hx" in intros ? hx; exact (h2 _ (h1 _ hx)) ].
  Qed.

  Lemma gpres_r_ext G G1 G2 r r' : gpres G G1 r r' -> gext G1 G2 -> gpres G G2 r r'.
  Proof. intros h hx. exact (gpres_trans _ _ _ _ _ _ h (gpres_ext _ _ hx r')). Qed.

  Lemma Forall2_gpres_r_ext G G1 G2 l l' :
    Forall2 (gpres G G1) l l' -> gext G1 G2 -> Forall2 (gpres G G2) l l'.
  Proof.
    intros h hx. induction h as [|r r' l l' hp hl ih]; constructor;
      [exact (gpres_r_ext _ _ _ _ _ hp hx)|exact ih].
  Qed.

  Lemma gren_ext G G' rs : gext G G' -> gren G G' rs rs.
  Proof.
    intros h. split; [exact (gx_codes h)|].
    induction rs as [|r rs ih]; constructor; [exact (gpres_ext _ _ h r)|exact ih].
  Qed.

  Lemma gren_refl G rs : gren G G rs rs.
  Proof. exact (gren_ext G G rs (gext_refl G)). Qed.

  Lemma gren_trans G1 G2 G3 rs1 rs2 rs3 :
    gren G1 G2 rs1 rs2 -> gren G2 G3 rs2 rs3 -> gren G1 G3 rs1 rs3.
  Proof.
    intros [hc1 hf1] [hc2 hf2]. split; [intros i e hi; exact (hc2 _ _ (hc1 _ _ hi))|].
    revert rs3 hf2. induction hf1 as [|r1 r2 l1 l2 hp hl ih]; intros rs3 hf2.
    - inversion hf2; subst. constructor.
    - inversion hf2 as [|r2' r3 l2' l3 hp2 hl2]; subst. constructor.
      + exact (gpres_trans _ _ _ _ _ _ hp hp2).
      + exact (ih _ hl2).
  Qed.

  Lemma gren_cons G G' r rs r' rs' :
    gren G G' (r :: rs) (r' :: rs') -> gpres G G' r r' /\ gren G G' rs rs'.
  Proof. intros [hc hf]. inversion hf; subst. split; [assumption|split; assumption]. Qed.

  Lemma gren_cok G G' rs rs' c : gren G G' rs rs' -> cok G c -> cok G' c.
  Proof. intros [hc _]. exact (cok_gcx _ _ hc c). Qed.

  (** ** A collection, against the ghost map

    The collector's walk ([gc_copy]) is followed with a second ghost [Gn] for the new heap,
    built as the walk goes: when the cell at old address [a] is copied to the new address
    [g_next], [Gn] is extended at that fresh address by [G a]. So nothing about the map the
    collector builds needs to be recovered afterwards, and no injectivity is needed: every
    forwarding pointer [a ↦ b] of the old heap has [Gn b = G a] ([gg_fwd]), which is all
    the renaming of a reading looks at, and every cell of the new heap is the renaming of
    the old cell it was copied from, so it stands for what that cell stood for
    ([gg_cells]). A [CBusy] cell is copied as [CBusy]. *)

  Section GhostCollect.
    Context (lo : positive) (G : ghost) (s : cbn_state) (hok : gok lo G s).

    Record gcg (Gn : ghost) (g : gc_state) : Prop := mkGcg {
      gg_inv : gc_inv nctx s.(st_heap) s.(st_next) g;
      gg_codes : gc Gn = gc G;
      gg_fwd : forall x b t, bh_get x g.(g_old) = Some (CFwd b) -> G x = Some t ->
        Gn b = Some t;
      gg_cells : forall b cl, bh_get b g.(g_heap) = Some cl ->
        exists t, Gn b = Some t /\ (cl = CBusy \/ exists u, g_cell Gn cl u /\ cred t u);
      gg_dom : forall b t, Gn b = Some t ->
        (s.(st_next) <= ha_p b)%positive /\ (ha_p b < g.(g_next))%positive }.

    (** What the walk asks of the address map it threads through the renamings. *)
    Definition cpg (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) : Prop :=
      forall a g a' g' Gn, gcg Gn g -> cp a g = COk (a', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ (forall t, G a = Some t -> Gn' a' = Some t).

    Section Walk.
      Context (cp : haddr -> gc_state -> cbn_res (haddr * gc_state)) (hcp : cpg cp).

      Lemma rn_addrs_g : forall l g l' g' Gn, gcg Gn g -> rn_addrs cp l g = COk (l', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn'
          /\ (forall ts, g_addrs G l ts -> g_addrs Gn' l' ts).
      Proof.
        induction l as [|a l ih]; intros g l' g' Gn hg he; simpl in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply gext_refl|].
          intros ts h. inversion h; subst. constructor.
        - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
          destruct (rn_addrs cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          destruct (ih _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hl2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros ts h. inversion h as [|a0 t l0 ts0 hat hl]; subst.
          constructor; [exact (hx2 _ _ (ha1 _ hat))|exact (hl2 _ hl)].
      Qed.

      Lemma rn_slot_g : forall x g x' g' Gn, gcg Gn g -> rn_slot cp x g = COk (x', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ (forall t, g_slot G x t -> g_slot Gn' x' t).
      Proof.
        intros x. induction x as [a|vs n o c ihvs] using slot_ind'; intros g x' g' Gn hg he.
        - simpl in he. destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          intros t h. constructor. exact (ha1 _ (g_slot_addr_inv _ _ _ h)).
        - rewrite rn_slot_SInl in he.
          destruct (rn_slots cp vs g) as [[vs' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          assert (hl : exists Gn', gcg Gn' g' /\ gext Gn Gn'
                    /\ (forall ts, g_slots G vs ts -> g_slots Gn' vs' ts)).
          { revert g vs' g' Gn hg e1.
            induction ihvs as [|y vs hy hvs ihl]; intros g vs' g1 Gn hg e1; simpl in e1.
            - inversion e1; subst; clear e1.
              exists Gn. split; [exact hg|]. split; [apply gext_refl|].
              intros ts h. inversion h; subst. constructor.
            - destruct (rn_slot cp y g) as [[y' ga]|wa] eqn:ea; [|discriminate].
              destruct (rn_slots cp vs ga) as [[vs2 gb]|wb] eqn:eb; [|discriminate].
              inversion e1; subst; clear e1.
              destruct (hy _ _ _ _ hg ea) as (Gna & hga & hxa & hra).
              destruct (ihl _ _ _ _ hga eb) as (Gnb & hgb & hxb & hrb).
              exists Gnb. split; [exact hgb|]. split; [exact (gext_trans _ _ _ hxa hxb)|].
              intros ts h. inversion h as [|y0 l0 t ts0 hy1 hl1]; subst.
              constructor; [exact (g_slot_mono _ _ hxb _ _ (hra _ hy1))|exact (hrb _ hl1)]. }
          destruct hl as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h as [|vals nvals goff c0 ts hts hnv hcok]; subst.
          rewrite <- (rn_slots_length _ _ _ _ _ e1).
          apply g_slot_inl; [exact (hr _ hts)|reflexivity|].
          exact (cok_eqc _ _ _ (gg_codes _ _ hg') hcok).
      Qed.

      Lemma rn_slots_g : forall l g l' g' Gn, gcg Gn g -> rn_slots cp l g = COk (l', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn'
          /\ (forall ts, g_slots G l ts -> g_slots Gn' l' ts).
      Proof.
        induction l as [|y l ih]; intros g l' g' Gn hg he; simpl in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply gext_refl|].
          intros ts h. inversion h; subst. constructor.
        - destruct (rn_slot cp y g) as [[y' g1]|w] eqn:e1; [|discriminate].
          destruct (rn_slots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_slot_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (ih _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros ts h. inversion h as [|y0 l0 t ts0 hy1 hl1]; subst.
          constructor; [exact (g_slot_mono _ _ hx2 _ _ (hr1 _ hy1))|exact (hr2 _ hl1)].
      Qed.

      Lemma rn_env_g e g e' g' Gn : gcg Gn g -> rn_env cp e g = COk (e', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ genv G Gn' e e'.
      Proof.
        destruct e as [vals n o]. intros hg he.
        unfold rn_env in he. cbn [ev_vals ev_nvals ev_goff] in he.
        destruct (rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
        inversion he; subst; clear he.
        destruct (rn_slots_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
        exists Gn'. split; [exact hg'|]. split; [exact hx'|].
        split; [reflexivity|]. split; [reflexivity|]. exact hr.
      Qed.

      Lemma rn_value_g v g v' g' Gn : gcg Gn g -> rn_value cp v g = COk (v', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ (forall t, g_value G v t -> g_value Gn' v' t).
      Proof.
        destruct v as [hd sp|e c|e c i sp|e c i sp|hd sp|e c|e c sp]; intros hg he;
          unfold rn_value in he.
        - (* VCon *)
          destruct (rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_addrs_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst. constructor. apply hr. assumption.
        - (* VLam *)
          destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_env_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst. constructor.
          + exact (genv_susp _ _ _ _ _ _ hr ltac:(eassumption)).
          + exact (cok_eqc _ _ _ (gg_codes _ _ hg') ltac:(eassumption)).
        - (* VFix *)
          destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_env_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (rn_addrs_g _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros t h. inversion h; subst.
          eapply g_VFix; [eassumption| | |apply hr2; assumption].
          + exact (genv_susp _ _ _ _ _ _ (genv_ext_r _ _ _ _ _ hr1 hx2) ltac:(eassumption)).
          + exact (cok_eqc _ _ _ (gg_codes _ _ hg2) ltac:(eassumption)).
        - (* VStuckFix *)
          destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_env_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (rn_addrs_g _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros t h. inversion h; subst.
          eapply g_VStuckFix; [eassumption| | |apply hr2; assumption].
          + exact (genv_susp _ _ _ _ _ _ (genv_ext_r _ _ _ _ _ hr1 hx2) ltac:(eassumption)).
          + exact (cok_eqc _ _ _ (gg_codes _ _ hg2) ltac:(eassumption)).
        - (* VNeu *)
          destruct (rn_addrs cp sp g) as [[sp' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_addrs_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst; constructor; apply hr; assumption.
        - (* VOpen *)
          destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_env_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros t h. inversion h; subst. constructor.
          + exact (genv_susp _ _ _ _ _ _ hr ltac:(eassumption)).
          + exact (cok_eqc _ _ _ (gg_codes _ _ hg') ltac:(eassumption)).
        - (* VStuck *)
          destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          destruct (rn_addrs cp sp g1) as [[sp' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_env_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (rn_addrs_g _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros t h. inversion h; subst.
          eapply g_VStuck; [| |apply hr2; assumption].
          + exact (genv_susp _ _ _ _ _ _ (genv_ext_r _ _ _ _ _ hr1 hx2) ltac:(eassumption)).
          + exact (cok_eqc _ _ _ (gg_codes _ _ hg2) ltac:(eassumption)).
      Qed.

      Lemma rn_cell_g cl g cl' g' Gn : gcg Gn g -> rn_cell cp cl g = COk (cl', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ (cl = CBusy -> cl' = CBusy)
          /\ (forall t, g_cell G cl t -> g_cell Gn' cl' t).
      Proof.
        destruct cl as [vals n o c|v| |b]; intros hg he; unfold rn_cell in he.
        - destruct (rn_slots cp vals g) as [[vs' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_slots_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          split; [intros hb; discriminate hb|].
          intros t h. pose proof (g_cell_susp_inv _ _ _ _ _ _ h) as hs.
          pose proof (g_cell_susp_cok _ _ _ _ _ _ h) as hc.
          constructor.
          + refine (genv_susp G Gn' (mkEnv vals n o) (mkEnv vs' n o) _ _ _ hs).
            split; [reflexivity|]. split; [reflexivity|]. exact hr.
          + exact (cok_eqc _ _ _ (gg_codes _ _ hg') hc).
        - destruct (rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_value_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          split; [intros hb; discriminate hb|].
          intros t h. constructor. exact (hr _ (g_cell_done_inv _ _ _ h)).
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply gext_refl|].
          split; [reflexivity|]. intros t h. inversion h.
        - destruct (cp b g) as [[b' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & _).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          split; [intros hb; discriminate hb|]. intros t h. inversion h.
      Qed.

      Lemma rn_root_g r g r' g' Gn : gcg Gn g -> rn_root cp r g = COk (r', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ gpres G Gn' r r'.
      Proof.
        destruct r as [a|x|e|v|l|l|cl]; intros hg he; unfold rn_root in he.
        - destruct (cp a g) as [[b g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|]. exact ha1.
        - destruct (rn_slot cp x g) as [[x' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_slot_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (rn_env cp e g) as [[e' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_env_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (rn_value cp v g) as [[v' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_value_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (rn_slots cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_slots_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (rn_addrs cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_addrs_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
        - destruct (rn_cell cp cl g) as [[cl' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_cell_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & _ & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|]. exact hr.
      Qed.

      Lemma rn_roots_g : forall l g l' g' Gn, gcg Gn g -> rn_roots cp l g = COk (l', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn' /\ Forall2 (gpres G Gn') l l'.
      Proof.
        induction l as [|r l ih]; intros g l' g' Gn hg he; simpl in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply gext_refl|]. constructor.
        - destruct (rn_root cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
          destruct (rn_roots cp l g1) as [[l2 g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_root_g _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hp1).
          destruct (ih _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hp2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          constructor; [exact (gpres_r_ext _ _ _ _ _ hp1 hx2)|exact hp2].
      Qed.

      Lemma rn_tree'_g : forall m g m' g' Gn, gcg Gn g -> rn_tree' cp m g = COk (m', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn'
          /\ (forall p a', PTree.get' p m' = Some a' ->
                exists a, PTree.get' p m = Some a
                  /\ (forall t, G a = Some t -> Gn' a' = Some t)).
      Proof.
        induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
          intros g m' g' Gn hg he; simpl in he.
        - (* Node001 *)
          destruct (rn_tree' cp r g) as [[r' g1]|w] eqn:e1; [|discriminate].
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
          destruct (rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (hcp _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & ha1).
          destruct (ihr _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          + exact (hr2 _ _ hb).
          + injection hb as <-. exists x. split; [reflexivity|].
            intros t ht. exact (hx2 _ _ (ha1 _ ht)).
        - (* Node100 *)
          destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          exists Gn1. split; [exact hg1|]. split; [exact hx1|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          exact (hr1 _ _ hb).
        - (* Node101 *)
          destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          destruct (rn_tree' cp r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (ihr _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hr2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          + exact (hr2 _ _ hb).
          + destruct (hr1 _ _ hb) as [a [ha hr]]. exists a. split; [exact ha|].
            intros t ht. exact (hx2 _ _ (hr _ ht)).
        - (* Node110 *)
          destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (hcp _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & ha2).
          exists Gn2. split; [exact hg2|]. split; [exact (gext_trans _ _ _ hx1 hx2)|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *; try discriminate.
          + destruct (hr1 _ _ hb) as [a [ha hr]]. exists a. split; [exact ha|].
            intros t ht. exact (hx2 _ _ (hr _ ht)).
          + injection hb as <-. exists x. split; [reflexivity|exact ha2].
        - (* Node111 *)
          destruct (rn_tree' cp l g) as [[l' g1]|w] eqn:e1; [|discriminate].
          destruct (cp x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
          destruct (rn_tree' cp r g2) as [[r' g3]|w] eqn:e3; [|discriminate].
          inversion he; subst; clear he.
          destruct (ihl _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hr1).
          destruct (hcp _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & ha2).
          destruct (ihr _ _ _ _ hg2 e3) as (Gn3 & hg3 & hx3 & hr3).
          exists Gn3. split; [exact hg3|].
          split; [exact (gext_trans _ _ _ hx1 (gext_trans _ _ _ hx2 hx3))|].
          intros p b hb. destruct p as [q|q|]; simpl in hb |- *.
          + exact (hr3 _ _ hb).
          + destruct (hr1 _ _ hb) as [a [ha hr]]. exists a. split; [exact ha|].
            intros t ht. exact (hx3 _ _ (hx2 _ _ (hr _ ht))).
          + injection hb as <-. exists x. split; [reflexivity|].
            intros t ht. exact (hx3 _ _ (ha2 _ ht)).
      Qed.

      Lemma rn_ptree_g m g m' g' Gn : gcg Gn g -> rn_ptree cp m g = COk (m', g') ->
        exists Gn', gcg Gn' g' /\ gext Gn Gn'
          /\ (forall p a', PTree.get p m' = Some a' ->
                exists a, PTree.get p m = Some a
                  /\ (forall t, G a = Some t -> Gn' a' = Some t)).
      Proof.
        destruct m as [|m]; intros hg he; unfold rn_ptree in he.
        - inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply gext_refl|].
          intros p b hb. discriminate hb.
        - destruct (rn_tree' cp m g) as [[m2 g1]|w] eqn:e1; [|discriminate].
          inversion he; subst; clear he.
          destruct (rn_tree'_g _ _ _ _ _ hg e1) as (Gn' & hg' & hx' & hr).
          exists Gn'. split; [exact hg'|]. split; [exact hx'|].
          intros p b hb. exact (hr p b hb).
      Qed.
    End Walk.

    (** One copied cell: its children are renamed, the copy goes to the fresh address
      [g_next], and the ghost of the new heap is extended there by the old ghost term. *)
    Lemma gc_copy_g_write k a g cl cl1 g1 old Gn :
      cpg (gc_copy k) -> gcg Gn g -> bh_get a g.(g_old) = Some cl -> cell_fwd cl = None ->
      rn_cell (gc_copy k) cl g = COk (cl1, g1) ->
      bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old) = Some old ->
      gc_inv nctx s.(st_heap) s.(st_next)
        (mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next))) ->
      exists Gn', gcg Gn' (mkGc old (bh_cons cl1 g1.(g_heap)) (Pos.succ g1.(g_next)))
        /\ gext Gn Gn' /\ (forall t, G a = Some t -> Gn' (HAddr g1.(g_next)) = Some t).
    Proof.
      intros hk hg ha hf e1 e2 hinv2.
      assert (hcl : bh_get a s.(st_heap) = Some cl)
        by exact (inv_keep _ _ _ _ (gg_inv _ _ hg) _ _ ha hf).
      destruct (gk_cells _ _ _ hok a cl hcl) as [t0 [hGa hc0]].
      destruct (rn_cell_g _ hk _ _ _ _ _ hg e1) as (Gn1 & hg1 & hx1 & hbusy & hr1).
      pose proof (inv_heap _ _ _ _ (gg_inv _ _ hg1)) as hok1.
      pose (Gn' := mkGhost (fun b => if haddr_eqb b (HAddr g1.(g_next)) then Some t0 else Gn1 b)
                     (gc Gn1)).
      assert (hfresh : forall b t, Gn1 b = Some t -> b <> HAddr g1.(g_next)).
      { intros b t hb ->. destruct (gg_dom _ _ hg1 _ _ hb) as [_ hlt]. cbn in hlt. lia. }
      assert (hx2 : gext Gn1 Gn').
      { split; [|intros i e hi; exact hi].
        intros b t hb. unfold Gn'. cbn [gm].
        destruct (haddr_eqb b (HAddr g1.(g_next))) eqn:eb; [|exact hb].
        apply haddr_eqb_eq in eb. exfalso. exact (hfresh _ _ hb eb). }
      assert (hnew : Gn' (HAddr g1.(g_next)) = Some t0).
      { unfold Gn'. cbn [gm]. rewrite haddr_eqb_refl. reflexivity. }
      exists Gn'. split; [|split; [exact (gext_trans _ _ _ hx1 hx2)|]].
      2: { intros t ht. rewrite hGa in ht. injection ht as <-. exact hnew. }
      split; cbn [g_old g_heap g_next].
      - exact hinv2.
      - unfold Gn'. cbn [gc]. exact (gg_codes _ _ hg1).
      - intros x b t hx ht. destruct (haddr_dec x a) as [->|hne].
        + rewrite (bh_get_upd_same _ _ _ _ e2) in hx. injection hx as <-.
          rewrite hGa in ht. injection ht as <-. exact hnew.
        + rewrite (bh_get_upd_other _ _ _ _ _ e2 hne) in hx.
          exact (hx2 _ _ (gg_fwd _ _ hg1 _ _ _ hx ht)).
      - intros b cl' hb. destruct (haddr_dec b (HAddr g1.(g_next))) as [->|hne].
        + rewrite (bh_get_cons_new _ _ _ _ hok1) in hb. injection hb as <-.
          exists t0. split; [exact hnew|].
          destruct hc0 as [->|[u [hu hred]]]; [left; exact (hbusy eq_refl)|].
          right. exists u. split; [exact (g_cell_mono _ _ hx2 _ _ (hr1 _ hu))|exact hred].
        + rewrite (bh_get_cons_old _ _ _ _ _ hok1 hne) in hb.
          destruct (gg_cells _ _ hg1 _ _ hb) as [t [ht hc]].
          exists t. split; [exact (hx2 _ _ ht)|].
          destruct hc as [hb'|[u [hu hred]]]; [left; exact hb'|].
          right. exists u. split; [exact (g_cell_mono _ _ hx2 _ _ hu)|exact hred].
      - intros b t hb. unfold Gn' in hb. cbn [gm] in hb.
        destruct (haddr_eqb b (HAddr g1.(g_next))) eqn:eb.
        + apply haddr_eqb_eq in eb. subst b. cbn.
          split; [exact (bh_ok_le _ _ _ hok1)|lia].
        + destruct (gg_dom _ _ hg1 _ _ hb) as [h1 h2]. split; [exact h1|]. cbn. lia.
    Qed.

    Lemma gc_copy_g : forall f, cpg (gc_copy f).
    Proof.
      intros f. induction f as [|k ih]; intros a g a' g' Gn hg he.
      - rewrite gc_copy_FO in he.
        destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
        destruct cl as [vals n o c|v| |b]; try discriminate.
        inversion he; subst; clear he.
        exists Gn. split; [exact hg|]. split; [apply gext_refl|].
        intros t ht. exact (gg_fwd _ _ hg _ _ _ ea ht).
      - pose proof he as he0.
        destruct (gc_copy_ok nctx s.(st_heap) s.(st_next) (FS k) a g a' g' (gg_inv _ _ hg) he0)
          as [hst _].
        rewrite gc_copy_FS in he.
        destruct (bh_get a g.(g_old)) as [cl|] eqn:ea; [|discriminate].
        destruct cl as [vals n o c|v| |b].
        + destruct (rn_cell (gc_copy (k tt)) (CSusp vals n o c) g) as [[cl1 g1]|w] eqn:e1;
            [|discriminate].
          destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
            [|discriminate].
          inversion he; subst; clear he.
          exact (gc_copy_g_write _ _ _ _ _ _ _ _ (ih tt) hg ea eq_refl e1 e2
                   (step_inv _ _ _ _ _ hst)).
        + destruct (rn_cell (gc_copy (k tt)) (CDone v) g) as [[cl1 g1]|w] eqn:e1;
            [|discriminate].
          destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
            [|discriminate].
          inversion he; subst; clear he.
          exact (gc_copy_g_write _ _ _ _ _ _ _ _ (ih tt) hg ea eq_refl e1 e2
                   (step_inv _ _ _ _ _ hst)).
        + destruct (rn_cell (gc_copy (k tt)) CBusy g) as [[cl1 g1]|w] eqn:e1; [|discriminate].
          destruct (bh_upd a (CFwd (HAddr g1.(g_next))) g1.(g_old)) as [old|] eqn:e2;
            [|discriminate].
          inversion he; subst; clear he.
          exact (gc_copy_g_write _ _ _ _ _ _ _ _ (ih tt) hg ea eq_refl e1 e2
                   (step_inv _ _ _ _ _ hst)).
        + inversion he; subst; clear he.
          exists Gn. split; [exact hg|]. split; [apply gext_refl|].
          intros t ht. exact (gg_fwd _ _ hg _ _ _ ea ht).
    Qed.

    (** The ghost invariant survives a collection: the state after it is [gok] at the old
      [st_next] for the ghost of the new heap, and every root comes back renamed with the
      reading it had. *)
    Lemma collect_ghost rs rs' s' :
      collect rs s = COk (rs', s') ->
      exists G', gc G' = gc G /\ Forall2 (gpres G G') rs rs' /\ gok s.(st_next) G' s'.
    Proof.
      intros he.
      destruct (collect_sound nctx rs s rs' s' (gk_nofwd _ _ _ hok) he)
        as (hso & hnf & _ & _ & _ & _).
      rewrite collect_eq in he.
      destruct (rn_ptree (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) s.(st_gam)
                  (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))) as [[gm1 g1]|w1] eqn:e1;
        [|discriminate].
      destruct (rn_roots (gc_copy (fuel_of_pos s.(st_next) (fun _ => FO))) rs g1)
        as [[rs2 g2]|w2] eqn:e2; [|discriminate].
      inversion he; subst; clear he.
      assert (hg0 : gcg (mkGhost (fun _ => None) (gc G))
                      (mkGc s.(st_heap) (bh_holes s.(st_next)) s.(st_next))).
      { split; cbn [g_old g_heap g_next gc gm].
        - constructor; cbn.
          + intros a cl hc _. exact hc.
          + intros a a' hc. destruct (gk_nofwd _ _ _ hok _ _ hc).
          + apply bh_ok_holes.
          + intros b cl hc. rewrite bh_get_holes in hc. discriminate.
          + intros b b' hc. rewrite bh_get_holes in hc. discriminate.
        - reflexivity.
        - intros x b t hx _. destruct (gk_nofwd _ _ _ hok _ _ hx).
        - intros b cl hc. rewrite bh_get_holes in hc. discriminate.
        - intros b t hb. discriminate hb. }
      destruct (rn_ptree_g _ (gc_copy_g _) _ _ _ _ _ hg0 e1) as (Gn1 & hg1 & hx1 & hgam).
      destruct (rn_roots_g _ (gc_copy_g _) _ _ _ _ _ hg1 e2) as (Gn2 & hg2 & hx2 & hroots).
      exists Gn2. split; [exact (gg_codes _ _ hg2)|]. split; [exact hroots|].
      split.
      - exact hso.
      - exact hnf.
      - intros a cl hc. exact (gg_cells _ _ hg2 _ _ hc).
      - intros a t ht. exact (gg_dom _ _ hg2 _ _ ht).
      - intros j a' hj. cbn [st_gam] in hj. destruct (hgam _ _ hj) as [a [ha hr]].
        destruct (gk_gam _ _ _ hok _ _ ha) as [t [hden hGa]].
        exists t. split; [exact hden|]. exact (hx2 _ _ (hr _ hGa)).
      - rewrite (gg_codes _ _ hg2).
        apply (mok_memo _ s); [reflexivity|exact (gk_memo _ _ _ hok)].
    Qed.
  End GhostCollect.

  (** *** Allocation, which may collect first *)

  Lemma alloc_now_sound lo G cl u s :
    gok lo G s -> g_cell G cl u ->
    exists G', gext G G' /\ gok lo G' (snd (alloc_now cl s))
      /\ G' (fst (alloc_now cl s)) = Some u.
  Proof.
    intros hok hcl. cbn [alloc_now fst snd].
    pose (G' := mkGhost (fun b => if haddr_eqb b (HAddr s.(st_next)) then Some u else G b)
                  (gc G)).
    assert (hnew : G' (HAddr s.(st_next)) = Some u).
    { unfold G'. cbn [gm]. rewrite haddr_eqb_refl. reflexivity. }
    assert (hold : gext G G').
    { split; [|intros i e hi; exact hi].
      intros b t hb. unfold G'. cbn [gm]. destruct (haddr_eqb b (HAddr s.(st_next))) eqn:eb;
        [|exact hb].
      apply haddr_eqb_eq in eb. subst b.
      destruct (gk_dom _ _ _ hok _ _ hb) as [_ hlt]. cbn in hlt. lia. }
    assert (hbok : bh_ok lo s.(st_next) s.(st_heap))
      by exact (so_heap _ _ (gk_state _ _ _ hok)).
    exists G'. split; [exact hold|].
    split; [|exact hnew].
    split.
    - apply (alloc_now_state_ok lo cl s (gk_state _ _ _ hok)).
      apply (addrs_in_grow lo s.(st_next) (Pos.succ s.(st_next))); [lia|].
      apply (gdom_addrs_in lo G s); [exact (gk_dom _ _ _ hok)|].
      exact (g_cell_ad G cl u hcl).
    - intros b b' hb. cbn in hb.
      destruct (haddr_dec b (HAddr s.(st_next))) as [->|hne].
      + rewrite (bh_get_cons_new _ _ _ _ hbok) in hb. injection hb as ->. inversion hcl.
      + rewrite (bh_get_cons_old _ _ _ _ _ hbok hne) in hb. exact (gk_nofwd _ _ _ hok _ _ hb).
    - intros b cl2 hb. unfold heap_get in hb. cbn in hb.
      destruct (haddr_dec b (HAddr s.(st_next))) as [->|hne].
      + rewrite (bh_get_cons_new _ _ _ _ hbok) in hb.
        inversion hb; subst cl2. exists u. split; [exact hnew|].
        right. exists u. split; [exact (g_cell_mono G G' hold cl u hcl)|apply cred_refl].
      + rewrite (bh_get_cons_old _ _ _ _ _ hbok hne) in hb.
        destruct (gk_cells _ _ _ hok _ _ hb) as [t [ht hrest]].
        exists t. split; [exact (hold _ _ ht)|].
        destruct hrest as [hbusy|[u1 [hu1 hred]]]; [left; exact hbusy|].
        right. exists u1. split; [exact (g_cell_mono G G' hold _ _ hu1)|exact hred].
    - intros b t hb. unfold G' in hb. cbn [gm] in hb. cbn.
      destruct (haddr_eqb b (HAddr s.(st_next))) eqn:eb.
      + apply haddr_eqb_eq in eb. subst b. cbn.
        split; [exact (bh_ok_le _ _ _ hbok)|lia].
      + destruct (gk_dom _ _ _ hok _ _ hb) as [h1 h2]. split; [exact h1|]. cbn. lia.
    - intros j b hj. cbn in hj.
      destruct (gk_gam _ _ _ hok _ _ hj) as [t [ht hg]].
      exists t. split; [exact ht|exact (hold _ _ hg)].
    - exact (gk_memo _ _ _ hok).
  Qed.

  (** [alloc] collects when [gc_due] says so, whatever [stress] is: the roots come back
    renamed ([collect_ghost]) and the new cell is allocated in the new heap. *)
  Lemma alloc_sound lo G cl u rs s a rs' s' :
    gok lo G s -> g_cell G cl u ->
    alloc stress cl rs s = COk (a, rs', s') ->
    exists lo' G', gren G G' rs rs' /\ gok lo' G' s' /\ G' a = Some u.
  Proof.
    intros hok hcl he.
    destruct (gc_due stress s) eqn:eg.
    - rewrite (alloc_gc stress cl rs s eg) in he.
      destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:ec; [|discriminate].
      destruct (collect_ghost lo G s hok _ _ _ ec) as (G1 & hc1 & hf1 & hok1).
      inversion hf1 as [|r1 r1' l1 l1' hp1 hf1']; subst.
      destruct r1' as [| | | | | |cl1]; try discriminate he.
      cbn [gpres] in hp1.
      destruct (alloc_now_sound _ _ _ _ _ hok1 (hp1 _ hcl)) as (G2 & hx2 & hok2 & ha2).
      cbn [alloc_now] in he. inversion he; subst; clear he.
      exists s.(st_next), G2. split; [|split; [exact hok2|exact ha2]].
      split.
      + intros i e hi. apply (gx_codes hx2). rewrite hc1. exact hi.
      + exact (Forall2_gpres_r_ext _ _ _ _ _ hf1' hx2).
    - rewrite (alloc_no_gc stress cl rs s eg) in he. inversion he; subst; clear he.
      destruct (alloc_now_sound _ _ _ _ _ hok hcl) as (G2 & hx2 & hok2 & ha2).
      exists lo, G2. split; [exact (gren_ext _ _ _ hx2)|]. split; [exact hok2|exact ha2].
  Qed.

  (** *** The context map *)

  Lemma gam_sound lo G j rs s a rs' s' :
    gok lo G s ->
    gam X_type X Γ nctx stress j rs s = COk (a, rs', s') ->
    exists lo' G' t, gren G G' rs rs' /\ gok lo' G' s' /\ G' a = Some t
                     /\ cred (tRel (lvl - nctx + j)) t.
  Proof.
    intros hok he. unfold gam in he. cbv zeta in he.
    destruct (PTree.get (key_of_succ_nat j) s.(st_gam)) as [a0|] eqn:eg.
    - inversion he; subst. clear he.
      destruct (gk_gam _ _ _ hok _ _ eg) as [t [ht hg]].
      exists lo, G, t. split; [apply gren_refl|].
      split; [exact hok|]. split; [exact hg|exact (ctx_den_red j t ht)].
    - destruct (nth_error Γ j) as [decl|] eqn:ed; [|discriminate].
      assert (hmain : forall G0 cl t s1,
        gext G G0 ->
        ctx_den Γ nctx lvl j = Some t -> g_cell G0 cl t -> gok lo G0 s1 ->
        (match alloc stress cl rs s1 with
         | COk (a2, rs2, s2) =>
             COk (a2, rs2, set_gam (PTree.set (key_of_succ_nat j) a2 (st_gam s2)) s2)
         | CFail w => CFail w
         end) = COk (a, rs', s') ->
        exists lo' G' t2, gren G G' rs rs' /\ gok lo' G' s' /\ G' a = Some t2
                          /\ cred (tRel (lvl - nctx + j)) t2).
      { intros G0 cl t s1 hx0 hden hcl hok1 hm.
        destruct (alloc stress cl rs s1) as [[[a1 rs1] s2]|w] eqn:ea; [|discriminate].
        inversion hm; subst. clear hm.
        destruct (alloc_sound lo G0 cl t rs s1 _ _ _ hok1 hcl ea)
          as (lo2 & G' & hren & hok2 & hga).
        destruct (gk_dom _ _ _ hok2 _ _ hga) as [hlo hlt].
        exists lo2, G', t. split; [exact (gren_trans _ _ _ _ _ _ (gren_ext _ _ _ hx0) hren)|].
        split; [|split; [exact hga|exact (ctx_den_red j t hden)]].
        split; cbn.
        - exact (state_ok_set_gam lo2 j _ _ (gk_state _ _ _ hok2) hlo hlt).
        - exact (gk_nofwd _ _ _ hok2).
        - exact (gk_cells _ _ _ hok2).
        - exact (gk_dom _ _ _ hok2).
        - intros j2 a2 hj2.
          destruct (key_eqb (key_of_succ_nat j2) (key_of_succ_nat j)) eqn:ek.
          + apply key_eqb_spec, key_of_succ_nat_inj in ek. subst j2.
            rewrite PTree.gss in hj2. injection hj2 as <-.
            exists t. split; [exact hden|exact hga].
          + rewrite PTree.gso in hj2 by (apply key_neq_of_eqb, ek).
            exact (gk_gam _ _ _ hok2 _ _ hj2).
        - exact (gk_memo _ _ _ hok2). }
      destruct decl.(decl_body) as [b|] eqn:eb.
      + destruct (new_entry X_type X b [] (NSCtx j) s) as [c s1] eqn:e1.
        assert (hc : c = fst (new_entry X_type X b [] (NSCtx j) s)) by (rewrite e1; reflexivity).
        assert (hs1 : s1 = snd (new_entry X_type X b [] (NSCtx j) s))
          by (rewrite e1; reflexivity).
        assert (hct : c.(c_term) = b) by (rewrite hc, new_entry_term; reflexivity).
        destruct (new_entry_shape b [] (NSCtx j) s) as (q1 & q2 & q3 & _ & q5 & _).
        destruct (gk_memo _ _ _ hok) as (hmi & hmo & hcodes & hokb).
        pose proof hmi as (hf & _).
        assert (hgrow : forall i e, PTree.get i (gc G) = Some e ->
                   PTree.get i ((s1.(st_memo)).(m_codes)) = Some e).
        { intros i e hi. rewrite hs1, new_entry_codes.
          exact (memo_codes_set_mono _ _ i e hf (hcodes i e hi)). }
        assert (hm1 : mok ((s1.(st_memo)).(m_codes)) s1).
        { rewrite hs1. split; [exact (memo_inv_new_entry X_type X b [] (NSCtx j) s hmi)|].
          split; [exact (new_entry_memo_ok X_type X b [] (NSCtx j) s hmo)|].
          split; [intros i e hi; exact hi|].
          intros i e hi. rewrite new_entry_codes in hi.
          destruct (key_eqb i ((s.(st_memo)).(m_ncode))) eqn:E.
          - apply key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
            injection hi as <-. cbn [ce_inst ce_term inst_code].
            exact (const_instance_ok j decl b ed eb).
          - rewrite PTree.gso in hi by (apply key_neq_of_eqb, E). exact (hokb i e hi). }
        pose (G1 := mkGhost (gm G) ((s1.(st_memo)).(m_codes))).
        assert (hx1 : gext G G1) by (split; [intros a1 t1 h; exact h|exact hgrow]).
        assert (hok1 : gok lo G1 s1).
        { apply (gok_recode lo G s s1);
            [exact hok|rewrite hs1; exact q1|rewrite hs1; exact q2|rewrite hs1; exact q5
            |exact hgrow|exact hm1]. }
        assert (hcok : cok G1 c).
        { exists (mkEntry b [] (NSCtx j) (wf_term_univs X_type X (inst_code [] b))).
          split.
          - unfold G1. cbn [gc]. rewrite hc, hs1. apply new_entry_in_table.
          - rewrite hc. apply new_entry_code_inv. }
        apply (hmain G1 (CSusp [] 0 (S j) c) (lift (lvl - nctx + S j) 0 c.(c_term)) s1 hx1).
        * unfold ctx_den. rewrite ed, eb, hct. reflexivity.
        * constructor; [|exact hcok].
          rewrite <- (subst_empty 0 (lift (lvl - nctx + S j) 0 c.(c_term))).
          exact (g_susp_intro G1 [] 0 (S j) c.(c_term) [] (g_slots_nil G1) eq_refl).
        * exact hok1.
        * exact he.
      + apply (hmain G (CDone (VNeu (NVar (nctx - S j)) [])) (tRel (lvl - S (nctx - S j))) s
                 (gext_refl G)).
        * unfold ctx_den. rewrite ed, eb. reflexivity.
        * constructor. exact (g_VNeuVar G (nctx - S j) [] [] (Forall2_nil _)).
        * exact hok.
        * exact he.
  Qed.

  (** *** Reading a variable of the environment *)

  Lemma env_var_sound lo G n e rs s x rs' s' tu :
    gok lo G s -> g_susp G e (tRel n) tu ->
    env_var X_type X Γ nctx stress n e rs s = COk (x, rs', s') ->
    exists lo' G' t, gren G G' rs rs' /\ gok lo' G' s' /\ g_slot G' x t /\ cred tu t.
  Proof.
    intros hok hsusp he. unfold env_var in he.
    destruct (g_susp_inv _ _ _ _ hsusp) as [ts (h1 & h2 & ->)].
    destruct (nth_error e.(ev_vals) n) as [x0|] eqn:en.
    - inversion he; subst. clear he.
      assert (hlt : n < #|e.(ev_vals)|) by (apply nth_error_Some_length in en; exact en).
      destruct (g_slots_nth _ _ _ _ _ h1 en) as [t [hnt hgt]].
      exists lo, G, t. split; [apply gren_refl|]. split; [exact hok|].
      split; [exact hgt|].
      rewrite h2, (lift_rel_lt (lvl - nctx + e.(ev_goff)) n #|e.(ev_vals)|); [|lia].
      rewrite (subst_rel_eq ts 0 n t n hnt eq_refl), lift0_id. apply cred_refl.
    - destruct (gam X_type X Γ nctx stress (n - e.(ev_nvals) + e.(ev_goff)) rs s)
        as [[[a1 rs1] s1]|w] eqn:eg; [|discriminate].
      inversion he; subst. clear he.
      destruct (gam_sound lo G (n - e.(ev_nvals) + e.(ev_goff)) rs s _ _ _ hok eg)
        as (lo1 & G' & t & hren & hok1 & hga & hred).
      assert (hge : #|e.(ev_vals)| <= n) by (apply nth_error_None in en; exact en).
      exists lo1, G', t. split; [exact hren|]. split; [exact hok1|].
      split; [constructor; exact hga|].
      rewrite h2.
      rewrite (lift_rel_ge (lvl - nctx + e.(ev_goff)) n #|e.(ev_vals)|); [|lia].
      rewrite (subst_rel_gt ts (lvl - nctx + e.(ev_goff) + n) 0);
        [|rewrite (g_slots_length _ _ _ h1); lia].
      rewrite (g_slots_length _ _ _ h1).
      replace (lvl - nctx + e.(ev_goff) + n - #|e.(ev_vals)|)
        with (lvl - nctx + (n - e.(ev_nvals) + e.(ev_goff))) by lia.
      exact hred.
  Qed.

  (** *** The slot of an argument *)

  Lemma arg_slot_sound lo G e c rs s x rs' s' tu :
    gok lo G s -> g_susp G e c.(c_term) tu -> cok G c ->
    arg_slot X_type X Γ nctx stress e c rs s = COk (x, rs', s') ->
    exists lo' G' t, gren G G' rs rs' /\ gok lo' G' s' /\ g_slot G' x t /\ cred tu t.
  Proof.
    intros hok hsusp hcok he. unfold arg_slot in he.
    destruct (g_susp_inv _ _ _ _ hsusp) as [ts (h1 & h2 & ->)].
    destruct e as [vals nvals goff]. cbn [ev_vals ev_nvals ev_goff] in *.
    destruct (c_term c) eqn:ec;
      [ refine (env_var_sound lo G n (mkEnv vals nvals goff) rs s x rs' s' _ hok _ he);
        exact hsusp | .. ].
    all: inversion he; subst; clear he.
    all: exists lo, G; eexists; split; [apply gren_refl|]; split; [exact hok|];
         split; [|apply cred_refl].
    all: rewrite <- ec; constructor; [exact h1|try reflexivity; try assumption|exact hcok].
  Qed.

  (** *** Putting a slot in the heap *)

  Lemma materialize_sound lo G x rs s a rs' s' t :
    gok lo G s -> g_slot G x t ->
    materialize X_type X stress x rs s = COk (a, rs', s') ->
    exists lo' G', gren G G' rs rs' /\ gok lo' G' s' /\ G' a = Some t.
  Proof.
    intros hok hx he. unfold materialize in he.
    destruct x as [a0|vals n o c].
    - inversion hx; subst. inversion he; subst. clear he.
      exists lo, G. split; [apply gren_refl|]. split; [exact hok|assumption].
    - inversion hx; subst. clear hx.
      match goal with h1 : g_slots G vals ?ts0 |- _ =>
        assert (hsusp : g_susp G (mkEnv vals #|vals| o) c.(c_term)
                          (subst ts0 0 (lift (lvl - nctx + o) #|vals| c.(c_term))))
          by (constructor; [exact h1|reflexivity])
      end.
      remember (subst _ 0 (lift (lvl - nctx + o) #|vals| c.(c_term))) as t0 eqn:ht0.
      destruct (c_term c) eqn:ec.
      all: try (assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
                  by (constructor; [rewrite ec; exact hsusp|assumption]);
                exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he)).
      + (* tSort *)
        assert (hcl : g_cell G (CDone (VOpen (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
      + (* tProd *)
        assert (hcl : g_cell G (CDone (VOpen (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
      + (* tLambda *)
        assert (hcl : g_cell G (CDone (VLam (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
      + (* tConst: the memo may add an entry first *)
        match type of he with context [delta X_type X ?kn ?ui s] =>
          destruct (delta X_type X kn ui s) as [[[c'|] s1]|w] eqn:ed
        end.
        * pose proof (delta_gok lo G _ _ s _ s1 hok ed) as hok1.
          assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
            by (constructor; [rewrite ec; exact hsusp|assumption]).
          exact (alloc_sound lo G _ _ rs s1 a rs' s' hok1 hcl he).
        * pose proof (delta_gok lo G _ _ s _ s1 hok ed) as hok1.
          assert (hcl : g_cell G (CDone (VNeu (NConst (tConst k ui)) [])) t0).
          { constructor. rewrite ht0, subst_lift_const.
            exact (g_VNeuConst G (tConst k ui) [] [] (Forall2_nil _)). }
          exact (alloc_sound lo G _ _ rs s1 a rs' s' hok1 hcl he).
        * assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
            by (constructor; [rewrite ec; exact hsusp|assumption]).
          exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
      + (* tFix: a fixpoint value, or a suspension if the index is out of range *)
        match goal with ec' : c_term c = tFix ?m ?i |- _ =>
          destruct (nth_error m i) as [def|] eqn:enth
        end.
        * match goal with ec' : c_term c = tFix ?m ?i |- _ =>
            assert (hcl : g_cell G (CDone (VFix (mkEnv vals #|vals| o) c i [])) t0)
          end.
          { constructor. change t0 with (mkApps t0 []).
            eapply g_VFix; [exact ec| |assumption|constructor].
            first [exact hsusp|rewrite <- ec; exact hsusp|rewrite ec in hsusp; exact hsusp]. }
          exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
        * assert (hcl : g_cell G (CSusp vals #|vals| o c) t0)
            by (constructor; [rewrite ec; exact hsusp|assumption]).
          exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
      + (* tPrim *)
        assert (hcl : g_cell G (CDone (VOpen (mkEnv vals #|vals| o) c)) t0)
          by (constructor; constructor; [rewrite ec; exact hsusp|assumption]).
        exact (alloc_sound lo G _ _ rs s a rs' s' hok hcl he).
  Qed.

  (** *** Binding a slot to a binder *)

  Lemma bind_sound lo G x body rs s y rs' s' t :
    gok lo G s -> g_slot G x t -> cok G body ->
    bind X_type X stress x body rs s = COk (y, rs', s') ->
    exists lo' G', gren G G' rs rs' /\ gok lo' G' s' /\ g_slot G' y t.
  Proof.
    intros hok hx hcb he. unfold bind in he.
    destruct x as [a0|vals n o c].
    - inversion he; subst. clear he.
      exists lo, G. split; [apply gren_refl|]. split; [exact hok|exact hx].
    - destruct (once_body body s) as [b s1] eqn:eo.
      destruct (once_body_shape body s) as (q1 & q2 & q3 & _ & q5 & _).
      assert (hs1 : s1 = snd (once_body body s)) by (rewrite eo; reflexivity).
      assert (hok1 : gok lo G s1).
      { destruct hcb as [e [hge hci]].
        apply (gok_same lo G s);
          [exact hok|rewrite hs1; exact q1|rewrite hs1; exact q2|rewrite hs1; exact q5|].
        rewrite hs1. destruct (gk_memo _ _ _ hok) as (_ & _ & h3 & _).
        exact (mok_once_body _ body e s (gk_memo _ _ _ hok) (h3 _ _ hge) hci). }
      clear hs1.
      destruct b.
      + inversion he; subst. clear he.
        exists lo, G. split; [apply gren_refl|]. split; [exact hok1|exact hx].
      + destruct (materialize X_type X stress (SInl vals n o c) rs s1)
          as [[[a1 rs1] s2]|w] eqn:em; [|discriminate].
        destruct (materialize_sound lo G (SInl vals n o c) rs s1 a1 rs1 s2 t hok1 hx em)
          as (lo2 & G2 & hren & hok2 & hga).
        inversion he; subst. clear he.
        exists lo2, G2. split; [exact hren|]. split; [exact hok2|constructor; exact hga].
  Qed.

  (** *** A whole stack put in the heap *)

  Lemma mat_all_sound : forall d lo G l ts rs s al rs' s',
    gok lo G s -> g_slots G l ts ->
    mat_all X_type X stress d l rs s = COk (al, rs', s') ->
    exists lo' G', gren G G' rs rs' /\ gok lo' G' s' /\ g_addrs G' al ts.
  Proof.
    intros d. induction d as [|k ih]; intros lo G l ts rs s al rs' s' hok hl he;
      destruct l as [|x l]; cbn [mat_all] in he.
    1,3: inversion he; subst; clear he; inversion hl; subst;
         exists lo, G; (split; [apply gren_refl|]); (split; [exact hok|constructor]).
    - discriminate.
    - inversion hl as [|x' l' tx ts0 hgx hgl hex hets]; subst; clear hl.
      destruct (materialize X_type X stress x (RSk l :: rs) s) as [[[a1 rs1] s1]|w] eqn:em;
        [|discriminate].
      destruct (materialize_sound lo G x (RSk l :: rs) s a1 rs1 s1 tx hok hgx em)
        as (lo1 & G1 & hren1 & hok1 & hga1).
      destruct rs1 as [|r rs1t]; [discriminate he|].
      destruct r as [| | | |l1| |]; try discriminate he.
      destruct (gren_cons _ _ _ _ _ _ hren1) as [hpk hren1']. cbn [gpres] in hpk.
      destruct (mat_all X_type X stress (k tt) l1 (RA a1 :: rs1t) s1)
        as [[[al1 rs2] s2]|w] eqn:em2; [|discriminate].
      destruct rs2 as [|r rs2t]; [discriminate he|].
      destruct r as [a0| | | | | |]; try discriminate he.
      injection he as hal hrs' hs'; subst al rs' s'.
      destruct (ih tt lo1 G1 l1 ts0 (RA a1 :: rs1t) s1 al1 (RA a0 :: rs2t) s2 hok1
                  (hpk _ hgl) em2)
        as (lo2 & G2 & hren2 & hok2 & haddr2).
      destruct (gren_cons _ _ _ _ _ _ hren2) as [hpa hren2']. cbn [gpres] in hpa.
      exists lo2, G2. split; [exact (gren_trans _ _ _ _ _ _ hren1' hren2')|].
      split; [exact hok2|].
      constructor; [exact (hpa _ hga1)|exact haddr2].
  Qed.

  (** A value grows its spine: what [apply] does to a constructor, a neutral, a stuck match
    or projection, and a stuck fixpoint once the stack is in the heap. *)
  Lemma g_value_add_spine G v t l ts v' :
    g_value G v t -> g_addrs G l ts -> add_spine v l = Some v' -> g_value G v' (mkApps t ts).
  Proof.
    intros hv hl ha. destruct hv; cbn in ha; try discriminate ha; injection ha as <-.
    all: rewrite <- mkApps_app; econstructor; try eassumption; apply Forall2_app; assumption.
  Qed.

  (** *** The cells of a fixpoint block

    [push_fix_cells] allocates fixpoint [i], ..., [i + m - 1] of the [tFix] code [c] as
    values over [e] and pushes them on [acc]: the new slots stand for those fixpoints read
    through [e], the last one first, which is [fix_subst]'s order. *)

  Lemma push_fix_cells_sound : forall m lo G e c mfix idx0 ts i acc tacc rs s e' rs' s',
    gok lo G s -> c.(c_term) = tFix mfix idx0 -> cok G c ->
    g_slots G e.(ev_vals) ts -> e.(ev_nvals) = #|e.(ev_vals)| ->
    g_slots G acc.(ev_vals) tacc -> acc.(ev_nvals) = #|acc.(ev_vals)| ->
    push_fix_cells stress e c i m acc rs s = COk (e', rs', s') ->
    exists lo' G', gren G G' rs rs' /\ gok lo' G' s'
       /\ g_slots G' e'.(ev_vals)
            (List.rev (map (fun j => subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals)
                                                     (tFix mfix j))) (seq i m)) ++ tacc)
       /\ e'.(ev_nvals) = #|e'.(ev_vals)| /\ e'.(ev_goff) = acc.(ev_goff).
  Proof.
    intros m. induction m as [|m ih];
      intros lo G e c mfix idx0 ts i acc tacc rs s e' rs' s'
        hok hc hcok hts hnv hacc hnacc he.
    - cbn [push_fix_cells] in he. inversion he; subst. clear he.
      exists lo, G. split; [apply gren_refl|]. split; [exact hok|].
      cbn [seq map List.rev app]. split; [exact hacc|]. split; [exact hnacc|reflexivity].
    - cbn [push_fix_cells] in he.
      destruct (alloc stress (CDone (VFix e c i [])) (RE e :: RE acc :: rs) s)
        as [[[a1 rs1] s1]|w] eqn:ea; [|discriminate he].
      set (tf := fun j => subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals) (tFix mfix j))).
      assert (hcl : g_cell G (CDone (VFix e c i [])) (tf i)).
      { constructor. exact (g_VFix G e c mfix idx0 i [] (tf i) [] hc
                              (g_susp_of_slots G e _ ts hts hnv) hcok (Forall2_nil _)). }
      destruct (alloc_sound lo G _ _ _ s a1 rs1 s1 hok hcl ea)
        as (lo1 & G1 & hren1 & hok1 & hga1).
      destruct rs1 as [|r1 rs1a]; [discriminate he|].
      destruct r1 as [| |e1| | | |]; try discriminate he.
      destruct rs1a as [|r2 rs1b]; [discriminate he|].
      destruct r2 as [| |acc1| | | |]; try discriminate he.
      destruct (gren_cons _ _ _ _ _ _ hren1) as [hpe hren1a].
      destruct (gren_cons _ _ _ _ _ _ hren1a) as [hpa hren1b].
      cbn [gpres] in hpe, hpa.
      destruct hpe as (hnv1 & hgo1 & hsl1). destruct hpa as (hnva & hgoa & hsla).
      assert (hts1 : g_slots G1 e1.(ev_vals) ts) by exact (hsl1 _ hts).
      assert (hnv1' : e1.(ev_nvals) = #|e1.(ev_vals)|).
      { rewrite hnv1, hnv, <- (g_slots_length _ _ _ hts), (g_slots_length _ _ _ hts1).
        reflexivity. }
      assert (hacc1 : g_slots G1 acc1.(ev_vals) tacc) by exact (hsla _ hacc).
      assert (hnacc1 : (env_push (SAddr a1) acc1).(ev_nvals)
                       = #|(env_push (SAddr a1) acc1).(ev_vals)|).
      { cbn [env_push ev_vals ev_nvals].
        rewrite hnva, hnacc, <- (g_slots_length _ _ _ hacc), (g_slots_length _ _ _ hacc1).
        reflexivity. }
      destruct (ih lo1 G1 e1 c mfix idx0 ts (S i) (env_push (SAddr a1) acc1) (tf i :: tacc)
                  rs1b s1 e' rs' s' hok1 hc (gren_cok _ _ _ _ c hren1 hcok) hts1 hnv1'
                  (g_slots_cons G1 (SAddr a1) _ (tf i) tacc (g_slot_addr G1 a1 (tf i) hga1)
                     hacc1)
                  hnacc1 he)
        as (lo2 & G2 & hren2 & hok2 & hsl & hnv' & hgoff).
      exists lo2, G2. split; [exact (gren_trans _ _ _ _ _ _ hren1b hren2)|].
      split; [exact hok2|].
      rewrite hnv1, hgo1 in hsl.
      split; [|split; [exact hnv'|rewrite hgoff; cbn [env_push ev_goff]; exact hgoa]].
      cbn [seq map List.rev]. rewrite <- app_assoc. exact hsl.
  Qed.
  (** ** The evaluator against PCUIC reduction

    The input stands (through the ghost map) for a term that reduces, in PCUIC, to the term
    the output value stands for, and the state invariant is re-established. A call may
    collect: the ghost it ends with is not an extension of the one it started with, and the
    roots come back renamed, standing for what they stood for ([gren]). A caller takes the
    structures it holds back out of the returned roots, as the machine does. The five
    functions are proved together by induction on the fuel. [whnf_fix] takes the code of a
    whole [tFix] block and the index [idx] of the fixpoint it applies, which need not be the
    index the code was written with: [apply] calls it on the fixpoint cells
    [push_fix_cells] made. *)

  Lemma machine_sound : forall d,
    (forall lo G a rs s v rs' s' t,
        gok lo G s -> G a = Some t ->
        force X_type X Γ nctx stress d a rs s = COk (v, rs', s') ->
        exists lo' G' u, gren G G' rs rs' /\ gok lo' G' s' /\ g_value G' v u /\ cred t u)
    /\ (forall lo G x stk sts tx rs s v rs' s',
        gok lo G s -> g_slot G x tx -> g_slots G stk sts ->
        eval_slot X_type X Γ nctx stress d x stk rs s = COk (v, rs', s') ->
        exists lo' G' u, gren G G' rs rs' /\ gok lo' G' s' /\ g_value G' v u
                         /\ cred (mkApps tx sts) u)
    /\ (forall lo G e c stk sts tc rs s v rs' s',
        gok lo G s -> g_susp G e c.(c_term) tc -> cok G c -> g_slots G stk sts ->
        whnf X_type X Γ nctx stress d e c stk rs s = COk (v, rs', s') ->
        exists lo' G' u, gren G G' rs rs' /\ gok lo' G' s' /\ g_value G' v u
                         /\ cred (mkApps tc sts) u)
    /\ (forall lo G e c mfix idx0 idx stk sts tc rs s v rs' s',
        gok lo G s -> c.(c_term) = tFix mfix idx0 ->
        g_susp G e (tFix mfix idx) tc -> cok G c -> g_slots G stk sts ->
        whnf_fix X_type X Γ nctx stress d e c mfix idx stk rs s = COk (v, rs', s') ->
        exists lo' G' u, gren G G' rs rs' /\ gok lo' G' s' /\ g_value G' v u
                         /\ cred (mkApps tc sts) u)
    /\ (forall lo G v stk sts tv rs s w rs' s',
        gok lo G s -> g_value G v tv -> g_slots G stk sts ->
        apply X_type X Γ nctx stress d v stk rs s = COk (w, rs', s') ->
        exists lo' G' u, gren G G' rs rs' /\ gok lo' G' s' /\ g_value G' w u
                         /\ cred (mkApps tv sts) u).
  Proof.
    intros d. induction d as [|k ih].
    - (* FO: every call fails, except [apply] with an empty stack *)
      split; [|split; [|split; [|split]]].
      + intros lo G a rs s v rs' s' t hok hGa he. cbn [force] in he. discriminate he.
      + intros lo G x stk sts tx rs s v rs' s' hok hx hsts he.
        cbn [eval_slot] in he. discriminate he.
      + intros lo G e c stk sts tc rs s v rs' s' hok hsusp hcok hsts he.
        cbn [whnf] in he. discriminate he.
      + intros lo G e c mfix idx0 idx stk sts tc rs s v rs' s' hok hcfix hsusp hcok hsts he.
        cbn [whnf_fix] in he. discriminate he.
      + intros lo G v stk sts tv rs s w rs' s' hok hv hsts he.
        cbn [apply] in he. destruct stk as [|y stk].
        * inversion he; subst. inversion hsts; subst.
          exists lo, G, tv. split; [apply gren_refl|]. split; [exact hok|].
          split; [exact hv|]. apply cred_refl.
        * discriminate he.
    - destruct (ih tt) as (IHf & IHs & IHw & IHx & IHa).
      split; [|split; [|split; [|split]]].
      + (* force *)
        intros lo G a0 rs0 s0 v0 rs' s' t0 hok hGa he.
        cbv beta iota zeta delta [force] in he.
        destruct (heap_get a0 s0) as [cl|] eqn:ehc; [|discriminate he].
        destruct (gk_cells _ _ _ hok a0 cl ehc) as [t1 [hGa1 hcell]].
        assert (t1 = t0) by (rewrite hGa in hGa1; injection hGa1 as ->; reflexivity).
        subst t1.
        destruct cl as [vs n o c| vd | | b].
        * (* CSusp: force, then write back *)
          destruct hcell as [hbusy|[u [hgc hcred]]]; [discriminate hbusy|].
          pose proof (g_cell_susp_inv _ _ _ _ _ _ hgc) as hsusp.
          pose proof (g_cell_susp_cok _ _ _ _ _ _ hgc) as hcok.
          destruct (heap_upd a0 CBusy s0) as [sb|] eqn:ebusy; [|discriminate he].
          lazymatch type of he with
          | context [match ?x with COk _ => _ | CFail _ => _ end] =>
            destruct x as [[[vw rsw] sw]|w] eqn:ew
          end; [|discriminate he].
          destruct rsw as [|r1 rsw']; [discriminate he|].
          destruct r1 as [ar| | | | | |]; try discriminate he.
          destruct (heap_upd ar (CDone vw) sw) as [sd|] eqn:edone; [|discriminate he].
          injection he as hiv hirs his; subst v0 rs' s'.
          assert (hokb : gok lo G sb) by exact (gok_heap_upd_busy lo G a0 s0 sb hok ebusy).
          destruct (IHw lo G (mkEnv vs n o) c [] [] u (RA a0 :: rs0) sb vw
                      (RA ar :: rsw') sw hokb hsusp hcok (g_slots_nil G) ew)
            as (lo1 & G' & uw & hren & hokw & hvw & hcredw).
          destruct (gren_cons _ _ _ _ _ _ hren) as [hpa hren'].
          cbn [gpres] in hpa.
          assert (hG'a : G' ar = Some t0) by exact (hpa t0 hGa).
          assert (hcred_t_uw : cred t0 uw) by exact (cred_trans t0 u uw hcred hcredw).
          exists lo1, G', uw. split; [exact hren'|].
          split; [exact (gok_heap_upd_done lo1 G' ar vw uw t0 sw sd hokw hG'a hvw
                           hcred_t_uw edone)|].
          split; [exact hvw|exact hcred_t_uw].
        * (* CDone vd: the value is already there *)
          destruct hcell as [hbusy|[u [hgc hcred]]]; [discriminate hbusy|].
          pose proof (g_cell_done_inv _ _ _ hgc) as hvd.
          inversion he; subst. clear he.
          exists lo, G, u. split; [apply gren_refl|]. split; [exact hok|].
          split; [exact hvd|exact hcred].
        * discriminate he.
        * discriminate he.
      + (* eval_slot *)
        intros lo G x stk sts tx rs0 s0 v0 rs' s' hok hslot hsts he.
        cbv beta iota zeta delta [eval_slot] in he.
        destruct x as [a|vs n o c].
        * (* SAddr a: force then apply *)
          pose proof (g_slot_addr_inv _ _ _ hslot) as hGa.
          lazymatch type of he with
          | context [match ?x with COk _ => _ | CFail _ => _ end] =>
            destruct x as [[[vf rsf] sf]|w] eqn:ef
          end; [|discriminate he].
          destruct rsf as [|r1 rsf']; [discriminate he|].
          destruct r1 as [| | | |lk| |]; try discriminate he.
          destruct (IHf lo G a (RSk stk :: rs0) s0 vf (RSk lk :: rsf') sf tx hok hGa ef)
            as (lof & Gf & uf & hrenf & hokf & hvf & hcredf).
          destruct (gren_cons _ _ _ _ _ _ hrenf) as [hpk hrenf'].
          cbn [gpres] in hpk.
          destruct (IHa lof Gf vf lk sts uf rsf' sf v0 rs' s' hokf hvf (hpk _ hsts) he)
            as (loa & G' & u' & hrena & hoka & hv' & hcreda).
          exists loa, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hrenf' hrena)|].
          split; [exact hoka|]. split; [exact hv'|].
          apply (cred_trans (mkApps tx sts) (mkApps uf sts) u').
          -- exact (cred_mkApps tx uf sts hcredf).
          -- exact hcreda.
        * (* SInl: whnf in place *)
          pose proof (g_slot_inl_inv _ _ _ _ _ _ hslot) as hsusp.
          pose proof (g_slot_inl_cok _ _ _ _ _ _ hslot) as hcok.
          exact (IHw lo G (mkEnv vs n o) c stk sts tx rs0 s0 v0 rs' s'
                   hok hsusp hcok hsts he).
      + (* whnf *)
        intros lo G e c stk sts tc rs0 s0 v0 rs' s' hok hsusp hcok hsts he.
        cbv beta iota zeta delta [whnf] in he.
        destruct (tick s0) as [st|] eqn:etick; [|discriminate he].
        destruct (tick_shape _ _ etick) as (th & tn & tr & tg & tm).
        assert (hokt : gok lo G st)
          by (apply (gok_same lo G s0 st hok th tn tg);
              exact (mok_memo _ s0 st tm (gk_memo _ _ _ hok))).
        clear hok.
        remember (c_term c) as ct eqn:ec;
        destruct ct as [n|vr|ev earg|srt|na A B|na A b|na b T body|f arg|k0 ui
                       |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm];
          try (solve [discriminate he]).
        * (* tRel n *)
          destruct (env_var X_type X Γ nctx stress n e (RSk stk :: rs0) st)
            as [[[xr rsr] sr]|w] eqn:ev; [|discriminate he].
          destruct rsr as [|r1 rsr']; [discriminate he|].
          destruct r1 as [| | | |lk| |]; try discriminate he.
          destruct (env_var_sound lo G n e (RSk stk :: rs0) st xr (RSk lk :: rsr') sr tc
                      hokt hsusp ev)
            as (lov & Gv & tv1 & hrenv & hokv & hslotv & hcredv).
          destruct (gren_cons _ _ _ _ _ _ hrenv) as [hpk hrenv'].
          cbn [gpres] in hpk.
          destruct (IHs lov Gv xr lk sts tv1 rsr' sr v0 rs' s' hokv hslotv (hpk _ hsts) he)
            as (los & G' & u' & hrens & hok' & hv' & hcred').
          exists los, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hrenv' hrens)|].
          split; [exact hok'|]. split; [exact hv'|].
          apply (cred_trans (mkApps tc sts) (mkApps tv1 sts) u').
          -- exact (cred_mkApps tc tv1 sts hcredv).
          -- exact hcred'.
        * (* tSort *)
          destruct stk as [|xh stk'].
          -- inversion he; subst; clear he. inversion hsts; subst.
             exists lo, G, tc. split; [apply gren_refl|]. split; [exact hokt|].
             split; [apply (g_VOpen G e c tc); [rewrite <- ec; exact hsusp|exact hcok]|].
             apply cred_refl.
          -- discriminate he.
        * (* tProd *)
          destruct stk as [|xh stk'].
          -- inversion he; subst; clear he. inversion hsts; subst.
             exists lo, G, tc. split; [apply gren_refl|]. split; [exact hokt|].
             split; [apply (g_VOpen G e c tc); [rewrite <- ec; exact hsusp|exact hcok]|].
             apply cred_refl.
          -- discriminate he.
        * (* tLambda na A b *)
          destruct stk as [|xh stk'].
          -- (* VLam *)
             inversion he; subst; clear he. inversion hsts; subst.
             exists lo, G, tc. split; [apply gren_refl|]. split; [exact hokt|].
             split; [apply (g_VLam G e c tc); [rewrite <- ec; exact hsusp|exact hcok]|].
             apply cred_refl.
          -- (* beta *)
             inversion hsts as [|x0 l0 txh sts' hsloth hslots']; subst.
             assert (hcb : cok G (child c 1 b))
               by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
             destruct (bind X_type X stress xh (child c 1 b) (RE e :: RSk stk' :: rs0) st)
               as [[[xb rsb] sb]|w] eqn:eb; [|discriminate he].
             destruct rsb as [|r1 rsb1]; [discriminate he|].
             destruct r1 as [| |ee| | | |]; try discriminate he.
             destruct rsb1 as [|r2 rsb2]; [discriminate he|].
             destruct r2 as [| | | |lk| |]; try discriminate he.
             destruct (bind_sound lo G xh (child c 1 b) (RE e :: RSk stk' :: rs0) st xb
                         (RE ee :: RSk lk :: rsb2) sb txh hokt hsloth hcb eb)
               as (lob & Gv & hrenb & hokb & hslotb).
             destruct (gren_cons _ _ _ _ _ _ hrenb) as [hpe hrenb1].
             destruct (gren_cons _ _ _ _ _ _ hrenb1) as [hpk hrenb2].
             cbn [gpres] in hpe, hpk.
             destruct (g_susp_lam Gv ee na A b tc (genv_susp _ _ _ _ _ _ hpe hsusp))
               as (A' & B & htc & hlamprop).
             destruct (IHw lob Gv (env_push xb ee) (child c 1 b) lk sts' (subst [txh] 0 B)
                         rsb2 sb v0 rs' s' hokb (hlamprop xb txh hslotb)
                         (gren_cok _ _ _ _ _ hrenb hcb) (hpk _ hslots') he)
               as (low & G' & u' & hrenw & hok' & hv' & hcred').
             exists low, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hrenb2 hrenw)|].
             split; [exact hok'|]. split; [exact hv'|].
             subst tc.
             apply (cred_trans (mkApps (tApp (tLambda na A' B) txh) sts')
                       (mkApps (subst [txh] 0 B) sts') u').
             ++ apply cred_mkApps. apply cred_one. apply red_beta.
             ++ exact hcred'.
        * (* tLetIn na b T body (zeta) *)
          destruct (g_susp_letin _ _ _ _ _ _ _ hsusp) as (d' & T' & B & htc & hsb & hletprop).
          assert (hc0 : cok G (child c 0 b))
            by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
          assert (hc2 : cok G (child c 2 body))
            by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
          destruct (arg_slot X_type X Γ nctx stress e (child c 0 b) (RE e :: RSk stk :: rs0) st)
            as [[[xa rsa] sa]|w] eqn:ea; [|discriminate he].
          destruct rsa as [|r1 rsa1]; [discriminate he|].
          destruct r1 as [| |ee| | | |]; try discriminate he.
          destruct rsa1 as [|r2 rsa2]; [discriminate he|].
          destruct r2 as [| | | |lk| |]; try discriminate he.
          destruct (arg_slot_sound lo G e (child c 0 b) (RE e :: RSk stk :: rs0) st xa
                      (RE ee :: RSk lk :: rsa2) sa d' hokt hsb hc0 ea)
            as (loa & Ga & tb & hrena & hoka & hslota & hcreda).
          destruct (gren_cons _ _ _ _ _ _ hrena) as [hpe hrena1].
          destruct (gren_cons _ _ _ _ _ _ hrena1) as [hpk hrena2].
          cbn [gpres] in hpe, hpk.
          destruct (bind X_type X stress xa (child c 2 body) (RE ee :: RSk lk :: rsa2) sa)
            as [[[xbnd rsb] sb]|w] eqn:eb; [|discriminate he].
          destruct rsb as [|r1 rsb1]; [discriminate he|].
          destruct r1 as [| |ee2| | | |]; try discriminate he.
          destruct rsb1 as [|r2 rsb2]; [discriminate he|].
          destruct r2 as [| | | |lk2| |]; try discriminate he.
          destruct (bind_sound loa Ga xa (child c 2 body) (RE ee :: RSk lk :: rsa2) sa xbnd
                      (RE ee2 :: RSk lk2 :: rsb2) sb tb hoka hslota
                      (gren_cok _ _ _ _ _ hrena hc2) eb)
            as (lob & Gb & hrenb & hokb & hslotb).
          destruct (gren_cons _ _ _ _ _ _ hrenb) as [hpe2 hrenb1].
          destruct (gren_cons _ _ _ _ _ _ hrenb1) as [hpk2 hrenb2].
          cbn [gpres] in hpe2, hpk2.
          destruct (g_susp_letin Gb ee2 na b T body tc
                      (genv_susp _ _ _ _ _ _ (genv_trans _ _ _ _ _ _ hpe hpe2) hsusp))
            as (d'2 & T'2 & B2 & htc2 & hsb2 & hletprop2).
          assert (heqlet : tLetIn na d' T' B = tLetIn na d'2 T'2 B2)
            by (rewrite <- htc; exact htc2).
          inversion heqlet; subst d'2 T'2 B2.
          destruct (IHw lob Gb (env_push xbnd ee2) (child c 2 body) lk2 sts (subst [tb] 0 B)
                      rsb2 sb v0 rs' s' hokb (hletprop2 xbnd tb hslotb)
                      (gren_cok _ _ _ _ _ hrenb (gren_cok _ _ _ _ _ hrena hc2))
                      (hpk2 _ (hpk _ hsts)) he)
            as (low & G' & u' & hrenw & hok' & hv' & hcred').
          exists low, G', u'.
          split; [exact (gren_trans _ _ _ _ _ _ hrena2
                           (gren_trans _ _ _ _ _ _ hrenb2 hrenw))|].
          split; [exact hok'|]. split; [exact hv'|].
          subst tc.
          apply (cred_trans (mkApps (tLetIn na d' T' B) sts) (mkApps (subst [tb] 0 B) sts) u').
          -- apply cred_mkApps.
             apply (cred_trans (tLetIn na d' T' B) (tLetIn na tb T' B) (subst [tb] 0 B)).
             ++ exact (cred_letin na d' tb T' B hcreda).
             ++ apply cred_one. apply red_zeta.
          -- exact hcred'.
        * (* tApp f arg *)
          destruct (g_susp_app _ _ _ _ _ hsusp) as (uf & ua & htc & hsf & hsa).
          assert (hc1 : cok G (child c 1 arg))
            by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
          assert (hc0f : cok G (child c 0 f))
            by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
          destruct (arg_slot X_type X Γ nctx stress e (child c 1 arg) (RE e :: RSk stk :: rs0) st)
            as [[[xr rsr] sr]|w] eqn:ea; [|discriminate he].
          destruct rsr as [|r1 rsr1]; [discriminate he|].
          destruct r1 as [| |ee| | | |]; try discriminate he.
          destruct rsr1 as [|r2 rsr2]; [discriminate he|].
          destruct r2 as [| | | |lk| |]; try discriminate he.
          destruct (arg_slot_sound lo G e (child c 1 arg) (RE e :: RSk stk :: rs0) st xr
                      (RE ee :: RSk lk :: rsr2) sr ua hokt hsa hc1 ea)
            as (loa & Gv & ta & hrena & hoka & hslota & hcreda).
          destruct (gren_cons _ _ _ _ _ _ hrena) as [hpe hrena1].
          destruct (gren_cons _ _ _ _ _ _ hrena1) as [hpk hrena2].
          cbn [gpres] in hpe, hpk.
          destruct (IHw loa Gv ee (child c 0 f) (xr :: lk) (ta :: sts) uf rsr2 sr v0 rs' s'
                      hoka (genv_susp _ _ _ _ _ _ hpe hsf) (gren_cok _ _ _ _ _ hrena hc0f)
                      (g_slots_cons Gv xr lk ta sts hslota (hpk _ hsts)) he)
            as (low & G' & u' & hrenw & hok' & hv' & hcred').
          exists low, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hrena2 hrenw)|].
          split; [exact hok'|]. split; [exact hv'|].
          subst tc.
          apply (cred_trans (mkApps (tApp uf ua) sts) (mkApps (tApp uf ta) sts) u').
          -- exact (cred_mkApps (tApp uf ua) (tApp uf ta) sts (cred_app_r uf ua ta hcreda)).
          -- exact hcred'.
        * (* tConst kn ui (delta) *)
          pose proof (g_susp_const _ _ _ _ _ hsusp) as htc.
          destruct (delta X_type X k0 ui st) as [[[c'| ] sd]|w] eqn:ed; [| |discriminate he].
          -- (* Some c': the body of [k0] at [ui], by [delta_body] and [delta_red1] *)
             destruct (gk_memo _ _ _ hokt) as (hmi & _ & hcodes & hokb).
             destruct hmi as (hf & _ & _ & _ & hdo).
             destruct (delta_body X_type X Σ k0 ui st sd c' hΣ hf hdo ed)
               as (cb & body & ce & hdecl & hb & hct & _ & hce & _ & _ & hci).
             assert (hclosed : closedn 0 c'.(c_term)).
             { rewrite hct. apply closed_inst_code.
               exact (declared_constant_closed_body Σ k0 cb body wfΣ hdecl hb). }
             assert (hinst : forall cb0, abstract_env_lookup X k0 = Some (ConstantDecl cb0) ->
                       ui = [] -> #|polymorphic_instance cb0.(cst_universes)| = 0).
             { intros cb0 hl hu. subst ui.
               destruct hcok as [e0 [he0 hci0]].
               pose proof (code_inv_consts_okb Σ e0 c hci0 (hokb _ _ (hcodes _ _ he0))) as hco.
               rewrite <- ec in hco. cbn in hco.
               exact (inst_okb_nil Σ k0 cb0 hco (lookup_env_of_abstract X_type X Σ k0 _ hΣ hl)). }
             assert (hcredc : cred (tConst k0 ui) (lift0 (lvl - nctx) c'.(c_term))).
             { rewrite (lift_closed (lvl - nctx) 0 c'.(c_term) hclosed).
               apply cred_one.
               exact (delta_red1 X_type X Σ ΓΔ k0 ui st sd c' hΣ wfΣ hf hdo ed hinst). }
             pose proof (delta_gok lo G k0 ui st (Some c') sd hokt ed) as hokd0.
             pose proof (proj1 (proj2 (proj2 (gk_memo _ _ _ hokd0)))) as hgd.
             pose (Gd := mkGhost (gm G) ((sd.(st_memo)).(m_codes))).
             assert (hxd : gext G Gd) by (split; [intros a1 t1 h; exact h|exact hgd]).
             assert (hokd : gok lo Gd sd).
             { apply (gok_recode lo G sd sd);
                 [exact hokd0|reflexivity|reflexivity|reflexivity|exact hgd
                 |exact (mok_widen _ _ (gk_memo _ _ _ hokd0))]. }
             assert (hcokc : cok Gd c') by (exists ce; split; [exact hce|exact hci]).
             assert (hsuspc : g_susp Gd env_empty c'.(c_term) (lift0 (lvl - nctx) c'.(c_term))).
             { unfold env_empty.
               replace (lift0 (lvl - nctx) c'.(c_term))
                 with (subst [] 0 (lift (lvl - nctx + 0) 0 c'.(c_term)))
                 by (rewrite subst_empty, Nat.add_0_r; reflexivity).
               exact (g_susp_intro Gd [] 0 0 c'.(c_term) [] (g_slots_nil Gd) eq_refl). }
             destruct (IHw lo Gd env_empty c' stk sts (lift0 (lvl - nctx) c'.(c_term))
                         rs0 sd v0 rs' s' hokd hsuspc hcokc
                         (g_slots_mono G Gd hxd stk sts hsts) he)
               as (low & G' & u' & hrenw & hok' & hv' & hcred').
             exists low, G', u'. split; [exact (gren_trans _ _ _ _ _ _ (gren_ext _ _ _ hxd) hrenw)|].
             split; [exact hok'|]. split; [exact hv'|].
             rewrite htc.
             apply (cred_trans (mkApps (tConst k0 ui) sts)
                       (mkApps (lift0 (lvl - nctx) c'.(c_term)) sts) u').
             ++ exact (cred_mkApps (tConst k0 ui) (lift0 (lvl - nctx) c'.(c_term)) sts hcredc).
             ++ exact hcred'.
          -- (* None: a neutral constant *)
             pose proof (delta_gok lo G k0 ui st None sd hokt ed) as hokd.
             destruct (mat_all X_type X stress (k tt) stk rs0 sd) as [[[sp rsm] sm]|w] eqn:em;
               [|discriminate he].
             injection he as hv0 hrs hsm; subst v0 rs' s'.
             destruct (mat_all_sound (k tt) lo G stk sts rs0 sd sp rsm sm hokd hsts em)
               as (lom & G' & hrenm & hokm & haddrm).
             exists lom, G', (mkApps (tConst k0 ui) sts).
             split; [exact hrenm|]. split; [exact hokm|].
             split; [exact (g_VNeuConst G' (tConst k0 ui) sp sts haddrm)|].
             rewrite htc. apply cred_refl.
        * (* tInd i ui *)
          pose proof (g_susp_tind _ _ _ _ _ hsusp) as htc.
          destruct (mat_all X_type X stress (k tt) stk rs0 st) as [[[sp rsm] sm]|w] eqn:em;
            [|discriminate he].
          injection he as hv0 hrs hsm; subst v0 rs' s'.
          destruct (mat_all_sound (k tt) lo G stk sts rs0 st sp rsm sm hokt hsts em)
            as (lom & G' & hrenm & hokm & haddrm).
          exists lom, G', (mkApps (tInd ind ui) sts). split; [exact hrenm|].
          split; [exact hokm|].
          split; [exact (g_VCon G' (tInd ind ui) sp sts haddrm)|].
          rewrite htc. apply cred_refl.
        * (* tConstruct ind n ui *)
          pose proof (g_susp_construct _ _ _ _ _ _ hsusp) as htc.
          destruct (mat_all X_type X stress (k tt) stk rs0 st) as [[[sp rsm] sm]|w] eqn:em;
            [|discriminate he].
          injection he as hv0 hrs hsm; subst v0 rs' s'.
          destruct (mat_all_sound (k tt) lo G stk sts rs0 st sp rsm sm hokt hsts em)
            as (lom & G' & hrenm & hokm & haddrm).
          exists lom, G', (mkApps (tConstruct ind n ui) sts). split; [exact hrenm|].
          split; [exact hokm|].
          split; [exact (g_VCon G' (tConstruct ind n ui) sp sts haddrm)|].
          rewrite htc. apply cred_refl.
        * (* tCase ci p scrut brs: iota, or a stuck match *)
          assert (hcs : cok G (child c 0 scrut))
            by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
          destruct (g_susp_inv _ _ _ _ hsusp) as (ts & hts & hnv & htc).
          rewrite subst_lift_case in htc.
          lazymatch type of he with
          | context [match ?y with COk _ => _ | CFail _ => _ end] =>
            destruct y as [[[vs rss] ss]|w] eqn:ews
          end; [|discriminate he].
          destruct (IHw lo G e (child c 0 scrut) [] [] _ (RE e :: RSk stk :: rs0) st vs rss ss
                      hokt (g_susp_of_slots G e scrut ts hts hnv) hcs (g_slots_nil G) ews)
            as (lo1 & G1 & us & hren1 & hok1 & hvs & hcreds).
          destruct rss as [|r1 rss1]; [discriminate he|].
          destruct r1 as [| |e2| | | |]; try discriminate he.
          destruct rss1 as [|r2 rss2]; [discriminate he|].
          destruct r2 as [| | | |stk2| |]; try discriminate he.
          destruct (gren_cons _ _ _ _ _ _ hren1) as [hpe hren1a].
          destruct (gren_cons _ _ _ _ _ _ hren1a) as [hpk hren1b].
          cbn [gpres] in hpe, hpk.
          pose proof hpe as (hnv2 & hgo2 & hsl2).
          assert (hts1 : g_slots G1 e2.(ev_vals) ts) by exact (hsl2 _ hts).
          assert (hsts1 : g_slots G1 stk2 sts) by exact (hpk _ hsts).
          cbv beta iota in he.
          destruct vs as [h0 args|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|nn sp1|e1 c1|e1 c1 sp1];
            try discriminate he.
          1: { (* VCon: iota *)
             destruct h0 as [| | | | | | | | | |cind cn cu| | | | |]; try discriminate he.
             lazymatch type of he with
             | context [if inductive_eqb ?a ?b then _ else _] =>
               destruct (inductive_eqb a b) eqn:eind
             end; [|discriminate he].
             apply inductive_eqb_eq in eind. subst cind.
             destruct (nth_error brs cn) as [br|] eqn:ebr; [|discriminate he].
             lazymatch type of he with
             | context [if ?b then _ else _] => destruct b eqn:eguard
             end; [|discriminate he].
             apply andb_true_iff in eguard as [hassum hlen].
             apply eqb_eq in hlen. apply forallb_is_assum_ctx in hassum.
             destruct (g_value_VCon_inv _ _ _ _ hvs) as (targs & hus & hargs).
             pose proof (Forall2_skipn _ _ _ _ _ (ci_npar ci) hargs) as hcargs.
             assert (hlen' : #|skipn (ci_npar ci) args| = #|bcontext br|).
             { rewrite length_skipn, hlen, (assumption_context_length _ hassum). lia. }
             assert (htl : #|List.rev (skipn (ci_npar ci) targs)| = #|bcontext br|).
             { rewrite List.length_rev, (g_addrs_length _ _ _ hcargs). exact hlen'. }
             assert (hcb : cok G1 (child c (case_branch_step (N.of_nat cn)) br.(bbody))).
             { apply (gren_cok _ _ _ _ _ hren1). apply cok_child; [exact hcok|rewrite <- ec].
               apply cs_case_branch. rewrite Nat2N.id. exact ebr. }
             rewrite env_push_addrs_vals in he.
             assert (hsb : g_susp G1
                       (mkEnv (map SAddr (List.rev (skipn (ci_npar ci) args)) ++ e2.(ev_vals))
                          (#|skipn (ci_npar ci) args| + e2.(ev_nvals)) e2.(ev_goff))
                       br.(bbody)
                       (subst (List.rev (skipn (ci_npar ci) targs) ++ ts) 0
                          (lift (lvl - nctx + e.(ev_goff))
                             (#|skipn (ci_npar ci) args| + e.(ev_nvals)) br.(bbody)))).
             { rewrite <- hnv2, <- hgo2.
               refine (g_susp_of_slots G1 (mkEnv _ _ _) br.(bbody) _ _ _).
               - cbn [ev_vals]. apply g_slots_app.
                 + apply g_slots_addrs. apply Forall2_rev. exact hcargs.
                 + exact hts1.
               - cbn [ev_vals ev_nvals]. rewrite length_app, length_map, List.length_rev.
                 rewrite hnv2, hnv, <- (g_slots_length _ _ _ hts), (g_slots_length _ _ _ hts1).
                 reflexivity. }
             destruct (IHw lo1 G1 _ (child c (case_branch_step (N.of_nat cn)) br.(bbody)) stk2 sts _
                         rss2 ss v0 rs' s' hok1 hsb hcb hsts1 he)
               as (low & G' & u' & hrenw & hok' & hv' & hcred').
             exists low, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hren1b hrenw)|].
             split; [exact hok'|]. split; [exact hv'|].
             refine (cred_trans _ _ _ _ hcred'). apply cred_mkApps. rewrite htc.
             eapply cred_trans; [apply cred_case_c; exact hcreds|].
             rewrite hus. apply cred_one.
             match goal with
             | |- red1 _ _ (tCase ?ci0 ?p0 (mkApps (tConstruct _ _ _) ?targs0) _) ?t =>
               replace t with (iota_red ci0.(ci_npar) p0 targs0
                                 (rbr ts (lvl - nctx + e.(ev_goff)) e.(ev_nvals) br))
             end.
             ++ apply red_iota.
                ** rewrite nth_error_map, ebr. reflexivity.
                ** rewrite (g_addrs_length _ _ _ hargs). exact hlen.
             ++ rewrite iota_red_assum by exact hassum. unfold rbr; cbn [bbody bcontext].
                rewrite hlen', subst_app_simpl, htl. reflexivity.
          } (* VStuckFix, VNeu, VStuck: a stuck match *)
          all: destruct (mat_all X_type X stress (k tt) stk2 (RE e2 :: rss2) ss)
                 as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he];
               destruct rsm as [|r1 rsm1]; [discriminate he|];
               destruct r1 as [| |ee| | | |]; try discriminate he;
               injection he as hv0 hrs hsm; subst v0 rs' s';
               destruct (mat_all_sound (k tt) lo1 G1 stk2 sts (RE e2 :: rss2) ss sp2
                           (RE ee :: rsm1) sm hok1 hsts1 em)
                 as (lom & G' & hrenm & hokm & haddrm);
               destruct (gren_cons _ _ _ _ _ _ hrenm) as [hpe3 hrenm1];
               cbn [gpres] in hpe3;
               exists lom, G', (mkApps tc sts);
               (split; [exact (gren_trans _ _ _ _ _ _ hren1b hrenm1)|]);
               (split; [exact hokm|]);
               (split; [|apply cred_refl]);
               apply g_VStuck;
               [ rewrite <- ec; exact (genv_susp _ _ _ _ _ _ (genv_trans _ _ _ _ _ _ hpe hpe3) hsusp)
               | exact (gren_cok _ _ _ _ _ hrenm (gren_cok _ _ _ _ _ hren1 hcok))
               | exact haddrm ].
        * (* tProj pr arg: projection, or a stuck projection *)
          assert (hca : cok G (child c 0 arg))
            by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
          destruct (g_susp_inv _ _ _ _ hsusp) as (ts & hts & hnv & htc).
          lazymatch type of he with
          | context [match ?y with COk _ => _ | CFail _ => _ end] =>
            destruct y as [[[vs rss] ss]|w] eqn:ews
          end; [|discriminate he].
          destruct (IHw lo G e (child c 0 arg) [] [] _ (RE e :: RSk stk :: rs0) st vs rss ss
                      hokt (g_susp_of_slots G e arg ts hts hnv) hca (g_slots_nil G) ews)
            as (lo1 & G1 & us & hren1 & hok1 & hvs & hcreds).
          destruct rss as [|r1 rss1]; [discriminate he|].
          destruct r1 as [| |e2| | | |]; try discriminate he.
          destruct rss1 as [|r2 rss2]; [discriminate he|].
          destruct r2 as [| | | |stk2| |]; try discriminate he.
          destruct (gren_cons _ _ _ _ _ _ hren1) as [hpe hren1a].
          destruct (gren_cons _ _ _ _ _ _ hren1a) as [hpk hren1b].
          cbn [gpres] in hpe, hpk.
          assert (hsts1 : g_slots G1 stk2 sts) by exact (hpk _ hsts).
          cbv beta iota in he.
          destruct vs as [h0 args|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|nn sp1|e1 c1|e1 c1 sp1];
            try discriminate he.
          1: { (* VCon: the projection rule *)
             destruct h0 as [| | | | | | | | | |cind cn cu| | | | |]; try discriminate he.
             destruct cn as [|cn]; try discriminate he.
             lazymatch type of he with
             | context [if inductive_eqb ?a ?b then _ else _] =>
               destruct (inductive_eqb a b) eqn:eind
             end; [|discriminate he].
             apply inductive_eqb_eq in eind. subst cind.
             destruct (nth_error args (proj_npars pr + proj_arg pr)) as [a|] eqn:ea;
               [|discriminate he].
             destruct (g_value_VCon_inv _ _ _ _ hvs) as (targs & hus & hargs).
             destruct (g_addrs_nth _ _ _ _ _ hargs ea) as (ta & hta & hGa).
             destruct (IHs lo1 G1 (SAddr a) stk2 sts ta rss2 ss v0 rs' s' hok1
                         (g_slot_addr G1 a ta hGa) hsts1 he)
               as (low & G' & u' & hrenw & hok' & hv' & hcred').
             exists low, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hren1b hrenw)|].
             split; [exact hok'|]. split; [exact hv'|].
             refine (cred_trans _ _ _ _ hcred'). apply cred_mkApps. rewrite htc.
             change (subst ts 0 (lift (lvl - nctx + ev_goff e) (ev_nvals e) (tProj pr arg)))
               with (tProj pr (subst ts 0 (lift (lvl - nctx + ev_goff e) (ev_nvals e) arg))).
             eapply cred_trans; [apply cred_proj_c; exact hcreds|].
             rewrite hus. apply cred_one. apply red_proj. exact hta.
          } (* VStuckFix, VNeu, VStuck: a stuck projection *)
          all: destruct (mat_all X_type X stress (k tt) stk2 (RE e2 :: rss2) ss)
                 as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he];
               destruct rsm as [|r1 rsm1]; [discriminate he|];
               destruct r1 as [| |ee| | | |]; try discriminate he;
               injection he as hv0 hrs hsm; subst v0 rs' s';
               destruct (mat_all_sound (k tt) lo1 G1 stk2 sts (RE e2 :: rss2) ss sp2
                           (RE ee :: rsm1) sm hok1 hsts1 em)
                 as (lom & G' & hrenm & hokm & haddrm);
               destruct (gren_cons _ _ _ _ _ _ hrenm) as [hpe3 hrenm1];
               cbn [gpres] in hpe3;
               exists lom, G', (mkApps tc sts);
               (split; [exact (gren_trans _ _ _ _ _ _ hren1b hrenm1)|]);
               (split; [exact hokm|]);
               (split; [|apply cred_refl]);
               apply g_VStuck;
               [ rewrite <- ec; exact (genv_susp _ _ _ _ _ _ (genv_trans _ _ _ _ _ _ hpe hpe3) hsusp)
               | exact (gren_cok _ _ _ _ _ hrenm (gren_cok _ _ _ _ _ hren1 hcok))
               | exact haddrm ].
        * (* tFix mfix idx *)
          exact (IHx lo G e c mfix idx idx stk sts tc rs0 st v0 rs' s' hokt
                   (eq_sym ec) hsusp hcok hsts he).
        * (* tPrim *)
          destruct stk as [|xh stk'].
          -- inversion he; subst; clear he. inversion hsts; subst.
             exists lo, G, tc. split; [apply gren_refl|]. split; [exact hokt|].
             split; [apply (g_VOpen G e c tc); [rewrite <- ec; exact hsusp|exact hcok]|].
             apply cred_refl.
          -- discriminate he.
      + (* whnf_fix *)
        intros lo G e c mfix idx0 idx stk sts tc rs0 s0 v0 rs' s' hok hcfix hsusp hcok
          hsts he.
        cbv beta iota zeta delta [whnf_fix] in he.
        destruct (nth_error mfix idx) as [def|] eqn:edef; [|discriminate he].
        destruct (g_susp_inv _ _ _ _ hsusp) as (ts & hts & hnv & htc).
        destruct (nth_error stk (rarg def)) as [x|] eqn:ex.
        2: { (* too few arguments: a fixpoint value *)
          destruct (mat_all X_type X stress (k tt) stk (RE e :: rs0) s0)
            as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he].
          destruct rsm as [|r1 rsm1]; [discriminate he|].
          destruct r1 as [| |ee| | | |]; try discriminate he.
          injection he as hv0 hrs hsm; subst v0 rs' s'.
          destruct (mat_all_sound (k tt) lo G stk sts (RE e :: rs0) s0 sp2 (RE ee :: rsm1) sm
                      hok hsts em)
            as (lom & G' & hrenm & hokm & haddrm).
          destruct (gren_cons _ _ _ _ _ _ hrenm) as [hpe hrenm1].
          cbn [gpres] in hpe.
          exists lom, G', (mkApps tc sts). split; [exact hrenm1|]. split; [exact hokm|].
          split; [|apply cred_refl].
          exact (g_VFix G' ee c mfix idx0 idx sp2 tc sts hcfix (genv_susp _ _ _ _ _ _ hpe hsusp)
                   (gren_cok _ _ _ _ _ hrenm hcok) haddrm). }
        destruct (g_slots_nth _ _ _ _ _ hsts ex) as (tx & htx & hgx).
        assert (hrarg : rarg def < #|sts|).
        { apply nth_error_Some_length in htx. exact htx. }
        (* put the recursive argument in the heap *)
        destruct (materialize X_type X stress x (RE e :: RSk stk :: rs0) s0)
          as [[[a rsa] sa]|w] eqn:ema; [|discriminate he].
        destruct (materialize_sound lo G x (RE e :: RSk stk :: rs0) s0 a rsa sa tx
                    hok hgx ema)
          as (loa & Ga & hrena & hoka & hGa).
        destruct rsa as [|r1 rsa1]; [discriminate he|].
        destruct r1 as [| |ea| | | |]; try discriminate he.
        destruct rsa1 as [|r2 rsa2]; [discriminate he|].
        destruct r2 as [| | | |stka| |]; try discriminate he.
        destruct (gren_cons _ _ _ _ _ _ hrena) as [hpea hrena1].
        destruct (gren_cons _ _ _ _ _ _ hrena1) as [hpka hrena2].
        cbn [gpres] in hpea, hpka.
        cbv beta iota in he.
        assert (hstka : g_slots Ga (list_set stka (rarg def) (SAddr a)) sts).
        { rewrite <- (list_set_nth_id sts (rarg def) tx htx).
          apply g_slots_list_set; [exact (hpka _ hsts)|]. constructor. exact hGa. }
        (* force it *)
        lazymatch type of he with
        | context [match ?y with COk _ => _ | CFail _ => _ end] =>
          destruct y as [[[vf rsf] sf]|w] eqn:ef
        end; [|discriminate he].
        destruct (IHf loa Ga a (RE ea :: RSk (list_set stka (rarg def) (SAddr a)) :: rsa2) sa
                    vf rsf sf tx hoka hGa ef)
          as (lof & Gf & uf & hrenf & hokf & hvf & hcredf).
        destruct rsf as [|r1 rsf1]; [discriminate he|].
        destruct r1 as [| |e3| | | |]; try discriminate he.
        destruct rsf1 as [|r2 rsf2]; [discriminate he|].
        destruct r2 as [| | | |stkf| |]; try discriminate he.
        destruct (gren_cons _ _ _ _ _ _ hrenf) as [hpef hrenf1].
        destruct (gren_cons _ _ _ _ _ _ hrenf1) as [hpkf hrenf2].
        cbn [gpres] in hpef, hpkf.
        cbv beta iota in he.
        assert (hstkf : g_slots Gf stkf sts) by exact (hpkf _ hstka).
        assert (hpe3 : genv G Gf e e3) by exact (genv_trans _ _ _ _ _ _ hpea hpef).
        destruct vf as [h0 args|e1 c1|e1 c1 i1 sp1|e1 c1 i1 sp1|nn sp1|e1 c1|e1 c1 sp1];
          try discriminate he.
        1: { (* VCon: unfold the fixpoint *)
           destruct h0 as [| | | | | | | | | |cind cn cu| | | | |]; try discriminate he.
           destruct (g_value_VCon_inv _ _ _ _ hvf) as (targs & huf & hargs).
           destruct (alloc stress (CDone (VCon (tConstruct cind cn cu) args))
                       (RE e3 :: RSk stkf :: rsf2) sf)
             as [[[a2 rs2] s2]|w] eqn:ea2; [|discriminate he].
           destruct (alloc_sound lof Gf _ uf _ sf a2 rs2 s2 hokf (g_cell_done Gf _ _ hvf) ea2)
             as (lo2 & G2 & hren2 & hok2 & hGa2).
           destruct rs2 as [|r1 rs2a]; [discriminate he|].
           destruct r1 as [| |e4| | | |]; try discriminate he.
           destruct rs2a as [|r2 rs4]; [discriminate he|].
           destruct r2 as [| | | |stk4| |]; try discriminate he.
           destruct (gren_cons _ _ _ _ _ _ hren2) as [hpe2 hren2a].
           destruct (gren_cons _ _ _ _ _ _ hren2a) as [hpk2 hren2b].
           cbn [gpres] in hpe2, hpk2.
           cbv beta iota in he.
           pose proof (genv_trans _ _ _ _ _ _ hpe3 hpe2) as (hnv4 & hgo4 & hsl4).
           assert (hts4 : g_slots G2 e4.(ev_vals) ts) by exact (hsl4 _ hts).
           assert (hnv4' : e4.(ev_nvals) = #|e4.(ev_vals)|).
           { rewrite hnv4, hnv, <- (g_slots_length _ _ _ hts), (g_slots_length _ _ _ hts4).
             reflexivity. }
           assert (hcok2 : cok G2 c)
             by exact (gren_cok _ _ _ _ _ hren2 (gren_cok _ _ _ _ _ hrenf
                         (gren_cok _ _ _ _ _ hrena hcok))).
           destruct (push_fix_cells stress e4 c 0 #|mfix| e4
                       (RSk (list_set stk4 (rarg def) (SAddr a2)) :: rs4) s2)
             as [[[e' rs3] s3]|w] eqn:ep; [|discriminate he].
           destruct (push_fix_cells_sound #|mfix| lo2 G2 e4 c mfix idx0 ts 0 e4 ts _ s2 e' rs3 s3
                       hok2 hcfix hcok2 hts4 hnv4' hts4 hnv4' ep)
             as (lo3 & G3 & hren3 & hok3 & hsl3 & hnv3 & hgoff3).
           destruct rs3 as [|r1 rs6]; [discriminate he|].
           destruct r1 as [| | | |stk6| |]; try discriminate he.
           destruct (gren_cons _ _ _ _ _ _ hren3) as [hpk3 hren3b].
           cbn [gpres] in hpk3.
           cbv beta iota in he.
           assert (hstk6 : g_slots G3 stk6 (list_set sts (rarg def) uf)).
           { apply hpk3. apply g_slots_list_set; [exact (hpk2 _ hstkf)|].
             constructor. exact hGa2. }
           assert (hcb : cok G3 (child c (N.of_nat idx) def.(dbody))).
           { apply (gren_cok _ _ _ _ _ hren3). apply cok_child; [exact hcok2|rewrite hcfix].
             apply cs_fix. rewrite Nat2N.id. exact edef. }
           rewrite hgo4, hnv4 in hsl3. rewrite hgo4 in hgoff3.
           pose proof (g_susp_of_slots G3 e' def.(dbody) _ hsl3 hnv3) as hsb.
           (* the body read through the fixpoint cells is the unfolded body of [unfold_fix] *)
           rewrite hgoff3, hnv3, <- (g_slots_length _ _ _ hsl3), length_app, List.length_rev,
             length_map, length_seq, (g_slots_length _ _ _ hts), <- hnv in hsb.
           assert (hm : map (fun j => subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals)
                                                   (tFix mfix j))) (seq 0 #|mfix|)
                        = map (tFix (rfix ts (lvl - nctx + ev_goff e) (ev_nvals e) mfix))
                            (seq 0 #|mfix|))
             by (apply map_ext; intros j; apply rfix_eq).
           rewrite hm in hsb.
           destruct (IHw lo3 G3 e' (child c (N.of_nat idx) def.(dbody))
                       stk6 (list_set sts (rarg def) uf) _
                       rs6 s3 v0 rs' s' hok3 hsb hcb hstk6 he)
             as (low & G' & u' & hrenw & hok' & hv' & hcred').
           exists low, G', u'.
           split; [exact (gren_trans _ _ _ _ _ _ hrena2 (gren_trans _ _ _ _ _ _ hrenf2
                            (gren_trans _ _ _ _ _ _ hren2b
                               (gren_trans _ _ _ _ _ _ hren3b hrenw))))|].
           split; [exact hok'|]. split; [exact hv'|].
           refine (cred_trans _ _ _ _ hcred').
           rewrite htc, rfix_eq.
           eapply cred_trans; [exact (cred_mkApps_list_set _ _ _ _ _ htx hcredf)|].
           apply cred_one. rewrite huf.
           eapply red_fix.
           ++ exact (unfold_fix_rfix ts (lvl - nctx + ev_goff e) (ev_nvals e) mfix idx def edef).
           ++ apply is_constructor_list_set. exact hrarg.
        } (* VStuckFix, VNeu, VStuck: a stuck fixpoint *)
        all: destruct (mat_all X_type X stress (k tt) stkf (RE e3 :: rsf2) sf)
               as [[[sp2 rsm] sm]|w] eqn:em; [|discriminate he];
             destruct rsm as [|r1 rsm1]; [discriminate he|];
             destruct r1 as [| |ee| | | |]; try discriminate he;
             injection he as hv0 hrs hsm; subst v0 rs' s';
             destruct (mat_all_sound (k tt) lof Gf stkf sts (RE e3 :: rsf2) sf sp2
                         (RE ee :: rsm1) sm hokf hstkf em)
               as (lom & G' & hrenm & hokm & haddrm);
             destruct (gren_cons _ _ _ _ _ _ hrenm) as [hpem hrenm1];
             cbn [gpres] in hpem;
             exists lom, G', (mkApps tc sts);
             (split; [exact (gren_trans _ _ _ _ _ _ hrena2
                               (gren_trans _ _ _ _ _ _ hrenf2 hrenm1))|]);
             (split; [exact hokm|]);
             (split; [|apply cred_refl]);
             exact (g_VStuckFix G' ee c mfix idx0 idx sp2 tc sts hcfix
                      (genv_susp _ _ _ _ _ _ (genv_trans _ _ _ _ _ _ hpe3 hpem) hsusp)
                      (gren_cok _ _ _ _ _ hrenm (gren_cok _ _ _ _ _ hrenf
                         (gren_cok _ _ _ _ _ hrena hcok)))
                      haddrm).
      + (* apply *)
        intros lo G vv stk sts tv rs0 s0 ww rs' s' hok hv hsts he.
        cbv beta iota zeta delta [apply] in he.
        destruct stk as [|xh stk'].
        * (* empty stack: the value itself *)
          inversion he; subst; clear he. inversion hsts; subst.
          exists lo, G, tv. split; [apply gren_refl|]. split; [exact hok|].
          split; [exact hv|]. apply cred_refl.
        * destruct vv as [h sp|e c|e c i args|e c i sp|nn sp|e c|e c sp].
          2: { (* VLam: beta *)
             pose proof (g_value_VLam_inv _ _ _ _ hv) as hsusp.
             pose proof (g_value_VLam_cok _ _ _ _ hv) as hcok.
             remember (c_term c) as ct eqn:ec;
             destruct ct as [n|vr|ev earg|srt|na A B|na A b|na bd T bo|f arg|k0 ui
                            |ind ui|ind n ui|ci p scrut brs|pr arg|mfix idx|cmfix cidx|prm];
               try discriminate he.
             inversion hsts as [|x0 l0 txh sts' hsloth hslots']; subst.
             assert (hcb : cok G (child c 1 b))
               by (apply cok_child; [exact hcok|rewrite <- ec; constructor]).
             destruct (bind X_type X stress xh (child c 1 b) (RE e :: RSk stk' :: rs0) s0)
               as [[[xb rsb] sb]|w] eqn:eb; [|discriminate he].
             destruct rsb as [|r1 rsb1]; [discriminate he|].
             destruct r1 as [| |ee| | | |]; try discriminate he.
             destruct rsb1 as [|r2 rsb2]; [discriminate he|].
             destruct r2 as [| | | |lk| |]; try discriminate he.
             destruct (bind_sound lo G xh (child c 1 b) (RE e :: RSk stk' :: rs0) s0 xb
                         (RE ee :: RSk lk :: rsb2) sb txh hok hsloth hcb eb)
               as (lob & Gv & hrenb & hokb & hslotb).
             destruct (gren_cons _ _ _ _ _ _ hrenb) as [hpe hrenb1].
             destruct (gren_cons _ _ _ _ _ _ hrenb1) as [hpk hrenb2].
             cbn [gpres] in hpe, hpk.
             destruct (g_susp_lam Gv ee na A b tv (genv_susp _ _ _ _ _ _ hpe hsusp))
               as (A' & B & htv & hlamprop).
             destruct (IHw lob Gv (env_push xb ee) (child c 1 b) lk sts' (subst [txh] 0 B)
                         rsb2 sb ww rs' s' hokb (hlamprop xb txh hslotb)
                         (gren_cok _ _ _ _ _ hrenb hcb) (hpk _ hslots') he)
               as (low & G' & u' & hrenw & hok' & hv' & hcred').
             exists low, G', u'. split; [exact (gren_trans _ _ _ _ _ _ hrenb2 hrenw)|].
             split; [exact hok'|]. split; [exact hv'|].
             subst tv.
             apply (cred_trans (mkApps (tApp (tLambda na A' B) txh) sts')
                       (mkApps (subst [txh] 0 B) sts') u').
             ++ apply cred_mkApps. apply cred_one. apply red_beta.
             ++ exact hcred'. }
          2: { (* VFix: the fixpoint applied to its spine, then to the stack *)
             destruct (g_value_VFix_inv _ _ _ _ _ _ hv)
               as (mfix0 & idx0 & h & ts & hc0 & hsf & hcok & hadd & htv).
             rewrite hc0 in he.
             destruct (IHx lo G e c mfix0 idx0 i (map SAddr args ++ xh :: stk') (ts ++ sts) h
                         rs0 s0 ww rs' s' hok hc0 hsf hcok
                         (g_slots_app G _ _ _ _ (g_slots_addrs G _ _ hadd) hsts) he)
               as (lox & G' & u' & hrenx & hok' & hv' & hcred').
             exists lox, G', u'. split; [exact hrenx|]. split; [exact hok'|].
             split; [exact hv'|].
             subst tv. rewrite <- mkApps_app. exact hcred'. }
          4: { (* VOpen: cannot be applied *) discriminate he. }
          (* VCon, VStuckFix, VNeu, VStuck: the stack goes into the spine *)
          all: lazymatch type of he with
               | context [match ?y with COk _ => _ | CFail _ => _ end] =>
                 destruct y as [[[sp2 rsm] sm]|w] eqn:em
               end; [|discriminate he];
               destruct rsm as [|r1 rsm1]; [discriminate he|];
               destruct r1 as [| | |vc| | |]; try discriminate he;
               destruct (add_spine vc sp2) as [vres|] eqn:eadd; [|discriminate he];
               injection he as hww hrsm hsm; subst ww rs' s';
               destruct (mat_all_sound (k tt) lo G (xh :: stk') sts _ s0 sp2 _ sm hok hsts em)
                 as (lom & G' & hrenm & hokm & haddrm);
               destruct (gren_cons _ _ _ _ _ _ hrenm) as [hpv hrenm1];
               cbn [gpres] in hpv;
               exists lom, G', (mkApps tv sts);
               (split; [exact hrenm1|]); (split; [exact hokm|]);
               (split; [exact (g_value_add_spine _ _ _ _ _ _ (hpv _ hv) haddrm eadd)
                       |apply cred_refl]).
  Qed.

End Eval.
