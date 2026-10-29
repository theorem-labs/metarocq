(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICReduction
  PCUICUnivSubst PCUICWfUniverses PCUICWeakeningEnv PCUICWeakeningEnvTyp.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv PCUICCallByNeed
  PCUICCallByNeedSound PCUICCallByNeedSoundGC PCUICCallByNeedSoundCtx.

Import CanonicalTries.

Local Notation cbn_key := String2pos.positive.
Local Notation cbn_cidx := String2pos.positive.

(** * The memo tables of one [cbn_conv] call

  [PCUICCallByNeed]'s [cbn_memo] holds five maps, all of them empty at the start of a call:
  the code table [cbn_m_codes] with its next index [cbn_m_ncode] (whose invariant [cbn_memo_ok] is
  [PCUICCallByNeedSoundCtx]'s), the delta trie [cbn_m_delta], and the three caches [cbn_m_once],
  [cbn_m_hash] and [cbn_m_ceq], keyed by code identifier. This file says what each one means.

  - **The trie is a map.** [cbn_dt_find] reads the association list at the node the bits of the
    constant's identifier lead to, and [cbn_dt_add] writes there. [cbn_dt_find_add_same],
    [cbn_dt_find_add_other] and [cbn_dt_find_nil] are the three map laws. They rest on the
    injectivity of the bit path of an identifier ([cbn_sbits_inj], through [Byte.to_bits]) and
    on [cbn_mp_find]/[cbn_mp_set] being an association list under [cbn_modpath_eqb], whose soundness
    is [cbn_modpath_eqb_eq].
  - **The delta entry means what it says.** [cbn_delta_ok] says that every [kn] the trie answers
    for either carries [CbnDAxiom], and then the environment's declaration for [kn] is a
    constant without a body, or carries [CbnDBody body insts], and then the environment's
    declaration for [kn] has that body and every [(u, i, t')] of [insts] records
    [t' = cbn_inst_code u body] at a code-table index [i] whose entry is [body] at instance [u].
    [cbn_delta_body] is the conclusion the evaluator needs: when the machine's [cbn_delta] answers
    for [tConst kn u], the code it returns is the root code of a table entry whose term is
    [cbn_inst_code u body] for the body [body] the environment gives [kn]; [cbn_delta_red1] turns
    that into PCUIC's delta step, for *every* instance, under [wf Σ].

    For a non-empty instance [cbn_inst_code] *is* [subst_instance], so [cbn_inst_code_red1_gen]
    needs nothing. For [u = []] the machine's [cbn_inst_code] returns the body unchanged
    where [red_delta] produces [subst_instance [] body]; the two agree exactly when the
    body carries no universe variable, which [cbn_declared_constant_body_closedu] gets from
    [wf Σ] by MetaRocq's [on_declared_constant], [typing_wf_universes],
    [wf_universes_closedu] (with [weaken_lookup_on_global_env'] for its [on_udecl_prop]
    side condition) and [closedu_subst_instance]. That needs [kn]'s universe context to
    have no variable, which is the one premise of [cbn_delta_red1] beyond the evaluator's.
    The evaluator discharges it with [PCUICCallByNeedSoundHook.cbn_inst_okb_nil].
  - **The caches.** [cbn_hash_ok]: the value stored for a code identifier is [cbn_thash] of that
    code's term. [cbn_once_ok]: the bit stored is [Nat.leb (cbn_occ 0 t) 1] for that code's term
    [t]. [cbn_ceq_ok]: the bit stored for a *pair* of identifiers is the value of
    [eqb_term_upto_univ] at [Conv] on the two terms.

    The invariant of [cbn_m_ceq] is *not* "true means the two codes have the same term".
    [PCUICCallByNeed.cbn_code_eq] answers [true] in two ways: [cbn_same_id c1 c2], where the terms
    are indeed equal ([cbn_same_id_sound_table]); or the cached bit
    [eqb_term_upto_univ (abstract_env_compare_universe X) … Conv c1.(cbn_c_term) c2.(cbn_c_term)],
    which is equality *up to universes* and holds of terms that differ (two sorts at
    convertible universes, two instances of a polymorphic constant). So the strongest sound
    statement is the disjunction [cbn_code_eq_sound] proves: equal terms, or [eqb_term_upto_univ]
    at [Conv] says [true]. [PCUICCallByNeedSoundConv.cbn_code_eq_sound_wf] consumes it. A
    [false] answer says nothing, and no lemma here states anything about it.
  - **The code table grows.** [cbn_memo_add_entry] writes at [cbn_m_ncode] and touches nothing else,
    so an index already in the table keeps its entry ([cbn_memo_add_entry_codes_mono]). That new
    index is fresh in *every* map of the memo, which is [cbn_memo_fresh] (through [cbn_key_val], the
    reading of a code index as a [positive], under which [cbn_key_succ] is [Pos.succ]). Without
    it the three cache invariants would not survive an added entry: a stale pair
    ([cbn_m_ncode], path) in [cbn_m_hash] would be read against the new entry. With it,
    [cbn_delta_ok], [cbn_once_ok], [cbn_hash_ok], [cbn_ceq_ok] and [cbn_memo_fresh] — bundled as
    [cbn_memo_inv] — all survive [cbn_memo_add_entry], [cbn_new_entry], [cbn_once_body],
    [cbn_code_hash], [cbn_code_eq] and [cbn_delta], and each setter keeps the other five fields.

  Nothing here is about the heap: every operation of this file leaves [cbn_st_heap], [cbn_st_next],
  [cbn_st_room], [cbn_st_steps] and [cbn_st_gam] alone, so [cbn_state_ok] crosses them without an
  argument. *)

(** ** Equality of names by identifier first

  [cbn_modpath_eqb] and its companions compare the identifier before the module path, where
  MetaRocq's [Kername.compare] compares the path first. A [true] answer means equality. *)

Lemma cbn_string_eqb_spec (x y : String.t) : String.eqb x y = true <-> x = y.
Proof.
  split.
  - intros h. exact (@eqb_eq String.t _ x y h).
  - intros <-. exact (@eqb_refl String.t _ x).
Qed.

Lemma cbn_dirpath_eqb_refl (d : dirpath) : cbn_dirpath_eqb d d = true.
Proof.
  induction d as [|x d IH]; cbn [cbn_dirpath_eqb]; [reflexivity|].
  apply Bool.andb_true_iff. split; [apply cbn_string_eqb_spec; reflexivity | exact IH].
Qed.

Lemma cbn_dirpath_eqb_eq (d1 d2 : dirpath) : cbn_dirpath_eqb d1 d2 = true -> d1 = d2.
Proof.
  revert d2. induction d1 as [|x d1 IH]; intros [|y d2] h; cbn [cbn_dirpath_eqb] in h;
    try discriminate h; [reflexivity|].
  apply Bool.andb_true_iff in h as [h1 h2].
  apply cbn_string_eqb_spec in h1. apply IH in h2. subst. reflexivity.
Qed.

Lemma cbn_modpath_eqb_refl (m : modpath) : cbn_modpath_eqb m m = true.
Proof.
  induction m as [d|d i k|m IH i]; cbn [cbn_modpath_eqb].
  - apply cbn_dirpath_eqb_refl.
  - apply Bool.andb_true_iff. split; [apply Bool.andb_true_iff; split|].
    + apply cbn_string_eqb_spec; reflexivity.
    + apply PeanoNat.Nat.eqb_eq; reflexivity.
    + apply cbn_dirpath_eqb_refl.
  - apply Bool.andb_true_iff. split; [apply cbn_string_eqb_spec; reflexivity | exact IH].
Qed.

Lemma cbn_modpath_eqb_eq (m1 m2 : modpath) : cbn_modpath_eqb m1 m2 = true -> m1 = m2.
Proof.
  revert m2. induction m1 as [d1|d1 i1 k1|m1 IH i1]; intros [d2|d2 i2 k2|m2 i2] h;
    cbn [cbn_modpath_eqb] in h; try discriminate h.
  - apply cbn_dirpath_eqb_eq in h. subst. reflexivity.
  - apply Bool.andb_true_iff in h as [h1 h2]. apply Bool.andb_true_iff in h1 as [h3 h4].
    apply cbn_string_eqb_spec in h3. apply PeanoNat.Nat.eqb_eq in h4.
    apply cbn_dirpath_eqb_eq in h2. subst. reflexivity.
  - apply Bool.andb_true_iff in h as [h1 h2]. apply cbn_string_eqb_spec in h1.
    apply IH in h2. subst. reflexivity.
Qed.

Lemma cbn_modpath_eqb_false (m1 m2 : modpath) : m1 <> m2 -> cbn_modpath_eqb m1 m2 = false.
Proof.
  intros hne. destruct (cbn_modpath_eqb m1 m2) eqn:E; [|reflexivity].
  apply cbn_modpath_eqb_eq in E. contradiction.
Qed.

Lemma cbn_inductive_eqb_eq (i1 i2 : inductive) : cbn_inductive_eqb i1 i2 = true -> i1 = i2.
Proof.
  destruct i1 as [[mp1 id1] n1], i2 as [[mp2 id2] n2]. unfold cbn_inductive_eqb. cbn.
  intros h. apply Bool.andb_true_iff in h as [h1 h2].
  apply Bool.andb_true_iff in h1 as [h3 h4].
  apply PeanoNat.Nat.eqb_eq in h3. apply cbn_string_eqb_spec in h4.
  apply cbn_modpath_eqb_eq in h2. subst. reflexivity.
Qed.

Lemma cbn_case_info_eqb_eq (c1 c2 : case_info) : cbn_case_info_eqb c1 c2 = true -> c1 = c2.
Proof.
  destruct c1 as [i1 n1 r1 d1], c2 as [i2 n2 r2 d2]. unfold cbn_case_info_eqb. cbn.
  intros h. apply Bool.andb_true_iff in h as [h0 hd].
  apply Bool.andb_true_iff in h0 as [h1 h2].
  apply Bool.andb_true_iff in h1 as [h3 h4].
  apply cbn_inductive_eqb_eq in h3. apply PeanoNat.Nat.eqb_eq in h4.
  apply eqb_eq in h2. apply Bool.eqb_prop in hd. subst. reflexivity.
Qed.

Lemma cbn_instance_eqb_eq (u v : Instance.t) : Instance.eqb u v = true -> u = v.
Proof.
  unfold Instance.eqb. revert v. induction u as [|l u IH]; intros [|l' v] h;
    cbn [forallb2] in h; try discriminate h; [reflexivity|].
  apply Bool.andb_true_iff in h as [h1 h2].
  destruct (Level.eqb_spec l l') as [he|hne]; [|discriminate h1].
  apply Level.eq_leibniz in he. apply IH in h2. subst. reflexivity.
Qed.

(** ** The delta trie is a finite map

  The trie branches on the bits of the constant's identifier, eight per byte, and holds at
  each node the association list of the module paths whose identifier ends there. *)

Definition cbn_dt_here (t : cbn_dtrie) : list (modpath * cbn_delta_memo) :=
  match t with CbnDTNil => [] | CbnDTNode h _ _ => h end.

Lemma cbn_dt_find_here (kn : kername) (t : cbn_dtrie) :
  cbn_dt_find kn t = cbn_mp_find kn.1 (cbn_dt_here (cbn_dt_walk kn.2 t)).
Proof. unfold cbn_dt_find. destruct (cbn_dt_walk kn.2 t); reflexivity. Qed.

(** *** The association list at a node *)

Lemma cbn_mp_find_set_same (mp : modpath) (d : cbn_delta_memo)
    (l : list (modpath * cbn_delta_memo)) :
  cbn_mp_find mp (cbn_mp_set mp d l) = Some d.
Proof.
  induction l as [|[mp' d'] l IH]; cbn [cbn_mp_set cbn_mp_find].
  - now rewrite cbn_modpath_eqb_refl.
  - destruct (cbn_modpath_eqb mp mp') eqn:E; cbn [cbn_mp_find].
    + now rewrite cbn_modpath_eqb_refl.
    + rewrite E. exact IH.
Qed.

Lemma cbn_mp_find_set_other (mp mp' : modpath) (d : cbn_delta_memo)
    (l : list (modpath * cbn_delta_memo)) :
  mp' <> mp -> cbn_mp_find mp' (cbn_mp_set mp d l) = cbn_mp_find mp' l.
Proof.
  intros hne. induction l as [|[mp0 d0] l IH]; cbn [cbn_mp_set cbn_mp_find].
  - now rewrite (cbn_modpath_eqb_false mp' mp hne).
  - destruct (cbn_modpath_eqb mp mp0) eqn:E; cbn [cbn_mp_find].
    + apply cbn_modpath_eqb_eq in E. subst mp0.
      now rewrite (cbn_modpath_eqb_false mp' mp hne).
    + destruct (cbn_modpath_eqb mp' mp0); [reflexivity | exact IH].
Qed.

(** *** Walking and updating by a list of bits *)

Definition cbn_dt_walkb (l : list bool) (t : cbn_dtrie) : cbn_dtrie :=
  fold_left (fun (u : cbn_dtrie) (b : bool) => cbn_dt_child b u) l t.

Fixpoint cbn_dt_updb (l : list bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) : cbn_dtrie :=
  match l with
  | [] => f t
  | b :: l => cbn_dt_upd_child b (cbn_dt_updb l f) t
  end.

Lemma cbn_dt_walkb_cons (b : bool) (l : list bool) (t : cbn_dtrie) :
  cbn_dt_walkb (b :: l) t = cbn_dt_walkb l (cbn_dt_child b t).
Proof. reflexivity. Qed.

Lemma cbn_dt_walkb_app (l1 l2 : list bool) (t : cbn_dtrie) :
  cbn_dt_walkb (l1 ++ l2) t = cbn_dt_walkb l2 (cbn_dt_walkb l1 t).
Proof. unfold cbn_dt_walkb. apply fold_left_app. Qed.

Lemma cbn_dt_upd_child_ext (b : bool) (f g : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  (forall u : cbn_dtrie, f u = g u) -> cbn_dt_upd_child b f t = cbn_dt_upd_child b g t.
Proof. intros h. unfold cbn_dt_upd_child. destruct t, b; now rewrite h. Qed.

Lemma cbn_dt_updb_ext (l : list bool) (f g : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  (forall u : cbn_dtrie, f u = g u) -> cbn_dt_updb l f t = cbn_dt_updb l g t.
Proof.
  intros h. revert t. induction l as [|b l IH]; intros t; cbn [cbn_dt_updb]; [apply h|].
  apply cbn_dt_upd_child_ext. intros u. apply IH.
Qed.

Lemma cbn_dt_updb_app (l1 l2 : list bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  cbn_dt_updb (l1 ++ l2) f t = cbn_dt_updb l1 (cbn_dt_updb l2 f) t.
Proof.
  revert t. induction l1 as [|b l1 IH]; intros t; cbn [cbn_dt_updb app]; [reflexivity|].
  apply cbn_dt_upd_child_ext. intros u. apply IH.
Qed.

Lemma cbn_dt_child_upd_same (b : bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  cbn_dt_child b (cbn_dt_upd_child b f t) = f (cbn_dt_child b t).
Proof. unfold cbn_dt_upd_child, cbn_dt_child. destruct t, b; reflexivity. Qed.

Lemma cbn_dt_child_upd_other (b b' : bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  b <> b' -> cbn_dt_child b (cbn_dt_upd_child b' f t) = cbn_dt_child b t.
Proof.
  intros hne. unfold cbn_dt_upd_child, cbn_dt_child. destruct t, b, b';
    first [ reflexivity | now destruct hne ].
Qed.

Lemma cbn_dt_here_upd_child (b : bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  cbn_dt_here (cbn_dt_upd_child b f t) = cbn_dt_here t.
Proof. unfold cbn_dt_upd_child, cbn_dt_here. destruct t, b; reflexivity. Qed.

Lemma cbn_dt_walkb_updb_same (l : list bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  cbn_dt_walkb l (cbn_dt_updb l f t) = f (cbn_dt_walkb l t).
Proof.
  revert t. induction l as [|b l IH]; intros t; [reflexivity|].
  cbn [cbn_dt_updb]. rewrite !cbn_dt_walkb_cons, cbn_dt_child_upd_same. apply IH.
Qed.

(** A function that leaves every child alone is invisible below the node it changes. *)
Lemma cbn_dt_walkb_child_pres (l : list bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  (forall (b : bool) (u : cbn_dtrie), cbn_dt_child b (f u) = cbn_dt_child b u) ->
  l <> [] -> cbn_dt_walkb l (f t) = cbn_dt_walkb l t.
Proof.
  intros hf. destruct l as [|b l]; [intros h; now destruct h|].
  intros _. rewrite !cbn_dt_walkb_cons, hf. reflexivity.
Qed.

Lemma cbn_dt_here_walkb_updb_other (l l' : list bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  (forall (b : bool) (u : cbn_dtrie), cbn_dt_child b (f u) = cbn_dt_child b u) ->
  l <> l' ->
  cbn_dt_here (cbn_dt_walkb l' (cbn_dt_updb l f t)) = cbn_dt_here (cbn_dt_walkb l' t).
Proof.
  intros hf. revert l' t. induction l as [|b l IH]; intros l' t hne.
  - cbn [cbn_dt_updb]. rewrite (cbn_dt_walkb_child_pres l' f t hf); [reflexivity|].
    intros ->. now destruct hne.
  - destruct l' as [|b' l'].
    + cbn [cbn_dt_updb]. unfold cbn_dt_walkb; cbn [fold_left]. apply cbn_dt_here_upd_child.
    + cbn [cbn_dt_updb]. rewrite !cbn_dt_walkb_cons.
      destruct (Bool.bool_dec b' b) as [->|hb].
      * rewrite cbn_dt_child_upd_same. apply IH. intros ->. now destruct hne.
      * rewrite (cbn_dt_child_upd_other b' b _ t hb). reflexivity.
Qed.

(** *** The bits of an identifier *)

Definition cbn_bits_of_byte (x : Byte.byte) : list bool :=
  let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := Byte.to_bits x in
  [b0; b1; b2; b3; b4; b5; b6; b7].

Fixpoint cbn_sbits (s : String.t) : list bool :=
  match s with
  | String.EmptyString => []
  | String.String x s => cbn_bits_of_byte x ++ cbn_sbits s
  end.

Lemma cbn_dt_byte_walkb (x : Byte.byte) (t : cbn_dtrie) :
  cbn_dt_byte x t = cbn_dt_walkb (cbn_bits_of_byte x) t.
Proof.
  unfold cbn_dt_byte, cbn_bits_of_byte.
  destruct (Byte.to_bits x) as [b0 [b1 [b2 [b3 [b4 [b5 [b6 b7]]]]]]]. reflexivity.
Qed.

Lemma cbn_dt_upd_byte_updb (x : Byte.byte) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  cbn_dt_upd_byte x f t = cbn_dt_updb (cbn_bits_of_byte x) f t.
Proof.
  unfold cbn_dt_upd_byte, cbn_bits_of_byte.
  destruct (Byte.to_bits x) as [b0 [b1 [b2 [b3 [b4 [b5 [b6 b7]]]]]]]. reflexivity.
Qed.

Lemma cbn_dt_walk_bits (s : String.t) (t : cbn_dtrie) : cbn_dt_walk s t
  = cbn_dt_walkb (cbn_sbits s) t.
Proof.
  revert t. induction s as [|x s IH]; intros t; cbn [cbn_dt_walk cbn_sbits]; [reflexivity|].
  rewrite cbn_dt_walkb_app, <- cbn_dt_byte_walkb. apply IH.
Qed.

Lemma cbn_dt_upd_bits (s : String.t) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) :
  cbn_dt_upd s f t = cbn_dt_updb (cbn_sbits s) f t.
Proof.
  revert t. induction s as [|x s IH]; intros t; cbn [cbn_dt_upd cbn_sbits]; [reflexivity|].
  rewrite cbn_dt_updb_app, cbn_dt_upd_byte_updb. apply cbn_dt_updb_ext. intros u. apply IH.
Qed.

Lemma cbn_bits_of_byte_length (x : Byte.byte) : #|cbn_bits_of_byte x| = 8.
Proof.
  unfold cbn_bits_of_byte.
  destruct (Byte.to_bits x) as [b0 [b1 [b2 [b3 [b4 [b5 [b6 b7]]]]]]]. reflexivity.
Qed.

Lemma cbn_bits_tuple_inj
    (p q : bool * (bool * (bool * (bool * (bool * (bool * (bool * bool))))))) :
  (let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := p in
   [b0; b1; b2; b3; b4; b5; b6; b7])
  = (let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := q in
     [b0; b1; b2; b3; b4; b5; b6; b7]) ->
  p = q.
Proof.
  destruct p as [a0 [a1 [a2 [a3 [a4 [a5 [a6 a7]]]]]]].
  destruct q as [c0 [c1 [c2 [c3 [c4 [c5 [c6 c7]]]]]]].
  intros h. injection h as -> -> -> -> -> -> -> ->. reflexivity.
Qed.

Lemma cbn_bits_of_byte_inj (x y : Byte.byte) : cbn_bits_of_byte x = cbn_bits_of_byte y -> x = y.
Proof.
  unfold cbn_bits_of_byte. intros h. apply cbn_bits_tuple_inj in h.
  rewrite <- (Byte.of_bits_to_bits x), <- (Byte.of_bits_to_bits y), h. reflexivity.
Qed.

Lemma cbn_app_eq_len {A : Type} (l1 l2 r1 r2 : list A) :
  #|l1| = #|l2| -> l1 ++ r1 = l2 ++ r2 -> l1 = l2 /\ r1 = r2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] hl h; cbn in hl, h;
    try discriminate hl.
  - split; [reflexivity | exact h].
  - injection h as <- h. injection hl as hl.
    destruct (IH l2 hl h) as [<- <-]. split; reflexivity.
Qed.

Lemma cbn_sbits_inj (s s' : String.t) : cbn_sbits s = cbn_sbits s' -> s = s'.
Proof.
  revert s'. induction s as [|x s IH]; intros [|y s'] h; cbn [cbn_sbits] in h.
  - reflexivity.
  - exfalso. assert (hl := f_equal (fun l : list bool => #|l|) h).
    rewrite cbn_length_app_cbn, cbn_bits_of_byte_length in hl. cbn in hl. lia.
  - exfalso. assert (hl := f_equal (fun l : list bool => #|l|) h).
    rewrite cbn_length_app_cbn, cbn_bits_of_byte_length in hl. cbn in hl. lia.
  - assert (hlen : #|cbn_bits_of_byte x| = #|cbn_bits_of_byte y|)
      by (rewrite !cbn_bits_of_byte_length; reflexivity).
    destruct (cbn_app_eq_len _ _ _ _ hlen h) as [hb hs].
    rewrite (cbn_bits_of_byte_inj x y hb), (IH s' hs). reflexivity.
Qed.

(** *** The three map laws *)

Definition cbn_dt_ins (mp : modpath) (d : cbn_delta_memo) (t : cbn_dtrie) : cbn_dtrie :=
  match t with
  | CbnDTNil => CbnDTNode [(mp, d)] CbnDTNil CbnDTNil
  | CbnDTNode h z o => CbnDTNode (cbn_mp_set mp d h) z o
  end.

Lemma cbn_dt_add_ins (kn : kername) (d : cbn_delta_memo) (t : cbn_dtrie) :
  cbn_dt_add kn d t = cbn_dt_upd kn.2 (cbn_dt_ins kn.1 d) t.
Proof. reflexivity. Qed.

Lemma cbn_dt_ins_child (mp : modpath) (d : cbn_delta_memo) (b : bool) (t : cbn_dtrie) :
  cbn_dt_child b (cbn_dt_ins mp d t) = cbn_dt_child b t.
Proof. unfold cbn_dt_ins, cbn_dt_child. destruct t, b; reflexivity. Qed.

Lemma cbn_dt_ins_here (mp : modpath) (d : cbn_delta_memo) (t : cbn_dtrie) :
  cbn_dt_here (cbn_dt_ins mp d t) = cbn_mp_set mp d (cbn_dt_here t).
Proof. unfold cbn_dt_ins, cbn_dt_here. destruct t; reflexivity. Qed.

Lemma cbn_dt_walkb_nil (l : list bool) : cbn_dt_walkb l CbnDTNil = CbnDTNil.
Proof.
  induction l as [|b l IH]; [reflexivity|]. rewrite cbn_dt_walkb_cons. exact IH.
Qed.

Lemma cbn_dt_find_nil (kn : kername) : cbn_dt_find kn CbnDTNil = None.
Proof.
  rewrite cbn_dt_find_here, cbn_dt_walk_bits, cbn_dt_walkb_nil. reflexivity.
Qed.

Lemma cbn_dt_find_add_same (kn : kername) (d : cbn_delta_memo) (t : cbn_dtrie) :
  cbn_dt_find kn (cbn_dt_add kn d t) = Some d.
Proof.
  rewrite cbn_dt_find_here, cbn_dt_add_ins, cbn_dt_walk_bits, cbn_dt_upd_bits,
    cbn_dt_walkb_updb_same,
    cbn_dt_ins_here.
  apply cbn_mp_find_set_same.
Qed.

Lemma cbn_dt_find_add_other (kn kn' : kername) (d : cbn_delta_memo) (t : cbn_dtrie) :
  kn' <> kn -> cbn_dt_find kn' (cbn_dt_add kn d t) = cbn_dt_find kn' t.
Proof.
  intros hne. rewrite !cbn_dt_find_here, cbn_dt_add_ins, !cbn_dt_walk_bits, cbn_dt_upd_bits.
  destruct (String.eqb kn'.2 kn.2) eqn:Es.
  - apply cbn_string_eqb_spec in Es. rewrite Es, cbn_dt_walkb_updb_same, cbn_dt_ins_here.
    apply cbn_mp_find_set_other. intros hmp. apply hne.
    destruct kn as [mp id], kn' as [mp' id']; cbn in Es, hmp. now subst.
  - f_equal. apply cbn_dt_here_walkb_updb_other.
    + intros b u. apply cbn_dt_ins_child.
    + intros heq. apply cbn_sbits_inj in heq.
      rewrite <- heq, (proj2 (cbn_string_eqb_spec kn.2 kn.2) eq_refl) in Es. discriminate Es.
Qed.

(** ** The memo's fields

  Each setter writes one field and copies the other five; [cbn_memo_add_entry] writes [cbn_m_codes]
  and [cbn_m_ncode] and copies the other four. *)

Lemma cbn_set_memo_memo (m : cbn_memo) (s : cbn_state) : (cbn_set_memo m s).(cbn_st_memo) = m.
Proof. reflexivity. Qed.

Lemma cbn_memo_set_delta_delta (t : cbn_dtrie) (m : cbn_memo) :
  (cbn_memo_set_delta t m).(cbn_m_delta) = t.
Proof. reflexivity. Qed.

Lemma cbn_memo_set_delta_codes (t : cbn_dtrie) (m : cbn_memo) :
  (cbn_memo_set_delta t m).(cbn_m_codes) = m.(cbn_m_codes).
Proof. reflexivity. Qed.

(** ** Two-level maps *)

Lemma cbn_get2_empty {A : Type} (k1 k2 : cbn_key) : cbn_get2 k1 k2 (PTree.empty (PTree.t A)) = None.
Proof. unfold cbn_get2. now rewrite PTree.gempty. Qed.

Lemma cbn_get2_some_outer {A : Type} (k1 k2 : cbn_key) (m : PTree.t (PTree.t A)) (x : A) :
  cbn_get2 k1 k2 m = Some x -> PTree.get k1 m <> None.
Proof.
  unfold cbn_get2. destruct (PTree.get k1 m) as [m2|]; intros h; [discriminate | discriminate h].
Qed.

Lemma cbn_get_set2_outer {A : Type} (k1 k2 j : cbn_key) (x : A) (m : PTree.t (PTree.t A)) :
  PTree.get j (cbn_set2 k1 k2 x m) <> None -> j = k1 \/ PTree.get j m <> None.
Proof.
  unfold cbn_set2; cbv zeta. intros h.
  destruct (cbn_key_eqb j k1) eqn:E.
  - left. now apply cbn_key_eqb_spec in E.
  - right. rewrite PTree.gso in h; [exact h | exact (cbn_key_neq_of_eqb j k1 E)].
Qed.

(** ** Code indices as numbers, and the freshness of [cbn_m_ncode]

  [cbn_key_succ] is [Pos.succ] under [cbn_key_val], so a code index is a number and the index
  [cbn_memo_add_entry] hands out is above every index the memo's maps hold. *)

Fixpoint cbn_key_val (p : cbn_key) : positive :=
  match p with
  | String2pos.xH => xH
  | String2pos.xO q => xO (cbn_key_val q)
  | String2pos.xI q => xI (cbn_key_val q)
  end.

Lemma cbn_key_val_succ (p : cbn_key) : cbn_key_val (cbn_key_succ p) = Pos.succ (cbn_key_val p).
Proof.
  induction p as [p IH|p IH|]; cbn [cbn_key_succ cbn_key_val];
    [now rewrite IH|reflexivity|reflexivity].
Qed.

Definition cbn_idx_lt (i j : cbn_key) : Prop := (cbn_key_val i < cbn_key_val j)%positive.

Lemma cbn_idx_lt_neq (i j : cbn_key) : cbn_idx_lt i j -> i <> j.
Proof. intros h ->. exact (Pos.lt_irrefl _ h). Qed.

Lemma cbn_idx_lt_succ (i : cbn_key) : cbn_idx_lt i (cbn_key_succ i).
Proof. unfold cbn_idx_lt. rewrite cbn_key_val_succ. apply Pos.lt_succ_diag_r. Qed.

Lemma cbn_idx_lt_up (i j : cbn_key) : cbn_idx_lt i j -> cbn_idx_lt i (cbn_key_succ j).
Proof.
  unfold cbn_idx_lt. rewrite cbn_key_val_succ. intros h.
  exact (Pos.lt_trans _ _ _ h (Pos.lt_succ_diag_r _)).
Qed.

(** [cbn_m_hash] and [cbn_m_once] are keyed by (index, path); [cbn_m_ceq] by
  (index, path, index, path), so indices sit at its first and third level. *)
Definition cbn_memo_fresh (m : cbn_memo) : Prop :=
  (forall i : cbn_key, PTree.get i m.(cbn_m_codes) <> None -> cbn_idx_lt i m.(cbn_m_ncode))
  /\ (forall i : cbn_key, PTree.get i m.(cbn_m_hash) <> None -> cbn_idx_lt i m.(cbn_m_ncode))
  /\ (forall i : cbn_key, PTree.get i m.(cbn_m_once) <> None -> cbn_idx_lt i m.(cbn_m_ncode))
  /\ (forall (i1 p1 : cbn_key) (r : PTree.t (PTree.t bool)),
         cbn_get2 i1 p1 m.(cbn_m_ceq) = Some r ->
         cbn_idx_lt i1 m.(cbn_m_ncode)
         /\ forall i2 : cbn_key, PTree.get i2 r <> None -> cbn_idx_lt i2 m.(cbn_m_ncode)).

Lemma cbn_memo_fresh_empty : cbn_memo_fresh cbn_memo_empty.
Proof.
  unfold cbn_memo_empty, cbn_memo_fresh.
  cbn [cbn_m_codes cbn_m_hash cbn_m_once cbn_m_ceq cbn_m_ncode].
  split; [|split; [|split]].
  - intros i. rewrite PTree.gempty. intros h; now destruct h.
  - intros i. rewrite PTree.gempty. intros h; now destruct h.
  - intros i. rewrite PTree.gempty. intros h; now destruct h.
  - intros i1 p1 r h. rewrite cbn_get2_empty in h. discriminate h.
Qed.

Lemma cbn_memo_fresh_codes (m : cbn_memo) (i : cbn_key) :
  cbn_memo_fresh m -> PTree.get i m.(cbn_m_codes) <> None -> cbn_idx_lt i m.(cbn_m_ncode).
Proof. intros [h _]. exact (h i). Qed.

Lemma cbn_memo_fresh_add_entry (e : cbn_code_entry) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_memo_fresh (snd (cbn_memo_add_entry e m)).
Proof.
  intros [hc [hh [ho hq]]]. unfold cbn_memo_add_entry, cbn_memo_fresh.
  cbn [snd cbn_m_codes cbn_m_hash cbn_m_once cbn_m_ceq cbn_m_ncode].
  split; [|split; [|split]].
  - intros i hi. destruct (cbn_key_eqb i m.(cbn_m_ncode)) eqn:E.
    + apply cbn_key_eqb_spec in E as ->. apply cbn_idx_lt_succ.
    + rewrite PTree.gso in hi by exact (cbn_key_neq_of_eqb i _ E).
      exact (cbn_idx_lt_up _ _ (hc i hi)).
  - intros i hi. exact (cbn_idx_lt_up _ _ (hh i hi)).
  - intros i hi. exact (cbn_idx_lt_up _ _ (ho i hi)).
  - intros i1 p1 r hi. destruct (hq i1 p1 r hi) as [h1 h2].
    split; [exact (cbn_idx_lt_up _ _ h1)|]. intros i2 h2'. exact (cbn_idx_lt_up _ _ (h2 i2 h2')).
Qed.

Lemma cbn_memo_fresh_set_delta (t : cbn_dtrie) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_memo_fresh (cbn_memo_set_delta t m).
Proof. intros h. exact h. Qed.

Lemma cbn_memo_fresh_set_once (i p : cbn_key) (b : bool) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_idx_lt i m.(cbn_m_ncode) ->
  cbn_memo_fresh (cbn_memo_set_once (cbn_set2 i p b m.(cbn_m_once)) m).
Proof.
  intros [hc [hh [ho hq]]] hi. unfold cbn_memo_set_once, cbn_memo_fresh.
  cbn [cbn_m_codes cbn_m_hash cbn_m_once cbn_m_ceq cbn_m_ncode].
  split; [exact hc|]. split; [exact hh|]. split; [|exact hq].
  intros j hj. destruct (cbn_get_set2_outer i p j b m.(cbn_m_once) hj) as [->|h]; [exact hi|].
  exact (ho j h).
Qed.

Lemma cbn_memo_fresh_set_hash (i p : cbn_key) (v : N) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_idx_lt i m.(cbn_m_ncode) ->
  cbn_memo_fresh (cbn_memo_set_hash (cbn_set2 i p v m.(cbn_m_hash)) m).
Proof.
  intros [hc [hh [ho hq]]] hi. unfold cbn_memo_set_hash, cbn_memo_fresh.
  cbn [cbn_m_codes cbn_m_hash cbn_m_once cbn_m_ceq cbn_m_ncode].
  split; [exact hc|]. split; [|split; [exact ho | exact hq]].
  intros j hj. destruct (cbn_get_set2_outer i p j v m.(cbn_m_hash) hj) as [->|h]; [exact hi|].
  exact (hh j h).
Qed.

Lemma cbn_memo_fresh_set_ceq (i1 p1 i2 p2 : cbn_key) (b : bool) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_idx_lt i1 m.(cbn_m_ncode) -> cbn_idx_lt i2 m.(cbn_m_ncode) ->
  cbn_memo_fresh
    (cbn_memo_set_ceq
       (cbn_set2 i1 p1
          (cbn_set2 i2 p2 b
             (match cbn_get2 i1 p1 m.(cbn_m_ceq) with Some q => q | None => PTree.empty _ end))
          m.(cbn_m_ceq)) m).
Proof.
  intros [hc [hh [ho hq]]] h1 h2. unfold cbn_memo_set_ceq, cbn_memo_fresh.
  cbn [cbn_m_codes cbn_m_hash cbn_m_once cbn_m_ceq cbn_m_ncode].
  split; [exact hc|]. split; [exact hh|]. split; [exact ho|].
  intros j1 q1 r hr.
  destruct (cbn_key_eqb j1 i1) eqn:E1; destruct (cbn_key_eqb q1 p1) eqn:E2.
  - apply cbn_key_eqb_spec in E1 as ->. apply cbn_key_eqb_spec in E2 as ->.
    rewrite cbn_get2_set2_same in hr. injection hr as <-.
    split; [exact h1|]. intros k hk.
    destruct (cbn_get_set2_outer i2 p2 k b _ hk) as [->|hk0]; [exact h2|].
    destruct (cbn_get2 i1 p1 m.(cbn_m_ceq)) as [r0|] eqn:Er0.
    + exact (proj2 (hq i1 p1 r0 Er0) k hk0).
    + rewrite PTree.gempty in hk0. now destruct hk0.
  - rewrite cbn_get2_set2_other in hr by (right; exact (cbn_key_neq_of_eqb _ _ E2)).
    exact (hq j1 q1 r hr).
  - rewrite cbn_get2_set2_other in hr by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
    exact (hq j1 q1 r hr).
  - rewrite cbn_get2_set2_other in hr by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
    exact (hq j1 q1 r hr).
Qed.

(** ** The caches [cbn_m_once] and [cbn_m_hash]

  Both are read and written at a code's identifier, so their statements speak of a code
  whose entry is in the table and which satisfies [cbn_code_inv] for it: all such codes at one
  identifier have one term ([cbn_same_ident_term], from [cbn_same_id_sound_table]). *)

Definition cbn_once_ok (m : cbn_memo) : Prop :=
  forall (c : cbn_code) (e : cbn_code_entry) (b : bool),
    cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) m.(cbn_m_once) = Some b ->
    PTree.get c.(cbn_c_entry) m.(cbn_m_codes) = Some e ->
    cbn_code_inv e c ->
    b = Nat.leb (cbn_occ 0 c.(cbn_c_term)) 1.

Definition cbn_hash_ok (m : cbn_memo) : Prop :=
  forall (c : cbn_code) (e : cbn_code_entry) (h : N),
    cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) m.(cbn_m_hash) = Some h ->
    PTree.get c.(cbn_c_entry) m.(cbn_m_codes) = Some e ->
    cbn_code_inv e c ->
    h = cbn_thash c.(cbn_c_term).

Lemma cbn_once_ok_fields (m m' : cbn_memo) :
  m'.(cbn_m_once) = m.(cbn_m_once) -> m'.(cbn_m_codes) = m.(cbn_m_codes) -> cbn_once_ok m ->
    cbn_once_ok m'.
Proof.
  intros h1 h2 h c e b g1 g2. rewrite h1 in g1. rewrite h2 in g2. exact (h c e b g1 g2).
Qed.

Lemma cbn_hash_ok_fields (m m' : cbn_memo) :
  m'.(cbn_m_hash) = m.(cbn_m_hash) -> m'.(cbn_m_codes) = m.(cbn_m_codes) -> cbn_hash_ok m ->
    cbn_hash_ok m'.
Proof.
  intros h1 h2 h c e v g1 g2. rewrite h1 in g1. rewrite h2 in g2. exact (h c e v g1 g2).
Qed.

Lemma cbn_once_ok_empty : cbn_once_ok cbn_memo_empty.
Proof.
  intros c e b g _ _. cbn [cbn_memo_empty cbn_m_once] in g. rewrite cbn_get2_empty in g.
  discriminate g.
Qed.

Lemma cbn_hash_ok_empty : cbn_hash_ok cbn_memo_empty.
Proof.
  intros c e v g _ _. cbn [cbn_memo_empty cbn_m_hash] in g. rewrite cbn_get2_empty in g.
  discriminate g.
Qed.

(** Two codes with the same identifier, each read against its table entry, have one term. *)
Lemma cbn_same_ident_term (codes : PTree.t cbn_code_entry) (c1 c2 : cbn_code)
  (e1 e2 : cbn_code_entry) :
  c1.(cbn_c_entry) = c2.(cbn_c_entry) -> c1.(cbn_c_path) = c2.(cbn_c_path) ->
  PTree.get c1.(cbn_c_entry) codes = Some e1 -> cbn_code_inv e1 c1 ->
  PTree.get c2.(cbn_c_entry) codes = Some e2 -> cbn_code_inv e2 c2 ->
  c1.(cbn_c_term) = c2.(cbn_c_term).
Proof.
  intros he hp g1 h1 g2 h2.
  refine (cbn_same_id_sound_table codes e1 e2 c1 c2 _ g1 h1 g2 h2).
  apply cbn_same_id_spec. split; assumption.
Qed.

Lemma cbn_once_ok_set (c : cbn_code) (e : cbn_code_entry) (m : cbn_memo) :
  cbn_once_ok m ->
  PTree.get c.(cbn_c_entry) m.(cbn_m_codes) = Some e -> cbn_code_inv e c ->
  cbn_once_ok (cbn_memo_set_once
             (cbn_set2 c.(cbn_c_entry) c.(cbn_c_path) (Nat.leb (cbn_occ 0 c.(cbn_c_term)) 1)
               m.(cbn_m_once)) m).
Proof.
  intros h g hi c' e' b. cbn [cbn_memo_set_once cbn_m_once cbn_m_codes]. intros g' g2 hi'.
  destruct (cbn_key_eqb c'.(cbn_c_entry) c.(cbn_c_entry)) eqn:E1;
    destruct (cbn_key_eqb c'.(cbn_c_path) c.(cbn_c_path)) eqn:E2.
  - apply cbn_key_eqb_spec in E1. apply cbn_key_eqb_spec in E2.
    rewrite E1, E2, cbn_get2_set2_same in g'. injection g' as <-.
    rewrite (cbn_same_ident_term m.(cbn_m_codes) c' c e' e E1 E2 g2 hi' g hi). reflexivity.
  - rewrite cbn_get2_set2_other in g' by (right; exact (cbn_key_neq_of_eqb _ _ E2)).
    exact (h c' e' b g' g2 hi').
  - rewrite cbn_get2_set2_other in g' by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
    exact (h c' e' b g' g2 hi').
  - rewrite cbn_get2_set2_other in g' by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
    exact (h c' e' b g' g2 hi').
Qed.

Lemma cbn_hash_ok_set (c : cbn_code) (e : cbn_code_entry) (m : cbn_memo) :
  cbn_hash_ok m ->
  PTree.get c.(cbn_c_entry) m.(cbn_m_codes) = Some e -> cbn_code_inv e c ->
  cbn_hash_ok (cbn_memo_set_hash (cbn_set2 c.(cbn_c_entry) c.(cbn_c_path) (cbn_thash c.(cbn_c_term))
    m.(cbn_m_hash)) m).
Proof.
  intros h g hi c' e' v. cbn [cbn_memo_set_hash cbn_m_hash cbn_m_codes]. intros g' g2 hi'.
  destruct (cbn_key_eqb c'.(cbn_c_entry) c.(cbn_c_entry)) eqn:E1;
    destruct (cbn_key_eqb c'.(cbn_c_path) c.(cbn_c_path)) eqn:E2.
  - apply cbn_key_eqb_spec in E1. apply cbn_key_eqb_spec in E2.
    rewrite E1, E2, cbn_get2_set2_same in g'. injection g' as <-.
    rewrite (cbn_same_ident_term m.(cbn_m_codes) c' c e' e E1 E2 g2 hi' g hi). reflexivity.
  - rewrite cbn_get2_set2_other in g' by (right; exact (cbn_key_neq_of_eqb _ _ E2)).
    exact (h c' e' v g' g2 hi').
  - rewrite cbn_get2_set2_other in g' by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
    exact (h c' e' v g' g2 hi').
  - rewrite cbn_get2_set2_other in g' by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
    exact (h c' e' v g' g2 hi').
Qed.

(** An added entry carries a fresh index, so no stale cache row is read against it. *)
Lemma cbn_once_ok_add_entry (e : cbn_code_entry) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_once_ok m -> cbn_once_ok (snd (cbn_memo_add_entry e m)).
Proof.
  intros [_ [_ [ho _]]] h c e' b. cbn [cbn_memo_add_entry snd cbn_m_once cbn_m_codes].
  intros g g2 hi.
  destruct (cbn_key_eqb c.(cbn_c_entry) m.(cbn_m_ncode)) eqn:E.
  - exfalso. apply cbn_key_eqb_spec in E.
    pose proof (ho c.(cbn_c_entry) (cbn_get2_some_outer _ _ _ _ g)) as hlt.
    unfold cbn_idx_lt in hlt. rewrite E in hlt. exact (Pos.lt_irrefl _ hlt).
  - rewrite PTree.gso in g2 by exact (cbn_key_neq_of_eqb _ _ E). exact (h c e' b g g2 hi).
Qed.

Lemma cbn_hash_ok_add_entry (e : cbn_code_entry) (m : cbn_memo) :
  cbn_memo_fresh m -> cbn_hash_ok m -> cbn_hash_ok (snd (cbn_memo_add_entry e m)).
Proof.
  intros [_ [hh _]] h c e' v. cbn [cbn_memo_add_entry snd cbn_m_hash cbn_m_codes].
  intros g g2 hi.
  destruct (cbn_key_eqb c.(cbn_c_entry) m.(cbn_m_ncode)) eqn:E.
  - exfalso. apply cbn_key_eqb_spec in E.
    pose proof (hh c.(cbn_c_entry) (cbn_get2_some_outer _ _ _ _ g)) as hlt.
    unfold cbn_idx_lt in hlt. rewrite E in hlt. exact (Pos.lt_irrefl _ hlt).
  - rewrite PTree.gso in g2 by exact (cbn_key_neq_of_eqb _ _ E). exact (h c e' v g g2 hi).
Qed.

(** ** [cbn_once_body] and [cbn_code_hash] over the state *)

Lemma cbn_once_body_memo (c : cbn_code) (s : cbn_state) :
  ((snd (cbn_once_body c s)).(cbn_st_memo)).(cbn_m_codes) = ((s.(cbn_st_memo)).(cbn_m_codes))
  /\ ((snd (cbn_once_body c s)).(cbn_st_memo)).(cbn_m_ncode) = ((s.(cbn_st_memo)).(cbn_m_ncode))
  /\ ((snd (cbn_once_body c s)).(cbn_st_memo)).(cbn_m_delta) = ((s.(cbn_st_memo)).(cbn_m_delta))
  /\ ((snd (cbn_once_body c s)).(cbn_st_memo)).(cbn_m_hash) = ((s.(cbn_st_memo)).(cbn_m_hash))
  /\ ((snd (cbn_once_body c s)).(cbn_st_memo)).(cbn_m_ceq) = ((s.(cbn_st_memo)).(cbn_m_ceq)).
Proof.
  unfold cbn_once_body. destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path)
    ((s.(cbn_st_memo)).(cbn_m_once)));
    cbn [snd]; repeat split.
Qed.

Lemma cbn_code_hash_state (c : cbn_code) (s : cbn_state) :
  (snd (cbn_code_hash c s)).(cbn_st_heap) = s.(cbn_st_heap)
  /\ (snd (cbn_code_hash c s)).(cbn_st_next) = s.(cbn_st_next)
  /\ (snd (cbn_code_hash c s)).(cbn_st_room) = s.(cbn_st_room)
  /\ (snd (cbn_code_hash c s)).(cbn_st_steps) = s.(cbn_st_steps)
  /\ (snd (cbn_code_hash c s)).(cbn_st_gam) = s.(cbn_st_gam).
Proof.
  unfold cbn_code_hash. destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path)
    ((s.(cbn_st_memo)).(cbn_m_hash)));
    cbn [snd]; repeat split.
Qed.

Lemma cbn_code_hash_memo (c : cbn_code) (s : cbn_state) :
  ((snd (cbn_code_hash c s)).(cbn_st_memo)).(cbn_m_codes) = ((s.(cbn_st_memo)).(cbn_m_codes))
  /\ ((snd (cbn_code_hash c s)).(cbn_st_memo)).(cbn_m_ncode) = ((s.(cbn_st_memo)).(cbn_m_ncode))
  /\ ((snd (cbn_code_hash c s)).(cbn_st_memo)).(cbn_m_delta) = ((s.(cbn_st_memo)).(cbn_m_delta))
  /\ ((snd (cbn_code_hash c s)).(cbn_st_memo)).(cbn_m_once) = ((s.(cbn_st_memo)).(cbn_m_once))
  /\ ((snd (cbn_code_hash c s)).(cbn_st_memo)).(cbn_m_ceq) = ((s.(cbn_st_memo)).(cbn_m_ceq)).
Proof.
  unfold cbn_code_hash. destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path)
    ((s.(cbn_st_memo)).(cbn_m_hash)));
    cbn [snd]; repeat split.
Qed.

Lemma cbn_ceq_set_state (c1 c2 : cbn_code) (b : bool) (s : cbn_state) :
  (cbn_ceq_set c1 c2 b s).(cbn_st_heap) = s.(cbn_st_heap)
  /\ (cbn_ceq_set c1 c2 b s).(cbn_st_next) = s.(cbn_st_next)
  /\ (cbn_ceq_set c1 c2 b s).(cbn_st_room) = s.(cbn_st_room)
  /\ (cbn_ceq_set c1 c2 b s).(cbn_st_steps) = s.(cbn_st_steps)
  /\ (cbn_ceq_set c1 c2 b s).(cbn_st_gam) = s.(cbn_st_gam).
Proof. unfold cbn_ceq_set; cbv zeta. repeat split. Qed.

Lemma cbn_ceq_set_memo (c1 c2 : cbn_code) (b : bool) (s : cbn_state) :
  (((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).(cbn_m_codes)) = ((s.(cbn_st_memo)).(cbn_m_codes))
  /\ (((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).(cbn_m_ncode)) = ((s.(cbn_st_memo)).(cbn_m_ncode))
  /\ (((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).(cbn_m_delta)) = ((s.(cbn_st_memo)).(cbn_m_delta))
  /\ (((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).(cbn_m_once)) = ((s.(cbn_st_memo)).(cbn_m_once))
  /\ (((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).(cbn_m_hash)) = ((s.(cbn_st_memo)).(cbn_m_hash)).
Proof. unfold cbn_ceq_set; cbv zeta. repeat split. Qed.

Lemma cbn_once_body_ok (c : cbn_code) (e : cbn_code_entry) (s : cbn_state) :
  cbn_once_ok (s.(cbn_st_memo)) ->
  PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e -> cbn_code_inv e c ->
  cbn_once_ok ((snd (cbn_once_body c s)).(cbn_st_memo)).
Proof.
  intros h g hi. unfold cbn_once_body.
  destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) ((s.(cbn_st_memo)).(cbn_m_once))) as [b|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite cbn_set_memo_memo. exact (cbn_once_ok_set c e (s.(cbn_st_memo)) h g hi).
Qed.

Lemma cbn_once_body_fresh (c : cbn_code) (e : cbn_code_entry) (s : cbn_state) :
  cbn_memo_fresh (s.(cbn_st_memo)) ->
  PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
  cbn_memo_fresh ((snd (cbn_once_body c s)).(cbn_st_memo)).
Proof.
  intros h g. unfold cbn_once_body.
  destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) ((s.(cbn_st_memo)).(cbn_m_once))) as [b|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite cbn_set_memo_memo. apply cbn_memo_fresh_set_once; [exact h|].
  apply (cbn_memo_fresh_codes (s.(cbn_st_memo)) c.(cbn_c_entry) h). rewrite g. discriminate.
Qed.

Lemma cbn_code_hash_ok (c : cbn_code) (e : cbn_code_entry) (s : cbn_state) :
  cbn_hash_ok (s.(cbn_st_memo)) ->
  PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e -> cbn_code_inv e c ->
  cbn_hash_ok ((snd (cbn_code_hash c s)).(cbn_st_memo)).
Proof.
  intros h g hi. unfold cbn_code_hash.
  destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) ((s.(cbn_st_memo)).(cbn_m_hash))) as [v|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite cbn_set_memo_memo. exact (cbn_hash_ok_set c e (s.(cbn_st_memo)) h g hi).
Qed.

Lemma cbn_code_hash_fresh (c : cbn_code) (e : cbn_code_entry) (s : cbn_state) :
  cbn_memo_fresh (s.(cbn_st_memo)) ->
  PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
  cbn_memo_fresh ((snd (cbn_code_hash c s)).(cbn_st_memo)).
Proof.
  intros h g. unfold cbn_code_hash.
  destruct (cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) ((s.(cbn_st_memo)).(cbn_m_hash))) as [v|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite cbn_set_memo_memo. apply cbn_memo_fresh_set_hash; [exact h|].
  apply (cbn_memo_fresh_codes (s.(cbn_st_memo)) c.(cbn_c_entry) h). rewrite g. discriminate.
Qed.

(** ** Instantiated code and PCUIC's delta step *)

Lemma cbn_inst_code_nil (t : term) : cbn_inst_code [] t = t.
Proof. reflexivity. Qed.

Lemma cbn_inst_code_cons (l : Level.t) (u : Instance.t) (t : term) :
  cbn_inst_code (l :: u) t = subst_instance (l :: u) t.
Proof. reflexivity. Qed.

(** *** The empty instance

  [cbn_inst_code [] body] is [body] where PCUIC's [red_delta] produces
  [subst_instance [] body]. The two agree exactly when [body] carries no universe
  variable, and a constant whose universe context has no variables — in particular a
  monomorphic one — has such a body in a well-formed environment. The chain is
  MetaRocq's: [on_declared_constant] types the body in [(Σ, cst_universes cb)],
  [typing_wf_universes] turns that into [wf_universes], [wf_universes_closedu] (with
  [weaken_lookup_on_global_env'] for its [on_udecl_prop] side condition) turns that into
  [closedu #|polymorphic_instance (cst_universes cb)| body], and
  [closedu_subst_instance] then says every instance leaves the body alone. *)

Lemma cbn_poly_instance_abstract (univs : universes_decl) :
  polymorphic_instance univs = abstract_instance univs.
Proof. destruct univs; reflexivity. Qed.

Lemma cbn_declared_constant_body_closedu {cf : checker_flags} (Σ : global_env)
    (kn : kername) (cb : constant_body) (body : term) :
  wf Σ -> lookup_env Σ kn = Some (ConstantDecl cb) -> cb.(cst_body) = Some body ->
  closedu #|polymorphic_instance cb.(cst_universes)| body.
Proof.
  intros wfΣ hl hb.
  assert (hdecl : declared_constant Σ kn cb)
    by (apply declared_constant_from_gen; exact hl).
  pose proof (on_declared_constant wfΣ hdecl) as hon.
  destruct hon as [hty _]. rewrite hb in hty. cbn in hty.
  pose proof (typing_wf_universes (Σ := (Σ, cb.(cst_universes))) wfΣ hty) as hwu.
  apply andb_true_iff in hwu as [hwu _].
  refine (wf_universes_closedu (Σ := Σ) (wfΣ := wfΣ) _ hwu).
  exact (weaken_lookup_on_global_env' Σ kn (ConstantDecl cb) wfΣ hl).
Qed.

(** The delta step for *every* instance: the side condition is vacuous unless the
  instance is empty. For the empty instance the machine's [cbn_inst_code] returns the body
  unchanged, where PCUIC's [red_delta] produces [subst_instance [] body], and
  [subst_instance []] sends every [Level.lvar] to [Level.lzero]. The two differ on any body
  that mentions a universe variable, so the side condition is needed for a polymorphic
  constant applied to the empty instance, whatever [Σ] is. *)
Lemma cbn_inst_code_red1_gen {cf : checker_flags} (Σ : global_env) (Γ : context)
    (kn : kername) (ui : Instance.t) (cb : constant_body) (body : term) :
  wf Σ -> lookup_env Σ kn = Some (ConstantDecl cb) -> cb.(cst_body) = Some body ->
  (ui = [] -> #|polymorphic_instance cb.(cst_universes)| = 0) ->
  red1 Σ Γ (tConst kn ui) (cbn_inst_code ui body).
Proof.
  intros wfΣ hl hb hmono.
  assert (hdecl : declared_constant Σ kn cb)
    by (apply declared_constant_from_gen; exact hl).
  destruct ui as [|l ui]; [|rewrite cbn_inst_code_cons; eapply red_delta; eassumption].
  assert (hcl : closedu 0 body).
  { rewrite <- (hmono eq_refl).
    exact (cbn_declared_constant_body_closedu Σ kn cb body wfΣ hl hb). }
  rewrite cbn_inst_code_nil, <- (closedu_subst_instance [] body hcl).
  eapply red_delta; eassumption.
Qed.

(** ** Pairs returned by the machine *)

Lemma cbn_COk_pair_inj {A B : Type} (x1 y1 : A) (x2 y2 : B) :
  CbnCOk (x1, x2) = CbnCOk (y1, y2) -> x1 = y1 /\ x2 = y2.
Proof. intros h. injection h as h1 h2. split; assumption. Qed.

(** ** The environment-facing invariants: delta and the code-equality cache *)

Section Memo.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** The syntactic test [cbn_code_eq] falls back on. *)
  Definition cbn_ceq_term (t u : term) : bool :=
    eqb_term_upto_univ (abstract_env_compare_universe X) (abstract_env_compare_sort X)
      (compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X))
      Conv t u.

  (** *** The code-equality cache

    The bit stored for a pair of identifiers is the value of [cbn_ceq_term] on the two
    terms, not a claim that they are equal: see the file header. *)

  Definition cbn_ceq_lookup (c1 c2 : cbn_code) (m : cbn_memo) : option bool :=
    match cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) m.(cbn_m_ceq) with
    | Some q => cbn_get2 c2.(cbn_c_entry) c2.(cbn_c_path) q
    | None => None
    end.

  Lemma cbn_ceq_get_lookup (c1 c2 : cbn_code) (s : cbn_state) :
    cbn_ceq_get c1 c2 s = cbn_ceq_lookup c1 c2 (s.(cbn_st_memo)).
  Proof. reflexivity. Qed.

  Definition cbn_ceq_ok (m : cbn_memo) : Prop :=
    forall (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (b : bool),
      cbn_ceq_lookup c1 c2 m = Some b ->
      PTree.get c1.(cbn_c_entry) m.(cbn_m_codes) = Some e1 -> cbn_code_inv e1 c1 ->
      PTree.get c2.(cbn_c_entry) m.(cbn_m_codes) = Some e2 -> cbn_code_inv e2 c2 ->
      b = cbn_ceq_term c1.(cbn_c_term) c2.(cbn_c_term).

  Lemma cbn_ceq_ok_fields (m m' : cbn_memo) :
    m'.(cbn_m_ceq) = m.(cbn_m_ceq) -> m'.(cbn_m_codes) = m.(cbn_m_codes) -> cbn_ceq_ok m ->
      cbn_ceq_ok m'.
  Proof.
    intros h1 h2 h c1 c2 e1 e2 b g g1 hi1 g2 hi2.
    unfold cbn_ceq_lookup in g. rewrite h1 in g. rewrite h2 in g1, g2.
    exact (h c1 c2 e1 e2 b g g1 hi1 g2 hi2).
  Qed.

  Lemma cbn_ceq_ok_empty : cbn_ceq_ok cbn_memo_empty.
  Proof.
    intros c1 c2 e1 e2 b g _ _ _ _. unfold cbn_ceq_lookup in g.
    cbn [cbn_memo_empty cbn_m_ceq] in g. rewrite cbn_get2_empty in g. discriminate g.
  Qed.

  Lemma cbn_ceq_ok_add_entry (e : cbn_code_entry) (m : cbn_memo) :
    cbn_memo_fresh m -> cbn_ceq_ok m -> cbn_ceq_ok (snd (cbn_memo_add_entry e m)).
  Proof.
    intros [_ [_ [_ hq]]] h c1 c2 e1 e2 b. unfold cbn_ceq_lookup.
    cbn [cbn_memo_add_entry snd cbn_m_ceq cbn_m_codes]. intros g g1 hi1 g2 hi2.
    destruct (cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) m.(cbn_m_ceq)) as [r|] eqn:Er;
      [|discriminate g].
    destruct (hq c1.(cbn_c_entry) c1.(cbn_c_path) r Er) as [hlt1 hlt2].
    assert (hne1 : c1.(cbn_c_entry) <> m.(cbn_m_ncode)) by exact (cbn_idx_lt_neq _ _ hlt1).
    assert (hne2 : c2.(cbn_c_entry) <> m.(cbn_m_ncode)).
    { apply cbn_idx_lt_neq. apply hlt2. exact (cbn_get2_some_outer _ _ _ _ g). }
    rewrite PTree.gso in g1 by exact hne1. rewrite PTree.gso in g2 by exact hne2.
    refine (h c1 c2 e1 e2 b _ g1 hi1 g2 hi2). unfold cbn_ceq_lookup. now rewrite Er.
  Qed.

  Lemma cbn_ceq_ok_set (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (m : cbn_memo) :
    cbn_ceq_ok m ->
    PTree.get c1.(cbn_c_entry) m.(cbn_m_codes) = Some e1 -> cbn_code_inv e1 c1 ->
    PTree.get c2.(cbn_c_entry) m.(cbn_m_codes) = Some e2 -> cbn_code_inv e2 c2 ->
    cbn_ceq_ok
      (cbn_memo_set_ceq
         (cbn_set2 c1.(cbn_c_entry) c1.(cbn_c_path)
            (cbn_set2 c2.(cbn_c_entry) c2.(cbn_c_path)
              (cbn_ceq_term c1.(cbn_c_term) c2.(cbn_c_term))
               (match cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) m.(cbn_m_ceq) with
                | Some q => q
                | None => PTree.empty _
                end))
            m.(cbn_m_ceq)) m).
  Proof.
    intros h g1 hi1 g2 hi2 d1 d2 f1 f2 b. unfold cbn_ceq_lookup.
    cbn [cbn_memo_set_ceq cbn_m_ceq cbn_m_codes]. intros g k1 ki1 k2 ki2.
    destruct (cbn_key_eqb d1.(cbn_c_entry) c1.(cbn_c_entry)) eqn:E1;
      destruct (cbn_key_eqb d1.(cbn_c_path) c1.(cbn_c_path)) eqn:E2.
    - apply cbn_key_eqb_spec in E1. apply cbn_key_eqb_spec in E2.
      assert (hd1 : d1.(cbn_c_term) = c1.(cbn_c_term))
        by exact (cbn_same_ident_term m.(cbn_m_codes) d1 c1 f1 e1 E1 E2 k1 ki1 g1 hi1).
      rewrite E1, E2, cbn_get2_set2_same in g.
      destruct (cbn_key_eqb d2.(cbn_c_entry) c2.(cbn_c_entry)) eqn:E3;
        destruct (cbn_key_eqb d2.(cbn_c_path) c2.(cbn_c_path)) eqn:E4.
      + apply cbn_key_eqb_spec in E3. apply cbn_key_eqb_spec in E4.
        rewrite E3, E4, cbn_get2_set2_same in g. injection g as <-.
        rewrite hd1, (cbn_same_ident_term m.(cbn_m_codes) d2 c2 f2 e2 E3 E4 k2 ki2 g2 hi2).
        reflexivity.
      + rewrite cbn_get2_set2_other in g by (right; exact (cbn_key_neq_of_eqb _ _ E4)).
        refine (h d1 d2 f1 f2 b _ k1 ki1 k2 ki2). unfold cbn_ceq_lookup. rewrite E1, E2.
        destruct (cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) m.(cbn_m_ceq)) as [r|]
          eqn:Er; [exact g|].
        rewrite cbn_get2_empty in g. discriminate g.
      + rewrite cbn_get2_set2_other in g by (left; exact (cbn_key_neq_of_eqb _ _ E3)).
        refine (h d1 d2 f1 f2 b _ k1 ki1 k2 ki2). unfold cbn_ceq_lookup. rewrite E1, E2.
        destruct (cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) m.(cbn_m_ceq)) as [r|]
          eqn:Er; [exact g|].
        rewrite cbn_get2_empty in g. discriminate g.
      + rewrite cbn_get2_set2_other in g by (left; exact (cbn_key_neq_of_eqb _ _ E3)).
        refine (h d1 d2 f1 f2 b _ k1 ki1 k2 ki2). unfold cbn_ceq_lookup. rewrite E1, E2.
        destruct (cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) m.(cbn_m_ceq)) as [r|]
          eqn:Er; [exact g|].
        rewrite cbn_get2_empty in g. discriminate g.
    - rewrite cbn_get2_set2_other in g by (right; exact (cbn_key_neq_of_eqb _ _ E2)).
      exact (h d1 d2 f1 f2 b g k1 ki1 k2 ki2).
    - rewrite cbn_get2_set2_other in g by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
      exact (h d1 d2 f1 f2 b g k1 ki1 k2 ki2).
    - rewrite cbn_get2_set2_other in g by (left; exact (cbn_key_neq_of_eqb _ _ E1)).
      exact (h d1 d2 f1 f2 b g k1 ki1 k2 ki2).
  Qed.

  Lemma cbn_ceq_set_ok (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (s : cbn_state) :
    cbn_ceq_ok (s.(cbn_st_memo)) ->
    PTree.get c1.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e1 -> cbn_code_inv e1 c1 ->
    PTree.get c2.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e2 -> cbn_code_inv e2 c2 ->
    cbn_ceq_ok (((cbn_ceq_set c1 c2 (cbn_ceq_term c1.(cbn_c_term) c2.(cbn_c_term))
      s)).(cbn_st_memo)).
  Proof.
    intros h g1 hi1 g2 hi2. unfold cbn_ceq_set; cbv zeta. rewrite cbn_set_memo_memo.
    exact (cbn_ceq_ok_set c1 c2 e1 e2 (s.(cbn_st_memo)) h g1 hi1 g2 hi2).
  Qed.

  Lemma cbn_ceq_set_fresh (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (s : cbn_state) (b : bool) :
    cbn_memo_fresh (s.(cbn_st_memo)) ->
    PTree.get c1.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e1 ->
    PTree.get c2.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e2 ->
    cbn_memo_fresh ((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).
  Proof.
    intros h g1 g2. unfold cbn_ceq_set; cbv zeta. rewrite cbn_set_memo_memo.
    apply cbn_memo_fresh_set_ceq; [exact h| |].
    - apply (cbn_memo_fresh_codes (s.(cbn_st_memo)) c1.(cbn_c_entry) h). rewrite g1. discriminate.
    - apply (cbn_memo_fresh_codes (s.(cbn_st_memo)) c2.(cbn_c_entry) h). rewrite g2. discriminate.
  Qed.

  Lemma cbn_ceq_set_once_ok (c1 c2 : cbn_code) (b : bool) (s : cbn_state) :
    cbn_once_ok (s.(cbn_st_memo)) -> cbn_once_ok ((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).
  Proof.
    apply cbn_once_ok_fields;
      [exact (proj1 (proj2 (proj2 (proj2 (cbn_ceq_set_memo c1 c2 b s)))))
      | exact (proj1 (cbn_ceq_set_memo c1 c2 b s))].
  Qed.

  Lemma cbn_ceq_set_hash_ok (c1 c2 : cbn_code) (b : bool) (s : cbn_state) :
    cbn_hash_ok (s.(cbn_st_memo)) -> cbn_hash_ok ((cbn_ceq_set c1 c2 b s).(cbn_st_memo)).
  Proof.
    apply cbn_hash_ok_fields;
      [exact (proj2 (proj2 (proj2 (proj2 (cbn_ceq_set_memo c1 c2 b s)))))
      | exact (proj1 (cbn_ceq_set_memo c1 c2 b s))].
  Qed.

  (** *** What a [true] from [cbn_code_eq] gives

    Either the two codes have the same term, or the syntactic comparison up to universes
    says [true]. Nothing is claimed of a [false]. *)

  Lemma cbn_code_eq_sound (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (s : cbn_state) :
    cbn_ceq_ok (s.(cbn_st_memo)) ->
    PTree.get c1.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e1 -> cbn_code_inv e1 c1 ->
    PTree.get c2.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e2 -> cbn_code_inv e2 c2 ->
    fst (cbn_code_eq X_type X c1 c2 s) = true ->
    c1.(cbn_c_term) = c2.(cbn_c_term) \/ cbn_ceq_term c1.(cbn_c_term) c2.(cbn_c_term) = true.
  Proof.
    intros hq g1 hi1 g2 hi2. unfold cbn_code_eq.
    destruct (cbn_same_id c1 c2) eqn:Esid.
    { intros _. left.
      exact (cbn_same_id_sound_table ((s.(cbn_st_memo)).(cbn_m_codes)) e1 e2 c1 c2 Esid g1
        hi1 g2 hi2). }
    destruct (negb (cbn_entry_wf c1.(cbn_c_entry) s && cbn_entry_wf c2.(cbn_c_entry) s)) eqn:Ewf;
      [cbn [fst]; intros hc; discriminate hc|].
    destruct (cbn_code_hash c1 s) as [v1 s1] eqn:E1.
    destruct (cbn_code_hash c2 s1) as [v2 s2] eqn:E2.
    assert (hs1 : s1 = snd (cbn_code_hash c1 s)) by (rewrite E1; reflexivity).
    assert (hs2 : s2 = snd (cbn_code_hash c2 s1)) by (rewrite E2; reflexivity).
    assert (hc1 : ((s1.(cbn_st_memo)).(cbn_m_codes)) = ((s.(cbn_st_memo)).(cbn_m_codes)))
      by (rewrite hs1; apply (proj1 (cbn_code_hash_memo c1 s))).
    assert (hq1 : ((s1.(cbn_st_memo)).(cbn_m_ceq)) = ((s.(cbn_st_memo)).(cbn_m_ceq)))
      by (rewrite hs1; exact (proj2 (proj2 (proj2 (proj2 (cbn_code_hash_memo c1 s)))))).
    assert (hc2 : ((s2.(cbn_st_memo)).(cbn_m_codes)) = ((s1.(cbn_st_memo)).(cbn_m_codes)))
      by (rewrite hs2; apply (proj1 (cbn_code_hash_memo c2 s1))).
    assert (hq2 : ((s2.(cbn_st_memo)).(cbn_m_ceq)) = ((s1.(cbn_st_memo)).(cbn_m_ceq)))
      by (rewrite hs2; exact (proj2 (proj2 (proj2 (proj2 (cbn_code_hash_memo c2 s1)))))).
    destruct (negb (N.eqb v1 v2)) eqn:Eh; [cbn [fst]; intros hc; discriminate hc|].
    destruct (cbn_ceq_get c1 c2 s2) as [b|] eqn:Ec; cbn [fst]; intros hb; right.
    - subst b. rewrite cbn_ceq_get_lookup in Ec.
      refine (eq_sym (hq c1 c2 e1 e2 true _ g1 hi1 g2 hi2)).
      unfold cbn_ceq_lookup in Ec |- *. rewrite hq2, hq1 in Ec. exact Ec.
    - exact hb.
  Qed.

  (** *** The delta memo

    The machine's oracle is [abstract_env_lookup X]; [cbn_lookup_declared] turns an answer of it
    into [declared_constant Σ] for any [Σ] the abstract environment stands for. *)

  Lemma cbn_lookup_declared (Σ : global_env_ext) (kn : kername) (cb : constant_body) :
    abstract_env_ext_rel X Σ ->
    abstract_env_lookup X kn = Some (ConstantDecl cb) ->
    declared_constant Σ kn cb.
  Proof.
    intros hΣ h. apply declared_constant_from_gen. unfold declared_constant_gen.
    rewrite (abstract_env_lookup_correct' X (Σ := Σ) kn hΣ). exact h.
  Qed.

  Definition cbn_inst_entry_ok (codes : PTree.t cbn_code_entry) (body : term)
    (p : Instance.t * cbn_cidx * term) : Prop :=
    let '(u, i, t) := p in
    t = cbn_inst_code u body
    /\ exists e : cbn_code_entry,
        PTree.get i codes = Some e /\ e.(cbn_ce_term) = body /\ e.(cbn_ce_inst) = u.

  Definition cbn_delta_ok (m : cbn_memo) : Prop :=
    forall (kn : kername) (d : cbn_delta_memo),
      cbn_dt_find kn m.(cbn_m_delta) = Some d ->
      match d with
      | CbnDAxiom =>
          exists cb : constant_body,
            abstract_env_lookup X kn = Some (ConstantDecl cb) /\ cb.(cst_body) = None
      | CbnDBody body insts =>
          (exists cb : constant_body,
              abstract_env_lookup X kn = Some (ConstantDecl cb)
              /\ cb.(cst_body) = Some body)
          /\ Forall (cbn_inst_entry_ok m.(cbn_m_codes) body) insts
      end.

  Lemma cbn_delta_ok_empty : cbn_delta_ok cbn_memo_empty.
  Proof.
    intros kn d h. cbn [cbn_memo_empty cbn_m_delta] in h. rewrite cbn_dt_find_nil in h.
    discriminate h.
  Qed.

  Lemma cbn_inst_entry_ok_mono (codes codes' : PTree.t cbn_code_entry) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) :
    (forall (i : cbn_key) (e : cbn_code_entry),
        PTree.get i codes = Some e -> PTree.get i codes' = Some e) ->
    Forall (cbn_inst_entry_ok codes body) insts ->
    Forall (cbn_inst_entry_ok codes' body) insts.
  Proof.
    intros hc hF. induction hF as [|p insts hp hFl IH]; constructor; [|exact IH].
    destruct p as [[u i] t]. destruct hp as [ht [e [he [h1 h2]]]].
    split; [exact ht|]. exists e. split; [exact (hc i e he)|]. split; assumption.
  Qed.

  (** [cbn_delta_ok] reads only the delta trie and the code table, and the code table only
    grows. *)
  Lemma cbn_delta_ok_mono (m m' : cbn_memo) :
    m'.(cbn_m_delta) = m.(cbn_m_delta) ->
    (forall (i : cbn_key) (e : cbn_code_entry),
        PTree.get i m.(cbn_m_codes) = Some e -> PTree.get i m'.(cbn_m_codes) = Some e) ->
    cbn_delta_ok m -> cbn_delta_ok m'.
  Proof.
    intros hd hc h kn d g. rewrite hd in g. specialize (h kn d g).
    destruct d as [|body insts]; [exact h|].
    destruct h as [hcb hF]. split; [exact hcb|].
    exact (cbn_inst_entry_ok_mono _ _ body insts hc hF).
  Qed.

  Lemma cbn_memo_add_entry_codes_mono (e : cbn_code_entry) (m : cbn_memo) :
    cbn_memo_fresh m ->
    forall (i : cbn_key) (e' : cbn_code_entry),
      PTree.get i m.(cbn_m_codes) = Some e' ->
      PTree.get i ((snd (cbn_memo_add_entry e m)).(cbn_m_codes)) = Some e'.
  Proof.
    intros hf i e' h. cbn [cbn_memo_add_entry snd cbn_m_codes].
    rewrite PTree.gso; [exact h|].
    apply cbn_idx_lt_neq. apply (cbn_memo_fresh_codes m i hf). rewrite h. discriminate.
  Qed.

  Lemma cbn_delta_ok_add_entry (e : cbn_code_entry) (m : cbn_memo) :
    cbn_memo_fresh m -> cbn_delta_ok m -> cbn_delta_ok (snd (cbn_memo_add_entry e m)).
  Proof.
    intros hf h.
    exact (cbn_delta_ok_mono m (snd (cbn_memo_add_entry e m)) eq_refl
             (cbn_memo_add_entry_codes_mono e m hf) h).
  Qed.

  (** *** [cbn_new_entry] *)

  Lemma cbn_new_entry_memo_eq (t : term) (u : Instance.t) (s : cbn_state) :
    ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo))
    = snd (cbn_memo_add_entry
             (cbn_mkEntry t u (cbn_wf_term_univs X_type X (cbn_inst_code u t))) (s.(cbn_st_memo))).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_fresh (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_memo_fresh
      ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).
  Proof. intros h. rewrite cbn_new_entry_memo_eq. now apply cbn_memo_fresh_add_entry. Qed.

  Lemma cbn_new_entry_once_ok (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_once_ok (s.(cbn_st_memo)) ->
    cbn_once_ok ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).
  Proof. intros hf h. rewrite cbn_new_entry_memo_eq. now apply cbn_once_ok_add_entry. Qed.

  Lemma cbn_new_entry_hash_ok (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_hash_ok (s.(cbn_st_memo)) ->
    cbn_hash_ok ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).
  Proof. intros hf h. rewrite cbn_new_entry_memo_eq. now apply cbn_hash_ok_add_entry. Qed.

  Lemma cbn_new_entry_ceq_ok (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_ceq_ok (s.(cbn_st_memo)) ->
    cbn_ceq_ok ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).
  Proof. intros hf h. rewrite cbn_new_entry_memo_eq. now apply cbn_ceq_ok_add_entry. Qed.

  Lemma cbn_new_entry_delta_ok (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_delta_ok (s.(cbn_st_memo)) ->
    cbn_delta_ok ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).
  Proof. intros hf h. rewrite cbn_new_entry_memo_eq. now apply cbn_delta_ok_add_entry. Qed.

  (** *** [cbn_delta_new]: one code entry per (constant, syntactic instance) *)

  Lemma cbn_delta_new_spec (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    cbn_delta_new X_type X kn ui body insts s
    = (fst (cbn_new_entry X_type X body ui s),
       cbn_set_memo
         (cbn_memo_set_delta
            (cbn_dt_add kn
               (CbnDBody body
                  ((ui, (fst (cbn_new_entry X_type X body ui s)).(cbn_c_entry),
                        (fst (cbn_new_entry X_type X body ui s)).(cbn_c_term))
                     :: insts))
               (((snd (cbn_new_entry X_type X body ui s)).(cbn_st_memo)).(cbn_m_delta)))
            ((snd (cbn_new_entry X_type X body ui s)).(cbn_st_memo)))
         (snd (cbn_new_entry X_type X body ui s))).
  Proof.
    unfold cbn_delta_new. destruct (cbn_new_entry X_type X body ui s). reflexivity.
  Qed.

  Lemma cbn_delta_new_fst (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    fst (cbn_delta_new X_type X kn ui body insts s)
    = fst (cbn_new_entry X_type X body ui s).
  Proof. rewrite cbn_delta_new_spec. reflexivity. Qed.

  Lemma cbn_delta_new_code (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    (fst (cbn_delta_new X_type X kn ui body insts s)).(cbn_c_term) = cbn_inst_code ui body
    /\ (fst (cbn_delta_new X_type X kn ui body insts s)).(cbn_c_path) = cbn_path_nil
    /\ (fst (cbn_delta_new X_type X kn ui body insts s)).(cbn_c_entry)
      = ((s.(cbn_st_memo)).(cbn_m_ncode)).
  Proof.
    rewrite cbn_delta_new_fst, cbn_new_entry_code. cbn [cbn_c_term cbn_c_path cbn_c_entry].
    repeat split.
  Qed.

  Lemma cbn_delta_new_codes (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo)).(cbn_m_codes))
    = (((snd (cbn_new_entry X_type X body ui s)).(cbn_st_memo)).(cbn_m_codes)).
  Proof. rewrite cbn_delta_new_spec. reflexivity. Qed.

  Lemma cbn_delta_new_entry (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    PTree.get ((fst (cbn_delta_new X_type X kn ui body insts s)).(cbn_c_entry))
      (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo)).(cbn_m_codes))
    = Some (cbn_mkEntry body ui
              (cbn_wf_term_univs X_type X (cbn_inst_code ui body))).
  Proof.
    rewrite cbn_delta_new_fst, cbn_delta_new_codes.
    exact (cbn_new_entry_in_table X_type X body ui s).
  Qed.

  Lemma cbn_delta_new_code_inv (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    cbn_code_inv (cbn_mkEntry body ui (cbn_wf_term_univs X_type X (cbn_inst_code ui body)))
      (fst (cbn_delta_new X_type X kn ui body insts s)).
  Proof.
    rewrite cbn_delta_new_fst. exact (cbn_new_entry_code_inv X_type X body ui s).
  Qed.

  Lemma cbn_delta_new_trie (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo)).(cbn_m_delta))
    = cbn_dt_add kn
        (CbnDBody body ((ui, ((s.(cbn_st_memo)).(cbn_m_ncode)), cbn_inst_code ui body) :: insts))
        ((s.(cbn_st_memo)).(cbn_m_delta)).
  Proof. rewrite cbn_delta_new_spec. reflexivity. Qed.

  Lemma cbn_delta_new_fresh (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) ->
    cbn_memo_fresh (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo))).
  Proof.
    intros h. rewrite cbn_delta_new_spec. cbn [snd]. rewrite cbn_set_memo_memo.
    apply cbn_memo_fresh_set_delta. now apply cbn_new_entry_fresh.
  Qed.

  Lemma cbn_delta_new_once_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_once_ok (s.(cbn_st_memo)) ->
    cbn_once_ok (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo))).
  Proof.
    intros hf h. rewrite cbn_delta_new_spec. cbn [snd]. rewrite cbn_set_memo_memo.
    refine (cbn_once_ok_fields _ _ _ _ (cbn_new_entry_once_ok body ui s hf h));
      reflexivity.
  Qed.

  Lemma cbn_delta_new_hash_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_hash_ok (s.(cbn_st_memo)) ->
    cbn_hash_ok (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo))).
  Proof.
    intros hf h. rewrite cbn_delta_new_spec. cbn [snd]. rewrite cbn_set_memo_memo.
    refine (cbn_hash_ok_fields _ _ _ _ (cbn_new_entry_hash_ok body ui s hf h));
      reflexivity.
  Qed.

  Lemma cbn_delta_new_ceq_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_ceq_ok (s.(cbn_st_memo)) ->
    cbn_ceq_ok (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo))).
  Proof.
    intros hf h. rewrite cbn_delta_new_spec. cbn [snd]. rewrite cbn_set_memo_memo.
    refine (cbn_ceq_ok_fields _ _ _ _ (cbn_new_entry_ceq_ok body ui s hf h));
      reflexivity.
  Qed.

  (** The new trie answers [CbnDBody body] for [kn], with the instance just added at the index
    just added, and keeps every other answer. *)
  Lemma cbn_delta_new_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) (cb : constant_body) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_delta_ok (s.(cbn_st_memo)) ->
    abstract_env_lookup X kn = Some (ConstantDecl cb) -> cb.(cst_body) = Some body ->
    Forall (cbn_inst_entry_ok ((s.(cbn_st_memo)).(cbn_m_codes)) body) insts ->
    cbn_delta_ok (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo))).
  Proof.
    intros hf hd hl hb hF.
    assert (hmono : forall (i : cbn_key) (e : cbn_code_entry),
               PTree.get i ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
               PTree.get i
                 (((snd (cbn_delta_new X_type X kn ui body insts s)).(cbn_st_memo)).(cbn_m_codes))
               = Some e).
    { intros i e h. rewrite cbn_delta_new_codes, cbn_new_entry_memo_eq.
      exact (cbn_memo_add_entry_codes_mono _ (s.(cbn_st_memo)) hf i e h). }
    intros kn' d g. rewrite cbn_delta_new_trie in g.
    destruct (eqb_specT kn' kn) as [->|hne].
    - rewrite cbn_dt_find_add_same in g. injection g as <-.
      split; [exists cb; split; assumption|].
      constructor.
      + split; [reflexivity|].
        exists (cbn_mkEntry body ui
                  (cbn_wf_term_univs X_type X (cbn_inst_code ui body))).
        split; [|split; reflexivity].
        pose proof (cbn_delta_new_entry kn ui body insts s) as hent.
        rewrite (proj2 (proj2 (cbn_delta_new_code kn ui body insts s))) in hent. exact hent.
      + exact (cbn_inst_entry_ok_mono _ _ body insts hmono hF).
    - rewrite (cbn_dt_find_add_other kn kn' _ _ hne) in g.
      pose proof (hd kn' d g) as hres.
      destruct d as [|body' insts']; [exact hres|].
      destruct hres as [hcb hF'].
      split; [exact hcb|]. exact (cbn_inst_entry_ok_mono _ _ body' insts' hmono hF').
  Qed.

  (** *** [cbn_find_inst] returns the body at that instance *)

  Lemma cbn_find_inst_sound (P : Instance.t * cbn_cidx * term -> Prop) (ui : Instance.t)
      (l : list (Instance.t * cbn_cidx * term)) (i : cbn_cidx) (t : term) :
    Forall P l -> cbn_find_inst ui l = Some (i, t) -> P (ui, i, t).
  Proof.
    induction 1 as [|p l hp hFl IH]; [intros hc; discriminate hc|].
    destruct p as [[u' i'] t']. cbn [cbn_find_inst].
    destruct (Instance.eqb ui u') eqn:E.
    - intros hc. injection hc as <- <-. apply cbn_instance_eqb_eq in E. subst u'. exact hp.
    - exact IH.
  Qed.

  (** *** The machine's [cbn_delta]

    [cbn_delta] returns [cbn_delta_new]'s result through a [let]-destructured pair;
    [cbn_let_COk_pair] reads the components without having to [destruct] the application and lose
    the name [cbn_delta_new] the per-field lemmas speak of. *)

  Lemma cbn_let_COk_pair {A : Type} (p : cbn_code * cbn_state) (g : cbn_code -> A)
      (r : A) (s' : cbn_state) :
    (let (c, s0) := p in CbnCOk (g c, s0)) = CbnCOk (r, s') -> r = g (fst p) /\ s' = snd p.
  Proof. destruct p as [c s0]. intros h. injection h as <- <-. split; reflexivity. Qed.

  (** The three outcomes of [cbn_delta]. The trie answers and the state is unchanged: [kn] is an
    axiom it knows, or a body it knows at [ui]. The body of [kn] is new at [ui]: it comes from
    the trie or from the environment, and [cbn_delta_new] adds it. [kn] is an axiom the trie did
    not know: the trie records it. *)
  Lemma cbn_delta_cases (kn : kername) (ui : Instance.t) (s : cbn_state) (r : option cbn_code)
      (s' : cbn_state) :
    cbn_delta X_type X kn ui s = CbnCOk (r, s') ->
    (s' = s
     /\ (r = None
         \/ exists body insts i t,
              cbn_dt_find kn ((s.(cbn_st_memo)).(cbn_m_delta)) = Some (CbnDBody body insts)
              /\ cbn_find_inst ui insts = Some (i, t) /\ r = Some (cbn_mkCode i cbn_path_nil t)))
    \/ (exists body insts,
          (cbn_dt_find kn ((s.(cbn_st_memo)).(cbn_m_delta)) = Some (CbnDBody body insts)
           \/ (cbn_dt_find kn ((s.(cbn_st_memo)).(cbn_m_delta)) = None /\ insts = []
               /\ exists cb, abstract_env_lookup X kn = Some (ConstantDecl cb)
                             /\ cb.(cst_body) = Some body))
          /\ r = Some (fst (cbn_delta_new X_type X kn ui body insts s))
          /\ s' = snd (cbn_delta_new X_type X kn ui body insts s))
    \/ (exists cb, abstract_env_lookup X kn = Some (ConstantDecl cb) /\ cb.(cst_body) = None
          /\ r = None
          /\ s' = cbn_set_memo (cbn_memo_set_delta
            (cbn_dt_add kn CbnDAxiom ((s.(cbn_st_memo)).(cbn_m_delta)))
                              (s.(cbn_st_memo))) s).
  Proof.
    unfold cbn_delta.
    destruct (cbn_dt_find kn ((s.(cbn_st_memo)).(cbn_m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [<- <-].
      left. split; [reflexivity|left; reflexivity].
    - destruct (cbn_find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [<- <-].
        left. split; [reflexivity|right]. exists body, insts, i, t.
        split; [reflexivity|]. split; [exact Ei|reflexivity].
      + intros hc.
        destruct (cbn_let_COk_pair (cbn_delta_new X_type X kn ui body insts s) Some r s' hc)
          as [-> ->].
        right; left. exists body, insts. split; [left; reflexivity|]. split; reflexivity.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (cbn_let_COk_pair (cbn_delta_new X_type X kn ui body [] s) Some r s' hc)
          as [-> ->].
        right; left. exists body, [].
        split; [right; split; [reflexivity|split; [reflexivity|]]|split; reflexivity].
        exists cb. split; [reflexivity|exact Eb].
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [<- <-].
        right; right. exists cb. split; [reflexivity|]. split; [exact Eb|].
        split; reflexivity.
  Qed.

  (** Where a new body comes from, in a sound trie: the environment's body of [kn], and
    instances the trie has right. *)
  Lemma cbn_delta_new_source (kn : kername) (m : cbn_memo) (body : term)
      (insts : list (Instance.t * cbn_cidx * term)) :
    cbn_delta_ok m ->
    (cbn_dt_find kn m.(cbn_m_delta) = Some (CbnDBody body insts)
     \/ (cbn_dt_find kn m.(cbn_m_delta) = None /\ insts = []
         /\ exists cb, abstract_env_lookup X kn = Some (ConstantDecl cb)
                       /\ cb.(cst_body) = Some body)) ->
    (exists cb, abstract_env_lookup X kn = Some (ConstantDecl cb) /\ cb.(cst_body) = Some body)
    /\ Forall (cbn_inst_entry_ok m.(cbn_m_codes) body) insts.
  Proof.
    intros hd [h|(_ & -> & hcb)]; [exact (hd kn _ h)|split; [exact hcb|constructor]].
  Qed.

  Lemma cbn_delta_fresh (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_delta X_type X kn ui s = CbnCOk (r, s') ->
    cbn_memo_fresh (s'.(cbn_st_memo)).
  Proof.
    intros hf hc.
    destruct (cbn_delta_cases kn ui s r s' hc)
      as [[-> _]|[(body & insts & _ & _ & ->)|(cb & _ & _ & _ & ->)]].
    - exact hf.
    - now apply cbn_delta_new_fresh.
    - rewrite cbn_set_memo_memo. now apply cbn_memo_fresh_set_delta.
  Qed.

  Lemma cbn_delta_memo_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_ok X_type X s -> cbn_delta X_type X kn ui s = CbnCOk (r, s') ->
      cbn_memo_ok X_type X s'.
  Proof.
    intros hm hc.
    destruct (cbn_delta_cases kn ui s r s' hc)
      as [[-> _]|[(body & insts & _ & _ & ->)|(cb & _ & _ & _ & ->)]].
    - exact hm.
    - refine (cbn_memo_ok_codes X_type X (snd (cbn_new_entry X_type X body ui s))
                _ _ (cbn_new_entry_memo_ok X_type X body ui s hm)).
      apply cbn_delta_new_codes.
    - refine (cbn_memo_ok_codes X_type X s _ _ hm). reflexivity.
  Qed.

  Lemma cbn_delta_ok_pres (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_delta_ok (s.(cbn_st_memo)) ->
    cbn_delta X_type X kn ui s = CbnCOk (r, s') -> cbn_delta_ok (s'.(cbn_st_memo)).
  Proof.
    intros hf hd hc.
    destruct (cbn_delta_cases kn ui s r s' hc)
      as [[-> _]|[(body & insts & hsrc & _ & ->)|(cb & hl & hb & _ & ->)]].
    - exact hd.
    - destruct (cbn_delta_new_source kn _ body insts hd hsrc) as [[cb [hl hb]] hF].
      exact (cbn_delta_new_ok kn ui body insts s cb hf hd hl hb hF).
    - rewrite cbn_set_memo_memo. intros kn' d g.
      rewrite cbn_memo_set_delta_delta in g. rewrite cbn_memo_set_delta_codes.
      destruct (eqb_specT kn' kn) as [->|hne].
      + rewrite cbn_dt_find_add_same in g. injection g as <-.
        exists cb. split; [exact hl|exact hb].
      + rewrite (cbn_dt_find_add_other kn kn' _ _ hne) in g.
        pose proof (hd kn' d g) as hres. destruct d as [|body' insts']; exact hres.
  Qed.

  Lemma cbn_delta_once_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_once_ok (s.(cbn_st_memo)) ->
    cbn_delta X_type X kn ui s = CbnCOk (r, s') -> cbn_once_ok (s'.(cbn_st_memo)).
  Proof.
    intros hf h hc.
    destruct (cbn_delta_cases kn ui s r s' hc)
      as [[-> _]|[(body & insts & _ & _ & ->)|(cb & _ & _ & _ & ->)]].
    - exact h.
    - now apply cbn_delta_new_once_ok.
    - rewrite cbn_set_memo_memo. refine (cbn_once_ok_fields _ _ _ _ h); reflexivity.
  Qed.

  Lemma cbn_delta_hash_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_hash_ok (s.(cbn_st_memo)) ->
    cbn_delta X_type X kn ui s = CbnCOk (r, s') -> cbn_hash_ok (s'.(cbn_st_memo)).
  Proof.
    intros hf h hc.
    destruct (cbn_delta_cases kn ui s r s' hc)
      as [[-> _]|[(body & insts & _ & _ & ->)|(cb & _ & _ & _ & ->)]].
    - exact h.
    - now apply cbn_delta_new_hash_ok.
    - rewrite cbn_set_memo_memo. refine (cbn_hash_ok_fields _ _ _ _ h); reflexivity.
  Qed.

  Lemma cbn_delta_ceq_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_ceq_ok (s.(cbn_st_memo)) ->
    cbn_delta X_type X kn ui s = CbnCOk (r, s') -> cbn_ceq_ok (s'.(cbn_st_memo)).
  Proof.
    intros hf h hc.
    destruct (cbn_delta_cases kn ui s r s' hc)
      as [[-> _]|[(body & insts & _ & _ & ->)|(cb & _ & _ & _ & ->)]].
    - exact h.
    - now apply cbn_delta_new_ceq_ok.
    - rewrite cbn_set_memo_memo. refine (cbn_ceq_ok_fields _ _ _ _ h); reflexivity.
  Qed.

  (** *** What the machine's [cbn_delta] answers

    This is the shape the evaluator needs: the code the fast path hands back for
    [tConst kn u] is the root code of a table entry whose term is the environment's body of
    [kn] at instance [u]. *)

  Lemma cbn_delta_body (Σ : global_env_ext) (kn : kername) (ui : Instance.t)
      (s s' : cbn_state) (c : cbn_code) :
    abstract_env_ext_rel X Σ ->
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_delta_ok (s.(cbn_st_memo)) ->
    cbn_delta X_type X kn ui s = CbnCOk (Some c, s') ->
    exists (cb : constant_body) (body : term) (e : cbn_code_entry),
      declared_constant Σ kn cb
      /\ cb.(cst_body) = Some body
      /\ c.(cbn_c_term) = cbn_inst_code ui body
      /\ c.(cbn_c_path) = cbn_path_nil
      /\ PTree.get c.(cbn_c_entry) ((s'.(cbn_st_memo)).(cbn_m_codes)) = Some e
      /\ e.(cbn_ce_term) = body
      /\ e.(cbn_ce_inst) = ui
      /\ cbn_code_inv e c.
  Proof.
    intros hΣ hf hd hc.
    destruct (cbn_delta_cases kn ui s (Some c) s' hc)
      as [[-> [hn|(body & insts & i & t & Ed & Ei & hr)]]
         |[(body & insts & hsrc & hr & ->)|(cb & _ & _ & hn & _)]].
    - discriminate hn.
    - injection hr as ->.
      destruct (hd kn _ Ed) as [[cb [hl hb]] hF].
      destruct (cbn_find_inst_sound _ ui insts i t hF Ei) as [ht [e [he [h3 h4]]]].
      exists cb, body, e.
      split; [exact (cbn_lookup_declared Σ kn cb hΣ hl)|].
      split; [exact hb|].
      split; [cbn [cbn_c_term]; exact ht|].
      split; [reflexivity|].
      split; [cbn [cbn_c_entry]; exact he|].
      split; [exact h3|]. split; [exact h4|].
      pose proof (cbn_code_inv_root e i) as hroot.
      rewrite h3, h4 in hroot. rewrite <- ht in hroot. exact hroot.
    - injection hr as ->.
      destruct (cbn_delta_new_source kn _ body insts hd hsrc) as [[cb [hl hb]] _].
      exists cb, body, (cbn_mkEntry body ui (cbn_wf_term_univs X_type X (cbn_inst_code ui body))).
      split; [exact (cbn_lookup_declared Σ kn cb hΣ hl)|].
      split; [exact hb|].
      destruct (cbn_delta_new_code kn ui body insts s) as [hct [hcp _]].
      split; [exact hct|]. split; [exact hcp|].
      split; [exact (cbn_delta_new_entry kn ui body insts s)|].
      split; [reflexivity|]. split; [reflexivity|].
      exact (cbn_delta_new_code_inv kn ui body insts s).
    - discriminate hn.
  Qed.

  Lemma cbn_lookup_env_of_abstract (Σ : global_env_ext) (kn : kername) (d : global_decl) :
    abstract_env_ext_rel X Σ -> abstract_env_lookup X kn = Some d ->
    lookup_env Σ kn = Some d.
  Proof.
    intros hΣ h. rewrite (abstract_env_lookup_correct' X (Σ := Σ) kn hΣ). exact h.
  Qed.

  (** The delta step of PCUIC, for *every* instance the machine can be given.

    The side condition is vacuous unless the instance is empty, and for the empty
    instance it says the constant's universe context has no variable. It is stated on
    [abstract_env_lookup X kn], which is the machine's own oracle, so a caller discharges
    it by the same lookup the machine makes. [wf Σ] is explicit because
    [abstract_env_ext_wf] only gives it squashed, and [red1] is in [Type]. *)
  Lemma cbn_delta_red1 (Σ : global_env_ext) (Γ : context) (kn : kername) (ui : Instance.t)
      (s s' : cbn_state) (c : cbn_code) :
    abstract_env_ext_rel X Σ -> wf Σ ->
    cbn_memo_fresh (s.(cbn_st_memo)) -> cbn_delta_ok (s.(cbn_st_memo)) ->
    cbn_delta X_type X kn ui s = CbnCOk (Some c, s') ->
    (forall cb : constant_body,
        abstract_env_lookup X kn = Some (ConstantDecl cb) ->
        ui = [] -> #|polymorphic_instance cb.(cst_universes)| = 0) ->
    red1 Σ Γ (tConst kn ui) c.(cbn_c_term).
  Proof.
    intros hΣ wfΣ hf hd he hmono.
    (* [red1] is in [Type]: take [cb] and [body] from the environment, and from
       [cbn_delta_cases] only that they are the ones [cbn_delta] used. *)
    assert (hsrc : exists cb body, abstract_env_lookup X kn = Some (ConstantDecl cb)
                     /\ cb.(cst_body) = Some body /\ c.(cbn_c_term) = cbn_inst_code ui body).
    { destruct (cbn_delta_cases kn ui s (Some c) s' he)
        as [[_ [hn|(body & insts & i & t & Ed & Ei & hr)]]
           |[(body & insts & hsrc & hr & _)|(cb & _ & _ & hn & _)]].
      - discriminate hn.
      - injection hr as ->.
        destruct (hd kn _ Ed) as [[cb [hl hb]] hF].
        destruct (cbn_find_inst_sound _ ui insts i t hF Ei) as [ht _].
        exists cb, body. split; [exact hl|]. split; [exact hb|exact ht].
      - injection hr as ->.
        destruct (cbn_delta_new_source kn _ body insts hd hsrc) as [[cb [hl hb]] _].
        exists cb, body. split; [exact hl|]. split; [exact hb|].
        exact (proj1 (cbn_delta_new_code kn ui body insts s)).
      - discriminate hn. }
    destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
      [|exfalso; destruct hsrc as (cb & _ & hl & _); discriminate hl
       |exfalso; destruct hsrc as (cb & _ & hl & _); discriminate hl].
    destruct (cb.(cst_body)) as [body|] eqn:Eb.
    - assert (hct : c.(cbn_c_term) = cbn_inst_code ui body).
      { destruct hsrc as (cb' & body' & hl & hb & hct). injection hl as <-.
        rewrite Eb in hb. injection hb as <-. exact hct. }
      rewrite hct.
      exact (cbn_inst_code_red1_gen Σ Γ kn ui cb body wfΣ
               (cbn_lookup_env_of_abstract Σ kn _ hΣ El) Eb (hmono cb eq_refl)).
    - exfalso. destruct hsrc as (cb' & body & hl & hb & _). injection hl as <-.
      rewrite Eb in hb. discriminate hb.
  Qed.

  (** ** The five invariants of one call, bundled *)

  Definition cbn_memo_inv (s : cbn_state) : Prop :=
    cbn_memo_fresh (s.(cbn_st_memo)) /\ cbn_once_ok (s.(cbn_st_memo)) /\
      cbn_hash_ok (s.(cbn_st_memo))
    /\ cbn_ceq_ok (s.(cbn_st_memo)) /\ cbn_delta_ok (s.(cbn_st_memo)).

  Lemma cbn_memo_inv_init : cbn_memo_inv cbn_init.
  Proof.
    unfold cbn_memo_inv, cbn_init. cbn [cbn_st_memo].
    split; [apply cbn_memo_fresh_empty|]. split; [apply cbn_once_ok_empty|].
    split; [apply cbn_hash_ok_empty|]. split; [apply cbn_ceq_ok_empty | apply cbn_delta_ok_empty].
  Qed.

  Lemma cbn_memo_inv_new_entry (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_inv s -> cbn_memo_inv (snd (cbn_new_entry X_type X t u s)).
  Proof.
    intros [hf [ho [hh [hq hd]]]]. unfold cbn_memo_inv.
    split; [now apply cbn_new_entry_fresh|]. split; [now apply cbn_new_entry_once_ok|].
    split; [now apply cbn_new_entry_hash_ok|].
    split; [now apply cbn_new_entry_ceq_ok | now apply cbn_new_entry_delta_ok].
  Qed.

  Lemma cbn_memo_inv_once_body (c : cbn_code) (e : cbn_code_entry) (s : cbn_state) :
    cbn_memo_inv s ->
    PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e -> cbn_code_inv e c ->
    cbn_memo_inv (snd (cbn_once_body c s)).
  Proof.
    intros [hf [ho [hh [hq hd]]]] g hi. unfold cbn_memo_inv.
    split; [exact (cbn_once_body_fresh c e s hf g)|].
    split; [exact (cbn_once_body_ok c e s ho g hi)|].
    split; [refine (cbn_hash_ok_fields _ _ _ _ hh);
            [exact (proj1 (proj2 (proj2 (proj2 (cbn_once_body_memo c s)))))
            | exact (proj1 (cbn_once_body_memo c s))]|].
    split; [refine (cbn_ceq_ok_fields _ _ _ _ hq);
            [exact (proj2 (proj2 (proj2 (proj2 (cbn_once_body_memo c s)))))
            | exact (proj1 (cbn_once_body_memo c s))]|].
    refine (cbn_delta_ok_mono _ _ _ _ hd).
    - exact (proj1 (proj2 (proj2 (cbn_once_body_memo c s)))).
    - intros i e' h. rewrite (proj1 (cbn_once_body_memo c s)). exact h.
  Qed.

  Lemma cbn_memo_inv_code_hash (c : cbn_code) (e : cbn_code_entry) (s : cbn_state) :
    cbn_memo_inv s ->
    PTree.get c.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e -> cbn_code_inv e c ->
    cbn_memo_inv (snd (cbn_code_hash c s)).
  Proof.
    intros [hf [ho [hh [hq hd]]]] g hi. unfold cbn_memo_inv.
    split; [exact (cbn_code_hash_fresh c e s hf g)|].
    split; [refine (cbn_once_ok_fields _ _ _ _ ho);
            [exact (proj1 (proj2 (proj2 (proj2 (cbn_code_hash_memo c s)))))
            | exact (proj1 (cbn_code_hash_memo c s))]|].
    split; [exact (cbn_code_hash_ok c e s hh g hi)|].
    split; [refine (cbn_ceq_ok_fields _ _ _ _ hq);
            [exact (proj2 (proj2 (proj2 (proj2 (cbn_code_hash_memo c s)))))
            | exact (proj1 (cbn_code_hash_memo c s))]|].
    refine (cbn_delta_ok_mono _ _ _ _ hd).
    - exact (proj1 (proj2 (proj2 (cbn_code_hash_memo c s)))).
    - intros i e' h. rewrite (proj1 (cbn_code_hash_memo c s)). exact h.
  Qed.

  Lemma cbn_memo_inv_ceq_set (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (s : cbn_state) :
    cbn_memo_inv s ->
    PTree.get c1.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e1 -> cbn_code_inv e1 c1 ->
    PTree.get c2.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e2 -> cbn_code_inv e2 c2 ->
    cbn_memo_inv (cbn_ceq_set c1 c2 (cbn_ceq_term c1.(cbn_c_term) c2.(cbn_c_term)) s).
  Proof.
    intros [hf [ho [hh [hq hd]]]] g1 hi1 g2 hi2. unfold cbn_memo_inv.
    set (b := cbn_ceq_term c1.(cbn_c_term) c2.(cbn_c_term)).
    split; [exact (cbn_ceq_set_fresh c1 c2 e1 e2 s b hf g1 g2)|].
    split; [exact (cbn_ceq_set_once_ok c1 c2 b s ho)|].
    split; [exact (cbn_ceq_set_hash_ok c1 c2 b s hh)|].
    split; [exact (cbn_ceq_set_ok c1 c2 e1 e2 s hq g1 hi1 g2 hi2)|].
    refine (cbn_delta_ok_mono _ _ _ _ hd).
    - exact (proj1 (proj2 (proj2 (cbn_ceq_set_memo c1 c2 b s)))).
    - intros i e' h. rewrite (proj1 (cbn_ceq_set_memo c1 c2 b s)). exact h.
  Qed.

  Lemma cbn_memo_inv_code_eq (c1 c2 : cbn_code) (e1 e2 : cbn_code_entry) (s : cbn_state) :
    cbn_memo_inv s ->
    PTree.get c1.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e1 -> cbn_code_inv e1 c1 ->
    PTree.get c2.(cbn_c_entry) ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e2 -> cbn_code_inv e2 c2 ->
    cbn_memo_inv (snd (cbn_code_eq X_type X c1 c2 s))
    /\ ((snd (cbn_code_eq X_type X c1 c2 s)).(cbn_st_memo)).(cbn_m_codes)
       = ((s.(cbn_st_memo)).(cbn_m_codes))
    /\ (snd (cbn_code_eq X_type X c1 c2 s)).(cbn_st_heap) = s.(cbn_st_heap)
    /\ (snd (cbn_code_eq X_type X c1 c2 s)).(cbn_st_next) = s.(cbn_st_next)
    /\ (snd (cbn_code_eq X_type X c1 c2 s)).(cbn_st_room) = s.(cbn_st_room)
    /\ (snd (cbn_code_eq X_type X c1 c2 s)).(cbn_st_steps) = s.(cbn_st_steps)
    /\ (snd (cbn_code_eq X_type X c1 c2 s)).(cbn_st_gam) = s.(cbn_st_gam).
  Proof.
    intros hm g1 hi1 g2 hi2. unfold cbn_code_eq.
    destruct (cbn_same_id c1 c2) eqn:Esid;
      [cbn [snd]; split; [exact hm|]; repeat split; reflexivity|].
    destruct (negb (cbn_entry_wf c1.(cbn_c_entry) s && cbn_entry_wf c2.(cbn_c_entry) s)) eqn:Ewf;
      [cbn [snd]; split; [exact hm|]; repeat split; reflexivity|].
    destruct (cbn_code_hash c1 s) as [v1 s1] eqn:E1.
    destruct (cbn_code_hash c2 s1) as [v2 s2] eqn:E2.
    assert (hs1 : s1 = snd (cbn_code_hash c1 s)) by (rewrite E1; reflexivity).
    assert (hm1 : cbn_memo_inv s1) by (rewrite hs1;
      exact (cbn_memo_inv_code_hash c1 e1 s hm g1 hi1)).
    assert (hc1 : ((s1.(cbn_st_memo)).(cbn_m_codes)) = ((s.(cbn_st_memo)).(cbn_m_codes)))
      by (rewrite hs1; apply (proj1 (cbn_code_hash_memo c1 s))).
    assert (hp1 : s1.(cbn_st_heap) = s.(cbn_st_heap) /\ s1.(cbn_st_next) = s.(cbn_st_next)
                  /\ s1.(cbn_st_room) = s.(cbn_st_room) /\ s1.(cbn_st_steps) = s.(cbn_st_steps)
                  /\ s1.(cbn_st_gam) = s.(cbn_st_gam))
      by (rewrite hs1; exact (cbn_code_hash_state c1 s)).
    rewrite <- hc1 in g1, g2.
    assert (hs2 : s2 = snd (cbn_code_hash c2 s1)) by (rewrite E2; reflexivity).
    assert (hm2 : cbn_memo_inv s2)
      by (rewrite hs2; exact (cbn_memo_inv_code_hash c2 e2 s1 hm1 g2 hi2)).
    assert (hc2 : ((s2.(cbn_st_memo)).(cbn_m_codes)) = ((s1.(cbn_st_memo)).(cbn_m_codes)))
      by (rewrite hs2; apply (proj1 (cbn_code_hash_memo c2 s1))).
    assert (hp2 : s2.(cbn_st_heap) = s1.(cbn_st_heap) /\ s2.(cbn_st_next) = s1.(cbn_st_next)
                  /\ s2.(cbn_st_room) = s1.(cbn_st_room) /\ s2.(cbn_st_steps) = s1.(cbn_st_steps)
                  /\ s2.(cbn_st_gam) = s1.(cbn_st_gam))
      by (rewrite hs2; exact (cbn_code_hash_state c2 s1)).
    rewrite <- hc2 in g1, g2.
    destruct hp1 as [p11 [p12 [p13 [p14 p15]]]].
    destruct hp2 as [p21 [p22 [p23 [p24 p25]]]].
    destruct (negb (N.eqb v1 v2)) eqn:Eh; cbn [snd].
    { split; [exact hm2|]; repeat split; congruence. }
    destruct (cbn_ceq_get c1 c2 s2) as [b|] eqn:Ec; cbn [snd].
    { split; [exact hm2|]; repeat split; congruence. }
    split; [exact (cbn_memo_inv_ceq_set c1 c2 e1 e2 s2 hm2 g1 hi1 g2 hi2)|].
    split; [rewrite (proj1 (cbn_ceq_set_memo c1 c2 _ s2)); congruence|].
    split; [rewrite (proj1 (cbn_ceq_set_state c1 c2 _ s2)); congruence|].
    split; [rewrite (proj1 (proj2 (cbn_ceq_set_state c1 c2 _ s2))); congruence|].
    split; [rewrite (proj1 (proj2 (proj2 (cbn_ceq_set_state c1 c2 _ s2)))); congruence|].
    split; [rewrite (proj1 (proj2 (proj2 (proj2 (cbn_ceq_set_state c1 c2 _ s2))))); congruence|].
    rewrite (proj2 (proj2 (proj2 (proj2 (cbn_ceq_set_state c1 c2 _ s2))))); congruence.
  Qed.

  Lemma cbn_memo_inv_delta (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option cbn_code) (s' : cbn_state) :
    cbn_memo_inv s -> cbn_delta X_type X kn ui s = CbnCOk (r, s') -> cbn_memo_inv s'.
  Proof.
    intros [hf [ho [hh [hq hd]]]] he. unfold cbn_memo_inv.
    split; [exact (cbn_delta_fresh kn ui s r s' hf he)|].
    split; [exact (cbn_delta_once_ok kn ui s r s' hf ho he)|].
    split; [exact (cbn_delta_hash_ok kn ui s r s' hf hh he)|].
    split; [exact (cbn_delta_ceq_ok kn ui s r s' hf hq he)
           | exact (cbn_delta_ok_pres kn ui s r s' hf hd he)].
  Qed.

End Memo.
