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

Local Notation key := String2pos.positive.
Local Notation cidx := String2pos.positive.

(** * The memo tables of one [cbn_conv] call

  [PCUICCallByNeed]'s [cbn_memo] holds five maps, all of them empty at the start of a call:
  the code table [m_codes] with its next index [m_ncode] (whose invariant [memo_ok] is
  [PCUICCallByNeedSoundCtx]'s), the delta trie [m_delta], and the three caches [m_once],
  [m_hash] and [m_ceq], keyed by code identifier. This file says what each one means.

  - **The trie is a map.** [dt_find] reads the association list at the node the bits of the
    constant's identifier lead to, and [dt_add] writes there. [dt_find_add_same],
    [dt_find_add_other] and [dt_find_nil] are the three map laws. They rest on the
    injectivity of the bit path of an identifier ([sbits_inj], through [Byte.to_bits]) and
    on [mp_find]/[mp_set] being an association list under [modpath_eqb], whose soundness
    is [modpath_eqb_eq].
  - **The delta entry means what it says.** [delta_ok] says that every [kn] the trie answers
    for either carries [DAxiom], and then the environment's declaration for [kn] is a
    constant without a body, or carries [DBody body insts], and then the environment's
    declaration for [kn] has that body and every [(u, i, t')] of [insts] records
    [t' = inst_code u body] at a code-table index [i] whose entry is [body] at instance [u].
    [delta_body] is the conclusion the evaluator needs: when the machine's [delta] answers
    for [tConst kn u], the code it returns is the root code of a table entry whose term is
    [inst_code u body] for the body [body] the environment gives [kn]; [delta_red1] turns
    that into PCUIC's delta step, for *every* instance, under [wf Σ].

    For a non-empty instance [inst_code] *is* [subst_instance], so [inst_code_red1_gen]
    needs nothing. For [u = []] the machine's [inst_code] returns the body unchanged
    where [red_delta] produces [subst_instance [] body]; the two agree exactly when the
    body carries no universe variable, which [declared_constant_body_closedu] gets from
    [wf Σ] by MetaRocq's [on_declared_constant], [typing_wf_universes],
    [wf_universes_closedu] (with [weaken_lookup_on_global_env'] for its [on_udecl_prop]
    side condition) and [closedu_subst_instance]. That needs [kn]'s universe context to
    have no variable, which is the one premise of [delta_red1] beyond the evaluator's.
    The evaluator discharges it with [PCUICCallByNeedSoundHook.inst_okb_nil].
  - **The caches.** [hash_ok]: the value stored for a code identifier is [thash] of that
    code's term. [once_ok]: the bit stored is [Nat.leb (occ 0 t) 1] for that code's term
    [t]. [ceq_ok]: the bit stored for a *pair* of identifiers is the value of
    [eqb_term_upto_univ] at [Conv] on the two terms.

    The invariant of [m_ceq] is *not* "true means the two codes have the same term".
    [PCUICCallByNeed.code_eq] answers [true] in two ways: [same_id c1 c2], where the terms
    are indeed equal ([same_id_sound_table]); or the cached bit
    [eqb_term_upto_univ (abstract_env_compare_universe X) … Conv c1.(c_term) c2.(c_term)],
    which is equality *up to universes* and holds of terms that differ (two sorts at
    convertible universes, two instances of a polymorphic constant). So the strongest sound
    statement is the disjunction [code_eq_sound] proves: equal terms, or [eqb_term_upto_univ]
    at [Conv] says [true]. [PCUICCallByNeedSoundConv.code_eq_sound_wf] consumes it. A
    [false] answer says nothing, and no lemma here states anything about it.
  - **The code table grows.** [memo_add_entry] writes at [m_ncode] and touches nothing else,
    so an index already in the table keeps its entry ([memo_add_entry_codes_mono]). That new
    index is fresh in *every* map of the memo, which is [memo_fresh] (through [key_val], the
    reading of a code index as a [positive], under which [key_succ] is [Pos.succ]). Without
    it the three cache invariants would not survive an added entry: a stale pair
    ([m_ncode], path) in [m_hash] would be read against the new entry. With it, [delta_ok],
    [once_ok], [hash_ok], [ceq_ok] and [memo_fresh] — bundled as [memo_inv] — all survive
    [memo_add_entry], [new_entry], [once_body], [code_hash], [code_eq] and [delta], and each
    setter keeps the other five fields.

  Nothing here is about the heap: every operation of this file leaves [st_heap], [st_next],
  [st_room], [st_steps] and [st_gam] alone, so [state_ok] crosses them without an
  argument. *)

(** ** Equality of names by identifier first

  [modpath_eqb] and its companions compare the identifier before the module path, where
  MetaRocq's [Kername.compare] compares the path first. A [true] answer means equality. *)

Lemma string_eqb_spec (x y : String.t) : String.eqb x y = true <-> x = y.
Proof.
  split.
  - intros h. exact (@eqb_eq String.t _ x y h).
  - intros <-. exact (@eqb_refl String.t _ x).
Qed.

Lemma dirpath_eqb_refl (d : dirpath) : dirpath_eqb d d = true.
Proof.
  induction d as [|x d IH]; cbn [dirpath_eqb]; [reflexivity|].
  apply Bool.andb_true_iff. split; [apply string_eqb_spec; reflexivity | exact IH].
Qed.

Lemma dirpath_eqb_eq (d1 d2 : dirpath) : dirpath_eqb d1 d2 = true -> d1 = d2.
Proof.
  revert d2. induction d1 as [|x d1 IH]; intros [|y d2] h; cbn [dirpath_eqb] in h;
    try discriminate h; [reflexivity|].
  apply Bool.andb_true_iff in h as [h1 h2].
  apply string_eqb_spec in h1. apply IH in h2. subst. reflexivity.
Qed.

Lemma modpath_eqb_refl (m : modpath) : modpath_eqb m m = true.
Proof.
  induction m as [d|d i k|m IH i]; cbn [modpath_eqb].
  - apply dirpath_eqb_refl.
  - apply Bool.andb_true_iff. split; [apply Bool.andb_true_iff; split|].
    + apply string_eqb_spec; reflexivity.
    + apply PeanoNat.Nat.eqb_eq; reflexivity.
    + apply dirpath_eqb_refl.
  - apply Bool.andb_true_iff. split; [apply string_eqb_spec; reflexivity | exact IH].
Qed.

Lemma modpath_eqb_eq (m1 m2 : modpath) : modpath_eqb m1 m2 = true -> m1 = m2.
Proof.
  revert m2. induction m1 as [d1|d1 i1 k1|m1 IH i1]; intros [d2|d2 i2 k2|m2 i2] h;
    cbn [modpath_eqb] in h; try discriminate h.
  - apply dirpath_eqb_eq in h. subst. reflexivity.
  - apply Bool.andb_true_iff in h as [h1 h2]. apply Bool.andb_true_iff in h1 as [h3 h4].
    apply string_eqb_spec in h3. apply PeanoNat.Nat.eqb_eq in h4.
    apply dirpath_eqb_eq in h2. subst. reflexivity.
  - apply Bool.andb_true_iff in h as [h1 h2]. apply string_eqb_spec in h1.
    apply IH in h2. subst. reflexivity.
Qed.

Lemma modpath_eqb_false (m1 m2 : modpath) : m1 <> m2 -> modpath_eqb m1 m2 = false.
Proof.
  intros hne. destruct (modpath_eqb m1 m2) eqn:E; [|reflexivity].
  apply modpath_eqb_eq in E. contradiction.
Qed.

Lemma inductive_eqb_eq (i1 i2 : inductive) : inductive_eqb i1 i2 = true -> i1 = i2.
Proof.
  destruct i1 as [[mp1 id1] n1], i2 as [[mp2 id2] n2]. unfold inductive_eqb. cbn.
  intros h. apply Bool.andb_true_iff in h as [h1 h2].
  apply Bool.andb_true_iff in h1 as [h3 h4].
  apply PeanoNat.Nat.eqb_eq in h3. apply string_eqb_spec in h4.
  apply modpath_eqb_eq in h2. subst. reflexivity.
Qed.

Lemma case_info_eqb_eq (c1 c2 : case_info) : case_info_eqb c1 c2 = true -> c1 = c2.
Proof.
  destruct c1 as [i1 n1 r1], c2 as [i2 n2 r2]. unfold case_info_eqb. cbn.
  intros h. apply Bool.andb_true_iff in h as [h1 h2].
  apply Bool.andb_true_iff in h1 as [h3 h4].
  apply inductive_eqb_eq in h3. apply PeanoNat.Nat.eqb_eq in h4.
  apply eqb_eq in h2. subst. reflexivity.
Qed.

Lemma instance_eqb_eq (u v : Instance.t) : Instance.eqb u v = true -> u = v.
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

Definition dt_here (t : dtrie) : list (modpath * delta_memo) :=
  match t with DTNil => [] | DTNode h _ _ => h end.

Lemma dt_find_here (kn : kername) (t : dtrie) :
  dt_find kn t = mp_find kn.1 (dt_here (dt_walk kn.2 t)).
Proof. unfold dt_find. destruct (dt_walk kn.2 t); reflexivity. Qed.

(** *** The association list at a node *)

Lemma mp_find_set_same (mp : modpath) (d : delta_memo)
    (l : list (modpath * delta_memo)) :
  mp_find mp (mp_set mp d l) = Some d.
Proof.
  induction l as [|[mp' d'] l IH]; cbn [mp_set mp_find].
  - now rewrite modpath_eqb_refl.
  - destruct (modpath_eqb mp mp') eqn:E; cbn [mp_find].
    + now rewrite modpath_eqb_refl.
    + rewrite E. exact IH.
Qed.

Lemma mp_find_set_other (mp mp' : modpath) (d : delta_memo)
    (l : list (modpath * delta_memo)) :
  mp' <> mp -> mp_find mp' (mp_set mp d l) = mp_find mp' l.
Proof.
  intros hne. induction l as [|[mp0 d0] l IH]; cbn [mp_set mp_find].
  - now rewrite (modpath_eqb_false mp' mp hne).
  - destruct (modpath_eqb mp mp0) eqn:E; cbn [mp_find].
    + apply modpath_eqb_eq in E. subst mp0.
      now rewrite (modpath_eqb_false mp' mp hne).
    + destruct (modpath_eqb mp' mp0); [reflexivity | exact IH].
Qed.

(** *** Walking and updating by a list of bits *)

Definition dt_walkb (l : list bool) (t : dtrie) : dtrie :=
  fold_left (fun (u : dtrie) (b : bool) => dt_child b u) l t.

Fixpoint dt_updb (l : list bool) (f : dtrie -> dtrie) (t : dtrie) : dtrie :=
  match l with
  | [] => f t
  | b :: l => dt_upd_child b (dt_updb l f) t
  end.

Lemma dt_walkb_cons (b : bool) (l : list bool) (t : dtrie) :
  dt_walkb (b :: l) t = dt_walkb l (dt_child b t).
Proof. reflexivity. Qed.

Lemma dt_walkb_app (l1 l2 : list bool) (t : dtrie) :
  dt_walkb (l1 ++ l2) t = dt_walkb l2 (dt_walkb l1 t).
Proof. unfold dt_walkb. apply fold_left_app. Qed.

Lemma dt_upd_child_ext (b : bool) (f g : dtrie -> dtrie) (t : dtrie) :
  (forall u : dtrie, f u = g u) -> dt_upd_child b f t = dt_upd_child b g t.
Proof. intros h. unfold dt_upd_child. destruct t, b; now rewrite h. Qed.

Lemma dt_updb_ext (l : list bool) (f g : dtrie -> dtrie) (t : dtrie) :
  (forall u : dtrie, f u = g u) -> dt_updb l f t = dt_updb l g t.
Proof.
  intros h. revert t. induction l as [|b l IH]; intros t; cbn [dt_updb]; [apply h|].
  apply dt_upd_child_ext. intros u. apply IH.
Qed.

Lemma dt_updb_app (l1 l2 : list bool) (f : dtrie -> dtrie) (t : dtrie) :
  dt_updb (l1 ++ l2) f t = dt_updb l1 (dt_updb l2 f) t.
Proof.
  revert t. induction l1 as [|b l1 IH]; intros t; cbn [dt_updb app]; [reflexivity|].
  apply dt_upd_child_ext. intros u. apply IH.
Qed.

Lemma dt_child_upd_same (b : bool) (f : dtrie -> dtrie) (t : dtrie) :
  dt_child b (dt_upd_child b f t) = f (dt_child b t).
Proof. unfold dt_upd_child, dt_child. destruct t, b; reflexivity. Qed.

Lemma dt_child_upd_other (b b' : bool) (f : dtrie -> dtrie) (t : dtrie) :
  b <> b' -> dt_child b (dt_upd_child b' f t) = dt_child b t.
Proof.
  intros hne. unfold dt_upd_child, dt_child. destruct t, b, b';
    first [ reflexivity | now destruct hne ].
Qed.

Lemma dt_here_upd_child (b : bool) (f : dtrie -> dtrie) (t : dtrie) :
  dt_here (dt_upd_child b f t) = dt_here t.
Proof. unfold dt_upd_child, dt_here. destruct t, b; reflexivity. Qed.

Lemma dt_walkb_updb_same (l : list bool) (f : dtrie -> dtrie) (t : dtrie) :
  dt_walkb l (dt_updb l f t) = f (dt_walkb l t).
Proof.
  revert t. induction l as [|b l IH]; intros t; [reflexivity|].
  cbn [dt_updb]. rewrite !dt_walkb_cons, dt_child_upd_same. apply IH.
Qed.

(** A function that leaves every child alone is invisible below the node it changes. *)
Lemma dt_walkb_child_pres (l : list bool) (f : dtrie -> dtrie) (t : dtrie) :
  (forall (b : bool) (u : dtrie), dt_child b (f u) = dt_child b u) ->
  l <> [] -> dt_walkb l (f t) = dt_walkb l t.
Proof.
  intros hf. destruct l as [|b l]; [intros h; now destruct h|].
  intros _. rewrite !dt_walkb_cons, hf. reflexivity.
Qed.

Lemma dt_here_walkb_updb_other (l l' : list bool) (f : dtrie -> dtrie) (t : dtrie) :
  (forall (b : bool) (u : dtrie), dt_child b (f u) = dt_child b u) ->
  l <> l' ->
  dt_here (dt_walkb l' (dt_updb l f t)) = dt_here (dt_walkb l' t).
Proof.
  intros hf. revert l' t. induction l as [|b l IH]; intros l' t hne.
  - cbn [dt_updb]. rewrite (dt_walkb_child_pres l' f t hf); [reflexivity|].
    intros ->. now destruct hne.
  - destruct l' as [|b' l'].
    + cbn [dt_updb]. unfold dt_walkb; cbn [fold_left]. apply dt_here_upd_child.
    + cbn [dt_updb]. rewrite !dt_walkb_cons.
      destruct (Bool.bool_dec b' b) as [->|hb].
      * rewrite dt_child_upd_same. apply IH. intros ->. now destruct hne.
      * rewrite (dt_child_upd_other b' b _ t hb). reflexivity.
Qed.

(** *** The bits of an identifier *)

Definition bits_of_byte (x : Byte.byte) : list bool :=
  let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := Byte.to_bits x in
  [b0; b1; b2; b3; b4; b5; b6; b7].

Fixpoint sbits (s : String.t) : list bool :=
  match s with
  | String.EmptyString => []
  | String.String x s => bits_of_byte x ++ sbits s
  end.

Lemma dt_byte_walkb (x : Byte.byte) (t : dtrie) :
  dt_byte x t = dt_walkb (bits_of_byte x) t.
Proof.
  unfold dt_byte, bits_of_byte.
  destruct (Byte.to_bits x) as [b0 [b1 [b2 [b3 [b4 [b5 [b6 b7]]]]]]]. reflexivity.
Qed.

Lemma dt_upd_byte_updb (x : Byte.byte) (f : dtrie -> dtrie) (t : dtrie) :
  dt_upd_byte x f t = dt_updb (bits_of_byte x) f t.
Proof.
  unfold dt_upd_byte, bits_of_byte.
  destruct (Byte.to_bits x) as [b0 [b1 [b2 [b3 [b4 [b5 [b6 b7]]]]]]]. reflexivity.
Qed.

Lemma dt_walk_bits (s : String.t) (t : dtrie) : dt_walk s t = dt_walkb (sbits s) t.
Proof.
  revert t. induction s as [|x s IH]; intros t; cbn [dt_walk sbits]; [reflexivity|].
  rewrite dt_walkb_app, <- dt_byte_walkb. apply IH.
Qed.

Lemma dt_upd_bits (s : String.t) (f : dtrie -> dtrie) (t : dtrie) :
  dt_upd s f t = dt_updb (sbits s) f t.
Proof.
  revert t. induction s as [|x s IH]; intros t; cbn [dt_upd sbits]; [reflexivity|].
  rewrite dt_updb_app, dt_upd_byte_updb. apply dt_updb_ext. intros u. apply IH.
Qed.

Lemma bits_of_byte_length (x : Byte.byte) : #|bits_of_byte x| = 8.
Proof.
  unfold bits_of_byte.
  destruct (Byte.to_bits x) as [b0 [b1 [b2 [b3 [b4 [b5 [b6 b7]]]]]]]. reflexivity.
Qed.

Lemma bits_tuple_inj
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

Lemma bits_of_byte_inj (x y : Byte.byte) : bits_of_byte x = bits_of_byte y -> x = y.
Proof.
  unfold bits_of_byte. intros h. apply bits_tuple_inj in h.
  rewrite <- (Byte.of_bits_to_bits x), <- (Byte.of_bits_to_bits y), h. reflexivity.
Qed.

Lemma app_eq_len {A : Type} (l1 l2 r1 r2 : list A) :
  #|l1| = #|l2| -> l1 ++ r1 = l2 ++ r2 -> l1 = l2 /\ r1 = r2.
Proof.
  revert l2. induction l1 as [|a l1 IH]; intros [|b l2] hl h; cbn in hl, h;
    try discriminate hl.
  - split; [reflexivity | exact h].
  - injection h as <- h. injection hl as hl.
    destruct (IH l2 hl h) as [<- <-]. split; reflexivity.
Qed.

Lemma sbits_inj (s s' : String.t) : sbits s = sbits s' -> s = s'.
Proof.
  revert s'. induction s as [|x s IH]; intros [|y s'] h; cbn [sbits] in h.
  - reflexivity.
  - exfalso. assert (hl := f_equal (fun l : list bool => #|l|) h).
    rewrite length_app_cbn, bits_of_byte_length in hl. cbn in hl. lia.
  - exfalso. assert (hl := f_equal (fun l : list bool => #|l|) h).
    rewrite length_app_cbn, bits_of_byte_length in hl. cbn in hl. lia.
  - assert (hlen : #|bits_of_byte x| = #|bits_of_byte y|)
      by (rewrite !bits_of_byte_length; reflexivity).
    destruct (app_eq_len _ _ _ _ hlen h) as [hb hs].
    rewrite (bits_of_byte_inj x y hb), (IH s' hs). reflexivity.
Qed.

(** *** The three map laws *)

Definition dt_ins (mp : modpath) (d : delta_memo) (t : dtrie) : dtrie :=
  match t with
  | DTNil => DTNode [(mp, d)] DTNil DTNil
  | DTNode h z o => DTNode (mp_set mp d h) z o
  end.

Lemma dt_add_ins (kn : kername) (d : delta_memo) (t : dtrie) :
  dt_add kn d t = dt_upd kn.2 (dt_ins kn.1 d) t.
Proof. reflexivity. Qed.

Lemma dt_ins_child (mp : modpath) (d : delta_memo) (b : bool) (t : dtrie) :
  dt_child b (dt_ins mp d t) = dt_child b t.
Proof. unfold dt_ins, dt_child. destruct t, b; reflexivity. Qed.

Lemma dt_ins_here (mp : modpath) (d : delta_memo) (t : dtrie) :
  dt_here (dt_ins mp d t) = mp_set mp d (dt_here t).
Proof. unfold dt_ins, dt_here. destruct t; reflexivity. Qed.

Lemma dt_walkb_nil (l : list bool) : dt_walkb l DTNil = DTNil.
Proof.
  induction l as [|b l IH]; [reflexivity|]. rewrite dt_walkb_cons. exact IH.
Qed.

Lemma dt_find_nil (kn : kername) : dt_find kn DTNil = None.
Proof.
  rewrite dt_find_here, dt_walk_bits, dt_walkb_nil. reflexivity.
Qed.

Lemma dt_find_add_same (kn : kername) (d : delta_memo) (t : dtrie) :
  dt_find kn (dt_add kn d t) = Some d.
Proof.
  rewrite dt_find_here, dt_add_ins, dt_walk_bits, dt_upd_bits, dt_walkb_updb_same,
    dt_ins_here.
  apply mp_find_set_same.
Qed.

Lemma dt_find_add_other (kn kn' : kername) (d : delta_memo) (t : dtrie) :
  kn' <> kn -> dt_find kn' (dt_add kn d t) = dt_find kn' t.
Proof.
  intros hne. rewrite !dt_find_here, dt_add_ins, !dt_walk_bits, dt_upd_bits.
  destruct (String.eqb kn'.2 kn.2) eqn:Es.
  - apply string_eqb_spec in Es. rewrite Es, dt_walkb_updb_same, dt_ins_here.
    apply mp_find_set_other. intros hmp. apply hne.
    destruct kn as [mp id], kn' as [mp' id']; cbn in Es, hmp. now subst.
  - f_equal. apply dt_here_walkb_updb_other.
    + intros b u. apply dt_ins_child.
    + intros heq. apply sbits_inj in heq.
      rewrite <- heq, (proj2 (string_eqb_spec kn.2 kn.2) eq_refl) in Es. discriminate Es.
Qed.

(** ** The memo's fields

  Each setter writes one field and copies the other five; [memo_add_entry] writes [m_codes]
  and [m_ncode] and copies the other four. *)

Lemma set_memo_memo (m : cbn_memo) (s : cbn_state) : (set_memo m s).(st_memo) = m.
Proof. reflexivity. Qed.

Lemma memo_set_delta_delta (t : dtrie) (m : cbn_memo) :
  (memo_set_delta t m).(m_delta) = t.
Proof. reflexivity. Qed.

Lemma memo_set_delta_codes (t : dtrie) (m : cbn_memo) :
  (memo_set_delta t m).(m_codes) = m.(m_codes).
Proof. reflexivity. Qed.

(** ** Two-level maps *)

Lemma get2_empty {A : Type} (k1 k2 : key) : get2 k1 k2 (PTree.empty (PTree.t A)) = None.
Proof. unfold get2. now rewrite PTree.gempty. Qed.

Lemma get2_some_outer {A : Type} (k1 k2 : key) (m : PTree.t (PTree.t A)) (x : A) :
  get2 k1 k2 m = Some x -> PTree.get k1 m <> None.
Proof.
  unfold get2. destruct (PTree.get k1 m) as [m2|]; intros h; [discriminate | discriminate h].
Qed.

Lemma get_set2_outer {A : Type} (k1 k2 j : key) (x : A) (m : PTree.t (PTree.t A)) :
  PTree.get j (set2 k1 k2 x m) <> None -> j = k1 \/ PTree.get j m <> None.
Proof.
  unfold set2; cbv zeta. intros h.
  destruct (key_eqb j k1) eqn:E.
  - left. now apply key_eqb_spec in E.
  - right. rewrite PTree.gso in h; [exact h | exact (key_neq_of_eqb j k1 E)].
Qed.

(** ** Code indices as numbers, and the freshness of [m_ncode]

  [key_succ] is [Pos.succ] under [key_val], so a code index is a number and the index
  [memo_add_entry] hands out is above every index the memo's maps hold. *)

Fixpoint key_val (p : key) : positive :=
  match p with
  | String2pos.xH => xH
  | String2pos.xO q => xO (key_val q)
  | String2pos.xI q => xI (key_val q)
  end.

Lemma key_val_succ (p : key) : key_val (key_succ p) = Pos.succ (key_val p).
Proof.
  induction p as [p IH|p IH|]; cbn [key_succ key_val]; [now rewrite IH|reflexivity|reflexivity].
Qed.

Definition idx_lt (i j : key) : Prop := (key_val i < key_val j)%positive.

Lemma idx_lt_neq (i j : key) : idx_lt i j -> i <> j.
Proof. intros h ->. exact (Pos.lt_irrefl _ h). Qed.

Lemma idx_lt_succ (i : key) : idx_lt i (key_succ i).
Proof. unfold idx_lt. rewrite key_val_succ. apply Pos.lt_succ_diag_r. Qed.

Lemma idx_lt_up (i j : key) : idx_lt i j -> idx_lt i (key_succ j).
Proof.
  unfold idx_lt. rewrite key_val_succ. intros h.
  exact (Pos.lt_trans _ _ _ h (Pos.lt_succ_diag_r _)).
Qed.

(** [m_hash] and [m_once] are keyed by (index, path); [m_ceq] by
  (index, path, index, path), so indices sit at its first and third level. *)
Definition memo_fresh (m : cbn_memo) : Prop :=
  (forall i : key, PTree.get i m.(m_codes) <> None -> idx_lt i m.(m_ncode))
  /\ (forall i : key, PTree.get i m.(m_hash) <> None -> idx_lt i m.(m_ncode))
  /\ (forall i : key, PTree.get i m.(m_once) <> None -> idx_lt i m.(m_ncode))
  /\ (forall (i1 p1 : key) (r : PTree.t (PTree.t bool)),
         get2 i1 p1 m.(m_ceq) = Some r ->
         idx_lt i1 m.(m_ncode)
         /\ forall i2 : key, PTree.get i2 r <> None -> idx_lt i2 m.(m_ncode)).

Lemma memo_fresh_empty : memo_fresh memo_empty.
Proof.
  unfold memo_empty, memo_fresh. cbn [m_codes m_hash m_once m_ceq m_ncode].
  split; [|split; [|split]].
  - intros i. rewrite PTree.gempty. intros h; now destruct h.
  - intros i. rewrite PTree.gempty. intros h; now destruct h.
  - intros i. rewrite PTree.gempty. intros h; now destruct h.
  - intros i1 p1 r h. rewrite get2_empty in h. discriminate h.
Qed.

Lemma memo_fresh_codes (m : cbn_memo) (i : key) :
  memo_fresh m -> PTree.get i m.(m_codes) <> None -> idx_lt i m.(m_ncode).
Proof. intros [h _]. exact (h i). Qed.

Lemma memo_fresh_add_entry (e : code_entry) (m : cbn_memo) :
  memo_fresh m -> memo_fresh (snd (memo_add_entry e m)).
Proof.
  intros [hc [hh [ho hq]]]. unfold memo_add_entry, memo_fresh.
  cbn [snd m_codes m_hash m_once m_ceq m_ncode].
  split; [|split; [|split]].
  - intros i hi. destruct (key_eqb i m.(m_ncode)) eqn:E.
    + apply key_eqb_spec in E as ->. apply idx_lt_succ.
    + rewrite PTree.gso in hi by exact (key_neq_of_eqb i _ E).
      exact (idx_lt_up _ _ (hc i hi)).
  - intros i hi. exact (idx_lt_up _ _ (hh i hi)).
  - intros i hi. exact (idx_lt_up _ _ (ho i hi)).
  - intros i1 p1 r hi. destruct (hq i1 p1 r hi) as [h1 h2].
    split; [exact (idx_lt_up _ _ h1)|]. intros i2 h2'. exact (idx_lt_up _ _ (h2 i2 h2')).
Qed.

Lemma memo_fresh_set_delta (t : dtrie) (m : cbn_memo) :
  memo_fresh m -> memo_fresh (memo_set_delta t m).
Proof. intros h. exact h. Qed.

Lemma memo_fresh_set_once (i p : key) (b : bool) (m : cbn_memo) :
  memo_fresh m -> idx_lt i m.(m_ncode) ->
  memo_fresh (memo_set_once (set2 i p b m.(m_once)) m).
Proof.
  intros [hc [hh [ho hq]]] hi. unfold memo_set_once, memo_fresh.
  cbn [m_codes m_hash m_once m_ceq m_ncode].
  split; [exact hc|]. split; [exact hh|]. split; [|exact hq].
  intros j hj. destruct (get_set2_outer i p j b m.(m_once) hj) as [->|h]; [exact hi|].
  exact (ho j h).
Qed.

Lemma memo_fresh_set_hash (i p : key) (v : N) (m : cbn_memo) :
  memo_fresh m -> idx_lt i m.(m_ncode) ->
  memo_fresh (memo_set_hash (set2 i p v m.(m_hash)) m).
Proof.
  intros [hc [hh [ho hq]]] hi. unfold memo_set_hash, memo_fresh.
  cbn [m_codes m_hash m_once m_ceq m_ncode].
  split; [exact hc|]. split; [|split; [exact ho | exact hq]].
  intros j hj. destruct (get_set2_outer i p j v m.(m_hash) hj) as [->|h]; [exact hi|].
  exact (hh j h).
Qed.

Lemma memo_fresh_set_ceq (i1 p1 i2 p2 : key) (b : bool) (m : cbn_memo) :
  memo_fresh m -> idx_lt i1 m.(m_ncode) -> idx_lt i2 m.(m_ncode) ->
  memo_fresh
    (memo_set_ceq
       (set2 i1 p1
          (set2 i2 p2 b
             (match get2 i1 p1 m.(m_ceq) with Some q => q | None => PTree.empty _ end))
          m.(m_ceq)) m).
Proof.
  intros [hc [hh [ho hq]]] h1 h2. unfold memo_set_ceq, memo_fresh.
  cbn [m_codes m_hash m_once m_ceq m_ncode].
  split; [exact hc|]. split; [exact hh|]. split; [exact ho|].
  intros j1 q1 r hr.
  destruct (key_eqb j1 i1) eqn:E1; destruct (key_eqb q1 p1) eqn:E2.
  - apply key_eqb_spec in E1 as ->. apply key_eqb_spec in E2 as ->.
    rewrite get2_set2_same in hr. injection hr as <-.
    split; [exact h1|]. intros k hk.
    destruct (get_set2_outer i2 p2 k b _ hk) as [->|hk0]; [exact h2|].
    destruct (get2 i1 p1 m.(m_ceq)) as [r0|] eqn:Er0.
    + exact (proj2 (hq i1 p1 r0 Er0) k hk0).
    + rewrite PTree.gempty in hk0. now destruct hk0.
  - rewrite get2_set2_other in hr by (right; exact (key_neq_of_eqb _ _ E2)).
    exact (hq j1 q1 r hr).
  - rewrite get2_set2_other in hr by (left; exact (key_neq_of_eqb _ _ E1)).
    exact (hq j1 q1 r hr).
  - rewrite get2_set2_other in hr by (left; exact (key_neq_of_eqb _ _ E1)).
    exact (hq j1 q1 r hr).
Qed.

(** ** The caches [m_once] and [m_hash]

  Both are read and written at a code's identifier, so their statements speak of a code
  whose entry is in the table and which satisfies [code_inv] for it: all such codes at one
  identifier have one term ([same_ident_term], from [same_id_sound_table]). *)

Definition once_ok (m : cbn_memo) : Prop :=
  forall (c : code) (e : code_entry) (b : bool),
    get2 c.(c_entry) c.(c_path) m.(m_once) = Some b ->
    PTree.get c.(c_entry) m.(m_codes) = Some e ->
    code_inv e c ->
    b = Nat.leb (occ 0 c.(c_term)) 1.

Definition hash_ok (m : cbn_memo) : Prop :=
  forall (c : code) (e : code_entry) (h : N),
    get2 c.(c_entry) c.(c_path) m.(m_hash) = Some h ->
    PTree.get c.(c_entry) m.(m_codes) = Some e ->
    code_inv e c ->
    h = thash c.(c_term).

Lemma once_ok_fields (m m' : cbn_memo) :
  m'.(m_once) = m.(m_once) -> m'.(m_codes) = m.(m_codes) -> once_ok m -> once_ok m'.
Proof.
  intros h1 h2 h c e b g1 g2. rewrite h1 in g1. rewrite h2 in g2. exact (h c e b g1 g2).
Qed.

Lemma hash_ok_fields (m m' : cbn_memo) :
  m'.(m_hash) = m.(m_hash) -> m'.(m_codes) = m.(m_codes) -> hash_ok m -> hash_ok m'.
Proof.
  intros h1 h2 h c e v g1 g2. rewrite h1 in g1. rewrite h2 in g2. exact (h c e v g1 g2).
Qed.

Lemma once_ok_empty : once_ok memo_empty.
Proof.
  intros c e b g _ _. cbn [memo_empty m_once] in g. rewrite get2_empty in g. discriminate g.
Qed.

Lemma hash_ok_empty : hash_ok memo_empty.
Proof.
  intros c e v g _ _. cbn [memo_empty m_hash] in g. rewrite get2_empty in g. discriminate g.
Qed.

(** Two codes with the same identifier, each read against its table entry, have one term. *)
Lemma same_ident_term (codes : PTree.t code_entry) (c1 c2 : code) (e1 e2 : code_entry) :
  c1.(c_entry) = c2.(c_entry) -> c1.(c_path) = c2.(c_path) ->
  PTree.get c1.(c_entry) codes = Some e1 -> code_inv e1 c1 ->
  PTree.get c2.(c_entry) codes = Some e2 -> code_inv e2 c2 ->
  c1.(c_term) = c2.(c_term).
Proof.
  intros he hp g1 h1 g2 h2.
  refine (same_id_sound_table codes e1 e2 c1 c2 _ g1 h1 g2 h2).
  apply same_id_spec. split; assumption.
Qed.

Lemma once_ok_set (c : code) (e : code_entry) (m : cbn_memo) :
  once_ok m ->
  PTree.get c.(c_entry) m.(m_codes) = Some e -> code_inv e c ->
  once_ok (memo_set_once
             (set2 c.(c_entry) c.(c_path) (Nat.leb (occ 0 c.(c_term)) 1) m.(m_once)) m).
Proof.
  intros h g hi c' e' b. cbn [memo_set_once m_once m_codes]. intros g' g2 hi'.
  destruct (key_eqb c'.(c_entry) c.(c_entry)) eqn:E1;
    destruct (key_eqb c'.(c_path) c.(c_path)) eqn:E2.
  - apply key_eqb_spec in E1. apply key_eqb_spec in E2.
    rewrite E1, E2, get2_set2_same in g'. injection g' as <-.
    rewrite (same_ident_term m.(m_codes) c' c e' e E1 E2 g2 hi' g hi). reflexivity.
  - rewrite get2_set2_other in g' by (right; exact (key_neq_of_eqb _ _ E2)).
    exact (h c' e' b g' g2 hi').
  - rewrite get2_set2_other in g' by (left; exact (key_neq_of_eqb _ _ E1)).
    exact (h c' e' b g' g2 hi').
  - rewrite get2_set2_other in g' by (left; exact (key_neq_of_eqb _ _ E1)).
    exact (h c' e' b g' g2 hi').
Qed.

Lemma hash_ok_set (c : code) (e : code_entry) (m : cbn_memo) :
  hash_ok m ->
  PTree.get c.(c_entry) m.(m_codes) = Some e -> code_inv e c ->
  hash_ok (memo_set_hash (set2 c.(c_entry) c.(c_path) (thash c.(c_term)) m.(m_hash)) m).
Proof.
  intros h g hi c' e' v. cbn [memo_set_hash m_hash m_codes]. intros g' g2 hi'.
  destruct (key_eqb c'.(c_entry) c.(c_entry)) eqn:E1;
    destruct (key_eqb c'.(c_path) c.(c_path)) eqn:E2.
  - apply key_eqb_spec in E1. apply key_eqb_spec in E2.
    rewrite E1, E2, get2_set2_same in g'. injection g' as <-.
    rewrite (same_ident_term m.(m_codes) c' c e' e E1 E2 g2 hi' g hi). reflexivity.
  - rewrite get2_set2_other in g' by (right; exact (key_neq_of_eqb _ _ E2)).
    exact (h c' e' v g' g2 hi').
  - rewrite get2_set2_other in g' by (left; exact (key_neq_of_eqb _ _ E1)).
    exact (h c' e' v g' g2 hi').
  - rewrite get2_set2_other in g' by (left; exact (key_neq_of_eqb _ _ E1)).
    exact (h c' e' v g' g2 hi').
Qed.

(** An added entry carries a fresh index, so no stale cache row is read against it. *)
Lemma once_ok_add_entry (e : code_entry) (m : cbn_memo) :
  memo_fresh m -> once_ok m -> once_ok (snd (memo_add_entry e m)).
Proof.
  intros [_ [_ [ho _]]] h c e' b. cbn [memo_add_entry snd m_once m_codes].
  intros g g2 hi.
  destruct (key_eqb c.(c_entry) m.(m_ncode)) eqn:E.
  - exfalso. apply key_eqb_spec in E.
    pose proof (ho c.(c_entry) (get2_some_outer _ _ _ _ g)) as hlt.
    unfold idx_lt in hlt. rewrite E in hlt. exact (Pos.lt_irrefl _ hlt).
  - rewrite PTree.gso in g2 by exact (key_neq_of_eqb _ _ E). exact (h c e' b g g2 hi).
Qed.

Lemma hash_ok_add_entry (e : code_entry) (m : cbn_memo) :
  memo_fresh m -> hash_ok m -> hash_ok (snd (memo_add_entry e m)).
Proof.
  intros [_ [hh _]] h c e' v. cbn [memo_add_entry snd m_hash m_codes].
  intros g g2 hi.
  destruct (key_eqb c.(c_entry) m.(m_ncode)) eqn:E.
  - exfalso. apply key_eqb_spec in E.
    pose proof (hh c.(c_entry) (get2_some_outer _ _ _ _ g)) as hlt.
    unfold idx_lt in hlt. rewrite E in hlt. exact (Pos.lt_irrefl _ hlt).
  - rewrite PTree.gso in g2 by exact (key_neq_of_eqb _ _ E). exact (h c e' v g g2 hi).
Qed.

(** ** [once_body] and [code_hash] over the state *)

Lemma once_body_memo (c : code) (s : cbn_state) :
  ((snd (once_body c s)).(st_memo)).(m_codes) = ((s.(st_memo)).(m_codes))
  /\ ((snd (once_body c s)).(st_memo)).(m_ncode) = ((s.(st_memo)).(m_ncode))
  /\ ((snd (once_body c s)).(st_memo)).(m_delta) = ((s.(st_memo)).(m_delta))
  /\ ((snd (once_body c s)).(st_memo)).(m_hash) = ((s.(st_memo)).(m_hash))
  /\ ((snd (once_body c s)).(st_memo)).(m_ceq) = ((s.(st_memo)).(m_ceq)).
Proof.
  unfold once_body. destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_once)));
    cbn [snd]; repeat split.
Qed.

Lemma code_hash_state (c : code) (s : cbn_state) :
  (snd (code_hash c s)).(st_heap) = s.(st_heap)
  /\ (snd (code_hash c s)).(st_next) = s.(st_next)
  /\ (snd (code_hash c s)).(st_room) = s.(st_room)
  /\ (snd (code_hash c s)).(st_steps) = s.(st_steps)
  /\ (snd (code_hash c s)).(st_gam) = s.(st_gam).
Proof.
  unfold code_hash. destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_hash)));
    cbn [snd]; repeat split.
Qed.

Lemma code_hash_memo (c : code) (s : cbn_state) :
  ((snd (code_hash c s)).(st_memo)).(m_codes) = ((s.(st_memo)).(m_codes))
  /\ ((snd (code_hash c s)).(st_memo)).(m_ncode) = ((s.(st_memo)).(m_ncode))
  /\ ((snd (code_hash c s)).(st_memo)).(m_delta) = ((s.(st_memo)).(m_delta))
  /\ ((snd (code_hash c s)).(st_memo)).(m_once) = ((s.(st_memo)).(m_once))
  /\ ((snd (code_hash c s)).(st_memo)).(m_ceq) = ((s.(st_memo)).(m_ceq)).
Proof.
  unfold code_hash. destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_hash)));
    cbn [snd]; repeat split.
Qed.

Lemma ceq_set_state (c1 c2 : code) (b : bool) (s : cbn_state) :
  (ceq_set c1 c2 b s).(st_heap) = s.(st_heap)
  /\ (ceq_set c1 c2 b s).(st_next) = s.(st_next)
  /\ (ceq_set c1 c2 b s).(st_room) = s.(st_room)
  /\ (ceq_set c1 c2 b s).(st_steps) = s.(st_steps)
  /\ (ceq_set c1 c2 b s).(st_gam) = s.(st_gam).
Proof. unfold ceq_set; cbv zeta. repeat split. Qed.

Lemma ceq_set_memo (c1 c2 : code) (b : bool) (s : cbn_state) :
  (((ceq_set c1 c2 b s).(st_memo)).(m_codes)) = ((s.(st_memo)).(m_codes))
  /\ (((ceq_set c1 c2 b s).(st_memo)).(m_ncode)) = ((s.(st_memo)).(m_ncode))
  /\ (((ceq_set c1 c2 b s).(st_memo)).(m_delta)) = ((s.(st_memo)).(m_delta))
  /\ (((ceq_set c1 c2 b s).(st_memo)).(m_once)) = ((s.(st_memo)).(m_once))
  /\ (((ceq_set c1 c2 b s).(st_memo)).(m_hash)) = ((s.(st_memo)).(m_hash)).
Proof. unfold ceq_set; cbv zeta. repeat split. Qed.

Lemma once_body_ok (c : code) (e : code_entry) (s : cbn_state) :
  once_ok (s.(st_memo)) ->
  PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e -> code_inv e c ->
  once_ok ((snd (once_body c s)).(st_memo)).
Proof.
  intros h g hi. unfold once_body.
  destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_once))) as [b|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite set_memo_memo. exact (once_ok_set c e (s.(st_memo)) h g hi).
Qed.

Lemma once_body_fresh (c : code) (e : code_entry) (s : cbn_state) :
  memo_fresh (s.(st_memo)) ->
  PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e ->
  memo_fresh ((snd (once_body c s)).(st_memo)).
Proof.
  intros h g. unfold once_body.
  destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_once))) as [b|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite set_memo_memo. apply memo_fresh_set_once; [exact h|].
  apply (memo_fresh_codes (s.(st_memo)) c.(c_entry) h). rewrite g. discriminate.
Qed.

Lemma code_hash_ok (c : code) (e : code_entry) (s : cbn_state) :
  hash_ok (s.(st_memo)) ->
  PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e -> code_inv e c ->
  hash_ok ((snd (code_hash c s)).(st_memo)).
Proof.
  intros h g hi. unfold code_hash.
  destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_hash))) as [v|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite set_memo_memo. exact (hash_ok_set c e (s.(st_memo)) h g hi).
Qed.

Lemma code_hash_fresh (c : code) (e : code_entry) (s : cbn_state) :
  memo_fresh (s.(st_memo)) ->
  PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e ->
  memo_fresh ((snd (code_hash c s)).(st_memo)).
Proof.
  intros h g. unfold code_hash.
  destruct (get2 c.(c_entry) c.(c_path) ((s.(st_memo)).(m_hash))) as [v|] eqn:E;
    cbn [snd]; [exact h|].
  rewrite set_memo_memo. apply memo_fresh_set_hash; [exact h|].
  apply (memo_fresh_codes (s.(st_memo)) c.(c_entry) h). rewrite g. discriminate.
Qed.

(** ** Instantiated code and PCUIC's delta step *)

Lemma inst_code_nil (t : term) : inst_code [] t = t.
Proof. reflexivity. Qed.

Lemma inst_code_cons (l : Level.t) (u : Instance.t) (t : term) :
  inst_code (l :: u) t = subst_instance (l :: u) t.
Proof. reflexivity. Qed.

(** *** The empty instance

  [inst_code [] body] is [body] where PCUIC's [red_delta] produces
  [subst_instance [] body]. The two agree exactly when [body] carries no universe
  variable, and a constant whose universe context has no variables — in particular a
  monomorphic one — has such a body in a well-formed environment. The chain is
  MetaRocq's: [on_declared_constant] types the body in [(Σ, cst_universes cb)],
  [typing_wf_universes] turns that into [wf_universes], [wf_universes_closedu] (with
  [weaken_lookup_on_global_env'] for its [on_udecl_prop] side condition) turns that into
  [closedu #|polymorphic_instance (cst_universes cb)| body], and
  [closedu_subst_instance] then says every instance leaves the body alone. *)

Lemma poly_instance_abstract (univs : universes_decl) :
  polymorphic_instance univs = abstract_instance univs.
Proof. destruct univs; reflexivity. Qed.

Lemma declared_constant_body_closedu {cf : checker_flags} (Σ : global_env)
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
  instance is empty. For the empty instance the machine's [inst_code] returns the body
  unchanged, where PCUIC's [red_delta] produces [subst_instance [] body], and
  [subst_instance []] sends every [Level.lvar] to [Level.lzero]. The two differ on any body
  that mentions a universe variable, so the side condition is needed for a polymorphic
  constant applied to the empty instance, whatever [Σ] is. *)
Lemma inst_code_red1_gen {cf : checker_flags} (Σ : global_env) (Γ : context)
    (kn : kername) (ui : Instance.t) (cb : constant_body) (body : term) :
  wf Σ -> lookup_env Σ kn = Some (ConstantDecl cb) -> cb.(cst_body) = Some body ->
  (ui = [] -> #|polymorphic_instance cb.(cst_universes)| = 0) ->
  red1 Σ Γ (tConst kn ui) (inst_code ui body).
Proof.
  intros wfΣ hl hb hmono.
  assert (hdecl : declared_constant Σ kn cb)
    by (apply declared_constant_from_gen; exact hl).
  destruct ui as [|l ui]; [|rewrite inst_code_cons; eapply red_delta; eassumption].
  assert (hcl : closedu 0 body).
  { rewrite <- (hmono eq_refl).
    exact (declared_constant_body_closedu Σ kn cb body wfΣ hl hb). }
  rewrite inst_code_nil, <- (closedu_subst_instance [] body hcl).
  eapply red_delta; eassumption.
Qed.

(** ** Pairs returned by the machine *)

Lemma cbn_COk_pair_inj {A B : Type} (x1 y1 : A) (x2 y2 : B) :
  COk (x1, x2) = COk (y1, y2) -> x1 = y1 /\ x2 = y2.
Proof. intros h. injection h as h1 h2. split; assumption. Qed.

(** ** The environment-facing invariants: delta and the code-equality cache *)

Section Memo.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).

  (** The syntactic test [code_eq] falls back on. *)
  Definition cbn_ceq_term (t u : term) : bool :=
    eqb_term_upto_univ (abstract_env_compare_universe X) (abstract_env_compare_sort X)
      (compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X))
      Conv t u.

  (** *** The code-equality cache

    The bit stored for a pair of identifiers is the value of [cbn_ceq_term] on the two
    terms, not a claim that they are equal: see the file header. *)

  Definition ceq_lookup (c1 c2 : code) (m : cbn_memo) : option bool :=
    match get2 c1.(c_entry) c1.(c_path) m.(m_ceq) with
    | Some q => get2 c2.(c_entry) c2.(c_path) q
    | None => None
    end.

  Lemma ceq_get_lookup (c1 c2 : code) (s : cbn_state) :
    ceq_get c1 c2 s = ceq_lookup c1 c2 (s.(st_memo)).
  Proof. reflexivity. Qed.

  Definition ceq_ok (m : cbn_memo) : Prop :=
    forall (c1 c2 : code) (e1 e2 : code_entry) (b : bool),
      ceq_lookup c1 c2 m = Some b ->
      PTree.get c1.(c_entry) m.(m_codes) = Some e1 -> code_inv e1 c1 ->
      PTree.get c2.(c_entry) m.(m_codes) = Some e2 -> code_inv e2 c2 ->
      b = cbn_ceq_term c1.(c_term) c2.(c_term).

  Lemma ceq_ok_fields (m m' : cbn_memo) :
    m'.(m_ceq) = m.(m_ceq) -> m'.(m_codes) = m.(m_codes) -> ceq_ok m -> ceq_ok m'.
  Proof.
    intros h1 h2 h c1 c2 e1 e2 b g g1 hi1 g2 hi2.
    unfold ceq_lookup in g. rewrite h1 in g. rewrite h2 in g1, g2.
    exact (h c1 c2 e1 e2 b g g1 hi1 g2 hi2).
  Qed.

  Lemma ceq_ok_empty : ceq_ok memo_empty.
  Proof.
    intros c1 c2 e1 e2 b g _ _ _ _. unfold ceq_lookup in g.
    cbn [memo_empty m_ceq] in g. rewrite get2_empty in g. discriminate g.
  Qed.

  Lemma ceq_ok_add_entry (e : code_entry) (m : cbn_memo) :
    memo_fresh m -> ceq_ok m -> ceq_ok (snd (memo_add_entry e m)).
  Proof.
    intros [_ [_ [_ hq]]] h c1 c2 e1 e2 b. unfold ceq_lookup.
    cbn [memo_add_entry snd m_ceq m_codes]. intros g g1 hi1 g2 hi2.
    destruct (get2 c1.(c_entry) c1.(c_path) m.(m_ceq)) as [r|] eqn:Er; [|discriminate g].
    destruct (hq c1.(c_entry) c1.(c_path) r Er) as [hlt1 hlt2].
    assert (hne1 : c1.(c_entry) <> m.(m_ncode)) by exact (idx_lt_neq _ _ hlt1).
    assert (hne2 : c2.(c_entry) <> m.(m_ncode)).
    { apply idx_lt_neq. apply hlt2. exact (get2_some_outer _ _ _ _ g). }
    rewrite PTree.gso in g1 by exact hne1. rewrite PTree.gso in g2 by exact hne2.
    refine (h c1 c2 e1 e2 b _ g1 hi1 g2 hi2). unfold ceq_lookup. now rewrite Er.
  Qed.

  Lemma ceq_ok_set (c1 c2 : code) (e1 e2 : code_entry) (m : cbn_memo) :
    ceq_ok m ->
    PTree.get c1.(c_entry) m.(m_codes) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) m.(m_codes) = Some e2 -> code_inv e2 c2 ->
    ceq_ok
      (memo_set_ceq
         (set2 c1.(c_entry) c1.(c_path)
            (set2 c2.(c_entry) c2.(c_path) (cbn_ceq_term c1.(c_term) c2.(c_term))
               (match get2 c1.(c_entry) c1.(c_path) m.(m_ceq) with
                | Some q => q
                | None => PTree.empty _
                end))
            m.(m_ceq)) m).
  Proof.
    intros h g1 hi1 g2 hi2 d1 d2 f1 f2 b. unfold ceq_lookup.
    cbn [memo_set_ceq m_ceq m_codes]. intros g k1 ki1 k2 ki2.
    destruct (key_eqb d1.(c_entry) c1.(c_entry)) eqn:E1;
      destruct (key_eqb d1.(c_path) c1.(c_path)) eqn:E2.
    - apply key_eqb_spec in E1. apply key_eqb_spec in E2.
      assert (hd1 : d1.(c_term) = c1.(c_term))
        by exact (same_ident_term m.(m_codes) d1 c1 f1 e1 E1 E2 k1 ki1 g1 hi1).
      rewrite E1, E2, get2_set2_same in g.
      destruct (key_eqb d2.(c_entry) c2.(c_entry)) eqn:E3;
        destruct (key_eqb d2.(c_path) c2.(c_path)) eqn:E4.
      + apply key_eqb_spec in E3. apply key_eqb_spec in E4.
        rewrite E3, E4, get2_set2_same in g. injection g as <-.
        rewrite hd1, (same_ident_term m.(m_codes) d2 c2 f2 e2 E3 E4 k2 ki2 g2 hi2).
        reflexivity.
      + rewrite get2_set2_other in g by (right; exact (key_neq_of_eqb _ _ E4)).
        refine (h d1 d2 f1 f2 b _ k1 ki1 k2 ki2). unfold ceq_lookup. rewrite E1, E2.
        destruct (get2 c1.(c_entry) c1.(c_path) m.(m_ceq)) as [r|] eqn:Er; [exact g|].
        rewrite get2_empty in g. discriminate g.
      + rewrite get2_set2_other in g by (left; exact (key_neq_of_eqb _ _ E3)).
        refine (h d1 d2 f1 f2 b _ k1 ki1 k2 ki2). unfold ceq_lookup. rewrite E1, E2.
        destruct (get2 c1.(c_entry) c1.(c_path) m.(m_ceq)) as [r|] eqn:Er; [exact g|].
        rewrite get2_empty in g. discriminate g.
      + rewrite get2_set2_other in g by (left; exact (key_neq_of_eqb _ _ E3)).
        refine (h d1 d2 f1 f2 b _ k1 ki1 k2 ki2). unfold ceq_lookup. rewrite E1, E2.
        destruct (get2 c1.(c_entry) c1.(c_path) m.(m_ceq)) as [r|] eqn:Er; [exact g|].
        rewrite get2_empty in g. discriminate g.
    - rewrite get2_set2_other in g by (right; exact (key_neq_of_eqb _ _ E2)).
      exact (h d1 d2 f1 f2 b g k1 ki1 k2 ki2).
    - rewrite get2_set2_other in g by (left; exact (key_neq_of_eqb _ _ E1)).
      exact (h d1 d2 f1 f2 b g k1 ki1 k2 ki2).
    - rewrite get2_set2_other in g by (left; exact (key_neq_of_eqb _ _ E1)).
      exact (h d1 d2 f1 f2 b g k1 ki1 k2 ki2).
  Qed.

  Lemma ceq_set_ok (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) :
    ceq_ok (s.(st_memo)) ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 -> code_inv e2 c2 ->
    ceq_ok (((ceq_set c1 c2 (cbn_ceq_term c1.(c_term) c2.(c_term)) s)).(st_memo)).
  Proof.
    intros h g1 hi1 g2 hi2. unfold ceq_set; cbv zeta. rewrite set_memo_memo.
    exact (ceq_ok_set c1 c2 e1 e2 (s.(st_memo)) h g1 hi1 g2 hi2).
  Qed.

  Lemma ceq_set_fresh (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) (b : bool) :
    memo_fresh (s.(st_memo)) ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 ->
    memo_fresh ((ceq_set c1 c2 b s).(st_memo)).
  Proof.
    intros h g1 g2. unfold ceq_set; cbv zeta. rewrite set_memo_memo.
    apply memo_fresh_set_ceq; [exact h| |].
    - apply (memo_fresh_codes (s.(st_memo)) c1.(c_entry) h). rewrite g1. discriminate.
    - apply (memo_fresh_codes (s.(st_memo)) c2.(c_entry) h). rewrite g2. discriminate.
  Qed.

  Lemma ceq_set_once_ok (c1 c2 : code) (b : bool) (s : cbn_state) :
    once_ok (s.(st_memo)) -> once_ok ((ceq_set c1 c2 b s).(st_memo)).
  Proof.
    apply once_ok_fields;
      [exact (proj1 (proj2 (proj2 (proj2 (ceq_set_memo c1 c2 b s)))))
      | exact (proj1 (ceq_set_memo c1 c2 b s))].
  Qed.

  Lemma ceq_set_hash_ok (c1 c2 : code) (b : bool) (s : cbn_state) :
    hash_ok (s.(st_memo)) -> hash_ok ((ceq_set c1 c2 b s).(st_memo)).
  Proof.
    apply hash_ok_fields;
      [exact (proj2 (proj2 (proj2 (proj2 (ceq_set_memo c1 c2 b s)))))
      | exact (proj1 (ceq_set_memo c1 c2 b s))].
  Qed.

  (** *** What a [true] from [code_eq] gives

    Either the two codes have the same term, or the syntactic comparison up to universes
    says [true]. Nothing is claimed of a [false]. *)

  Lemma code_eq_sound (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) :
    ceq_ok (s.(st_memo)) ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 -> code_inv e2 c2 ->
    fst (code_eq X_type X c1 c2 s) = true ->
    c1.(c_term) = c2.(c_term) \/ cbn_ceq_term c1.(c_term) c2.(c_term) = true.
  Proof.
    intros hq g1 hi1 g2 hi2. unfold code_eq.
    destruct (same_id c1 c2) eqn:Esid.
    { intros _. left.
      exact (same_id_sound_table ((s.(st_memo)).(m_codes)) e1 e2 c1 c2 Esid g1 hi1 g2 hi2). }
    destruct (negb (entry_wf c1.(c_entry) s && entry_wf c2.(c_entry) s)) eqn:Ewf;
      [cbn [fst]; intros hc; discriminate hc|].
    destruct (code_hash c1 s) as [v1 s1] eqn:E1.
    destruct (code_hash c2 s1) as [v2 s2] eqn:E2.
    assert (hs1 : s1 = snd (code_hash c1 s)) by (rewrite E1; reflexivity).
    assert (hs2 : s2 = snd (code_hash c2 s1)) by (rewrite E2; reflexivity).
    assert (hc1 : ((s1.(st_memo)).(m_codes)) = ((s.(st_memo)).(m_codes)))
      by (rewrite hs1; apply (proj1 (code_hash_memo c1 s))).
    assert (hq1 : ((s1.(st_memo)).(m_ceq)) = ((s.(st_memo)).(m_ceq)))
      by (rewrite hs1; exact (proj2 (proj2 (proj2 (proj2 (code_hash_memo c1 s)))))).
    assert (hc2 : ((s2.(st_memo)).(m_codes)) = ((s1.(st_memo)).(m_codes)))
      by (rewrite hs2; apply (proj1 (code_hash_memo c2 s1))).
    assert (hq2 : ((s2.(st_memo)).(m_ceq)) = ((s1.(st_memo)).(m_ceq)))
      by (rewrite hs2; exact (proj2 (proj2 (proj2 (proj2 (code_hash_memo c2 s1)))))).
    destruct (negb (N.eqb v1 v2)) eqn:Eh; [cbn [fst]; intros hc; discriminate hc|].
    destruct (ceq_get c1 c2 s2) as [b|] eqn:Ec; cbn [fst]; intros hb; right.
    - subst b. rewrite ceq_get_lookup in Ec.
      refine (eq_sym (hq c1 c2 e1 e2 true _ g1 hi1 g2 hi2)).
      unfold ceq_lookup in Ec |- *. rewrite hq2, hq1 in Ec. exact Ec.
    - exact hb.
  Qed.

  (** *** The delta memo

    The machine's oracle is [abstract_env_lookup X]; [lookup_declared] turns an answer of it
    into [declared_constant Σ] for any [Σ] the abstract environment stands for. *)

  Lemma lookup_declared (Σ : global_env_ext) (kn : kername) (cb : constant_body) :
    abstract_env_ext_rel X Σ ->
    abstract_env_lookup X kn = Some (ConstantDecl cb) ->
    declared_constant Σ kn cb.
  Proof.
    intros hΣ h. apply declared_constant_from_gen. unfold declared_constant_gen.
    rewrite (abstract_env_lookup_correct' X (Σ := Σ) kn hΣ). exact h.
  Qed.

  Definition inst_entry_ok (codes : PTree.t code_entry) (body : term)
    (p : Instance.t * cidx * term) : Prop :=
    let '(u, i, t) := p in
    t = inst_code u body
    /\ exists e : code_entry,
        PTree.get i codes = Some e /\ e.(ce_term) = body /\ e.(ce_inst) = u.

  Definition delta_ok (m : cbn_memo) : Prop :=
    forall (kn : kername) (d : delta_memo),
      dt_find kn m.(m_delta) = Some d ->
      match d with
      | DAxiom =>
          exists cb : constant_body,
            abstract_env_lookup X kn = Some (ConstantDecl cb) /\ cb.(cst_body) = None
      | DBody body insts =>
          (exists cb : constant_body,
              abstract_env_lookup X kn = Some (ConstantDecl cb)
              /\ cb.(cst_body) = Some body)
          /\ Forall (inst_entry_ok m.(m_codes) body) insts
      end.

  Lemma delta_ok_empty : delta_ok memo_empty.
  Proof.
    intros kn d h. cbn [memo_empty m_delta] in h. rewrite dt_find_nil in h. discriminate h.
  Qed.

  Lemma inst_entry_ok_mono (codes codes' : PTree.t code_entry) (body : term)
      (insts : list (Instance.t * cidx * term)) :
    (forall (i : key) (e : code_entry),
        PTree.get i codes = Some e -> PTree.get i codes' = Some e) ->
    Forall (inst_entry_ok codes body) insts ->
    Forall (inst_entry_ok codes' body) insts.
  Proof.
    intros hc hF. induction hF as [|p insts hp hFl IH]; constructor; [|exact IH].
    destruct p as [[u i] t]. destruct hp as [ht [e [he [h1 h2]]]].
    split; [exact ht|]. exists e. split; [exact (hc i e he)|]. split; assumption.
  Qed.

  (** [delta_ok] reads only the delta trie and the code table, and the code table only
    grows. *)
  Lemma delta_ok_mono (m m' : cbn_memo) :
    m'.(m_delta) = m.(m_delta) ->
    (forall (i : key) (e : code_entry),
        PTree.get i m.(m_codes) = Some e -> PTree.get i m'.(m_codes) = Some e) ->
    delta_ok m -> delta_ok m'.
  Proof.
    intros hd hc h kn d g. rewrite hd in g. specialize (h kn d g).
    destruct d as [|body insts]; [exact h|].
    destruct h as [hcb hF]. split; [exact hcb|].
    exact (inst_entry_ok_mono _ _ body insts hc hF).
  Qed.

  Lemma memo_add_entry_codes_mono (e : code_entry) (m : cbn_memo) :
    memo_fresh m ->
    forall (i : key) (e' : code_entry),
      PTree.get i m.(m_codes) = Some e' ->
      PTree.get i ((snd (memo_add_entry e m)).(m_codes)) = Some e'.
  Proof.
    intros hf i e' h. cbn [memo_add_entry snd m_codes].
    rewrite PTree.gso; [exact h|].
    apply idx_lt_neq. apply (memo_fresh_codes m i hf). rewrite h. discriminate.
  Qed.

  Lemma delta_ok_add_entry (e : code_entry) (m : cbn_memo) :
    memo_fresh m -> delta_ok m -> delta_ok (snd (memo_add_entry e m)).
  Proof.
    intros hf h.
    exact (delta_ok_mono m (snd (memo_add_entry e m)) eq_refl
             (memo_add_entry_codes_mono e m hf) h).
  Qed.

  (** *** [new_entry] *)

  Lemma new_entry_memo_eq (t : term) (u : Instance.t) (s : cbn_state) :
    ((snd (new_entry X_type X t u s)).(st_memo))
    = snd (memo_add_entry
             (mkEntry t u (wf_term_univs X_type X (inst_code u t))) (s.(st_memo))).
  Proof. reflexivity. Qed.

  Lemma new_entry_fresh (t : term) (u : Instance.t) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> memo_fresh ((snd (new_entry X_type X t u s)).(st_memo)).
  Proof. intros h. rewrite new_entry_memo_eq. now apply memo_fresh_add_entry. Qed.

  Lemma new_entry_once_ok (t : term) (u : Instance.t) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> once_ok (s.(st_memo)) ->
    once_ok ((snd (new_entry X_type X t u s)).(st_memo)).
  Proof. intros hf h. rewrite new_entry_memo_eq. now apply once_ok_add_entry. Qed.

  Lemma new_entry_hash_ok (t : term) (u : Instance.t) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> hash_ok (s.(st_memo)) ->
    hash_ok ((snd (new_entry X_type X t u s)).(st_memo)).
  Proof. intros hf h. rewrite new_entry_memo_eq. now apply hash_ok_add_entry. Qed.

  Lemma new_entry_ceq_ok (t : term) (u : Instance.t) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> ceq_ok (s.(st_memo)) ->
    ceq_ok ((snd (new_entry X_type X t u s)).(st_memo)).
  Proof. intros hf h. rewrite new_entry_memo_eq. now apply ceq_ok_add_entry. Qed.

  Lemma new_entry_delta_ok (t : term) (u : Instance.t) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> delta_ok (s.(st_memo)) ->
    delta_ok ((snd (new_entry X_type X t u s)).(st_memo)).
  Proof. intros hf h. rewrite new_entry_memo_eq. now apply delta_ok_add_entry. Qed.

  (** *** [delta_new]: one code entry per (constant, syntactic instance) *)

  Lemma delta_new_spec (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    delta_new X_type X kn ui body insts s
    = (fst (new_entry X_type X body ui s),
       set_memo
         (memo_set_delta
            (dt_add kn
               (DBody body
                  ((ui, (fst (new_entry X_type X body ui s)).(c_entry),
                        (fst (new_entry X_type X body ui s)).(c_term))
                     :: insts))
               (((snd (new_entry X_type X body ui s)).(st_memo)).(m_delta)))
            ((snd (new_entry X_type X body ui s)).(st_memo)))
         (snd (new_entry X_type X body ui s))).
  Proof.
    unfold delta_new. destruct (new_entry X_type X body ui s). reflexivity.
  Qed.

  Lemma delta_new_fst (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    fst (delta_new X_type X kn ui body insts s)
    = fst (new_entry X_type X body ui s).
  Proof. rewrite delta_new_spec. reflexivity. Qed.

  Lemma delta_new_code (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    (fst (delta_new X_type X kn ui body insts s)).(c_term) = inst_code ui body
    /\ (fst (delta_new X_type X kn ui body insts s)).(c_path) = path_nil
    /\ (fst (delta_new X_type X kn ui body insts s)).(c_entry) = ((s.(st_memo)).(m_ncode)).
  Proof.
    rewrite delta_new_fst, new_entry_code. cbn [c_term c_path c_entry]. repeat split.
  Qed.

  Lemma delta_new_codes (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    (((snd (delta_new X_type X kn ui body insts s)).(st_memo)).(m_codes))
    = (((snd (new_entry X_type X body ui s)).(st_memo)).(m_codes)).
  Proof. rewrite delta_new_spec. reflexivity. Qed.

  Lemma delta_new_entry (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    PTree.get ((fst (delta_new X_type X kn ui body insts s)).(c_entry))
      (((snd (delta_new X_type X kn ui body insts s)).(st_memo)).(m_codes))
    = Some (mkEntry body ui
              (wf_term_univs X_type X (inst_code ui body))).
  Proof.
    rewrite delta_new_fst, delta_new_codes.
    exact (new_entry_in_table X_type X body ui s).
  Qed.

  Lemma delta_new_code_inv (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    code_inv (mkEntry body ui (wf_term_univs X_type X (inst_code ui body)))
      (fst (delta_new X_type X kn ui body insts s)).
  Proof.
    rewrite delta_new_fst. exact (new_entry_code_inv X_type X body ui s).
  Qed.

  Lemma delta_new_trie (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    (((snd (delta_new X_type X kn ui body insts s)).(st_memo)).(m_delta))
    = dt_add kn
        (DBody body ((ui, ((s.(st_memo)).(m_ncode)), inst_code ui body) :: insts))
        ((s.(st_memo)).(m_delta)).
  Proof. rewrite delta_new_spec. reflexivity. Qed.

  Lemma delta_new_fresh (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    memo_fresh (s.(st_memo)) ->
    memo_fresh (((snd (delta_new X_type X kn ui body insts s)).(st_memo))).
  Proof.
    intros h. rewrite delta_new_spec. cbn [snd]. rewrite set_memo_memo.
    apply memo_fresh_set_delta. now apply new_entry_fresh.
  Qed.

  Lemma delta_new_once_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> once_ok (s.(st_memo)) ->
    once_ok (((snd (delta_new X_type X kn ui body insts s)).(st_memo))).
  Proof.
    intros hf h. rewrite delta_new_spec. cbn [snd]. rewrite set_memo_memo.
    refine (once_ok_fields _ _ _ _ (new_entry_once_ok body ui s hf h));
      reflexivity.
  Qed.

  Lemma delta_new_hash_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> hash_ok (s.(st_memo)) ->
    hash_ok (((snd (delta_new X_type X kn ui body insts s)).(st_memo))).
  Proof.
    intros hf h. rewrite delta_new_spec. cbn [snd]. rewrite set_memo_memo.
    refine (hash_ok_fields _ _ _ _ (new_entry_hash_ok body ui s hf h));
      reflexivity.
  Qed.

  Lemma delta_new_ceq_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) :
    memo_fresh (s.(st_memo)) -> ceq_ok (s.(st_memo)) ->
    ceq_ok (((snd (delta_new X_type X kn ui body insts s)).(st_memo))).
  Proof.
    intros hf h. rewrite delta_new_spec. cbn [snd]. rewrite set_memo_memo.
    refine (ceq_ok_fields _ _ _ _ (new_entry_ceq_ok body ui s hf h));
      reflexivity.
  Qed.

  (** The new trie answers [DBody body] for [kn], with the instance just added at the index
    just added, and keeps every other answer. *)
  Lemma delta_new_ok (kn : kername) (ui : Instance.t) (body : term)
      (insts : list (Instance.t * cidx * term)) (s : cbn_state) (cb : constant_body) :
    memo_fresh (s.(st_memo)) -> delta_ok (s.(st_memo)) ->
    abstract_env_lookup X kn = Some (ConstantDecl cb) -> cb.(cst_body) = Some body ->
    Forall (inst_entry_ok ((s.(st_memo)).(m_codes)) body) insts ->
    delta_ok (((snd (delta_new X_type X kn ui body insts s)).(st_memo))).
  Proof.
    intros hf hd hl hb hF.
    assert (hmono : forall (i : key) (e : code_entry),
               PTree.get i ((s.(st_memo)).(m_codes)) = Some e ->
               PTree.get i
                 (((snd (delta_new X_type X kn ui body insts s)).(st_memo)).(m_codes))
               = Some e).
    { intros i e h. rewrite delta_new_codes, new_entry_memo_eq.
      exact (memo_add_entry_codes_mono _ (s.(st_memo)) hf i e h). }
    intros kn' d g. rewrite delta_new_trie in g.
    destruct (eqb_specT kn' kn) as [->|hne].
    - rewrite dt_find_add_same in g. injection g as <-.
      split; [exists cb; split; assumption|].
      constructor.
      + split; [reflexivity|].
        exists (mkEntry body ui
                  (wf_term_univs X_type X (inst_code ui body))).
        split; [|split; reflexivity].
        pose proof (delta_new_entry kn ui body insts s) as hent.
        rewrite (proj2 (proj2 (delta_new_code kn ui body insts s))) in hent. exact hent.
      + exact (inst_entry_ok_mono _ _ body insts hmono hF).
    - rewrite (dt_find_add_other kn kn' _ _ hne) in g.
      pose proof (hd kn' d g) as hres.
      destruct d as [|body' insts']; [exact hres|].
      destruct hres as [hcb hF'].
      split; [exact hcb|]. exact (inst_entry_ok_mono _ _ body' insts' hmono hF').
  Qed.

  (** *** [find_inst] returns the body at that instance *)

  Lemma find_inst_sound (P : Instance.t * cidx * term -> Prop) (ui : Instance.t)
      (l : list (Instance.t * cidx * term)) (i : cidx) (t : term) :
    Forall P l -> find_inst ui l = Some (i, t) -> P (ui, i, t).
  Proof.
    induction 1 as [|p l hp hFl IH]; [intros hc; discriminate hc|].
    destruct p as [[u' i'] t']. cbn [find_inst].
    destruct (Instance.eqb ui u') eqn:E.
    - intros hc. injection hc as <- <-. apply instance_eqb_eq in E. subst u'. exact hp.
    - exact IH.
  Qed.

  (** *** The machine's [delta]

    [delta] returns [delta_new]'s result through a [let]-destructured pair; [let_COk_pair]
    reads the components without having to [destruct] the application and lose the name
    [delta_new] the per-field lemmas speak of. *)

  Lemma let_COk_pair {A : Type} (p : code * cbn_state) (g : code -> A)
      (r : A) (s' : cbn_state) :
    (let (c, s0) := p in COk (g c, s0)) = COk (r, s') -> r = g (fst p) /\ s' = snd p.
  Proof. destruct p as [c s0]. intros h. injection h as <- <-. split; reflexivity. Qed.

  Lemma delta_fresh (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_fresh (s.(st_memo)) -> delta X_type X kn ui s = COk (r, s') ->
    memo_fresh (s'.(st_memo)).
  Proof.
    intros hf. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact hf.
    - destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact hf.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s' hc)
          as [_ ->]. now apply delta_new_fresh.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s' hc)
          as [_ ->]. now apply delta_new_fresh.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst s'.
        rewrite set_memo_memo. now apply memo_fresh_set_delta.
  Qed.

  Lemma delta_memo_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_ok X_type X s -> delta X_type X kn ui s = COk (r, s') -> memo_ok X_type X s'.
  Proof.
    intros hm. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact hm.
    - destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact hm.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s' hc)
          as [_ ->].
        refine (memo_ok_codes X_type X (snd (new_entry X_type X body ui s))
                  _ _ (new_entry_memo_ok X_type X body ui s hm)).
        apply delta_new_codes.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s' hc)
          as [_ ->].
        refine (memo_ok_codes X_type X (snd (new_entry X_type X body ui s))
                  _ _ (new_entry_memo_ok X_type X body ui s hm)).
        apply delta_new_codes.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst s'.
        refine (memo_ok_codes X_type X s _ _ hm). reflexivity.
  Qed.

  Lemma delta_ok_pres (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_fresh (s.(st_memo)) -> delta_ok (s.(st_memo)) ->
    delta X_type X kn ui s = COk (r, s') -> delta_ok (s'.(st_memo)).
  Proof.
    intros hf hd. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact hd.
    - pose proof (hd kn _ Ed) as hdb. destruct hdb as [[cb [hl hb]] hF].
      destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact hd.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s' hc)
          as [_ ->].
        exact (delta_new_ok kn ui body insts s cb hf hd hl hb hF).
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s' hc)
          as [_ ->].
        exact (delta_new_ok kn ui body [] s cb hf hd El Eb (Forall_nil _)).
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst s'.
        rewrite set_memo_memo. intros kn' d g.
        rewrite memo_set_delta_delta in g. rewrite memo_set_delta_codes.
        destruct (eqb_specT kn' kn) as [->|hne].
        * rewrite dt_find_add_same in g. injection g as <-.
          exists cb. split; assumption.
        * rewrite (dt_find_add_other kn kn' _ _ hne) in g.
          pose proof (hd kn' d g) as hres. destruct d as [|body' insts']; exact hres.
  Qed.

  Lemma delta_once_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_fresh (s.(st_memo)) -> once_ok (s.(st_memo)) ->
    delta X_type X kn ui s = COk (r, s') -> once_ok (s'.(st_memo)).
  Proof.
    intros hf h. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact h.
    - destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact h.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s' hc)
          as [_ ->]. now apply delta_new_once_ok.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s' hc)
          as [_ ->]. now apply delta_new_once_ok.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst s'.
        rewrite set_memo_memo. refine (once_ok_fields _ _ _ _ h); reflexivity.
  Qed.

  Lemma delta_hash_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_fresh (s.(st_memo)) -> hash_ok (s.(st_memo)) ->
    delta X_type X kn ui s = COk (r, s') -> hash_ok (s'.(st_memo)).
  Proof.
    intros hf h. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact h.
    - destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact h.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s' hc)
          as [_ ->]. now apply delta_new_hash_ok.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s' hc)
          as [_ ->]. now apply delta_new_hash_ok.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst s'.
        rewrite set_memo_memo. refine (hash_ok_fields _ _ _ _ h); reflexivity.
  Qed.

  Lemma delta_ceq_ok (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_fresh (s.(st_memo)) -> ceq_ok (s.(st_memo)) ->
    delta X_type X kn ui s = COk (r, s') -> ceq_ok (s'.(st_memo)).
  Proof.
    intros hf h. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact h.
    - destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst. exact h.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some r s' hc)
          as [_ ->]. now apply delta_new_ceq_ok.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some r s' hc)
          as [_ ->]. now apply delta_new_ceq_ok.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. subst s'.
        rewrite set_memo_memo. refine (ceq_ok_fields _ _ _ _ h); reflexivity.
  Qed.

  (** *** What the machine's [delta] answers

    This is the shape the evaluator needs: the code the fast path hands back for
    [tConst kn u] is the root code of a table entry whose term is the environment's body of
    [kn] at instance [u]. *)

  Lemma delta_body (Σ : global_env_ext) (kn : kername) (ui : Instance.t)
      (s s' : cbn_state) (c : code) :
    abstract_env_ext_rel X Σ ->
    memo_fresh (s.(st_memo)) -> delta_ok (s.(st_memo)) ->
    delta X_type X kn ui s = COk (Some c, s') ->
    exists (cb : constant_body) (body : term) (e : code_entry),
      declared_constant Σ kn cb
      /\ cb.(cst_body) = Some body
      /\ c.(c_term) = inst_code ui body
      /\ c.(c_path) = path_nil
      /\ PTree.get c.(c_entry) ((s'.(st_memo)).(m_codes)) = Some e
      /\ e.(ce_term) = body
      /\ e.(ce_inst) = ui
      /\ code_inv e c.
  Proof.
    intros hΣ hf hd. unfold delta.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. discriminate h1.
    - pose proof (hd kn _ Ed) as hdb. destruct hdb as [[cb [hl hb]] hF].
      destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2].
        injection h1 as <-. subst s'.
        destruct (find_inst_sound _ ui insts i t hF Ei) as [ht [e [he [h3 h4]]]].
        exists cb, body, e.
        split; [exact (lookup_declared Σ kn cb hΣ hl)|].
        split; [exact hb|].
        split; [cbn [c_term]; exact ht|].
        split; [reflexivity|].
        split; [cbn [c_entry]; exact he|].
        split; [exact h3|]. split; [exact h4|].
        pose proof (code_inv_root e i) as hroot.
        rewrite h3, h4 in hroot. rewrite <- ht in hroot. exact hroot.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some (Some c) s' hc)
          as [hr ->]. injection hr as ->.
        exists cb, body,
          (mkEntry body ui (wf_term_univs X_type X (inst_code ui body))).
        split; [exact (lookup_declared Σ kn cb hΣ hl)|].
        split; [exact hb|].
        destruct (delta_new_code kn ui body insts s) as [hct [hcp hce]].
        split; [exact hct|]. split; [exact hcp|].
        split; [exact (delta_new_entry kn ui body insts s)|].
        split; [reflexivity|]. split; [reflexivity|].
        exact (delta_new_code_inv kn ui body insts s).
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|intros hc; discriminate hc|intros hc; discriminate hc].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + intros hc.
        destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some (Some c) s' hc)
          as [hr ->]. injection hr as ->.
        exists cb, body,
          (mkEntry body ui (wf_term_univs X_type X (inst_code ui body))).
        split; [exact (lookup_declared Σ kn cb hΣ El)|].
        split; [exact Eb|].
        destruct (delta_new_code kn ui body [] s) as [hct [hcp hce]].
        split; [exact hct|]. split; [exact hcp|].
        split; [exact (delta_new_entry kn ui body [] s)|].
        split; [reflexivity|]. split; [reflexivity|].
        exact (delta_new_code_inv kn ui body [] s).
      + intros hc. destruct (cbn_COk_pair_inj _ _ _ _ hc) as [h1 h2]. discriminate h1.
  Qed.

  Lemma lookup_env_of_abstract (Σ : global_env_ext) (kn : kername) (d : global_decl) :
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
  Lemma delta_red1 (Σ : global_env_ext) (Γ : context) (kn : kername) (ui : Instance.t)
      (s s' : cbn_state) (c : code) :
    abstract_env_ext_rel X Σ -> wf Σ ->
    memo_fresh (s.(st_memo)) -> delta_ok (s.(st_memo)) ->
    delta X_type X kn ui s = COk (Some c, s') ->
    (forall cb : constant_body,
        abstract_env_lookup X kn = Some (ConstantDecl cb) ->
        ui = [] -> #|polymorphic_instance cb.(cst_universes)| = 0) ->
    red1 Σ Γ (tConst kn ui) c.(c_term).
  Proof.
    intros hΣ wfΣ hf hd he hmono. unfold delta in he.
    destruct (dt_find kn ((s.(st_memo)).(m_delta))) as [[|body insts]|] eqn:Ed.
    - destruct (cbn_COk_pair_inj _ _ _ _ he) as [h1 h2]. discriminate h1.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El.
      + assert (Hb : cb.(cst_body) = Some body).
        { destruct (hd kn _ Ed) as [[cb0 [hl hb]] _]. rewrite El in hl.
          injection hl as <-. exact hb. }
        destruct (find_inst ui insts) as [[i t]|] eqn:Ei.
        * destruct (cbn_COk_pair_inj _ _ _ _ he) as [h1 h2]. injection h1 as <-.
          cbn [c_term].
          assert (Ht : t = inst_code ui body).
          { destruct (hd kn _ Ed) as [_ hF].
            destruct (find_inst_sound _ ui insts i t hF Ei) as [ht _]. exact ht. }
          rewrite Ht.
          exact (inst_code_red1_gen Σ Γ kn ui cb body wfΣ
                   (lookup_env_of_abstract Σ kn _ hΣ El) Hb (hmono cb eq_refl)).
        * destruct (let_COk_pair (delta_new X_type X kn ui body insts s) Some (Some c) s' he)
            as [hr _].
          assert (Hc : c.(c_term) = inst_code ui body).
          { apply (f_equal (fun o : option code =>
                     match o with Some x => x.(c_term) | None => c.(c_term) end)) in hr.
            cbn in hr. rewrite hr. apply (proj1 (delta_new_code kn ui body insts s)). }
          rewrite Hc.
          exact (inst_code_red1_gen Σ Γ kn ui cb body wfΣ
                   (lookup_env_of_abstract Σ kn _ hΣ El) Hb (hmono cb eq_refl)).
      + exfalso. destruct (hd kn _ Ed) as [[cb0 [hl _]] _]. rewrite El in hl. discriminate hl.
      + exfalso. destruct (hd kn _ Ed) as [[cb0 [hl _]] _]. rewrite El in hl. discriminate hl.
    - destruct (abstract_env_lookup X kn) as [[cb|mib]|] eqn:El;
        [|discriminate he|discriminate he].
      destruct (cb.(cst_body)) as [body|] eqn:Eb.
      + destruct (let_COk_pair (delta_new X_type X kn ui body [] s) Some (Some c) s' he)
          as [hr _].
        assert (Hc : c.(c_term) = inst_code ui body).
        { apply (f_equal (fun o : option code =>
                   match o with Some x => x.(c_term) | None => c.(c_term) end)) in hr.
          cbn in hr. rewrite hr. apply (proj1 (delta_new_code kn ui body [] s)). }
        rewrite Hc.
        exact (inst_code_red1_gen Σ Γ kn ui cb body wfΣ
                 (lookup_env_of_abstract Σ kn _ hΣ El) Eb (hmono cb eq_refl)).
      + destruct (cbn_COk_pair_inj _ _ _ _ he) as [h1 h2]. discriminate h1.
  Qed.

  (** ** The five invariants of one call, bundled *)

  Definition memo_inv (s : cbn_state) : Prop :=
    memo_fresh (s.(st_memo)) /\ once_ok (s.(st_memo)) /\ hash_ok (s.(st_memo))
    /\ ceq_ok (s.(st_memo)) /\ delta_ok (s.(st_memo)).

  Lemma memo_inv_init : memo_inv cbn_init.
  Proof.
    unfold memo_inv, cbn_init. cbn [st_memo].
    split; [apply memo_fresh_empty|]. split; [apply once_ok_empty|].
    split; [apply hash_ok_empty|]. split; [apply ceq_ok_empty | apply delta_ok_empty].
  Qed.

  Lemma memo_inv_new_entry (t : term) (u : Instance.t) (s : cbn_state) :
    memo_inv s -> memo_inv (snd (new_entry X_type X t u s)).
  Proof.
    intros [hf [ho [hh [hq hd]]]]. unfold memo_inv.
    split; [now apply new_entry_fresh|]. split; [now apply new_entry_once_ok|].
    split; [now apply new_entry_hash_ok|].
    split; [now apply new_entry_ceq_ok | now apply new_entry_delta_ok].
  Qed.

  Lemma memo_inv_once_body (c : code) (e : code_entry) (s : cbn_state) :
    memo_inv s ->
    PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e -> code_inv e c ->
    memo_inv (snd (once_body c s)).
  Proof.
    intros [hf [ho [hh [hq hd]]]] g hi. unfold memo_inv.
    split; [exact (once_body_fresh c e s hf g)|].
    split; [exact (once_body_ok c e s ho g hi)|].
    split; [refine (hash_ok_fields _ _ _ _ hh);
            [exact (proj1 (proj2 (proj2 (proj2 (once_body_memo c s)))))
            | exact (proj1 (once_body_memo c s))]|].
    split; [refine (ceq_ok_fields _ _ _ _ hq);
            [exact (proj2 (proj2 (proj2 (proj2 (once_body_memo c s)))))
            | exact (proj1 (once_body_memo c s))]|].
    refine (delta_ok_mono _ _ _ _ hd).
    - exact (proj1 (proj2 (proj2 (once_body_memo c s)))).
    - intros i e' h. rewrite (proj1 (once_body_memo c s)). exact h.
  Qed.

  Lemma memo_inv_code_hash (c : code) (e : code_entry) (s : cbn_state) :
    memo_inv s ->
    PTree.get c.(c_entry) ((s.(st_memo)).(m_codes)) = Some e -> code_inv e c ->
    memo_inv (snd (code_hash c s)).
  Proof.
    intros [hf [ho [hh [hq hd]]]] g hi. unfold memo_inv.
    split; [exact (code_hash_fresh c e s hf g)|].
    split; [refine (once_ok_fields _ _ _ _ ho);
            [exact (proj1 (proj2 (proj2 (proj2 (code_hash_memo c s)))))
            | exact (proj1 (code_hash_memo c s))]|].
    split; [exact (code_hash_ok c e s hh g hi)|].
    split; [refine (ceq_ok_fields _ _ _ _ hq);
            [exact (proj2 (proj2 (proj2 (proj2 (code_hash_memo c s)))))
            | exact (proj1 (code_hash_memo c s))]|].
    refine (delta_ok_mono _ _ _ _ hd).
    - exact (proj1 (proj2 (proj2 (code_hash_memo c s)))).
    - intros i e' h. rewrite (proj1 (code_hash_memo c s)). exact h.
  Qed.

  Lemma memo_inv_ceq_set (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) :
    memo_inv s ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 -> code_inv e2 c2 ->
    memo_inv (ceq_set c1 c2 (cbn_ceq_term c1.(c_term) c2.(c_term)) s).
  Proof.
    intros [hf [ho [hh [hq hd]]]] g1 hi1 g2 hi2. unfold memo_inv.
    set (b := cbn_ceq_term c1.(c_term) c2.(c_term)).
    split; [exact (ceq_set_fresh c1 c2 e1 e2 s b hf g1 g2)|].
    split; [exact (ceq_set_once_ok c1 c2 b s ho)|].
    split; [exact (ceq_set_hash_ok c1 c2 b s hh)|].
    split; [exact (ceq_set_ok c1 c2 e1 e2 s hq g1 hi1 g2 hi2)|].
    refine (delta_ok_mono _ _ _ _ hd).
    - exact (proj1 (proj2 (proj2 (ceq_set_memo c1 c2 b s)))).
    - intros i e' h. rewrite (proj1 (ceq_set_memo c1 c2 b s)). exact h.
  Qed.

  Lemma memo_inv_code_eq (c1 c2 : code) (e1 e2 : code_entry) (s : cbn_state) :
    memo_inv s ->
    PTree.get c1.(c_entry) ((s.(st_memo)).(m_codes)) = Some e1 -> code_inv e1 c1 ->
    PTree.get c2.(c_entry) ((s.(st_memo)).(m_codes)) = Some e2 -> code_inv e2 c2 ->
    memo_inv (snd (code_eq X_type X c1 c2 s))
    /\ ((snd (code_eq X_type X c1 c2 s)).(st_memo)).(m_codes)
       = ((s.(st_memo)).(m_codes))
    /\ (snd (code_eq X_type X c1 c2 s)).(st_heap) = s.(st_heap)
    /\ (snd (code_eq X_type X c1 c2 s)).(st_next) = s.(st_next)
    /\ (snd (code_eq X_type X c1 c2 s)).(st_room) = s.(st_room)
    /\ (snd (code_eq X_type X c1 c2 s)).(st_steps) = s.(st_steps)
    /\ (snd (code_eq X_type X c1 c2 s)).(st_gam) = s.(st_gam).
  Proof.
    intros hm g1 hi1 g2 hi2. unfold code_eq.
    destruct (same_id c1 c2) eqn:Esid;
      [cbn [snd]; split; [exact hm|]; repeat split; reflexivity|].
    destruct (negb (entry_wf c1.(c_entry) s && entry_wf c2.(c_entry) s)) eqn:Ewf;
      [cbn [snd]; split; [exact hm|]; repeat split; reflexivity|].
    destruct (code_hash c1 s) as [v1 s1] eqn:E1.
    destruct (code_hash c2 s1) as [v2 s2] eqn:E2.
    assert (hs1 : s1 = snd (code_hash c1 s)) by (rewrite E1; reflexivity).
    assert (hm1 : memo_inv s1) by (rewrite hs1; exact (memo_inv_code_hash c1 e1 s hm g1 hi1)).
    assert (hc1 : ((s1.(st_memo)).(m_codes)) = ((s.(st_memo)).(m_codes)))
      by (rewrite hs1; apply (proj1 (code_hash_memo c1 s))).
    assert (hp1 : s1.(st_heap) = s.(st_heap) /\ s1.(st_next) = s.(st_next)
                  /\ s1.(st_room) = s.(st_room) /\ s1.(st_steps) = s.(st_steps)
                  /\ s1.(st_gam) = s.(st_gam))
      by (rewrite hs1; exact (code_hash_state c1 s)).
    rewrite <- hc1 in g1, g2.
    assert (hs2 : s2 = snd (code_hash c2 s1)) by (rewrite E2; reflexivity).
    assert (hm2 : memo_inv s2)
      by (rewrite hs2; exact (memo_inv_code_hash c2 e2 s1 hm1 g2 hi2)).
    assert (hc2 : ((s2.(st_memo)).(m_codes)) = ((s1.(st_memo)).(m_codes)))
      by (rewrite hs2; apply (proj1 (code_hash_memo c2 s1))).
    assert (hp2 : s2.(st_heap) = s1.(st_heap) /\ s2.(st_next) = s1.(st_next)
                  /\ s2.(st_room) = s1.(st_room) /\ s2.(st_steps) = s1.(st_steps)
                  /\ s2.(st_gam) = s1.(st_gam))
      by (rewrite hs2; exact (code_hash_state c2 s1)).
    rewrite <- hc2 in g1, g2.
    destruct hp1 as [p11 [p12 [p13 [p14 p15]]]].
    destruct hp2 as [p21 [p22 [p23 [p24 p25]]]].
    destruct (negb (N.eqb v1 v2)) eqn:Eh; cbn [snd].
    { split; [exact hm2|]; repeat split; congruence. }
    destruct (ceq_get c1 c2 s2) as [b|] eqn:Ec; cbn [snd].
    { split; [exact hm2|]; repeat split; congruence. }
    split; [exact (memo_inv_ceq_set c1 c2 e1 e2 s2 hm2 g1 hi1 g2 hi2)|].
    split; [rewrite (proj1 (ceq_set_memo c1 c2 _ s2)); congruence|].
    split; [rewrite (proj1 (ceq_set_state c1 c2 _ s2)); congruence|].
    split; [rewrite (proj1 (proj2 (ceq_set_state c1 c2 _ s2))); congruence|].
    split; [rewrite (proj1 (proj2 (proj2 (ceq_set_state c1 c2 _ s2)))); congruence|].
    split; [rewrite (proj1 (proj2 (proj2 (proj2 (ceq_set_state c1 c2 _ s2))))); congruence|].
    rewrite (proj2 (proj2 (proj2 (proj2 (ceq_set_state c1 c2 _ s2))))); congruence.
  Qed.

  Lemma memo_inv_delta (kn : kername) (ui : Instance.t) (s : cbn_state)
      (r : option code) (s' : cbn_state) :
    memo_inv s -> delta X_type X kn ui s = COk (r, s') -> memo_inv s'.
  Proof.
    intros [hf [ho [hh [hq hd]]]] he. unfold memo_inv.
    split; [exact (delta_fresh kn ui s r s' hf he)|].
    split; [exact (delta_once_ok kn ui s r s' hf ho he)|].
    split; [exact (delta_hash_ok kn ui s r s' hf hh he)|].
    split; [exact (delta_ceq_ok kn ui s r s' hf hq he)
           | exact (delta_ok_pres kn ui s r s' hf hd he)].
  Qed.

End Memo.
