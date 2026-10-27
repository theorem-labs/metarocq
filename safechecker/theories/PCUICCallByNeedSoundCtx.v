(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC.

Import CanonicalTries.

(** * BET-298 step 2c: the start of a call and the reading of a context variable

  [PCUICCallByNeedSound] says what a machine structure stands for ([repr_addr] and its
  companions) and what a good state is ([state_ok]). This file adds the two invariants that
  speak of the maps a call starts with, and the facts the comparison proof needs about the
  start of a call:

  - [gam_ok lvl s]: every cell [st_gam] holds for the context entry [j] stands, at [lvl]
    levels in scope, for the term that entry denotes ([ctx_den]): the body lifted over the
    entries between it and the hole, or the variable of the entry as a de Bruijn index. It
    holds vacuously of [cbn_init], and [gam] (the machine's context lookup, which allocates
    the cell on first use) keeps it: a hit returns a cell that already stands for the right
    term, a miss allocates one that does.
  - [memo_ok s]: every index of the code table holds an entry whose root code is the one
    [new_entry] builds, with the universe check [new_entry] recorded. [memo_add_entry] keeps
    it, and the code [new_entry] returns satisfies [code_inv] for the entry it added.
    [code_inv_child_step] carries [code_inv] along the machine's child codes.
  - the frame of a call: the state [cbn_run] hands to [conv_term] satisfies the three
    invariants, and the suspension of an input term in the empty environment stands for that
    term itself. This is the "roots in" end of the soundness argument.
  - [cbn_conv] answers [true] only through [CbnYes], and [stress] enters the machine only
    through [gc_due] in [alloc].

  A collection is the collector's ([PCUICCallByNeedSoundGC]): [collect_pres], the statement
  that a collection keeps [gam_ok] and [heap_nofwd] and re-establishes [state_ok], is proved
  here from its [collect_sound], so no lemma of this file carries a collector hypothesis.
  [heap_nofwd] (no forwarding pointer in the machine's heap between collections) is what
  [collect_sound] asks of its input, so every invariant of a call carries it. *)

(** ** Field equations used as rewrites *)

Lemma set_gam_heap (g : PTree.t haddr) (s : cbn_state) :
  (set_gam g s).(st_heap) = s.(st_heap).
Proof. reflexivity. Qed.

Lemma set_gam_next (g : PTree.t haddr) (s : cbn_state) :
  (set_gam g s).(st_next) = s.(st_next).
Proof. reflexivity. Qed.

Lemma set_gam_gam (g : PTree.t haddr) (s : cbn_state) : (set_gam g s).(st_gam) = g.
Proof. reflexivity. Qed.

Lemma set_gam_memo (g : PTree.t haddr) (s : cbn_state) :
  (set_gam g s).(st_memo) = s.(st_memo).
Proof. reflexivity. Qed.

Lemma set_memo_heap (m : cbn_memo) (s : cbn_state) :
  (set_memo m s).(st_heap) = s.(st_heap).
Proof. reflexivity. Qed.

Lemma set_memo_gam (m : cbn_memo) (s : cbn_state) : (set_memo m s).(st_gam) = s.(st_gam).
Proof. reflexivity. Qed.

Lemma alloc_now_gam (cl : cbn_cell) (s : cbn_state) :
  (snd (alloc_now cl s)).(st_gam) = s.(st_gam).
Proof. reflexivity. Qed.

Lemma alloc_now_memo (cl : cbn_cell) (s : cbn_state) :
  (snd (alloc_now cl s)).(st_memo) = s.(st_memo).
Proof. reflexivity. Qed.

Lemma alloc_now_heap (cl : cbn_cell) (s : cbn_state) :
  (snd (alloc_now cl s)).(st_heap) = bh_cons cl (s.(st_heap)).
Proof. reflexivity. Qed.

Lemma key_neq_of_eqb (p q : String2pos.positive) : key_eqb p q = false -> p <> q.
Proof. intros he ->. rewrite (proj2 (key_eqb_spec q q) eq_refl) in he. discriminate. Qed.

(** ** The shape of a collection

  The collector renames [st_gam] and the roots into a fresh heap; it keeps the code table
  and the step budget. *)

Lemma rn_roots_cons {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (r : root)
    (l : list root) (g : G) :
  rn_roots f (r :: l) g =
  match rn_root f r g with
  | COk (r', g1) =>
    match rn_roots f l g1 with
    | COk (l', g2) => COk (r' :: l', g2)
    | CFail w => CFail w
    end
  | CFail w => CFail w
  end.
Proof. reflexivity. Qed.

Lemma rn_root_RC {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) (cl : cbn_cell) (g : G) :
  rn_root f (RC cl) g =
  match rn_cell f cl g with
  | COk (cl', g') => COk (RC cl', g')
  | CFail w => CFail w
  end.
Proof. reflexivity. Qed.

Lemma collect_inv (rs rs' : list root) (s s' : cbn_state) :
  collect rs s = COk (rs', s') ->
  exists (gm : PTree.t haddr) (g1 g2 : gc_state),
    rn_roots (gc_copy (fuel_of_pos (s.(st_next)) (fun _ : unit => FO))) rs g1
    = COk (rs', g2)
    /\ s' = mkState (g2.(g_heap)) (g2.(g_next))
              (gc_room (N.sub (Npos (g2.(g_next))) (Npos (s.(st_next)))))
              (s.(st_steps)) gm (s.(st_memo)).
Proof.
  intros e. unfold collect in e. cbv zeta in e.
  match type of e with
  | context [match ?X with COk _ => _ | CFail _ => _ end] =>
    destruct X as [[gm g1]|w] eqn:E1
  end; [|discriminate].
  match type of e with
  | context [match ?X with COk _ => _ | CFail _ => _ end] =>
    destruct X as [[l g2]|w] eqn:E2
  end; [|discriminate].
  injection e as e1 e2. subst rs' s'. exists gm, g1, g2. split; [exact E2 | reflexivity].
Qed.

Lemma collect_memo (rs rs' : list root) (s s' : cbn_state) :
  collect rs s = COk (rs', s') -> s'.(st_memo) = s.(st_memo).
Proof.
  intros e. destruct (collect_inv rs rs' s s' e) as [gm [g1 [g2 [_ ->]]]]. reflexivity.
Qed.

(** A cell the collector copies unchanged comes back as the head of the roots. *)
Lemma collect_cons_cell (cl : cbn_cell) (rs rs' : list root) (s s' : cbn_state) :
  (forall (G : Type) (f : haddr -> G -> cbn_res (haddr * G)) (g : G),
      rn_cell f cl g = COk (cl, g)) ->
  collect (RC cl :: rs) s = COk (rs', s') ->
  exists rs2 : list root, rs' = RC cl :: rs2.
Proof.
  intros hrn e. destruct (collect_inv _ _ _ _ e) as [gm [g1 [g2 [hr _]]]].
  rewrite rn_roots_cons, rn_root_RC, hrn in hr.
  match type of hr with
  | context [match ?X with COk _ => _ | CFail _ => _ end] =>
    destruct X as [[l g3]|w] eqn:E2
  end; [|discriminate].
  injection hr as hr1 hr2. exists l. now symmetry.
Qed.

(** ** No forwarding pointer between collections

  [collect_sound] asks [heap_nofwd] of the heap it is given, so the machine must keep it
  between collections: a [CFwd] is written only by the collector, and only in the old heap
  it then throws away. *)

Lemma heap_nofwd_holes (p : positive) : heap_nofwd (bh_holes p).
Proof. intros a a' e. rewrite bh_get_holes in e. discriminate. Qed.

(** A cell that holds no address is not a forwarding pointer. *)
Lemma ad_cell_nil_not_fwd (cl : cbn_cell) (b : haddr) : ad_cell cl = [] -> cl <> CFwd b.
Proof. destruct cl; intros h e; discriminate. Qed.

Lemma heap_nofwd_alloc_now (lo : positive) (cl : cbn_cell) (s : cbn_state) :
  bh_ok lo (s.(st_next)) (s.(st_heap)) -> heap_nofwd (s.(st_heap)) ->
  (forall b : haddr, cl <> CFwd b) ->
  heap_nofwd ((snd (alloc_now cl s)).(st_heap)).
Proof.
  intros hb hnf hcl a a' e. rewrite alloc_now_heap in e.
  destruct (haddr_dec a (HAddr (s.(st_next)))) as [->|hne].
  - erewrite bh_digits_get_cons_new in e by eauto using bh_ok_digits.
    injection e as e. exact (hcl a' e).
  - erewrite bh_digits_get_cons_old in e by eauto using bh_ok_digits.
    exact (hnf _ _ e).
Qed.

Lemma heap_nofwd_heap_upd (a : haddr) (cl : cbn_cell) (s s' : cbn_state) :
  heap_nofwd (s.(st_heap)) -> (forall b : haddr, cl <> CFwd b) ->
  heap_upd a cl s = Some s' -> heap_nofwd (s'.(st_heap)).
Proof.
  intros hnf hcl e. unfold heap_upd in e.
  destruct (bh_upd a cl (s.(st_heap))) as [h'|] eqn:hu; [|discriminate].
  cbn in e. injection e as e. subst s'. cbn [st_heap].
  intros b b' hb. destruct (haddr_dec b a) as [->|hne].
  - rewrite (bh_get_upd_same _ _ _ _ hu) in hb. injection hb as hb. exact (hcl b' hb).
  - rewrite (bh_get_upd_other _ _ _ _ _ hu hne) in hb. exact (hnf _ _ hb).
Qed.

(** ** The collector keeps the keys of [st_gam]

  [collect_sound] says what the image of a key that [st_gam] held reads back to;
  [gam_ok] of the new state needs the other direction, that the renaming invented no key.
  [rn_tree'] maps each node to the same node, so the key sets are the same. *)

Lemma rn_tree'_get_some {G : Type} (f : haddr -> G -> cbn_res (haddr * G)) :
  forall (m : PTree.tree' haddr) (g : G) (m' : PTree.tree' haddr) (g' : G),
    rn_tree' f m g = COk (m', g') ->
    forall (p : String2pos.positive) (a' : haddr),
      PTree.get' p m' = Some a' -> exists a : haddr, PTree.get' p m = Some a.
Proof.
  induction m as [r ihr|x|x r ihr|l ihl|l ihl r ihr|l ihl x|l ihl x r ihr];
    intros g m' g' he p a' hp; simpl in he.
  - destruct (rn_tree' f r g) as [[r' g1]|w] eqn:e1; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    exact (ihr _ _ _ e1 q a' hp).
  - destruct (f x g) as [[x' g1]|w] eqn:e1; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    eexists; reflexivity.
  - destruct (f x g) as [[x' g1]|w] eqn:e1; [|discriminate].
    destruct (rn_tree' f r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    + exact (ihr _ _ _ e2 q a' hp).
    + eexists; reflexivity.
  - destruct (rn_tree' f l g) as [[l' g1]|w] eqn:e1; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    exact (ihl _ _ _ e1 q a' hp).
  - destruct (rn_tree' f l g) as [[l' g1]|w] eqn:e1; [|discriminate].
    destruct (rn_tree' f r g1) as [[r' g2]|w] eqn:e2; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    + exact (ihr _ _ _ e2 q a' hp).
    + exact (ihl _ _ _ e1 q a' hp).
  - destruct (rn_tree' f l g) as [[l' g1]|w] eqn:e1; [|discriminate].
    destruct (f x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    + exact (ihl _ _ _ e1 q a' hp).
    + eexists; reflexivity.
  - destruct (rn_tree' f l g) as [[l' g1]|w] eqn:e1; [|discriminate].
    destruct (f x g1) as [[x' g2]|w] eqn:e2; [|discriminate].
    destruct (rn_tree' f r g2) as [[r' g3]|w] eqn:e3; [|discriminate].
    injection he as he1 he2; subst m' g'.
    destruct p as [q|q|]; simpl in hp |- *; try discriminate.
    + exact (ihr _ _ _ e3 q a' hp).
    + exact (ihl _ _ _ e1 q a' hp).
    + eexists; reflexivity.
Qed.

Lemma rn_ptree_get_some {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
    (m : PTree.t haddr) (g : G) (m' : PTree.t haddr) (g' : G) :
  rn_ptree f m g = COk (m', g') ->
  forall (p : String2pos.positive) (a' : haddr),
    PTree.get p m' = Some a' -> exists a : haddr, PTree.get p m = Some a.
Proof.
  destruct m as [|m]; unfold rn_ptree; intros he p a' hp.
  - injection he as he1 he2; subst m'. discriminate hp.
  - destruct (rn_tree' f m g) as [[m2 g1]|w] eqn:e1; [|discriminate].
    injection he as he1 he2; subst m' g'.
    exact (rn_tree'_get_some f m g m2 g1 e1 p a' hp).
Qed.

Lemma collect_gam_some (rs rs' : list root) (s s' : cbn_state) :
  collect rs s = COk (rs', s') ->
  forall (k : String2pos.positive) (a' : haddr),
    PTree.get k (s'.(st_gam)) = Some a' ->
    exists a : haddr, PTree.get k (s.(st_gam)) = Some a.
Proof.
  intros he. rewrite collect_eq in he.
  destruct (rn_ptree (gc_copy (fuel_of_pos (s.(st_next)) (fun _ => FO))) (s.(st_gam))
              (mkGc (s.(st_heap)) (bh_holes (s.(st_next))) (s.(st_next))))
    as [[gm g1]|w1] eqn:e1; [|discriminate].
  destruct (rn_roots (gc_copy (fuel_of_pos (s.(st_next)) (fun _ => FO))) rs g1)
    as [[rs2 g2]|w2] eqn:e2; [|discriminate].
  injection he as he1 he2. subst rs' s'. cbn [st_gam].
  intros k a' hk. exact (rn_ptree_get_some _ _ _ _ _ e1 k a' hk).
Qed.

(** ** [stress] enters the machine only through [gc_due] in [alloc] *)

Lemma gc_due_true (s : cbn_state) : gc_due true s = true.
Proof. reflexivity. Qed.

Lemma gc_due_false (s : cbn_state) : gc_due false s = true <-> s.(st_room) = 0%N.
Proof.
  unfold gc_due. destruct (s.(st_room)) eqn:E; cbn;
    split; intros h; (reflexivity || discriminate h || discriminate).
Qed.

(** [alloc] is the only function of the machine that reads [stress], and it reads it only
  through [gc_due]: two values of [stress] that agree there allocate the same way. *)
Lemma alloc_gc_due (b1 b2 : bool) (cl : cbn_cell) (rs : list root) (s : cbn_state) :
  gc_due b1 s = gc_due b2 s -> alloc b1 cl rs s = alloc b2 cl rs s.
Proof. intros h. unfold alloc. rewrite h. reflexivity. Qed.

Lemma alloc_no_gc (b : bool) (cl : cbn_cell) (rs : list root) (s : cbn_state) :
  gc_due b s = false ->
  alloc b cl rs s = COk (fst (alloc_now cl s), rs, snd (alloc_now cl s)).
Proof. intros h. unfold alloc. rewrite h. destruct (alloc_now cl s). reflexivity. Qed.

Lemma alloc_gc (b : bool) (cl : cbn_cell) (rs : list root) (s : cbn_state) :
  gc_due b s = true ->
  alloc b cl rs s
  = match collect (RC cl :: rs) s with
    | COk (RC cl' :: rs', s') => COk (fst (alloc_now cl' s'), rs', snd (alloc_now cl' s'))
    | COk _ => CFail WRoots
    | CFail w => CFail w
    end.
Proof.
  intros h. unfold alloc. rewrite h.
  destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w]; [|reflexivity].
  destruct rs2 as [|r rs2]; [reflexivity|]. destruct r; reflexivity.
Qed.

Section CtxMemo.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat). (* nctx = #|Γ| *)
  Context (stress : bool).

  (** ** Read-back of the structures a start or a context lookup builds *)

  (** A suspension with no slots: the read-back lifts the code and substitutes nothing. *)
  Lemma repr_susp_empty_env (H : bheap cbn_cell) (lvl goff : nat) (t : term) :
    repr_susp nctx H lvl (mkEnv [] 0 goff) t (lift (lvl - nctx + goff) 0 t).
  Proof.
    pose proof (repr_susp_intro nctx H lvl [] 0 goff t [] (repr_slots_nil nctx H lvl)) as h.
    now rewrite subst_empty in h.
  Qed.

  (** The suspension [cbn_run] starts from stands for the input term itself. *)
  Lemma repr_susp_env_empty (H : bheap cbn_cell) (t : term) :
    repr_susp nctx H nctx env_empty t t.
  Proof.
    pose proof (repr_susp_empty_env H nctx 0 t) as h.
    rewrite Nat.sub_diag in h. cbn [Nat.add] in h. rewrite lift0_id in h. exact h.
  Qed.

  (** The cell [gam] builds for a context entry with a body. *)
  Lemma repr_cell_ctx_body (H : bheap cbn_cell) (lvl j : nat) (c : code) :
    repr_cell nctx H lvl (CSusp [] 0 (S j) c) (lift (lvl - nctx + S j) 0 c.(c_term)).
  Proof. constructor. apply repr_susp_empty_env. Qed.

  (** The cell [gam] builds for a context entry without a body. *)
  Lemma repr_cell_ctx_var (H : bheap cbn_cell) (lvl l : nat) :
    repr_cell nctx H lvl (CDone (VNeu (NVar l) [])) (tRel (lvl - S l)).
  Proof.
    constructor. exact (repr_VNeuVar nctx H lvl l [] [] (repr_addrs_nil nctx H lvl)).
  Qed.

  (** ** What [new_entry] does to the state *)

  Lemma new_entry_code (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    fst (new_entry X_type X t u ns s)
    = mkCode ((s.(st_memo)).(m_ncode)) path_nil (inst_code u t).
  Proof. reflexivity. Qed.

  Lemma new_entry_codes (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    ((snd (new_entry X_type X t u ns s)).(st_memo)).(m_codes)
    = PTree.set ((s.(st_memo)).(m_ncode))
        (mkEntry t u ns (wf_term_univs X_type X (inst_code u t)))
        ((s.(st_memo)).(m_codes)).
  Proof. reflexivity. Qed.

  Lemma new_entry_ncode (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    ((snd (new_entry X_type X t u ns s)).(st_memo)).(m_ncode)
    = key_succ ((s.(st_memo)).(m_ncode)).
  Proof. reflexivity. Qed.

  Lemma new_entry_heap (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    (snd (new_entry X_type X t u ns s)).(st_heap) = s.(st_heap).
  Proof. reflexivity. Qed.

  Lemma new_entry_next (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    (snd (new_entry X_type X t u ns s)).(st_next) = s.(st_next).
  Proof. reflexivity. Qed.

  Lemma new_entry_gam (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    (snd (new_entry X_type X t u ns s)).(st_gam) = s.(st_gam).
  Proof. reflexivity. Qed.

  Lemma new_entry_term (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    (fst (new_entry X_type X t u ns s)).(c_term) = inst_code u t.
  Proof. reflexivity. Qed.

  Lemma new_entry_entry (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    (fst (new_entry X_type X t u ns s)).(c_entry) = (s.(st_memo)).(m_ncode).
  Proof. reflexivity. Qed.

  (** ** The entry invariant *)

  (** Every index of the code table holds an entry whose root code is the one [new_entry]
    builds for it, carrying the universe check [new_entry] recorded. *)
  Definition memo_ok (s : cbn_state) : Prop :=
    forall (i : String2pos.positive) (e : code_entry),
      PTree.get i ((s.(st_memo)).(m_codes)) = Some e ->
      code_inv e (mkCode i path_nil (inst_code e.(ce_inst) e.(ce_term)))
      /\ e.(ce_wf) = wf_term_univs X_type X (inst_code e.(ce_inst) e.(ce_term)).

  Lemma memo_ok_init : memo_ok cbn_init.
  Proof.
    intros i e h. unfold cbn_init, memo_empty in h. cbn [st_memo m_codes] in h.
    rewrite PTree.gempty in h. discriminate.
  Qed.

  (** [memo_ok] reads only the code table, so every operation that leaves it alone keeps the
    invariant. *)
  Lemma memo_ok_codes (s s' : cbn_state) :
    ((s'.(st_memo)).(m_codes)) = ((s.(st_memo)).(m_codes)) -> memo_ok s -> memo_ok s'.
  Proof. intros he h i e hi. rewrite he in hi. exact (h i e hi). Qed.

  Lemma memo_ok_alloc_now (cl : cbn_cell) (s : cbn_state) :
    memo_ok s -> memo_ok (snd (alloc_now cl s)).
  Proof. apply memo_ok_codes. rewrite alloc_now_memo. reflexivity. Qed.

  Lemma memo_ok_set_gam (g : PTree.t haddr) (s : cbn_state) :
    memo_ok s -> memo_ok (set_gam g s).
  Proof. apply memo_ok_codes. rewrite set_gam_memo. reflexivity. Qed.

  Lemma memo_ok_collect (rs rs' : list root) (s s' : cbn_state) :
    collect rs s = COk (rs', s') -> memo_ok s -> memo_ok s'.
  Proof. intros e. apply memo_ok_codes. rewrite (collect_memo rs rs' s s' e). reflexivity. Qed.

  Lemma memo_ok_tick (s s' : cbn_state) : tick s = Some s' -> memo_ok s -> memo_ok s'.
  Proof.
    intros e. apply memo_ok_codes. unfold tick in e. destruct (s.(st_steps)); [discriminate|].
    injection e as <-. reflexivity.
  Qed.

  Lemma memo_ok_heap_upd (a : haddr) (cl : cbn_cell) (s s' : cbn_state) :
    heap_upd a cl s = Some s' -> memo_ok s -> memo_ok s'.
  Proof.
    intros e. apply memo_ok_codes.
    destruct (heap_upd_fields a cl s s' e) as [_ [_ [_ [_ h]]]]. rewrite h. reflexivity.
  Qed.

  (** Adding an entry that records its own universe check keeps the invariant. *)
  Lemma memo_add_entry_ok (e : code_entry) (s : cbn_state) :
    memo_ok s ->
    e.(ce_wf) = wf_term_univs X_type X (inst_code e.(ce_inst) e.(ce_term)) ->
    memo_ok (set_memo (snd (memo_add_entry e (s.(st_memo)))) s).
  Proof.
    intros h hw i e' hi.
    change (((set_memo (snd (memo_add_entry e (s.(st_memo)))) s).(st_memo)).(m_codes))
      with (PTree.set ((s.(st_memo)).(m_ncode)) e ((s.(st_memo)).(m_codes))) in hi.
    destruct (key_eqb i ((s.(st_memo)).(m_ncode))) eqn:E.
    - apply key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
      injection hi as hi; subst e'. split; [apply code_inv_root | exact hw].
    - rewrite PTree.gso in hi by (apply key_neq_of_eqb, E). exact (h i e' hi).
  Qed.

  Lemma new_entry_memo_ok (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    memo_ok s -> memo_ok (snd (new_entry X_type X t u ns s)).
  Proof.
    intros h i e hi. rewrite new_entry_codes in hi.
    destruct (key_eqb i ((s.(st_memo)).(m_ncode))) eqn:E.
    - apply key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
      injection hi as hi; subst e. split; [apply code_inv_root | reflexivity].
    - rewrite PTree.gso in hi by (apply key_neq_of_eqb, E). exact (h i e hi).
  Qed.

  (** The code [new_entry] returns satisfies [code_inv] for the entry it added, and the
    table holds that entry at the code's index. *)
  Lemma new_entry_code_inv (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    code_inv (mkEntry t u ns (wf_term_univs X_type X (inst_code u t)))
      (fst (new_entry X_type X t u ns s)).
  Proof. rewrite new_entry_code. apply code_inv_root. Qed.

  Lemma new_entry_in_table (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    PTree.get ((fst (new_entry X_type X t u ns s)).(c_entry))
      (((snd (new_entry X_type X t u ns s)).(st_memo)).(m_codes))
    = Some (mkEntry t u ns (wf_term_univs X_type X (inst_code u t))).
  Proof. rewrite new_entry_codes, new_entry_entry. apply PTree.gss. Qed.

  Lemma new_entry_wf (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state) :
    entry_wf ((fst (new_entry X_type X t u ns s)).(c_entry))
      (snd (new_entry X_type X t u ns s))
    = wf_term_univs X_type X (inst_code u t).
  Proof. unfold entry_wf. rewrite new_entry_in_table. reflexivity. Qed.

  (** Under [memo_ok], the boolean [entry_wf] reads is the universe check of the entry's
    root term, and the root code of a table entry satisfies [code_inv]. *)
  Lemma memo_entry_wf (s : cbn_state) (i : String2pos.positive) (e : code_entry) :
    memo_ok s -> PTree.get i ((s.(st_memo)).(m_codes)) = Some e ->
    entry_wf i s = wf_term_univs X_type X (inst_code e.(ce_inst) e.(ce_term)).
  Proof. intros h hi. unfold entry_wf. rewrite hi. exact (proj2 (h i e hi)). Qed.

  Lemma memo_code_inv_root (s : cbn_state) (i : String2pos.positive) (e : code_entry) :
    memo_ok s -> PTree.get i ((s.(st_memo)).(m_codes)) = Some e ->
    code_inv e (mkCode i path_nil (inst_code e.(ce_inst) e.(ce_term))).
  Proof. intros h hi. exact (proj1 (h i e hi)). Qed.

  (** ** The child codes the machine builds

    [child_step t k t'] lists the steps the machine's traversal takes: one constructor per
    [code_inv_child_*] lemma of step 2a. [code_inv_child_step] carries [code_inv] along any
    of them, so a proof over the traversal needs one lemma, not sixteen. *)
  Inductive child_step : term -> N -> term -> Prop :=
  | cs_app_fun f a : child_step (tApp f a) 0 f
  | cs_app_arg f a : child_step (tApp f a) 1 a
  | cs_lambda_dom na d b : child_step (tLambda na d b) 0 d
  | cs_lambda_body na d b : child_step (tLambda na d b) 1 b
  | cs_prod_dom na d b : child_step (tProd na d b) 0 d
  | cs_prod_body na d b : child_step (tProd na d b) 1 b
  | cs_letin_def na b ty body : child_step (tLetIn na b ty body) 0 b
  | cs_letin_type na b ty body : child_step (tLetIn na b ty body) 1 ty
  | cs_letin_body na b ty body : child_step (tLetIn na b ty body) 2 body
  | cs_case_scrut ci p scrut brs : child_step (tCase ci p scrut brs) 0 scrut
  | cs_case_return ci p scrut brs : child_step (tCase ci p scrut brs) 1 p.(preturn)
  | cs_case_param ci p scrut brs i t :
      nth_error p.(pparams) (N.to_nat i) = Some t ->
      child_step (tCase ci p scrut brs) (case_param_step i) t
  | cs_case_branch ci p scrut brs i br :
      nth_error brs (N.to_nat i) = Some br ->
      child_step (tCase ci p scrut brs) (case_branch_step i) br.(bbody)
  | cs_proj pr a : child_step (tProj pr a) 0 a
  | cs_fix mfix idx k d :
      nth_error mfix (N.to_nat k) = Some d -> child_step (tFix mfix idx) k d.(dbody)
  | cs_cofix mfix idx k d :
      nth_error mfix (N.to_nat k) = Some d -> child_step (tCoFix mfix idx) k d.(dbody).

  Lemma code_inv_child_step (ce : code_entry) (c : code) (k : N) (t : term) :
    code_inv ce c -> child_step c.(c_term) k t -> code_inv ce (child c k t).
  Proof.
    intros hc hs. inversion hs; subst;
      eauto using code_inv_child_app_fun, code_inv_child_app_arg,
        code_inv_child_lambda_dom, code_inv_child_lambda_body,
        code_inv_child_prod_dom, code_inv_child_prod_body,
        code_inv_child_letin_def, code_inv_child_letin_type, code_inv_child_letin_body,
        code_inv_child_case_scrut, code_inv_child_case_return,
        code_inv_child_case_param, code_inv_child_case_branch,
        code_inv_child_proj, code_inv_child_fix, code_inv_child_cofix.
  Qed.

  (** ** The context map stands for the context *)

  (** The term the [j]th entry of [Γ] denotes with [lvl] levels in scope: its body lifted
    over the [S j] entries between it and the hole, or, for an entry without a body, the de
    Bruijn index of the level [nctx - S j] the machine gives it. *)
  Definition ctx_den (lvl j : nat) : option term :=
    match nth_error Γ j with
    | None => None
    | Some decl =>
      match decl.(decl_body) with
      | Some b => Some (lift (lvl - nctx + S j) 0 b)
      | None => Some (tRel (lvl - S (nctx - S j)))
      end
    end.

  Definition gam_ok (lvl : nat) (s : cbn_state) : Prop :=
    forall (j : nat) (a : haddr),
      PTree.get (key_of_succ_nat j) (s.(st_gam)) = Some a ->
      exists t : term, ctx_den lvl j = Some t /\ repr_addr nctx (s.(st_heap)) lvl a t.

  Lemma gam_ok_init (lvl : nat) : gam_ok lvl cbn_init.
  Proof.
    intros j a h. unfold cbn_init in h. cbn [st_gam] in h.
    rewrite PTree.gempty in h. discriminate.
  Qed.

  (** A state that keeps [st_gam] and only grows the heap keeps the invariant. *)
  Lemma gam_ok_heap_le (lvl : nat) (s s' : cbn_state) :
    s'.(st_gam) = s.(st_gam) -> heap_le (s.(st_heap)) (s'.(st_heap)) ->
    gam_ok lvl s -> gam_ok lvl s'.
  Proof.
    intros hg hle h j a e. rewrite hg in e. destruct (h j a e) as [t [h1 h2]].
    exists t. split; [exact h1 | exact (repr_addr_mono nctx _ _ hle _ _ _ h2)].
  Qed.

  Lemma state_ok_set_memo (lo : positive) (m : cbn_memo) (s : cbn_state) :
    state_ok lo s -> state_ok lo (set_memo m s).
  Proof. intros [h1 h2 h3]. split; assumption. Qed.

  Lemma gam_ok_set_memo (lvl : nat) (m : cbn_memo) (s : cbn_state) :
    gam_ok lvl s -> gam_ok lvl (set_memo m s).
  Proof. intros h. exact h. Qed.

  Lemma new_entry_state_ok (lo : positive) (t : term) (u : Instance.t) (ns : code_ns)
      (s : cbn_state) :
    state_ok lo s -> state_ok lo (snd (new_entry X_type X t u ns s)).
  Proof.
    intros [h1 h2 h3]. split; [rewrite new_entry_next, new_entry_heap; exact h1 | | ].
    - rewrite new_entry_next, new_entry_heap. exact h2.
    - rewrite new_entry_next, new_entry_gam. exact h3.
  Qed.

  Lemma new_entry_gam_ok (lvl : nat) (t : term) (u : Instance.t) (ns : code_ns)
      (s : cbn_state) :
    gam_ok lvl s -> gam_ok lvl (snd (new_entry X_type X t u ns s)).
  Proof.
    intros h. apply (gam_ok_heap_le lvl s);
      [apply new_entry_gam | rewrite new_entry_heap; apply heap_le_refl | exact h].
  Qed.

  (** Writing the cell of the entry [j] keeps the invariant, if that cell stands for what
    the entry denotes. *)
  Lemma gam_ok_set (lvl j : nat) (a : haddr) (t : term) (s : cbn_state) :
    gam_ok lvl s -> ctx_den lvl j = Some t -> repr_addr nctx (s.(st_heap)) lvl a t ->
    gam_ok lvl (set_gam (PTree.set (key_of_succ_nat j) a (s.(st_gam))) s).
  Proof.
    intros hg hd hr j' a' e. rewrite set_gam_gam in e. rewrite set_gam_heap.
    destruct (key_eqb (key_of_succ_nat j') (key_of_succ_nat j)) eqn:E.
    - apply key_eqb_spec, key_of_succ_nat_inj in E; subst j'.
      rewrite PTree.gss in e. injection e as e; subst a'.
      exists t. split; assumption.
    - rewrite PTree.gso in e by (apply key_neq_of_eqb, E). exact (hg j' a' e).
  Qed.

  (** Recording the address of the entry [j] keeps the state invariant, if that address is
    one the heap has. *)
  Lemma state_ok_set_gam (lo : positive) (j : nat) (a : haddr) (s : cbn_state) :
    state_ok lo s -> (lo <= ha_p a)%positive -> (ha_p a < s.(st_next))%positive ->
    state_ok lo (set_gam (PTree.set (key_of_succ_nat j) a (s.(st_gam))) s).
  Proof.
    intros [h1 h2 h3] hlo hhi. split; [exact h1 | exact h2 |].
    intros k a' e. rewrite set_gam_gam in e. rewrite set_gam_next.
    destruct (key_eqb k (key_of_succ_nat j)) eqn:Ek.
    - apply key_eqb_spec in Ek; subst k. rewrite PTree.gss in e.
      injection e as e; subst a'. split; assumption.
    - rewrite PTree.gso in e by (apply key_neq_of_eqb, Ek). exact (h3 k a' e).
  Qed.

  (** ** Allocation of a cell that holds no address *)

  Lemma rn_cell_ctx_body {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
      (j : nat) (c : code) (g : G) :
    rn_cell f (CSusp [] 0 (S j) c) g = COk (CSusp [] 0 (S j) c, g).
  Proof. reflexivity. Qed.

  Lemma rn_cell_ctx_var {G : Type} (f : haddr -> G -> cbn_res (haddr * G))
      (l : nat) (g : G) :
    rn_cell f (CDone (VNeu (NVar l) [])) g = COk (CDone (VNeu (NVar l) []), g).
  Proof. reflexivity. Qed.

  (** An allocation of a cell that holds no address: the state, the context map and the
    absence of forwarding pointers stay good, and the new address stands for what the cell
    stands for. *)
  Lemma alloc_now_addr_free (lo : positive) (lvl : nat) (cl : cbn_cell) (t : term)
      (s : cbn_state) :
    state_ok lo s -> gam_ok lvl s -> heap_nofwd (s.(st_heap)) -> ad_cell cl = [] ->
    (forall H : bheap cbn_cell, repr_cell nctx H lvl cl t) ->
    state_ok lo (snd (alloc_now cl s)) /\ gam_ok lvl (snd (alloc_now cl s))
    /\ heap_nofwd ((snd (alloc_now cl s)).(st_heap))
    /\ repr_addr nctx ((snd (alloc_now cl s)).(st_heap)) lvl (fst (alloc_now cl s)) t
    /\ (lo <= ha_p (fst (alloc_now cl s)))%positive
    /\ (ha_p (fst (alloc_now cl s)) < (snd (alloc_now cl s)).(st_next))%positive.
  Proof.
    intros hs hg hnf had hre.
    assert (hb : bh_ok lo (s.(st_next)) (s.(st_heap))) by (destruct hs as [h _ _]; exact h).
    split; [|split; [|split; [|split; [|split]]]].
    - apply alloc_now_state_ok; [exact hs|]. unfold addrs_in. rewrite had. constructor.
    - apply (gam_ok_heap_le lvl s);
        [apply alloc_now_gam | exact (alloc_now_heap_le lo cl s hb) | exact hg].
    - exact (heap_nofwd_alloc_now lo cl s hb hnf (fun b => ad_cell_nil_not_fwd cl b had)).
    - exact (repr_addr_alloc nctx lo cl s lvl t hb (hre _)).
    - rewrite alloc_now_addr. cbn [ha_p]. exact (bh_ok_le _ _ _ hb).
    - rewrite alloc_now_addr, alloc_now_next. cbn [ha_p]. apply Pos.lt_succ_diag_r.
  Qed.

  (** What a collection keeps, as the lemmas below need it. [collect_sound] of
    [PCUICCallByNeedSoundGC] gives it: it asks [heap_nofwd] of the heap it collects and
    re-establishes [state_ok] at the old [st_next]. *)
  Definition collect_pres (lvl : nat) : Prop :=
    forall (rs rs' : list root) (s s' : cbn_state),
      gam_ok lvl s -> heap_nofwd (s.(st_heap)) -> collect rs s = COk (rs', s') ->
      state_ok (s.(st_next)) s' /\ gam_ok lvl s' /\ heap_nofwd (s'.(st_heap)).

  (** The collector keeps the context map: a key of the new map was a key of the old one
    ([collect_gam_some]), and its address stands for what the old one stood for (the last
    conjunct of [collect_sound]). *)
  Lemma collect_pres_holds (lvl : nat) : collect_pres lvl.
  Proof.
    intros rs rs' s s' hg hnf he.
    destruct (collect_sound nctx rs s rs' s' hnf he) as [hok [hnf' [_ [_ [_ hgam]]]]].
    split; [exact hok|]. split; [|exact hnf'].
    intros j a' hk.
    destruct (collect_gam_some rs rs' s s' he _ _ hk) as [a ha].
    destruct (hg j a ha) as [t [hd hr]].
    destruct (hgam _ _ ha) as [a2 [ha2 hpres]].
    rewrite ha2 in hk. injection hk as hk. subst a2.
    exists t. split; [exact hd | exact (hpres lvl t hr)].
  Qed.

  Lemma alloc_addr_free (lo : positive) (lvl : nat) (cl : cbn_cell) (t : term)
      (rs : list root) (s : cbn_state) (a : haddr) (rs' : list root) (s' : cbn_state) :
    state_ok lo s -> gam_ok lvl s -> memo_ok s -> heap_nofwd (s.(st_heap)) ->
    ad_cell cl = [] ->
    (forall H : bheap cbn_cell, repr_cell nctx H lvl cl t) ->
    (forall (G : Type) (f : haddr -> G -> cbn_res (haddr * G)) (g : G),
        rn_cell f cl g = COk (cl, g)) ->
    alloc stress cl rs s = COk (a, rs', s') ->
    exists lo' : positive,
      state_ok lo' s' /\ gam_ok lvl s' /\ memo_ok s' /\ heap_nofwd (s'.(st_heap))
      /\ repr_addr nctx (s'.(st_heap)) lvl a t
      /\ (lo' <= ha_p a)%positive /\ (ha_p a < s'.(st_next))%positive.
  Proof.
    intros hs hg hm hnf had hre hrn e. unfold alloc in e.
    destruct (gc_due stress s) eqn:Egc.
    - destruct (collect (RC cl :: rs) s) as [[rs2 s2]|w] eqn:Ec; [|discriminate].
      destruct (collect_cons_cell cl rs rs2 s s2 hrn Ec) as [rs3 ->].
      destruct (collect_pres_holds lvl (RC cl :: rs) (RC cl :: rs3) s s2 hg hnf Ec)
        as [hs2 [hg2 hnf2]].
      assert (hm2 : memo_ok s2) by exact (memo_ok_collect _ _ _ _ Ec hm).
      destruct (alloc_now cl s2) as [a2 s3] eqn:Ea.
      injection e as e1 e2 e3. subst a rs' s'.
      destruct (alloc_now_addr_free (s.(st_next)) lvl cl t s2 hs2 hg2 hnf2 had hre)
        as [h1 [h2 [h3 [h4 [h5 h6]]]]].
      rewrite Ea in h1, h2, h3, h4, h5, h6. cbn [fst snd] in h1, h2, h3, h4, h5, h6.
      exists (s.(st_next)). split; [exact h1|]. split; [exact h2|].
      split; [apply (memo_ok_codes s2);
                [rewrite <- (alloc_now_memo cl s2), Ea; reflexivity | exact hm2]|].
      split; [exact h3|]. split; [exact h4|]. split; [exact h5 | exact h6].
    - destruct (alloc_now cl s) as [a2 s3] eqn:Ea.
      injection e as e1 e2 e3. subst a rs' s'.
      destruct (alloc_now_addr_free lo lvl cl t s hs hg hnf had hre)
        as [h1 [h2 [h3 [h4 [h5 h6]]]]].
      rewrite Ea in h1, h2, h3, h4, h5, h6. cbn [fst snd] in h1, h2, h3, h4, h5, h6.
      exists lo. split; [exact h1|]. split; [exact h2|].
      split; [apply (memo_ok_codes s);
                [rewrite <- (alloc_now_memo cl s), Ea; reflexivity | exact hm]|].
      split; [exact h3|]. split; [exact h4|]. split; [exact h5 | exact h6].
  Qed.

  (** The allocation of a context cell, then its record in [st_gam]. *)
  Lemma gam_alloc_set (lo : positive) (lvl j : nat) (cl : cbn_cell) (t : term)
      (rs : list root) (s : cbn_state) (a : haddr) (rs' : list root) (s2 : cbn_state) :
    state_ok lo s -> gam_ok lvl s -> memo_ok s -> heap_nofwd (s.(st_heap)) ->
    ad_cell cl = [] ->
    (forall H : bheap cbn_cell, repr_cell nctx H lvl cl t) ->
    (forall (G : Type) (f : haddr -> G -> cbn_res (haddr * G)) (g : G),
        rn_cell f cl g = COk (cl, g)) ->
    ctx_den lvl j = Some t ->
    alloc stress cl rs s = COk (a, rs', s2) ->
    exists lo' : positive,
      state_ok lo' (set_gam (PTree.set (key_of_succ_nat j) a (s2.(st_gam))) s2)
      /\ gam_ok lvl (set_gam (PTree.set (key_of_succ_nat j) a (s2.(st_gam))) s2)
      /\ memo_ok (set_gam (PTree.set (key_of_succ_nat j) a (s2.(st_gam))) s2)
      /\ heap_nofwd
           ((set_gam (PTree.set (key_of_succ_nat j) a (s2.(st_gam))) s2).(st_heap))
      /\ repr_addr nctx
           ((set_gam (PTree.set (key_of_succ_nat j) a (s2.(st_gam))) s2).(st_heap)) lvl a t.
  Proof.
    intros hs hg hm hnf had hre hrn hd e.
    destruct (alloc_addr_free lo lvl cl t rs s a rs' s2 hs hg hm hnf had hre hrn e)
      as [lo2 [h1 [h2 [h3 [h4 [h5 [h6 h7]]]]]]].
    exists lo2. split; [|split; [|split; [|split]]].
    - exact (state_ok_set_gam lo2 j a s2 h1 h6 h7).
    - exact (gam_ok_set lvl j a t s2 h2 hd h5).
    - apply memo_ok_set_gam, h3.
    - rewrite set_gam_heap. exact h4.
    - rewrite set_gam_heap. exact h5.
  Qed.

  (** ** The context lookup *)

  (** A hit: the machine returns the cell it already has, and that cell stands for what the
    entry denotes. *)
  Lemma gam_hit (j : nat) (a : haddr) (rs : list root) (s : cbn_state) :
    PTree.get (key_of_succ_nat j) (s.(st_gam)) = Some a ->
    gam X_type X Γ nctx stress j rs s = COk (a, rs, s).
  Proof. intros e. unfold gam. cbv zeta. rewrite e. reflexivity. Qed.

  Lemma gam_hit_repr (lvl j : nat) (a : haddr) (s : cbn_state) :
    gam_ok lvl s -> PTree.get (key_of_succ_nat j) (s.(st_gam)) = Some a ->
    exists t : term, ctx_den lvl j = Some t /\ repr_addr nctx (s.(st_heap)) lvl a t.
  Proof. intros hg e. exact (hg j a e). Qed.

  (** A miss: the machine allocates a cell that stands for what the entry denotes, and
    records it. *)
  Lemma gam_miss (lo : positive) (lvl j : nat) (rs : list root) (s : cbn_state)
      (a : haddr) (rs' : list root) (s' : cbn_state) :
    state_ok lo s -> gam_ok lvl s -> memo_ok s -> heap_nofwd (s.(st_heap)) ->
    PTree.get (key_of_succ_nat j) (s.(st_gam)) = None ->
    gam X_type X Γ nctx stress j rs s = COk (a, rs', s') ->
    exists (lo' : positive) (t : term),
      state_ok lo' s' /\ gam_ok lvl s' /\ memo_ok s' /\ heap_nofwd (s'.(st_heap))
      /\ ctx_den lvl j = Some t /\ repr_addr nctx (s'.(st_heap)) lvl a t.
  Proof.
    intros hs hg hm hnf hnone e. unfold gam in e. cbv zeta in e. rewrite hnone in e.
    destruct (nth_error Γ j) as [decl|] eqn:En; [|discriminate].
    destruct (decl.(decl_body)) as [b|] eqn:Eb.
    - rewrite (surjective_pairing (new_entry X_type X b [] (NSCtx j) s)) in e.
      cbv beta iota zeta in e.
      set (c := fst (new_entry X_type X b [] (NSCtx j) s)) in *.
      set (s1 := snd (new_entry X_type X b [] (NSCtx j) s)) in *.
      destruct (alloc stress (CSusp [] 0 (S j) c) rs s1) as [[[a2 rs2] s2]|w] eqn:Ea;
        [|discriminate].
      injection e as e1 e2 e3. subst a rs' s'.
      assert (hs1 : state_ok lo s1) by (apply new_entry_state_ok, hs).
      assert (hg1 : gam_ok lvl s1) by (apply new_entry_gam_ok, hg).
      assert (hm1 : memo_ok s1) by (apply new_entry_memo_ok, hm).
      assert (hnf1 : heap_nofwd (s1.(st_heap)))
        by (unfold s1; rewrite new_entry_heap; exact hnf).
      assert (hd : ctx_den lvl j = Some (lift (lvl - nctx + S j) 0 b))
        by (unfold ctx_den; rewrite En, Eb; reflexivity).
      assert (hct : c.(c_term) = b) by (unfold c; rewrite new_entry_term; reflexivity).
      destruct (gam_alloc_set lo lvl j (CSusp [] 0 (S j) c) (lift (lvl - nctx + S j) 0 b)
                  rs s1 a2 rs2 s2 hs1 hg1 hm1 hnf1 eq_refl
                  (fun H => eq_ind _ (fun x => repr_cell nctx H lvl (CSusp [] 0 (S j) c)
                                                 (lift (lvl - nctx + S j) 0 x))
                              (repr_cell_ctx_body H lvl j c) b hct)
                  (fun G f g => rn_cell_ctx_body f j c g) hd Ea)
        as [lo2 [h1 [h2 [h3 [h4 h5]]]]].
      exists lo2, (lift (lvl - nctx + S j) 0 b).
      split; [exact h1|]. split; [exact h2|]. split; [exact h3|]. split; [exact h4|].
      split; [exact hd | exact h5].
    - cbv beta iota zeta in e.
      destruct (alloc stress (CDone (VNeu (NVar (nctx - S j)) [])) rs s)
        as [[[a2 rs2] s2]|w] eqn:Ea; [|discriminate].
      injection e as e1 e2 e3. subst a rs' s'.
      assert (hd : ctx_den lvl j = Some (tRel (lvl - S (nctx - S j))))
        by (unfold ctx_den; rewrite En, Eb; reflexivity).
      destruct (gam_alloc_set lo lvl j (CDone (VNeu (NVar (nctx - S j)) []))
                  (tRel (lvl - S (nctx - S j))) rs s a2 rs2 s2 hs hg hm hnf eq_refl
                  (fun H => repr_cell_ctx_var H lvl (nctx - S j))
                  (fun G f g => rn_cell_ctx_var f (nctx - S j) g) hd Ea)
        as [lo2 [h1 [h2 [h3 [h4 h5]]]]].
      exists lo2, (tRel (lvl - S (nctx - S j))).
      split; [exact h1|]. split; [exact h2|]. split; [exact h3|]. split; [exact h4|].
      split; [exact hd | exact h5].
  Qed.

  (** The lookup, hit or miss: the address it returns stands for what the entry denotes, and
    the four invariants survive. No collector hypothesis: [collect_pres_holds] discharges
    the one a collection needs. *)
  Lemma gam_pres (lo : positive) (lvl j : nat) (rs : list root) (s : cbn_state)
      (a : haddr) (rs' : list root) (s' : cbn_state) :
    state_ok lo s -> gam_ok lvl s -> memo_ok s -> heap_nofwd (s.(st_heap)) ->
    gam X_type X Γ nctx stress j rs s = COk (a, rs', s') ->
    exists (lo' : positive) (t : term),
      state_ok lo' s' /\ gam_ok lvl s' /\ memo_ok s' /\ heap_nofwd (s'.(st_heap))
      /\ ctx_den lvl j = Some t /\ repr_addr nctx (s'.(st_heap)) lvl a t.
  Proof.
    intros hs hg hm hnf e.
    destruct (PTree.get (key_of_succ_nat j) (s.(st_gam))) as [a0|] eqn:Eg.
    - rewrite (gam_hit j a0 rs s Eg) in e. injection e as e1 e2 e3. subst a0 rs' s'.
      destruct (gam_hit_repr lvl j a s hg Eg) as [t [h1 h2]].
      exists lo, t. split; [exact hs|]. split; [exact hg|]. split; [exact hm|].
      split; [exact hnf|]. split; [exact h1 | exact h2].
    - exact (gam_miss lo lvl j rs s a rs' s' hs hg hm hnf Eg e).
  Qed.

  (** ** The frame of a call *)

  Definition run_s1 (t : term) : cbn_state :=
    snd (new_entry X_type X t [] (NSInput false) cbn_init).
  Definition run_c1 (t : term) : code :=
    fst (new_entry X_type X t [] (NSInput false) cbn_init).
  Definition run_s2 (t u : term) : cbn_state :=
    snd (new_entry X_type X u [] (NSInput true) (run_s1 t)).
  Definition run_c2 (t u : term) : code :=
    fst (new_entry X_type X u [] (NSInput true) (run_s1 t)).

  Lemma cbn_run_eq (le : conv_pb) (t u : term) :
    cbn_run X_type X Γ nctx stress le t u
    = match conv_term X_type X Γ nctx stress cbn_depth nctx le
              env_empty (run_c1 t) env_empty (run_c2 t u) [] (run_s2 t u) with
      | COk (true, _, _) => CbnYes
      | COk (false, _, _) => CbnNoRule
      | CFail w => CbnFail w
      end.
  Proof.
    unfold cbn_run, run_c1, run_c2, run_s1, run_s2.
    rewrite (surjective_pairing (new_entry X_type X t [] (NSInput false) cbn_init)).
    cbv beta iota zeta.
    rewrite (surjective_pairing (new_entry X_type X u [] (NSInput true)
      (snd (new_entry X_type X t [] (NSInput false) cbn_init)))).
    cbv beta iota zeta. reflexivity.
  Qed.

  Lemma run_s2_heap (t u : term) : (run_s2 t u).(st_heap) = bh_holes 1.
  Proof. unfold run_s2, run_s1. rewrite !new_entry_heap. reflexivity. Qed.

  Lemma run_s2_nofwd (t u : term) : heap_nofwd ((run_s2 t u).(st_heap)).
  Proof. rewrite run_s2_heap. apply heap_nofwd_holes. Qed.

  Lemma run_c1_term (t : term) : (run_c1 t).(c_term) = t.
  Proof. unfold run_c1. apply new_entry_term. Qed.

  Lemma run_c2_term (t u : term) : (run_c2 t u).(c_term) = u.
  Proof. unfold run_c2. apply new_entry_term. Qed.

  Lemma run_c1_entry (t : term) : (run_c1 t).(c_entry) = String2pos.xH.
  Proof. reflexivity. Qed.

  Lemma run_c2_entry (t u : term) : (run_c2 t u).(c_entry) = key_succ String2pos.xH.
  Proof. reflexivity. Qed.

  (** The state the call hands to [conv_term] satisfies the three invariants. *)
  Lemma run_s2_state_ok (t u : term) : state_ok 1 (run_s2 t u).
  Proof.
    unfold run_s2, run_s1. apply new_entry_state_ok, new_entry_state_ok, state_ok_init.
  Qed.

  Lemma run_s2_gam_ok (lvl : nat) (t u : term) : gam_ok lvl (run_s2 t u).
  Proof. unfold run_s2, run_s1. apply new_entry_gam_ok, new_entry_gam_ok, gam_ok_init. Qed.

  Lemma run_s2_memo_ok (t u : term) : memo_ok (run_s2 t u).
  Proof. unfold run_s2, run_s1. apply new_entry_memo_ok, new_entry_memo_ok, memo_ok_init. Qed.

  (** The two codes the call starts from: the table holds their entries, and each code is
    the root code of its entry. *)
  Lemma run_s2_codes (t u : term) :
    (((run_s2 t u).(st_memo)).(m_codes))
    = PTree.set (key_succ String2pos.xH)
        (mkEntry u [] (NSInput true) (wf_term_univs X_type X u))
        (PTree.set String2pos.xH
           (mkEntry t [] (NSInput false) (wf_term_univs X_type X t))
           (PTree.empty code_entry)).
  Proof.
    unfold run_s2, run_s1. rewrite new_entry_codes, new_entry_ncode, new_entry_codes.
    reflexivity.
  Qed.

  Lemma run_c1_in_table (t u : term) :
    PTree.get ((run_c1 t).(c_entry)) (((run_s2 t u).(st_memo)).(m_codes))
    = Some (mkEntry t [] (NSInput false) (wf_term_univs X_type X t)).
  Proof.
    rewrite run_s2_codes, run_c1_entry.
    rewrite PTree.gso by (cbn [key_succ]; discriminate). apply PTree.gss.
  Qed.

  Lemma run_c2_in_table (t u : term) :
    PTree.get ((run_c2 t u).(c_entry)) (((run_s2 t u).(st_memo)).(m_codes))
    = Some (mkEntry u [] (NSInput true) (wf_term_univs X_type X u)).
  Proof. rewrite run_s2_codes, run_c2_entry. apply PTree.gss. Qed.

  Lemma run_c1_code_inv (t : term) :
    code_inv (mkEntry t [] (NSInput false) (wf_term_univs X_type X t)) (run_c1 t).
  Proof. unfold run_c1. apply (new_entry_code_inv t [] (NSInput false) cbn_init). Qed.

  Lemma run_c2_code_inv (t u : term) :
    code_inv (mkEntry u [] (NSInput true) (wf_term_univs X_type X u)) (run_c2 t u).
  Proof. unfold run_c2. apply (new_entry_code_inv u [] (NSInput true) (run_s1 t)). Qed.

  (** The "roots in" end of the argument: the suspension of each input term in the empty
    environment stands for that term itself, in the heap the call starts with. *)
  Lemma run_repr_input (t u : term) :
    repr_susp nctx ((run_s2 t u).(st_heap)) nctx env_empty ((run_c1 t).(c_term)) t
    /\ repr_susp nctx ((run_s2 t u).(st_heap)) nctx env_empty ((run_c2 t u).(c_term)) u.
  Proof.
    split; [rewrite run_c1_term | rewrite run_c2_term]; apply repr_susp_env_empty.
  Qed.

  (** The whole frame of a call, as step 4 needs it. *)
  Lemma cbn_run_frame (t u : term) :
    state_ok 1 (run_s2 t u)
    /\ (forall lvl : nat, gam_ok lvl (run_s2 t u))
    /\ memo_ok (run_s2 t u)
    /\ heap_nofwd ((run_s2 t u).(st_heap))
    /\ repr_susp nctx ((run_s2 t u).(st_heap)) nctx env_empty ((run_c1 t).(c_term)) t
    /\ repr_susp nctx ((run_s2 t u).(st_heap)) nctx env_empty ((run_c2 t u).(c_term)) u
    /\ PTree.get ((run_c1 t).(c_entry)) (((run_s2 t u).(st_memo)).(m_codes))
       = Some (mkEntry t [] (NSInput false) (wf_term_univs X_type X t))
    /\ PTree.get ((run_c2 t u).(c_entry)) (((run_s2 t u).(st_memo)).(m_codes))
       = Some (mkEntry u [] (NSInput true) (wf_term_univs X_type X u))
    /\ code_inv (mkEntry t [] (NSInput false) (wf_term_univs X_type X t)) (run_c1 t)
    /\ code_inv (mkEntry u [] (NSInput true) (wf_term_univs X_type X u)) (run_c2 t u).
  Proof.
    destruct (run_repr_input t u) as [hr1 hr2].
    split; [apply run_s2_state_ok|].
    split; [intros lvl; apply run_s2_gam_ok|].
    split; [apply run_s2_memo_ok|].
    split; [apply run_s2_nofwd|].
    split; [exact hr1|]. split; [exact hr2|].
    split; [apply run_c1_in_table|]. split; [apply run_c2_in_table|].
    split; [apply run_c1_code_inv | apply run_c2_code_inv].
  Qed.

  (** [CbnYes] comes only from a [true] of [conv_term], for either value of [stress]. *)
  Lemma cbn_run_yes_inv (le : conv_pb) (t u : term) :
    cbn_run X_type X Γ nctx stress le t u = CbnYes ->
    exists (rs : list root) (s : cbn_state),
      conv_term X_type X Γ nctx stress cbn_depth nctx le
        env_empty (run_c1 t) env_empty (run_c2 t u) [] (run_s2 t u) = COk (true, rs, s).
  Proof.
    rewrite cbn_run_eq. intros h.
    destruct (conv_term X_type X Γ nctx stress cbn_depth nctx le
                env_empty (run_c1 t) env_empty (run_c2 t u) [] (run_s2 t u))
      as [[[b rs] s]|w] eqn:E; [|discriminate].
    destruct b; [|discriminate]. exists rs, s. reflexivity.
  Qed.

End CtxMemo.

(** ** The answer of the fast path *)

Lemma cbn_conv_answer_run {cf : checker_flags} (X_type : abstract_env_impl)
    (X : X_type.π2.π1) (b : bool) (le : conv_pb) (Γ : context) (t u : term) :
  cbn_conv_answer X_type X b le Γ t u = cbn_run X_type X Γ #|Γ| b le t u.
Proof. reflexivity. Qed.

(** [cbn_conv] answers [true] only through [CbnYes]. *)
Lemma cbn_conv_yes {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (le : conv_pb) (Γ : context) (t u : term) :
  cbn_conv X_type X le Γ t u = true -> cbn_conv_answer X_type X false le Γ t u = CbnYes.
Proof.
  unfold cbn_conv. destruct (cbn_conv_answer X_type X false le Γ t u);
    [reflexivity | discriminate | discriminate].
Qed.

Lemma cbn_conv_yes_iff {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
    (le : conv_pb) (Γ : context) (t u : term) :
  cbn_conv X_type X le Γ t u = true <-> cbn_conv_answer X_type X false le Γ t u = CbnYes.
Proof.
  split; [apply cbn_conv_yes|]. unfold cbn_conv. intros h. rewrite h. reflexivity.
Qed.

(** So a [true] of [cbn_conv] is a [true] of [conv_term] on the state and the two codes the
  call starts from. *)
Lemma cbn_conv_yes_conv_term {cf : checker_flags} (X_type : abstract_env_impl)
    (X : X_type.π2.π1) (le : conv_pb) (Γ : context) (t u : term) :
  cbn_conv X_type X le Γ t u = true ->
  exists (rs : list root) (s : cbn_state),
    conv_term X_type X Γ #|Γ| false cbn_depth #|Γ| le
      env_empty (run_c1 X_type X t) env_empty (run_c2 X_type X t u) []
      (run_s2 X_type X t u) = COk (true, rs, s).
Proof.
  intros h. apply cbn_conv_yes in h. rewrite cbn_conv_answer_run in h.
  exact (cbn_run_yes_inv X_type X Γ #|Γ| false le t u h).
Qed.
