(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst.
From MetaRocq.SafeChecker Require Import PCUICWfEnv PCUICCallByNeed PCUICCallByNeedSound
  PCUICCallByNeedSoundGC.

Import CanonicalTries.

(** * The start of a call: the code table and the context entries

  This file states what the machine's code table and context map mean, and proves the facts
  about the state [cbn_run] starts from that the soundness proof uses.

  - [memo_ok s]: every index of the code table holds an entry whose root code is the one
    [new_entry] builds, with the universe check [new_entry] recorded. [new_entry] keeps it,
    and the code [new_entry] returns satisfies [code_inv] for the entry it added.
    [code_inv_child_step] carries [code_inv] along the machine's child codes.
  - [ctx_den lvl j]: the term the context entry [j] denotes with [lvl] levels in scope. The
    ghost invariant [gok] of [PCUICCallByNeedSoundEval] asks each cell of [st_gam] to carry
    this term as its ghost.
  - the start of a call: [run_s1], [run_c1], [run_s2] and [run_c2] are the states and codes
    [cbn_run] builds before its first [conv_term] ([cbn_run_eq]); the start state satisfies
    [state_ok], [memo_ok] and [heap_nofwd], and the table holds the two root entries.
  - [heap_nofwd] (no forwarding pointer in the machine's heap between collections) is what
    [PCUICCallByNeedSoundGC.collect_sound] asks of its input; [heap_nofwd_holes] and
    [heap_nofwd_heap_upd] show that the start heap and a write keep it. *)

(** ** Field equations used as rewrites *)

Lemma set_gam_next (g : PTree.t haddr) (s : cbn_state) :
  (set_gam g s).(st_next) = s.(st_next).
Proof. reflexivity. Qed.

Lemma set_gam_gam (g : PTree.t haddr) (s : cbn_state) : (set_gam g s).(st_gam) = g.
Proof. reflexivity. Qed.

Lemma key_neq_of_eqb (p q : String2pos.positive) : key_eqb p q = false -> p <> q.
Proof. intros he ->. rewrite (proj2 (key_eqb_spec q q) eq_refl) in he. discriminate. Qed.

(** ** No forwarding pointer between collections

  [collect_sound] asks [heap_nofwd] of the heap it is given, so the machine must keep it
  between collections: a [CFwd] is written only by the collector, and only in the old heap
  it then throws away. *)

Lemma heap_nofwd_holes (p : positive) : heap_nofwd (bh_holes p).
Proof. intros a a' e. rewrite bh_get_holes in e. discriminate. Qed.

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

(** ** The two cases of [alloc]: without and with a collection *)

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

  (** Under [memo_ok], the boolean [entry_wf] reads is the universe check of the entry's
    root term, and the root code of a table entry satisfies [code_inv]. *)
  Lemma memo_entry_wf (s : cbn_state) (i : String2pos.positive) (e : code_entry) :
    memo_ok s -> PTree.get i ((s.(st_memo)).(m_codes)) = Some e ->
    entry_wf i s = wf_term_univs X_type X (inst_code e.(ce_inst) e.(ce_term)).
  Proof. intros h hi. unfold entry_wf. rewrite hi. exact (proj2 (h i e hi)). Qed.

  (** ** The child codes the machine builds

    [child_step t k t'] lists the steps the machine's traversal takes: one constructor per
    [code_inv_child_*] lemma of [PCUICCallByNeed]. [code_inv_child_step] carries [code_inv] along any
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

  (** ** The terms the context entries denote *)

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

  Lemma new_entry_state_ok (lo : positive) (t : term) (u : Instance.t) (ns : code_ns)
      (s : cbn_state) :
    state_ok lo s -> state_ok lo (snd (new_entry X_type X t u ns s)).
  Proof.
    intros [h1 h2 h3]. split; [rewrite new_entry_next, new_entry_heap; exact h1 | | ].
    - rewrite new_entry_next, new_entry_heap. exact h2.
    - rewrite new_entry_next, new_entry_gam. exact h3.
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

  (** The state the call hands to [conv_term] satisfies [state_ok] and [memo_ok]. *)
  Lemma run_s2_state_ok (t u : term) : state_ok 1 (run_s2 t u).
  Proof.
    unfold run_s2, run_s1. apply new_entry_state_ok, new_entry_state_ok, state_ok_init.
  Qed.

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

End CtxMemo.
