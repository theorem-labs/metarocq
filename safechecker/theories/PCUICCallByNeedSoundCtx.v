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

  - [cbn_memo_ok s]: every index of the code table holds an entry whose root code is the one
    [cbn_new_entry] builds, with the universe check [cbn_new_entry] recorded. [cbn_new_entry] keeps
    it, and the code [cbn_new_entry] returns satisfies [cbn_code_inv] for the entry it added.
    [cbn_code_inv_child_step] carries [cbn_code_inv] along the machine's child codes.
  - [cbn_ctx_den lvl j]: the term the context entry [j] denotes with [lvl] levels in scope. The
    ghost invariant [cbn_gok] of [PCUICCallByNeedSoundEval] asks each cell of [cbn_st_gam] to carry
    this term as its ghost.
  - the start of a call: [cbn_run_s1], [cbn_run_c1], [cbn_run_s2] and [cbn_run_c2] are the states
  and codes
    [cbn_run] builds before its first [cbn_conv_term] ([cbn_run_eq]); the start state satisfies
    [cbn_state_ok], [cbn_memo_ok] and [cbn_heap_nofwd], and the table holds the two root entries.
  - [cbn_heap_nofwd] (no forwarding pointer in the machine's heap between collections) is what
    [PCUICCallByNeedSoundGC.cbn_collect_sound] asks of its input; [cbn_heap_nofwd_holes] and
    [cbn_heap_nofwd_heap_upd] show that the start heap and a write keep it. *)

(** ** Field equations used as rewrites *)

Lemma cbn_set_gam_next (g : PTree.t cbn_haddr) (s : cbn_state) :
  (cbn_set_gam g s).(cbn_st_next) = s.(cbn_st_next).
Proof. reflexivity. Qed.

Lemma cbn_set_gam_gam (g : PTree.t cbn_haddr) (s : cbn_state) : (cbn_set_gam g s).(cbn_st_gam) = g.
Proof. reflexivity. Qed.

Lemma cbn_key_neq_of_eqb (p q : String2pos.positive) : cbn_key_eqb p q = false -> p <> q.
Proof. intros he ->. rewrite (proj2 (cbn_key_eqb_spec q q) eq_refl) in he. discriminate. Qed.

(** ** No forwarding pointer between collections

  [cbn_collect_sound] asks [cbn_heap_nofwd] of the heap it is given, so the machine must keep it
  between collections: a [CbnCFwd] is written only by the collector, and only in the old heap
  it then throws away. *)

Lemma cbn_heap_nofwd_holes (p : positive) : cbn_heap_nofwd (cbn_bh_holes p).
Proof. intros a a' e. rewrite cbn_bh_get_holes in e. discriminate. Qed.

Lemma cbn_heap_nofwd_heap_upd (a : cbn_haddr) (cl : cbn_cell) (s s' : cbn_state) :
  cbn_heap_nofwd (s.(cbn_st_heap)) -> (forall b : cbn_haddr, cl <> CbnCFwd b) ->
  cbn_heap_upd a cl s = Some s' -> cbn_heap_nofwd (s'.(cbn_st_heap)).
Proof.
  intros hnf hcl e. unfold cbn_heap_upd in e.
  destruct (cbn_bh_upd a cl (s.(cbn_st_heap))) as [h'|] eqn:hu; [|discriminate].
  cbn in e. injection e as e. subst s'. cbn [cbn_st_heap].
  intros b b' hb. destruct (cbn_haddr_dec b a) as [->|hne].
  - rewrite (cbn_bh_get_upd_same _ _ _ _ hu) in hb. injection hb as hb. exact (hcl b' hb).
  - rewrite (cbn_bh_get_upd_other _ _ _ _ _ hu hne) in hb. exact (hnf _ _ hb).
Qed.

(** ** The two cases of [cbn_alloc]: without and with a collection *)

Lemma cbn_alloc_no_gc (cl : cbn_cell) (rs : list cbn_root) (s : cbn_state) :
  cbn_gc_due s = false ->
  cbn_alloc cl rs s = CbnCOk (fst (cbn_alloc_now cl s), rs, snd (cbn_alloc_now cl s)).
Proof. intros h. unfold cbn_alloc. rewrite h. destruct (cbn_alloc_now cl s). reflexivity. Qed.

Lemma cbn_alloc_gc (cl : cbn_cell) (rs : list cbn_root) (s : cbn_state) :
  cbn_gc_due s = true ->
  cbn_alloc cl rs s
  = match cbn_collect (CbnRC cl :: rs) s with
    | CbnCOk (CbnRC cl' :: rs', s') => CbnCOk
      (fst (cbn_alloc_now cl' s'), rs', snd (cbn_alloc_now cl' s'))
    | CbnCOk _ => CbnCFail CbnWRoots
    | CbnCFail w => CbnCFail w
    end.
Proof.
  intros h. unfold cbn_alloc. rewrite h.
  destruct (cbn_collect (CbnRC cl :: rs) s) as [[rs2 s2]|w]; [|reflexivity].
  destruct rs2 as [|r rs2]; [reflexivity|]. destruct r; reflexivity.
Qed.

Section CtxMemo.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat). (* nctx = #|Γ| *)

  (** ** What [cbn_new_entry] does to the state *)

  Lemma cbn_new_entry_code (t : term) (u : Instance.t) (s : cbn_state) :
    fst (cbn_new_entry X_type X t u s)
    = cbn_mkCode ((s.(cbn_st_memo)).(cbn_m_ncode)) cbn_path_nil (cbn_inst_code u t).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_codes (t : term) (u : Instance.t) (s : cbn_state) :
    ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).(cbn_m_codes)
    = PTree.set ((s.(cbn_st_memo)).(cbn_m_ncode))
        (cbn_mkEntry t u (cbn_wf_term_univs X_type X (cbn_inst_code u t)))
        ((s.(cbn_st_memo)).(cbn_m_codes)).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_ncode (t : term) (u : Instance.t) (s : cbn_state) :
    ((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).(cbn_m_ncode)
    = cbn_key_succ ((s.(cbn_st_memo)).(cbn_m_ncode)).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_heap (t : term) (u : Instance.t) (s : cbn_state) :
    (snd (cbn_new_entry X_type X t u s)).(cbn_st_heap) = s.(cbn_st_heap).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_next (t : term) (u : Instance.t) (s : cbn_state) :
    (snd (cbn_new_entry X_type X t u s)).(cbn_st_next) = s.(cbn_st_next).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_gam (t : term) (u : Instance.t) (s : cbn_state) :
    (snd (cbn_new_entry X_type X t u s)).(cbn_st_gam) = s.(cbn_st_gam).
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_term (t : term) (u : Instance.t) (s : cbn_state) :
    (fst (cbn_new_entry X_type X t u s)).(cbn_c_term) = cbn_inst_code u t.
  Proof. reflexivity. Qed.

  Lemma cbn_new_entry_entry (t : term) (u : Instance.t) (s : cbn_state) :
    (fst (cbn_new_entry X_type X t u s)).(cbn_c_entry) = (s.(cbn_st_memo)).(cbn_m_ncode).
  Proof. reflexivity. Qed.

  (** ** The entry invariant *)

  (** Every index of the code table holds an entry whose root code is the one [cbn_new_entry]
    builds for it, carrying the universe check [cbn_new_entry] recorded. *)
  Definition cbn_memo_ok (s : cbn_state) : Prop :=
    forall (i : String2pos.positive) (e : cbn_code_entry),
      PTree.get i ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
      cbn_code_inv e (cbn_mkCode i cbn_path_nil (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)))
      /\ e.(cbn_ce_wf) = cbn_wf_term_univs X_type X (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)).

  Lemma cbn_memo_ok_init : cbn_memo_ok cbn_init.
  Proof.
    intros i e h. unfold cbn_init, cbn_memo_empty in h. cbn [cbn_st_memo cbn_m_codes] in h.
    rewrite PTree.gempty in h. discriminate.
  Qed.

  (** [cbn_memo_ok] reads only the code table, so every operation that leaves it alone keeps the
    invariant. *)
  Lemma cbn_memo_ok_codes (s s' : cbn_state) :
    ((s'.(cbn_st_memo)).(cbn_m_codes)) = ((s.(cbn_st_memo)).(cbn_m_codes)) -> cbn_memo_ok s ->
      cbn_memo_ok s'.
  Proof. intros he h i e hi. rewrite he in hi. exact (h i e hi). Qed.

  Lemma cbn_new_entry_memo_ok (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_memo_ok s -> cbn_memo_ok (snd (cbn_new_entry X_type X t u s)).
  Proof.
    intros h i e hi. rewrite cbn_new_entry_codes in hi.
    destruct (cbn_key_eqb i ((s.(cbn_st_memo)).(cbn_m_ncode))) eqn:E.
    - apply cbn_key_eqb_spec in E; subst i. rewrite PTree.gss in hi.
      injection hi as hi; subst e. split; [apply cbn_code_inv_root | reflexivity].
    - rewrite PTree.gso in hi by (apply cbn_key_neq_of_eqb, E). exact (h i e hi).
  Qed.

  (** The code [cbn_new_entry] returns satisfies [cbn_code_inv] for the entry it added, and the
    table holds that entry at the code's index. *)
  Lemma cbn_new_entry_code_inv (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_code_inv (cbn_mkEntry t u (cbn_wf_term_univs X_type X (cbn_inst_code u t)))
      (fst (cbn_new_entry X_type X t u s)).
  Proof. rewrite cbn_new_entry_code. apply cbn_code_inv_root. Qed.

  Lemma cbn_new_entry_in_table (t : term) (u : Instance.t) (s : cbn_state) :
    PTree.get ((fst (cbn_new_entry X_type X t u s)).(cbn_c_entry))
      (((snd (cbn_new_entry X_type X t u s)).(cbn_st_memo)).(cbn_m_codes))
    = Some (cbn_mkEntry t u (cbn_wf_term_univs X_type X (cbn_inst_code u t))).
  Proof. rewrite cbn_new_entry_codes, cbn_new_entry_entry. apply PTree.gss. Qed.

  (** Under [cbn_memo_ok], the boolean [cbn_entry_wf] reads is the universe check of the entry's
    root term, and the root code of a table entry satisfies [cbn_code_inv]. *)
  Lemma cbn_memo_entry_wf (s : cbn_state) (i : String2pos.positive) (e : cbn_code_entry) :
    cbn_memo_ok s -> PTree.get i ((s.(cbn_st_memo)).(cbn_m_codes)) = Some e ->
    cbn_entry_wf i s = cbn_wf_term_univs X_type X (cbn_inst_code e.(cbn_ce_inst) e.(cbn_ce_term)).
  Proof. intros h hi. unfold cbn_entry_wf. rewrite hi. exact (proj2 (h i e hi)). Qed.

  (** ** The child codes the machine builds

    [cbn_child_step t k t'] lists the steps the machine's traversal takes: one constructor per
    [code_inv_child_*] lemma of [PCUICCallByNeed]. [cbn_code_inv_child_step] carries [cbn_code_inv]
    along any of them, so a proof over the traversal needs one lemma, not sixteen. *)
  Inductive cbn_child_step : term -> N -> term -> Prop :=
  | cbn_cs_app_fun f a : cbn_child_step (tApp f a) 0 f
  | cbn_cs_app_arg f a : cbn_child_step (tApp f a) 1 a
  | cbn_cs_lambda_dom na d b : cbn_child_step (tLambda na d b) 0 d
  | cbn_cs_lambda_body na d b : cbn_child_step (tLambda na d b) 1 b
  | cbn_cs_prod_dom na d b : cbn_child_step (tProd na d b) 0 d
  | cbn_cs_prod_body na d b : cbn_child_step (tProd na d b) 1 b
  | cbn_cs_letin_def na b ty body : cbn_child_step (tLetIn na b ty body) 0 b
  | cbn_cs_letin_type na b ty body : cbn_child_step (tLetIn na b ty body) 1 ty
  | cbn_cs_letin_body na b ty body : cbn_child_step (tLetIn na b ty body) 2 body
  | cbn_cs_case_scrut ci p scrut brs : cbn_child_step (tCase ci p scrut brs) 0 scrut
  | cbn_cs_case_return ci p scrut brs : cbn_child_step (tCase ci p scrut brs) 1 p.(preturn)
  | cbn_cs_case_param ci p scrut brs i t :
      nth_error p.(pparams) (N.to_nat i) = Some t ->
      cbn_child_step (tCase ci p scrut brs) (cbn_case_param_step i) t
  | cbn_cs_case_branch ci p scrut brs i br :
      nth_error brs (N.to_nat i) = Some br ->
      cbn_child_step (tCase ci p scrut brs) (cbn_case_branch_step i) br.(bbody)
  | cbn_cs_proj pr a : cbn_child_step (tProj pr a) 0 a
  | cbn_cs_fix mfix idx k d :
      nth_error mfix (N.to_nat k) = Some d -> cbn_child_step (tFix mfix idx) k d.(dbody)
  | cbn_cs_cofix mfix idx k d :
      nth_error mfix (N.to_nat k) = Some d -> cbn_child_step (tCoFix mfix idx) k d.(dbody).

  Lemma cbn_code_inv_child_step (ce : cbn_code_entry) (c : cbn_code) (k : N) (t : term) :
    cbn_code_inv ce c -> cbn_child_step c.(cbn_c_term) k t -> cbn_code_inv ce (cbn_child c k t).
  Proof.
    intros hc hs. inversion hs; subst;
      eauto using cbn_code_inv_child_app_fun, cbn_code_inv_child_app_arg,
        cbn_code_inv_child_lambda_dom, cbn_code_inv_child_lambda_body,
        cbn_code_inv_child_prod_dom, cbn_code_inv_child_prod_body,
        cbn_code_inv_child_letin_def, cbn_code_inv_child_letin_type, cbn_code_inv_child_letin_body,
        cbn_code_inv_child_case_scrut, cbn_code_inv_child_case_return,
        cbn_code_inv_child_case_param, cbn_code_inv_child_case_branch,
        cbn_code_inv_child_proj, cbn_code_inv_child_fix, cbn_code_inv_child_cofix.
  Qed.

  (** ** The terms the context entries denote *)

  (** The term the [j]th entry of [Γ] denotes with [lvl] levels in scope: its body lifted
    over the [S j] entries between it and the hole, or, for an entry without a body, the de
    Bruijn index of the level [nctx - S j] the machine gives it. *)
  Definition cbn_ctx_den (lvl j : nat) : option term :=
    match nth_error Γ j with
    | None => None
    | Some decl =>
      match decl.(decl_body) with
      | Some b => Some (lift (lvl - nctx + S j) 0 b)
      | None => Some (tRel (lvl - S (nctx - S j)))
      end
    end.

  Lemma cbn_new_entry_state_ok (lo : positive) (t : term) (u : Instance.t) (s : cbn_state) :
    cbn_state_ok lo s -> cbn_state_ok lo (snd (cbn_new_entry X_type X t u s)).
  Proof.
    intros [h1 h2 h3]. split; [rewrite cbn_new_entry_next, cbn_new_entry_heap; exact h1 | | ].
    - rewrite cbn_new_entry_next, cbn_new_entry_heap. exact h2.
    - rewrite cbn_new_entry_next, cbn_new_entry_gam. exact h3.
  Qed.

  (** Recording the address of the entry [j] keeps the state invariant, if that address is
    one the heap has. *)
  Lemma cbn_state_ok_set_gam (lo : positive) (j : nat) (a : cbn_haddr) (s : cbn_state) :
    cbn_state_ok lo s -> (lo <= cbn_ha_p a)%positive -> (cbn_ha_p a < s.(cbn_st_next))%positive ->
    cbn_state_ok lo (cbn_set_gam (PTree.set (cbn_key_of_succ_nat j) a (s.(cbn_st_gam))) s).
  Proof.
    intros [h1 h2 h3] hlo hhi. split; [exact h1 | exact h2 |].
    intros k a' e. rewrite cbn_set_gam_gam in e. rewrite cbn_set_gam_next.
    destruct (cbn_key_eqb k (cbn_key_of_succ_nat j)) eqn:Ek.
    - apply cbn_key_eqb_spec in Ek; subst k. rewrite PTree.gss in e.
      injection e as e; subst a'. split; assumption.
    - rewrite PTree.gso in e by (apply cbn_key_neq_of_eqb, Ek). exact (h3 k a' e).
  Qed.

  (** ** The frame of a call *)

  Definition cbn_run_s1 (t : term) : cbn_state :=
    snd (cbn_new_entry X_type X t [] cbn_init).
  Definition cbn_run_c1 (t : term) : cbn_code :=
    fst (cbn_new_entry X_type X t [] cbn_init).
  Definition cbn_run_s2 (t u : term) : cbn_state :=
    snd (cbn_new_entry X_type X u [] (cbn_run_s1 t)).
  Definition cbn_run_c2 (t u : term) : cbn_code :=
    fst (cbn_new_entry X_type X u [] (cbn_run_s1 t)).

  Lemma cbn_run_eq (le : conv_pb) (t u : term) :
    cbn_run X_type X Γ nctx le t u
    = match cbn_conv_term X_type X Γ nctx cbn_depth nctx le
              cbn_env_empty (cbn_run_c1 t) cbn_env_empty (cbn_run_c2 t u) [] (cbn_run_s2 t u) with
      | CbnCOk (true, _, _) => CbnYes
      | CbnCOk (false, _, _) => CbnNoRule
      | CbnCFail w => CbnFail w
      end.
  Proof.
    unfold cbn_run, cbn_run_c1, cbn_run_c2, cbn_run_s1, cbn_run_s2.
    rewrite (surjective_pairing (cbn_new_entry X_type X t [] cbn_init)).
    cbv beta iota zeta.
    rewrite (surjective_pairing (cbn_new_entry X_type X u []
      (snd (cbn_new_entry X_type X t [] cbn_init)))).
    cbv beta iota zeta. reflexivity.
  Qed.

  Lemma cbn_run_s2_heap (t u : term) : (cbn_run_s2 t u).(cbn_st_heap) = cbn_bh_holes 1.
  Proof. unfold cbn_run_s2, cbn_run_s1. rewrite !cbn_new_entry_heap. reflexivity. Qed.

  Lemma cbn_run_s2_nofwd (t u : term) : cbn_heap_nofwd ((cbn_run_s2 t u).(cbn_st_heap)).
  Proof. rewrite cbn_run_s2_heap. apply cbn_heap_nofwd_holes. Qed.

  Lemma cbn_run_c1_term (t : term) : (cbn_run_c1 t).(cbn_c_term) = t.
  Proof. unfold cbn_run_c1. apply cbn_new_entry_term. Qed.

  Lemma cbn_run_c2_term (t u : term) : (cbn_run_c2 t u).(cbn_c_term) = u.
  Proof. unfold cbn_run_c2. apply cbn_new_entry_term. Qed.

  Lemma cbn_run_c1_entry (t : term) : (cbn_run_c1 t).(cbn_c_entry) = String2pos.xH.
  Proof. reflexivity. Qed.

  Lemma cbn_run_c2_entry (t u : term) : (cbn_run_c2 t u).(cbn_c_entry) = cbn_key_succ String2pos.xH.
  Proof. reflexivity. Qed.

  (** The state the call hands to [cbn_conv_term] satisfies [cbn_state_ok] and [cbn_memo_ok]. *)
  Lemma cbn_run_s2_state_ok (t u : term) : cbn_state_ok 1 (cbn_run_s2 t u).
  Proof.
    unfold cbn_run_s2, cbn_run_s1. apply cbn_new_entry_state_ok, cbn_new_entry_state_ok,
      cbn_state_ok_init.
  Qed.

  Lemma cbn_run_s2_memo_ok (t u : term) : cbn_memo_ok (cbn_run_s2 t u).
  Proof. unfold cbn_run_s2, cbn_run_s1. apply cbn_new_entry_memo_ok, cbn_new_entry_memo_ok,
    cbn_memo_ok_init. Qed.

  (** The two codes the call starts from: the table holds their entries, and each code is
    the root code of its entry. *)
  Lemma cbn_run_s2_codes (t u : term) :
    (((cbn_run_s2 t u).(cbn_st_memo)).(cbn_m_codes))
    = PTree.set (cbn_key_succ String2pos.xH)
        (cbn_mkEntry u [] (cbn_wf_term_univs X_type X u))
        (PTree.set String2pos.xH
           (cbn_mkEntry t [] (cbn_wf_term_univs X_type X t))
           (PTree.empty cbn_code_entry)).
  Proof.
    unfold cbn_run_s2, cbn_run_s1. rewrite cbn_new_entry_codes, cbn_new_entry_ncode,
      cbn_new_entry_codes.
    reflexivity.
  Qed.

  Lemma cbn_run_c1_in_table (t u : term) :
    PTree.get ((cbn_run_c1 t).(cbn_c_entry)) (((cbn_run_s2 t u).(cbn_st_memo)).(cbn_m_codes))
    = Some (cbn_mkEntry t [] (cbn_wf_term_univs X_type X t)).
  Proof.
    rewrite cbn_run_s2_codes, cbn_run_c1_entry.
    rewrite PTree.gso by (cbn [cbn_key_succ]; discriminate). apply PTree.gss.
  Qed.

  Lemma cbn_run_c2_in_table (t u : term) :
    PTree.get ((cbn_run_c2 t u).(cbn_c_entry)) (((cbn_run_s2 t u).(cbn_st_memo)).(cbn_m_codes))
    = Some (cbn_mkEntry u [] (cbn_wf_term_univs X_type X u)).
  Proof. rewrite cbn_run_s2_codes, cbn_run_c2_entry. apply PTree.gss. Qed.

  Lemma cbn_run_c1_code_inv (t : term) :
    cbn_code_inv (cbn_mkEntry t [] (cbn_wf_term_univs X_type X t)) (cbn_run_c1 t).
  Proof. unfold cbn_run_c1. apply (cbn_new_entry_code_inv t [] cbn_init). Qed.

  Lemma cbn_run_c2_code_inv (t u : term) :
    cbn_code_inv (cbn_mkEntry u [] (cbn_wf_term_univs X_type X u)) (cbn_run_c2 t u).
  Proof. unfold cbn_run_c2. apply (cbn_new_entry_code_inv u [] (cbn_run_s1 t)). Qed.

End CtxMemo.
