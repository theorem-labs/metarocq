(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries ByteCompare.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICWfUniverses.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnvEta.

Import CanonicalTries.

(** * FORECAST-ONLY (fc/etak-forecast1): the η environment's copy of [PCUICCallByNeed]

  Byte-for-byte the text of integ-all7's [safechecker/theories/PCUICCallByNeed.v] (8d96afc9),
  except the import line above: [PCUICWfEnvEta] in place of [PCUICWfEnv].  The machine uses
  only the computational operations of the abstract environment ([abstract_env_lookup],
  [abstract_env_compare_universe], [abstract_env_compare_sort],
  [abstract_env_ext_wf_universeb], [abstract_env_ext_wf_sortb]), which [PCUICWfEnvEta] defines
  with the same names and the same text over its own class.  The copy exists because
  [PCUICTypeCheckerEta.convert] runs over a [PCUICWfEnvEta.abstract_env_impl], a different type
  from base's, so base [cbn_conv] cannot be applied there; behaviour is unchanged: the same
  machine, the same answers.

  Its soundness over [welltypedE] is the named hypothesis [PCUICCallByNeedSoundEta.cbn_conv_soundE]
  (with its base instance there).  Forecast-only: [frac/eta] has no call-by-need fast path
  (BET-298 is in integ-all7 only).  Reconciled at the landing of [convert_cbn_soundE] (the E
  statement of [PCUICCallByNeedSoundHookProof.convert_cbn_sound], over [welltypedE]). *)

(** * Call-by-need conversion fast path

  [cbn_conv le Γ t u] evaluates [t] and [u] with a weak-head call-by-need environment
  machine and compares the weak-head values. [true] means that [t] and [u] are convertible
  at [le]; [false] means "don't know", never "not convertible". [cbn_conv_answer] gives the
  same answer with the reason for a "don't know".

  - Heap: a binary random-access list whose digits are the bits of [cbn_st_next] (the next
    address), least significant first; a digit 1 at position [j] holds a complete tree of
    [2^j] cells. Heap addresses ([cbn_haddr]) are allocation numbers from 1 (index 0 of the
    list is never allocated) and have their own type. A lookup scans the bits of the
    address against the digits (no arithmetic): the cell is in the tree of the highest
    position where the address has 0 and the digit is 1, unless a higher position has
    address 1 and digit 0 (then the address is not below [cbn_st_next]), and the bits below
    that position are its path in the tree. A cell holds a suspension (the fields of an
    environment, and a code), a value, or a black hole while it is forced. Forcing writes
    the value back.
  - Environment: a list of slots for the bound variables, their number, and the offset in
    [Γ] of the free variables beyond them ([goff]). A slot is a heap address or an inline
    suspension (environment, code) that is not in the heap: an argument bound to a binder
    whose variable occurs at most once stays inline.
  - Allocation economy: an argument that is a variable reuses the variable's slot; an
    argument that is a lambda, a fixpoint, a sort, a product, a primitive or a bodiless
    constant is allocated as a value cell; other arguments as suspensions.
  - Roots in, roots out: every function that can allocate takes the list of roots its
    callers hold and returns it renamed together with its result. An allocation may run the
    copying collector first, when the cells allocated since the last collection exceed
    twice the live count after it and at least [cbn_gc_min]. The collector copies the cells
    reachable from the roots and from [cbn_st_gam] into a fresh heap with new addresses from the
    old [cbn_st_next] on. It does not use the step budget. An address that is not in the heap makes
    the whole call answer "don't know".
  - Code: every term the machine evaluates is the subterm, at a path, of the instantiated
    term of an entry of the code table. A code carries the entry index, the path (encoded
    injectively as a positive, newest step outermost) and that subterm. The table only grows
    and an entry never changes, so equal (index, path) pairs mean equal codes. Per (index,
    path), the state keeps the structural hash of the code and whether a binder's variable
    occurs at most once in it.
  - Same code: equal identifiers, or (when both entries passed their [wf_universeb] check at
    creation) equal hashes and [eqb_term_upto_univ] at [Conv]; the result of that equality is
    cached by the ordered pair of identifiers for the rest of the call.
  - Bounds: every function is a structural [Fixpoint] on a lazily generated [cbn_fuel] (the
    recursion depth, in effect unbounded), and every machine, read-back and comparison step
    takes one unit of an [N] step budget. Out of budget means "don't know".
  - Delta: constant bodies are looked up once per [cbn_conv] call and memoised by kername;
    one code entry per (constant, syntactic instance).

  The soundness theorem of [cbn_conv] is
  [PCUICCallByNeedSoundHookProof.convert_cbn_sound]. *)

(** ** Keys of the code table, of [cbn_st_gam] and of the per-code maps *)

Local Notation cbn_key := String2pos.positive.
Local Notation cbn_cidx := String2pos.positive. (* code-table index *)

Fixpoint cbn_key_succ (p : cbn_key) : cbn_key :=
  match p with
  | String2pos.xI q => String2pos.xO (cbn_key_succ q)
  | String2pos.xO q => String2pos.xI q
  | String2pos.xH => String2pos.xO String2pos.xH
  end.

Fixpoint cbn_key_eqb (p q : cbn_key) : bool :=
  match p, q with
  | String2pos.xI p, String2pos.xI q => cbn_key_eqb p q
  | String2pos.xO p, String2pos.xO q => cbn_key_eqb p q
  | String2pos.xH, String2pos.xH => true
  | _, _ => false
  end.

Fixpoint cbn_key_of_succ_nat (n : nat) : cbn_key :=
  match n with
  | O => String2pos.xH
  | S n => cbn_key_succ (cbn_key_of_succ_nat n)
  end.

Definition cbn_get2 {A} (k1 k2 : cbn_key) (m : PTree.t (PTree.t A)) : option A :=
  match PTree.get k1 m with
  | Some m2 => PTree.get k2 m2
  | None => None
  end.

Definition cbn_set2 {A} (k1 k2 : cbn_key) (x : A) (m : PTree.t (PTree.t A)) : PTree.t (PTree.t A) :=
  let m2 := match PTree.get k1 m with Some m2 => m2 | None => PTree.empty _ end in
  PTree.set k1 (PTree.set k2 x m2) m.

(** *** Facts about keys and the two-level maps *)

Lemma cbn_key_eqb_spec (p q : cbn_key) : cbn_key_eqb p q = true <-> p = q.
Proof.
  revert q; induction p as [p IH|p IH|]; intros [q|q|]; cbn;
    first [ rewrite IH; split; [now intros -> | now intros [= ->]]
          | split; discriminate
          | split; reflexivity ].
Qed.

Lemma cbn_key_of_succ_nat_inj (n m : nat) : cbn_key_of_succ_nat n = cbn_key_of_succ_nat m -> n = m.
Proof.
  assert (Htp : exists tp : cbn_key -> positive,
            tp String2pos.xH = xH /\ forall p, tp (cbn_key_succ p) = Pos.succ (tp p)).
  { exists (fix tp (p : cbn_key) : positive :=
              match p with
              | String2pos.xI q => xI (tp q)
              | String2pos.xO q => xO (tp q)
              | String2pos.xH => xH
              end).
    split; [reflexivity|].
    induction p as [p IH|p|]; cbn; [rewrite IH|..]; reflexivity. }
  destruct Htp as [tp [Hone Hsucc]].
  assert (Hnat : forall k, tp (cbn_key_of_succ_nat k) = Pos.of_succ_nat k).
  { intros k; induction k as [|k IH]; cbn; [exact Hone | now rewrite Hsucc, IH]. }
  intros E. apply SuccNat2Pos.inj. now rewrite <- !Hnat, E.
Qed.

Lemma cbn_get2_set2_same {A} (k1 k2 : cbn_key) (x : A) m
  : cbn_get2 k1 k2 (cbn_set2 k1 k2 x m) = Some x.
Proof.
  unfold cbn_get2, cbn_set2; cbv zeta. rewrite PTree.gss. cbv beta iota. now rewrite PTree.gss.
Qed.

Lemma cbn_get2_set2_other {A} (k1 k2 k1' k2' : cbn_key) (x : A) m :
  k1' <> k1 \/ k2' <> k2 -> cbn_get2 k1' k2' (cbn_set2 k1 k2 x m) = cbn_get2 k1' k2' m.
Proof.
  intros Hne. unfold cbn_get2, cbn_set2; cbv zeta.
  destruct (cbn_key_eqb k1' k1) eqn:E.
  - apply cbn_key_eqb_spec in E; subst k1'. destruct Hne as [Hne|Hne]; [congruence|].
    rewrite PTree.gss. cbv beta iota. rewrite PTree.gso by exact Hne.
    destruct (PTree.get k1 m); [reflexivity | apply PTree.gempty].
  - assert (k1' <> k1).
    { intros ->. rewrite (proj2 (cbn_key_eqb_spec k1 k1) eq_refl) in E. discriminate. }
    now rewrite PTree.gso.
Qed.

(** ** Heap addresses *)

Record cbn_haddr := CbnHAddr { cbn_ha_p : positive }.

Definition cbn_haddr_eqb (a b : cbn_haddr) : bool := Pos.eqb a.(cbn_ha_p) b.(cbn_ha_p).

(** ** Fuel *)

(** The recursion bound. [CbnFS k] produces the next unit on demand, so a large bound costs no
  memory: [cbn_fuel_of_pos p k] is [p] units followed by [k tt]. *)
Inductive cbn_fuel := CbnFO | CbnFS (k : unit -> cbn_fuel).

Fixpoint cbn_fuel_of_pos (p : positive) (k : unit -> cbn_fuel) : cbn_fuel :=
  match p with
  | xH => CbnFS k
  | xO p => cbn_fuel_of_pos p (fun _ => cbn_fuel_of_pos p k)
  | xI p => CbnFS (fun _ => cbn_fuel_of_pos p (fun _ => cbn_fuel_of_pos p k))
  end.

(** 2^62 units of recursion depth. *)
Definition cbn_depth : cbn_fuel := cbn_fuel_of_pos 4611686018427387904%positive (fun _ => CbnFO).

(** Step budget of one [cbn_conv] call. A call that exhausts it answers "don't know", and
  [convert] then runs [isconv_term], so the value bounds only the time such a call loses;
  it was chosen by measurement, not derived. *)
Definition cbn_steps : N := 4000000000%N.

(** The collector runs when the cells allocated since the last collection exceed
  [max (2 * live) cbn_gc_min]. [cbn_gc_min] keeps a small heap from being collected after every few
  allocations; its value was chosen by measurement, not derived. *)
Definition cbn_gc_min : N := 1000000%N.

(** The allocations allowed before the next collection, after a collection that copied
  [live] cells. *)
Definition cbn_gc_room (live : N) : N := N.succ (N.max (N.double live) cbn_gc_min).

(** ** Results *)

(** Why a call answers "don't know". *)
Inductive cbn_why :=
| CbnWDepth       (* the recursion bound ran out *)
| CbnWSteps       (* the step budget ran out *)
| CbnWDangling    (* a heap read or write at an address that is not in the heap *)
| CbnWBusy        (* a black hole: a cell forced during its own evaluation *)
| CbnWShape       (* a term or value shape the machine does not handle *)
| CbnWCtx         (* a free variable beyond the context *)
| CbnWDelta       (* a constant that is not in the environment *)
| CbnWGcDangling  (* the collector met an address that is not in the heap *)
| CbnWGcFuel      (* the collector's walk ran out of fuel *)
| CbnWRoots.      (* returned roots of an unexpected shape (an internal error) *)

Inductive cbn_res (A : Type) := CbnCOk (x : A) | CbnCFail (w : cbn_why).
Arguments CbnCOk {A} x.
Arguments CbnCFail {A} w.

Inductive cbn_answer := CbnYes | CbnNoRule | CbnFail (w : cbn_why).

Local Notation "'cbn2' ( x , s ) := c 'in' k" :=
  (match c with CbnCOk (x, s) => k | CbnCFail w => CbnCFail w end)
  (at level 200, x ident, s ident, c at level 100, k at level 200, only parsing).

Local Notation "'cbnlet' ( x , r , s ) := c 'in' k" :=
  (match c with CbnCOk (x, r, s) => k | CbnCFail w => CbnCFail w end)
  (at level 200, x ident, r ident, s ident, c at level 100, k at level 200, only parsing).

(** [cbnwhen n (r, s) := c in k]: continue with [k] if [c] answers [true]; on [false], answer
  [false] with the roots of [c] less the [n] frames the caller pushed for [c]. *)
Local Notation "'cbnwhen' n ( r , s ) := c 'in' k" :=
  (match c with
   | CbnCOk (true, r, s) => k
   | CbnCOk (false, r, s) => CbnCOk (false, skipn n r, s)
   | CbnCFail w => CbnCFail w end)
  (at level 200, n at level 0, r ident, s ident, c at level 100, k at level 200, only parsing).

(** ** Code table *)

(** [cbn_ce_wf]: the result of the [wf_universeb] check of the instantiated term, run once when
  the entry is created. *)
Record cbn_code_entry := cbn_mkEntry {
  cbn_ce_term : term;
  cbn_ce_inst : Instance.t;
  cbn_ce_wf : bool }.

(** The term the machine evaluates for an entry: its term with its instance substituted.
  The empty instance leaves the term unchanged (monomorphic bodies have no universe
  variables). *)
Definition cbn_inst_code (u : Instance.t) (t : term) : term :=
  match u with
  | [] => t
  | u => subst_instance u t
  end.

(** [cbn_c_path] encodes the list of path steps, newest step outermost, each step [k] as the
  Elias-gamma code of [k + 1] (prefix-free, so the encoding is injective). *)
Record cbn_code := cbn_mkCode {
  cbn_c_entry : cbn_cidx;
  cbn_c_path : cbn_key;
  cbn_c_term : term }.

Definition cbn_path_nil : cbn_key := String2pos.xH.

Fixpoint cbn_wrap_bits (m : positive) (p : cbn_key) (z : nat) : cbn_key * nat :=
  match m with
  | xH => (String2pos.xI p, z)
  | xO m => cbn_wrap_bits m (String2pos.xO p) (S z)
  | xI m => cbn_wrap_bits m (String2pos.xI p) (S z)
  end.

Fixpoint cbn_wrap_zeros (z : nat) (p : cbn_key) : cbn_key :=
  match z with
  | O => p
  | S z => String2pos.xO (cbn_wrap_zeros z p)
  end.

Definition cbn_path_push (k : N) (p : cbn_key) : cbn_key :=
  let (q, z) := cbn_wrap_bits (N.succ_pos k) p O in cbn_wrap_zeros z q.

(** Path steps: [tApp f a]: f 0, a 1; [tLambda]/[tProd]: domain 0, body 1; [tLetIn]: definition
  0, body 2; [tCase]: scrutinee 0, return 1, parameter [i] 2+2i, branch [i] 3+2i; [tProj]: 0;
  [tFix]: body of definition [i] is step [i]. *)
Definition cbn_child (c : cbn_code) (k : N) (t : term) : cbn_code :=
  cbn_mkCode c.(cbn_c_entry) (cbn_path_push k c.(cbn_c_path)) t.

Definition cbn_case_param_step (i : N) : N := N.add 2 (N.double i).
Definition cbn_case_branch_step (i : N) : N := N.add 3 (N.double i).

Definition cbn_same_id (c1 c2 : cbn_code) : bool :=
  cbn_key_eqb c1.(cbn_c_entry) c2.(cbn_c_entry) && cbn_key_eqb c1.(cbn_c_path) c2.(cbn_c_path).

(** *** Paths are injective; a code's (entry, path) determines its term *)

Lemma cbn_wrap_bits_snd m p z : snd (cbn_wrap_bits m p z) + 1 = z + Pos.size_nat m.
Proof.
  revert p z; induction m as [m IH|m IH|]; intros p z; cbn; [rewrite IH|rewrite IH|]; lia.
Qed.

Lemma cbn_wrap_bits_fst_xI m p z : exists a, fst (cbn_wrap_bits m p z) = String2pos.xI a.
Proof.
  revert p z; induction m as [m IH|m IH|]; intros p z; cbn;
    [apply IH|apply IH|eexists; reflexivity].
Qed.

Lemma cbn_wrap_bits_inj m m' p p' z z' :
  Pos.size_nat m = Pos.size_nat m' -> fst (cbn_wrap_bits m p z) = fst (cbn_wrap_bits m' p' z') ->
  m = m' /\ p = p'.
Proof.
  revert m' p p' z z'; induction m as [m IH|m IH|]; intros [m'|m'|] p p' z z' Hs H;
    cbn in Hs, H.
  - injection Hs as Hs. destruct (IH _ _ _ _ _ Hs H) as [-> E]. now injection E as ->.
  - injection Hs as Hs. destruct (IH _ _ _ _ _ Hs H) as [_ E]. discriminate E.
  - injection Hs as Hs. destruct m; cbn in Hs; discriminate Hs.
  - injection Hs as Hs. destruct (IH _ _ _ _ _ Hs H) as [_ E]. discriminate E.
  - injection Hs as Hs. destruct (IH _ _ _ _ _ Hs H) as [-> E]. now injection E as ->.
  - injection Hs as Hs. destruct m; cbn in Hs; discriminate Hs.
  - injection Hs as Hs. destruct m'; cbn in Hs; discriminate Hs.
  - injection Hs as Hs. destruct m'; cbn in Hs; discriminate Hs.
  - now injection H as ->.
Qed.

Lemma cbn_wrap_zeros_inj z z' a a' :
  cbn_wrap_zeros z (String2pos.xI a) = cbn_wrap_zeros z' (String2pos.xI a') -> z = z' /\ a = a'.
Proof.
  revert z'; induction z as [|z IH]; intros [|z'] H; cbn in H; try discriminate.
  - now injection H as ->.
  - injection H as H. destruct (IH _ H) as [-> ->]. now split.
Qed.

Lemma cbn_path_push_inj k k' p p' : cbn_path_push k p = cbn_path_push k' p' -> k = k' /\ p = p'.
Proof.
  unfold cbn_path_push.
  pose proof (cbn_wrap_bits_snd (N.succ_pos k) p 0) as Hs.
  pose proof (cbn_wrap_bits_snd (N.succ_pos k') p' 0) as Hs'.
  destruct (cbn_wrap_bits_fst_xI (N.succ_pos k) p 0) as [a Ha].
  destruct (cbn_wrap_bits_fst_xI (N.succ_pos k') p' 0) as [a' Ha'].
  pose proof (cbn_wrap_bits_inj (N.succ_pos k) (N.succ_pos k') p p' 0 0) as Hinj.
  destruct (cbn_wrap_bits (N.succ_pos k) p 0) as [q z].
  destruct (cbn_wrap_bits (N.succ_pos k') p' 0) as [q' z'].
  cbn in Hs, Hs', Ha, Ha', Hinj. subst q q'.
  intros H. apply cbn_wrap_zeros_inj in H as [<- <-].
  assert (Hsz : Pos.size_nat (N.succ_pos k) = Pos.size_nat (N.succ_pos k')) by lia.
  destruct (Hinj Hsz eq_refl) as [Hm ->].
  split; [|reflexivity].
  apply N.succ_inj. rewrite <- !N.succ_pos_spec. now rewrite Hm.
Qed.

Lemma cbn_path_push_not_nil k p : cbn_path_push k p <> cbn_path_nil.
Proof.
  unfold cbn_path_push, cbn_path_nil.
  destruct (cbn_wrap_bits_fst_xI (N.succ_pos k) p 0) as [a Ha].
  destruct (cbn_wrap_bits (N.succ_pos k) p 0) as [q [|z]]; cbn in Ha |- *; subst q; discriminate.
Qed.

Lemma cbn_path_fold_inj ks ks' :
  fold_right cbn_path_push cbn_path_nil ks = fold_right cbn_path_push cbn_path_nil ks' -> ks = ks'.
Proof.
  revert ks'; induction ks as [|k ks IH]; intros [|k' ks'] H; cbn [fold_right] in H.
  - reflexivity.
  - symmetry in H. destruct (cbn_path_push_not_nil _ _ H).
  - destruct (cbn_path_push_not_nil _ _ H).
  - apply cbn_path_push_inj in H as [-> H]. f_equal. now apply IH.
Qed.

(** The code invariant for the entry [ce]: the term of [c] is the subterm of the entry's
  instantiated term at the path of [c]. [ks] lists the path steps newest first, as
  [cbn_c_path] stores them; [step t k] is the subterm of [t] at step [k], with the steps of the
  comment above [cbn_child] (and [tLetIn]: type 1; [tCoFix]: as [tFix]). *)
Definition cbn_code_inv (ce : cbn_code_entry) (c : cbn_code) : Prop :=
  let step (t : term) (k : N) : option term :=
    match t with
    | tApp f a => match k with N0 => Some f | Npos xH => Some a | _ => None end
    | tLambda _ d b | tProd _ d b =>
      match k with N0 => Some d | Npos xH => Some b | _ => None end
    | tLetIn _ b ty body =>
      match k with N0 => Some b | Npos xH => Some ty | Npos (xO xH) => Some body | _ => None end
    | tCase _ p scrut brs =>
      match k with
      | N0 => Some scrut
      | Npos xH => Some p.(preturn)
      | Npos (xO q) => nth_error p.(pparams) (Nat.pred (Pos.to_nat q))
      | Npos (xI q) => option_map bbody (nth_error brs (Nat.pred (Pos.to_nat q)))
      end
    | tProj _ a => match k with N0 => Some a | _ => None end
    | tFix m _ | tCoFix m _ => option_map dbody (nth_error m (N.to_nat k))
    | _ => None
    end
  in
  exists ks : list N,
    c.(cbn_c_path) = fold_right cbn_path_push cbn_path_nil ks /\
    fold_right (fun k ot => match ot with Some t => step t k | None => None end)
      (Some (cbn_inst_code ce.(cbn_ce_inst) ce.(cbn_ce_term))) ks = Some c.(cbn_c_term).

Lemma cbn_code_inv_root ce i :
  cbn_code_inv ce (cbn_mkCode i cbn_path_nil (cbn_inst_code ce.(cbn_ce_inst) ce.(cbn_ce_term))).
Proof. unfold cbn_code_inv; cbv zeta. exists []. now split. Qed.

Lemma cbn_code_inv_path_term ce c1 c2 :
  cbn_code_inv ce c1 -> cbn_code_inv ce c2 -> c1.(cbn_c_path) = c2.(cbn_c_path) ->
    c1.(cbn_c_term) = c2.(cbn_c_term).
Proof.
  unfold cbn_code_inv; cbv zeta.
  intros [ks [Hp1 Ht1]] [ks' [Hp2 Ht2]] E.
  rewrite Hp1, Hp2 in E. apply cbn_path_fold_inj in E. subst ks'. congruence.
Qed.

Lemma cbn_same_id_spec c1 c2 :
  cbn_same_id c1 c2 = true <-> c1.(cbn_c_entry) = c2.(cbn_c_entry) /\
    c1.(cbn_c_path) = c2.(cbn_c_path).
Proof.
  unfold cbn_same_id. split.
  - intros H. apply Bool.andb_true_iff in H as [H1 H2].
    apply cbn_key_eqb_spec in H1, H2. now split.
  - intros [H1 H2]. apply Bool.andb_true_iff. now split; apply cbn_key_eqb_spec.
Qed.

Lemma cbn_same_id_sound ce c1 c2 :
  cbn_same_id c1 c2 = true -> cbn_code_inv ce c1 -> cbn_code_inv ce c2 ->
    c1.(cbn_c_term) = c2.(cbn_c_term).
Proof.
  intros H H1 H2. apply cbn_same_id_spec in H as [_ Hp].
  exact (cbn_code_inv_path_term ce c1 c2 H1 H2 Hp).
Qed.

(** The same with the entries looked up in a code table: [cbn_same_id] gives equal indices, so
  both codes are read against one entry. *)
Lemma cbn_same_id_sound_table (codes : PTree.t cbn_code_entry) ce1 ce2 c1 c2 :
  cbn_same_id c1 c2 = true ->
  PTree.get c1.(cbn_c_entry) codes = Some ce1 -> cbn_code_inv ce1 c1 ->
  PTree.get c2.(cbn_c_entry) codes = Some ce2 -> cbn_code_inv ce2 c2 ->
  c1.(cbn_c_term) = c2.(cbn_c_term).
Proof.
  intros H G1 H1 G2 H2. pose proof H as [He _]%cbn_same_id_spec.
  rewrite He, G2 in G1. injection G1 as ->.
  exact (cbn_same_id_sound ce1 c1 c2 H H1 H2).
Qed.

(** [cbn_child] preserves [cbn_code_inv], at every step the machine takes. *)

Lemma cbn_case_param_step_pos i : cbn_case_param_step i = Npos (xO (N.succ_pos i)).
Proof. destruct i as [|p]; [reflexivity | destruct p; reflexivity]. Qed.

Lemma cbn_case_branch_step_pos i : cbn_case_branch_step i = Npos (xI (N.succ_pos i)).
Proof. destruct i as [|p]; [reflexivity | destruct p; reflexivity]. Qed.

Lemma cbn_succ_pos_to_nat i : Pos.to_nat (N.succ_pos i) = S (N.to_nat i).
Proof. destruct i as [|p]; [reflexivity | exact (Pos2Nat.inj_succ p)]. Qed.

Local Ltac cbn_code_inv_child_tac k :=
  unfold cbn_code_inv; cbv zeta;
  let ks := fresh "ks" in let Hp := fresh "Hp" in let Ht := fresh "Ht" in
  let Hc := fresh "Hc" in
  intros [ks [Hp Ht]] Hc; exists (k :: ks); split;
  [ cbn [fold_right cbn_child cbn_c_path]; now rewrite Hp
  | cbn [fold_right cbn_child cbn_c_term]; rewrite Ht, Hc; reflexivity ].

Lemma cbn_code_inv_child_app_fun ce c f a :
  cbn_code_inv ce c -> c.(cbn_c_term) = tApp f a -> cbn_code_inv ce (cbn_child c 0 f).
Proof. cbn_code_inv_child_tac 0%N. Qed.

Lemma cbn_code_inv_child_app_arg ce c f a :
  cbn_code_inv ce c -> c.(cbn_c_term) = tApp f a -> cbn_code_inv ce (cbn_child c 1 a).
Proof. cbn_code_inv_child_tac 1%N. Qed.

Lemma cbn_code_inv_child_lambda_dom ce c na d b :
  cbn_code_inv ce c -> c.(cbn_c_term) = tLambda na d b -> cbn_code_inv ce (cbn_child c 0 d).
Proof. cbn_code_inv_child_tac 0%N. Qed.

Lemma cbn_code_inv_child_lambda_body ce c na d b :
  cbn_code_inv ce c -> c.(cbn_c_term) = tLambda na d b -> cbn_code_inv ce (cbn_child c 1 b).
Proof. cbn_code_inv_child_tac 1%N. Qed.

Lemma cbn_code_inv_child_prod_dom ce c na d b :
  cbn_code_inv ce c -> c.(cbn_c_term) = tProd na d b -> cbn_code_inv ce (cbn_child c 0 d).
Proof. cbn_code_inv_child_tac 0%N. Qed.

Lemma cbn_code_inv_child_prod_body ce c na d b :
  cbn_code_inv ce c -> c.(cbn_c_term) = tProd na d b -> cbn_code_inv ce (cbn_child c 1 b).
Proof. cbn_code_inv_child_tac 1%N. Qed.

Lemma cbn_code_inv_child_letin_def ce c na b ty body :
  cbn_code_inv ce c -> c.(cbn_c_term) = tLetIn na b ty body -> cbn_code_inv ce (cbn_child c 0 b).
Proof. cbn_code_inv_child_tac 0%N. Qed.

Lemma cbn_code_inv_child_letin_type ce c na b ty body :
  cbn_code_inv ce c -> c.(cbn_c_term) = tLetIn na b ty body -> cbn_code_inv ce (cbn_child c 1 ty).
Proof. cbn_code_inv_child_tac 1%N. Qed.

Lemma cbn_code_inv_child_letin_body ce c na b ty body :
  cbn_code_inv ce c -> c.(cbn_c_term) = tLetIn na b ty body -> cbn_code_inv ce (cbn_child c 2 body).
Proof. cbn_code_inv_child_tac 2%N. Qed.

Lemma cbn_code_inv_child_case_scrut ce c ci p scrut brs :
  cbn_code_inv ce c -> c.(cbn_c_term) = tCase ci p scrut brs ->
    cbn_code_inv ce (cbn_child c 0 scrut).
Proof. cbn_code_inv_child_tac 0%N. Qed.

Lemma cbn_code_inv_child_case_return ce c ci p scrut brs :
  cbn_code_inv ce c -> c.(cbn_c_term) = tCase ci p scrut brs ->
    cbn_code_inv ce (cbn_child c 1 p.(preturn)).
Proof. cbn_code_inv_child_tac 1%N. Qed.

Lemma cbn_code_inv_child_case_param ce c ci p scrut brs i t :
  cbn_code_inv ce c -> c.(cbn_c_term) = tCase ci p scrut brs ->
  nth_error p.(pparams) (N.to_nat i) = Some t ->
  cbn_code_inv ce (cbn_child c (cbn_case_param_step i) t).
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [Hp Ht]] Hc Hn.
  exists (cbn_case_param_step i :: ks); split.
  - cbn [fold_right cbn_child cbn_c_path]. now rewrite Hp.
  - cbn [fold_right cbn_child cbn_c_term]. rewrite Ht, Hc, cbn_case_param_step_pos.
    cbv beta iota. rewrite cbn_succ_pos_to_nat. exact Hn.
Qed.

Lemma cbn_code_inv_child_case_branch ce c ci p scrut brs i br :
  cbn_code_inv ce c -> c.(cbn_c_term) = tCase ci p scrut brs ->
  nth_error brs (N.to_nat i) = Some br ->
  cbn_code_inv ce (cbn_child c (cbn_case_branch_step i) br.(bbody)).
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [Hp Ht]] Hc Hn.
  exists (cbn_case_branch_step i :: ks); split.
  - cbn [fold_right cbn_child cbn_c_path]. now rewrite Hp.
  - cbn [fold_right cbn_child cbn_c_term]. rewrite Ht, Hc, cbn_case_branch_step_pos.
    cbv beta iota. rewrite cbn_succ_pos_to_nat. cbn [Nat.pred]. now rewrite Hn.
Qed.

Lemma cbn_code_inv_child_proj ce c pr a :
  cbn_code_inv ce c -> c.(cbn_c_term) = tProj pr a -> cbn_code_inv ce (cbn_child c 0 a).
Proof. cbn_code_inv_child_tac 0%N. Qed.

Lemma cbn_code_inv_child_fix ce c mfix idx k d :
  cbn_code_inv ce c -> c.(cbn_c_term) = tFix mfix idx -> nth_error mfix (N.to_nat k) = Some d ->
  cbn_code_inv ce (cbn_child c k d.(dbody)).
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [Hp Ht]] Hc Hn.
  exists (k :: ks); split.
  - cbn [fold_right cbn_child cbn_c_path]. now rewrite Hp.
  - cbn [fold_right cbn_child cbn_c_term]. rewrite Ht, Hc. cbv beta iota. now rewrite Hn.
Qed.

Lemma cbn_code_inv_child_cofix ce c mfix idx k d :
  cbn_code_inv ce c -> c.(cbn_c_term) = tCoFix mfix idx -> nth_error mfix (N.to_nat k) = Some d ->
  cbn_code_inv ce (cbn_child c k d.(dbody)).
Proof.
  unfold cbn_code_inv; cbv zeta. intros [ks [Hp Ht]] Hc Hn.
  exists (k :: ks); split.
  - cbn [fold_right cbn_child cbn_c_path]. now rewrite Hp.
  - cbn [fold_right cbn_child cbn_c_term]. rewrite Ht, Hc. cbv beta iota. now rewrite Hn.
Qed.

(** ** Occurrence count and structural hash of a code *)

(** Occurrences of [tRel k], capped at 2: an occurrence under a lambda, product, fixpoint or
  cofixpoint counts 2, match branches take the maximum. Only cost depends on it. *)
Fixpoint cbn_occ (k : nat) (t : term) : nat :=
  match t with
  | tRel n => if n == k then 1 else 0
  | tApp f a => Nat.min 2 (cbn_occ k f + cbn_occ k a)
  | tLambda _ d b | tProd _ d b => Nat.min 2 (cbn_occ k d + 2 * cbn_occ (S k) b)
  | tLetIn _ b ty body => Nat.min 2 (cbn_occ k b + cbn_occ k ty + cbn_occ (S k) body)
  | tCase _ p c brs =>
    let pp := fold_left (fun n x => n + cbn_occ k x) p.(pparams) 0 in
    let pr := cbn_occ (k + #|p.(pcontext)|) p.(preturn) in
    let bm := fold_left (fun m b => Nat.max m (cbn_occ (k + #|b.(bcontext)|) b.(bbody))) brs 0 in
    Nat.min 2 (pp + pr + cbn_occ k c + bm)
  | tProj _ c => cbn_occ k c
  | tFix m _ | tCoFix m _ =>
    let n := #|m| in
    if existsb (fun d => negb (cbn_occ k d.(dtype) == 0) || negb (cbn_occ (k + n) d.(dbody) == 0)) m
    then 2 else 0
  | tEvar _ _ => 2
  | _ => 0
  end.

Definition cbn_hmask : N := 2305843009213693951%N. (* 2^61 - 1 *)

Definition cbn_hmix (h x : N) : N := N.land (N.add (N.sub (N.shiftl h 5) h) x) cbn_hmask.

Fixpoint cbn_hash_string (h : N) (s : String.t) : N :=
  match s with
  | String.EmptyString => h
  | String.String b s => cbn_hash_string (cbn_hmix h (ByteCompare.ByteN.to_N b)) s
  end.

(** A structural hash: equal terms, and terms equal up to universes and names, have equal
  hashes. It is only a filter in front of [eqb_term_upto_univ]. *)
Fixpoint cbn_thash (t : term) : N :=
  match t with
  | tRel n => cbn_hmix 1 (N.of_nat n)
  | tVar _ => 2%N
  | tEvar n l => fold_left (fun h x => cbn_hmix h (cbn_thash x)) l (cbn_hmix 3 (N.of_nat n))
  | tSort _ => 4%N
  | tProd _ a b => cbn_hmix (cbn_hmix 5 (cbn_thash a)) (cbn_thash b)
  | tLambda _ a b => cbn_hmix (cbn_hmix 6 (cbn_thash a)) (cbn_thash b)
  | tLetIn _ b ty body => cbn_hmix (cbn_hmix (cbn_hmix 7 (cbn_thash b)) (cbn_thash ty))
    (cbn_thash body)
  | tApp f a => cbn_hmix (cbn_hmix 8 (cbn_thash f)) (cbn_thash a)
  | tConst kn _ => cbn_hash_string 9 (snd kn)
  | tInd i _ => cbn_hmix (cbn_hash_string 10 (snd i.(inductive_mind))) (N.of_nat i.(inductive_ind))
  | tConstruct i n _ =>
    cbn_hmix (cbn_hmix (cbn_hash_string 11 (snd i.(inductive_mind))) (N.of_nat i.(inductive_ind)))
      (N.of_nat n)
  | tCase _ p c brs =>
    let h := fold_left (fun h x => cbn_hmix h (cbn_thash x)) p.(pparams)
      (cbn_hmix 12 (N.of_nat #|brs|)) in
    let h := cbn_hmix (cbn_hmix h (cbn_thash p.(preturn))) (cbn_thash c) in
    fold_left (fun h b => cbn_hmix h (cbn_thash b.(bbody))) brs h
  | tProj p c => cbn_hmix (cbn_hmix 13 (N.of_nat p.(proj_arg))) (cbn_thash c)
  | tFix m i =>
    fold_left (fun h d => cbn_hmix (cbn_hmix h (cbn_thash d.(dtype))) (cbn_thash d.(dbody))) m
      (cbn_hmix 14 (N.of_nat i))
  | tCoFix m i =>
    fold_left (fun h d => cbn_hmix (cbn_hmix h (cbn_thash d.(dtype))) (cbn_thash d.(dbody))) m
      (cbn_hmix 15 (N.of_nat i))
  | _ => 16%N
  end.

(** ** Machine data *)

Inductive cbn_slot :=
| CbnSAddr (a : cbn_haddr)
| CbnSInl (vals : list cbn_slot) (nvals goff : nat) (c : cbn_code).

Record cbn_env := cbn_mkEnv {
  cbn_ev_vals : list cbn_slot;
  cbn_ev_nvals : nat;
  cbn_ev_goff : nat }.

Definition cbn_env_empty : cbn_env := cbn_mkEnv [] 0 0.

Definition cbn_env_push (x : cbn_slot) (e : cbn_env) : cbn_env :=
  cbn_mkEnv (x :: e.(cbn_ev_vals)) (S e.(cbn_ev_nvals)) e.(cbn_ev_goff).

Definition cbn_env_push_addrs (l : list cbn_haddr) (e : cbn_env) : cbn_env :=
  fold_left (fun e a => cbn_env_push (CbnSAddr a) e) l e.

Inductive cbn_neutral :=
| CbnNVar (lvl : nat)   (* a context variable without a body or a fresh variable, as a level *)
| CbnNConst (h : term). (* an axiom or opaque constant [tConst kn u] *)

Inductive cbn_value :=
| CbnVCon (h : term) (sp : list cbn_haddr)                      (* [tConstruct]/[tInd] head *)
| CbnVLam (e : cbn_env) (c : cbn_code)                          (* [tLambda] closure *)
| CbnVFix (e : cbn_env) (c : cbn_code) (idx : nat) (sp : list cbn_haddr)
    (* fixpoint [idx] of the [tFix] code [c], applied to too few arguments *)
| CbnVStuckFix (e : cbn_env) (c : cbn_code) (idx : nat) (sp : list cbn_haddr)
    (* fixpoint whose recursive argument is neutral or stuck *)
| CbnVNeu (h : cbn_neutral) (sp : list cbn_haddr)
| CbnVOpen (e : cbn_env) (c : cbn_code)                         (* [tSort], [tProd], [tPrim] *)
| CbnVStuck (e : cbn_env) (c : cbn_code) (sp : list cbn_haddr).     (* stuck [tCase]/[tProj] *)

(** [CbnCFwd a]: the new address [a] of a cell that the collector copied; it exists only in the
  old heap during a collection. *)
Inductive cbn_cell :=
| CbnCSusp (vals : list cbn_slot) (nvals goff : nat) (c : cbn_code)
| CbnCDone (v : cbn_value)
| CbnCBusy
| CbnCFwd (a : cbn_haddr).

(** What a caller holds across a call that can allocate. *)
Inductive cbn_root :=
| CbnRA (a : cbn_haddr)
| CbnRSl (x : cbn_slot)
| CbnRE (e : cbn_env)
| CbnRV (v : cbn_value)
| CbnRSk (l : list cbn_slot)
| CbnRSp (l : list cbn_haddr)
| CbnRC (c : cbn_cell).

Definition cbn_spine_of (v : cbn_value) : list cbn_haddr :=
  match v with
  | CbnVCon _ sp | CbnVFix _ _ _ sp | CbnVStuckFix _ _ _ sp | CbnVNeu _ sp | CbnVStuck _ _ sp => sp
  | CbnVLam _ _ | CbnVOpen _ _ => []
  end.

Definition cbn_add_spine (v : cbn_value) (l : list cbn_haddr) : option cbn_value :=
  match v with
  | CbnVCon h sp => Some (CbnVCon h (sp ++ l))
  | CbnVStuckFix e c i sp => Some (CbnVStuckFix e c i (sp ++ l))
  | CbnVNeu h sp => Some (CbnVNeu h (sp ++ l))
  | CbnVStuck e c sp => Some (CbnVStuck e c (sp ++ l))
  | _ => None
  end.

(** ** Renaming: one function per type that holds heap addresses *)

Section Rename.
  Context {G : Type} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G)).

  Fixpoint cbn_rn_slot (x : cbn_slot) (g : G) {struct x} : cbn_res (cbn_slot * G) :=
    match x with
    | CbnSAddr a => cbn2 (a, g) := f a g in CbnCOk (CbnSAddr a, g)
    | CbnSInl vs n o c =>
      let fix go (l : list cbn_slot) (g : G) : cbn_res (list cbn_slot * G) :=
        match l with
        | [] => CbnCOk ([], g)
        | y :: l =>
          cbn2 (y, g) := cbn_rn_slot y g in
          cbn2 (l, g) := go l g in
          CbnCOk (y :: l, g)
        end in
      cbn2 (vs, g) := go vs g in CbnCOk (CbnSInl vs n o c, g)
    end.

  Fixpoint cbn_rn_slots (l : list cbn_slot) (g : G) : cbn_res (list cbn_slot * G) :=
    match l with
    | [] => CbnCOk ([], g)
    | y :: l =>
      cbn2 (y, g) := cbn_rn_slot y g in
      cbn2 (l, g) := cbn_rn_slots l g in
      CbnCOk (y :: l, g)
    end.

  Fixpoint cbn_rn_addrs (l : list cbn_haddr) (g : G) : cbn_res (list cbn_haddr * G) :=
    match l with
    | [] => CbnCOk ([], g)
    | a :: l =>
      cbn2 (a, g) := f a g in
      cbn2 (l, g) := cbn_rn_addrs l g in
      CbnCOk (a :: l, g)
    end.

  Definition cbn_rn_env (e : cbn_env) (g : G) : cbn_res (cbn_env * G) :=
    cbn2 (vs, g) := cbn_rn_slots e.(cbn_ev_vals) g in CbnCOk
      (cbn_mkEnv vs e.(cbn_ev_nvals) e.(cbn_ev_goff), g).

  Definition cbn_rn_value (v : cbn_value) (g : G) : cbn_res (cbn_value * G) :=
    match v with
    | CbnVCon h sp => cbn2 (sp, g) := cbn_rn_addrs sp g in CbnCOk (CbnVCon h sp, g)
    | CbnVLam e c => cbn2 (e, g) := cbn_rn_env e g in CbnCOk (CbnVLam e c, g)
    | CbnVFix e c i sp =>
      cbn2 (e, g) := cbn_rn_env e g in cbn2 (sp, g) :=
        cbn_rn_addrs sp g in CbnCOk (CbnVFix e c i sp, g)
    | CbnVStuckFix e c i sp =>
      cbn2 (e, g) := cbn_rn_env e g in cbn2 (sp, g) :=
        cbn_rn_addrs sp g in CbnCOk (CbnVStuckFix e c i sp, g)
    | CbnVNeu h sp => cbn2 (sp, g) := cbn_rn_addrs sp g in CbnCOk (CbnVNeu h sp, g)
    | CbnVOpen e c => cbn2 (e, g) := cbn_rn_env e g in CbnCOk (CbnVOpen e c, g)
    | CbnVStuck e c sp =>
      cbn2 (e, g) := cbn_rn_env e g in cbn2 (sp, g) :=
        cbn_rn_addrs sp g in CbnCOk (CbnVStuck e c sp, g)
    end.

  Definition cbn_rn_cell (cl : cbn_cell) (g : G) : cbn_res (cbn_cell * G) :=
    match cl with
    | CbnCSusp vs n o c => cbn2 (vs, g) := cbn_rn_slots vs g in CbnCOk (CbnCSusp vs n o c, g)
    | CbnCDone v => cbn2 (v, g) := cbn_rn_value v g in CbnCOk (CbnCDone v, g)
    | CbnCBusy => CbnCOk (CbnCBusy, g)
    | CbnCFwd a => cbn2 (a, g) := f a g in CbnCOk (CbnCFwd a, g)
    end.

  Definition cbn_rn_root (r : cbn_root) (g : G) : cbn_res (cbn_root * G) :=
    match r with
    | CbnRA a => cbn2 (a, g) := f a g in CbnCOk (CbnRA a, g)
    | CbnRSl x => cbn2 (x, g) := cbn_rn_slot x g in CbnCOk (CbnRSl x, g)
    | CbnRE e => cbn2 (e, g) := cbn_rn_env e g in CbnCOk (CbnRE e, g)
    | CbnRV v => cbn2 (v, g) := cbn_rn_value v g in CbnCOk (CbnRV v, g)
    | CbnRSk l => cbn2 (l, g) := cbn_rn_slots l g in CbnCOk (CbnRSk l, g)
    | CbnRSp l => cbn2 (l, g) := cbn_rn_addrs l g in CbnCOk (CbnRSp l, g)
    | CbnRC c => cbn2 (c, g) := cbn_rn_cell c g in CbnCOk (CbnRC c, g)
    end.

  Fixpoint cbn_rn_roots (l : list cbn_root) (g : G) : cbn_res (list cbn_root * G) :=
    match l with
    | [] => CbnCOk ([], g)
    | r :: l =>
      cbn2 (r, g) := cbn_rn_root r g in
      cbn2 (l, g) := cbn_rn_roots l g in
      CbnCOk (r :: l, g)
    end.

  (** The values of [cbn_st_gam]. *)
  Fixpoint cbn_rn_tree' (m : PTree.tree' cbn_haddr) (g : G) : cbn_res (PTree.tree' cbn_haddr * G) :=
    match m with
    | PTree.Node001 r => cbn2 (r, g) := cbn_rn_tree' r g in CbnCOk (PTree.Node001 r, g)
    | PTree.Node010 x => cbn2 (x, g) := f x g in CbnCOk (PTree.Node010 x, g)
    | PTree.Node011 x r =>
      cbn2 (x, g) := f x g in cbn2 (r, g) := cbn_rn_tree' r g in CbnCOk (PTree.Node011 x r, g)
    | PTree.Node100 l => cbn2 (l, g) := cbn_rn_tree' l g in CbnCOk (PTree.Node100 l, g)
    | PTree.Node101 l r =>
      cbn2 (l, g) := cbn_rn_tree' l g in cbn2 (r, g) :=
        cbn_rn_tree' r g in CbnCOk (PTree.Node101 l r, g)
    | PTree.Node110 l x =>
      cbn2 (l, g) := cbn_rn_tree' l g in cbn2 (x, g) := f x g in CbnCOk (PTree.Node110 l x, g)
    | PTree.Node111 l x r =>
      cbn2 (l, g) := cbn_rn_tree' l g in cbn2 (x, g) := f x g in cbn2 (r, g) := cbn_rn_tree' r g in
      CbnCOk (PTree.Node111 l x r, g)
    end.

  Definition cbn_rn_ptree (m : PTree.t cbn_haddr) (g : G) : cbn_res (PTree.t cbn_haddr * G) :=
    match m with
    | PTree.Empty => CbnCOk (PTree.Empty, g)
    | PTree.Nodes m => cbn2 (m, g) := cbn_rn_tree' m g in CbnCOk (PTree.Nodes m, g)
    end.
End Rename.

(** ** Lemmas on the machine's data structures

  Slots, environments, values, cells and roots: their renamings and the heap addresses they
  hold. Nothing here mentions the heap, reduction, cumulativity or typing.

  A renaming takes an effectful map [f : cbn_haddr -> G -> cbn_res (cbn_haddr * G)], which threads a
  state and may fail. [mp_X u] is the renaming of [X] by a total map [u : cbn_haddr -> cbn_haddr],
  and [ad_X] lists the addresses that [X] holds, in the order in which the functions of the
  [Rename] section visit them. *)

(** *** Induction on slots *)

(** The generated [cbn_slot_ind] gives no hypothesis on the slots of an [CbnSInl]. *)
Lemma cbn_slot_ind' (P : cbn_slot -> Prop)
    (Ha : forall a, P (CbnSAddr a))
    (Hi : forall vs n o c, Forall P vs -> P (CbnSInl vs n o c)) :
  forall x, P x.
Proof.
  fix IH 1. intros [a|vs n o c].
  - apply Ha.
  - apply Hi. revert vs. fix IHl 1. intros [|y vs].
    + constructor.
    + constructor; [apply IH|apply IHl].
Qed.

(** *** List facts used below *)

Lemma cbn_length_app_cbn {A} (l1 l2 : list A) : #|l1 ++ l2| = #|l1| + #|l2|.
Proof. induction l1; simpl; [reflexivity|]. rewrite IHl1. reflexivity. Qed.

(** *** Renaming by a total map *)

Fixpoint cbn_mp_slot (u : cbn_haddr -> cbn_haddr) (x : cbn_slot) : cbn_slot :=
  match x with
  | CbnSAddr a => CbnSAddr (u a)
  | CbnSInl vs n o c => CbnSInl (map (cbn_mp_slot u) vs) n o c
  end.

Definition cbn_mp_slots (u : cbn_haddr -> cbn_haddr) (l : list cbn_slot) : list cbn_slot :=
  map (cbn_mp_slot u) l.

Definition cbn_mp_env (u : cbn_haddr -> cbn_haddr) (e : cbn_env) : cbn_env :=
  cbn_mkEnv (cbn_mp_slots u e.(cbn_ev_vals)) e.(cbn_ev_nvals) e.(cbn_ev_goff).

Definition cbn_mp_value (u : cbn_haddr -> cbn_haddr) (v : cbn_value) : cbn_value :=
  match v with
  | CbnVCon h sp => CbnVCon h (map u sp)
  | CbnVLam e c => CbnVLam (cbn_mp_env u e) c
  | CbnVFix e c i sp => CbnVFix (cbn_mp_env u e) c i (map u sp)
  | CbnVStuckFix e c i sp => CbnVStuckFix (cbn_mp_env u e) c i (map u sp)
  | CbnVNeu h sp => CbnVNeu h (map u sp)
  | CbnVOpen e c => CbnVOpen (cbn_mp_env u e) c
  | CbnVStuck e c sp => CbnVStuck (cbn_mp_env u e) c (map u sp)
  end.

Definition cbn_mp_cell (u : cbn_haddr -> cbn_haddr) (cl : cbn_cell) : cbn_cell :=
  match cl with
  | CbnCSusp vs n o c => CbnCSusp (cbn_mp_slots u vs) n o c
  | CbnCDone v => CbnCDone (cbn_mp_value u v)
  | CbnCBusy => CbnCBusy
  | CbnCFwd a => CbnCFwd (u a)
  end.

Definition cbn_mp_root (u : cbn_haddr -> cbn_haddr) (r : cbn_root) : cbn_root :=
  match r with
  | CbnRA a => CbnRA (u a)
  | CbnRSl x => CbnRSl (cbn_mp_slot u x)
  | CbnRE e => CbnRE (cbn_mp_env u e)
  | CbnRV v => CbnRV (cbn_mp_value u v)
  | CbnRSk l => CbnRSk (cbn_mp_slots u l)
  | CbnRSp l => CbnRSp (map u l)
  | CbnRC c => CbnRC (cbn_mp_cell u c)
  end.

Definition cbn_mp_roots (u : cbn_haddr -> cbn_haddr) (l : list cbn_root) : list cbn_root :=
  map (cbn_mp_root u) l.

(** *** The addresses a structure holds *)

Fixpoint cbn_ad_slot (x : cbn_slot) : list cbn_haddr :=
  match x with
  | CbnSAddr a => [a]
  | CbnSInl vs _ _ _ => flat_map cbn_ad_slot vs
  end.

Definition cbn_ad_slots (l : list cbn_slot) : list cbn_haddr := flat_map cbn_ad_slot l.

Definition cbn_ad_env (e : cbn_env) : list cbn_haddr := cbn_ad_slots e.(cbn_ev_vals).

Definition cbn_ad_value (v : cbn_value) : list cbn_haddr :=
  match v with
  | CbnVCon _ sp => sp
  | CbnVLam e _ => cbn_ad_env e
  | CbnVFix e _ _ sp => cbn_ad_env e ++ sp
  | CbnVStuckFix e _ _ sp => cbn_ad_env e ++ sp
  | CbnVNeu _ sp => sp
  | CbnVOpen e _ => cbn_ad_env e
  | CbnVStuck e _ sp => cbn_ad_env e ++ sp
  end.

Definition cbn_ad_cell (cl : cbn_cell) : list cbn_haddr :=
  match cl with
  | CbnCSusp vs _ _ _ => cbn_ad_slots vs
  | CbnCDone v => cbn_ad_value v
  | CbnCBusy => []
  | CbnCFwd a => [a]
  end.

Definition cbn_ad_root (r : cbn_root) : list cbn_haddr :=
  match r with
  | CbnRA a => [a]
  | CbnRSl x => cbn_ad_slot x
  | CbnRE e => cbn_ad_env e
  | CbnRV v => cbn_ad_value v
  | CbnRSk l => cbn_ad_slots l
  | CbnRSp l => l
  | CbnRC c => cbn_ad_cell c
  end.

Definition cbn_ad_roots (l : list cbn_root) : list cbn_haddr := flat_map cbn_ad_root l.

(** *** [cbn_rn_slot] on an inline suspension is [cbn_rn_slots] on its slots *)

(** [cbn_rn_slot] repeats the body of [cbn_rn_slots] as a local fixpoint; this is the only lemma
  that has to look at that copy. *)
Lemma cbn_rn_slot_SInl {G} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G))
    (l : list cbn_slot) (n o : nat) (c : cbn_code) (g : G) :
  cbn_rn_slot f (CbnSInl l n o c) g =
  match cbn_rn_slots f l g with
  | CbnCOk (l', g') => CbnCOk (CbnSInl l' n o c, g')
  | CbnCFail w => CbnCFail w
  end.
Proof.
  revert g. induction l as [|y l IH]; intros g; [reflexivity|].
  simpl. destruct (cbn_rn_slot f y g) as [[y' g1]|w]; [|reflexivity].
  specialize (IH g1). simpl in IH.
  revert IH. destruct (cbn_rn_slots f l g1) as [[l3 g3]|w3];
    match goal with |- context [?X l g1] => destruct (X l g1) as [[l2 g2]|w2] end;
    intros IH; inversion IH; subst; reflexivity.
Qed.

(** *** Shape: lengths, slot lists and spines of renamed and extended structures *)

Lemma cbn_rn_slots_length {G} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G))
  (l : list cbn_slot) (g : G)
    (l' : list cbn_slot) (g' : G) :
  cbn_rn_slots f l g = CbnCOk (l', g') -> #|l'| = #|l|.
Proof.
  revert g l' g'. induction l as [|y l IH]; intros g l' g' H; simpl in H.
  - inversion H; reflexivity.
  - destruct (cbn_rn_slot f y g) as [[y' g1]|w]; [|discriminate].
    destruct (cbn_rn_slots f l g1) as [[l2 g2]|w] eqn:E; [|discriminate].
    inversion H; subst. simpl. f_equal. exact (IH _ _ _ E).
Qed.

Lemma cbn_rn_env_vals {G} (f : cbn_haddr -> G -> cbn_res (cbn_haddr * G)) (e : cbn_env) (g : G)
    (e' : cbn_env) (g' : G) :
  cbn_rn_env f e g = CbnCOk (e', g') -> cbn_rn_slots f e.(cbn_ev_vals) g
    = CbnCOk (e'.(cbn_ev_vals), g').
Proof.
  unfold cbn_rn_env. destruct (cbn_rn_slots f (cbn_ev_vals e) g) as [[vs g1]|w]; intros H;
    inversion H; subst. reflexivity.
Qed.

Lemma cbn_env_push_addrs_vals (l : list cbn_haddr) (e : cbn_env) :
  cbn_env_push_addrs l e
  = cbn_mkEnv (map CbnSAddr (List.rev l) ++ e.(cbn_ev_vals)) (#|l| + e.(cbn_ev_nvals))
    e.(cbn_ev_goff).
Proof.
  unfold cbn_env_push_addrs. revert e. induction l as [|a l IH]; intros e.
  - destruct e; reflexivity.
  - simpl. rewrite IH. simpl. rewrite map_app, <- app_assoc, Nat.add_succ_r. reflexivity.
Qed.

Lemma cbn_mp_spine_of (u : cbn_haddr -> cbn_haddr) (v : cbn_value) :
  cbn_spine_of (cbn_mp_value u v) = map u (cbn_spine_of v).
Proof. destruct v; reflexivity. Qed.

(** ** The heap: a binary random-access list indexed by the bits of the address *)

Inductive cbn_btree (A : Type) :=
| CbnBLeaf (x : A)
| CbnBNode (l r : cbn_btree A)
| CbnBEmpty.
Arguments CbnBLeaf {A} x.
Arguments CbnBNode {A} l r.
Arguments CbnBEmpty {A}.

Inductive cbn_digit (A : Type) :=
| CbnDZero
| CbnDOne (t : cbn_btree A).
Arguments CbnDZero {A}.
Arguments CbnDOne {A} t.

(** The digits of the number of allocated addresses, least significant first. *)
Definition cbn_bheap (A : Type) := list (cbn_digit A).

(** Insert a tree of depth [j] at position [j] (the carry of a binary increment). The tree
  already at a position holds the older cells, so it goes left. *)
Fixpoint cbn_bh_carry {A} (t : cbn_btree A) (h : cbn_bheap A) : cbn_bheap A :=
  match h with
  | [] => [CbnDOne t]
  | CbnDZero :: h => CbnDOne t :: h
  | CbnDOne t' :: h => CbnDZero :: cbn_bh_carry (CbnBNode t' t) h
  end.

Definition cbn_bh_cons {A} (x : A) (h : cbn_bheap A) : cbn_bheap A := cbn_bh_carry (CbnBLeaf x) h.

(** The heap of the dropped addresses below [p]: the digits of [p], each tree [CbnBEmpty]. *)
Fixpoint cbn_bh_holes {A} (p : positive) : cbn_bheap A :=
  match p with
  | xH => [CbnDOne CbnBEmpty]
  | xO p => CbnDZero :: cbn_bh_holes p
  | xI p => CbnDOne CbnBEmpty :: cbn_bh_holes p
  end.

(** A path in a tree, top split first. *)
Inductive cbn_bpath := CbnPEnd | CbnPL (q : cbn_bpath) | CbnPR (q : cbn_bpath).

(** The scan, from the current position up: [acc] is the path of the bits below it (the
  latest first), [cand] the tree and path of the cell if the bits from here on are equal
  to the digits. Beyond the address's highest bit 1 ([cbn_bh_top]) its bits are 0. *)
Fixpoint cbn_bh_top {A} (h : cbn_bheap A) (acc : cbn_bpath)
  (cand : option (cbn_btree A * cbn_bpath))
  : option (cbn_btree A * cbn_bpath) :=
  match h with
  | [] => cand
  | CbnDZero :: h => cbn_bh_top h (CbnPL acc) cand
  | CbnDOne t :: h => cbn_bh_top h (CbnPL acc) (Some (t, acc))
  end.

Fixpoint cbn_bh_scan {A} (p : positive) (h : cbn_bheap A) (acc : cbn_bpath)
  (cand : option (cbn_btree A * cbn_bpath)) : option (cbn_btree A * cbn_bpath) :=
  match p, h with
  | _, [] => None
  | xH, CbnDZero :: h => cbn_bh_top h (CbnPR acc) None
  | xH, CbnDOne _ :: h => cbn_bh_top h (CbnPR acc) cand
  | xO p, CbnDZero :: h => cbn_bh_scan p h (CbnPL acc) cand
  | xO p, CbnDOne t :: h => cbn_bh_scan p h (CbnPL acc) (Some (t, acc))
  | xI p, CbnDZero :: h => cbn_bh_scan p h (CbnPR acc) None
  | xI p, CbnDOne _ :: h => cbn_bh_scan p h (CbnPR acc) cand
  end.

(** The tree that holds the cell of address [a] and the cell's path in it; [None] unless
  [a] is below the number that the digits [h] encode. *)
Definition cbn_bh_find {A} (a : cbn_haddr) (h : cbn_bheap A) : option (cbn_btree A * cbn_bpath) :=
  cbn_bh_scan a.(cbn_ha_p) h CbnPEnd None.

Fixpoint cbn_bt_get {A} (q : cbn_bpath) (t : cbn_btree A) : option A :=
  match q, t with
  | CbnPEnd, CbnBLeaf x => Some x
  | CbnPL q, CbnBNode l _ => cbn_bt_get q l
  | CbnPR q, CbnBNode _ r => cbn_bt_get q r
  | _, _ => None
  end.

Fixpoint cbn_bt_set {A} (q : cbn_bpath) (x : A) (t : cbn_btree A) : option (cbn_btree A) :=
  match q, t with
  | CbnPEnd, CbnBLeaf _ => Some (CbnBLeaf x)
  | CbnPL q, CbnBNode l r => option_map (fun l => CbnBNode l r) (cbn_bt_set q x l)
  | CbnPR q, CbnBNode l r => option_map (fun r => CbnBNode l r) (cbn_bt_set q x r)
  | _, _ => None
  end.

(** Replace the tree at the position given by the length of [q]. *)
Fixpoint cbn_bh_put {A} (q : cbn_bpath) (t : cbn_btree A) (h : cbn_bheap A)
  : option (cbn_bheap A) :=
  match q, h with
  | CbnPEnd, CbnDOne _ :: h => Some (CbnDOne t :: h)
  | (CbnPL q | CbnPR q), d :: h => option_map (cons d) (cbn_bh_put q t h)
  | _, _ => None
  end.

Definition cbn_bh_get {A} (a : cbn_haddr) (h : cbn_bheap A) : option A :=
  match cbn_bh_find a h with
  | Some (t, q) => cbn_bt_get q t
  | None => None
  end.

Definition cbn_bh_upd {A} (a : cbn_haddr) (x : A) (h : cbn_bheap A) : option (cbn_bheap A) :=
  match cbn_bh_find a h with
  | Some (t, q) =>
    match cbn_bt_set q x t with
    | Some t => cbn_bh_put q t h
    | None => None
    end
  | None => None
  end.

(** ** Laws of the heap

  [cbn_bh_ok lo n h]: [h] is the heap reached from [cbn_bh_holes lo] by [cbn_bh_cons] and
  [cbn_bh_upd], with [n] the next address ([lo] plus the number of [cbn_bh_cons]). The laws:
  [cbn_bh_get_cons_new], [cbn_bh_get_cons_old], [cbn_bh_get_upd_same], [cbn_bh_get_upd_other],
  [cbn_bh_upd_none], [cbn_bh_upd_ok]. The rest of this part are the steps of their proofs. The laws
  over the state that the proofs use are after the state's operations. *)

(** The digits of [h] are the binary digits of [n], least significant first. *)
Inductive cbn_bh_digits {A} : cbn_bheap A -> positive -> Prop :=
| cbn_bh_digits_one t : cbn_bh_digits [CbnDOne t] xH
| cbn_bh_digits_zero h n : cbn_bh_digits h n -> cbn_bh_digits (CbnDZero :: h) (xO n)
| cbn_bh_digits_more t h n : cbn_bh_digits h n -> cbn_bh_digits (CbnDOne t :: h) (xI n).

(** The heaps that the machine builds: from the holes below [lo], [cbn_bh_cons] (the next
  address goes from [n] to [Pos.succ n]) and [cbn_bh_upd]. *)
Inductive cbn_bh_ok {A} (lo : positive) : positive -> cbn_bheap A -> Prop :=
| cbn_bh_ok_holes : cbn_bh_ok lo lo (cbn_bh_holes lo)
| cbn_bh_ok_cons n h x : cbn_bh_ok lo n h -> cbn_bh_ok lo (Pos.succ n) (cbn_bh_cons x h)
| cbn_bh_ok_upd n h a x h' : cbn_bh_ok lo n h -> cbn_bh_upd a x h = Some h' -> cbn_bh_ok lo n h'.

(** *** Trees *)

Lemma cbn_bt_get_set_same {A} q (x : A) t t' : cbn_bt_set q x t = Some t' ->
  cbn_bt_get q t' = Some x.
Proof.
  revert t t'; induction q as [|q IH|q IH]; intros t t' H; destruct t as [y|l r|];
    cbn in H; try discriminate.
  - injection H as <-; reflexivity.
  - destruct (cbn_bt_set q x l) as [l'|] eqn:E; cbn in H; [|discriminate].
    injection H as <-; exact (IH _ _ E).
  - destruct (cbn_bt_set q x r) as [r'|] eqn:E; cbn in H; [|discriminate].
    injection H as <-; exact (IH _ _ E).
Qed.

Lemma cbn_bt_get_set_other {A} q q' (x : A) t t' :
  cbn_bt_set q x t = Some t' -> q' <> q -> cbn_bt_get q' t' = cbn_bt_get q' t.
Proof.
  revert q' t t'; induction q as [|q IH|q IH]; intros q' t t' H Hne; destruct t as [y|l r|];
    cbn in H; try discriminate.
  - injection H as <-; destruct q'; [congruence|reflexivity|reflexivity].
  - destruct (cbn_bt_set q x l) as [l'|] eqn:E; cbn in H; [|discriminate].
    injection H as <-; destruct q' as [|q'|q']; cbn; [reflexivity| |reflexivity].
    apply (IH _ _ _ E); congruence.
  - destruct (cbn_bt_set q x r) as [r'|] eqn:E; cbn in H; [|discriminate].
    injection H as <-; destruct q' as [|q'|q']; cbn; [reflexivity|reflexivity|].
    apply (IH _ _ _ E); congruence.
Qed.

Lemma cbn_bt_set_none {A} q (x : A) t : cbn_bt_set q x t = None <-> cbn_bt_get q t = None.
Proof.
  revert t; induction q as [|q IH|q IH]; intros t; destruct t as [y|l r|]; cbn;
    try (split; intro; congruence).
  - rewrite <- (IH l); destruct (cbn_bt_set q x l); cbn; split; congruence.
  - rewrite <- (IH r); destruct (cbn_bt_set q x r); cbn; split; congruence.
Qed.

(** *** Where the scan finds a cell *)

Local Fixpoint cbn_bp_len (q : cbn_bpath) : nat :=
  match q with CbnPEnd => O | CbnPL q | CbnPR q => S (cbn_bp_len q) end.

Local Fixpoint cbn_bp_drop (k : nat) (q : cbn_bpath) : cbn_bpath :=
  match k, q with
  | S k, (CbnPL q | CbnPR q) => cbn_bp_drop k q
  | _, _ => q
  end.

Local Lemma cbn_bp_drop_S k q r : cbn_bp_drop k q = CbnPL r \/ cbn_bp_drop k q = CbnPR r ->
  cbn_bp_drop (S k) q = r.
Proof.
  revert q; induction k as [|k IH]; intros q H.
  - cbn in H; destruct H; subst; reflexivity.
  - destruct q as [|q|q]; cbn in *; [destruct H; discriminate| apply IH, H | apply IH, H].
Qed.

(** [cbn_bh_at h acc t q]: the scan from [acc] at the start of [h] found the tree [t] in [h], at
  the position given by the length of [q] beyond [acc], and [q] extends [acc]. *)
Local Definition cbn_bh_at {A} (h : cbn_bheap A) (acc : cbn_bpath) (t : cbn_btree A)
  (q : cbn_bpath) : Prop :=
  cbn_bp_len acc <= cbn_bp_len q /\ cbn_bp_drop (cbn_bp_len q - cbn_bp_len acc) q = acc
  /\ nth_error h (cbn_bp_len q - cbn_bp_len acc) = Some (CbnDOne t).

Local Lemma cbn_bh_at_here {A} (h : cbn_bheap A) acc t : cbn_bh_at (CbnDOne t :: h) acc t acc.
Proof. unfold cbn_bh_at; rewrite Nat.sub_diag; auto. Qed.

Local Lemma cbn_bh_at_shift {A} (d : cbn_digit A) h acc acc' t q :
  acc' = CbnPL acc \/ acc' = CbnPR acc -> cbn_bh_at h acc' t q -> cbn_bh_at (d :: h) acc t q.
Proof.
  unfold cbn_bh_at; intros Hacc (Hl & Hd & Hn).
  assert (E : cbn_bp_len acc' = S (cbn_bp_len acc)) by (destruct Hacc; subst; reflexivity).
  rewrite E in Hl, Hd, Hn.
  replace (cbn_bp_len q - cbn_bp_len acc) with (S (cbn_bp_len q - S (cbn_bp_len acc))) by lia.
  split; [lia|]; split; [|exact Hn].
  apply cbn_bp_drop_S; destruct Hacc; subst; [left|right]; exact Hd.
Qed.

Local Ltac cbn_pl_pr := first [ left; reflexivity | right; reflexivity ].

Local Ltac cbn_res_step R :=
  destruct R as [E|E];
  [ first [ left; exact E | discriminate E | injection E as <- <-; right; apply cbn_bh_at_here ]
  | right; refine (cbn_bh_at_shift _ _ _ _ _ _ _ E); cbn_pl_pr ].

Local Lemma cbn_bh_top_res {A} (h : cbn_bheap A) acc c t q :
  cbn_bh_top h acc c = Some (t, q) -> c = Some (t, q) \/ cbn_bh_at h acc t q.
Proof.
  revert acc c; induction h as [|d h IH]; intros acc c H; cbn in H; [left; exact H|].
  destruct d; cbn_res_step (IH _ _ H).
Qed.

Local Lemma cbn_bh_scan_nil {A} p acc (c : option (cbn_btree A * cbn_bpath))
  : cbn_bh_scan p [] acc c = None.
Proof. destruct p; reflexivity. Qed.

Local Lemma cbn_bh_scan_res {A} p (h : cbn_bheap A) acc c t q :
  cbn_bh_scan p h acc c = Some (t, q) -> c = Some (t, q) \/ cbn_bh_at h acc t q.
Proof.
  revert p acc c; induction h as [|d h IH]; intros p acc c H.
  - rewrite cbn_bh_scan_nil in H; discriminate.
  - destruct p, d; cbn in H;
      first [ cbn_res_step (IH _ _ _ H) | cbn_res_step (cbn_bh_top_res h _ _ _ _ H) ].
Qed.

(** *** Two addresses found at the same path are equal *)

Local Definition cbn_bh_short {A} (c : option (cbn_btree A * cbn_bpath)) (acc : cbn_bpath) : Prop :=
  forall t q, c = Some (t, q) -> cbn_bp_len q < cbn_bp_len acc.

Local Lemma cbn_bh_short_none {A} acc : @cbn_bh_short A None acc.
Proof. intros t q E; discriminate. Qed.

Local Lemma cbn_bh_short_here {A} (t : cbn_btree A) acc acc' :
  acc' = CbnPL acc \/ acc' = CbnPR acc -> cbn_bh_short (Some (t, acc)) acc'.
Proof. intros Ha t' q E; injection E as _ <-; destruct Ha; subst; cbn; lia. Qed.

Local Lemma cbn_bh_short_step {A} (c : option (cbn_btree A * cbn_bpath)) acc acc' :
  acc' = CbnPL acc \/ acc' = CbnPR acc -> cbn_bh_short c acc -> cbn_bh_short c acc'.
Proof. intros Ha Hs t q E; specialize (Hs t q E); destruct Ha; subst; cbn; lia. Qed.

(** Both results at the same path beyond [acc], or both from the candidates. *)
Local Definition cbn_bh_same_res (acc q1 q2 : cbn_bpath) : Prop :=
  (q1 = q2 /\ cbn_bp_len acc <= cbn_bp_len q1) \/
    (cbn_bp_len q1 < cbn_bp_len acc /\ cbn_bp_len q2 < cbn_bp_len acc).

Local Lemma cbn_bh_same_res_step acc acc' q1 q2 :
  acc' = CbnPL acc \/ acc' = CbnPR acc -> cbn_bh_same_res acc q1 q2 -> cbn_bh_same_res acc' q1 q2.
Proof.
  intros Ha C; assert (E : cbn_bp_len acc' = S (cbn_bp_len acc)) by
    (destruct Ha; subst; reflexivity).
  unfold cbn_bh_same_res in *; rewrite E.
  destruct C as [[<- Hl]|[Hl1 Hl2]].
  - destruct (Nat.eq_dec (cbn_bp_len q1) (cbn_bp_len acc));
    [right; lia|left; split; [reflexivity|lia]].
  - right; lia.
Qed.

Local Lemma cbn_bh_same_res_sym acc q1 q2 : cbn_bh_same_res acc q1 q2 -> cbn_bh_same_res acc q2 q1.
Proof. unfold cbn_bh_same_res; intros [[<- Hl]|[Hl1 Hl2]]; [left; auto|right; auto]. Qed.

Local Ltac cbn_short_tac :=
  first [ apply cbn_bh_short_none
        | eapply cbn_bh_short_here; cbn_pl_pr
        | eapply cbn_bh_short_step; [|eassumption]; cbn_pl_pr ].

(** Every result of a scan comes from its candidate or lies beyond [acc]: when the two
  results are at the same path or both short, one of these clashes. *)
Local Ltac cbn_crunch :=
  repeat match goal with
  | H : cbn_bh_scan _ _ _ _ = Some _ |- _ =>
    apply cbn_bh_scan_res in H; destruct H as [H | (? & ? & ?)]
  | H : cbn_bh_top _ _ _ = Some _ |- _ =>
    apply cbn_bh_top_res in H; destruct H as [H | (? & ? & ?)]
  | H : None = Some _ |- _ => discriminate H
  | H : Some (_, _) = Some (_, _) |- _ => injection H as _ H; apply (f_equal cbn_bp_len) in H
  | Hs : cbn_bh_short ?c ?a, H : ?c = Some (_, _) |- _ => pose proof (Hs _ _ H); clear H
  end;
  cbn [cbn_bp_len] in *;
  first [ lia
        | match goal with
          | H1 : cbn_bp_drop ?k ?q = CbnPL _, H2 : cbn_bp_drop ?k ?q = CbnPR _ |- _ =>
            rewrite H1 in H2; discriminate H2
          end ].

Local Lemma cbn_bh_top_scan {A} (h : cbn_bheap A) : forall p acc c1 c2 t1 t2 q1 q2,
  cbn_bh_short c1 acc -> cbn_bh_short c2 acc ->
  cbn_bh_top h acc c1 = Some (t1, q1) -> cbn_bh_scan p h acc c2 = Some (t2, q2) ->
  cbn_bh_same_res acc q1 q2 -> False.
Proof.
  induction h as [|d h IH]; intros p acc c1 c2 t1 t2 q1 q2 S1 S2 H1 H2 C.
  - rewrite cbn_bh_scan_nil in H2; discriminate.
  - destruct p as [p|p|], d as [|t]; cbn in H1, H2;
      try (eapply IH; [ | | exact H1 | exact H2 | refine (cbn_bh_same_res_step _ _ _ _ _ C);
        cbn_pl_pr ];
           cbn_short_tac);
      destruct C as [[<- ?]|[? ?]]; cbn_crunch.
Qed.

Local Lemma cbn_bh_scan_inj {A} (h : cbn_bheap A) : forall p1 p2 acc c1 c2 t1 t2 q1 q2,
  cbn_bh_short c1 acc -> cbn_bh_short c2 acc ->
  cbn_bh_scan p1 h acc c1 = Some (t1, q1) -> cbn_bh_scan p2 h acc c2 = Some (t2, q2) ->
  cbn_bh_same_res acc q1 q2 -> p1 = p2.
Proof.
  induction h as [|d h IH]; intros p1 p2 acc c1 c2 t1 t2 q1 q2 S1 S2 H1 H2 C.
  - rewrite cbn_bh_scan_nil in H1; discriminate.
  - destruct p1 as [p1|p1|], p2 as [p2|p2|], d as [|t]; cbn in H1, H2;
      try reflexivity;
      try (f_equal; eapply IH;
           [ | | exact H1 | exact H2 | refine (cbn_bh_same_res_step _ _ _ _ _ C); cbn_pl_pr ];
           cbn_short_tac);
      exfalso;
      try (first
             [ eapply cbn_bh_top_scan;
               [ | | exact H1 | exact H2 | refine (cbn_bh_same_res_step _ _ _ _ _ C); cbn_pl_pr ]
             | eapply cbn_bh_top_scan;
               [ | | exact H2 | exact H1
               | apply cbn_bh_same_res_sym; refine (cbn_bh_same_res_step _ _ _ _ _ C); cbn_pl_pr ]
                 ];
           cbn_short_tac);
      destruct C as [[<- ?]|[? ?]]; cbn_crunch.
Qed.

Local Lemma cbn_bh_find_inj {A} a b (h : cbn_bheap A) t1 t2 q :
  cbn_bh_find a h = Some (t1, q) -> cbn_bh_find b h = Some (t2, q) -> a = b.
Proof.
  intros H1 H2; destruct a as [pa], b as [pb]; f_equal.
  eapply (cbn_bh_scan_inj h pa pb CbnPEnd None None);
    [apply cbn_bh_short_none|apply cbn_bh_short_none|
    exact H1|exact H2|left; split; [reflexivity|cbn; lia]].
Qed.

Local Lemma cbn_bh_find_nth {A} a (h : cbn_bheap A) t q :
  cbn_bh_find a h = Some (t, q) -> nth_error h (cbn_bp_len q) = Some (CbnDOne t).
Proof.
  unfold cbn_bh_find; intros H; apply cbn_bh_scan_res in H.
  destruct H as [H|(_ & _ & Hn)]; [discriminate|].
  cbn [cbn_bp_len] in Hn; rewrite Nat.sub_0_r in Hn; exact Hn.
Qed.

(** *** The scan depends on the digits only *)

Local Definition cbn_bh_dshape {A} (d d' : cbn_digit A) : Prop :=
  match d, d' with
  | CbnDZero, CbnDZero => True
  | CbnDOne _, CbnDOne _ => True
  | _, _ => False
  end.

Local Definition cbn_bh_crel {A} (c c' : option (cbn_btree A * cbn_bpath)) : Prop :=
  match c, c' with
  | None, None => True
  | Some (_, q), Some (_, q') => q = q'
  | _, _ => False
  end.

Local Lemma cbn_bh_top_shape {A} (h h' : cbn_bheap A) : Forall2 cbn_bh_dshape h h' ->
  forall acc c c', cbn_bh_crel c c' -> cbn_bh_crel (cbn_bh_top h acc c) (cbn_bh_top h' acc c').
Proof.
  induction 1 as [|d d' h h' Hd Hf IH]; intros acc c c' Hc; cbn; [exact Hc|].
  destruct d, d'; cbn in Hd; try contradiction; apply IH; cbn; auto.
Qed.

Local Lemma cbn_bh_scan_shape {A} (h h' : cbn_bheap A) : Forall2 cbn_bh_dshape h h' ->
  forall p acc c c', cbn_bh_crel c c' ->
    cbn_bh_crel (cbn_bh_scan p h acc c) (cbn_bh_scan p h' acc c').
Proof.
  induction 1 as [|d d' h h' Hd Hf IH]; intros p acc c c' Hc.
  - rewrite !cbn_bh_scan_nil; exact I.
  - destruct p, d, d'; cbn in Hd |- *; try contradiction;
      first [ apply IH | apply cbn_bh_top_shape; [exact Hf|] ]; cbn; auto.
Qed.

Local Lemma cbn_bh_put_shape {A} k (t : cbn_btree A) h h' :
  cbn_bh_put k t h = Some h' -> Forall2 cbn_bh_dshape h h'.
Proof.
  revert k h'; induction h as [|d h IH]; intros k h' H; destruct k as [|k|k]; cbn in H;
    try discriminate.
  - destruct d; [discriminate|]; injection H as <-; constructor; [exact I|].
    clear; induction h as [|d h IH]; constructor; [destruct d; exact I|exact IH].
  - destruct (cbn_bh_put k t h) eqn:E; cbn in H; [|discriminate]; injection H as <-.
    constructor; [destruct d; exact I|exact (IH _ _ E)].
  - destruct (cbn_bh_put k t h) eqn:E; cbn in H; [|discriminate]; injection H as <-.
    constructor; [destruct d; exact I|exact (IH _ _ E)].
Qed.

Local Lemma cbn_bh_put_nth {A} k (t : cbn_btree A) h h' : cbn_bh_put k t h = Some h' ->
  forall i, nth_error h' i = if Nat.eqb i (cbn_bp_len k) then Some (CbnDOne t) else nth_error h i.
Proof.
  revert k h'; induction h as [|d h IH]; intros k h' H i; destruct k as [|k|k]; cbn in H;
    try discriminate.
  - destruct d; [discriminate|]; injection H as <-; destruct i; reflexivity.
  - destruct (cbn_bh_put k t h) eqn:E; cbn in H; [|discriminate]; injection H as <-.
    destruct i; cbn; [reflexivity|exact (IH _ _ E i)].
  - destruct (cbn_bh_put k t h) eqn:E; cbn in H; [|discriminate]; injection H as <-.
    destruct i; cbn; [reflexivity|exact (IH _ _ E i)].
Qed.

Local Lemma cbn_bh_put_some {A} k (t t' : cbn_btree A) h :
  nth_error h (cbn_bp_len k) = Some (CbnDOne t) -> exists h', cbn_bh_put k t' h = Some h'.
Proof.
  revert k; induction h as [|d h IH]; intros k H; destruct k as [|k|k]; cbn in H |- *;
    try discriminate.
  - injection H as ->; eexists; reflexivity.
  - destruct (IH _ H) as [h' E]; rewrite E; eexists; reflexivity.
  - destruct (IH _ H) as [h' E]; rewrite E; eexists; reflexivity.
Qed.

Local Lemma cbn_bh_find_put {A} a (h : cbn_bheap A) k t' h' t q :
  cbn_bh_put k t' h = Some h' -> cbn_bh_find a h = Some (t, q) ->
  cbn_bh_find a h' = Some (if Nat.eqb (cbn_bp_len q) (cbn_bp_len k) then t' else t, q).
Proof.
  intros Hp Hf.
  pose proof (cbn_bh_scan_shape _ _ (cbn_bh_put_shape _ _ _ _ Hp) a.(cbn_ha_p) CbnPEnd None None I)
    as R.
  fold (cbn_bh_find a h) (cbn_bh_find a h') in R; rewrite Hf in R.
  destruct (cbn_bh_find a h') as [[t'' q']|] eqn:E; cbn in R; [|contradiction]; subst q'.
  pose proof (cbn_bh_find_nth _ _ _ _ E) as N'; rewrite (cbn_bh_put_nth _ _ _ _ Hp) in N'.
  pose proof (cbn_bh_find_nth _ _ _ _ Hf) as N.
  destruct (Nat.eqb (cbn_bp_len q) (cbn_bp_len k)); [|rewrite N in N']; congruence.
Qed.

Local Lemma cbn_bh_find_put_none {A} a (h : cbn_bheap A) k t' h' :
  cbn_bh_put k t' h = Some h' -> cbn_bh_find a h = None -> cbn_bh_find a h' = None.
Proof.
  intros Hp Hf.
  pose proof (cbn_bh_scan_shape _ _ (cbn_bh_put_shape _ _ _ _ Hp) a.(cbn_ha_p) CbnPEnd None None I)
    as R.
  fold (cbn_bh_find a h) (cbn_bh_find a h') in R; rewrite Hf in R.
  destruct (cbn_bh_find a h'); [contradiction|reflexivity].
Qed.

Local Lemma cbn_bh_digits_shape {A} (h h' : cbn_bheap A) n :
  cbn_bh_digits h n -> Forall2 cbn_bh_dshape h h' -> cbn_bh_digits h' n.
Proof.
  intros Hd; revert h'; induction Hd as [t|h n Hd IH|t h n Hd IH]; intros h' Hf;
    inversion Hf as [|d d' h0 h0' Hdd Hrest]; subst;
    destruct d' as [|t']; cbn in Hdd; try contradiction.
  - inversion Hrest; subst; constructor.
  - constructor; exact (IH _ Hrest).
  - constructor; exact (IH _ Hrest).
Qed.

(** *** [cbn_bh_upd] *)

Lemma cbn_bh_get_upd_same {A} a (x : A) h h' : cbn_bh_upd a x h = Some h' ->
  cbn_bh_get a h' = Some x.
Proof.
  unfold cbn_bh_upd, cbn_bh_get; intros H.
  destruct (cbn_bh_find a h) as [[t q]|] eqn:Ef; [|discriminate].
  destruct (cbn_bt_set q x t) as [t1|] eqn:Es; [|discriminate].
  rewrite (cbn_bh_find_put _ _ _ _ _ _ _ H Ef), Nat.eqb_refl.
  exact (cbn_bt_get_set_same _ _ _ _ Es).
Qed.

Lemma cbn_bh_get_upd_other {A} a b (x : A) h h' :
  cbn_bh_upd a x h = Some h' -> b <> a -> cbn_bh_get b h' = cbn_bh_get b h.
Proof.
  unfold cbn_bh_upd, cbn_bh_get; intros H Hne.
  destruct (cbn_bh_find a h) as [[t q]|] eqn:Ef; [|discriminate].
  destruct (cbn_bt_set q x t) as [t1|] eqn:Es; [|discriminate].
  destruct (cbn_bh_find b h) as [[s q']|] eqn:Eb.
  - rewrite (cbn_bh_find_put _ _ _ _ _ _ _ H Eb).
    destruct (Nat.eqb (cbn_bp_len q') (cbn_bp_len q)) eqn:El; [|reflexivity].
    apply Nat.eqb_eq in El.
    pose proof (cbn_bh_find_nth _ _ _ _ Ef) as N1; pose proof (cbn_bh_find_nth _ _ _ _ Eb) as N2.
    rewrite El, N1 in N2; injection N2 as <-.
    apply (cbn_bt_get_set_other _ _ _ _ _ Es).
    intros ->; apply Hne; exact (cbn_bh_find_inj _ _ _ _ _ _ Eb Ef).
  - rewrite (cbn_bh_find_put_none _ _ _ _ _ H Eb); reflexivity.
Qed.

Lemma cbn_bh_upd_none {A} a (x : A) h : cbn_bh_upd a x h = None <-> cbn_bh_get a h = None.
Proof.
  unfold cbn_bh_upd, cbn_bh_get.
  destruct (cbn_bh_find a h) as [[t q]|] eqn:Ef; [|split; auto].
  destruct (cbn_bt_set q x t) as [t1|] eqn:Es.
  - destruct (cbn_bh_put_some q t t1 h (cbn_bh_find_nth _ _ _ _ Ef)) as [h' Ep]; rewrite Ep.
    split; [discriminate|]; intros Hg.
    apply (proj2 (cbn_bt_set_none q x t)) in Hg; congruence.
  - split; [intros _; exact (proj1 (cbn_bt_set_none q x t) Es)|reflexivity].
Qed.

Lemma cbn_bh_digits_upd {A} a (x : A) h h' n :
  cbn_bh_upd a x h = Some h' -> cbn_bh_digits h n -> cbn_bh_digits h' n.
Proof.
  unfold cbn_bh_upd; intros H Hd.
  destruct (cbn_bh_find a h) as [[t q]|]; [|discriminate].
  destruct (cbn_bt_set q x t) as [t1|]; [|discriminate].
  exact (cbn_bh_digits_shape _ _ _ Hd (cbn_bh_put_shape _ _ _ _ H)).
Qed.

(** *** [cbn_bh_cons] *)

Lemma cbn_bh_digits_holes {A} p : cbn_bh_digits (@cbn_bh_holes A p) p.
Proof. induction p; cbn; constructor; auto. Qed.

Lemma cbn_bh_digits_cons {A} (x : A) h n : cbn_bh_digits h n ->
  cbn_bh_digits (cbn_bh_cons x h) (Pos.succ n).
Proof.
  unfold cbn_bh_cons; generalize (CbnBLeaf x); intros T Hd; revert T.
  induction Hd as [t|h n Hd IH|t h n Hd IH]; intros T; cbn; repeat constructor; auto.
Qed.

Local Definition cbn_bh_val {A} (r : option (cbn_btree A * cbn_bpath)) : option A :=
  match r with Some (t, q) => cbn_bt_get q t | None => None end.

Local Lemma cbn_bh_top_indep {A} (h : cbn_bheap A) n : cbn_bh_digits h n ->
  forall acc c c', cbn_bh_top h acc c = cbn_bh_top h acc c'.
Proof. induction 1; intros; cbn; auto. Qed.

Local Lemma cbn_bh_scan_exact {A} (h : cbn_bheap A) n : cbn_bh_digits h n ->
  forall acc c, cbn_bh_scan n h acc c = c.
Proof. induction 1; intros; cbn; auto. Qed.

Local Lemma cbn_bh_scan_indep {A} (h : cbn_bheap A) n : cbn_bh_digits h n ->
  forall p acc c c', p <> n -> cbn_bh_scan p h acc c = cbn_bh_scan p h acc c'.
Proof.
  induction 1 as [t|h n Hd IH|t h n Hd IH]; intros p acc c c' Hp; destruct p as [p|p|]; cbn;
    rewrite ?cbn_bh_scan_nil; try reflexivity; try congruence;
    first [ apply IH; congruence | eapply cbn_bh_top_indep; eassumption ].
Qed.

Local Lemma cbn_bh_scan_carry_new {A} (h : cbn_bheap A) n : cbn_bh_digits h n ->
  forall T acc c, cbn_bh_val (cbn_bh_scan n (cbn_bh_carry T h) acc c) = cbn_bt_get acc T.
Proof.
  induction 1 as [t|h n Hd IH|t h n Hd IH]; intros T acc c.
  - reflexivity.
  - cbn [cbn_bh_carry cbn_bh_scan]; rewrite (cbn_bh_scan_exact _ _ Hd); reflexivity.
  - cbn [cbn_bh_carry cbn_bh_scan]; rewrite IH; reflexivity.
Qed.

Local Lemma cbn_bh_top_carry {A} (h : cbn_bheap A) n : cbn_bh_digits h n ->
  forall T acc, cbn_bh_val (cbn_bh_top (cbn_bh_carry T h) acc None)
    = cbn_bh_val (cbn_bh_top h acc None).
Proof.
  induction 1 as [t|h n Hd IH|t h n Hd IH]; intros T acc.
  - reflexivity.
  - cbn [cbn_bh_carry cbn_bh_top]; f_equal; eapply cbn_bh_top_indep; eassumption.
  - cbn [cbn_bh_carry cbn_bh_top]; rewrite IH; f_equal; eapply cbn_bh_top_indep; eassumption.
Qed.

Local Lemma cbn_bh_scan_carry_old {A} (h : cbn_bheap A) n : cbn_bh_digits h n ->
  forall T p acc c, p <> n ->
  cbn_bh_val (cbn_bh_scan p (cbn_bh_carry T h) acc None) = cbn_bh_val (cbn_bh_scan p h acc c).
Proof.
  induction 1 as [t|h n Hd IH|t h n Hd IH]; intros T p acc c Hp; destruct p as [p|p|].
  - destruct p; cbn; rewrite ?cbn_bh_scan_nil; reflexivity.
  - destruct p; cbn; rewrite ?cbn_bh_scan_nil; reflexivity.
  - congruence.
  - reflexivity.
  - cbn [cbn_bh_carry cbn_bh_scan]; f_equal; eapply cbn_bh_scan_indep; [eassumption|congruence].
  - reflexivity.
  - cbn [cbn_bh_carry cbn_bh_scan]; apply IH; congruence.
  - cbn [cbn_bh_carry cbn_bh_scan]; destruct (Pos.eq_dec p n) as [->|Hne].
    + rewrite (cbn_bh_scan_carry_new _ _ Hd), (cbn_bh_scan_exact _ _ Hd); reflexivity.
    + apply IH; exact Hne.
  - cbn [cbn_bh_carry cbn_bh_scan]; rewrite (cbn_bh_top_carry _ _ Hd); f_equal;
      eapply cbn_bh_top_indep; eassumption.
Qed.

Lemma cbn_bh_digits_get_cons_new {A} (x : A) h n :
  cbn_bh_digits h n -> cbn_bh_get (CbnHAddr n) (cbn_bh_cons x h) = Some x.
Proof. intros Hd; exact (cbn_bh_scan_carry_new _ _ Hd (CbnBLeaf x) CbnPEnd None). Qed.

Lemma cbn_bh_digits_get_cons_old {A} (x : A) h n a :
  cbn_bh_digits h n -> a <> CbnHAddr n -> cbn_bh_get a (cbn_bh_cons x h) = cbn_bh_get a h.
Proof.
  intros Hd Ha; destruct a as [pa].
  exact (cbn_bh_scan_carry_old _ _ Hd (CbnBLeaf x) pa CbnPEnd None ltac:(congruence)).
Qed.

Local Lemma cbn_bh_holes_nth {A} p i (t : cbn_btree A) :
  nth_error (cbn_bh_holes p) i = Some (CbnDOne t) -> t = CbnBEmpty.
Proof.
  revert i; induction p as [p IH|p IH|]; intros i H; destruct i as [|i]; cbn in H;
    first [ discriminate | injection H as <-; reflexivity | exact (IH _ H)
          | destruct i; discriminate ].
Qed.

Lemma cbn_bh_get_holes {A} a p : cbn_bh_get a (@cbn_bh_holes A p) = None.
Proof.
  unfold cbn_bh_get; destruct (cbn_bh_find a (cbn_bh_holes p)) as [[t q]|] eqn:E; [|reflexivity].
  rewrite (cbn_bh_holes_nth _ _ _ (cbn_bh_find_nth _ _ _ _ E)); destruct q; reflexivity.
Qed.

(** *** The laws over [cbn_bh_ok] *)

Lemma cbn_bh_ok_digits {A} lo n (h : cbn_bheap A) : cbn_bh_ok lo n h -> cbn_bh_digits h n.
Proof.
  induction 1; [apply cbn_bh_digits_holes|apply cbn_bh_digits_cons; assumption|].
  eapply cbn_bh_digits_upd; eassumption.
Qed.

Lemma cbn_bh_ok_le {A} lo n (h : cbn_bheap A) : cbn_bh_ok lo n h -> (lo <= n)%positive.
Proof. induction 1; lia. Qed.

(** [cbn_bh_upd] keeps the next address. *)
Lemma cbn_bh_upd_ok {A} lo n (h : cbn_bheap A) a x h' :
  cbn_bh_ok lo n h -> cbn_bh_upd a x h = Some h' -> cbn_bh_ok lo n h'.
Proof. intros Hok Hu; exact (cbn_bh_ok_upd _ _ _ _ _ _ Hok Hu). Qed.

Lemma cbn_bh_get_cons_new {A} lo n h (x : A) :
  cbn_bh_ok lo n h -> cbn_bh_get (CbnHAddr n) (cbn_bh_cons x h) = Some x.
Proof. intros Hok; exact (cbn_bh_digits_get_cons_new _ _ _ (cbn_bh_ok_digits _ _ _ Hok)). Qed.

Lemma cbn_bh_get_cons_old {A} lo n h (x : A) a :
  cbn_bh_ok lo n h -> a <> CbnHAddr n -> cbn_bh_get a (cbn_bh_cons x h) = cbn_bh_get a h.
Proof. intros Hok; exact (cbn_bh_digits_get_cons_old _ _ _ _ (cbn_bh_ok_digits _ _ _ Hok)). Qed.

(** ** State *)

Inductive cbn_delta_memo :=
| CbnDAxiom
| CbnDBody (body : term) (insts : list (Instance.t * cbn_cidx * term)).

(** *** Equality of names by identifier first *)

Fixpoint cbn_dirpath_eqb (d1 d2 : dirpath) : bool :=
  match d1, d2 with
  | [], [] => true
  | x :: d1, y :: d2 => String.eqb x y && cbn_dirpath_eqb d1 d2
  | _, _ => false
  end.

Fixpoint cbn_modpath_eqb (m1 m2 : modpath) : bool :=
  match m1, m2 with
  | MPfile d1, MPfile d2 => cbn_dirpath_eqb d1 d2
  | MPbound d1 i1 k1, MPbound d2 i2 k2 =>
    String.eqb i1 i2 && Nat.eqb k1 k2 && cbn_dirpath_eqb d1 d2
  | MPdot m1 i1, MPdot m2 i2 => String.eqb i1 i2 && cbn_modpath_eqb m1 m2
  | _, _ => false
  end.

(** Equality of inductives: the index, the identifier, then the module path (the kername
  comparison of [Kernames] compares the module path first, byte by byte). *)
Definition cbn_inductive_eqb (i1 i2 : inductive) : bool :=
  Nat.eqb i1.(inductive_ind) i2.(inductive_ind)
  && String.eqb i1.(inductive_mind).2 i2.(inductive_mind).2
  && cbn_modpath_eqb i1.(inductive_mind).1 i2.(inductive_mind).1.

Definition cbn_case_info_eqb (c1 c2 : case_info) : bool :=
  cbn_inductive_eqb c1.(ci_ind) c2.(ci_ind) && Nat.eqb c1.(ci_npar) c2.(ci_npar)
  && eqb c1.(ci_relevance) c2.(ci_relevance)
  && Bool.eqb c1.(ci_cofix_nondep) c2.(ci_cofix_nondep).

(** *** The delta memo: a binary trie on the bits of the constant's identifier, each node
  with the module paths of the constants whose identifier ends there *)

Inductive cbn_dtrie :=
| CbnDTNil
| CbnDTNode (here : list (modpath * cbn_delta_memo)) (z o : cbn_dtrie).

Definition cbn_dt_child (b : bool) (t : cbn_dtrie) : cbn_dtrie :=
  match t with
  | CbnDTNil => CbnDTNil
  | CbnDTNode _ z o => if b then o else z
  end.

Definition cbn_dt_byte (x : Byte.byte) (t : cbn_dtrie) : cbn_dtrie :=
  let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := Byte.to_bits x in
  cbn_dt_child b7 (cbn_dt_child b6 (cbn_dt_child b5 (cbn_dt_child b4
    (cbn_dt_child b3 (cbn_dt_child b2 (cbn_dt_child b1 (cbn_dt_child b0 t))))))).

Fixpoint cbn_dt_walk (s : String.t) (t : cbn_dtrie) : cbn_dtrie :=
  match s with
  | String.EmptyString => t
  | String.String x s => cbn_dt_walk s (cbn_dt_byte x t)
  end.

Fixpoint cbn_mp_find (mp : modpath) (l : list (modpath * cbn_delta_memo)) : option cbn_delta_memo :=
  match l with
  | [] => None
  | (mp', d) :: l => if cbn_modpath_eqb mp mp' then Some d else cbn_mp_find mp l
  end.

Definition cbn_dt_find (kn : kername) (t : cbn_dtrie) : option cbn_delta_memo :=
  match cbn_dt_walk kn.2 t with
  | CbnDTNil => None
  | CbnDTNode here _ _ => cbn_mp_find kn.1 here
  end.

Definition cbn_dt_upd_child (b : bool) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) : cbn_dtrie :=
  match t with
  | CbnDTNil => if b then CbnDTNode [] CbnDTNil (f CbnDTNil) else CbnDTNode [] (f CbnDTNil) CbnDTNil
  | CbnDTNode h z o => if b then CbnDTNode h z (f o) else CbnDTNode h (f z) o
  end.

Definition cbn_dt_upd_byte (x : Byte.byte) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie)
  : cbn_dtrie :=
  let '(b0, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := Byte.to_bits x in
  cbn_dt_upd_child b0 (cbn_dt_upd_child b1 (cbn_dt_upd_child b2 (cbn_dt_upd_child b3
    (cbn_dt_upd_child b4 (cbn_dt_upd_child b5 (cbn_dt_upd_child b6 (cbn_dt_upd_child b7 f))))))) t.

Fixpoint cbn_dt_upd (s : String.t) (f : cbn_dtrie -> cbn_dtrie) (t : cbn_dtrie) : cbn_dtrie :=
  match s with
  | String.EmptyString => f t
  | String.String x s => cbn_dt_upd_byte x (cbn_dt_upd s f) t
  end.

Fixpoint cbn_mp_set (mp : modpath) (d : cbn_delta_memo) (l : list (modpath * cbn_delta_memo))
  : list (modpath * cbn_delta_memo) :=
  match l with
  | [] => [(mp, d)]
  | (mp', d') :: l => if cbn_modpath_eqb mp mp' then (mp, d) :: l else (mp', d')
    :: cbn_mp_set mp d l
  end.

Definition cbn_dt_add (kn : kername) (d : cbn_delta_memo) (t : cbn_dtrie) : cbn_dtrie :=
  cbn_dt_upd kn.2 (fun t => match t with
                        | CbnDTNil => CbnDTNode [(kn.1, d)] CbnDTNil CbnDTNil
                        | CbnDTNode h z o => CbnDTNode (cbn_mp_set kn.1 d h) z o
                        end) t.

(** Per-call data that holds no heap address. *)
Record cbn_memo := cbn_mkMemo {
  cbn_m_codes : PTree.t cbn_code_entry;
  cbn_m_ncode : cbn_cidx;
  cbn_m_delta : cbn_dtrie;
  cbn_m_once : PTree.t (PTree.t bool);  (* (index, path) of a binder's body: occurs at most once *)
  cbn_m_hash : PTree.t (PTree.t N);     (* (index, path): structural hash of the code *)
  cbn_m_ceq : PTree.t (PTree.t (PTree.t (PTree.t bool))) }. (* code equality of two identifiers *)

Record cbn_state := cbn_mkState {
  cbn_st_heap : cbn_bheap cbn_cell;
  cbn_st_next : positive;        (* the next heap address *)
  cbn_st_room : N;               (* allocations left before the next collection *)
  cbn_st_steps : N;
  cbn_st_gam : PTree.t cbn_haddr;    (* the cell of a context entry, by [cbn_key_of_succ_nat j] *)
  cbn_st_memo : cbn_memo }.

Definition cbn_memo_empty : cbn_memo :=
  cbn_mkMemo (PTree.empty _) String2pos.xH CbnDTNil (PTree.empty _) (PTree.empty _) (PTree.empty _).

Definition cbn_init : cbn_state :=
  cbn_mkState (cbn_bh_holes xH) xH (cbn_gc_room 0) cbn_steps (PTree.empty _) cbn_memo_empty.

Definition cbn_tick (s : cbn_state) : option cbn_state :=
  match s.(cbn_st_steps) with
  | N0 => None
  | n => Some (cbn_mkState s.(cbn_st_heap) s.(cbn_st_next) s.(cbn_st_room) (N.pred n) s.(cbn_st_gam)
    s.(cbn_st_memo))
  end.

Definition cbn_heap_get (a : cbn_haddr) (s : cbn_state) : option cbn_cell :=
  cbn_bh_get a s.(cbn_st_heap).

Definition cbn_heap_upd (a : cbn_haddr) (c : cbn_cell) (s : cbn_state) : option cbn_state :=
  option_map (fun h => cbn_mkState h s.(cbn_st_next) s.(cbn_st_room) s.(cbn_st_steps) s.(cbn_st_gam)
    s.(cbn_st_memo))
    (cbn_bh_upd a c s.(cbn_st_heap)).

Definition cbn_alloc_now (c : cbn_cell) (s : cbn_state) : cbn_haddr * cbn_state :=
  (CbnHAddr s.(cbn_st_next),
   cbn_mkState (cbn_bh_cons c s.(cbn_st_heap)) (Pos.succ s.(cbn_st_next)) (N.pred s.(cbn_st_room))
     s.(cbn_st_steps)
     s.(cbn_st_gam) s.(cbn_st_memo)).

Definition cbn_set_memo (m : cbn_memo) (s : cbn_state) : cbn_state :=
  cbn_mkState s.(cbn_st_heap) s.(cbn_st_next) s.(cbn_st_room) s.(cbn_st_steps) s.(cbn_st_gam) m.

Definition cbn_set_gam (g : PTree.t cbn_haddr) (s : cbn_state) : cbn_state :=
  cbn_mkState s.(cbn_st_heap) s.(cbn_st_next) s.(cbn_st_room) s.(cbn_st_steps) g s.(cbn_st_memo).

(** *** The heap laws over the state: [cbn_heap_get], [cbn_heap_upd], [cbn_alloc_now] *)

Lemma cbn_init_ok : cbn_bh_ok xH cbn_init.(cbn_st_next) cbn_init.(cbn_st_heap).
Proof. exact (cbn_bh_ok_holes xH). Qed.

Lemma cbn_heap_get_upd_same a c s s' : cbn_heap_upd a c s = Some s' -> cbn_heap_get a s' = Some c.
Proof.
  unfold cbn_heap_upd, cbn_heap_get; destruct (cbn_bh_upd a c s.(cbn_st_heap)) as [h|] eqn:E; cbn;
    [|discriminate].
  intros H; injection H as <-; exact (cbn_bh_get_upd_same _ _ _ _ E).
Qed.

Lemma cbn_heap_get_upd_other a b c s s' :
  cbn_heap_upd a c s = Some s' -> b <> a -> cbn_heap_get b s' = cbn_heap_get b s.
Proof.
  unfold cbn_heap_upd, cbn_heap_get; destruct (cbn_bh_upd a c s.(cbn_st_heap)) as [h|] eqn:E; cbn;
    [|discriminate].
  intros H Hne; injection H as <-; exact (cbn_bh_get_upd_other _ _ _ _ _ E Hne).
Qed.

Definition cbn_memo_add_entry (e : cbn_code_entry) (m : cbn_memo) : cbn_cidx * cbn_memo :=
  let i := m.(cbn_m_ncode) in
  (i, cbn_mkMemo (PTree.set i e m.(cbn_m_codes)) (cbn_key_succ i) m.(cbn_m_delta) m.(cbn_m_once)
    m.(cbn_m_hash)
        m.(cbn_m_ceq)).

Definition cbn_memo_set_delta (d : cbn_dtrie) (m : cbn_memo) : cbn_memo :=
  cbn_mkMemo m.(cbn_m_codes) m.(cbn_m_ncode) d m.(cbn_m_once) m.(cbn_m_hash) m.(cbn_m_ceq).

Definition cbn_memo_set_once (o : PTree.t (PTree.t bool)) (m : cbn_memo) : cbn_memo :=
  cbn_mkMemo m.(cbn_m_codes) m.(cbn_m_ncode) m.(cbn_m_delta) o m.(cbn_m_hash) m.(cbn_m_ceq).

Definition cbn_memo_set_hash (h : PTree.t (PTree.t N)) (m : cbn_memo) : cbn_memo :=
  cbn_mkMemo m.(cbn_m_codes) m.(cbn_m_ncode) m.(cbn_m_delta) m.(cbn_m_once) h m.(cbn_m_ceq).

Definition cbn_memo_set_ceq (q : PTree.t (PTree.t (PTree.t (PTree.t bool)))) (m : cbn_memo)
  : cbn_memo :=
  cbn_mkMemo m.(cbn_m_codes) m.(cbn_m_ncode) m.(cbn_m_delta) m.(cbn_m_once) m.(cbn_m_hash) q.

(** ** The collector *)

Record cbn_gc_state := cbn_mkGc {
  cbn_g_old : cbn_bheap cbn_cell;   (* the old heap, a copied cell replaced by [CbnCFwd] *)
  cbn_g_heap : cbn_bheap cbn_cell;  (* the new heap *)
  cbn_g_next : positive }.      (* its next address *)

(** Copy the cell at [a] of the old heap and the cells it reaches, children first; give it
  the next new address and leave that address in the old heap. [f] bounds the depth of the
  walk: [cbn_st_next] units, more than the number of cells, so a heap without cycles is
  never cut off. *)
Fixpoint cbn_gc_copy (f : cbn_fuel) (a : cbn_haddr) (g : cbn_gc_state) {struct f}
  : cbn_res (cbn_haddr * cbn_gc_state) :=
  match cbn_bh_get a g.(cbn_g_old) with
  | None => CbnCFail CbnWGcDangling
  | Some (CbnCFwd a') => CbnCOk (a', g)
  | Some cl =>
    match f with
    | CbnFO => CbnCFail CbnWGcFuel
    | CbnFS k =>
      cbn2 (cl, g) := cbn_rn_cell (cbn_gc_copy (k tt)) cl g in
      let a' := CbnHAddr g.(cbn_g_next) in
      match cbn_bh_upd a (CbnCFwd a') g.(cbn_g_old) with
      | Some old => CbnCOk (a', cbn_mkGc old (cbn_bh_cons cl g.(cbn_g_heap))
        (Pos.succ g.(cbn_g_next)))
      | None => CbnCFail CbnWGcDangling
      end
    end
  end.

(** Copy what [rs] and [cbn_st_gam] reach into a fresh heap whose addresses start at the old
  [cbn_st_next] (the addresses below are dropped), and rename [rs] and [cbn_st_gam]. No step is
  taken from the budget. *)
Definition cbn_collect (rs : list cbn_root) (s : cbn_state) : cbn_res (list cbn_root * cbn_state) :=
  let onext := s.(cbn_st_next) in
  let copy := cbn_gc_copy (cbn_fuel_of_pos onext (fun _ => CbnFO)) in
  let g := cbn_mkGc s.(cbn_st_heap) (cbn_bh_holes onext) onext in
  cbn2 (gm, g) := cbn_rn_ptree copy s.(cbn_st_gam) g in
  cbn2 (rs, g) := cbn_rn_roots copy rs g in
  CbnCOk (rs, cbn_mkState g.(cbn_g_heap) g.(cbn_g_next)
    (cbn_gc_room (N.sub (Npos g.(cbn_g_next)) (Npos onext)))
             s.(cbn_st_steps) gm s.(cbn_st_memo)).

Definition cbn_gc_due (s : cbn_state) : bool :=
  match s.(cbn_st_room) with N0 => true | Npos _ => false end.

Fixpoint cbn_find_inst (u : Instance.t) (l : list (Instance.t * cbn_cidx * term))
  : option (cbn_cidx * term) :=
  match l with
  | [] => None
  | (u', i, t) :: l => if Instance.eqb u u' then Some (i, t) else cbn_find_inst u l
  end.

Definition cbn_is_assum (d : context_decl) : bool :=
  match d.(decl_body) with None => true | Some _ => false end.

(** Contexts of a match related by [eq_context_upto_names], without let-ins. *)
Definition cbn_case_ctx_ok (ctx1 ctx2 : context) : bool :=
  forallb2 (fun d1 d2 => cbn_is_assum d1 && cbn_is_assum d2 && eqb_decl_upto_names d1 d2) ctx1 ctx2.

Fixpoint cbn_list_set {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: l, O => x :: l
  | y :: l, S n => y :: cbn_list_set l n x
  end.

Section CallByNeed.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat). (* nctx = #|Γ| *)

  (** *** Universe-checked syntactic comparison *)

  Definition cbn_wf_term_univs (t : term) : bool :=
    on_universes (abstract_env_ext_wf_universeb X) closedu t.

  Definition cbn_cmp_term (pb : conv_pb) (napp : nat) (t u : term) : bool :=
    cbn_wf_term_univs t && cbn_wf_term_univs u &&
    eqb_term_upto_univ_napp (abstract_env_compare_universe X) (abstract_env_compare_sort X)
      (compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X))
      pb napp t u.

  Definition cbn_cmp_sort (pb : conv_pb) (s1 s2 : sort) : bool :=
    abstract_env_ext_wf_sortb X s1 && abstract_env_ext_wf_sortb X s2 &&
    abstract_env_compare_sort X pb s1 s2.

  Definition cbn_cmp_level_conv (l1 l2 : Level.t) : bool :=
    let u1 := Universe.make' l1 in
    let u2 := Universe.make' l2 in
    abstract_env_ext_wf_universeb X u1 && abstract_env_ext_wf_universeb X u2 &&
    abstract_env_compare_universe X Conv u1 u2.

  (** *** Code entries, the per-code maps and the same-code test *)

  Definition cbn_new_entry (t : term) (u : Instance.t) (s : cbn_state)
    : cbn_code * cbn_state :=
    let ct := cbn_inst_code u t in
    let (i, m) := cbn_memo_add_entry (cbn_mkEntry t u (cbn_wf_term_univs ct)) s.(cbn_st_memo) in
    (cbn_mkCode i cbn_path_nil ct, cbn_set_memo m s).

  Definition cbn_entry_wf (i : cbn_cidx) (s : cbn_state) : bool :=
    match PTree.get i s.(cbn_st_memo).(cbn_m_codes) with
    | Some e => e.(cbn_ce_wf)
    | None => false
    end.

  (** Whether the variable of the binder over the body [c] occurs at most once in it. *)
  Definition cbn_once_body (c : cbn_code) (s : cbn_state) : bool * cbn_state :=
    match cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) s.(cbn_st_memo).(cbn_m_once) with
    | Some b => (b, s)
    | None =>
      let b := Nat.leb (cbn_occ 0 c.(cbn_c_term)) 1 in
      (b, cbn_set_memo (cbn_memo_set_once
        (cbn_set2 c.(cbn_c_entry) c.(cbn_c_path) b s.(cbn_st_memo).(cbn_m_once))
                      s.(cbn_st_memo)) s)
    end.

  Definition cbn_code_hash (c : cbn_code) (s : cbn_state) : N * cbn_state :=
    match cbn_get2 c.(cbn_c_entry) c.(cbn_c_path) s.(cbn_st_memo).(cbn_m_hash) with
    | Some h => (h, s)
    | None =>
      let h := cbn_thash c.(cbn_c_term) in
      (h, cbn_set_memo (cbn_memo_set_hash
        (cbn_set2 c.(cbn_c_entry) c.(cbn_c_path) h s.(cbn_st_memo).(cbn_m_hash))
                      s.(cbn_st_memo)) s)
    end.

  Definition cbn_ceq_get (c1 c2 : cbn_code) (s : cbn_state) : option bool :=
    match cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) s.(cbn_st_memo).(cbn_m_ceq) with
    | Some m => cbn_get2 c2.(cbn_c_entry) c2.(cbn_c_path) m
    | None => None
    end.

  Definition cbn_ceq_set (c1 c2 : cbn_code) (b : bool) (s : cbn_state) : cbn_state :=
    let q := s.(cbn_st_memo).(cbn_m_ceq) in
    let m := match cbn_get2 c1.(cbn_c_entry) c1.(cbn_c_path) q with Some m => m | None =>
      PTree.empty _ end in
    cbn_set_memo (cbn_memo_set_ceq (cbn_set2 c1.(cbn_c_entry) c1.(cbn_c_path)
      (cbn_set2 c2.(cbn_c_entry) c2.(cbn_c_path) b m) q)
                s.(cbn_st_memo)) s.

  (** Code equality: equal identifiers; or both entries passed their universe check, the
    hashes are equal, and [eqb_term_upto_univ] at [Conv] (cached by identifier pair). *)
  Definition cbn_code_eq (c1 c2 : cbn_code) (s : cbn_state) : bool * cbn_state :=
    if cbn_same_id c1 c2 then (true, s)
    else if negb (cbn_entry_wf c1.(cbn_c_entry) s && cbn_entry_wf c2.(cbn_c_entry) s)
      then (false, s)
    else
      let (h1, s) := cbn_code_hash c1 s in
      let (h2, s) := cbn_code_hash c2 s in
      if negb (N.eqb h1 h2) then (false, s)
      else
        match cbn_ceq_get c1 c2 s with
        | Some b => (b, s)
        | None =>
          let b := eqb_term_upto_univ (abstract_env_compare_universe X)
                     (abstract_env_compare_sort X)
                     (compare_global_instance (abstract_env_lookup X)
                        (abstract_env_compare_universe X))
                     Conv c1.(cbn_c_term) c2.(cbn_c_term) in
          (b, cbn_ceq_set c1 c2 b s)
        end.

  (** *** Allocation, which may collect first *)

  Definition cbn_alloc (cl : cbn_cell) (rs : list cbn_root) (s : cbn_state)
    : cbn_res (cbn_haddr * list cbn_root * cbn_state) :=
    if cbn_gc_due s then
      match cbn_collect (CbnRC cl :: rs) s with
      | CbnCOk (CbnRC cl :: rs, s) => let (a, s) := cbn_alloc_now cl s in CbnCOk (a, rs, s)
      | CbnCOk _ => CbnCFail CbnWRoots
      | CbnCFail w => CbnCFail w
      end
    else let (a, s) := cbn_alloc_now cl s in CbnCOk (a, rs, s).

  (** *** Delta, with the memo of this call *)

  Definition cbn_delta_new (kn : kername) (u : Instance.t) (body : term)
    (insts : list (Instance.t * cbn_cidx * term)) (s : cbn_state) : cbn_code * cbn_state :=
    let (c, s) := cbn_new_entry body u s in
    (c, cbn_set_memo (cbn_memo_set_delta
      (cbn_dt_add kn (CbnDBody body ((u, c.(cbn_c_entry), c.(cbn_c_term)) :: insts))
                                    s.(cbn_st_memo).(cbn_m_delta)) s.(cbn_st_memo)) s).

  (** [Some c]: the instantiated body; [None]: an axiom or opaque constant. *)
  Definition cbn_delta (kn : kername) (u : Instance.t) (s : cbn_state)
    : cbn_res (option cbn_code * cbn_state) :=
    match cbn_dt_find kn s.(cbn_st_memo).(cbn_m_delta) with
    | Some CbnDAxiom => CbnCOk (None, s)
    | Some (CbnDBody body insts) =>
      match cbn_find_inst u insts with
      | Some (i, t) => CbnCOk (Some (cbn_mkCode i cbn_path_nil t), s)
      | None => let (c, s) := cbn_delta_new kn u body insts s in CbnCOk (Some c, s)
      end
    | None =>
      match abstract_env_lookup X kn with
      | Some (ConstantDecl cb) =>
        match cb.(cst_body) with
        | Some body => let (c, s) := cbn_delta_new kn u body [] s in CbnCOk (Some c, s)
        | None =>
          CbnCOk (None, cbn_set_memo (cbn_memo_set_delta
            (cbn_dt_add kn CbnDAxiom s.(cbn_st_memo).(cbn_m_delta))
                                 s.(cbn_st_memo)) s)
        end
      | _ => CbnCFail CbnWDelta
      end
    end.

  (** *** Context entries: one cell per entry of [Γ], made on first use *)

  Definition cbn_gam (j : nat) (rs : list cbn_root) (s : cbn_state)
    : cbn_res (cbn_haddr * list cbn_root * cbn_state) :=
    let k := cbn_key_of_succ_nat j in
    match PTree.get k s.(cbn_st_gam) with
    | Some a => CbnCOk (a, rs, s)
    | None =>
      match nth_error Γ j with
      | None => CbnCFail CbnWCtx
      | Some decl =>
        let (cl, s) :=
          match decl.(decl_body) with
          | Some b =>
            let (c, s) := cbn_new_entry b [] s in
            (CbnCSusp [] 0 (S j) c, s)
          | None => (CbnCDone (CbnVNeu (CbnNVar (nctx - S j)) []), s)
          end in
        cbnlet (a, rs, s) := cbn_alloc cl rs s in
        CbnCOk (a, rs, cbn_set_gam (PTree.set k a s.(cbn_st_gam)) s)
      end
    end.

  Definition cbn_env_var (n : nat) (e : cbn_env) (rs : list cbn_root) (s : cbn_state)
    : cbn_res (cbn_slot * list cbn_root * cbn_state) :=
    match nth_error e.(cbn_ev_vals) n with
    | Some x => CbnCOk (x, rs, s)
    | None =>
      cbnlet (a, rs, s) := cbn_gam (n - e.(cbn_ev_nvals) + e.(cbn_ev_goff)) rs s in CbnCOk
        (CbnSAddr a, rs, s)
    end.

  (** The slot of an argument (of an application or a let): a variable reuses its slot;
    anything else is an inline suspension until it is bound or stored. *)
  Definition cbn_arg_slot (e : cbn_env) (c : cbn_code) (rs : list cbn_root) (s : cbn_state)
    : cbn_res (cbn_slot * list cbn_root * cbn_state) :=
    match c.(cbn_c_term) with
    | tRel n => cbn_env_var n e rs s
    | _ => CbnCOk (CbnSInl e.(cbn_ev_vals) e.(cbn_ev_nvals) e.(cbn_ev_goff) c, rs, s)
    end.

  (** Put a slot in the heap: lambdas, fixpoints, sorts, products, primitives and bodiless
    constants as value cells, anything else as a suspension. *)
  Definition cbn_materialize (x : cbn_slot) (rs : list cbn_root) (s : cbn_state)
    : cbn_res (cbn_haddr * list cbn_root * cbn_state) :=
    match x with
    | CbnSAddr a => CbnCOk (a, rs, s)
    | CbnSInl vs n o c =>
      match c.(cbn_c_term) with
      | tLambda _ _ _ => cbn_alloc (CbnCDone (CbnVLam (cbn_mkEnv vs n o) c)) rs s
      | tFix mfix idx =>
        match nth_error mfix idx with
        | Some _ => cbn_alloc (CbnCDone (CbnVFix (cbn_mkEnv vs n o) c idx [])) rs s
        | None => cbn_alloc (CbnCSusp vs n o c) rs s
        end
      | tSort _ | tProd _ _ _ | tPrim _ => cbn_alloc (CbnCDone (CbnVOpen (cbn_mkEnv vs n o) c)) rs s
      | tConst kn u =>
        match cbn_delta kn u s with
        | CbnCOk (None, s) => cbn_alloc (CbnCDone (CbnVNeu (CbnNConst c.(cbn_c_term)) [])) rs s
        | CbnCOk (Some _, s) => cbn_alloc (CbnCSusp vs n o c) rs s
        | CbnCFail _ => cbn_alloc (CbnCSusp vs n o c) rs s
        end
      | _ => cbn_alloc (CbnCSusp vs n o c) rs s
      end
    end.

  (** Bind a slot to the binder over the body [body]: an inline suspension stays inline if
    the variable occurs at most once in [body], and is put in the heap otherwise. *)
  Definition cbn_bind (x : cbn_slot) (body : cbn_code) (rs : list cbn_root) (s : cbn_state)
    : cbn_res (cbn_slot * list cbn_root * cbn_state) :=
    match x with
    | CbnSAddr _ => CbnCOk (x, rs, s)
    | CbnSInl _ _ _ _ =>
      let (once, s) := cbn_once_body body s in
      if once then CbnCOk (x, rs, s)
      else cbnlet (a, rs, s) := cbn_materialize x rs s in CbnCOk (CbnSAddr a, rs, s)
    end.

  (** Put every slot of a stack in the heap (a stack that becomes a value's spine). *)
  Fixpoint cbn_mat_all (d : cbn_fuel) (l : list cbn_slot) (rs : list cbn_root) (s : cbn_state)
    {struct d} : cbn_res (list cbn_haddr * list cbn_root * cbn_state) :=
    match l with
    | [] => CbnCOk ([], rs, s)
    | x :: l =>
      match d with
      | CbnFO => CbnCFail CbnWDepth
      | CbnFS k =>
        cbnlet (a, rs, s) := cbn_materialize x (CbnRSk l :: rs) s in
        match rs with
        | CbnRSk l :: rs =>
          cbnlet (al, rs, s) := cbn_mat_all (k tt) l (CbnRA a :: rs) s in
          match rs with
          | CbnRA a :: rs => CbnCOk (a :: al, rs, s)
          | _ => CbnCFail CbnWRoots
          end
        | _ => CbnCFail CbnWRoots
        end
      end
    end.

  (** Allocate the cells of the [n] fixpoints of the [tFix] code [c] over [e] and push them on
    [acc], fixpoint 0 first, so that [tRel 0] is fixpoint [n-1] as in [fix_subst]. *)
  Fixpoint cbn_push_fix_cells (e : cbn_env) (c : cbn_code) (i n : nat) (acc : cbn_env)
    (rs : list cbn_root) (s : cbn_state) : cbn_res (cbn_env * list cbn_root * cbn_state) :=
    match n with
    | O => CbnCOk (acc, rs, s)
    | S n =>
      cbnlet (a, rs, s) := cbn_alloc (CbnCDone (CbnVFix e c i [])) (CbnRE e :: CbnRE acc :: rs) s in
      match rs with
      | CbnRE e :: CbnRE acc :: rs => cbn_push_fix_cells e c (S i) n
        (cbn_env_push (CbnSAddr a) acc) rs s
      | _ => CbnCFail CbnWRoots
      end
    end.

  (** Push [n] fresh variables, levels [lvl] to [lvl + n - 1], on both environments. *)
  Fixpoint cbn_push_fresh (n lvl : nat) (e1 e2 : cbn_env) (rs : list cbn_root) (s : cbn_state)
    : cbn_res ((nat * cbn_env * cbn_env) * list cbn_root * cbn_state) :=
    match n with
    | O => CbnCOk ((lvl, e1, e2), rs, s)
    | S n =>
      cbnlet (x, rs, s) := cbn_alloc (CbnCDone (CbnVNeu (CbnNVar lvl) []))
        (CbnRE e1 :: CbnRE e2 :: rs) s in
      match rs with
      | CbnRE e1 :: CbnRE e2 :: rs =>
        cbn_push_fresh n (S lvl) (cbn_env_push (CbnSAddr x) e1) (cbn_env_push (CbnSAddr x) e2) rs s
      | _ => CbnCFail CbnWRoots
      end
    end.

  (** *** The machine *)

  Fixpoint cbn_force (d : cbn_fuel) (a : cbn_haddr) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (cbn_value * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match cbn_heap_get a s with
      | Some (CbnCDone v) => CbnCOk (v, rs, s)
      | Some (CbnCSusp vs n o c) =>
        match cbn_heap_upd a CbnCBusy s with
        | None => CbnCFail CbnWDangling
        | Some s =>
          cbnlet (v, rs, s) := cbn_whnf d (cbn_mkEnv vs n o) c [] (CbnRA a :: rs) s in
          match rs with
          | CbnRA a :: rs =>
            match cbn_heap_upd a (CbnCDone v) s with
            | Some s => CbnCOk (v, rs, s)
            | None => CbnCFail CbnWDangling
            end
          | _ => CbnCFail CbnWRoots
          end
        end
      | Some CbnCBusy => CbnCFail CbnWBusy
      | Some (CbnCFwd _) | None => CbnCFail CbnWDangling
      end
    end

  (** Evaluate a slot applied to [stk]: an address is forced, an inline suspension is
    evaluated in place (no write-back). *)
  with cbn_eval_slot (d : cbn_fuel) (x : cbn_slot) (stk : list cbn_slot) (rs : list cbn_root)
    (s : cbn_state) {struct d} : cbn_res (cbn_value * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match x with
      | CbnSAddr a =>
        cbnlet (v, rs, s) := cbn_force d a (CbnRSk stk :: rs) s in
        match rs with
        | CbnRSk stk :: rs => cbn_apply d v stk rs s
        | _ => CbnCFail CbnWRoots
        end
      | CbnSInl vs n o c => cbn_whnf d (cbn_mkEnv vs n o) c stk rs s
      end
    end

  with cbn_whnf (d : cbn_fuel) (e : cbn_env) (c : cbn_code) (stk : list cbn_slot)
    (rs : list cbn_root)
    (s : cbn_state) {struct d} : cbn_res (cbn_value * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match cbn_tick s with
      | None => CbnCFail CbnWSteps
      | Some s =>
      match c.(cbn_c_term) with
      | tRel n =>
        cbnlet (x, rs, s) := cbn_env_var n e (CbnRSk stk :: rs) s in
        match rs with
        | CbnRSk stk :: rs => cbn_eval_slot d x stk rs s
        | _ => CbnCFail CbnWRoots
        end
      | tApp f arg =>
        cbnlet (x, rs, s) := cbn_arg_slot e (cbn_child c 1 arg) (CbnRE e :: CbnRSk stk :: rs) s in
        match rs with
        | CbnRE e :: CbnRSk stk :: rs => cbn_whnf d e (cbn_child c 0 f) (x :: stk) rs s
        | _ => CbnCFail CbnWRoots
        end
      | tLambda _ _ b =>
        match stk with
        | x :: stk =>
          let cb := cbn_child c 1 b in
          cbnlet (x, rs, s) := cbn_bind x cb (CbnRE e :: CbnRSk stk :: rs) s in
          match rs with
          | CbnRE e :: CbnRSk stk :: rs => cbn_whnf d (cbn_env_push x e) cb stk rs s
          | _ => CbnCFail CbnWRoots
          end
        | [] => CbnCOk (CbnVLam e c, rs, s)
        end
      | tLetIn _ b _ body =>
        let cb := cbn_child c 2 body in
        cbnlet (x, rs, s) := cbn_arg_slot e (cbn_child c 0 b) (CbnRE e :: CbnRSk stk :: rs) s in
        match rs with
        | CbnRE e :: CbnRSk stk :: rs =>
          cbnlet (x, rs, s) := cbn_bind x cb (CbnRE e :: CbnRSk stk :: rs) s in
          match rs with
          | CbnRE e :: CbnRSk stk :: rs => cbn_whnf d (cbn_env_push x e) cb stk rs s
          | _ => CbnCFail CbnWRoots
          end
        | _ => CbnCFail CbnWRoots
        end
      | tConst kn u =>
        cbn2 (r, s) := cbn_delta kn u s in
        match r with
        | Some c' => cbn_whnf d cbn_env_empty c' stk rs s
        | None =>
          cbnlet (sp, rs, s) := cbn_mat_all d stk rs s in CbnCOk
            (CbnVNeu (CbnNConst c.(cbn_c_term)) sp, rs, s)
        end
      | tConstruct _ _ _ | tInd _ _ =>
        cbnlet (sp, rs, s) := cbn_mat_all d stk rs s in CbnCOk (CbnVCon c.(cbn_c_term) sp, rs, s)
      | tCase ci p scrut brs =>
        cbnlet (v, rs, s) := cbn_whnf d e (cbn_child c 0 scrut) []
          (CbnRE e :: CbnRSk stk :: rs) s in
        match rs with
        | CbnRE e :: CbnRSk stk :: rs =>
          match v with
          | CbnVCon (tConstruct ind n _) args =>
            if cbn_inductive_eqb ind ci.(ci_ind) then
              match nth_error brs n with
              | Some br =>
                let cargs := skipn ci.(ci_npar) args in
                if forallb cbn_is_assum br.(bcontext)
                   && (#|args| == ci.(ci_npar) + context_assumptions br.(bcontext)) then
                  cbn_whnf d (cbn_env_push_addrs cargs e)
                    (cbn_child c (cbn_case_branch_step (N.of_nat n)) br.(bbody)) stk rs s
                else CbnCFail CbnWShape
              | None => CbnCFail CbnWShape
              end
            else CbnCFail CbnWShape
          | CbnVNeu _ _ | CbnVStuck _ _ _ | CbnVStuckFix _ _ _ _ =>
            cbnlet (sp, rs, s) := cbn_mat_all d stk (CbnRE e :: rs) s in
            match rs with
            | CbnRE e :: rs => CbnCOk (CbnVStuck e c sp, rs, s)
            | _ => CbnCFail CbnWRoots
            end
          | _ => CbnCFail CbnWShape
          end
        | _ => CbnCFail CbnWRoots
        end
      | tProj p arg =>
        cbnlet (v, rs, s) := cbn_whnf d e (cbn_child c 0 arg) [] (CbnRE e :: CbnRSk stk :: rs) s in
        match rs with
        | CbnRE e :: CbnRSk stk :: rs =>
          match v with
          | CbnVCon (tConstruct ind 0 _) args =>
            if cbn_inductive_eqb ind p.(proj_ind) then
              match nth_error args (p.(proj_npars) + p.(proj_arg)) with
              | Some a => cbn_eval_slot d (CbnSAddr a) stk rs s
              | None => CbnCFail CbnWShape
              end
            else CbnCFail CbnWShape
          | CbnVNeu _ _ | CbnVStuck _ _ _ | CbnVStuckFix _ _ _ _ =>
            cbnlet (sp, rs, s) := cbn_mat_all d stk (CbnRE e :: rs) s in
            match rs with
            | CbnRE e :: rs => CbnCOk (CbnVStuck e c sp, rs, s)
            | _ => CbnCFail CbnWRoots
            end
          | _ => CbnCFail CbnWShape
          end
        | _ => CbnCFail CbnWRoots
        end
      | tFix mfix idx => cbn_whnf_fix d e c mfix idx stk rs s
      | tSort _ | tProd _ _ _ | tPrim _ =>
        match stk with
        | [] => CbnCOk (CbnVOpen e c, rs, s)
        | _ => CbnCFail CbnWShape
        end
      | _ => CbnCFail CbnWShape
      end
      end
    end

  with cbn_whnf_fix (d : cbn_fuel) (e : cbn_env) (c : cbn_code) (mfix : mfixpoint term) (idx : nat)
    (stk : list cbn_slot) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (cbn_value * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match nth_error mfix idx with
      | None => CbnCFail CbnWShape
      | Some def =>
        match nth_error stk def.(rarg) with
        | None =>
          cbnlet (sp, rs, s) := cbn_mat_all d stk (CbnRE e :: rs) s in
          match rs with
          | CbnRE e :: rs => CbnCOk (CbnVFix e c idx sp, rs, s)
          | _ => CbnCFail CbnWRoots
          end
        | Some x =>
          cbnlet (a, rs, s) := cbn_materialize x (CbnRE e :: CbnRSk stk :: rs) s in
          match rs with
          | CbnRE e :: CbnRSk stk :: rs =>
            let stk := cbn_list_set stk def.(rarg) (CbnSAddr a) in
            cbnlet (v, rs, s) := cbn_force d a (CbnRE e :: CbnRSk stk :: rs) s in
            match rs with
            | CbnRE e :: CbnRSk stk :: rs =>
              match v with
              | CbnVCon (tConstruct _ _ _) _ =>
                (* The stack holds the forced argument in a fresh cell, so that the
                   argument the unfolded body sees is the constructor the guard tested. *)
                cbnlet (a2, rs, s) := cbn_alloc (CbnCDone v) (CbnRE e :: CbnRSk stk :: rs) s in
                match rs with
                | CbnRE e :: CbnRSk stk :: rs =>
                  let stk := cbn_list_set stk def.(rarg) (CbnSAddr a2) in
                  cbnlet (e', rs, s) := cbn_push_fix_cells e c 0 #|mfix| e (CbnRSk stk :: rs) s in
                  match rs with
                  | CbnRSk stk :: rs => cbn_whnf d e'
                    (cbn_child c (N.of_nat idx) def.(dbody)) stk rs s
                  | _ => CbnCFail CbnWRoots
                  end
                | _ => CbnCFail CbnWRoots
                end
              | CbnVNeu _ _ | CbnVStuck _ _ _ | CbnVStuckFix _ _ _ _ =>
                cbnlet (sp, rs, s) := cbn_mat_all d stk (CbnRE e :: rs) s in
                match rs with
                | CbnRE e :: rs => CbnCOk (CbnVStuckFix e c idx sp, rs, s)
                | _ => CbnCFail CbnWRoots
                end
              | _ => CbnCFail CbnWShape
              end
            | _ => CbnCFail CbnWRoots
            end
          | _ => CbnCFail CbnWRoots
          end
        end
      end
    end

  with cbn_apply (d : cbn_fuel) (v : cbn_value) (stk : list cbn_slot) (rs : list cbn_root)
    (s : cbn_state) {struct d} : cbn_res (cbn_value * list cbn_root * cbn_state) :=
    match stk with
    | [] => CbnCOk (v, rs, s)
    | _ =>
      match d with
      | CbnFO => CbnCFail CbnWDepth
      | CbnFS k =>
        let d := k tt in
        match v with
        | CbnVLam e c =>
          match c.(cbn_c_term), stk with
          | tLambda _ _ b, x :: stk =>
            let cb := cbn_child c 1 b in
            cbnlet (x, rs, s) := cbn_bind x cb (CbnRE e :: CbnRSk stk :: rs) s in
            match rs with
            | CbnRE e :: CbnRSk stk :: rs => cbn_whnf d (cbn_env_push x e) cb stk rs s
            | _ => CbnCFail CbnWRoots
            end
          | _, _ => CbnCFail CbnWShape
          end
        | CbnVFix e c idx args =>
          match c.(cbn_c_term) with
          | tFix mfix _ => cbn_whnf_fix d e c mfix idx (map CbnSAddr args ++ stk) rs s
          | _ => CbnCFail CbnWShape
          end
        | CbnVOpen _ _ => CbnCFail CbnWShape
        | CbnVCon _ _ | CbnVStuckFix _ _ _ _ | CbnVNeu _ _ | CbnVStuck _ _ _ =>
          cbnlet (sp, rs, s) := cbn_mat_all d stk (CbnRV v :: rs) s in
          match rs with
          | CbnRV v :: rs =>
            match cbn_add_spine v sp with
            | Some v => CbnCOk (v, rs, s)
            | None => CbnCFail CbnWShape
            end
          | _ => CbnCFail CbnWRoots
          end
        end
      end
    end.

  (** *** Read-back to a term in [Γ] extended by [lvl - nctx] fresh variables (no
    allocation) *)

  Fixpoint cbn_map_st {A B S} (f : A -> S -> cbn_res (B * S)) (l : list A) (s : S)
    : cbn_res (list B * S) :=
    match l with
    | [] => CbnCOk ([], s)
    | x :: l =>
      cbn2 (y, s) := f x s in
      cbn2 (ys, s) := cbn_map_st f l s in
      CbnCOk (y :: ys, s)
    end.

  Fixpoint cbn_rb_cell (d : cbn_fuel) (lvl : nat) (a : cbn_haddr) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match cbn_heap_get a s with
      | Some (CbnCDone v) => cbn_rb_value d lvl v s
      | Some (CbnCSusp vs n o c) => cbn_rb_susp d lvl (cbn_mkEnv vs n o) c.(cbn_c_term) s
      | Some CbnCBusy => CbnCFail CbnWBusy
      | Some (CbnCFwd _) | None => CbnCFail CbnWDangling
      end
    end

  with cbn_rb_slot (d : cbn_fuel) (lvl : nat) (x : cbn_slot) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match x with
      | CbnSAddr a => cbn_rb_cell d lvl a s
      | CbnSInl vs n o c => cbn_rb_susp d lvl (cbn_mkEnv vs n o) c.(cbn_c_term) s
      end
    end

  with cbn_rb_susp (d : cbn_fuel) (lvl : nat) (e : cbn_env) (t : term) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match cbn_tick s with
      | None => CbnCFail CbnWSteps
      | Some s =>
        cbn2 (ts, s) := cbn_map_st (cbn_rb_slot d lvl) e.(cbn_ev_vals) s in
        CbnCOk (subst ts 0 (lift (lvl - nctx + e.(cbn_ev_goff)) e.(cbn_ev_nvals) t), s)
      end
    end

  with cbn_rb_value (d : cbn_fuel) (lvl : nat) (v : cbn_value) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      let spine h sp s :=
        cbn2 (ts, s) := cbn_map_st (cbn_rb_cell d lvl) sp s in
        CbnCOk (mkApps h ts, s) in
      match v with
      | CbnVCon h sp => spine h sp s
      | CbnVLam e c | CbnVOpen e c => cbn_rb_susp d lvl e c.(cbn_c_term) s
      | CbnVFix e c i sp | CbnVStuckFix e c i sp =>
        match c.(cbn_c_term) with
        | tFix mfix _ =>
          cbn2 (h, s) := cbn_rb_susp d lvl e (tFix mfix i) s in
          spine h sp s
        | _ => CbnCFail CbnWShape
        end
      | CbnVNeu (CbnNVar l) sp => spine (tRel (lvl - S l)) sp s
      | CbnVNeu (CbnNConst h) sp => spine h sp s
      | CbnVStuck e c sp =>
        cbn2 (h, s) := cbn_rb_susp d lvl e c.(cbn_c_term) s in
        spine h sp s
      end
    end.

  (** *** The comparison: [CbnCOk (true, rs, s)] convertible; [CbnCOk (false, rs, s)] this rule does
    not apply (try the next one, or "don't know"); [CbnCFail w] give up the whole call. *)

  Definition cbn_slot_same (x1 x2 : cbn_slot) : bool :=
    match x1, x2 with
    | CbnSAddr a1, CbnSAddr a2 => cbn_haddr_eqb a1 a2
    | _, _ => false
    end.

  Fixpoint cbn_conv_slot (d : cbn_fuel) (lvl : nat) (le : conv_pb) (x1 x2 : cbn_slot)
    (rs : list cbn_root) (s : cbn_state) {struct d} : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match x1, x2 with
      | CbnSAddr a1, CbnSAddr a2 =>
        if cbn_haddr_eqb a1 a2 then CbnCOk (true, rs, s) else cbn_conv_eval d lvl le x1 x2 rs s
      | CbnSInl vs1 n1 o1 c1, CbnSInl vs2 n2 o2 c2 =>
        cbnlet (b, rs, s) := cbn_conv_same_code d lvl (cbn_mkEnv vs1 n1 o1) c1
          (cbn_mkEnv vs2 n2 o2) c2
                               (CbnRSl x1 :: CbnRSl x2 :: rs) s in
        match rs with
        | CbnRSl x1 :: CbnRSl x2 :: rs =>
          if b then CbnCOk (true, rs, s) else cbn_conv_eval d lvl le x1 x2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | _, _ => cbn_conv_eval d lvl le x1 x2 rs s
      end
    end

  with cbn_conv_eval (d : cbn_fuel) (lvl : nat) (le : conv_pb) (x1 x2 : cbn_slot)
    (rs : list cbn_root) (s : cbn_state) {struct d} : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      cbnlet (v1, rs, s) := cbn_eval_slot d x1 [] (CbnRSl x2 :: rs) s in
      match rs with
      | CbnRSl x2 :: rs =>
        cbnlet (v2, rs, s) := cbn_eval_slot d x2 [] (CbnRV v1 :: rs) s in
        match rs with
        | CbnRV v1 :: rs => cbn_conv_value d lvl le v1 v2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | _ => CbnCFail CbnWRoots
      end
    end

  (** Spines pairwise at [Conv]. *)
  with cbn_conv_cells (d : cbn_fuel) (lvl : nat) (l1 l2 : list cbn_haddr) (rs : list cbn_root)
    (s : cbn_state) {struct d} : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | a1 :: l1, a2 :: l2 =>
        cbnwhen 2 (rs, s) := cbn_conv_slot d lvl Conv (CbnSAddr a1) (CbnSAddr a2)
          (CbnRSp l1 :: CbnRSp l2 :: rs) s in
        match rs with
        | CbnRSp l1 :: CbnRSp l2 :: rs => cbn_conv_cells d lvl l1 l2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | _, _ => CbnCOk (false, rs, s)
      end
    end

  with cbn_conv_term (d : cbn_fuel) (lvl : nat) (le : conv_pb) (e1 : cbn_env) (c1 : cbn_code)
    (e2 : cbn_env) (c2 : cbn_code) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      cbnlet (v1, rs, s) := cbn_whnf d e1 c1 [] (CbnRE e2 :: rs) s in
      match rs with
      | CbnRE e2 :: rs =>
        cbnlet (v2, rs, s) := cbn_whnf d e2 c2 [] (CbnRV v1 :: rs) s in
        match rs with
        | CbnRV v1 :: rs => cbn_conv_value d lvl le v1 v2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | _ => CbnCFail CbnWRoots
      end
    end

  (** Same code: equal [goff] and [nvals], equal codes ([cbn_code_eq]), and the environment
    slots free in the code pairwise convertible at [Conv]. *)
  with cbn_conv_same_code (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code) (e2 : cbn_env)
    (c2 : cbn_code) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      if (e1.(cbn_ev_goff) == e2.(cbn_ev_goff)) && (e1.(cbn_ev_nvals) == e2.(cbn_ev_nvals)) then
        let (b, s) := cbn_code_eq c1 c2 s in
        if b then cbn_same_code_cells d lvl c1.(cbn_c_term) 0 e1.(cbn_ev_vals) e2.(cbn_ev_vals) rs s
        else CbnCOk (false, rs, s)
      else CbnCOk (false, rs, s)
    end

  with cbn_same_code_cells (d : cbn_fuel) (lvl : nat) (t : term) (i : nat)
    (l1 l2 : list cbn_slot) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | x1 :: l1, x2 :: l2 =>
        if cbn_slot_same x1 x2 || noccur_between i 1 t then cbn_same_code_cells d lvl t
          (S i) l1 l2 rs s
        else
          cbnwhen 2 (rs, s) := cbn_conv_slot d lvl Conv x1 x2 (CbnRSk l1 :: CbnRSk l2 :: rs) s in
          match rs with
          | CbnRSk l1 :: CbnRSk l2 :: rs => cbn_same_code_cells d lvl t (S i) l1 l2 rs s
          | _ => CbnCFail CbnWRoots
          end
      | _, _ => CbnCOk (false, rs, s)
      end
    end

  (** Congruence of two stuck matches. *)
  with cbn_case_cong (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code) (e2 : cbn_env)
    (c2 : cbn_code) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match c1.(cbn_c_term), c2.(cbn_c_term) with
      | tCase ci1 p1 sc1 brs1, tCase ci2 p2 sc2 brs2 =>
        if cbn_case_info_eqb ci1 ci2 && (#|brs1| == #|brs2|) && (#|p1.(pparams)| == #|p2.(pparams)|)
           && forallb2 cbn_cmp_level_conv p1.(puinst) p2.(puinst)
           && cbn_case_ctx_ok p1.(pcontext) p2.(pcontext)
        then
          cbnwhen 2 (rs, s) := cbn_case_params d lvl e1 c1 e2 c2 0%N p1.(pparams) p2.(pparams)
                               (CbnRE e1 :: CbnRE e2 :: rs) s in
          match rs with
          | CbnRE e1 :: CbnRE e2 :: rs =>
            cbnlet (r, rs, s) := cbn_push_fresh #|p1.(pcontext)| lvl e1 e2
              (CbnRE e1 :: CbnRE e2 :: rs) s in
            let '(lvlr, er1, er2) := r in
            cbnwhen 2 (rs, s) := cbn_conv_term d lvlr Conv er1 (cbn_child c1 1 p1.(preturn))
                                 er2 (cbn_child c2 1 p2.(preturn)) rs s in
            match rs with
            | CbnRE e1 :: CbnRE e2 :: rs =>
              cbnwhen 2 (rs, s) := cbn_conv_term d lvl Conv e1 (cbn_child c1 0 sc1) e2
                (cbn_child c2 0 sc2)
                                   (CbnRE e1 :: CbnRE e2 :: rs) s in
              match rs with
              | CbnRE e1 :: CbnRE e2 :: rs => cbn_case_branches d lvl e1 c1 e2 c2 0%N brs1 brs2 rs s
              | _ => CbnCFail CbnWRoots
              end
            | _ => CbnCFail CbnWRoots
            end
          | _ => CbnCFail CbnWRoots
          end
        else CbnCOk (false, rs, s)
      | _, _ => CbnCOk (false, rs, s)
      end
    end

  with cbn_case_params (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code) (e2 : cbn_env)
    (c2 : cbn_code) (i : N) (l1 l2 : list term) (rs : list cbn_root) (s : cbn_state) {struct d}
    : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | t1 :: l1, t2 :: l2 =>
        cbnwhen 2 (rs, s) := cbn_conv_term d lvl Conv e1 (cbn_child c1 (cbn_case_param_step i) t1)
                             e2 (cbn_child c2 (cbn_case_param_step i) t2)
                               (CbnRE e1 :: CbnRE e2 :: rs) s in
        match rs with
        | CbnRE e1 :: CbnRE e2 :: rs => cbn_case_params d lvl e1 c1 e2 c2 (N.succ i) l1 l2 rs s
        | _ => CbnCFail CbnWRoots
        end
      | _, _ => CbnCOk (false, rs, s)
      end
    end

  with cbn_case_branches (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : cbn_code) (e2 : cbn_env)
    (c2 : cbn_code) (i : N) (l1 l2 : list (branch term)) (rs : list cbn_root) (s : cbn_state)
    {struct d} : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => CbnCOk (true, rs, s)
      | b1 :: l1, b2 :: l2 =>
        if cbn_case_ctx_ok b1.(bcontext) b2.(bcontext) then
          cbnlet (r, rs, s) := cbn_push_fresh #|b1.(bcontext)| lvl e1 e2
            (CbnRE e1 :: CbnRE e2 :: rs) s in
          let '(lvlb, eb1, eb2) := r in
          cbnwhen 2 (rs, s) := cbn_conv_term d lvlb Conv eb1
            (cbn_child c1 (cbn_case_branch_step i) b1.(bbody))
                               eb2 (cbn_child c2 (cbn_case_branch_step i) b2.(bbody)) rs s in
          match rs with
          | CbnRE e1 :: CbnRE e2 :: rs => cbn_case_branches d lvl e1 c1 e2 c2 (N.succ i) l1 l2 rs s
          | _ => CbnCFail CbnWRoots
          end
        else CbnCOk (false, rs, s)
      | _, _ => CbnCOk (false, rs, s)
      end
    end

  (** The comparison of two weak-head values that [cbn_conv_value] did not settle by a shared
    code. *)
  with cbn_conv_rows (d : cbn_fuel) (lvl : nat) (le : conv_pb) (v1 v2 : cbn_value)
    (rs : list cbn_root) (s : cbn_state) {struct d} : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match v1, v2 with
      | CbnVCon h1 sp1, CbnVCon h2 sp2 =>
        let n := #|sp1| in
        if (n == #|sp2|) && cbn_cmp_term le n h1 h2 then cbn_conv_cells d lvl sp1 sp2 rs s
        else CbnCOk (false, rs, s)
      | CbnVNeu (CbnNVar l1) sp1, CbnVNeu (CbnNVar l2) sp2 =>
        if l1 == l2 then cbn_conv_cells d lvl sp1 sp2 rs s else CbnCOk (false, rs, s)
      | CbnVNeu (CbnNConst h1) sp1, CbnVNeu (CbnNConst h2) sp2 =>
        if cbn_cmp_term Conv #|sp1| h1 h2 then cbn_conv_cells d lvl sp1 sp2 rs s else CbnCOk
          (false, rs, s)
      | CbnVLam e1 c1, CbnVLam e2 c2 =>
        match c1.(cbn_c_term), c2.(cbn_c_term) with
        | tLambda na1 A1 b1, tLambda na2 A2 b2 =>
          if eqb_binder_annot na1 na2 then
            cbnwhen 2 (rs, s) := cbn_conv_term d lvl Conv e1 (cbn_child c1 0 A1) e2
              (cbn_child c2 0 A2)
                                 (CbnRE e1 :: CbnRE e2 :: rs) s in
            match rs with
            | CbnRE e1 :: CbnRE e2 :: rs =>
              cbnlet (x, rs, s) := cbn_alloc (CbnCDone (CbnVNeu (CbnNVar lvl) []))
                (CbnRE e1 :: CbnRE e2 :: rs) s in
              match rs with
              | CbnRE e1 :: CbnRE e2 :: rs =>
                cbn_conv_term d (S lvl) Conv (cbn_env_push (CbnSAddr x) e1) (cbn_child c1 1 b1)
                  (cbn_env_push (CbnSAddr x) e2) (cbn_child c2 1 b2) rs s
              | _ => CbnCFail CbnWRoots
              end
            | _ => CbnCFail CbnWRoots
            end
          else CbnCOk (false, rs, s)
        | _, _ => CbnCOk (false, rs, s)
        end
      | CbnVOpen e1 c1, CbnVOpen e2 c2 =>
        match c1.(cbn_c_term), c2.(cbn_c_term) with
        | tProd na1 A1 B1, tProd na2 A2 B2 =>
          if eqb_binder_annot na1 na2 then
            cbnwhen 2 (rs, s) := cbn_conv_term d lvl Conv e1 (cbn_child c1 0 A1) e2
              (cbn_child c2 0 A2)
                                 (CbnRE e1 :: CbnRE e2 :: rs) s in
            match rs with
            | CbnRE e1 :: CbnRE e2 :: rs =>
              cbnlet (x, rs, s) := cbn_alloc (CbnCDone (CbnVNeu (CbnNVar lvl) []))
                (CbnRE e1 :: CbnRE e2 :: rs) s in
              match rs with
              | CbnRE e1 :: CbnRE e2 :: rs =>
                cbn_conv_term d (S lvl) le (cbn_env_push (CbnSAddr x) e1) (cbn_child c1 1 B1)
                  (cbn_env_push (CbnSAddr x) e2) (cbn_child c2 1 B2) rs s
              | _ => CbnCFail CbnWRoots
              end
            | _ => CbnCFail CbnWRoots
            end
          else CbnCOk (false, rs, s)
        | tSort s1, tSort s2 => CbnCOk (cbn_cmp_sort le s1 s2, rs, s)
        | tPrim _, tPrim _ =>
          cbn2 (t1, s) := cbn_rb_susp d lvl e1 c1.(cbn_c_term) s in
          cbn2 (t2, s) := cbn_rb_susp d lvl e2 c2.(cbn_c_term) s in
          CbnCOk (cbn_cmp_term Conv 0 t1 t2, rs, s)
        | _, _ => CbnCOk (false, rs, s)
        end
      | CbnVStuck e1 c1 sp1, CbnVStuck e2 c2 sp2 =>
        if #|sp1| == #|sp2| then
          cbnlet (b, rs, s) :=
            match c1.(cbn_c_term), c2.(cbn_c_term) with
            | tCase _ _ _ _, tCase _ _ _ _ =>
              cbn_case_cong d lvl e1 c1 e2 c2 (CbnRV v1 :: CbnRV v2 :: rs) s
            | _, _ => CbnCOk (false, CbnRV v1 :: CbnRV v2 :: rs, s)
            end in
          match rs with
          | CbnRV (CbnVStuck e1 c1 sp1) :: CbnRV (CbnVStuck e2 c2 sp2) :: rs =>
            if b then cbn_conv_cells d lvl sp1 sp2 rs s
            else
              cbn2 (t1, s) := cbn_rb_susp d lvl e1 c1.(cbn_c_term) s in
              cbn2 (t2, s) := cbn_rb_susp d lvl e2 c2.(cbn_c_term) s in
              if cbn_cmp_term Conv #|sp1| t1 t2 then cbn_conv_cells d lvl sp1 sp2 rs s
              else CbnCOk (false, rs, s)
          | _ => CbnCFail CbnWRoots
          end
        else CbnCOk (false, rs, s)
      | CbnVFix e1 c1 i1 sp1, CbnVFix e2 c2 i2 sp2
      | CbnVStuckFix e1 c1 i1 sp1, CbnVStuckFix e2 c2 i2 sp2 =>
        if (i1 == i2) && (#|sp1| == #|sp2|) then
          match c1.(cbn_c_term), c2.(cbn_c_term) with
          | tFix m1 _, tFix m2 _ =>
            cbn2 (t1, s) := cbn_rb_susp d lvl e1 (tFix m1 i1) s in
            cbn2 (t2, s) := cbn_rb_susp d lvl e2 (tFix m2 i2) s in
            if cbn_cmp_term Conv #|sp1| t1 t2 then cbn_conv_cells d lvl sp1 sp2 rs s
            else CbnCOk (false, rs, s)
          | _, _ => CbnCOk (false, rs, s)
          end
        else CbnCOk (false, rs, s)
      | _, _ => CbnCOk (false, rs, s)
      end
    end

  (** Same code first for closures, stuck terms and fixpoints, then the rows. The values are
    roots across the same-code test, for the fallback. *)
  with cbn_conv_value (d : cbn_fuel) (lvl : nat) (le : conv_pb) (v1 v2 : cbn_value)
    (rs : list cbn_root) (s : cbn_state) {struct d} : cbn_res (bool * list cbn_root * cbn_state) :=
    match d with
    | CbnFO => CbnCFail CbnWDepth
    | CbnFS k =>
      let d := k tt in
      match cbn_tick s with
      | None => CbnCFail CbnWSteps
      | Some s =>
        let same e1 c1 e2 c2 (spines : bool) :=
          cbnlet (b, rs, s) := cbn_conv_same_code d lvl e1 c1 e2 c2
            (CbnRV v1 :: CbnRV v2 :: rs) s in
          match rs with
          | CbnRV v1 :: CbnRV v2 :: rs =>
            if b then
              if spines then cbn_conv_cells d lvl (cbn_spine_of v1) (cbn_spine_of v2) rs s
              else CbnCOk (true, rs, s)
            else cbn_conv_rows d lvl le v1 v2 rs s
          | _ => CbnCFail CbnWRoots
          end in
        match v1, v2 with
        | CbnVLam e1 c1, CbnVLam e2 c2 | CbnVOpen e1 c1, CbnVOpen e2 c2 => same e1 c1 e2 c2 false
        | CbnVStuck e1 c1 sp1, CbnVStuck e2 c2 sp2 =>
          if #|sp1| == #|sp2| then same e1 c1 e2 c2 true else cbn_conv_rows d lvl le v1 v2 rs s
        | CbnVFix e1 c1 i1 sp1, CbnVFix e2 c2 i2 sp2
        | CbnVStuckFix e1 c1 i1 sp1, CbnVStuckFix e2 c2 i2 sp2 =>
          if (i1 == i2) && (#|sp1| == #|sp2|) then same e1 c1 e2 c2 true
          else cbn_conv_rows d lvl le v1 v2 rs s
        | _, _ => cbn_conv_rows d lvl le v1 v2 rs s
        end
      end
    end.

  Definition cbn_run (le : conv_pb) (t u : term) : cbn_answer :=
    let s := cbn_init in
    let (c1, s) := cbn_new_entry t [] s in
    let (c2, s) := cbn_new_entry u [] s in
    match cbn_conv_term cbn_depth nctx le cbn_env_empty c1 cbn_env_empty c2 [] s with
    | CbnCOk (true, _, _) => CbnYes
    | CbnCOk (false, _, _) => CbnNoRule
    | CbnCFail w => CbnFail w
    end.

End CallByNeed.

(** The answer of the fast path, with the reason for a "don't know". *)
Definition cbn_conv_answer {cf : checker_flags} (X_type : abstract_env_impl)
  (X : X_type.π2.π1) (le : conv_pb) (Γ : context) (t u : term) : cbn_answer :=
  cbn_run X_type X Γ #|Γ| le t u.

(** [true]: [t] and [u] are convertible at [le] in [Γ]. [false]: don't know. *)
Definition cbn_conv {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
  (le : conv_pb) (Γ : context) (t u : term) : bool :=
  match cbn_conv_answer X_type X le Γ t u with
  | CbnYes => true
  | _ => false
  end.
