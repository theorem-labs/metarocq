(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICWfUniverses.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv.

Import CanonicalTries.

(** * Call-by-need conversion fast path (design CN-1 of BET-298)

  [cbn_conv le Γ t u] evaluates [t] and [u] with a weak-head call-by-need environment
  machine and compares the weak-head values. [true] means that [t] and [u] are convertible
  at [le]; [false] means "don't know", never "not convertible".

  - Heap: a persistent [PTree] from addresses ([String2pos.positive]) to cells. A cell holds
    a suspension (environment, code), a value, or a black hole while it is forced. Forcing
    writes the value back.
  - Environment: the heap addresses of the bound variables, their number, and the offset in
    [Γ] of the free variables beyond them ([goff]).
  - Code: every term the machine evaluates is the subterm, at a path, of the instantiated
    term of an entry of the code table. A code carries the entry index, the path (newest step
    first) and that subterm. The table only grows and an entry never changes, so equal
    (index, path) pairs mean equal codes.
  - Bounds: every function is a structural [Fixpoint] on a lazily generated [cbn_fuel] (the
    recursion depth, in effect unbounded), and every machine, read-back and comparison step
    takes one unit of an [N] step budget. Out of budget means "don't know".
  - Delta: constant bodies are looked up once per [cbn_conv] call and memoised by kername;
    one code entry per (constant, syntactic instance).

  No soundness proofs yet: the comparison theorem is the hook obligation in
  [PCUICTypeChecker.convert]. *)

Local Notation addr := String2pos.positive.

Fixpoint addr_succ (p : addr) : addr :=
  match p with
  | String2pos.xI q => String2pos.xO (addr_succ q)
  | String2pos.xO q => String2pos.xI q
  | String2pos.xH => String2pos.xO String2pos.xH
  end.

Fixpoint addr_eqb (p q : addr) : bool :=
  match p, q with
  | String2pos.xI p, String2pos.xI q => addr_eqb p q
  | String2pos.xO p, String2pos.xO q => addr_eqb p q
  | String2pos.xH, String2pos.xH => true
  | _, _ => false
  end.

Fixpoint addr_of_succ_nat (n : nat) : addr :=
  match n with
  | O => String2pos.xH
  | S n => addr_succ (addr_of_succ_nat n)
  end.

(** ** Fuel *)

(** The recursion bound. [FS k] produces the next unit on demand, so a large bound costs no
  memory: [fuel_of_pos p k] is [p] units followed by [k tt]. *)
Inductive cbn_fuel := FO | FS (k : unit -> cbn_fuel).

Fixpoint fuel_of_pos (p : positive) (k : unit -> cbn_fuel) : cbn_fuel :=
  match p with
  | xH => FS k
  | xO p => fuel_of_pos p (fun _ => fuel_of_pos p k)
  | xI p => FS (fun _ => fuel_of_pos p (fun _ => fuel_of_pos p k))
  end.

(** 2^62 units of recursion depth. *)
Definition cbn_depth : cbn_fuel := fuel_of_pos 4611686018427387904%positive (fun _ => FO).

(** Step budget of one [cbn_conv] call. *)
Definition cbn_steps : N := 4000000000%N.

(** ** Code table *)

Inductive code_ns :=
| NSInput (right : bool)  (* an input term of the comparison *)
| NSCtx (j : nat)         (* the body of the context entry [j] of [Γ] *)
| NSConst (kn : kername). (* the body of a constant *)

Record code_entry := mkEntry {
  ce_term : term;
  ce_inst : Instance.t;
  ce_ns : code_ns }.

(** The term the machine evaluates for an entry: its term with its instance substituted.
  The empty instance leaves the term unchanged (monomorphic bodies have no universe
  variables). *)
Definition entry_code (e : code_entry) : term :=
  match e.(ce_inst) with
  | [] => e.(ce_term)
  | u => subst_instance u e.(ce_term)
  end.

Record code := mkCode {
  c_entry : addr;
  c_path : list N;
  c_term : term }.

(** Path steps: [tApp f a]: f 0, a 1; [tLambda]/[tProd]: domain 0, body 1; [tLetIn]: definition
  0, body 2; [tCase]: scrutinee 0, return 1, parameter [i] 2+2i, branch [i] 3+2i; [tProj]: 0;
  [tFix]: body of definition [i] is step [i]. *)
Definition child (c : code) (k : N) (t : term) : code :=
  mkCode c.(c_entry) (k :: c.(c_path)) t.

Definition case_param_step (i : N) : N := N.add 2 (N.double i).
Definition case_branch_step (i : N) : N := N.add 3 (N.double i).

Definition same_code (c1 c2 : code) : bool :=
  addr_eqb c1.(c_entry) c2.(c_entry) && forallb2 N.eqb c1.(c_path) c2.(c_path).

(** ** Machine data *)

Record cbn_env := mkEnv {
  ev_vals : list addr;
  ev_nvals : nat;
  ev_goff : nat }.

Definition env_empty : cbn_env := mkEnv [] 0 0.

Definition env_push (a : addr) (e : cbn_env) : cbn_env :=
  mkEnv (a :: e.(ev_vals)) (S e.(ev_nvals)) e.(ev_goff).

Definition env_push_all (l : list addr) (e : cbn_env) : cbn_env :=
  fold_left (fun e a => env_push a e) l e.

Inductive cbn_neutral :=
| NVar (lvl : nat)   (* a context variable without a body or a fresh variable, as a level *)
| NConst (h : term). (* an axiom or opaque constant [tConst kn u] *)

Inductive cbn_value :=
| VCon (h : term) (sp : list addr)                       (* [tConstruct]/[tInd] head *)
| VLam (e : cbn_env) (c : code)                          (* [tLambda] closure *)
| VFix (e : cbn_env) (c : code) (idx : nat) (sp : list addr)
    (* fixpoint [idx] of the [tFix] code [c], applied to too few arguments *)
| VStuckFix (e : cbn_env) (c : code) (idx : nat) (sp : list addr)
    (* fixpoint whose recursive argument is neutral or stuck *)
| VNeu (h : cbn_neutral) (sp : list addr)
| VOpen (e : cbn_env) (c : code)                         (* [tSort], [tProd], [tPrim] *)
| VStuck (e : cbn_env) (c : code) (sp : list addr).      (* stuck [tCase]/[tProj] *)

Inductive cbn_cell :=
| CSusp (e : cbn_env) (c : code)
| CDone (v : cbn_value)
| CBusy.

Inductive delta_memo :=
| DAxiom
| DBody (body : term) (insts : list (Instance.t * addr * term)).

Record cbn_state := mkState {
  st_heap : PTree.t cbn_cell;
  st_next : addr;
  st_steps : N;
  st_codes : PTree.t code_entry;
  st_ncode : addr;
  st_delta : KernameMap.t delta_memo;
  st_gam : PTree.t addr }.

Definition cbn_init : cbn_state :=
  mkState (PTree.empty _) String2pos.xH cbn_steps (PTree.empty _) String2pos.xH
    (KernameMap.empty _) (PTree.empty _).

Definition tick (s : cbn_state) : option cbn_state :=
  match s.(st_steps) with
  | N0 => None
  | n => Some (mkState s.(st_heap) s.(st_next) (N.pred n) s.(st_codes) s.(st_ncode)
                 s.(st_delta) s.(st_gam))
  end.

Definition heap_get (a : addr) (s : cbn_state) : option cbn_cell :=
  PTree.get a s.(st_heap).

Definition heap_set (a : addr) (c : cbn_cell) (s : cbn_state) : cbn_state :=
  mkState (PTree.set a c s.(st_heap)) s.(st_next) s.(st_steps) s.(st_codes) s.(st_ncode)
    s.(st_delta) s.(st_gam).

Definition alloc (c : cbn_cell) (s : cbn_state) : addr * cbn_state :=
  let a := s.(st_next) in
  (a, mkState (PTree.set a c s.(st_heap)) (addr_succ a) s.(st_steps) s.(st_codes)
        s.(st_ncode) s.(st_delta) s.(st_gam)).

Definition new_entry (e : code_entry) (s : cbn_state) : addr * cbn_state :=
  let i := s.(st_ncode) in
  (i, mkState s.(st_heap) s.(st_next) s.(st_steps) (PTree.set i e s.(st_codes))
        (addr_succ i) s.(st_delta) s.(st_gam)).

Definition set_delta (m : KernameMap.t delta_memo) (s : cbn_state) : cbn_state :=
  mkState s.(st_heap) s.(st_next) s.(st_steps) s.(st_codes) s.(st_ncode) m s.(st_gam).

Definition set_gam (m : PTree.t addr) (s : cbn_state) : cbn_state :=
  mkState s.(st_heap) s.(st_next) s.(st_steps) s.(st_codes) s.(st_ncode) s.(st_delta) m.

Fixpoint find_inst (u : Instance.t) (l : list (Instance.t * addr * term)) : option (addr * term) :=
  match l with
  | [] => None
  | (u', i, t) :: l => if Instance.eqb u u' then Some (i, t) else find_inst u l
  end.

Definition is_assum (d : context_decl) : bool :=
  match d.(decl_body) with None => true | Some _ => false end.

(** Allocate the cells of the [n] fixpoints of the [tFix] code [c] over [e] and push them on
  [acc], fixpoint 0 first, so that [tRel 0] is fixpoint [n-1] as in [fix_subst]. *)
Fixpoint push_fix_cells (e : cbn_env) (c : code) (i n : nat) (acc : cbn_env) (s : cbn_state)
  : cbn_env * cbn_state :=
  match n with
  | O => (acc, s)
  | S n =>
    let (a, s) := alloc (CDone (VFix e c i [])) s in
    push_fix_cells e c (S i) n (env_push a acc) s
  end.

(** Push [n] fresh variables, levels [lvl] to [lvl + n - 1], on both environments. *)
Fixpoint push_fresh (n lvl : nat) (e1 e2 : cbn_env) (s : cbn_state)
  : nat * cbn_env * cbn_env * cbn_state :=
  match n with
  | O => (lvl, e1, e2, s)
  | S n =>
    let (x, s) := alloc (CDone (VNeu (NVar lvl) [])) s in
    push_fresh n (S lvl) (env_push x e1) (env_push x e2) s
  end.

(** Contexts of a match related by [eq_context_upto_names], without let-ins. *)
Definition case_ctx_ok (ctx1 ctx2 : context) : bool :=
  forallb2 (fun d1 d2 => is_assum d1 && is_assum d2 && eqb_decl_upto_names d1 d2) ctx1 ctx2.

Local Notation "'cbnlet' ( x , s ) := c 'in' k" :=
  (match c with Some (x, s) => k | None => None end)
  (at level 200, x ident, s ident, c at level 100, k at level 200, only parsing).

Local Notation "'cbnwhen' s := c 'in' k" :=
  (match c with Some (true, s) => k | Some (false, s) => Some (false, s) | None => None end)
  (at level 200, s ident, c at level 100, k at level 200, only parsing).

Section CallByNeed.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat). (* nctx = #|Γ| *)

  (** *** Delta, with the memo of this call *)

  Definition delta_new (kn : kername) (u : Instance.t) (body : term)
    (insts : list (Instance.t * addr * term)) (s : cbn_state) : code * cbn_state :=
    let ent := mkEntry body u (NSConst kn) in
    let t := entry_code ent in
    let (i, s) := new_entry ent s in
    (mkCode i [] t, set_delta (KernameMap.add kn (DBody body ((u, i, t) :: insts)) s.(st_delta)) s).

  (** [Some (Some c)]: the instantiated body; [Some None]: an axiom or opaque constant;
    [None]: give up. *)
  Definition delta (kn : kername) (u : Instance.t) (s : cbn_state)
    : option (option code * cbn_state) :=
    match KernameMap.find kn s.(st_delta) with
    | Some DAxiom => Some (None, s)
    | Some (DBody body insts) =>
      match find_inst u insts with
      | Some (i, t) => Some (Some (mkCode i [] t), s)
      | None => let (c, s) := delta_new kn u body insts s in Some (Some c, s)
      end
    | None =>
      match abstract_env_lookup X kn with
      | Some (ConstantDecl cb) =>
        match cb.(cst_body) with
        | Some body => let (c, s) := delta_new kn u body [] s in Some (Some c, s)
        | None => Some (None, set_delta (KernameMap.add kn DAxiom s.(st_delta)) s)
        end
      | _ => None
      end
    end.

  (** *** Context entries: one cell per entry of [Γ], made on first use *)

  Definition gam (j : nat) (s : cbn_state) : option (addr * cbn_state) :=
    let key := addr_of_succ_nat j in
    match PTree.get key s.(st_gam) with
    | Some a => Some (a, s)
    | None =>
      match nth_error Γ j with
      | None => None
      | Some decl =>
        let (cl, s) :=
          match decl.(decl_body) with
          | Some b =>
            let (i, s) := new_entry (mkEntry b [] (NSCtx j)) s in
            (CSusp (mkEnv [] 0 (S j)) (mkCode i [] b), s)
          | None => (CDone (VNeu (NVar (nctx - S j)) []), s)
          end in
        let (a, s) := alloc cl s in
        Some (a, set_gam (PTree.set key a s.(st_gam)) s)
      end
    end.

  (** *** The machine *)

  Fixpoint force (d : cbn_fuel) (a : addr) (s : cbn_state) {struct d}
    : option (cbn_value * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match heap_get a s with
      | Some (CDone v) => Some (v, s)
      | Some (CSusp e c) =>
        cbnlet (v, s) := whnf d e c [] (heap_set a CBusy s) in
        Some (v, heap_set a (CDone v) s)
      | _ => None
      end
    end

  with whnf (d : cbn_fuel) (e : cbn_env) (c : code) (stk : list addr) (s : cbn_state)
    {struct d} : option (cbn_value * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match tick s with
      | None => None
      | Some s =>
      match c.(c_term) with
      | tRel n =>
        match nth_error e.(ev_vals) n with
        | Some a =>
          cbnlet (v, s) := force d a s in
          apply d v stk s
        | None =>
          cbnlet (a, s) := gam (n - e.(ev_nvals) + e.(ev_goff)) s in
          cbnlet (v, s) := force d a s in
          apply d v stk s
        end
      | tApp f arg =>
        let (a, s) := alloc (CSusp e (child c 1 arg)) s in
        whnf d e (child c 0 f) (a :: stk) s
      | tLambda _ _ b =>
        match stk with
        | a :: stk => whnf d (env_push a e) (child c 1 b) stk s
        | [] => Some (VLam e c, s)
        end
      | tLetIn _ b _ body =>
        let (a, s) := alloc (CSusp e (child c 0 b)) s in
        whnf d (env_push a e) (child c 2 body) stk s
      | tConst kn u =>
        cbnlet (r, s) := delta kn u s in
        match r with
        | Some c' => whnf d env_empty c' stk s
        | None => Some (VNeu (NConst c.(c_term)) stk, s)
        end
      | tConstruct _ _ _ | tInd _ _ => Some (VCon c.(c_term) stk, s)
      | tCase ci p scrut brs =>
        cbnlet (v, s) := whnf d e (child c 0 scrut) [] s in
        match v with
        | VCon (tConstruct ind n _) args =>
          if eqb ind ci.(ci_ind) then
            match nth_error brs n with
            | Some br =>
              let cargs := skipn ci.(ci_npar) args in
              if forallb is_assum br.(bcontext) && (#|cargs| == #|br.(bcontext)|) then
                whnf d (env_push_all cargs e) (child c (case_branch_step (N.of_nat n)) br.(bbody))
                  stk s
              else None
            | None => None
            end
          else None
        | VNeu _ _ | VStuck _ _ _ | VStuckFix _ _ _ _ => Some (VStuck e c stk, s)
        | _ => None
        end
      | tProj p arg =>
        cbnlet (v, s) := whnf d e (child c 0 arg) [] s in
        match v with
        | VCon (tConstruct ind 0 _) args =>
          if eqb ind p.(proj_ind) then
            match nth_error args (p.(proj_npars) + p.(proj_arg)) with
            | Some a =>
              cbnlet (v, s) := force d a s in
              apply d v stk s
            | None => None
            end
          else None
        | VNeu _ _ | VStuck _ _ _ | VStuckFix _ _ _ _ => Some (VStuck e c stk, s)
        | _ => None
        end
      | tFix mfix idx => whnf_fix d e c mfix idx stk s
      | tSort _ | tProd _ _ _ | tPrim _ =>
        match stk with
        | [] => Some (VOpen e c, s)
        | _ => None
        end
      | _ => None
      end
      end
    end

  with whnf_fix (d : cbn_fuel) (e : cbn_env) (c : code) (mfix : mfixpoint term) (idx : nat)
    (stk : list addr) (s : cbn_state) {struct d} : option (cbn_value * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match nth_error mfix idx with
      | None => None
      | Some def =>
        match nth_error stk def.(rarg) with
        | None => Some (VFix e c idx stk, s)
        | Some a =>
          cbnlet (v, s) := force d a s in
          match v with
          | VCon (tConstruct _ _ _) _ =>
            let (e', s) := push_fix_cells e c 0 #|mfix| e s in
            whnf d e' (child c (N.of_nat idx) def.(dbody)) stk s
          | VNeu _ _ | VStuck _ _ _ | VStuckFix _ _ _ _ => Some (VStuckFix e c idx stk, s)
          | _ => None
          end
        end
      end
    end

  with apply (d : cbn_fuel) (v : cbn_value) (stk : list addr) (s : cbn_state) {struct d}
    : option (cbn_value * cbn_state) :=
    match stk with
    | [] => Some (v, s)
    | _ =>
      match d with
      | FO => None
      | FS k =>
        let d := k tt in
        match v with
        | VCon h args => Some (VCon h (args ++ stk), s)
        | VLam e c =>
          match c.(c_term), stk with
          | tLambda _ _ b, a :: stk => whnf d (env_push a e) (child c 1 b) stk s
          | _, _ => None
          end
        | VFix e c idx args =>
          match c.(c_term) with
          | tFix mfix _ => whnf_fix d e c mfix idx (args ++ stk) s
          | _ => None
          end
        | VStuckFix e c idx args => Some (VStuckFix e c idx (args ++ stk), s)
        | VNeu h args => Some (VNeu h (args ++ stk), s)
        | VStuck e c args => Some (VStuck e c (args ++ stk), s)
        | VOpen _ _ => None
        end
      end
    end.

  (** *** Read-back to a term in [Γ] extended by [lvl - nctx] fresh variables *)

  Fixpoint map_st {A B S} (f : A -> S -> option (B * S)) (l : list A) (s : S)
    : option (list B * S) :=
    match l with
    | [] => Some ([], s)
    | x :: l =>
      cbnlet (y, s) := f x s in
      cbnlet (ys, s) := map_st f l s in
      Some (y :: ys, s)
    end.

  Fixpoint rb_cell (d : cbn_fuel) (lvl : nat) (a : addr) (s : cbn_state) {struct d}
    : option (term * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match heap_get a s with
      | Some (CDone v) => rb_value d lvl v s
      | Some (CSusp e c) => rb_susp d lvl e c.(c_term) s
      | _ => None
      end
    end

  with rb_susp (d : cbn_fuel) (lvl : nat) (e : cbn_env) (t : term) (s : cbn_state) {struct d}
    : option (term * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match tick s with
      | None => None
      | Some s =>
        cbnlet (ts, s) := map_st (rb_cell d lvl) e.(ev_vals) s in
        Some (subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals) t), s)
      end
    end

  with rb_value (d : cbn_fuel) (lvl : nat) (v : cbn_value) (s : cbn_state) {struct d}
    : option (term * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      let spine h sp s :=
        cbnlet (ts, s) := map_st (rb_cell d lvl) sp s in
        Some (mkApps h ts, s) in
      match v with
      | VCon h sp => spine h sp s
      | VLam e c | VOpen e c => rb_susp d lvl e c.(c_term) s
      | VFix e c i sp | VStuckFix e c i sp =>
        match c.(c_term) with
        | tFix mfix _ =>
          cbnlet (h, s) := rb_susp d lvl e (tFix mfix i) s in
          spine h sp s
        | _ => None
        end
      | VNeu (NVar l) sp => spine (tRel (lvl - S l)) sp s
      | VNeu (NConst h) sp => spine h sp s
      | VStuck e c sp =>
        cbnlet (h, s) := rb_susp d lvl e c.(c_term) s in
        spine h sp s
      end
    end.

  (** *** Universe-checked syntactic comparison *)

  Definition wf_term_univs (t : term) : bool :=
    on_universes (abstract_env_ext_wf_universeb X) closedu t.

  Definition cmp_term (pb : conv_pb) (napp : nat) (t u : term) : bool :=
    wf_term_univs t && wf_term_univs u &&
    eqb_term_upto_univ_napp (abstract_env_compare_universe X) (abstract_env_compare_sort X)
      (compare_global_instance (abstract_env_lookup X) (abstract_env_compare_universe X))
      pb napp t u.

  Definition cmp_sort (pb : conv_pb) (s1 s2 : sort) : bool :=
    abstract_env_ext_wf_sortb X s1 && abstract_env_ext_wf_sortb X s2 &&
    abstract_env_compare_sort X pb s1 s2.

  Definition cmp_level_conv (l1 l2 : Level.t) : bool :=
    let u1 := Universe.make' l1 in
    let u2 := Universe.make' l2 in
    abstract_env_ext_wf_universeb X u1 && abstract_env_ext_wf_universeb X u2 &&
    abstract_env_compare_universe X Conv u1 u2.

  (** *** The comparison: [Some (true, s)] convertible; [Some (false, s)] this rule does not
    apply (try the next one, or "don't know"); [None] give up the whole call. *)

  Fixpoint conv_cell (d : cbn_fuel) (lvl : nat) (le : conv_pb) (a1 a2 : addr) (s : cbn_state)
    {struct d} : option (bool * cbn_state) :=
    if addr_eqb a1 a2 then Some (true, s) else
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      cbnlet (v1, s) := force d a1 s in
      cbnlet (v2, s) := force d a2 s in
      conv_value d lvl le v1 v2 s
    end

  with conv_cells (d : cbn_fuel) (lvl : nat) (l1 l2 : list addr) (s : cbn_state) {struct d}
    : option (bool * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      let fix go l1 l2 s :=
        match l1, l2 with
        | [], [] => Some (true, s)
        | a1 :: l1, a2 :: l2 =>
          cbnwhen s := conv_cell d lvl Conv a1 a2 s in
          go l1 l2 s
        | _, _ => Some (false, s)
        end in
      go l1 l2 s
    end

  with conv_term (d : cbn_fuel) (lvl : nat) (le : conv_pb) (e1 : cbn_env) (c1 : code)
    (e2 : cbn_env) (c2 : code) (s : cbn_state) {struct d} : option (bool * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      cbnlet (v1, s) := whnf d e1 c1 [] s in
      cbnlet (v2, s) := whnf d e2 c2 [] s in
      conv_value d lvl le v1 v2 s
    end

  (** Same code: equal code identifiers, equal [goff] and [nvals], and the environment cells
    free in the code pairwise convertible at [Conv]. *)
  with conv_same_code (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code) (e2 : cbn_env)
    (c2 : code) (s : cbn_state) {struct d} : option (bool * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      if same_code c1 c2 && (e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals))
      then
        let t := c1.(c_term) in
        let fix go i l1 l2 s :=
          match l1, l2 with
          | [], [] => Some (true, s)
          | a1 :: l1, a2 :: l2 =>
            if addr_eqb a1 a2 || noccur_between i 1 t then go (S i) l1 l2 s
            else
              cbnwhen s := conv_cell d lvl Conv a1 a2 s in
              go (S i) l1 l2 s
          | _, _ => Some (false, s)
          end in
        go 0 e1.(ev_vals) e2.(ev_vals) s
      else Some (false, s)
    end

  (** Stuck match congruence (rule table, row "stuck match / stuck match"). *)
  with case_cong (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code) (e2 : cbn_env)
    (c2 : code) (s : cbn_state) {struct d} : option (bool * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match c1.(c_term), c2.(c_term) with
      | tCase ci1 p1 sc1 brs1, tCase ci2 p2 sc2 brs2 =>
        if eqb ci1 ci2 && (#|brs1| == #|brs2|) && (#|p1.(pparams)| == #|p2.(pparams)|)
           && forallb2 cmp_level_conv p1.(puinst) p2.(puinst)
           && case_ctx_ok p1.(pcontext) p2.(pcontext)
        then
          let fix params i l1 l2 s :=
            match l1, l2 with
            | [], [] => Some (true, s)
            | t1 :: l1, t2 :: l2 =>
              cbnwhen s := conv_term d lvl Conv e1 (child c1 (case_param_step i) t1)
                             e2 (child c2 (case_param_step i) t2) s in
              params (N.succ i) l1 l2 s
            | _, _ => Some (false, s)
            end in
          cbnwhen s := params 0%N p1.(pparams) p2.(pparams) s in
          let '(lvlr, er1, er2, s) := push_fresh #|p1.(pcontext)| lvl e1 e2 s in
          cbnwhen s := conv_term d lvlr Conv er1 (child c1 1 p1.(preturn))
                         er2 (child c2 1 p2.(preturn)) s in
          cbnwhen s := conv_term d lvl Conv e1 (child c1 0 sc1) e2 (child c2 0 sc2) s in
          let fix branches i l1 l2 s :=
            match l1, l2 with
            | [], [] => Some (true, s)
            | b1 :: l1, b2 :: l2 =>
              if case_ctx_ok b1.(bcontext) b2.(bcontext) then
                let '(lvlb, eb1, eb2, s) := push_fresh #|b1.(bcontext)| lvl e1 e2 s in
                cbnwhen s := conv_term d lvlb Conv eb1 (child c1 (case_branch_step i) b1.(bbody))
                               eb2 (child c2 (case_branch_step i) b2.(bbody)) s in
                branches (N.succ i) l1 l2 s
              else Some (false, s)
            | _, _ => Some (false, s)
            end in
          branches 0%N brs1 brs2 s
        else Some (false, s)
      | _, _ => Some (false, s)
      end
    end

  (** The rows of the rule table after "same address" and "same code". *)
  with conv_rows (d : cbn_fuel) (lvl : nat) (le : conv_pb) (v1 v2 : cbn_value) (s : cbn_state)
    {struct d} : option (bool * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match v1, v2 with
      | VCon h1 sp1, VCon h2 sp2 =>
        let n := #|sp1| in
        if (n == #|sp2|) && cmp_term le n h1 h2 then conv_cells d lvl sp1 sp2 s
        else Some (false, s)
      | VNeu (NVar l1) sp1, VNeu (NVar l2) sp2 =>
        if l1 == l2 then conv_cells d lvl sp1 sp2 s else Some (false, s)
      | VNeu (NConst h1) sp1, VNeu (NConst h2) sp2 =>
        if cmp_term Conv #|sp1| h1 h2 then conv_cells d lvl sp1 sp2 s else Some (false, s)
      | VLam e1 c1, VLam e2 c2 =>
        match c1.(c_term), c2.(c_term) with
        | tLambda na1 A1 b1, tLambda na2 A2 b2 =>
          if eqb_binder_annot na1 na2 then
            cbnwhen s := conv_term d lvl Conv e1 (child c1 0 A1) e2 (child c2 0 A2) s in
            let (x, s) := alloc (CDone (VNeu (NVar lvl) [])) s in
            conv_term d (S lvl) Conv (env_push x e1) (child c1 1 b1) (env_push x e2)
              (child c2 1 b2) s
          else Some (false, s)
        | _, _ => Some (false, s)
        end
      | VOpen e1 c1, VOpen e2 c2 =>
        match c1.(c_term), c2.(c_term) with
        | tProd na1 A1 B1, tProd na2 A2 B2 =>
          if eqb_binder_annot na1 na2 then
            cbnwhen s := conv_term d lvl Conv e1 (child c1 0 A1) e2 (child c2 0 A2) s in
            let (x, s) := alloc (CDone (VNeu (NVar lvl) [])) s in
            conv_term d (S lvl) le (env_push x e1) (child c1 1 B1) (env_push x e2)
              (child c2 1 B2) s
          else Some (false, s)
        | tSort s1, tSort s2 => Some (cmp_sort le s1 s2, s)
        | tPrim _, tPrim _ =>
          cbnlet (t1, s) := rb_susp d lvl e1 c1.(c_term) s in
          cbnlet (t2, s) := rb_susp d lvl e2 c2.(c_term) s in
          Some (cmp_term Conv 0 t1 t2, s)
        | _, _ => Some (false, s)
        end
      | VStuck e1 c1 sp1, VStuck e2 c2 sp2 =>
        if #|sp1| == #|sp2| then
          cbnlet (b, s) :=
            match c1.(c_term), c2.(c_term) with
            | tCase _ _ _ _, tCase _ _ _ _ => case_cong d lvl e1 c1 e2 c2 s
            | _, _ => Some (false, s)
            end in
          if b then conv_cells d lvl sp1 sp2 s
          else
            cbnlet (t1, s) := rb_susp d lvl e1 c1.(c_term) s in
            cbnlet (t2, s) := rb_susp d lvl e2 c2.(c_term) s in
            if cmp_term Conv #|sp1| t1 t2 then conv_cells d lvl sp1 sp2 s
            else Some (false, s)
        else Some (false, s)
      | VFix e1 c1 i1 sp1, VFix e2 c2 i2 sp2
      | VStuckFix e1 c1 i1 sp1, VStuckFix e2 c2 i2 sp2 =>
        if (i1 == i2) && (#|sp1| == #|sp2|) then
          match c1.(c_term), c2.(c_term) with
          | tFix m1 _, tFix m2 _ =>
            cbnlet (t1, s) := rb_susp d lvl e1 (tFix m1 i1) s in
            cbnlet (t2, s) := rb_susp d lvl e2 (tFix m2 i2) s in
            if cmp_term Conv #|sp1| t1 t2 then conv_cells d lvl sp1 sp2 s
            else Some (false, s)
          | _, _ => Some (false, s)
          end
        else Some (false, s)
      | _, _ => Some (false, s)
      end
    end

  with conv_value (d : cbn_fuel) (lvl : nat) (le : conv_pb) (v1 v2 : cbn_value)
    (s : cbn_state) {struct d} : option (bool * cbn_state) :=
    match d with
    | FO => None
    | FS k =>
      let d := k tt in
      match tick s with
      | None => None
      | Some s =>
        match v1, v2 with
        | VLam e1 c1, VLam e2 c2 | VOpen e1 c1, VOpen e2 c2 =>
          cbnlet (b, s) := conv_same_code d lvl e1 c1 e2 c2 s in
          if b then Some (true, s) else conv_rows d lvl le v1 v2 s
        | VStuck e1 c1 sp1, VStuck e2 c2 sp2 =>
          if #|sp1| == #|sp2| then
            cbnlet (b, s) := conv_same_code d lvl e1 c1 e2 c2 s in
            if b then conv_cells d lvl sp1 sp2 s else conv_rows d lvl le v1 v2 s
          else conv_rows d lvl le v1 v2 s
        | VFix e1 c1 i1 sp1, VFix e2 c2 i2 sp2
        | VStuckFix e1 c1 i1 sp1, VStuckFix e2 c2 i2 sp2 =>
          if (i1 == i2) && (#|sp1| == #|sp2|) then
            cbnlet (b, s) := conv_same_code d lvl e1 c1 e2 c2 s in
            if b then conv_cells d lvl sp1 sp2 s else conv_rows d lvl le v1 v2 s
          else conv_rows d lvl le v1 v2 s
        | _, _ => conv_rows d lvl le v1 v2 s
        end
      end
    end.

  Definition cbn_run (le : conv_pb) (t u : term) : option (bool * cbn_state) :=
    let s := cbn_init in
    let (i1, s) := new_entry (mkEntry t [] (NSInput false)) s in
    let (i2, s) := new_entry (mkEntry u [] (NSInput true)) s in
    conv_term cbn_depth nctx le env_empty (mkCode i1 [] t) env_empty (mkCode i2 [] u) s.

End CallByNeed.

(** [true]: [t] and [u] are convertible at [le] in [Γ]. [false]: don't know. *)
Definition cbn_conv {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
  (le : conv_pb) (Γ : context) (t u : term) : bool :=
  match cbn_run X_type X Γ #|Γ| le t u with
  | Some (true, _) => true
  | _ => false
  end.
