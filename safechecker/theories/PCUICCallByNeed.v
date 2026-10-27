(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import BinPos BinNat.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Utils Require String2pos CanonicalTries ByteCompare.
From MetaRocq.Common Require Import config Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICWfUniverses.
From MetaRocq.SafeChecker Require Import PCUICEqualityDec PCUICWfEnv.

Import CanonicalTries.

(** * Call-by-need conversion fast path (design CN-1.1 of BET-298)

  [cbn_conv le Γ t u] evaluates [t] and [u] with a weak-head call-by-need environment
  machine and compares the weak-head values. [true] means that [t] and [u] are convertible
  at [le]; [false] means "don't know", never "not convertible". [cbn_conv_answer] gives the
  same answer with the reason for a "don't know".

  - Heap: a binary random-access list whose digits are the bits of [st_next] (the number of
    addresses ever allocated), least significant first; a digit 1 at position [j] holds a
    complete tree of [2^j] cells. Heap addresses ([haddr]) are allocation numbers and have
    their own type. A lookup scans the bits of the address against the digits (no
    arithmetic): the cell is in the tree of the highest position where the address has 0
    and the digit is 1, unless a higher position has address 1 and digit 0 (then the
    address is not below [st_next]), and the bits below that position are its path in the
    tree. A cell holds a suspension (environment, code), a value, or a black hole while it
    is forced. Forcing writes the value back.
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
    twice the live count after it and at least [gc_min] (or at every allocation in stress
    mode). The collector copies the cells reachable from the roots and from [st_gam] into a
    fresh heap with new addresses from the old [st_next] on. It does not use the step
    budget. An address that is not in the heap makes the whole call answer "don't know".
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

  No soundness proofs yet: the comparison theorem is the hook obligation in
  [PCUICTypeChecker.convert]. *)

(** ** Keys of the code table, of [st_gam] and of the per-code maps *)

Local Notation key := String2pos.positive.
Local Notation cidx := String2pos.positive. (* code-table index *)

Fixpoint key_succ (p : key) : key :=
  match p with
  | String2pos.xI q => String2pos.xO (key_succ q)
  | String2pos.xO q => String2pos.xI q
  | String2pos.xH => String2pos.xO String2pos.xH
  end.

Fixpoint key_eqb (p q : key) : bool :=
  match p, q with
  | String2pos.xI p, String2pos.xI q => key_eqb p q
  | String2pos.xO p, String2pos.xO q => key_eqb p q
  | String2pos.xH, String2pos.xH => true
  | _, _ => false
  end.

Fixpoint key_of_succ_nat (n : nat) : key :=
  match n with
  | O => String2pos.xH
  | S n => key_succ (key_of_succ_nat n)
  end.

Fixpoint key_of_pos (p : positive) : key :=
  match p with
  | xH => String2pos.xH
  | xO p => String2pos.xO (key_of_pos p)
  | xI p => String2pos.xI (key_of_pos p)
  end.

Definition get2 {A} (k1 k2 : key) (m : PTree.t (PTree.t A)) : option A :=
  match PTree.get k1 m with
  | Some m2 => PTree.get k2 m2
  | None => None
  end.

Definition set2 {A} (k1 k2 : key) (x : A) (m : PTree.t (PTree.t A)) : PTree.t (PTree.t A) :=
  let m2 := match PTree.get k1 m with Some m2 => m2 | None => PTree.empty _ end in
  PTree.set k1 (PTree.set k2 x m2) m.

(** ** Heap addresses *)

Record haddr := HAddr { ha_n : N }.

Definition haddr_eqb (a b : haddr) : bool := N.eqb a.(ha_n) b.(ha_n).

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

(** The collector runs when the cells allocated since the last collection exceed
  [max (2 * live) gc_min]. *)
Definition gc_min : N := 1000000%N.

(** The allocations allowed before the next collection, after a collection that copied
  [live] cells. *)
Definition gc_room (live : N) : N := N.succ (N.max (N.double live) gc_min).

(** ** Results *)

(** Why a call answers "don't know". *)
Inductive cbn_why :=
| WDepth       (* the recursion bound ran out *)
| WSteps       (* the step budget ran out *)
| WDangling    (* a heap read or write at an address that is not in the heap *)
| WBusy        (* a black hole: a cell forced during its own evaluation *)
| WShape       (* a term or value shape the machine does not handle *)
| WCtx         (* a free variable beyond the context *)
| WDelta       (* a constant that is not in the environment *)
| WGcDangling  (* the collector met an address that is not in the heap *)
| WGcFuel      (* the collector's walk ran out of fuel *)
| WRoots.      (* returned roots of an unexpected shape (an internal error) *)

Inductive cbn_res (A : Type) := COk (x : A) | CFail (w : cbn_why).
Arguments COk {A} x.
Arguments CFail {A} w.

Inductive cbn_answer := CbnYes | CbnNoRule | CbnFail (w : cbn_why).

Local Notation "'cbn2' ( x , s ) := c 'in' k" :=
  (match c with COk (x, s) => k | CFail w => CFail w end)
  (at level 200, x ident, s ident, c at level 100, k at level 200, only parsing).

Local Notation "'cbnlet' ( x , r , s ) := c 'in' k" :=
  (match c with COk (x, r, s) => k | CFail w => CFail w end)
  (at level 200, x ident, r ident, s ident, c at level 100, k at level 200, only parsing).

(** [cbnwhen n (r, s) := c in k]: continue with [k] if [c] answers [true]; on [false], answer
  [false] with the roots of [c] less the [n] frames the caller pushed for [c]. *)
Local Notation "'cbnwhen' n ( r , s ) := c 'in' k" :=
  (match c with
   | COk (true, r, s) => k
   | COk (false, r, s) => COk (false, skipn n r, s)
   | CFail w => CFail w end)
  (at level 200, n at level 0, r ident, s ident, c at level 100, k at level 200, only parsing).

(** ** Code table *)

Inductive code_ns :=
| NSInput (right : bool)  (* an input term of the comparison *)
| NSCtx (j : nat)         (* the body of the context entry [j] of [Γ] *)
| NSConst (kn : kername). (* the body of a constant *)

(** [ce_wf]: the result of the [wf_universeb] check of the instantiated term, run once when
  the entry is created. *)
Record code_entry := mkEntry {
  ce_term : term;
  ce_inst : Instance.t;
  ce_ns : code_ns;
  ce_wf : bool }.

(** The term the machine evaluates for an entry: its term with its instance substituted.
  The empty instance leaves the term unchanged (monomorphic bodies have no universe
  variables). *)
Definition inst_code (u : Instance.t) (t : term) : term :=
  match u with
  | [] => t
  | u => subst_instance u t
  end.

(** [c_path] encodes the list of path steps, newest step outermost, each step [k] as the
  Elias-gamma code of [k + 1] (prefix-free, so the encoding is injective). *)
Record code := mkCode {
  c_entry : cidx;
  c_path : key;
  c_term : term }.

Definition path_nil : key := String2pos.xH.

Fixpoint wrap_bits (m : positive) (p : key) (z : nat) : key * nat :=
  match m with
  | xH => (String2pos.xI p, z)
  | xO m => wrap_bits m (String2pos.xO p) (S z)
  | xI m => wrap_bits m (String2pos.xI p) (S z)
  end.

Fixpoint wrap_zeros (z : nat) (p : key) : key :=
  match z with
  | O => p
  | S z => String2pos.xO (wrap_zeros z p)
  end.

Definition path_push (k : N) (p : key) : key :=
  let (q, z) := wrap_bits (N.succ_pos k) p O in wrap_zeros z q.

(** Path steps: [tApp f a]: f 0, a 1; [tLambda]/[tProd]: domain 0, body 1; [tLetIn]: definition
  0, body 2; [tCase]: scrutinee 0, return 1, parameter [i] 2+2i, branch [i] 3+2i; [tProj]: 0;
  [tFix]: body of definition [i] is step [i]. *)
Definition child (c : code) (k : N) (t : term) : code :=
  mkCode c.(c_entry) (path_push k c.(c_path)) t.

Definition case_param_step (i : N) : N := N.add 2 (N.double i).
Definition case_branch_step (i : N) : N := N.add 3 (N.double i).

Definition same_id (c1 c2 : code) : bool :=
  key_eqb c1.(c_entry) c2.(c_entry) && key_eqb c1.(c_path) c2.(c_path).

(** ** Occurrence count and structural hash of a code *)

(** Occurrences of [tRel k], capped at 2: an occurrence under a lambda, product, fixpoint or
  cofixpoint counts 2, match branches take the maximum. Only cost depends on it. *)
Fixpoint occ (k : nat) (t : term) : nat :=
  match t with
  | tRel n => if n == k then 1 else 0
  | tApp f a => Nat.min 2 (occ k f + occ k a)
  | tLambda _ d b | tProd _ d b => Nat.min 2 (occ k d + 2 * occ (S k) b)
  | tLetIn _ b ty body => Nat.min 2 (occ k b + occ k ty + occ (S k) body)
  | tCase _ p c brs =>
    let pp := fold_left (fun n x => n + occ k x) p.(pparams) 0 in
    let pr := occ (k + #|p.(pcontext)|) p.(preturn) in
    let bm := fold_left (fun m b => Nat.max m (occ (k + #|b.(bcontext)|) b.(bbody))) brs 0 in
    Nat.min 2 (pp + pr + occ k c + bm)
  | tProj _ c => occ k c
  | tFix m _ | tCoFix m _ =>
    let n := #|m| in
    if existsb (fun d => negb (occ k d.(dtype) == 0) || negb (occ (k + n) d.(dbody) == 0)) m
    then 2 else 0
  | tEvar _ _ => 2
  | _ => 0
  end.

Definition hmask : N := 2305843009213693951%N. (* 2^61 - 1 *)

Definition hmix (h x : N) : N := N.land (N.add (N.sub (N.shiftl h 5) h) x) hmask.

Fixpoint hash_string (h : N) (s : String.t) : N :=
  match s with
  | String.EmptyString => h
  | String.String b s => hash_string (hmix h (ByteCompare.ByteN.to_N b)) s
  end.

(** A structural hash: equal terms, and terms equal up to universes and names, have equal
  hashes. It is only a filter in front of [eqb_term_upto_univ]. *)
Fixpoint thash (t : term) : N :=
  match t with
  | tRel n => hmix 1 (N.of_nat n)
  | tVar _ => 2%N
  | tEvar n l => fold_left (fun h x => hmix h (thash x)) l (hmix 3 (N.of_nat n))
  | tSort _ => 4%N
  | tProd _ a b => hmix (hmix 5 (thash a)) (thash b)
  | tLambda _ a b => hmix (hmix 6 (thash a)) (thash b)
  | tLetIn _ b ty body => hmix (hmix (hmix 7 (thash b)) (thash ty)) (thash body)
  | tApp f a => hmix (hmix 8 (thash f)) (thash a)
  | tConst kn _ => hash_string 9 (snd kn)
  | tInd i _ => hmix (hash_string 10 (snd i.(inductive_mind))) (N.of_nat i.(inductive_ind))
  | tConstruct i n _ =>
    hmix (hmix (hash_string 11 (snd i.(inductive_mind))) (N.of_nat i.(inductive_ind))) (N.of_nat n)
  | tCase _ p c brs =>
    let h := fold_left (fun h x => hmix h (thash x)) p.(pparams) (hmix 12 (N.of_nat #|brs|)) in
    let h := hmix (hmix h (thash p.(preturn))) (thash c) in
    fold_left (fun h b => hmix h (thash b.(bbody))) brs h
  | tProj p c => hmix (hmix 13 (N.of_nat p.(proj_arg))) (thash c)
  | tFix m i =>
    fold_left (fun h d => hmix (hmix h (thash d.(dtype))) (thash d.(dbody))) m (hmix 14 (N.of_nat i))
  | tCoFix m i =>
    fold_left (fun h d => hmix (hmix h (thash d.(dtype))) (thash d.(dbody))) m (hmix 15 (N.of_nat i))
  | _ => 16%N
  end.

(** ** Machine data *)

(** A slot of an environment: a heap address, or an inline suspension (the fields of an
  environment, and a code). *)
Inductive cbn_slot :=
| SAddr (a : haddr)
| SInl (vals : list cbn_slot) (nvals goff : nat) (c : code).

Record cbn_env := mkEnv {
  ev_vals : list cbn_slot;
  ev_nvals : nat;
  ev_goff : nat }.

Definition env_empty : cbn_env := mkEnv [] 0 0.

Definition env_push (x : cbn_slot) (e : cbn_env) : cbn_env :=
  mkEnv (x :: e.(ev_vals)) (S e.(ev_nvals)) e.(ev_goff).

Definition env_push_addrs (l : list haddr) (e : cbn_env) : cbn_env :=
  fold_left (fun e a => env_push (SAddr a) e) l e.

Inductive cbn_neutral :=
| NVar (lvl : nat)   (* a context variable without a body or a fresh variable, as a level *)
| NConst (h : term). (* an axiom or opaque constant [tConst kn u] *)

Inductive cbn_value :=
| VCon (h : term) (sp : list haddr)                      (* [tConstruct]/[tInd] head *)
| VLam (e : cbn_env) (c : code)                          (* [tLambda] closure *)
| VFix (e : cbn_env) (c : code) (idx : nat) (sp : list haddr)
    (* fixpoint [idx] of the [tFix] code [c], applied to too few arguments *)
| VStuckFix (e : cbn_env) (c : code) (idx : nat) (sp : list haddr)
    (* fixpoint whose recursive argument is neutral or stuck *)
| VNeu (h : cbn_neutral) (sp : list haddr)
| VOpen (e : cbn_env) (c : code)                         (* [tSort], [tProd], [tPrim] *)
| VStuck (e : cbn_env) (c : code) (sp : list haddr).     (* stuck [tCase]/[tProj] *)

Inductive cbn_cell :=
| CSusp (e : cbn_env) (c : code)
| CDone (v : cbn_value)
| CBusy.

(** What a caller holds across a call that can allocate. *)
Inductive root :=
| RA (a : haddr)
| RSl (x : cbn_slot)
| RE (e : cbn_env)
| RV (v : cbn_value)
| RSk (l : list cbn_slot)
| RSp (l : list haddr)
| RC (c : cbn_cell).

Definition spine_of (v : cbn_value) : list haddr :=
  match v with
  | VCon _ sp | VFix _ _ _ sp | VStuckFix _ _ _ sp | VNeu _ sp | VStuck _ _ sp => sp
  | VLam _ _ | VOpen _ _ => []
  end.

Definition add_spine (v : cbn_value) (l : list haddr) : option cbn_value :=
  match v with
  | VCon h sp => Some (VCon h (sp ++ l))
  | VStuckFix e c i sp => Some (VStuckFix e c i (sp ++ l))
  | VNeu h sp => Some (VNeu h (sp ++ l))
  | VStuck e c sp => Some (VStuck e c (sp ++ l))
  | _ => None
  end.

(** ** Renaming: one function per type that holds heap addresses *)

Section Rename.
  Context {G : Type} (f : haddr -> G -> cbn_res (haddr * G)).

  Fixpoint rn_slot (x : cbn_slot) (g : G) {struct x} : cbn_res (cbn_slot * G) :=
    match x with
    | SAddr a => cbn2 (a, g) := f a g in COk (SAddr a, g)
    | SInl vs n o c =>
      let fix go (l : list cbn_slot) (g : G) : cbn_res (list cbn_slot * G) :=
        match l with
        | [] => COk ([], g)
        | y :: l =>
          cbn2 (y, g) := rn_slot y g in
          cbn2 (l, g) := go l g in
          COk (y :: l, g)
        end in
      cbn2 (vs, g) := go vs g in COk (SInl vs n o c, g)
    end.

  Fixpoint rn_slots (l : list cbn_slot) (g : G) : cbn_res (list cbn_slot * G) :=
    match l with
    | [] => COk ([], g)
    | y :: l =>
      cbn2 (y, g) := rn_slot y g in
      cbn2 (l, g) := rn_slots l g in
      COk (y :: l, g)
    end.

  Fixpoint rn_addrs (l : list haddr) (g : G) : cbn_res (list haddr * G) :=
    match l with
    | [] => COk ([], g)
    | a :: l =>
      cbn2 (a, g) := f a g in
      cbn2 (l, g) := rn_addrs l g in
      COk (a :: l, g)
    end.

  Definition rn_env (e : cbn_env) (g : G) : cbn_res (cbn_env * G) :=
    cbn2 (vs, g) := rn_slots e.(ev_vals) g in COk (mkEnv vs e.(ev_nvals) e.(ev_goff), g).

  Definition rn_value (v : cbn_value) (g : G) : cbn_res (cbn_value * G) :=
    match v with
    | VCon h sp => cbn2 (sp, g) := rn_addrs sp g in COk (VCon h sp, g)
    | VLam e c => cbn2 (e, g) := rn_env e g in COk (VLam e c, g)
    | VFix e c i sp =>
      cbn2 (e, g) := rn_env e g in cbn2 (sp, g) := rn_addrs sp g in COk (VFix e c i sp, g)
    | VStuckFix e c i sp =>
      cbn2 (e, g) := rn_env e g in cbn2 (sp, g) := rn_addrs sp g in COk (VStuckFix e c i sp, g)
    | VNeu h sp => cbn2 (sp, g) := rn_addrs sp g in COk (VNeu h sp, g)
    | VOpen e c => cbn2 (e, g) := rn_env e g in COk (VOpen e c, g)
    | VStuck e c sp =>
      cbn2 (e, g) := rn_env e g in cbn2 (sp, g) := rn_addrs sp g in COk (VStuck e c sp, g)
    end.

  Definition rn_cell (cl : cbn_cell) (g : G) : cbn_res (cbn_cell * G) :=
    match cl with
    | CSusp e c => cbn2 (e, g) := rn_env e g in COk (CSusp e c, g)
    | CDone v => cbn2 (v, g) := rn_value v g in COk (CDone v, g)
    | CBusy => COk (CBusy, g)
    end.

  Definition rn_root (r : root) (g : G) : cbn_res (root * G) :=
    match r with
    | RA a => cbn2 (a, g) := f a g in COk (RA a, g)
    | RSl x => cbn2 (x, g) := rn_slot x g in COk (RSl x, g)
    | RE e => cbn2 (e, g) := rn_env e g in COk (RE e, g)
    | RV v => cbn2 (v, g) := rn_value v g in COk (RV v, g)
    | RSk l => cbn2 (l, g) := rn_slots l g in COk (RSk l, g)
    | RSp l => cbn2 (l, g) := rn_addrs l g in COk (RSp l, g)
    | RC c => cbn2 (c, g) := rn_cell c g in COk (RC c, g)
    end.

  Fixpoint rn_roots (l : list root) (g : G) : cbn_res (list root * G) :=
    match l with
    | [] => COk ([], g)
    | r :: l =>
      cbn2 (r, g) := rn_root r g in
      cbn2 (l, g) := rn_roots l g in
      COk (r :: l, g)
    end.

  (** The values of [st_gam]. *)
  Fixpoint rn_tree' (m : PTree.tree' haddr) (g : G) : cbn_res (PTree.tree' haddr * G) :=
    match m with
    | PTree.Node001 r => cbn2 (r, g) := rn_tree' r g in COk (PTree.Node001 r, g)
    | PTree.Node010 x => cbn2 (x, g) := f x g in COk (PTree.Node010 x, g)
    | PTree.Node011 x r =>
      cbn2 (x, g) := f x g in cbn2 (r, g) := rn_tree' r g in COk (PTree.Node011 x r, g)
    | PTree.Node100 l => cbn2 (l, g) := rn_tree' l g in COk (PTree.Node100 l, g)
    | PTree.Node101 l r =>
      cbn2 (l, g) := rn_tree' l g in cbn2 (r, g) := rn_tree' r g in COk (PTree.Node101 l r, g)
    | PTree.Node110 l x =>
      cbn2 (l, g) := rn_tree' l g in cbn2 (x, g) := f x g in COk (PTree.Node110 l x, g)
    | PTree.Node111 l x r =>
      cbn2 (l, g) := rn_tree' l g in cbn2 (x, g) := f x g in cbn2 (r, g) := rn_tree' r g in
      COk (PTree.Node111 l x r, g)
    end.

  Definition rn_ptree (m : PTree.t haddr) (g : G) : cbn_res (PTree.t haddr * G) :=
    match m with
    | PTree.Empty => COk (PTree.Empty, g)
    | PTree.Nodes m => cbn2 (m, g) := rn_tree' m g in COk (PTree.Nodes m, g)
    end.
End Rename.

(** ** The heap: a binary random-access list indexed by the bits of the address *)

(** A complete binary tree of depth [j]: [BNode l r] splits on the bit [j - 1] of the
  allocation number (0 left, 1 right). [BEmpty] stands for a subtree of cells that a
  collection dropped. *)
Inductive btree (A : Type) :=
| BLeaf (x : A)
| BNode (l r : btree A)
| BEmpty.
Arguments BLeaf {A} x.
Arguments BNode {A} l r.
Arguments BEmpty {A}.

Inductive digit (A : Type) :=
| DZero
| DOne (t : btree A).
Arguments DZero {A}.
Arguments DOne {A} t.

(** The digits of the number of allocated addresses, least significant first. *)
Definition bheap (A : Type) := list (digit A).

(** Insert a tree of depth [j] at position [j] (the carry of a binary increment). The tree
  already at a position holds the older cells, so it goes left. *)
Fixpoint bh_carry {A} (t : btree A) (h : bheap A) : bheap A :=
  match h with
  | [] => [DOne t]
  | DZero :: h => DOne t :: h
  | DOne t' :: h => DZero :: bh_carry (BNode t' t) h
  end.

Definition bh_cons {A} (x : A) (h : bheap A) : bheap A := bh_carry (BLeaf x) h.

(** The heap of [n] dropped addresses: the digits of [n], each tree [BEmpty]. *)
Fixpoint bh_holes_pos {A} (p : positive) : bheap A :=
  match p with
  | xH => [DOne BEmpty]
  | xO p => DZero :: bh_holes_pos p
  | xI p => DOne BEmpty :: bh_holes_pos p
  end.

Definition bh_holes {A} (n : N) : bheap A :=
  match n with
  | N0 => []
  | Npos p => bh_holes_pos p
  end.

(** A path in a tree, top split first. *)
Inductive bpath := PEnd | PL (q : bpath) | PR (q : bpath).

(** The scan, from the current position up: [acc] is the path of the bits below it (the
  latest first), [cand] the tree and path of the cell if the bits from here on are equal
  to the digits. Beyond the address's highest bit 1 ([bh_top]) its bits are 0. *)
Fixpoint bh_top {A} (h : bheap A) (acc : bpath) (cand : option (btree A * bpath))
  : option (btree A * bpath) :=
  match h with
  | [] => cand
  | DZero :: h => bh_top h (PL acc) cand
  | DOne t :: h => bh_top h (PL acc) (Some (t, acc))
  end.

Fixpoint bh_scan {A} (p : positive) (h : bheap A) (acc : bpath)
  (cand : option (btree A * bpath)) : option (btree A * bpath) :=
  match p, h with
  | _, [] => None
  | xH, DZero :: h => bh_top h (PR acc) None
  | xH, DOne _ :: h => bh_top h (PR acc) cand
  | xO p, DZero :: h => bh_scan p h (PL acc) cand
  | xO p, DOne t :: h => bh_scan p h (PL acc) (Some (t, acc))
  | xI p, DZero :: h => bh_scan p h (PR acc) None
  | xI p, DOne _ :: h => bh_scan p h (PR acc) cand
  end.

(** The tree that holds the cell of address [a] and the cell's path in it; [None] unless
  [a] is below the number of addresses that [h] encodes. *)
Definition bh_find {A} (a : N) (h : bheap A) : option (btree A * bpath) :=
  match a with
  | N0 => bh_top h PEnd None
  | Npos p => bh_scan p h PEnd None
  end.

Fixpoint bt_get {A} (q : bpath) (t : btree A) : option A :=
  match q, t with
  | PEnd, BLeaf x => Some x
  | PL q, BNode l _ => bt_get q l
  | PR q, BNode _ r => bt_get q r
  | _, _ => None
  end.

Fixpoint bt_set {A} (q : bpath) (x : A) (t : btree A) : option (btree A) :=
  match q, t with
  | PEnd, BLeaf _ => Some (BLeaf x)
  | PL q, BNode l r => option_map (fun l => BNode l r) (bt_set q x l)
  | PR q, BNode l r => option_map (fun r => BNode l r) (bt_set q x r)
  | _, _ => None
  end.

(** Replace the tree at the position given by the length of [q]. *)
Fixpoint bh_put {A} (q : bpath) (t : btree A) (h : bheap A) : option (bheap A) :=
  match q, h with
  | PEnd, DOne _ :: h => Some (DOne t :: h)
  | (PL q | PR q), d :: h => option_map (cons d) (bh_put q t h)
  | _, _ => None
  end.

Definition bh_get {A} (a : haddr) (h : bheap A) : option A :=
  match bh_find a.(ha_n) h with
  | Some (t, q) => bt_get q t
  | None => None
  end.

Definition bh_upd {A} (a : haddr) (x : A) (h : bheap A) : option (bheap A) :=
  match bh_find a.(ha_n) h with
  | Some (t, q) =>
    match bt_set q x t with
    | Some t => bh_put q t h
    | None => None
    end
  | None => None
  end.

(** ** State *)

Inductive delta_memo :=
| DAxiom
| DBody (body : term) (insts : list (Instance.t * cidx * term)).

(** Per-call data that holds no heap address. *)
Record cbn_memo := mkMemo {
  m_codes : PTree.t code_entry;
  m_ncode : cidx;
  m_delta : KernameMap.t delta_memo;
  m_once : PTree.t (PTree.t bool);  (* (index, path) of a binder's body: occurs at most once *)
  m_hash : PTree.t (PTree.t N);     (* (index, path): structural hash of the code *)
  m_ceq : PTree.t (PTree.t (PTree.t (PTree.t bool))) }. (* code equality of two identifiers *)

Record cbn_state := mkState {
  st_heap : bheap cbn_cell;
  st_next : N;               (* the next heap address *)
  st_room : N;               (* allocations left before the next collection *)
  st_steps : N;
  st_gam : PTree.t haddr;    (* the cell of a context entry, by [key_of_succ_nat j] *)
  st_memo : cbn_memo }.

Definition memo_empty : cbn_memo :=
  mkMemo (PTree.empty _) String2pos.xH (KernameMap.empty _) (PTree.empty _) (PTree.empty _)
    (PTree.empty _).

Definition cbn_init : cbn_state :=
  mkState [] N0 (gc_room 0) cbn_steps (PTree.empty _) memo_empty.

Definition tick (s : cbn_state) : option cbn_state :=
  match s.(st_steps) with
  | N0 => None
  | n => Some (mkState s.(st_heap) s.(st_next) s.(st_room) (N.pred n) s.(st_gam) s.(st_memo))
  end.

Definition heap_get (a : haddr) (s : cbn_state) : option cbn_cell :=
  bh_get a s.(st_heap).

Definition heap_upd (a : haddr) (c : cbn_cell) (s : cbn_state) : option cbn_state :=
  option_map (fun h => mkState h s.(st_next) s.(st_room) s.(st_steps) s.(st_gam) s.(st_memo))
    (bh_upd a c s.(st_heap)).

Definition alloc_now (c : cbn_cell) (s : cbn_state) : haddr * cbn_state :=
  (HAddr s.(st_next),
   mkState (bh_cons c s.(st_heap)) (N.succ s.(st_next)) (N.pred s.(st_room)) s.(st_steps)
     s.(st_gam) s.(st_memo)).

Definition set_memo (m : cbn_memo) (s : cbn_state) : cbn_state :=
  mkState s.(st_heap) s.(st_next) s.(st_room) s.(st_steps) s.(st_gam) m.

Definition set_gam (g : PTree.t haddr) (s : cbn_state) : cbn_state :=
  mkState s.(st_heap) s.(st_next) s.(st_room) s.(st_steps) g s.(st_memo).

Definition memo_add_entry (e : code_entry) (m : cbn_memo) : cidx * cbn_memo :=
  let i := m.(m_ncode) in
  (i, mkMemo (PTree.set i e m.(m_codes)) (key_succ i) m.(m_delta) m.(m_once) m.(m_hash)
        m.(m_ceq)).

Definition memo_set_delta (d : KernameMap.t delta_memo) (m : cbn_memo) : cbn_memo :=
  mkMemo m.(m_codes) m.(m_ncode) d m.(m_once) m.(m_hash) m.(m_ceq).

Definition memo_set_once (o : PTree.t (PTree.t bool)) (m : cbn_memo) : cbn_memo :=
  mkMemo m.(m_codes) m.(m_ncode) m.(m_delta) o m.(m_hash) m.(m_ceq).

Definition memo_set_hash (h : PTree.t (PTree.t N)) (m : cbn_memo) : cbn_memo :=
  mkMemo m.(m_codes) m.(m_ncode) m.(m_delta) m.(m_once) h m.(m_ceq).

Definition memo_set_ceq (q : PTree.t (PTree.t (PTree.t (PTree.t bool)))) (m : cbn_memo)
  : cbn_memo :=
  mkMemo m.(m_codes) m.(m_ncode) m.(m_delta) m.(m_once) m.(m_hash) q.

(** ** The collector *)

Record gc_state := mkGc {
  g_fwd : PTree.t haddr;    (* old address (as a key) to new address *)
  g_heap : bheap cbn_cell;  (* the new heap *)
  g_next : N }.             (* its next address *)

Definition key_of_N (n : N) : key :=
  match n with
  | N0 => String2pos.xH
  | Npos p => String2pos.xO (key_of_pos p)
  end.

(** Copy the cell at [a] of the old heap [old] and the cells it reaches, children first;
  give it the next new address. [f] bounds the depth of the walk: [st_next + 1] units, more
  than the number of cells, so a heap without cycles is never cut off. *)
Fixpoint gc_copy (old : bheap cbn_cell) (f : cbn_fuel) (a : haddr) (g : gc_state)
  {struct f} : cbn_res (haddr * gc_state) :=
  match PTree.get (key_of_N a.(ha_n)) g.(g_fwd) with
  | Some a' => COk (a', g)
  | None =>
    match f with
    | FO => CFail WGcFuel
    | FS k =>
      match bh_get a old with
      | None => CFail WGcDangling
      | Some cl =>
        cbn2 (cl, g) := rn_cell (gc_copy old (k tt)) cl g in
        let a' := HAddr g.(g_next) in
        COk (a', mkGc (PTree.set (key_of_N a.(ha_n)) a' g.(g_fwd)) (bh_cons cl g.(g_heap))
                   (N.succ g.(g_next)))
      end
    end
  end.

(** Copy what [rs] and [st_gam] reach into a fresh heap whose addresses start at the old
  [st_next] (the addresses below are dropped), and rename [rs] and [st_gam]. No step is
  taken from the budget. *)
Definition collect (rs : list root) (s : cbn_state) : cbn_res (list root * cbn_state) :=
  let old := s.(st_heap) in
  let onext := s.(st_next) in
  let copy := gc_copy old (fuel_of_pos (N.succ_pos onext) (fun _ => FO)) in
  let g := mkGc (PTree.empty _) (bh_holes onext) onext in
  cbn2 (gm, g) := rn_ptree copy s.(st_gam) g in
  cbn2 (rs, g) := rn_roots copy rs g in
  COk (rs, mkState g.(g_heap) g.(g_next) (gc_room (N.sub g.(g_next) onext)) s.(st_steps) gm
             s.(st_memo)).

Definition gc_due (stress : bool) (s : cbn_state) : bool :=
  stress || match s.(st_room) with N0 => true | Npos _ => false end.

Fixpoint find_inst (u : Instance.t) (l : list (Instance.t * cidx * term)) : option (cidx * term) :=
  match l with
  | [] => None
  | (u', i, t) :: l => if Instance.eqb u u' then Some (i, t) else find_inst u l
  end.

Definition is_assum (d : context_decl) : bool :=
  match d.(decl_body) with None => true | Some _ => false end.

(** Contexts of a match related by [eq_context_upto_names], without let-ins. *)
Definition case_ctx_ok (ctx1 ctx2 : context) : bool :=
  forallb2 (fun d1 d2 => is_assum d1 && is_assum d2 && eqb_decl_upto_names d1 d2) ctx1 ctx2.

Fixpoint list_set {A} (l : list A) (n : nat) (x : A) : list A :=
  match l, n with
  | [], _ => []
  | _ :: l, O => x :: l
  | y :: l, S n => y :: list_set l n x
  end.

Section CallByNeed.
  Context {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1).
  Context (Γ : context) (nctx : nat). (* nctx = #|Γ| *)
  Context (stress : bool). (* collect at every allocation *)

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

  (** *** Code entries, the per-code maps and the same-code test *)

  Definition new_entry (t : term) (u : Instance.t) (ns : code_ns) (s : cbn_state)
    : code * cbn_state :=
    let ct := inst_code u t in
    let (i, m) := memo_add_entry (mkEntry t u ns (wf_term_univs ct)) s.(st_memo) in
    (mkCode i path_nil ct, set_memo m s).

  Definition entry_wf (i : cidx) (s : cbn_state) : bool :=
    match PTree.get i s.(st_memo).(m_codes) with
    | Some e => e.(ce_wf)
    | None => false
    end.

  (** Whether the variable of the binder over the body [c] occurs at most once in it. *)
  Definition once_body (c : code) (s : cbn_state) : bool * cbn_state :=
    match get2 c.(c_entry) c.(c_path) s.(st_memo).(m_once) with
    | Some b => (b, s)
    | None =>
      let b := Nat.leb (occ 0 c.(c_term)) 1 in
      (b, set_memo (memo_set_once (set2 c.(c_entry) c.(c_path) b s.(st_memo).(m_once))
                      s.(st_memo)) s)
    end.

  Definition code_hash (c : code) (s : cbn_state) : N * cbn_state :=
    match get2 c.(c_entry) c.(c_path) s.(st_memo).(m_hash) with
    | Some h => (h, s)
    | None =>
      let h := thash c.(c_term) in
      (h, set_memo (memo_set_hash (set2 c.(c_entry) c.(c_path) h s.(st_memo).(m_hash))
                      s.(st_memo)) s)
    end.

  Definition ceq_get (c1 c2 : code) (s : cbn_state) : option bool :=
    match get2 c1.(c_entry) c1.(c_path) s.(st_memo).(m_ceq) with
    | Some m => get2 c2.(c_entry) c2.(c_path) m
    | None => None
    end.

  Definition ceq_set (c1 c2 : code) (b : bool) (s : cbn_state) : cbn_state :=
    let q := s.(st_memo).(m_ceq) in
    let m := match get2 c1.(c_entry) c1.(c_path) q with Some m => m | None => PTree.empty _ end in
    set_memo (memo_set_ceq (set2 c1.(c_entry) c1.(c_path) (set2 c2.(c_entry) c2.(c_path) b m) q)
                s.(st_memo)) s.

  (** Code equality: equal identifiers; or both entries passed their universe check, the
    hashes are equal, and [eqb_term_upto_univ] at [Conv] (cached by identifier pair). *)
  Definition code_eq (c1 c2 : code) (s : cbn_state) : bool * cbn_state :=
    if same_id c1 c2 then (true, s)
    else if negb (entry_wf c1.(c_entry) s && entry_wf c2.(c_entry) s) then (false, s)
    else
      let (h1, s) := code_hash c1 s in
      let (h2, s) := code_hash c2 s in
      if negb (N.eqb h1 h2) then (false, s)
      else
        match ceq_get c1 c2 s with
        | Some b => (b, s)
        | None =>
          let b := eqb_term_upto_univ (abstract_env_compare_universe X)
                     (abstract_env_compare_sort X)
                     (compare_global_instance (abstract_env_lookup X)
                        (abstract_env_compare_universe X))
                     Conv c1.(c_term) c2.(c_term) in
          (b, ceq_set c1 c2 b s)
        end.

  (** *** Allocation, which may collect first *)

  Definition alloc (cl : cbn_cell) (rs : list root) (s : cbn_state)
    : cbn_res (haddr * list root * cbn_state) :=
    if gc_due stress s then
      match collect (RC cl :: rs) s with
      | COk (RC cl :: rs, s) => let (a, s) := alloc_now cl s in COk (a, rs, s)
      | COk _ => CFail WRoots
      | CFail w => CFail w
      end
    else let (a, s) := alloc_now cl s in COk (a, rs, s).

  (** *** Delta, with the memo of this call *)

  Definition delta_new (kn : kername) (u : Instance.t) (body : term)
    (insts : list (Instance.t * cidx * term)) (s : cbn_state) : code * cbn_state :=
    let (c, s) := new_entry body u (NSConst kn) s in
    (c, set_memo (memo_set_delta (KernameMap.add kn (DBody body ((u, c.(c_entry), c.(c_term)) :: insts))
                                    s.(st_memo).(m_delta)) s.(st_memo)) s).

  (** [Some c]: the instantiated body; [None]: an axiom or opaque constant. *)
  Definition delta (kn : kername) (u : Instance.t) (s : cbn_state)
    : cbn_res (option code * cbn_state) :=
    match KernameMap.find kn s.(st_memo).(m_delta) with
    | Some DAxiom => COk (None, s)
    | Some (DBody body insts) =>
      match find_inst u insts with
      | Some (i, t) => COk (Some (mkCode i path_nil t), s)
      | None => let (c, s) := delta_new kn u body insts s in COk (Some c, s)
      end
    | None =>
      match abstract_env_lookup X kn with
      | Some (ConstantDecl cb) =>
        match cb.(cst_body) with
        | Some body => let (c, s) := delta_new kn u body [] s in COk (Some c, s)
        | None =>
          COk (None, set_memo (memo_set_delta (KernameMap.add kn DAxiom s.(st_memo).(m_delta))
                                 s.(st_memo)) s)
        end
      | _ => CFail WDelta
      end
    end.

  (** *** Context entries: one cell per entry of [Γ], made on first use *)

  Definition gam (j : nat) (rs : list root) (s : cbn_state)
    : cbn_res (haddr * list root * cbn_state) :=
    let k := key_of_succ_nat j in
    match PTree.get k s.(st_gam) with
    | Some a => COk (a, rs, s)
    | None =>
      match nth_error Γ j with
      | None => CFail WCtx
      | Some decl =>
        let (cl, s) :=
          match decl.(decl_body) with
          | Some b =>
            let (c, s) := new_entry b [] (NSCtx j) s in
            (CSusp (mkEnv [] 0 (S j)) c, s)
          | None => (CDone (VNeu (NVar (nctx - S j)) []), s)
          end in
        cbnlet (a, rs, s) := alloc cl rs s in
        COk (a, rs, set_gam (PTree.set k a s.(st_gam)) s)
      end
    end.

  Definition env_var (n : nat) (e : cbn_env) (rs : list root) (s : cbn_state)
    : cbn_res (cbn_slot * list root * cbn_state) :=
    match nth_error e.(ev_vals) n with
    | Some x => COk (x, rs, s)
    | None =>
      cbnlet (a, rs, s) := gam (n - e.(ev_nvals) + e.(ev_goff)) rs s in COk (SAddr a, rs, s)
    end.

  (** The slot of an argument (of an application or a let): a variable reuses its slot;
    anything else is an inline suspension until it is bound or stored. *)
  Definition arg_slot (e : cbn_env) (c : code) (rs : list root) (s : cbn_state)
    : cbn_res (cbn_slot * list root * cbn_state) :=
    match c.(c_term) with
    | tRel n => env_var n e rs s
    | _ => COk (SInl e.(ev_vals) e.(ev_nvals) e.(ev_goff) c, rs, s)
    end.

  (** Put a slot in the heap: lambdas, fixpoints, sorts, products, primitives and bodiless
    constants as value cells, anything else as a suspension. *)
  Definition materialize (x : cbn_slot) (rs : list root) (s : cbn_state)
    : cbn_res (haddr * list root * cbn_state) :=
    match x with
    | SAddr a => COk (a, rs, s)
    | SInl vs n o c =>
      let e := mkEnv vs n o in
      match c.(c_term) with
      | tLambda _ _ _ => alloc (CDone (VLam e c)) rs s
      | tFix mfix idx =>
        match nth_error mfix idx with
        | Some _ => alloc (CDone (VFix e c idx [])) rs s
        | None => alloc (CSusp e c) rs s
        end
      | tSort _ | tProd _ _ _ | tPrim _ => alloc (CDone (VOpen e c)) rs s
      | tConst kn u =>
        match delta kn u s with
        | COk (None, s) => alloc (CDone (VNeu (NConst c.(c_term)) [])) rs s
        | COk (Some _, s) => alloc (CSusp e c) rs s
        | CFail _ => alloc (CSusp e c) rs s
        end
      | _ => alloc (CSusp e c) rs s
      end
    end.

  (** Bind a slot to the binder over the body [body]: an inline suspension stays inline if
    the variable occurs at most once in [body], and is put in the heap otherwise. *)
  Definition bind (x : cbn_slot) (body : code) (rs : list root) (s : cbn_state)
    : cbn_res (cbn_slot * list root * cbn_state) :=
    match x with
    | SAddr _ => COk (x, rs, s)
    | SInl _ _ _ _ =>
      let (once, s) := once_body body s in
      if once then COk (x, rs, s)
      else cbnlet (a, rs, s) := materialize x rs s in COk (SAddr a, rs, s)
    end.

  (** Put every slot of a stack in the heap (a stack that becomes a value's spine). *)
  Fixpoint mat_all (d : cbn_fuel) (l : list cbn_slot) (rs : list root) (s : cbn_state)
    {struct d} : cbn_res (list haddr * list root * cbn_state) :=
    match l with
    | [] => COk ([], rs, s)
    | x :: l =>
      match d with
      | FO => CFail WDepth
      | FS k =>
        cbnlet (a, rs, s) := materialize x (RSk l :: rs) s in
        match rs with
        | RSk l :: rs =>
          cbnlet (al, rs, s) := mat_all (k tt) l (RA a :: rs) s in
          match rs with
          | RA a :: rs => COk (a :: al, rs, s)
          | _ => CFail WRoots
          end
        | _ => CFail WRoots
        end
      end
    end.

  (** Allocate the cells of the [n] fixpoints of the [tFix] code [c] over [e] and push them on
    [acc], fixpoint 0 first, so that [tRel 0] is fixpoint [n-1] as in [fix_subst]. *)
  Fixpoint push_fix_cells (e : cbn_env) (c : code) (i n : nat) (acc : cbn_env)
    (rs : list root) (s : cbn_state) : cbn_res (cbn_env * list root * cbn_state) :=
    match n with
    | O => COk (acc, rs, s)
    | S n =>
      cbnlet (a, rs, s) := alloc (CDone (VFix e c i [])) (RE e :: RE acc :: rs) s in
      match rs with
      | RE e :: RE acc :: rs => push_fix_cells e c (S i) n (env_push (SAddr a) acc) rs s
      | _ => CFail WRoots
      end
    end.

  (** Push [n] fresh variables, levels [lvl] to [lvl + n - 1], on both environments. *)
  Fixpoint push_fresh (n lvl : nat) (e1 e2 : cbn_env) (rs : list root) (s : cbn_state)
    : cbn_res ((nat * cbn_env * cbn_env) * list root * cbn_state) :=
    match n with
    | O => COk ((lvl, e1, e2), rs, s)
    | S n =>
      cbnlet (x, rs, s) := alloc (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s in
      match rs with
      | RE e1 :: RE e2 :: rs =>
        push_fresh n (S lvl) (env_push (SAddr x) e1) (env_push (SAddr x) e2) rs s
      | _ => CFail WRoots
      end
    end.

  (** *** The machine *)

  Fixpoint force (d : cbn_fuel) (a : haddr) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (cbn_value * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match heap_get a s with
      | Some (CDone v) => COk (v, rs, s)
      | Some (CSusp e c) =>
        match heap_upd a CBusy s with
        | None => CFail WDangling
        | Some s =>
          cbnlet (v, rs, s) := whnf d e c [] (RA a :: rs) s in
          match rs with
          | RA a :: rs =>
            match heap_upd a (CDone v) s with
            | Some s => COk (v, rs, s)
            | None => CFail WDangling
            end
          | _ => CFail WRoots
          end
        end
      | Some CBusy => CFail WBusy
      | None => CFail WDangling
      end
    end

  (** Evaluate a slot applied to [stk]: an address is forced, an inline suspension is
    evaluated in place (no write-back). *)
  with eval_slot (d : cbn_fuel) (x : cbn_slot) (stk : list cbn_slot) (rs : list root)
    (s : cbn_state) {struct d} : cbn_res (cbn_value * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match x with
      | SAddr a =>
        cbnlet (v, rs, s) := force d a (RSk stk :: rs) s in
        match rs with
        | RSk stk :: rs => apply d v stk rs s
        | _ => CFail WRoots
        end
      | SInl vs n o c => whnf d (mkEnv vs n o) c stk rs s
      end
    end

  with whnf (d : cbn_fuel) (e : cbn_env) (c : code) (stk : list cbn_slot) (rs : list root)
    (s : cbn_state) {struct d} : cbn_res (cbn_value * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match tick s with
      | None => CFail WSteps
      | Some s =>
      match c.(c_term) with
      | tRel n =>
        cbnlet (x, rs, s) := env_var n e (RSk stk :: rs) s in
        match rs with
        | RSk stk :: rs => eval_slot d x stk rs s
        | _ => CFail WRoots
        end
      | tApp f arg =>
        cbnlet (x, rs, s) := arg_slot e (child c 1 arg) (RE e :: RSk stk :: rs) s in
        match rs with
        | RE e :: RSk stk :: rs => whnf d e (child c 0 f) (x :: stk) rs s
        | _ => CFail WRoots
        end
      | tLambda _ _ b =>
        match stk with
        | x :: stk =>
          let cb := child c 1 b in
          cbnlet (x, rs, s) := bind x cb (RE e :: RSk stk :: rs) s in
          match rs with
          | RE e :: RSk stk :: rs => whnf d (env_push x e) cb stk rs s
          | _ => CFail WRoots
          end
        | [] => COk (VLam e c, rs, s)
        end
      | tLetIn _ b _ body =>
        let cb := child c 2 body in
        cbnlet (x, rs, s) := arg_slot e (child c 0 b) (RE e :: RSk stk :: rs) s in
        match rs with
        | RE e :: RSk stk :: rs =>
          cbnlet (x, rs, s) := bind x cb (RE e :: RSk stk :: rs) s in
          match rs with
          | RE e :: RSk stk :: rs => whnf d (env_push x e) cb stk rs s
          | _ => CFail WRoots
          end
        | _ => CFail WRoots
        end
      | tConst kn u =>
        cbn2 (r, s) := delta kn u s in
        match r with
        | Some c' => whnf d env_empty c' stk rs s
        | None =>
          cbnlet (sp, rs, s) := mat_all d stk rs s in COk (VNeu (NConst c.(c_term)) sp, rs, s)
        end
      | tConstruct _ _ _ | tInd _ _ =>
        cbnlet (sp, rs, s) := mat_all d stk rs s in COk (VCon c.(c_term) sp, rs, s)
      | tCase ci p scrut brs =>
        cbnlet (v, rs, s) := whnf d e (child c 0 scrut) [] (RE e :: RSk stk :: rs) s in
        match rs with
        | RE e :: RSk stk :: rs =>
          match v with
          | VCon (tConstruct ind n _) args =>
            if eqb ind ci.(ci_ind) then
              match nth_error brs n with
              | Some br =>
                let cargs := skipn ci.(ci_npar) args in
                if forallb is_assum br.(bcontext) && (#|cargs| == #|br.(bcontext)|) then
                  whnf d (env_push_addrs cargs e)
                    (child c (case_branch_step (N.of_nat n)) br.(bbody)) stk rs s
                else CFail WShape
              | None => CFail WShape
              end
            else CFail WShape
          | VNeu _ _ | VStuck _ _ _ | VStuckFix _ _ _ _ =>
            cbnlet (sp, rs, s) := mat_all d stk (RE e :: rs) s in
            match rs with
            | RE e :: rs => COk (VStuck e c sp, rs, s)
            | _ => CFail WRoots
            end
          | _ => CFail WShape
          end
        | _ => CFail WRoots
        end
      | tProj p arg =>
        cbnlet (v, rs, s) := whnf d e (child c 0 arg) [] (RE e :: RSk stk :: rs) s in
        match rs with
        | RE e :: RSk stk :: rs =>
          match v with
          | VCon (tConstruct ind 0 _) args =>
            if eqb ind p.(proj_ind) then
              match nth_error args (p.(proj_npars) + p.(proj_arg)) with
              | Some a => eval_slot d (SAddr a) stk rs s
              | None => CFail WShape
              end
            else CFail WShape
          | VNeu _ _ | VStuck _ _ _ | VStuckFix _ _ _ _ =>
            cbnlet (sp, rs, s) := mat_all d stk (RE e :: rs) s in
            match rs with
            | RE e :: rs => COk (VStuck e c sp, rs, s)
            | _ => CFail WRoots
            end
          | _ => CFail WShape
          end
        | _ => CFail WRoots
        end
      | tFix mfix idx => whnf_fix d e c mfix idx stk rs s
      | tSort _ | tProd _ _ _ | tPrim _ =>
        match stk with
        | [] => COk (VOpen e c, rs, s)
        | _ => CFail WShape
        end
      | _ => CFail WShape
      end
      end
    end

  with whnf_fix (d : cbn_fuel) (e : cbn_env) (c : code) (mfix : mfixpoint term) (idx : nat)
    (stk : list cbn_slot) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (cbn_value * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match nth_error mfix idx with
      | None => CFail WShape
      | Some def =>
        match nth_error stk def.(rarg) with
        | None =>
          cbnlet (sp, rs, s) := mat_all d stk (RE e :: rs) s in
          match rs with
          | RE e :: rs => COk (VFix e c idx sp, rs, s)
          | _ => CFail WRoots
          end
        | Some x =>
          cbnlet (a, rs, s) := materialize x (RE e :: RSk stk :: rs) s in
          match rs with
          | RE e :: RSk stk :: rs =>
            let stk := list_set stk def.(rarg) (SAddr a) in
            cbnlet (v, rs, s) := force d a (RE e :: RSk stk :: rs) s in
            match rs with
            | RE e :: RSk stk :: rs =>
              match v with
              | VCon (tConstruct _ _ _) _ =>
                cbnlet (e', rs, s) := push_fix_cells e c 0 #|mfix| e (RSk stk :: rs) s in
                match rs with
                | RSk stk :: rs => whnf d e' (child c (N.of_nat idx) def.(dbody)) stk rs s
                | _ => CFail WRoots
                end
              | VNeu _ _ | VStuck _ _ _ | VStuckFix _ _ _ _ =>
                cbnlet (sp, rs, s) := mat_all d stk (RE e :: rs) s in
                match rs with
                | RE e :: rs => COk (VStuckFix e c idx sp, rs, s)
                | _ => CFail WRoots
                end
              | _ => CFail WShape
              end
            | _ => CFail WRoots
            end
          | _ => CFail WRoots
          end
        end
      end
    end

  with apply (d : cbn_fuel) (v : cbn_value) (stk : list cbn_slot) (rs : list root)
    (s : cbn_state) {struct d} : cbn_res (cbn_value * list root * cbn_state) :=
    match stk with
    | [] => COk (v, rs, s)
    | _ =>
      match d with
      | FO => CFail WDepth
      | FS k =>
        let d := k tt in
        match v with
        | VLam e c =>
          match c.(c_term), stk with
          | tLambda _ _ b, x :: stk =>
            let cb := child c 1 b in
            cbnlet (x, rs, s) := bind x cb (RE e :: RSk stk :: rs) s in
            match rs with
            | RE e :: RSk stk :: rs => whnf d (env_push x e) cb stk rs s
            | _ => CFail WRoots
            end
          | _, _ => CFail WShape
          end
        | VFix e c idx args =>
          match c.(c_term) with
          | tFix mfix _ => whnf_fix d e c mfix idx (map SAddr args ++ stk) rs s
          | _ => CFail WShape
          end
        | VOpen _ _ => CFail WShape
        | VCon _ _ | VStuckFix _ _ _ _ | VNeu _ _ | VStuck _ _ _ =>
          cbnlet (sp, rs, s) := mat_all d stk (RV v :: rs) s in
          match rs with
          | RV v :: rs =>
            match add_spine v sp with
            | Some v => COk (v, rs, s)
            | None => CFail WShape
            end
          | _ => CFail WRoots
          end
        end
      end
    end.

  (** *** Read-back to a term in [Γ] extended by [lvl - nctx] fresh variables (no
    allocation) *)

  Fixpoint map_st {A B S} (f : A -> S -> cbn_res (B * S)) (l : list A) (s : S)
    : cbn_res (list B * S) :=
    match l with
    | [] => COk ([], s)
    | x :: l =>
      cbn2 (y, s) := f x s in
      cbn2 (ys, s) := map_st f l s in
      COk (y :: ys, s)
    end.

  Fixpoint rb_cell (d : cbn_fuel) (lvl : nat) (a : haddr) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match heap_get a s with
      | Some (CDone v) => rb_value d lvl v s
      | Some (CSusp e c) => rb_susp d lvl e c.(c_term) s
      | Some CBusy => CFail WBusy
      | None => CFail WDangling
      end
    end

  with rb_slot (d : cbn_fuel) (lvl : nat) (x : cbn_slot) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match x with
      | SAddr a => rb_cell d lvl a s
      | SInl vs n o c => rb_susp d lvl (mkEnv vs n o) c.(c_term) s
      end
    end

  with rb_susp (d : cbn_fuel) (lvl : nat) (e : cbn_env) (t : term) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match tick s with
      | None => CFail WSteps
      | Some s =>
        cbn2 (ts, s) := map_st (rb_slot d lvl) e.(ev_vals) s in
        COk (subst ts 0 (lift (lvl - nctx + e.(ev_goff)) e.(ev_nvals) t), s)
      end
    end

  with rb_value (d : cbn_fuel) (lvl : nat) (v : cbn_value) (s : cbn_state) {struct d}
    : cbn_res (term * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      let spine h sp s :=
        cbn2 (ts, s) := map_st (rb_cell d lvl) sp s in
        COk (mkApps h ts, s) in
      match v with
      | VCon h sp => spine h sp s
      | VLam e c | VOpen e c => rb_susp d lvl e c.(c_term) s
      | VFix e c i sp | VStuckFix e c i sp =>
        match c.(c_term) with
        | tFix mfix _ =>
          cbn2 (h, s) := rb_susp d lvl e (tFix mfix i) s in
          spine h sp s
        | _ => CFail WShape
        end
      | VNeu (NVar l) sp => spine (tRel (lvl - S l)) sp s
      | VNeu (NConst h) sp => spine h sp s
      | VStuck e c sp =>
        cbn2 (h, s) := rb_susp d lvl e c.(c_term) s in
        spine h sp s
      end
    end.

  (** *** The comparison: [COk (true, rs, s)] convertible; [COk (false, rs, s)] this rule does
    not apply (try the next one, or "don't know"); [CFail w] give up the whole call. *)

  Definition slot_same (x1 x2 : cbn_slot) : bool :=
    match x1, x2 with
    | SAddr a1, SAddr a2 => haddr_eqb a1 a2
    | _, _ => false
    end.

  Fixpoint conv_slot (d : cbn_fuel) (lvl : nat) (le : conv_pb) (x1 x2 : cbn_slot)
    (rs : list root) (s : cbn_state) {struct d} : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match x1, x2 with
      | SAddr a1, SAddr a2 =>
        if haddr_eqb a1 a2 then COk (true, rs, s) else conv_eval d lvl le x1 x2 rs s
      | SInl vs1 n1 o1 c1, SInl vs2 n2 o2 c2 =>
        cbnlet (b, rs, s) := conv_same_code d lvl (mkEnv vs1 n1 o1) c1 (mkEnv vs2 n2 o2) c2
                               (RSl x1 :: RSl x2 :: rs) s in
        match rs with
        | RSl x1 :: RSl x2 :: rs =>
          if b then COk (true, rs, s) else conv_eval d lvl le x1 x2 rs s
        | _ => CFail WRoots
        end
      | _, _ => conv_eval d lvl le x1 x2 rs s
      end
    end

  with conv_eval (d : cbn_fuel) (lvl : nat) (le : conv_pb) (x1 x2 : cbn_slot)
    (rs : list root) (s : cbn_state) {struct d} : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      cbnlet (v1, rs, s) := eval_slot d x1 [] (RSl x2 :: rs) s in
      match rs with
      | RSl x2 :: rs =>
        cbnlet (v2, rs, s) := eval_slot d x2 [] (RV v1 :: rs) s in
        match rs with
        | RV v1 :: rs => conv_value d lvl le v1 v2 rs s
        | _ => CFail WRoots
        end
      | _ => CFail WRoots
      end
    end

  (** Spines pairwise at [Conv]. *)
  with conv_cells (d : cbn_fuel) (lvl : nat) (l1 l2 : list haddr) (rs : list root)
    (s : cbn_state) {struct d} : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => COk (true, rs, s)
      | a1 :: l1, a2 :: l2 =>
        cbnwhen 2 (rs, s) := conv_slot d lvl Conv (SAddr a1) (SAddr a2) (RSp l1 :: RSp l2 :: rs) s in
        match rs with
        | RSp l1 :: RSp l2 :: rs => conv_cells d lvl l1 l2 rs s
        | _ => CFail WRoots
        end
      | _, _ => COk (false, rs, s)
      end
    end

  with conv_term (d : cbn_fuel) (lvl : nat) (le : conv_pb) (e1 : cbn_env) (c1 : code)
    (e2 : cbn_env) (c2 : code) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      cbnlet (v1, rs, s) := whnf d e1 c1 [] (RE e2 :: rs) s in
      match rs with
      | RE e2 :: rs =>
        cbnlet (v2, rs, s) := whnf d e2 c2 [] (RV v1 :: rs) s in
        match rs with
        | RV v1 :: rs => conv_value d lvl le v1 v2 rs s
        | _ => CFail WRoots
        end
      | _ => CFail WRoots
      end
    end

  (** Same code: equal [goff] and [nvals], equal codes ([code_eq]), and the environment
    slots free in the code pairwise convertible at [Conv]. *)
  with conv_same_code (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code) (e2 : cbn_env)
    (c2 : code) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      if (e1.(ev_goff) == e2.(ev_goff)) && (e1.(ev_nvals) == e2.(ev_nvals)) then
        let (b, s) := code_eq c1 c2 s in
        if b then same_code_cells d lvl c1.(c_term) 0 e1.(ev_vals) e2.(ev_vals) rs s
        else COk (false, rs, s)
      else COk (false, rs, s)
    end

  with same_code_cells (d : cbn_fuel) (lvl : nat) (t : term) (i : nat)
    (l1 l2 : list cbn_slot) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => COk (true, rs, s)
      | x1 :: l1, x2 :: l2 =>
        if slot_same x1 x2 || noccur_between i 1 t then same_code_cells d lvl t (S i) l1 l2 rs s
        else
          cbnwhen 2 (rs, s) := conv_slot d lvl Conv x1 x2 (RSk l1 :: RSk l2 :: rs) s in
          match rs with
          | RSk l1 :: RSk l2 :: rs => same_code_cells d lvl t (S i) l1 l2 rs s
          | _ => CFail WRoots
          end
      | _, _ => COk (false, rs, s)
      end
    end

  (** Stuck match congruence (rule table, row "stuck match / stuck match"). *)
  with case_cong (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code) (e2 : cbn_env)
    (c2 : code) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match c1.(c_term), c2.(c_term) with
      | tCase ci1 p1 sc1 brs1, tCase ci2 p2 sc2 brs2 =>
        if eqb ci1 ci2 && (#|brs1| == #|brs2|) && (#|p1.(pparams)| == #|p2.(pparams)|)
           && forallb2 cmp_level_conv p1.(puinst) p2.(puinst)
           && case_ctx_ok p1.(pcontext) p2.(pcontext)
        then
          cbnwhen 2 (rs, s) := case_params d lvl e1 c1 e2 c2 0%N p1.(pparams) p2.(pparams)
                               (RE e1 :: RE e2 :: rs) s in
          match rs with
          | RE e1 :: RE e2 :: rs =>
            cbnlet (r, rs, s) := push_fresh #|p1.(pcontext)| lvl e1 e2 (RE e1 :: RE e2 :: rs) s in
            let '(lvlr, er1, er2) := r in
            cbnwhen 2 (rs, s) := conv_term d lvlr Conv er1 (child c1 1 p1.(preturn))
                                 er2 (child c2 1 p2.(preturn)) rs s in
            match rs with
            | RE e1 :: RE e2 :: rs =>
              cbnwhen 2 (rs, s) := conv_term d lvl Conv e1 (child c1 0 sc1) e2 (child c2 0 sc2)
                                   (RE e1 :: RE e2 :: rs) s in
              match rs with
              | RE e1 :: RE e2 :: rs => case_branches d lvl e1 c1 e2 c2 0%N brs1 brs2 rs s
              | _ => CFail WRoots
              end
            | _ => CFail WRoots
            end
          | _ => CFail WRoots
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end
    end

  with case_params (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code) (e2 : cbn_env)
    (c2 : code) (i : N) (l1 l2 : list term) (rs : list root) (s : cbn_state) {struct d}
    : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => COk (true, rs, s)
      | t1 :: l1, t2 :: l2 =>
        cbnwhen 2 (rs, s) := conv_term d lvl Conv e1 (child c1 (case_param_step i) t1)
                             e2 (child c2 (case_param_step i) t2) (RE e1 :: RE e2 :: rs) s in
        match rs with
        | RE e1 :: RE e2 :: rs => case_params d lvl e1 c1 e2 c2 (N.succ i) l1 l2 rs s
        | _ => CFail WRoots
        end
      | _, _ => COk (false, rs, s)
      end
    end

  with case_branches (d : cbn_fuel) (lvl : nat) (e1 : cbn_env) (c1 : code) (e2 : cbn_env)
    (c2 : code) (i : N) (l1 l2 : list (branch term)) (rs : list root) (s : cbn_state)
    {struct d} : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match l1, l2 with
      | [], [] => COk (true, rs, s)
      | b1 :: l1, b2 :: l2 =>
        if case_ctx_ok b1.(bcontext) b2.(bcontext) then
          cbnlet (r, rs, s) := push_fresh #|b1.(bcontext)| lvl e1 e2 (RE e1 :: RE e2 :: rs) s in
          let '(lvlb, eb1, eb2) := r in
          cbnwhen 2 (rs, s) := conv_term d lvlb Conv eb1 (child c1 (case_branch_step i) b1.(bbody))
                               eb2 (child c2 (case_branch_step i) b2.(bbody)) rs s in
          match rs with
          | RE e1 :: RE e2 :: rs => case_branches d lvl e1 c1 e2 c2 (N.succ i) l1 l2 rs s
          | _ => CFail WRoots
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end
    end

  (** The rows of the rule table after "same address" and "same code". *)
  with conv_rows (d : cbn_fuel) (lvl : nat) (le : conv_pb) (v1 v2 : cbn_value)
    (rs : list root) (s : cbn_state) {struct d} : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match v1, v2 with
      | VCon h1 sp1, VCon h2 sp2 =>
        let n := #|sp1| in
        if (n == #|sp2|) && cmp_term le n h1 h2 then conv_cells d lvl sp1 sp2 rs s
        else COk (false, rs, s)
      | VNeu (NVar l1) sp1, VNeu (NVar l2) sp2 =>
        if l1 == l2 then conv_cells d lvl sp1 sp2 rs s else COk (false, rs, s)
      | VNeu (NConst h1) sp1, VNeu (NConst h2) sp2 =>
        if cmp_term Conv #|sp1| h1 h2 then conv_cells d lvl sp1 sp2 rs s else COk (false, rs, s)
      | VLam e1 c1, VLam e2 c2 =>
        match c1.(c_term), c2.(c_term) with
        | tLambda na1 A1 b1, tLambda na2 A2 b2 =>
          if eqb_binder_annot na1 na2 then
            cbnwhen 2 (rs, s) := conv_term d lvl Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
                                 (RE e1 :: RE e2 :: rs) s in
            match rs with
            | RE e1 :: RE e2 :: rs =>
              cbnlet (x, rs, s) := alloc (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s in
              match rs with
              | RE e1 :: RE e2 :: rs =>
                conv_term d (S lvl) Conv (env_push (SAddr x) e1) (child c1 1 b1)
                  (env_push (SAddr x) e2) (child c2 1 b2) rs s
              | _ => CFail WRoots
              end
            | _ => CFail WRoots
            end
          else COk (false, rs, s)
        | _, _ => COk (false, rs, s)
        end
      | VOpen e1 c1, VOpen e2 c2 =>
        match c1.(c_term), c2.(c_term) with
        | tProd na1 A1 B1, tProd na2 A2 B2 =>
          if eqb_binder_annot na1 na2 then
            cbnwhen 2 (rs, s) := conv_term d lvl Conv e1 (child c1 0 A1) e2 (child c2 0 A2)
                                 (RE e1 :: RE e2 :: rs) s in
            match rs with
            | RE e1 :: RE e2 :: rs =>
              cbnlet (x, rs, s) := alloc (CDone (VNeu (NVar lvl) [])) (RE e1 :: RE e2 :: rs) s in
              match rs with
              | RE e1 :: RE e2 :: rs =>
                conv_term d (S lvl) le (env_push (SAddr x) e1) (child c1 1 B1)
                  (env_push (SAddr x) e2) (child c2 1 B2) rs s
              | _ => CFail WRoots
              end
            | _ => CFail WRoots
            end
          else COk (false, rs, s)
        | tSort s1, tSort s2 => COk (cmp_sort le s1 s2, rs, s)
        | tPrim _, tPrim _ =>
          cbn2 (t1, s) := rb_susp d lvl e1 c1.(c_term) s in
          cbn2 (t2, s) := rb_susp d lvl e2 c2.(c_term) s in
          COk (cmp_term Conv 0 t1 t2, rs, s)
        | _, _ => COk (false, rs, s)
        end
      | VStuck e1 c1 sp1, VStuck e2 c2 sp2 =>
        if #|sp1| == #|sp2| then
          cbnlet (b, rs, s) :=
            match c1.(c_term), c2.(c_term) with
            | tCase _ _ _ _, tCase _ _ _ _ => case_cong d lvl e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s
            | _, _ => COk (false, RV v1 :: RV v2 :: rs, s)
            end in
          match rs with
          | RV (VStuck e1 c1 sp1) :: RV (VStuck e2 c2 sp2) :: rs =>
            if b then conv_cells d lvl sp1 sp2 rs s
            else
              cbn2 (t1, s) := rb_susp d lvl e1 c1.(c_term) s in
              cbn2 (t2, s) := rb_susp d lvl e2 c2.(c_term) s in
              if cmp_term Conv #|sp1| t1 t2 then conv_cells d lvl sp1 sp2 rs s
              else COk (false, rs, s)
          | _ => CFail WRoots
          end
        else COk (false, rs, s)
      | VFix e1 c1 i1 sp1, VFix e2 c2 i2 sp2
      | VStuckFix e1 c1 i1 sp1, VStuckFix e2 c2 i2 sp2 =>
        if (i1 == i2) && (#|sp1| == #|sp2|) then
          match c1.(c_term), c2.(c_term) with
          | tFix m1 _, tFix m2 _ =>
            cbn2 (t1, s) := rb_susp d lvl e1 (tFix m1 i1) s in
            cbn2 (t2, s) := rb_susp d lvl e2 (tFix m2 i2) s in
            if cmp_term Conv #|sp1| t1 t2 then conv_cells d lvl sp1 sp2 rs s
            else COk (false, rs, s)
          | _, _ => COk (false, rs, s)
          end
        else COk (false, rs, s)
      | _, _ => COk (false, rs, s)
      end
    end

  (** Same code first for closures, stuck terms and fixpoints, then the rows. The values are
    roots across the same-code test, for the fallback. *)
  with conv_value (d : cbn_fuel) (lvl : nat) (le : conv_pb) (v1 v2 : cbn_value)
    (rs : list root) (s : cbn_state) {struct d} : cbn_res (bool * list root * cbn_state) :=
    match d with
    | FO => CFail WDepth
    | FS k =>
      let d := k tt in
      match tick s with
      | None => CFail WSteps
      | Some s =>
        let same e1 c1 e2 c2 (spines : bool) :=
          cbnlet (b, rs, s) := conv_same_code d lvl e1 c1 e2 c2 (RV v1 :: RV v2 :: rs) s in
          match rs with
          | RV v1 :: RV v2 :: rs =>
            if b then
              if spines then conv_cells d lvl (spine_of v1) (spine_of v2) rs s
              else COk (true, rs, s)
            else conv_rows d lvl le v1 v2 rs s
          | _ => CFail WRoots
          end in
        match v1, v2 with
        | VLam e1 c1, VLam e2 c2 | VOpen e1 c1, VOpen e2 c2 => same e1 c1 e2 c2 false
        | VStuck e1 c1 sp1, VStuck e2 c2 sp2 =>
          if #|sp1| == #|sp2| then same e1 c1 e2 c2 true else conv_rows d lvl le v1 v2 rs s
        | VFix e1 c1 i1 sp1, VFix e2 c2 i2 sp2
        | VStuckFix e1 c1 i1 sp1, VStuckFix e2 c2 i2 sp2 =>
          if (i1 == i2) && (#|sp1| == #|sp2|) then same e1 c1 e2 c2 true
          else conv_rows d lvl le v1 v2 rs s
        | _, _ => conv_rows d lvl le v1 v2 rs s
        end
      end
    end.

  Definition cbn_run (le : conv_pb) (t u : term) : cbn_answer :=
    let s := cbn_init in
    let (c1, s) := new_entry t [] (NSInput false) s in
    let (c2, s) := new_entry u [] (NSInput true) s in
    match conv_term cbn_depth nctx le env_empty c1 env_empty c2 [] s with
    | COk (true, _, _) => CbnYes
    | COk (false, _, _) => CbnNoRule
    | CFail w => CbnFail w
    end.

End CallByNeed.

(** The answer of the fast path, with the reason for a "don't know". [stress] collects at
  every allocation (for the measurement harness only); the answer must not depend on it. *)
Definition cbn_conv_answer {cf : checker_flags} (X_type : abstract_env_impl)
  (X : X_type.π2.π1) (stress : bool) (le : conv_pb) (Γ : context) (t u : term) : cbn_answer :=
  cbn_run X_type X Γ #|Γ| stress le t u.

(** [true]: [t] and [u] are convertible at [le] in [Γ]. [false]: don't know. *)
Definition cbn_conv {cf : checker_flags} (X_type : abstract_env_impl) (X : X_type.π2.π1)
  (le : conv_pb) (Γ : context) (t u : term) : bool :=
  match cbn_conv_answer X_type X false le Γ t u with
  | CbnYes => true
  | _ => false
  end.
