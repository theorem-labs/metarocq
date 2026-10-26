(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment Kernames.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive.

From Stdlib Require Import ssreflect ssrbool.

Local Open Scope bs_scope.
Set Default Goal Selector "!".

(** * Recursive-argument trees

  The guard checker of the Rocq kernel reads, for each inductive block, data
  that PCUIC does not store in its environment:

  - [mind_recargs]: for each inductive of the block, a regular tree saying
    which constructor arguments are recursive (labels [recarg]);
  - [mind_nparams_rec]: the number of recursive (uniform) parameters.

  This file computes both from a PCUIC [mutual_inductive_body], as the kernel
  does when it declares the block (port of [compute_rec_par],
  [ienv_push_var], [ienv_push_inductive], [ienv_decompose_prod],
  [check_positivity_one] and [check_positivity], kernel/indtypes.ml), and
  ports the guard-time approximation of these trees
  ([check_inductive_codomain], [abstract_mind_lc], [get_recargs_approx],
  [has_constant_parameters], kernel/inductive.ml).

  Everything here is a total executable function:

  - Every function whose kernel counterpart recurses on an unbounded or
    infinite structure takes a [fuel : nat].  The fuel is an exponent: a fuel
    of [k] allows [2 ^ k] nested steps through the doubling combinator
    [dfuel], so a large fuel never builds a large unary number.  Exhaustion
    is the answer [RtFuel], distinct from a failure [RtBad].
  - Where the kernel raises an exception (an anomaly, an assertion, an array
    bound, or a positivity/well-formedness error), the result is [RtBad].
    The positivity checks themselves are not ported: a block of a
    well-formed PCUIC environment is already positive, and the kernel
    computes the same trees with its positivity checks turned off
    ([chkpos = false]).
  - Everything the kernel does with [whd_all env c] on a type is done with a
    reducer parameter [whd : term -> red_answer] that treats every [tRel] as
    an opaque variable.  The only local definitions the block computation
    introduces are the [let] parameters of the block; they are unfolded
    here ([whd_in]), so [whd] never needs a local context. *)

(** ** Doubling fuel

  [dfuel step n k] is [step] iterated [2 ^ n] times in depth around the
  continuation [k]: the [rec] argument of the outermost [step] is the
  [(2 ^ n - 1)]-fold iterate.  The inner continuation is kept eta-expanded,
  so only the levels a computation reaches are unfolded. *)
Section DFuel.
  Context {A : Type} {B : A -> Type}.
  Context (step : (forall a, B a) -> forall a, B a).

  Fixpoint dfuel (n : nat) (k : forall a, B a) : forall a, B a :=
    match n with
    | 0 => fun a => step k a
    | S n => fun a => dfuel n (fun a' => dfuel n k a') a
    end.
End DFuel.

Definition nfuel {X Y : Type} (step : (X -> Y) -> X -> Y) (n : nat) (k : X -> Y) : X -> Y :=
  @dfuel X (fun _ => Y) step n k.

(** ** Answers *)

Inductive rt_answer (X : Type) : Type :=
| RtOk (x : X)
| RtBad (msg : string)
| RtFuel.
Arguments RtOk {X} x.
Arguments RtBad {X} msg.
Arguments RtFuel {X}.

Definition rt_bind {X Y} (m : rt_answer X) (f : X -> rt_answer Y) : rt_answer Y :=
  match m with
  | RtOk x => f x
  | RtBad msg => RtBad msg
  | RtFuel => RtFuel
  end.

Local Notation "x <-? m ;; f" := (rt_bind m (fun x => f))
  (at level 100, m at next level, right associativity).

Definition rt_of_option {X} (msg : string) (o : option X) : rt_answer X :=
  match o with
  | Some x => RtOk x
  | None => RtBad msg
  end.

Fixpoint rt_map_list {X Y} (f : X -> rt_answer Y) (l : list X) : rt_answer (list Y) :=
  match l with
  | [] => RtOk []
  | x :: l => y <-? f x ;; ys <-? rt_map_list f l ;; RtOk (y :: ys)
  end.

(** [Array.map2]: lengths must agree. *)
Definition rt_map2 {X Y Z} (f : X -> Y -> rt_answer Z) (l : list X) (l' : list Y)
  : rt_answer (list Z) :=
  if negb (Nat.eqb #|l| #|l'|) then RtBad "Array.map2: lengths differ" else
  let fix go (l : list X) (l' : list Y) {struct l} : rt_answer (list Z) :=
    match l, l' with
    | x :: l, y :: l' => z <-? f x y ;; zs <-? go l l' ;; RtOk (z :: zs)
    | _, _ => RtOk []
    end in
  go l l'.

(** [Array.for_all2]: lengths must agree; stops at the first [false]. *)
Definition rt_forall2 {X Y} (f : X -> Y -> rt_answer bool) (l : list X) (l' : list Y)
  : rt_answer bool :=
  if negb (Nat.eqb #|l| #|l'|) then RtBad "Array.for_all2: lengths differ" else
  let fix go (l : list X) (l' : list Y) {struct l} : rt_answer bool :=
    match l, l' with
    | x :: l, y :: l' => b <-? f x y ;; if b then go l l' else RtOk false
    | _, _ => RtOk true
    end in
  go l l'.

(** [Array.exists]: stops at the first [true]. *)
Fixpoint rt_exists {X} (f : X -> rt_answer bool) (l : list X) : rt_answer bool :=
  match l with
  | [] => RtOk false
  | x :: l => b <-? f x ;; if b then RtOk true else rt_exists f l
  end.

(** ** Regular trees (port of kernel/rtree.ml)

  - [RVar i j] is the [j]-th tree introduced at depth [i] (both from 0);
  - [RNode lab sons] is a node, with a list of lists of sons (for a
    recursive-argument tree: one list per constructor, one son per
    constructor argument);
  - [RRec j defs] is the [j]-th of the mutually recursive trees [defs], in
    which the variables [RVar 0 k] stand for [RRec k defs].

  The kernel represents the unfolding of [Rec] with closures and explicit
  substitutions ([Esubst]) for speed; here the unfolding substitutes
  directly ([rt_subst_rec]), which gives the same trees. *)

#[warnings="-register-all"]
Inductive rtree (A : Type) : Type :=
| RVar (i j : nat)
| RNode (lab : A) (sons : list (list (rtree A)))
| RRec (j : nat) (defs : list (rtree A)).
Arguments RVar {A} i j.
Arguments RNode {A} lab sons.
Arguments RRec {A} j defs.

Section RTree.
  Context {A : Type}.
  Implicit Types (t : rtree A) (fuel : nat).

  (** [lift_rtree_rec] *)
  Fixpoint rt_lift_rec (depth n : nat) (t : rtree A) : rtree A :=
    match t with
    | RVar i j => if Nat.ltb i depth then RVar i j else RVar (i + n) j
    | RNode l sons => RNode l (map (map (rt_lift_rec depth n)) sons)
    | RRec j defs => RRec j (map (rt_lift_rec (S depth) n) defs)
    end.

  (** [lift] *)
  Definition rt_lift (n : nat) (t : rtree A) : rtree A :=
    if Nat.eqb n 0 then t else rt_lift_rec 0 n t.

  (** [mk_rec_calls] *)
  Definition rt_mk_rec_calls (i : nat) : list (rtree A) :=
    map (fun j => RVar 0 j) (seq 0 i).

  (** Substitute [RRec k defs] (lifted by [depth]) for the variables [RVar
      depth k] of [t], and lower the variables bound outside. *)
  Fixpoint rt_subst_rec (depth : nat) (defs : list (rtree A)) (t : rtree A) : rtree A :=
    match t with
    | RVar i j =>
      if Nat.ltb i depth then RVar i j
      else if Nat.eqb i depth then RRec j (map (rt_lift_rec 1 depth) defs)
      else RVar (i - 1) j
    | RNode l sons => RNode l (map (map (rt_subst_rec depth defs)) sons)
    | RRec j ds => RRec j (map (rt_subst_rec (S depth) defs) ds)
    end.

  (** [expand]: unfold the head [Rec]s until a node or a free variable. *)
  Definition rt_expand_step (rec : rtree A -> rt_answer (rtree A)) (t : rtree A)
    : rt_answer (rtree A) :=
    match t with
    | RRec j defs =>
      match nth_error defs j with
      | Some d => rec (rt_subst_rec 0 defs d)
      | None => RtBad "Rtree.expand: index out of bounds"
      end
    | _ => RtOk t
    end.

  Definition rt_expand fuel (t : rtree A) : rt_answer (rtree A) :=
    nfuel rt_expand_step fuel (fun _ => RtFuel) t.

  (** [mk_rec]: the mutually recursive trees with bodies [defs], after the
      kernel's check that every body introduces a node or a parameter (so
      that the expansion terminates): following [RVar 0 j] chains from a
      body must not come back to an already visited body ("invalid rec
      call").  The chain visits distinct bodies, so [S #|defs|] steps
      suffice. *)
  Definition rt_mk_rec fuel (defs : list (rtree A)) : rt_answer (list (rtree A)) :=
    let fix check (n : nat) (histo : list nat) (d : rtree A) {struct n} : rt_answer unit :=
      match n with
      | 0 => RtBad "Rtree.mk_rec: invalid rec call"
      | S n =>
        e <-? rt_expand fuel d ;;
        match e with
        | RVar 0 j =>
          if existsb (Nat.eqb j) histo then RtBad "Rtree.mk_rec: invalid rec call"
          else match nth_error defs j with
               | Some dj => check n (j :: histo) dj
               | None => RtBad "Rtree.mk_rec: index out of bounds"
               end
        | _ => RtOk tt
        end
      end in
    let fix go (i : nat) (ds : list (rtree A)) {struct ds} : rt_answer (list (rtree A)) :=
      match ds with
      | [] => RtOk []
      | d :: ds =>
        ok <-? check (S #|defs|) [i] d ;;
        rs <-? go (S i) ds ;;
        RtOk (RRec i defs :: rs)
      end in
    go 0 defs.

  (** [dest_node], [dest_head], [is_node] *)
  Definition rt_dest_node fuel t : rt_answer (A * list (list (rtree A))) :=
    e <-? rt_expand fuel t ;;
    match e with
    | RNode l sons => RtOk (l, sons)
    | _ => RtBad "Rtree.dest_node"
    end.

  Definition rt_dest_head fuel t : rt_answer A :=
    e <-? rt_expand fuel t ;;
    match e with
    | RNode l _ => RtOk l
    | _ => RtBad "Rtree.dest_head"
    end.

  Definition rt_is_node fuel t : rt_answer bool :=
    e <-? rt_expand fuel t ;;
    match e with
    | RNode _ _ => RtOk true
    | _ => RtOk false
    end.

  (** [raw_eq]: structural equality. *)
  Fixpoint rt_raw_eq (cmp : A -> A -> bool) (t t' : rtree A) {struct t} : bool :=
    match t, t' with
    | RVar i j, RVar i' j' => Nat.eqb i i' && Nat.eqb j j'
    | RNode x a, RNode x' a' => cmp x x' && forallb2 (forallb2 (rt_raw_eq cmp)) a a'
    | RRec i a, RRec i' a' => Nat.eqb i i' && forallb2 (rt_raw_eq cmp) a a'
    | _, _ => false
    end.

  Definition rt_raw_eq2 (cmp : A -> A -> bool) (p q : rtree A * rtree A) : bool :=
    rt_raw_eq cmp p.1 q.1 && rt_raw_eq cmp p.2 q.2.

  (** [equiv]: equivalence of the expanded trees, with the history of the
      pairs already visited ([cmp] compares labels when searching the
      history, [cmp'] when comparing nodes). *)
  Definition rt_equiv_step (cmp cmp' : A -> A -> bool) fuel
    (rec : list (rtree A * rtree A) * (rtree A * rtree A) -> rt_answer bool)
    (x : list (rtree A * rtree A) * (rtree A * rtree A)) : rt_answer bool :=
    let '(histo, tt') := x in
    if existsb (rt_raw_eq2 cmp tt') histo then RtOk true else
    e <-? rt_expand fuel tt'.1 ;;
    e' <-? rt_expand fuel tt'.2 ;;
    match e, e' with
    | RNode l v, RNode l' v' =>
      if cmp' l l' && Nat.eqb #|v| #|v'| then
        rt_forall2 (fun s s' => rt_forall2 (fun u u' => rec (tt' :: histo, (u, u'))) s s') v v'
      else RtOk false
    | _, _ => RtOk false
    end.

  Definition rt_equiv (cmp cmp' : A -> A -> bool) fuel (t t' : rtree A) : rt_answer bool :=
    nfuel (rt_equiv_step cmp cmp' fuel) fuel (fun _ => RtFuel) ([], (t, t')).

  (** [equal]: structural equality first, then the equivalence. *)
  Definition rt_equal (cmp : A -> A -> bool) fuel (t t' : rtree A) : rt_answer bool :=
    if rt_raw_eq cmp t t' then RtOk true else rt_equiv cmp cmp fuel t t'.

  (** [inter]: the meet of two trees of the same arity.  [interlbl] meets
      two labels ([None]: no common label, the result is the leaf [def]).
      The history maps an already visited pair to the [Rec] it built, as a
      pair (depth, index). *)
  Definition rt_inter_req : Type :=
    (nat * list ((rtree A * rtree A) * (nat * nat)) * (rtree A * rtree A))%type.

  Definition rt_inter_step (cmp : A -> A -> bool) (interlbl : A -> A -> option A) (def : A) fuel
    (rec : rt_inter_req -> rt_answer (rtree A)) (x : rt_inter_req) : rt_answer (rtree A) :=
    let '(n, histo, (t, t')) := x in
    match find (fun h => rt_raw_eq2 cmp (t, t') h.1) histo with
    | Some (_, (i, j)) => RtOk (RVar (n - i - 1) j)
    | None =>
      match t, t' with
      | RVar i j, RVar i' j' =>
        if Nat.eqb i i' && Nat.eqb j j' then RtOk t else RtBad "Rtree.inter: assertion failed"
      | RNode l a, RNode l' a' =>
        match interlbl l l' with
        | None => RtOk (RNode def [])
        | Some l'' =>
          sons <-? rt_map2 (fun s s' => rt_map2 (fun u u' => rec (n, histo, (u, u'))) s s') a a' ;;
          RtOk (RNode l'' sons)
        end
      | RRec i v, RRec i' v' =>
        (* If possible, preserve the shape of the input trees; otherwise
           mutually recursive trees become nested ones. *)
        if Nat.eqb i i' && Nat.eqb #|v| #|v'| then
          let histo := ((t, t'), (n, i)) :: histo in
          defs <-? rt_map2 (fun u u' => rec (S n, histo, (u, u'))) v v' ;;
          RtOk (RRec i defs)
        else
          let histo := ((t, t'), (n, 0)) :: histo in
          e <-? rt_expand fuel t ;;
          e' <-? rt_expand fuel t' ;;
          r <-? rec (S n, histo, (e, e')) ;;
          RtOk (RRec 0 [r])
      | RRec _ _, _ => e <-? rt_expand fuel t ;; rec (n, histo, (e, t'))
      | _, RRec _ _ => e' <-? rt_expand fuel t' ;; rec (n, histo, (t, e'))
      | _, _ => RtBad "Rtree.inter: assertion failed"
      end
    end.

  Definition rt_inter (cmp : A -> A -> bool) (interlbl : A -> A -> option A) (def : A) fuel
    (t t' : rtree A) : rt_answer (rtree A) :=
    nfuel (rt_inter_step cmp interlbl def fuel) fuel (fun _ => RtFuel) (0, [], (t, t')).

  (** [incl] *)
  Definition rt_incl (cmp : A -> A -> bool) (interlbl : A -> A -> option A) (def : A) fuel
    (t t' : rtree A) : rt_answer bool :=
    r <-? rt_inter cmp interlbl def fuel t t' ;;
    rt_equal cmp fuel t r.

  (** [is_infinite]: whether the expanded tree has an infinite branch. *)
  Definition rt_is_infinite_step (cmp : A -> A -> bool) fuel
    (rec : list (rtree A) * rtree A -> rt_answer bool) (x : list (rtree A) * rtree A)
    : rt_answer bool :=
    let '(histo, t) := x in
    if existsb (rt_raw_eq cmp t) histo then RtOk true else
    e <-? rt_expand fuel t ;;
    match e with
    | RNode _ v => rt_exists (rt_exists (fun u => rec (t :: histo, u))) v
    | _ => RtOk false
    end.

  Definition rt_is_infinite (cmp : A -> A -> bool) fuel (t : rtree A) : rt_answer bool :=
    nfuel (rt_is_infinite_step cmp fuel) fuel (fun _ => RtFuel) ([], t).
End RTree.

(** [map] *)
Fixpoint rt_map {A B} (f : A -> B) (t : rtree A) : rtree B :=
  match t with
  | RVar i j => RVar i j
  | RNode a sons => RNode (f a) (map (map (rt_map f)) sons)
  | RRec j defs => RRec j (map (rt_map f) defs)
  end.

(** ** Labels (kernel/declarations.mli) *)

Inductive recarg_type :=
| RecArgInd (ind : inductive)
| RecArgPrim (c : kername).

Inductive recarg :=
| Norec
| Mrec (r : recarg_type).

Definition recarg_type_eqb (r r' : recarg_type) : bool :=
  match r, r' with
  | RecArgInd i, RecArgInd i' => eqb i i'
  | RecArgPrim c, RecArgPrim c' => eqb c c'
  | _, _ => false
  end.

(** [eq_recarg] (kernel/declareops.ml) *)
Definition recarg_eqb (r r' : recarg) : bool :=
  match r, r' with
  | Norec, Norec => true
  | Mrec t, Mrec t' => recarg_type_eqb t t'
  | _, _ => false
  end.

Lemma recarg_eqb_spec (r r' : recarg) : reflect (r = r') (recarg_eqb r r').
Proof.
  destruct r as [|[i|c]], r' as [|[i'|c']]; cbn; try (constructor; congruence).
  - destruct (eqb_specT i i'); constructor; congruence.
  - destruct (eqb_specT c c'); constructor; congruence.
Qed.

Definition wf_paths := rtree recarg.

(** kernel/declareops.ml *)
Definition mk_norec : wf_paths := RNode Norec [].

Definition mk_paths (r : recarg) (recargs : list (list wf_paths)) : wf_paths :=
  RNode r recargs.

Definition dest_recarg (fuel : nat) (p : wf_paths) : rt_answer recarg :=
  x <-? rt_dest_node fuel p ;; RtOk x.1.

Definition dest_subterms (fuel : nat) (p : wf_paths) : rt_answer (list (list wf_paths)) :=
  x <-? rt_dest_node fuel p ;; RtOk x.2.

(** [is_norec_path] (kernel/inductive.ml): a variable at the head is not a
    [Norec] path (the kernel catches the [Failure] of [Rtree.dest_head]). *)
Definition is_norec_path (fuel : nat) (t : wf_paths) : rt_answer bool :=
  e <-? rt_expand fuel t ;;
  match e with
  | RNode Norec _ => RtOk true
  | _ => RtOk false
  end.

(** ** Reduction parameter *)

Inductive red_answer :=
| RdWhnf (t : term)
| RdBad (msg : string)
| RdFuel.

Definition rt_of_red (r : red_answer) : rt_answer term :=
  match r with
  | RdWhnf t => RtOk t
  | RdBad msg => RtBad msg
  | RdFuel => RtFuel
  end.

(** [is_primitive_positive_container] (kernel/inductive.ml): [c] is the type
    of primitive arrays. *)
Definition is_primitive_positive_container (retro : Retroknowledge.t) (c : kername) : bool :=
  match retro.(Retroknowledge.retro_array) with
  | Some c' => eqb c c'
  | None => false
  end.

Definition lookup_mind (lookup : kername -> option global_decl) (kn : kername)
  : rt_answer mutual_inductive_body :=
  match lookup kn with
  | Some (InductiveDecl mdecl) => RtOk mdecl
  | Some (ConstantDecl _) => RtBad ("not an inductive: " ^ string_of_kername kn)
  | None => RtBad ("unknown inductive: " ^ string_of_kername kn)
  end.

(** [List.chop]: [None] when the list is too short. *)
Fixpoint chop_opt {X} (n : nat) (l : list X) : option (list X * list X) :=
  match n, l with
  | 0, _ => Some ([], l)
  | S n, x :: l => option_map (fun p => (x :: p.1, p.2)) (chop_opt n l)
  | S _, [] => None
  end.

Definition array_min {X} (nmr : nat) (a : list (nat * X)) : nat :=
  if Nat.eqb nmr 0 then 0 else fold_left (fun k p => Nat.min k p.1) a nmr.

(** [mind_extract_params] = [decompose_prod_n_decls]: remove [n] syntactic
    products or [let]s. *)
Fixpoint mind_extract_params (n : nat) (c : term) : option term :=
  match n with
  | 0 => Some c
  | S n =>
    match c with
    | tProd _ _ b | tLetIn _ _ _ b => mind_extract_params n b
    | _ => None
    end
  end.

(** [hnf_prod_applist] *)
Fixpoint hnf_prod_applist (whdf : term -> rt_answer term) (c : term) (args : list term)
  : rt_answer term :=
  match args with
  | [] => RtOk c
  | a :: args =>
    c' <-? whdf c ;;
    match c' with
    | tProd _ _ b => hnf_prod_applist whdf (subst10 a b) args
    | _ => RtBad "hnf_prod_applist: need a product"
    end
  end.

(** ** [abstract_mind_lc] (kernel/inductive.ml)

  Removes the [npars] recursive parameters of the inductives of a block in
  the types [lc] of its constructors.  A kernel constructor type mentions the
  block's inductives as [Ind]; a PCUIC [cstr_type] mentions them as the
  variables of the arities context (inductive [i] of [ntyps] is
  [tRel (k + ntyps - 1 - i)] under [k] binders), so the variable is kept and
  only its first [npars] arguments are dropped; a partial application is
  completed with [lambda_implicit]. *)

Definition implicit_binder : aname := mkBindAnn nAnon Relevant.

Fixpoint lambda_implicit (n : nat) (a : term) : term :=
  match n with
  | 0 => a
  | S n => tLambda implicit_binder (tSort Sort.type0) (lambda_implicit n a)
  end.

Section AbstractMindLc.
  Context (ntyps npars : nat).

  (** The occurrence [tRel j] of an inductive of the block, applied to the
      already processed arguments [args]. *)
  Definition abstract_ind_app (j : nat) (args : list term) : term :=
    if Nat.leb npars #|args| then mkApps (tRel j) (skipn npars args)
    else let n := npars - #|args| in lambda_implicit n (tRel (j + n)).

  (** [replace_ind k t acc] processes [mkApps t acc] under [k] binders, where
      the arguments [acc] are already processed. *)
  Fixpoint replace_ind (k : nat) (t : term) (acc : list term) {struct t} : term :=
    match t with
    | tApp u v => replace_ind k u (replace_ind k v [] :: acc)
    | tRel j =>
      if Nat.leb k j && Nat.ltb j (k + ntyps) then abstract_ind_app j acc
      else mkApps (tRel j) acc
    | tEvar ev args => mkApps (tEvar ev (map (fun a => replace_ind k a []) args)) acc
    | tLambda na T M => mkApps (tLambda na (replace_ind k T []) (replace_ind (S k) M [])) acc
    | tProd na T M => mkApps (tProd na (replace_ind k T []) (replace_ind (S k) M [])) acc
    | tLetIn na b B u =>
      mkApps (tLetIn na (replace_ind k b []) (replace_ind k B []) (replace_ind (S k) u [])) acc
    | tCase ci p c brs =>
      mkApps (tCase ci (map_predicate_k id (fun k t => replace_ind k t []) k p)
                (replace_ind k c [])
                (map_branches_k (fun k t => replace_ind k t []) id k brs)) acc
    | tProj p c => mkApps (tProj p (replace_ind k c [])) acc
    | tFix mfix idx =>
      let k' := #|mfix| + k in
      mkApps (tFix (map (map_def (fun t => replace_ind k t []) (fun t => replace_ind k' t [])) mfix) idx) acc
    | tCoFix mfix idx =>
      let k' := #|mfix| + k in
      mkApps (tCoFix (map (map_def (fun t => replace_ind k t []) (fun t => replace_ind k' t [])) mfix) idx) acc
    | tPrim p => mkApps (tPrim (map_prim (fun t => replace_ind k t []) p)) acc
    | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => mkApps t acc
    end.
End AbstractMindLc.

Definition abstract_mind_lc (ntyps npars : nat) (lc : list term) : list term :=
  map (fun c => replace_ind ntyps npars 0 c []) lc.

(** ** The recursive-argument trees of a block (kernel/indtypes.ml) *)

(** The per-call memo of block results ([nmr], trees), keyed by the block's
    name, as the kernel's [Cache]. *)
Definition recargs_memo := list (kername * (nat * list wf_paths)).

Definition memo_find (memo : recargs_memo) (kn : kername) : option (nat * list wf_paths) :=
  option_map snd (find (fun p => eqb p.1 kn) memo).

(** A state monad threading the memo. *)
Definition sm (X : Type) : Type := recargs_memo -> rt_answer (X * recargs_memo).

Definition sm_ret {X} (x : X) : sm X := fun memo => RtOk (x, memo).
Definition sm_bind {X Y} (m : sm X) (f : X -> sm Y) : sm Y :=
  fun memo => rt_bind (m memo) (fun p => f p.1 p.2).
Definition sm_lift {X} (m : rt_answer X) : sm X :=
  fun memo => rt_bind m (fun x => RtOk (x, memo)).
Definition sm_bad {X} (msg : string) : sm X := fun _ => RtBad msg.
Definition sm_fuel {X} : sm X := fun _ => RtFuel.

Local Notation "x <- m ;; f" := (sm_bind m (fun x => f))
  (at level 100, m at next level, right associativity).

Fixpoint sm_map {X Y} (f : X -> sm Y) (l : list X) : sm (list Y) :=
  match l with
  | [] => sm_ret []
  | x :: l => y <- f x ;; ys <- sm_map f l ;; sm_ret (y :: ys)
  end.

Fixpoint sm_mapi_rec {X Y} (f : nat -> X -> sm Y) (i : nat) (l : list X) : sm (list Y) :=
  match l with
  | [] => sm_ret []
  | x :: l => y <- f i x ;; ys <- sm_mapi_rec f (S i) l ;; sm_ret (y :: ys)
  end.

Definition sm_mapi {X Y} (f : nat -> X -> sm Y) (l : list X) : sm (list Y) :=
  sm_mapi_rec f 0 l.

Fixpoint sm_fold_left_map {X Y} (f : nat -> X -> sm (nat * Y)) (acc : nat) (l : list X)
  : sm (nat * list Y) :=
  match l with
  | [] => sm_ret (acc, [])
  | x :: l =>
    p <- f acc x ;;
    q <- sm_fold_left_map f p.1 l ;;
    sm_ret (q.1, p.2 :: q.2)
  end.

(** The environment of the block computation (kernel [ienv], without the
    typing environment):
    - [ie_n]: de Bruijn index (from 0) of the last inductive of the block,
      which then occupies [ie_n .. ie_n + ie_ntypes - 1];
    - [ie_ra]: the label and tree of each variable, innermost first;
    - [ie_lets]: the body of each variable that is a [let] (the [let]
      parameters of the block), innermost first. *)
Record ienv := mk_ienv {
  ie_n : nat;
  ie_ntypes : nat;
  ie_ra : list (recarg * wf_paths);
  ie_lets : list (option term) }.

Definition lift_ra_env (n : nat) (ra : list (recarg * wf_paths)) : list (recarg * wf_paths) :=
  map (fun p => (p.1, rt_lift n p.2)) ra.

(** [ienv_push_var] *)
Definition ienv_push_var (ie : ienv) (ra : wf_paths) : ienv :=
  {| ie_n := S ie.(ie_n); ie_ntypes := ie.(ie_ntypes);
     ie_ra := (Norec, ra) :: ie.(ie_ra); ie_lets := None :: ie.(ie_lets) |}.

(** [ienv_push_inductive] *)
Definition ienv_push_inductive (ie : ienv) (ind : inductive) : ienv :=
  {| ie_n := S ie.(ie_n); ie_ntypes := ie.(ie_ntypes);
     ie_ra := (Mrec (RecArgInd ind), RVar 0 0) :: lift_ra_env 1 ie.(ie_ra);
     ie_lets := None :: ie.(ie_lets) |}.

(** The labels and trees of the variables standing for the inductives of the
    block [mind] of [ntypes] inductives: the variable [0] is the last
    inductive ([Array.rev_to_list] of the kernel's [rc]). *)
Definition block_ra_env (mind : kername) (ntypes : nat) : list (recarg * wf_paths) :=
  List.rev (mapi (fun j (t : wf_paths) => (Mrec (RecArgInd (mkInd mind j)), t))
                 (rt_mk_rec_calls ntypes)).

(** What the kernel knows about the block whose constructors it checks (the
    arguments of [check_positivity_one]). *)
Record blk := mk_blk {
  blk_mind : kername;
  blk_params : context;
  blk_recursive : bool;
  blk_index : nat }.

(** The mutually recursive functions of [check_positivity_one], plus the
    computation of a whole block (needed for the [mind_nparams_rec] of a
    nested inductive), as requests of one recursive function. *)
Inductive pos_req :=
| PStrict (b : blk) (ie : ienv) (nmr : nat) (c : term)
  (** [check_strict_positivity] *)
| PNested (b : blk) (ie : ienv) (nmr : nat) (ind : inductive) (largs : list term)
  (** [check_positivity_nested] *)
| PNestedPrim (b : blk) (ie : ienv) (nmr : nat) (c : kername) (largs : list term)
  (** [check_positivity_nested_primitive] *)
| PConstr (b : blk) (ie : ienv) (check_head : bool) (nmr : nat) (lrec : list wf_paths) (c : term)
  (** [check_constr_rec] in [check_constructors] *)
| PBlock (mind : kername)
  (** [check_positivity] on the block [mind], memoised *).

Definition pos_res (r : pos_req) : Type :=
  match r with
  | PStrict _ _ _ _ | PNested _ _ _ _ _ | PNestedPrim _ _ _ _ _ => nat * wf_paths
  | PConstr _ _ _ _ _ _ | PBlock _ => nat * list wf_paths
  end.

Section Block.
  Context (whd : term -> red_answer) (lookup : kername -> option global_decl)
    (retro : Retroknowledge.t) (fuel : nat).

  (** [whd_all] in an environment whose [let] variables are [lets]. *)
  Definition whd_in (lets : list (option term)) (t : term) : rt_answer term :=
    nfuel (fun rec t =>
      r <-? rt_of_red (whd t) ;;
      match decompose_app r with
      | (tRel i, args) =>
        match nth_error lets i with
        | Some (Some b) => rec (mkApps (lift0 (S i) b) args)
        | _ => RtOk r
        end
      | _ => RtOk r
      end) fuel (fun _ => RtFuel) t.

  (** [compute_rec_par]: the number of first parameters that the arguments
      [largs] of a recursive occurrence pass unchanged, at most [nmr]. *)
  Definition compute_rec_par (ie : ienv) (paramsctxt : context) (nmr : nat) (largs : list term)
    : rt_answer nat :=
    if Nat.eqb nmr 0 then RtOk 0 else
    match chop_opt nmr largs with
    | None => RtBad "compute_rec_par: fewer arguments than parameters"
    | Some (lpar, _) =>
      let fix find (k index : nat) (lp : list term) (ps : context) {struct ps} : rt_answer nat :=
        match lp with
        | [] => RtOk nmr
        | p :: lp' =>
          match ps with
          | [] => RtBad "compute_rec_par: assertion failed"
          | d :: ps' =>
            match d.(decl_body) with
            | Some _ => find k (index - 1) lp ps'
            | None =>
              p' <-? whd_in ie.(ie_lets) p ;;
              match p' with
              | tRel w => if Nat.eqb w index then find (S k) (index - 1) lp' ps' else RtOk k
              | _ => RtOk k
              end
            end
          end
        end in
      find 0 (ie.(ie_n) - 1) lpar (List.rev paramsctxt)
    end.

  (** [ienv_decompose_prod] *)
  Fixpoint ienv_decompose_prod (ie : ienv) (n : nat) (c : term) : rt_answer (ienv * term) :=
    match n with
    | 0 => RtOk (ie, c)
    | S n =>
      c' <-? whd_in ie.(ie_lets) c ;;
      match c' with
      | tProd _ _ b => ienv_decompose_prod (ienv_push_var ie mk_norec) n b
      | _ => RtBad "ienv_decompose_prod: assertion failed"
      end
    end.

  (** [check_correct_par] (without its positivity part): the head of a
      constructor type is its inductive applied to the block's parameters. *)
  Definition check_correct_par (ie : ienv) (paramdecls : context) (args : list term)
    : rt_answer unit :=
    let nparams := context_assumptions paramdecls in
    if Nat.ltb #|args| nparams then RtBad "a constructor type has too few arguments" else
    let fix check (ps : list term) (decls : context) (idx : nat) {struct decls} : rt_answer unit :=
      match decls with
      | [] => RtOk tt
      | d :: decls =>
        match d.(decl_body) with
        | Some _ => check ps decls (S idx)
        | None =>
          match ps with
          | [] => RtBad "check_correct_par: assertion failed"
          | p :: ps =>
            p' <-? whd_in ie.(ie_lets) p ;;
            match p' with
            | tRel w =>
              if Nat.eqb w idx then check ps decls (S idx)
              else RtBad "a constructor type does not apply its inductive to the parameters"
            | _ => RtBad "a constructor type does not apply its inductive to the parameters"
            end
          end
        end
      end in
    check (List.rev (firstn nparams args)) paramdecls (ie.(ie_n) - #|paramdecls|).

  Section Steps.
    Context (rec : forall r, sm (pos_res r)).

    Definition call_strict b ie nmr c : sm (nat * wf_paths) := rec (PStrict b ie nmr c).
    Definition call_nested b ie nmr ind largs : sm (nat * wf_paths) :=
      rec (PNested b ie nmr ind largs).
    Definition call_nested_prim b ie nmr c largs : sm (nat * wf_paths) :=
      rec (PNestedPrim b ie nmr c largs).
    Definition call_constr b ie check_head nmr lrec c : sm (nat * list wf_paths) :=
      rec (PConstr b ie check_head nmr lrec c).
    Definition call_block mind : sm (nat * list wf_paths) := rec (PBlock mind).

    (** [check_strict_positivity]: the tree of one constructor argument. *)
    Definition strict_step (b : blk) (ie : ienv) (nmr : nat) (c : term) : sm (nat * wf_paths) :=
      x' <- sm_lift (whd_in ie.(ie_lets) c) ;;
      let '(x, largs) := decompose_app x' in
      match x with
      | tProd _ _ d =>
        match largs with
        | [] => call_strict b (ienv_push_var ie mk_norec) nmr d
        | _ => sm_bad "check_strict_positivity: assertion failed"
        end
      | tRel k =>
        match nth_error ie.(ie_ra) k with
        | Some (ra, rarg) =>
          largs' <- sm_lift (rt_map_list (whd_in ie.(ie_lets)) largs) ;;
          nmr1 <- match ra with
                  | Mrec (RecArgInd ind') =>
                    if eqb ind'.(inductive_mind) b.(blk_mind)
                    then sm_lift (compute_rec_par ie b.(blk_params) nmr largs')
                    else sm_ret nmr
                  | _ => sm_ret nmr
                  end ;;
          sm_ret (nmr1, rarg)
        | None => sm_ret (nmr, mk_norec)
        end
      | tInd ind _ =>
        if forallb (noccur_between ie.(ie_n) ie.(ie_ntypes)) largs then sm_ret (nmr, mk_norec)
        else call_nested b ie nmr ind largs
      | tConst c _ =>
        if is_primitive_positive_container retro c then
          if forallb (noccur_between ie.(ie_n) ie.(ie_ntypes)) largs then sm_ret (nmr, mk_norec)
          else call_nested_prim b ie nmr c largs
        else sm_ret (nmr, mk_norec)
      | _ => sm_ret (nmr, mk_norec)
      end.

    (** [check_positivity_nested]: an inductive of the block occurs in the
        parameters of another inductive [ind]. *)
    Definition nested_step (b : blk) (ie : ienv) (nmr : nat) (ind : inductive) (largs : list term)
      : sm (nat * wf_paths) :=
      mdecl <- sm_lift (lookup_mind lookup ind.(inductive_mind)) ;;
      mip <- sm_lift (rt_of_option "check_positivity_nested: inductive index out of bounds"
                        (nth_error mdecl.(ind_bodies) ind.(inductive_ind))) ;;
      info <- call_block ind.(inductive_mind) ;;
      let auxnrecpar := info.1 in
      let auxnnonrecpar := mdecl.(ind_npars) - auxnrecpar in
      match chop_opt auxnrecpar largs with
      | None => sm_bad "check_positivity_nested: non-positive occurrence (too few parameters)"
      | Some (auxrecparams, _) =>
        let auxntyp := #|mdecl.(ind_bodies)| in
        if negb (Nat.eqb auxntyp 1) then
          sm_bad "check_positivity_nested: non-positive occurrence (nested mutual inductive)"
        else
        let auxlcvect := abstract_mind_lc auxntyp auxnrecpar (map cstr_type mip.(ind_ctors)) in
        let ie' := ienv_push_inductive ie ind in
        let auxrecparams' := map (lift0 auxntyp) auxrecparams in
        irecargs_nmr <- sm_map (fun c =>
            c' <- sm_lift (hnf_prod_applist (whd_in ie'.(ie_lets)) c auxrecparams') ;;
            p <- sm_lift (ienv_decompose_prod ie' auxnnonrecpar c') ;;
            call_constr b p.1 false nmr [] p.2) auxlcvect ;;
        let irecargs := map snd irecargs_nmr in
        let nmr' := array_min nmr irecargs_nmr in
        trees <- sm_lift (rt_mk_rec fuel [mk_paths (Mrec (RecArgInd ind)) irecargs]) ;;
        match trees with
        | [t] => sm_ret (nmr', t)
        | _ => sm_bad "Rtree.mk_rec: unexpected result"
        end
      end.

    (** [check_positivity_nested_primitive]: the primitive type [c X1 ... Xn]
        is modelled as an inductive with one constructor [X1 -> ... -> Xn ->
        c X1 ... Xn]. *)
    Definition nested_prim_step (b : blk) (ie : ienv) (nmr : nat) (c : kername) (largs : list term)
      : sm (nat * wf_paths) :=
      let ie' := {| ie_n := ie.(ie_n); ie_ntypes := ie.(ie_ntypes);
                    ie_ra := lift_ra_env 1 ie.(ie_ra); ie_lets := ie.(ie_lets) |} in
      p <- sm_fold_left_map (fun nmr a => call_strict b ie' nmr a) nmr largs ;;
      trees <- sm_lift (rt_mk_rec fuel [mk_paths (Mrec (RecArgPrim c)) [p.2]]) ;;
      match trees with
      | [t] => sm_ret (p.1, t)
      | _ => sm_bad "Rtree.mk_rec: unexpected result"
      end.

    (** [check_constr_rec]: the trees of the arguments of a constructor type
        [c]; [lrec] holds the trees of the arguments already crossed, in
        reverse order.  With [check_head], the head must be the inductive
        [blk_index] applied to the parameters ([check_correct_par]). *)
    Definition constr_step (b : blk) (ie : ienv) (check_head : bool) (nmr : nat)
      (lrec : list wf_paths) (c : term) : sm (nat * list wf_paths) :=
      x' <- sm_lift (whd_in ie.(ie_lets) c) ;;
      let '(x, largs) := decompose_app x' in
      match x with
      | tProd _ a d =>
        match largs with
        | _ :: _ => sm_bad "check_constructors: assertion failed"
        | [] =>
          if negb b.(blk_recursive) && negb (noccur_between ie.(ie_n) ie.(ie_ntypes) a) then
            sm_bad "a non-recursive type occurs in the type of one of its constructors"
          else
            p <- call_strict b ie nmr a ;;
            call_constr b (ienv_push_var ie mk_norec) check_head p.1 (p.2 :: lrec) d
        end
      | hd =>
        ok <- (if check_head then
                 match hd with
                 | tRel j =>
                   if Nat.eqb j (ie.(ie_n) + ie.(ie_ntypes) - b.(blk_index) - 1)
                   then sm_lift (check_correct_par ie b.(blk_params) largs)
                   else sm_bad "a constructor type does not end with its inductive type"
                 | _ => sm_bad "a constructor type does not end with its inductive type"
                 end
               else sm_ret tt) ;;
        sm_ret (nmr, List.rev lrec)
      end.

    (** [check_positivity] on the block [mind] (with [check_positivity_one]
        for each of its inductives), memoised. *)
    Definition block_step (mind : kername) : sm (nat * list wf_paths) :=
      fun memo =>
      match memo_find memo mind with
      | Some r => RtOk (r, memo)
      | None =>
        (mdecl <- sm_lift (lookup_mind lookup mind) ;;
         let ntypes := #|mdecl.(ind_bodies)| in
         let recursive := match mdecl.(ind_finite) with BiFinite => false | _ => true end in
         if negb recursive && negb (Nat.eqb ntypes 1) then
           sm_bad "a non-recursive block must have exactly one inductive"
         else
         let params := mdecl.(ind_params) in
         let nparamsctxt := #|params| in
         let nmr := context_assumptions params in
         let ra_env_ar := block_ra_env mind ntypes in
         let ie := {| ie_n := nparamsctxt; ie_ntypes := ntypes;
                      ie_ra := List.app (repeat (Norec, mk_norec) nparamsctxt) ra_env_ar;
                      ie_lets := List.app (map decl_body params) (repeat None ntypes) |} in
         irecargs_nmr <- sm_mapi (fun i body =>
             let bk := {| blk_mind := mind; blk_params := params;
                          blk_recursive := recursive; blk_index := i |} in
             ctors <- sm_map (fun cdecl =>
                 rawc <- sm_lift (rt_of_option "a constructor type has fewer binders than parameters"
                                    (mind_extract_params nparamsctxt cdecl.(cstr_type))) ;;
                 call_constr bk ie true nmr [] rawc) body.(ind_ctors) ;;
             sm_ret (array_min nmr ctors,
                     mk_paths (Mrec (RecArgInd (mkInd mind i))) (map snd ctors))) mdecl.(ind_bodies) ;;
         let nmr' := array_min nmr irecargs_nmr in
         trees <- sm_lift (rt_mk_rec fuel (map snd irecargs_nmr)) ;;
         fun memo' => RtOk ((nmr', trees), (mind, (nmr', trees)) :: memo')) memo
      end.
  End Steps.

  Definition pos_step (rec : forall r, sm (pos_res r)) (r : pos_req) : sm (pos_res r) :=
    match r as r0 return sm (pos_res r0) with
    | PStrict b ie nmr c => strict_step rec b ie nmr c
    | PNested b ie nmr ind largs => nested_step rec b ie nmr ind largs
    | PNestedPrim b ie nmr c largs => nested_prim_step rec b ie nmr c largs
    | PConstr b ie ch nmr lrec c => constr_step rec b ie ch nmr lrec c
    | PBlock mind => block_step rec mind
    end.
End Block.

(** [ind_block_recargs_memo whd lookup retro fuel memo mind]: the number of
    recursive parameters of the block [mind] ([mind_nparams_rec]) and the
    tree of each of its inductives ([mind_recargs] of each packet, i.e. the
    [Rtree.mk_rec] of the block), reusing and extending [memo]. *)
Definition ind_block_recargs_memo (whd : term -> red_answer)
  (lookup : kername -> option global_decl) (retro : Retroknowledge.t) (fuel : nat)
  (memo : recargs_memo) (mind : kername) : rt_answer ((nat * list wf_paths) * recargs_memo) :=
  @dfuel pos_req (fun r => sm (pos_res r)) (pos_step whd lookup retro fuel) fuel
    (fun _ => sm_fuel) (PBlock mind) memo.

Definition ind_block_recargs (whd : term -> red_answer)
  (lookup : kername -> option global_decl) (retro : Retroknowledge.t) (fuel : nat)
  (mind : kername) : rt_answer (nat * list wf_paths) :=
  p <-? ind_block_recargs_memo whd lookup retro fuel [] mind ;; RtOk p.1.

(** ** The guard-time approximation (kernel/inductive.ml) *)

(** [check_inductive_codomain]: after its abstractions and products, the
    whnf of [p] has an inductive at its head. *)
Definition check_inductive_codomain (whd : term -> red_answer) (fuel : nat) (p : term)
  : rt_answer bool :=
  nfuel (fun rec (x : bool * term) =>
    let '(in_prods, t) := x in
    t' <-? rt_of_red (whd t) ;;
    match in_prods, t' with
    | false, tLambda _ _ b => rec (false, b)
    | false, _ => rec (true, t')
    | true, tProd _ _ b => rec (true, b)
    | true, _ => RtOk (match (decompose_app t').1 with tInd _ _ => true | _ => false end)
    end) fuel (fun _ => RtFuel) (false, p).

(** The requests of [get_recargs_approx]: the environment is the list of the
    label and tree of each variable ([ra_env]), innermost first; a free
    variable is [Norec]. *)
Inductive ax_req :=
| AXRec (ra : list (recarg * wf_paths)) (tree : wf_paths) (c : term)
  (** [build_recargs] *)
| AXNested (ra : list (recarg * wf_paths)) (tree : wf_paths) (ind : inductive) (largs : list term)
  (** [build_recargs_nested] *)
| AXNestedPrim (ra : list (recarg * wf_paths)) (tree : wf_paths) (c : kername) (largs : list term)
  (** [build_recargs_nested_primitive] *)
| AXConstr (ra : list (recarg * wf_paths)) (trees : list wf_paths) (lrec : list wf_paths) (c : term)
  (** [recargs_constr_rec] in [build_recargs_constructors] *).

Definition ax_res (r : ax_req) : Type :=
  match r with
  | AXConstr _ _ _ _ => list wf_paths
  | _ => wf_paths
  end.

Section Approx.
  Context (whd : term -> red_answer) (lookup : kername -> option global_decl)
    (retro : Retroknowledge.t) (fuel : nat).

  Definition whd_rt (t : term) : rt_answer term := rt_of_red (whd t).

  (** [ienv_decompose_prod] of kernel/inductive.ml (no [let]s here). *)
  Fixpoint approx_decompose_prod (ra : list (recarg * wf_paths)) (n : nat) (c : term)
    : rt_answer (list (recarg * wf_paths) * term) :=
    match n with
    | 0 => RtOk (ra, c)
    | S n =>
      c' <-? whd_rt c ;;
      match c' with
      | tProd _ _ b => approx_decompose_prod ((Norec, mk_norec) :: ra) n b
      | _ => RtBad "ienv_decompose_prod: assertion failed"
      end
    end.

  Definition block_info (mind : kername) : sm (nat * list wf_paths) :=
    fun memo => ind_block_recargs_memo whd lookup retro fuel memo mind.

  Section Steps.
    Context (rec : forall r, sm (ax_res r)).

    Definition call_rec ra tree c : sm wf_paths := rec (AXRec ra tree c).
    Definition call_rnested ra tree ind largs : sm wf_paths := rec (AXNested ra tree ind largs).
    Definition call_rnested_prim ra tree c largs : sm wf_paths := rec (AXNestedPrim ra tree c largs).
    Definition call_rconstr ra trees lrec c : sm (list wf_paths) := rec (AXConstr ra trees lrec c).

    (** [build_recargs] *)
    Definition build_recargs_step (ra : list (recarg * wf_paths)) (tree : wf_paths) (c : term)
      : sm wf_paths :=
      x' <- sm_lift (whd_rt c) ;;
      let '(x, largs) := decompose_app x' in
      match x with
      | tProd _ _ d =>
        match largs with
        | [] => call_rec ((Norec, mk_norec) :: ra) tree d
        | _ => sm_bad "build_recargs: assertion failed"
        end
      | tRel k =>
        (* free variables are allowed and assigned Norec *)
        sm_ret (match nth_error ra k with Some p => p.2 | None => mk_norec end)
      | tInd ind _ =>
        (* when the tree allows it, a potential nested inductive type *)
        r <- sm_lift (dest_recarg fuel tree) ;;
        match r with
        | Mrec (RecArgInd ind') =>
          if eqb ind ind' then call_rnested ra tree ind largs else sm_ret mk_norec
        | _ => sm_ret mk_norec
        end
      | tConst c _ =>
        if is_primitive_positive_container retro c then
          r <- sm_lift (dest_recarg fuel tree) ;;
          match r with
          | Mrec (RecArgPrim c') =>
            if eqb c c' then call_rnested_prim ra tree c largs else sm_ret mk_norec
          | _ => sm_ret mk_norec
          end
        else sm_ret mk_norec
      | _ => sm_ret mk_norec
      end.

    (** [build_recargs_nested] *)
    Definition build_recargs_nested_step (ra : list (recarg * wf_paths)) (tree : wf_paths)
      (ind : inductive) (largs : list term) : sm wf_paths :=
      nr <- sm_lift (is_norec_path fuel tree) ;;
      (* if the tree already disallows recursion, no need to go further *)
      if nr then sm_ret tree else
      let mind := ind.(inductive_mind) in
      mdecl <- sm_lift (lookup_mind lookup mind) ;;
      info <- block_info mind ;;
      let nrecpar := info.1 in
      let nonrecpar := mdecl.(ind_npars) - nrecpar in
      match chop_opt nrecpar largs with
      | None => sm_bad "get_recargs_approx: fewer arguments than recursive parameters"
      | Some (lpar, _) =>
        let auxntyp := #|mdecl.(ind_bodies)| in
        let ra' := List.app (block_ra_env mind auxntyp) (lift_ra_env auxntyp ra) in
        let lpar' := map (lift0 auxntyp) lpar in
        (* for a mutual container, the trees computed for its block *)
        trees <- sm_lift (if Nat.eqb auxntyp 1
                          then (s <-? dest_subterms fuel tree ;; RtOk [s])
                          else rt_map_list (dest_subterms fuel) info.2) ;;
        irecargs <- sm_mapi (fun j mip =>
            let auxlcvect := abstract_mind_lc auxntyp nrecpar (map cstr_type mip.(ind_ctors)) in
            paths <- sm_mapi (fun k c =>
                c' <- sm_lift (hnf_prod_applist whd_rt c lpar') ;;
                p <- sm_lift (approx_decompose_prod ra' nonrecpar c') ;;
                tjk <- sm_lift (rt_of_option "get_recargs_approx: constructor index out of bounds"
                                  (match nth_error trees j with
                                   | Some tj => nth_error tj k
                                   | None => None
                                   end)) ;;
                call_rconstr p.1 tjk [] p.2) auxlcvect ;;
            sm_ret (mk_paths (Mrec (RecArgInd (mkInd mind j))) paths)) mdecl.(ind_bodies) ;;
        defs <- sm_lift (rt_mk_rec fuel irecargs) ;;
        sm_lift (rt_of_option "get_recargs_approx: inductive index out of bounds"
                   (nth_error defs ind.(inductive_ind)))
      end.

    (** [build_recargs_nested_primitive] *)
    Definition build_recargs_nested_primitive_step (ra : list (recarg * wf_paths))
      (tree : wf_paths) (c : kername) (largs : list term) : sm wf_paths :=
      nr <- sm_lift (is_norec_path fuel tree) ;;
      if nr then sm_ret tree else
      let ra' := lift_ra_env 1 ra in
      subs <- sm_lift (dest_subterms fuel tree) ;;
      match subs with
      | [] => sm_bad "get_recargs_approx: index out of bounds"
      | sub0 :: _ =>
        if negb (Nat.eqb #|sub0| #|largs|) then sm_bad "List.map2: lengths differ" else
        paths <- sm_map (fun p => call_rec ra' p.1 p.2) (combine sub0 largs) ;;
        defs <- sm_lift (rt_mk_rec fuel [mk_paths (Mrec (RecArgPrim c)) [paths]]) ;;
        match defs with
        | [t] => sm_ret t
        | _ => sm_bad "Rtree.mk_rec: unexpected result"
        end
      end.

    (** [recargs_constr_rec]: [trees] are the trees of the remaining
        arguments of the constructor in the tree being approximated. *)
    Definition build_recargs_constr_step (ra : list (recarg * wf_paths))
      (trees lrec : list wf_paths) (c : term) : sm (list wf_paths) :=
      x' <- sm_lift (whd_rt c) ;;
      let '(x, largs) := decompose_app x' in
      match x with
      | tProd _ b d =>
        match largs with
        | _ :: _ => sm_bad "build_recargs_constructors: assertion failed"
        | [] =>
          match trees with
          | [] => sm_bad "List.hd: a constructor has more arguments than its tree"
          | t :: trees' =>
            recarg <- call_rec ra t b ;;
            call_rconstr ((Norec, mk_norec) :: ra) trees' (recarg :: lrec) d
          end
        end
      | _ => sm_ret (List.rev lrec)
      end.
  End Steps.

  Definition ax_step (rec : forall r, sm (ax_res r)) (r : ax_req) : sm (ax_res r) :=
    match r as r0 return sm (ax_res r0) with
    | AXRec ra tree c => build_recargs_step rec ra tree c
    | AXNested ra tree ind largs => build_recargs_nested_step rec ra tree ind largs
    | AXNestedPrim ra tree c largs => build_recargs_nested_primitive_step rec ra tree c largs
    | AXConstr ra trees lrec c => build_recargs_constr_step rec ra trees lrec c
    end.
End Approx.

(** [get_recargs_approx whd lookup retro fuel memo tree ind args]: an
    approximation of the tree of [ind] applied to [args], knowing [tree];
    [tree] says when a candidate nested type is traversed, and the result is
    pruned to [mk_norec] otherwise.  The environment of [args] is opaque:
    each of its variables is [Norec].  The memo of block results is threaded
    through. *)
Definition get_recargs_approx (whd : term -> red_answer)
  (lookup : kername -> option global_decl) (retro : Retroknowledge.t) (fuel : nat)
  (memo : recargs_memo) (tree : wf_paths) (ind : inductive) (args : list term)
  : rt_answer (wf_paths * recargs_memo) :=
  @dfuel ax_req (fun r => sm (ax_res r)) (ax_step whd lookup retro fuel) fuel
    (fun _ => sm_fuel) (AXNested [] tree ind args) memo.

(** [has_constant_parameters whd lookup retro fuel memo nvars k ind args]:
    the recursive-parameter arguments in [args] of the inductive [ind]
    mention none of the variables in the kernel's range.  The kernel tests
    [noccur_with_meta (1 + k) (nvars + k)] (1-based), i.e. the 0-based range
    [k .. 2 k + nvars - 1]; this is ported as is. *)
Definition has_constant_parameters (whd : term -> red_answer)
  (lookup : kername -> option global_decl) (retro : Retroknowledge.t) (fuel : nat)
  (memo : recargs_memo) (nvars k : nat) (ind : inductive) (args : list term)
  : rt_answer (bool * recargs_memo) :=
  p <-? ind_block_recargs_memo whd lookup retro fuel memo ind.(inductive_mind) ;;
  match chop_opt p.1.1 args with
  | None => RtBad "has_constant_parameters: fewer arguments than recursive parameters"
  | Some (lpar, _) => RtOk (forallb (noccur_between k (nvars + k)) lpar, p.2)
  end.
