(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICPrimitive.
From Equations.Prop Require Import DepElim.
From Equations Require Import Equations.
Set Default Goal Selector "!".

(** * PCUIC's side of the primitive-operation interface

  [prim_of_lit] builds the payload of a literal argument and [lit_of_prim] reads
  one back; [readback] turns a result of [prim_op_denote] into the term the
  reduction rule produces.  Together with [common/theories/PrimitiveOps.v] and
  Template's pair in [template-rocq/theories/Typing.v] these are the only places
  that inspect a [PrimInt63.int] or [PrimString.string] payload: the machine and
  conversion reach literals only through [lit_of_prim]. *)

Definition prim_of_lit (l : prim_lit) : prim_val term :=
  match l with
  | LInt i => prim_int i
  | LString s => prim_string s
  end.

Definition lit_of_prim (p : prim_val term) : option prim_lit :=
  match p.π2 in prim_model _ t return option prim_lit with
  | primIntModel i => Some (LInt i)
  | primStringModel s => Some (LString s)
  | primFloatModel _ | primArrayModel _ => None
  end.

(** The term a literal argument occurs as in a redex. *)
Definition term_of_lit (l : prim_lit) : term := tPrim (prim_of_lit l).

(** A term's literal, if it is one of the expected tag.  This is what the
    machine and [whnf] use; neither matches a payload. *)
Definition lit_of_term (t : term) : option prim_lit :=
  match t with
  | tPrim p => lit_of_prim p
  | _ => None
  end.

(** The readback of a result.  [SBool] reads back to a constructor of the
    inductive registered as [retro_bool], positionally: [true] is constructor 0
    and [false] constructor 1, which is the kernel's orientation
    ([Register_ind PIT_bool] stores [((ind,1),(ind,2))], kernel/primred.ml, and
    kernel constructor indices are 1-based while [tConstruct] is 0-based). *)
Definition readback (Σ : global_env) (s : prim_shape) (r : prim_result) : option term :=
  match s, r with
  | SInt, RInt i => Some (tPrim (prim_int i))
  | SBool, RBool b =>
      match Σ.(retroknowledge).(Retroknowledge.retro_bool) with
      | Some ind => Some (tConstruct ind (if b then 0 else 1) [])
      | None => None
      end
  | SInt, RBool _ | SBool, RInt _ => None
  end.

(** ** Round trips *)

Lemma lit_of_prim_of_lit l : lit_of_prim (prim_of_lit l) = Some l.
Proof. by destruct l. Qed.

Lemma lit_of_prim_inv p l : lit_of_prim p = Some l -> p = prim_of_lit l.
Proof.
  destruct p as [t m]; destruct m; cbn; intros [= <-]; reflexivity.
Qed.

Lemma lit_of_term_of_lit l : lit_of_term (term_of_lit l) = Some l.
Proof. apply lit_of_prim_of_lit. Qed.

Lemma lit_of_term_inv t l : lit_of_term t = Some l -> t = term_of_lit l.
Proof.
  destruct t => //=; intros h; rewrite /term_of_lit; f_equal; now apply lit_of_prim_inv.
Qed.

Lemma prim_of_lit_inj l l' : prim_of_lit l = prim_of_lit l' -> l = l'.
Proof.
  intros e; apply (f_equal lit_of_prim) in e.
  rewrite !lit_of_prim_of_lit in e; now injection e.
Qed.

Lemma term_of_lit_inj l l' : term_of_lit l = term_of_lit l' -> l = l'.
Proof.
  intros e; apply (f_equal lit_of_term) in e.
  rewrite !lit_of_term_of_lit in e; now injection e.
Qed.

Lemma map_term_of_lit_inj ls ls' :
  map term_of_lit ls = map term_of_lit ls' -> ls = ls'.
Proof.
  induction ls as [|a ls ih] in ls' |- *; destruct ls' as [|b ls'] => //=.
  intros e; injection e as e1 e2.
  apply prim_of_lit_inj in e1. apply ih in e2. now subst.
Qed.

(** ** The reduct of a redex is unique

  A redex of the rule determines its head constant, its universe instance and
  its literal arguments; [prim_op_of] is a function of the head (the table's
  kernames are distinct), [prim_op_denote] is a function, and so is [readback].
  These are the two halves confluence needs. *)

Lemma prim_redex_inj c u ls c' u' ls' :
  mkApps (tConst c u) (map term_of_lit ls) = mkApps (tConst c' u') (map term_of_lit ls') ->
  [× c = c', u = u' & ls = ls'].
Proof.
  intros e.
  eapply mkApps_eq_inj in e as [e1 e2]; [|easy|easy].
  noconf e1. split => //. now apply map_term_of_lit_inj.
Qed.

Lemma readback_funct Σ s r v v' :
  readback Σ s r = Some v -> readback Σ s r = Some v' -> v = v'.
Proof.
  intros h h'; rewrite h in h'; now injection h' as <-.
Qed.

(** One reduct: the data of two firings of the rule on the same term agree.
    [op = op'] is the caller's: [prim_op_of] is a function of the head, and
    [prim_redex_inj] gives it the same head. *)
Lemma red_prim_op_det Σ op ls r r' v v' :
  prim_op_denote op ls = Some r -> prim_op_denote op ls = Some r' ->
  readback Σ (po_shape (info op)) r = Some v ->
  readback Σ (po_shape (info op)) r' = Some v' ->
  v = v'.
Proof.
  intros d d' b b'.
  pose proof (prim_op_denote_funct _ _ _ _ d d') as <-.
  now eapply readback_funct.
Qed.

(** ** The arguments of a redex, and the computed reduct

  The machine ([PCUICSafeReduce], design §7.2), the weak-head forms
  ([PCUICNormal], §6) and the machine's graph ([PCUICArityRed], §7.2) all have
  to answer the same two questions about an application of a registered
  operation: which of its arguments are already literals, and what the rule
  produces if they all are.  They are answered here, once, so that none of
  those three files matches on a payload.

  [split_lits] reads the arguments left to right: [inl ls] when every one is a
  literal, [inr (ls, a, rest)] when [a] is the first that is not.  The
  decomposition is therefore unique, which is what makes the machine's graph
  deterministic. *)

Fixpoint split_lits (args : list term)
  : list prim_lit + (list prim_lit * term * list term) :=
  match args with
  | [] => inl []
  | a :: args =>
      match lit_of_term a with
      | Some l =>
          match split_lits args with
          | inl ls => inl (l :: ls)
          | inr (ls, b, rest) => inr (l :: ls, b, rest)
          end
      | None => inr ([], a, args)
      end
  end.

Definition lits_of_args (args : list term) : option (list prim_lit) :=
  match split_lits args with inl ls => Some ls | inr _ => None end.

Lemma split_lits_inl {args ls} : split_lits args = inl ls -> args = map term_of_lit ls.
Proof.
  induction args as [|a args ih] in ls |- *; cbn.
  - intros [= <-]; reflexivity.
  - destruct (lit_of_term a) as [l|] eqn:ha => //.
    destruct (split_lits args) as [ls'|[[??]?]] eqn:hs => // [= <-].
    cbn; f_equal; [now apply lit_of_term_inv|now apply ih].
Qed.

Lemma split_lits_inr {args ls a rest} :
  split_lits args = inr (ls, a, rest) ->
  (args = map term_of_lit ls ++ a :: rest) × (lit_of_term a = None).
Proof.
  induction args as [|b args ih] in ls, a, rest |- *; cbn => //.
  destruct (lit_of_term b) as [l|] eqn:hb.
  - destruct (split_lits args) as [ls'|[[ls' a'] rest']] eqn:hs => // [= <- <- <-].
    destruct (ih _ _ _ eq_refl) as [e hl]. split => //.
    cbn; f_equal; [now apply lit_of_term_inv|exact e].
  - intros [= <- <- <-]. split => //.
Qed.

Lemma split_lits_map ls : split_lits (map term_of_lit ls) = inl ls.
Proof.
  induction ls as [|l ls ih]; [reflexivity|].
  cbn [map split_lits]. rewrite lit_of_term_of_lit ih //.
Qed.

Lemma split_lits_length_inr {args ls a rest} :
  split_lits args = inr (ls, a, rest) -> #|args| = S (#|ls| + #|rest|).
Proof.
  intros h; destruct (split_lits_inr h) as [-> _]; len; lia.
Qed.

Lemma split_lits_app {ls a rest} :
  lit_of_term a = None -> split_lits (map term_of_lit ls ++ a :: rest) = inr (ls, a, rest).
Proof.
  intros ha; induction ls as [|l ls ih]; [now cbn; rewrite ha|].
  cbn [map app split_lits]. rewrite lit_of_term_of_lit ih //.
Qed.

(** Replacing the first non-literal argument by its weak-head normal form, when
    that is not a literal either, leaves the split where it was.  This is what
    makes the machine's stopping state its own weak-head normal form. *)
Lemma split_lits_replace {n args ls a rest b} :
  n <= #|args| ->
  split_lits (firstn n args) = inr (ls, a, rest) ->
  lit_of_term b = None ->
  (n <= #|map term_of_lit ls ++ b :: rest ++ skipn n args|) ×
  (firstn n (map term_of_lit ls ++ b :: rest ++ skipn n args)
     = map term_of_lit ls ++ b :: rest).
Proof.
  intros hn hs hb.
  destruct (split_lits_inr hs) as [ef _].
  have hfl : #|firstn n args| = n by rewrite length_firstn; lia.
  have hlen : #|map term_of_lit ls ++ b :: rest| = n.
  { rewrite -hfl ef !length_app !length_map //=. }
  have happ : forall (x y : list term), #|x| = n -> firstn n (x ++ y) = x.
  { intros x y hx. rewrite firstn_app -hx firstn_all Nat.sub_diag /= app_nil_r //. }
  have esp : map term_of_lit ls ++ b :: rest ++ skipn n args
           = (map term_of_lit ls ++ b :: rest) ++ skipn n args
    by rewrite -app_assoc.
  rewrite esp.
  split; [rewrite length_app; lia|exact (happ _ _ hlen)].
Qed.

Lemma split_lits_length_inl {args ls} : split_lits args = inl ls -> #|args| = #|ls|.
Proof. intros h; rewrite (split_lits_inl h) length_map //. Qed.

Lemma lits_of_args_inv {args ls} : lits_of_args args = Some ls -> args = map term_of_lit ls.
Proof.
  rewrite /lits_of_args; destruct (split_lits args) eqn:h => // [= <-].
  now apply split_lits_inl.
Qed.

Lemma lits_of_args_map ls : lits_of_args (map term_of_lit ls) = Some ls.
Proof. by rewrite /lits_of_args split_lits_map. Qed.

(** The reduct the rule produces on these arguments, if it can fire.  [None] is
    exactly §6's [cannot_fire]: an argument that is not a literal (stuck, or a
    payload of the wrong kind), an argument list the operation does not accept,
    or a readback that fails because the booleans are not registered. *)
Definition prim_reduct (Σ : global_env) (op : prim_op) (args : list term) : option term :=
  match lits_of_args args with
  | Some ls =>
      match prim_op_denote op ls with
      | Some r => readback Σ (po_shape (info op)) r
      | None => None
      end
  | None => None
  end.

Lemma prim_reduct_lits Σ op ls :
  prim_reduct Σ op (map term_of_lit ls) =
  match prim_op_denote op ls with
  | Some r => readback Σ (po_shape (info op)) r
  | None => None
  end.
Proof. by rewrite /prim_reduct lits_of_args_map. Qed.

Lemma prim_reduct_spec {Σ op args v} :
  prim_reduct Σ op args = Some v ->
  ∑ ls r, [× lits_of_args args = Some ls, prim_op_denote op ls = Some r,
             readback Σ (po_shape (info op)) r = Some v & args = map term_of_lit ls].
Proof.
  rewrite /prim_reduct; destruct (lits_of_args args) as [ls|] eqn:hls => //.
  destruct (prim_op_denote op ls) as [r|] eqn:hd => // hb.
  exists ls, r; split => //. now apply lits_of_args_inv.
Qed.

(** Only the arguments decide whether the rule fires, so a reduct computed in
    one environment is computed in every environment with the same booleans. *)
Lemma prim_reduct_retro {Σ Σ' op args} :
  Σ.(retroknowledge).(Retroknowledge.retro_bool)
    = Σ'.(retroknowledge).(Retroknowledge.retro_bool) ->
  prim_reduct Σ op args = prim_reduct Σ' op args.
Proof.
  intros e; rewrite /prim_reduct; destruct (lits_of_args args) as [ls|] => //.
  destruct (prim_op_denote op ls) as [[i|b]|] => //=.
  destruct (po_shape (info op)) => //=. now rewrite e.
Qed.
