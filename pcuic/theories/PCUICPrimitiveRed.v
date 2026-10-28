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

Lemma split_lits_length_inl {args ls} : split_lits args = inl ls -> #|args| = #|ls|.
Proof. intros h; rewrite (split_lits_inl h) length_map //. Qed.

Lemma lits_of_args_inv {args ls} : lits_of_args args = Some ls -> args = map term_of_lit ls.
Proof.
  rewrite /lits_of_args; destruct (split_lits args) eqn:h => // [= <-].
  now apply split_lits_inl.
Qed.

Lemma lits_of_args_map ls : lits_of_args (map term_of_lit ls) = Some ls.
Proof. by rewrite /lits_of_args split_lits_map. Qed.

(** The reduct the rule produces on these arguments, if it can fire.  [None] means
    the rule cannot fire: an argument that is not a literal (stuck, or a
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
