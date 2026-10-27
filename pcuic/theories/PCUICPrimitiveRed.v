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
