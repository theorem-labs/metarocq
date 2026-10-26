(* The positivity check of the safe checker, run directly on quoted inductive types.

   [nested_positivity.v] tests the whole of [MetaRocq SafeCheck]. This file runs only the
   positivity function, [PCUICPositivityCheck.check_positive_cstr], on each constructor of
   each block, so its answer is checked by [vm_compute] even where the rest of SafeCheck
   would stop earlier (for example at a template-polymorphic universe). Each [Check_*]
   below is an equation that holds by computation: the list of answers, one per
   constructor, is exactly the expected one. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import Loader.
From MetaRocq.Template Require Ast.
From MetaRocq.PCUIC Require Import PCUICAst.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICPositivityCheck.

Import MonadNotation.

(** The declaration of an inductive, from a PCUIC environment. *)
Definition env_lookup (Σ : global_env) (ind : inductive) :
  typing_result (mutual_inductive_body × one_inductive_body) :=
  match lookup_env Σ (inductive_mind ind) with
  | Some (InductiveDecl mdecl') =>
    match nth_error (ind_bodies mdecl') (inductive_ind ind) with
    | Some idecl' => ret (mdecl', idecl')
    | None => raise (UndeclaredInductive ind)
    end
  | _ => raise (UndeclaredInductive ind)
  end.

(** The answer for one constructor type: [None] for accepted, [Some msg] for refused. *)
Definition answer lookup mdecl i t : option string :=
  match check_positive_cstr lookup positivity_fuel mdecl i [] t with
  | Checked _ => None
  | TypeError (Msg s) => Some s
  | TypeError _ => Some "other error"
  end.

(** The answers for the constructors of the block that a quoted program's main term names,
    in order. The environment used for lookups is the whole translated program; the block
    cannot nest in itself through a lookup, because the rule looks up only [tInd] heads, and
    the block's own members are [tRel]s in its constructor types. *)
Definition positivity_answers (p : Ast.Env.program) : list (option string) :=
  let Σ := PCUICProgram.trans_env_env (trans_global_env p.1) in
  match p.2 with
  | Ast.tInd ind _ =>
    match env_lookup Σ ind with
    | Checked (mdecl, _) =>
      concat (mapi (fun i idecl =>
        map (fun cdecl => answer (env_lookup Σ) mdecl i (cstr_type cdecl)) (ind_ctors idecl))
        (ind_bodies mdecl))
    | _ => [Some "not an inductive"]
    end
  | _ => [Some "not an inductive"]
  end.

(** The translated environment and the declaration that a quoted program's main term
    names, for the hand-built cases at the end. *)
Definition program_env (p : Ast.Env.program) : global_env :=
  PCUICProgram.trans_env_env (trans_global_env p.1).

Definition program_ind (p : Ast.Env.program) : inductive :=
  match p.2 with
  | Ast.tInd ind _ => ind
  | _ => {| inductive_mind := (MPfile [], ""); inductive_ind := 0 |}
  end.

Definition program_decl (p : Ast.Env.program) : mutual_inductive_body × one_inductive_body :=
  match env_lookup (program_env p) (program_ind p) with
  | Checked d => d
  | TypeError _ =>
    ({| ind_finite := Finite; ind_npars := 0; ind_params := []; ind_bodies := [];
        ind_universes := Monomorphic_ctx; ind_variance := None |},
     {| ind_name := ""; ind_indices := []; ind_sort := Sort.type0; ind_type := tSort Sort.type0;
        ind_kelim := IntoAny; ind_ctors := []; ind_projs := []; ind_relevance := Relevant |})
  end.

Inductive mlist (A : Set) : Set := mnil : mlist A | mcons : A -> mlist A -> mlist A.
Inductive mpair (A B : Set) : Set := mp : A -> B -> mpair A B.

(** * Accepted *)

Inductive rose := Node : list rose -> rose.
MetaRocq Quote Recursively Definition q_rose := rose.
Example Check_rose : positivity_answers q_rose = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive opt_tree := OptNode : option opt_tree -> nat -> opt_tree.
MetaRocq Quote Recursively Definition q_opt_tree := opt_tree.
Example Check_opt_tree : positivity_answers q_opt_tree = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive rose_pair : Set := NodeP : mlist (mpair nat rose_pair) -> rose_pair.
MetaRocq Quote Recursively Definition q_rose_pair := rose_pair.
Example Check_rose_pair : positivity_answers q_rose_pair = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive rose_prod := NodePr : list (prod nat rose_prod) -> rose_prod.
MetaRocq Quote Recursively Definition q_rose_prod := rose_prod.
Example Check_rose_prod : positivity_answers q_rose_prod = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive mprose (A : Set) : Set := MPNode : A -> mlist (mprose A) -> mprose A.
MetaRocq Quote Recursively Definition q_mprose := mprose.
Example Check_mprose : positivity_answers q_mprose = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive NU (A : Type) (n : nat) :=
| nu0 : NU A n
| nu1 : A -> NU A (S n) -> NU A n.
Inductive use_nu := UseNU : NU use_nu 0 -> use_nu.
MetaRocq Quote Recursively Definition q_use_nu := use_nu.
Example Check_use_nu : positivity_answers q_use_nu = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).
Inductive vtree := VNode : forall n, vec vtree n -> vtree.
MetaRocq Quote Recursively Definition q_vtree := vtree.
Example Check_vtree : positivity_answers q_vtree = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive mt1 := M1 : list mt2 -> mt1
with mt2 := M2 : mt1 -> mt2.
MetaRocq Quote Recursively Definition q_mt1 := mt1.
Example Check_mt1 : positivity_answers q_mt1 = [None; None].
Proof. vm_compute. reflexivity. Qed.

Inductive mW (A : Set) : Set := mw : mpair nat (mW A) -> mW A | mleaf : A -> mW A.
Inductive use_mw : Set := UseMW : mW use_mw -> use_mw.
MetaRocq Quote Recursively Definition q_use_mw := use_mw.
Example Check_use_mw : positivity_answers q_use_mw = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive mlet (A : Set) (B := mpair A A) : Set :=
| mlc : B -> mlet A -> mlet A
| mln : mlet A.
Inductive use_mlet : Set := UseMLet : mlet use_mlet -> use_mlet.
MetaRocq Quote Recursively Definition q_use_mlet := use_mlet.
Example Check_use_mlet : positivity_answers q_use_mlet = [None].
Proof. vm_compute. reflexivity. Qed.

Inductive mpair2 (A B : Set) (C : Set) : Set :=
| mp2 : A -> B -> mpair2 A B C
| mp2' : mpair2 A B (C -> C) -> mpair2 A B C.
Inductive use_mpair2 : Set := UseMP2 : mpair2 use_mpair2 nat bool -> use_mpair2.
MetaRocq Quote Recursively Definition q_use_mpair2 := use_mpair2.
Example Check_use_mpair2 : positivity_answers q_use_mpair2 = [None].
Proof. vm_compute. reflexivity. Qed.

(** * Refused, each with its message *)

#[bypass_check(positivity)]
Inductive bad_plain := BadPlain : (bad_plain -> nat) -> bad_plain.
MetaRocq Quote Recursively Definition q_bad_plain := bad_plain.
Example Check_bad_plain : positivity_answers q_bad_plain = [Some "Non-positive occurrence."].
Proof. vm_compute. reflexivity. Qed.

#[bypass_check(positivity)]
Inductive bad_nested := BadNested : list (bad_nested -> nat) -> bad_nested.
MetaRocq Quote Recursively Definition q_bad_nested := bad_nested.
Example Check_bad_nested : positivity_answers q_bad_nested = [Some "Non-positive occurrence."].
Proof. vm_compute. reflexivity. Qed.

#[bypass_check(positivity)]
Inductive bad_nested2 : Set := BadNested2 : mlist (mpair nat (bad_nested2 -> False)) -> bad_nested2.
MetaRocq Quote Recursively Definition q_bad_nested2 := bad_nested2.
Example Check_bad_nested2 : positivity_answers q_bad_nested2 = [Some "Non-positive occurrence."].
Proof. vm_compute. reflexivity. Qed.

Inductive T (A : Type) := TC : A -> T A | TD : T (A -> False) -> T A.
#[bypass_check(positivity)]
Inductive bad_nonunif := BadNonUnif : T bad_nonunif -> bad_nonunif.
MetaRocq Quote Recursively Definition q_bad_nonunif := bad_nonunif.
Example Check_bad_nonunif : positivity_answers q_bad_nonunif =
  [Some "Nested positivity: the block occurs in an argument that is not a uniform parameter"].
Proof. vm_compute. reflexivity. Qed.

Inductive mI : Set -> Set := mic : mI nat.
#[bypass_check(positivity)]
Inductive bad_index : Set := BadIndex : mI bad_index -> bad_index.
MetaRocq Quote Recursively Definition q_bad_index := bad_index.
Example Check_bad_index : positivity_answers q_bad_index =
  [Some "Nested positivity: the block occurs in an argument that is not a uniform parameter"].
Proof. vm_compute. reflexivity. Qed.

Inductive T2 (A B : Set) : Set := c2 : T2 B A -> T2 A B.
#[bypass_check(positivity)]
Inductive bad_swap : Set := BadSwap : T2 bad_swap bad_swap -> bad_swap.
MetaRocq Quote Recursively Definition q_bad_swap := bad_swap.
Example Check_bad_swap : positivity_answers q_bad_swap =
  [Some "Nested positivity: the block occurs in an argument that is not a uniform parameter"].
Proof. vm_compute. reflexivity. Qed.

Inductive T1 (A : Set) : Set := c1 : T1 nat -> T1 A.
#[bypass_check(positivity)]
Inductive bad_fixed : Set := BadFixed : T1 bad_fixed -> bad_fixed.
MetaRocq Quote Recursively Definition q_bad_fixed := bad_fixed.
Example Check_bad_fixed : positivity_answers q_bad_fixed =
  [Some "Nested positivity: the block occurs in an argument that is not a uniform parameter"].
Proof. vm_compute. reflexivity. Qed.

Definition L (A : Set) : Set := mlist A.
Inductive via_const : Set := VC : L via_const -> via_const.
MetaRocq Quote Recursively Definition q_via_const := via_const.
Example Check_via_const : positivity_answers q_via_const =
  [Some "Positivity: the block occurs under a head that is neither a member of the block nor an inductive"].
Proof. vm_compute. reflexivity. Qed.

(* The block occurs under a parameter of the block, a variable that is neither a member
   of the block nor an enclosing nesting inductive. *)
#[bypass_check(positivity)]
Inductive bad_param (F : Type -> Type) : Type := BadParam : F (bad_param F) -> bad_param F.
MetaRocq Quote Recursively Definition q_bad_param := bad_param.
Example Check_bad_param : positivity_answers q_bad_param =
  [Some "Positivity: the block occurs in an argument of a variable that is not an inductive of the block"].
Proof. vm_compute. reflexivity. Qed.

(* A cumulative block with a covariant universe level, nested in [list]. The kernel
   accepts it. The rule refuses it, because the arguments of an inductive application
   are compared by conversion, so [list cov@{u}] is not a subtype of [list cov@{u'}]
   even when [u <= u']. *)
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Inductive cov@{u} : Type@{u+1} := Cov : Type@{u} -> list cov -> cov.
Unset Polymorphic Inductive Cumulativity.
Unset Universe Polymorphism.
MetaRocq Quote Recursively Definition q_cov := cov.
Example Check_cov : positivity_answers q_cov =
  [Some "Nested positivity: the block has a covariant universe level"].
Proof. vm_compute. reflexivity. Qed.

(* Nesting in a primitive array. The kernel accepts it; the rule does not support it. *)
From Corelib Require Import PrimArray.
Inductive arr_tree := ANode : array arr_tree -> arr_tree.
MetaRocq Quote Recursively Definition q_arr_tree := arr_tree.
Example Check_arr_tree : positivity_answers q_arr_tree =
  [Some "Positivity: the block occurs under a head that is neither a member of the block nor an inductive"].
Proof. vm_compute. reflexivity. Qed.

(** * Refused, hand-built

  Rocq's kernel refuses the two shapes below even with its positivity check bypassed, so
  no Rocq declaration has them. A program handed to the checker can, so the checker is
  run on hand-built constructor types. The block being checked is [rose]'s (one body,
  monomorphic); its constructor type is [N (Rel 0) -> Rel 1], where [N] is the nesting
  inductive and [Rel 0] / [Rel 1] is the block. *)

Definition nested_cstr_type (ind : inductive) : term :=
  tProd nested_binder (mkApps (tInd ind []) [tRel 0]) (tRel 1).

(* The nesting inductive is a mutual block. *)
Inductive tl (A : Type) := tn : tl A | tc : A -> tl2 A -> tl A
with tl2 (A : Type) := t2 : tl A -> tl2 A.
MetaRocq Quote Recursively Definition q_tl := tl.
Example Check_mutual_outer :
  answer (env_lookup (program_env q_tl)) (fst (program_decl q_rose)) 0
    (nested_cstr_type (program_ind q_tl)) =
  Some "Nested positivity: the nested inductive is mutual".
Proof. vm_compute. reflexivity. Qed.

(* A constructor of the nesting inductive does not conclude at the nesting inductive.
   [with_ctor_type decl t] is the declaration [decl] with its constructors replaced by
   one of type [t]. *)
Definition with_ctor_type (d : mutual_inductive_body × one_inductive_body) (t : term) :
  mutual_inductive_body × one_inductive_body :=
  let '(mdecl', idecl') := d in
  let ctor := {| cstr_name := "bad"; cstr_args := []; cstr_indices := [];
                 cstr_type := t; cstr_arity := 0 |} in
  let idecl'' := {| ind_name := ind_name idecl'; ind_indices := ind_indices idecl';
                    ind_sort := ind_sort idecl'; ind_type := ind_type idecl';
                    ind_kelim := ind_kelim idecl'; ind_ctors := [ctor];
                    ind_projs := ind_projs idecl'; ind_relevance := ind_relevance idecl' |} in
  ({| ind_finite := ind_finite mdecl'; ind_npars := ind_npars mdecl';
      ind_params := ind_params mdecl'; ind_bodies := [idecl''];
      ind_universes := ind_universes mdecl'; ind_variance := ind_variance mdecl' |}, idecl'').

(* The conclusion is not a variable: [mlist] with one constructor of type
   [forall (A : Set), Set]. *)
MetaRocq Quote Recursively Definition q_mlist := mlist.
Definition bad_concl_decl := with_ctor_type (program_decl q_mlist)
  (it_mkProd_or_LetIn (ind_params (fst (program_decl q_mlist))) (tSort Sort.type0)).
Example Check_wrong_conclusion :
  answer (fun _ => ret bad_concl_decl) (fst (program_decl q_rose)) 0
    (nested_cstr_type (program_ind q_mlist)) =
  Some "Nested positivity: a constructor of the nesting inductive does not conclude at its own instance".
Proof. vm_compute. reflexivity. Qed.

(* The conclusion is a variable, but not the nesting inductive: [mpair] with one
   constructor of type [forall (A B : Set), B], nested through its first parameter
   only, so that [B] is pushed as a plain variable. *)
MetaRocq Quote Recursively Definition q_mpair := mpair.
Definition bad_concl_var_decl := with_ctor_type (program_decl q_mpair)
  (it_mkProd_or_LetIn (ind_params (fst (program_decl q_mpair))) (tRel 0)).
Example Check_wrong_conclusion_variable :
  answer (fun _ => ret bad_concl_var_decl) (fst (program_decl q_rose)) 0
    (nested_cstr_type (program_ind q_mpair)) =
  Some "Nested positivity: a constructor of the nesting inductive does not conclude at its own instance".
Proof. vm_compute. reflexivity. Qed.
