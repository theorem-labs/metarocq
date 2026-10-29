(* Tests of the table of distances that the canonical abstract environment stores with its
   universe graph ([wGraph.pf_table]).

   The environment is built as the checker builds it: [check_univs] checks a set of global
   universes and builds the environment with [abstract_env_init], which builds the table;
   [abstract_env_empty_ext] extends it for a monomorphic declaration and copies the table.
   Each comparison [abstract_env_leqb_level_n] then reads the table. The tests check by
   [vm_compute] that the table has a row for every vertex, so that every comparison below
   reads a row, and that every comparison answers as the untabled query [leqb_level_n_ix] on
   the same index, and as the constraints say. *)

From MetaRocq.Utils Require Import utils CanonicalTries.
From MetaRocq.Common Require Import config Universes Environment uGraph.
From MetaRocq.PCUIC Require Import PCUICSN.
From MetaRocq.SafeChecker Require Import PCUICErrors PCUICWfEnv PCUICWfEnvImpl PCUICSafeChecker.

Local Open Scope bs_scope.
Local Existing Instance default_checker_flags.
Local Existing Instance PCUICSN.default_normalizing.
Local Existing Instance real_guard_impl.

Definition ut_a := Level.level "a".
Definition ut_b := Level.level "b".
Definition ut_c := Level.level "c".
Definition ut_d := Level.level "d".
Definition ut_e := Level.level "e".
Definition ut_f := Level.level "f".
(** Not a global level. *)
Definition ut_off := Level.level "off".

(** [a < b <= c], [a <= d < e <= c], and [f] unrelated: two paths from [a] to [c] with
    different weights. *)
Definition ut_univs : ContextSet.t :=
  (LevelSetProp.of_list [Level.lzero; ut_a; ut_b; ut_c; ut_d; ut_e; ut_f],
   ConstraintSetProp.of_list
     [(ut_a, ConstraintType.Le 1, ut_b); (ut_b, ConstraintType.Le 0, ut_c);
      (ut_a, ConstraintType.Le 0, ut_d); (ut_d, ConstraintType.Le 1, ut_e);
      (ut_e, ConstraintType.Le 0, ut_c)]).

Definition ut_env : option reference_impl :=
  match check_univs canonical_abstract_env_impl ut_univs Retroknowledge.empty with
  | CorrectDecl (exist X _) => Some X
  | EnvError _ _ => None
  end.

Definition ut_ext : option reference_impl_ext :=
  option_map (fun X => abstract_env_empty_ext (X_type := canonical_abstract_env_impl) X) ut_env.

Definition ut_levels := [Level.lzero; ut_a; ut_b; ut_c; ut_d; ut_e; ut_f; ut_off].

(** Every global level has a key in the index, and every key has a row in the table. *)
Definition ut_all_rows (X : reference_impl_ext) : bool :=
  forallb (fun l =>
    match wGraph.VMap.find l (wGraph.ix_lookup (reference_impl_ext_index X)) with
    | Some k =>
        match PTree.get k (reference_impl_ext_table X) with Some _ => true | None => false end
    | None => if Level.eq_dec l ut_off then true else false
    end) ut_levels.

Lemma ut_rows : option_map ut_all_rows ut_ext = Some true.
Proof. vm_compute. reflexivity. Qed.

(** Every comparison of two levels of [ut_levels] at a weight from -2 to 2. *)
Definition ut_cases : list (Z * Level.t * Level.t) :=
  flat_map (fun n => flat_map (fun l => map (fun l' => (n, l, l')) ut_levels) ut_levels)
    [(-2)%Z; (-1)%Z; 0%Z; 1%Z; 2%Z].

Definition ut_same (X : reference_impl_ext) : bool :=
  forallb (fun '(n, l, l') =>
    Bool.eqb (abstract_env_leqb_level_n X n l l')
      (leqb_level_n_ix (reference_impl_ext_index X) n l l')) ut_cases.

Lemma ut_tabled_eq_untabled : option_map ut_same ut_ext = Some true.
Proof. vm_compute. reflexivity. Qed.

(** The answers of the tabled query, as the constraints give them. *)
Definition ut_answers (X : reference_impl_ext) : list bool :=
  map (fun '(n, l, l') => abstract_env_leqb_level_n X n l l')
    [(1%Z, ut_a, ut_c); (2%Z, ut_a, ut_c); (1%Z, ut_a, ut_e); (2%Z, ut_a, ut_e);
     (0%Z, ut_c, ut_a); (1%Z, Level.lzero, ut_f); (0%Z, ut_f, ut_c); (0%Z, ut_off, ut_off);
     (0%Z, ut_a, ut_off)].

Lemma ut_expected :
  option_map ut_answers ut_ext =
    Some [true; false; true; false; false; true; false; true; false].
Proof. vm_compute. reflexivity. Qed.
