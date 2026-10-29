(* Tests of the table of distances that the canonical abstract environment stores with its
   universe graph ([wGraph.pf_table]).

   The environment is built as the checker builds it: [check_univs] checks a set of global
   universes and builds the environment with [abstract_env_init], which builds the table;
   [abstract_env_empty_ext] extends it for a monomorphic declaration and copies the table.
   Each comparison [abstract_env_leqb_level_n] then reads the table. The tests check by
   [vm_compute] that the table has a row for every vertex, so that every comparison below
   reads a row, and that every comparison answers as the untabled query [leqb_level_n_ix] on
   the same index, and as the constraints say.

   The same checks run in the optimized environment ([optimized_abstract_env_impl], which the
   checker plugin uses). A last group of tests extends the environment for a polymorphic
   declaration with its own levels and constraints. That extension stores the empty table,
   so each comparison computes its distances; the tests check that it still answers as
   [leqb_level_n_ix] and as the constraints say, in both environments. *)

From MetaRocq.Utils Require Import utils CanonicalTries.
From MetaRocq.Common Require Import config BasicAst Kernames Universes Environment uGraph.
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

(** [a <= b <= c], [a <= d < e <= c], and [f] unrelated: two paths from [a] to [c], of
    weight 0 through [b] and of weight 1 through [d] and [e]. The row of [a] must give the
    longer one: [a + 1 <= c] holds, and [a + 2 <= c] does not. *)
Definition ut_univs : ContextSet.t :=
  (LevelSetProp.of_list [Level.lzero; ut_a; ut_b; ut_c; ut_d; ut_e; ut_f],
   ConstraintSetProp.of_list
     [(ut_a, ConstraintType.Le 0, ut_b); (ut_b, ConstraintType.Le 0, ut_c);
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

(** The distance from [l] to [l'] that the row of [l] in the table stores. *)
Definition ut_row_distance (X : reference_impl_ext) (l l' : Level.t) : option (option Z) :=
  let ix := reference_impl_ext_index X in
  match wGraph.VMap.find l (wGraph.ix_lookup ix), wGraph.VMap.find l' (wGraph.ix_lookup ix) with
  | Some k, Some k' =>
      option_map (fun row => wGraph.pf_lookup row k') (PTree.get k (reference_impl_ext_table X))
  | _, _ => None
  end.

(** The row of [a] gives the weight of the longer of the two paths to [c], 1, not 0. *)
Lemma ut_row_longer_path :
  option_map (fun X => ut_row_distance X ut_a ut_c) ut_ext = Some (Some (Some 1%Z)).
Proof. vm_compute. reflexivity. Qed.

(** * The checker's steps, in the canonical and the optimized environments *)

Definition ut_kn : kername := (MPfile ["univ_table"], "decl").

(** The extension for a declaration with universes [udecl], built as the checker builds it:
    [check_univs] on [ut_univs] in the environment [X_type], then [make_abstract_env_ext]. *)
Definition ut_ext_in (X_type : abstract_env_impl) (udecl : universes_decl)
  : option (X_env_ext_type X_type) :=
  match check_univs X_type ut_univs Retroknowledge.empty with
  | CorrectDecl (exist X _) =>
      match make_abstract_env_ext X_type X ut_kn udecl with
      | CorrectDecl (exist X' _) => Some X'
      | EnvError _ _ => None
      end
  | EnvError _ _ => None
  end.

(** For the levels [levels]: how many have a key in the index, how many of these keys have a
    row in the table, and whether the table has no row at all. *)
Definition ut_row_counts (levels : list Level.t) (X : reference_impl_ext) : nat * nat * bool :=
  let keys :=
    flat_map (fun l =>
      match wGraph.VMap.find l (wGraph.ix_lookup (reference_impl_ext_index X)) with
      | Some k => [k]
      | None => []
      end) levels in
  (List.length keys,
   List.length (List.filter (fun k =>
     match PTree.get k (reference_impl_ext_table X) with Some _ => true | None => false end) keys),
   match reference_impl_ext_table X with PTree.Empty => true | PTree.Nodes _ => false end).

(** Every comparison of two levels of [levels] at a weight from -2 to 2. *)
Definition ut_cases_of (levels : list Level.t) : list (Z * Level.t * Level.t) :=
  flat_map (fun n => flat_map (fun l => map (fun l' => (n, l, l')) levels) levels)
    [(-2)%Z; (-1)%Z; 0%Z; 1%Z; 2%Z].

(** The query [leqb] answers as the untabled query on the index [ix], on every comparison of
    two levels of [levels]. *)
Definition ut_same_on (levels : list Level.t) (leqb : Z -> Level.t -> Level.t -> bool)
  (ix : wGraph.index) : bool :=
  forallb (fun '(n, l, l') => Bool.eqb (leqb n l l') (leqb_level_n_ix ix n l l'))
    (ut_cases_of levels).

(** ** The optimized environment, for a monomorphic declaration *)

Definition ut_opt_mono : option wf_env_ext :=
  ut_ext_in optimized_abstract_env_impl Monomorphic_ctx.

(** The extension copies the global table: each of the 7 global levels has a key and a row. *)
Lemma ut_opt_rows :
  option_map (fun X : wf_env_ext => ut_row_counts ut_levels X) ut_opt_mono = Some (7, 7, false).
Proof. vm_compute. reflexivity. Qed.

Lemma ut_opt_tabled_eq_untabled :
  option_map (fun X : wf_env_ext =>
    ut_same_on ut_levels (abstract_env_leqb_level_n X) (reference_impl_ext_index X)) ut_opt_mono =
  Some true.
Proof. vm_compute. reflexivity. Qed.

(** ** A polymorphic declaration with its own levels and constraints: the empty table *)

Definition ut_i := Level.lvar 0.
Definition ut_j := Level.lvar 1.

(** [a <= i < j <= c]: two levels [i] and [j] of the declaration, between [a] and [c]. *)
Definition ut_poly : universes_decl :=
  Polymorphic_ctx ([nNamed "i"; nNamed "j"],
    ConstraintSetProp.of_list
      [(ut_a, ConstraintType.Le 0, ut_i); (ut_i, ConstraintType.Le 1, ut_j);
       (ut_j, ConstraintType.Le 0, ut_c)]).

Definition ut_poly_levels := app ut_levels [ut_i; ut_j].

Definition ut_can_poly : option reference_impl_ext :=
  ut_ext_in canonical_abstract_env_impl ut_poly.

Definition ut_opt_poly : option wf_env_ext := ut_ext_in optimized_abstract_env_impl ut_poly.

(** The index has a key for the 7 global levels and for [i] and [j], and the table has no
    row. *)
Lemma ut_poly_no_rows :
  option_map (fun X : reference_impl_ext => ut_row_counts ut_poly_levels X) ut_can_poly =
    Some (9, 0, true) /\
  option_map (fun X : wf_env_ext => ut_row_counts ut_poly_levels X) ut_opt_poly =
    Some (9, 0, true).
Proof. split; vm_compute; reflexivity. Qed.

Lemma ut_poly_tabled_eq_untabled :
  option_map (fun X : reference_impl_ext =>
    ut_same_on ut_poly_levels (abstract_env_leqb_level_n X) (reference_impl_ext_index X))
    ut_can_poly = Some true /\
  option_map (fun X : wf_env_ext =>
    ut_same_on ut_poly_levels (abstract_env_leqb_level_n X) (reference_impl_ext_index X))
    ut_opt_poly = Some true.
Proof. split; vm_compute; reflexivity. Qed.

(** The answers of the query, as the constraints give them, on comparisons with [i] or [j]
    and on [a] and [c], whose longest path stays 1. *)
Definition ut_poly_answers (leqb : Z -> Level.t -> Level.t -> bool) : list bool :=
  map (fun '(n, l, l') => leqb n l l')
    [(1%Z, ut_i, ut_j); (2%Z, ut_i, ut_j); (1%Z, ut_a, ut_j); (2%Z, ut_a, ut_j);
     (0%Z, ut_j, ut_c); (1%Z, ut_j, ut_c); (0%Z, ut_c, ut_i); (0%Z, ut_i, ut_f);
     (1%Z, ut_a, ut_c); (2%Z, ut_a, ut_c)].

Lemma ut_poly_expected :
  option_map (fun X : reference_impl_ext => ut_poly_answers (abstract_env_leqb_level_n X))
    ut_can_poly =
    Some [true; false; true; false; true; false; false; false; true; false] /\
  option_map (fun X : wf_env_ext => ut_poly_answers (abstract_env_leqb_level_n X))
    ut_opt_poly =
    Some [true; false; true; false; true; false; false; false; true; false].
Proof. split; vm_compute; reflexivity. Qed.
