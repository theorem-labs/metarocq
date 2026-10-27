(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config BasicAst Universes Environment.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICGuardChecker.

Local Open Scope bs_scope.

(** * Regression checks for the guard checker

  Each [Example] below runs [check_guard_gen] on a fixpoint or cofixpoint
  block, so the [pcuic] build fails if a version of the checker accepts one of
  these unsafe blocks, or refuses one of the three safe controls.

  The environment and the blocks are PCUIC terms obtained by quoting the
  Gallina sources given in the comments and translating them to PCUIC; the
  kernel names are renamed to the module path [Regress], universe levels are
  replaced by [Sort.type0] and universe instances are empty.  Each block is
  checked at the top level ([n = 0]), on its stripped form, as the safe
  checker calls it. *)

Definition mp : modpath := MPfile ["Regress"].
Definition kn (s : ident) : kername := (mp, s).
Definition ind (s : ident) : inductive := {| inductive_mind := kn s; inductive_ind := 0 |}.
Definition tind (s : ident) : term := tInd (ind s) [].
Definition tcstr (s : ident) (c : nat) : term := tConstruct (ind s) c [].
Definition anon : aname := {| binder_name := nAnon; binder_relevance := Relevant |}.
Definition nm (s : ident) : aname := {| binder_name := nNamed s; binder_relevance := Relevant |}.

Definition is_reject (r : guard_result) : bool :=
  match r with Reject _ => true | _ => false end.

(** ** The environment *)

(** [Inductive nat := O | S (n : nat)]. *)
Definition nat_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := Finite;
      ind_npars := 0;
      ind_params := [];
      ind_bodies :=
        [{|
           ind_name := "nat";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tSort Sort.type0;
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "O";
                cstr_args := [];
                cstr_indices := [];
                cstr_type := tRel 0;
                cstr_arity := 0
              |};
              {|
                cstr_name := "S";
                cstr_args := [vass anon (tRel 0)];
                cstr_indices := [];
                cstr_type := tProd anon (tRel 0) (tRel 1);
                cstr_arity := 1
              |}];
           ind_projs := [];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [CoInductive Stream := Cons : nat -> Stream -> Stream]. *)
Definition stream_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := CoFinite;
      ind_npars := 0;
      ind_params := [];
      ind_bodies :=
        [{|
           ind_name := "Stream";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tSort Sort.type0;
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "Cons";
                cstr_args := [vass anon (tRel 1); vass anon (tind "nat")];
                cstr_indices := [];
                cstr_type := tProd anon (tind "nat") (tProd anon (tRel 1) (tRel 2));
                cstr_arity := 2
              |}];
           ind_projs := [];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [CoFixpoint zeros : Stream := Cons 0 zeros]. *)
Definition zeros_decl : global_decl :=
  ConstantDecl
    {|
      cst_type := tind "Stream";
      cst_body :=
        Some
          (tCoFix
             [{|
                dname := nm "zeros";
                dtype := tind "Stream";
                dbody := tApp (tApp (tcstr "Stream" 0) (tcstr "nat" 0)) (tRel 0);
                rarg := 0
              |}]
             0);
      cst_universes := Monomorphic_ctx;
      cst_relevance := Relevant
    |}.

(** [Inductive box := Box : nat -> box]. *)
Definition box_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := Finite;
      ind_npars := 0;
      ind_params := [];
      ind_bodies :=
        [{|
           ind_name := "box";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tSort Sort.type0;
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "Box";
                cstr_args := [vass anon (tind "nat")];
                cstr_indices := [];
                cstr_type := tProd anon (tind "nat") (tRel 1);
                cstr_arity := 1
              |}];
           ind_projs := [];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [Record pr := mk { fst' : nat; snd' : Stream }], with primitive projections. *)
Definition pr_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := BiFinite;
      ind_npars := 0;
      ind_params := [];
      ind_bodies :=
        [{|
           ind_name := "pr";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tSort Sort.type0;
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "mk";
                cstr_args := [vass (nm "snd'") (tind "Stream"); vass (nm "fst'") (tind "nat")];
                cstr_indices := [];
                cstr_type :=
                  tProd (nm "fst'") (tind "nat") (tProd (nm "snd'") (tind "Stream") (tRel 2));
                cstr_arity := 2
              |}];
           ind_projs :=
             [{| proj_name := "fst'"; proj_relevance := Relevant; proj_type := tind "nat" |};
              {|
                proj_name := "snd'"; proj_relevance := Relevant; proj_type := tind "Stream"
              |}];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [Inductive T := C : Str T -> T]: [T] is nested in the coinductive [Str]. *)
Definition t_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := Finite;
      ind_npars := 0;
      ind_params := [];
      ind_bodies :=
        [{|
           ind_name := "T";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tSort Sort.type0;
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "C";
                cstr_args := [vass anon (tApp (tind "Str") (tRel 0))];
                cstr_indices := [];
                cstr_type := tProd anon (tApp (tind "Str") (tRel 0)) (tRel 1);
                cstr_arity := 1
              |}];
           ind_projs := [];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [CoInductive Str (A : Type) := SCons : A -> Str A -> Str A]. *)
Definition str_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := CoFinite;
      ind_npars := 1;
      ind_params := [vass (nm "A") (tSort Sort.type0)];
      ind_bodies :=
        [{|
           ind_name := "Str";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tProd (nm "A") (tSort Sort.type0) (tSort Sort.type0);
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "SCons";
                cstr_args := [vass anon (tApp (tRel 2) (tRel 1)); vass anon (tRel 0)];
                cstr_indices := [];
                cstr_type :=
                  tProd (nm "A") (tSort Sort.type0)
                    (tProd anon (tRel 0)
                       (tProd anon (tApp (tRel 2) (tRel 1)) (tApp (tRel 3) (tRel 2))));
                cstr_arity := 2
              |}];
           ind_projs := [];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [CoInductive S := mkS { hd : nat; tl : S }], with primitive projections. *)
Definition s_decl : global_decl :=
  InductiveDecl
    {|
      ind_finite := CoFinite;
      ind_npars := 0;
      ind_params := [];
      ind_bodies :=
        [{|
           ind_name := "S";
           ind_indices := [];
           ind_sort := Sort.type0;
           ind_type := tSort Sort.type0;
           ind_kelim := IntoAny;
           ind_ctors :=
             [{|
                cstr_name := "mkS";
                cstr_args := [vass (nm "tl") (tRel 1); vass (nm "hd") (tind "nat")];
                cstr_indices := [];
                cstr_type :=
                  tProd (nm "hd") (tind "nat") (tProd (nm "tl") (tRel 1) (tRel 2));
                cstr_arity := 2
              |}];
           ind_projs :=
             [{| proj_name := "hd"; proj_relevance := Relevant; proj_type := tind "nat" |};
              {| proj_name := "tl"; proj_relevance := Relevant; proj_type := tind "S" |}];
           ind_relevance := Relevant
         |}];
      ind_universes := Monomorphic_ctx;
      ind_variance := None
    |}.

(** [CoFixpoint zs : S := mkS 0 zs]. *)
Definition zs_decl : global_decl :=
  ConstantDecl
    {|
      cst_type := tind "S";
      cst_body :=
        Some
          (tCoFix
             [{|
                dname := nm "zs";
                dtype := tind "S";
                dbody := tApp (tApp (tcstr "S" 0) (tcstr "nat" 0)) (tRel 0);
                rarg := 0
              |}]
             0);
      cst_universes := Monomorphic_ctx;
      cst_relevance := Relevant
    |}.

Definition Σ : global_env :=
  {| universes := ContextSet.empty;
     declarations :=
       [(kn "zs", zs_decl); (kn "S", s_decl);
        (kn "Str", str_decl); (kn "T", t_decl); (kn "pr", pr_decl); (kn "box", box_decl);
        (kn "zeros", zeros_decl); (kn "Stream", stream_decl); (kn "nat", nat_decl)];
     retroknowledge := Retroknowledge.empty |}.

(** ** An inductive nested in a coinductive

  [fix t_f (x : T) : nat := match x with C y => match y with SCons t _ => t_f t end end]
  and [cofix t_s : Str T := SCons T (C t_s) t_s].

  [t_f] calls itself on [t], which it takes out of [y : Str T] by a match on a
  coinductive value; [t_s] calls itself inside [C t_s], an argument of [SCons]
  that is not a recursive argument of [Str].  Together they loop:
  [t_f (C t_s)] matches [C t_s], then unfolds [t_s] to [SCons T (C t_s) t_s],
  takes [t := C t_s], and calls [t_f (C t_s)] again.  So at least one of the
  two blocks must be refused, whatever the fixpoint and cofixpoint rules are. *)

Definition tf_block : mfixpoint term :=
  [{|
     dname := nm "t_f";
     dtype := tProd (nm "x") (tind "T") (tind "nat");
     dbody :=
       tLambda (nm "x") (tind "T")
         (tCase {| ci_ind := ind "T"; ci_npar := 0; ci_relevance := Relevant |}
            {|
              pparams := [];
              puinst := [];
              pcontext := [vass (nm "x") (tind "T")];
              preturn := tind "nat"
            |} (tRel 0)
            [{|
               bcontext := [vass (nm "y") (tApp (tind "Str") (tind "T"))];
               bbody :=
                 tCase {| ci_ind := ind "Str"; ci_npar := 1; ci_relevance := Relevant |}
                   {|
                     pparams := [tind "T"];
                     puinst := [];
                     pcontext := [vass (nm "y") (tApp (tind "Str") (tRel 0))];
                     preturn := tind "nat"
                   |} (tRel 0)
                   [{|
                      bcontext :=
                        [vass (nm "s") (tApp (tind "Str") (tRel 1)); vass (nm "t") (tRel 0)];
                      bbody := tApp (tRel 4) (tRel 1)
                    |}]
             |}]);
     rarg := 0
   |}].

Definition ts_block : mfixpoint term :=
  [{|
     dname := nm "t_s";
     dtype := tApp (tind "Str") (tind "T");
     dbody :=
       tApp (tApp (tApp (tcstr "Str" 0) (tind "T")) (tApp (tcstr "T" 0) (tRel 0))) (tRel 0);
     rarg := 0
   |}].

(** Each half is refused on its own.  The loop needs both a subterm taken
    through a match on a coinductive and a cofixpoint call in a non-recursive
    constructor argument; either rule alone breaks it, and both are kept and
    asserted, so that a later change to one rule cannot open the pair. *)
Example nested_coinductive_fix_half_refused :
  is_reject (check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 Fix 0 (strip_mfix tf_block)) = true.
Proof. vm_compute. reflexivity. Qed.

Example nested_coinductive_cofix_half_refused :
  is_reject (check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0 (strip_mfix ts_block)) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Corecursive calls in parts that a reduction step discards

  In each block the corecursive call [g] sits under a [match] or a
  projection, not under a constructor, inside a part of the body that one
  reduction step throws away.  A rule that reduced first and checked only the
  reduct would never see the call; the call is not guarded, so the block must
  be refused. *)

(** [cofix g : Stream := (fix h (k s : nat) {struct k} : Stream := Cons 0 zeros) O
       (match g with Cons a _ => a end)]: unfolding [h] discards its argument [s]. *)
Definition g_fix_block : mfixpoint term :=
  [{|
     dname := nm "g";
     dtype := tind "Stream";
     dbody :=
       tApp
         (tApp
            (tFix
               [{|
                  dname := nm "h";
                  dtype :=
                    tProd (nm "k") (tind "nat") (tProd (nm "s") (tind "nat") (tind "Stream"));
                  dbody :=
                    tLambda (nm "k") (tind "nat")
                      (tLambda (nm "s") (tind "nat")
                         (tApp (tApp (tcstr "Stream" 0) (tcstr "nat" 0))
                            (tConst (kn "zeros") [])));
                  rarg := 0
                |}]
               0)
            (tcstr "nat" 0))
         (tCase {| ci_ind := ind "Stream"; ci_npar := 0; ci_relevance := Relevant |}
            {|
              pparams := [];
              puinst := [];
              pcontext := [vass (nm "g") (tind "Stream")];
              preturn := tind "nat"
            |} (tRel 0)
            [{|
               bcontext := [vass (nm "s") (tind "Stream"); vass (nm "a") (tind "nat")];
               bbody := tRel 1
             |}]);
     rarg := 0
   |}].

Example cofix_call_in_discarded_fix_argument_refused :
  is_reject (check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0 (strip_mfix g_fix_block))
  = true.
Proof. vm_compute. reflexivity. Qed.

(** [cofix g : Stream := match Box (match g with Cons a _ => a end) with Box _ => Cons 0 zeros end]:
    ι-reduction discards the constructor argument that the branch does not use. *)
Definition g_iota_block : mfixpoint term :=
  [{|
     dname := nm "g";
     dtype := tind "Stream";
     dbody :=
       tCase {| ci_ind := ind "box"; ci_npar := 0; ci_relevance := Relevant |}
         {|
           pparams := [];
           puinst := [];
           pcontext := [vass (nm "x") (tind "box")];
           preturn := tind "Stream"
         |}
         (tApp (tcstr "box" 0)
            (tCase {| ci_ind := ind "Stream"; ci_npar := 0; ci_relevance := Relevant |}
               {|
                 pparams := [];
                 puinst := [];
                 pcontext := [vass (nm "g") (tind "Stream")];
                 preturn := tind "nat"
               |} (tRel 0)
               [{|
                  bcontext := [vass (nm "s") (tind "Stream"); vass (nm "a") (tind "nat")];
                  bbody := tRel 1
                |}]))
         [{|
            bcontext := [vass (nm "n") (tind "nat")];
            bbody := tApp (tApp (tcstr "Stream" 0) (tcstr "nat" 0)) (tConst (kn "zeros") [])
          |}];
     rarg := 0
   |}].

Example cofix_call_in_discarded_constructor_argument_refused :
  is_reject (check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0 (strip_mfix g_iota_block))
  = true.
Proof. vm_compute. reflexivity. Qed.

(** [cofix g : Stream := (mk (match g with Cons a _ => a end) (Cons 0 zeros)).(snd')]:
    the projection discards the other field. *)
Definition g_proj_block : mfixpoint term :=
  [{|
     dname := nm "g";
     dtype := tind "Stream";
     dbody :=
       tProj {| proj_ind := ind "pr"; proj_npars := 0; proj_arg := 1 |}
         (tApp
            (tApp (tcstr "pr" 0)
               (tCase {| ci_ind := ind "Stream"; ci_npar := 0; ci_relevance := Relevant |}
                  {|
                    pparams := [];
                    puinst := [];
                    pcontext := [vass (nm "g") (tind "Stream")];
                    preturn := tind "nat"
                  |} (tRel 0)
                  [{|
                     bcontext := [vass (nm "s") (tind "Stream"); vass (nm "a") (tind "nat")];
                     bbody := tRel 1
                   |}]))
            (tApp (tApp (tcstr "Stream" 0) (tcstr "nat" 0)) (tConst (kn "zeros") [])));
     rarg := 0
   |}].

Example cofix_call_in_discarded_field_refused :
  is_reject (check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0 (strip_mfix g_proj_block))
  = true.
Proof. vm_compute. reflexivity. Qed.

(** [cofix g : S := (fun _ : nat => mkS 0 zs) (hd g)], where [S] is
    [CoInductive S := mkS { hd : nat; tl : S }] with primitive projections:
    a corecursive call under a primitive projection, inside an argument that
    β discards.  Unfolding [g] under [hd] gives back a term that contains
    [hd g] again.  Unlike the blocks above, it has no [match] on a coinductive. *)
Definition g_beta_proj_block : mfixpoint term :=
  [{|
     dname := nm "g";
     dtype := tind "S";
     dbody :=
       tApp
         (tLambda anon (tind "nat")
            (tApp (tApp (tcstr "S" 0) (tcstr "nat" 0)) (tConst (kn "zs") [])))
         (tProj {| proj_ind := ind "S"; proj_npars := 0; proj_arg := 0 |} (tRel 0));
     rarg := 0
   |}].

Example cofix_call_under_projection_in_discarded_argument_refused :
  is_reject (check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0
               (strip_mfix g_beta_proj_block))
  = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Controls: three guarded blocks are accepted

  So the refusals above are not an artefact of the environment. *)

(** [cofix zeros : Stream := Cons 0 zeros]: the call is a recursive argument of [Cons]. *)
Definition zeros_block : mfixpoint term :=
  [{|
     dname := nm "zeros";
     dtype := tind "Stream";
     dbody := tApp (tApp (tcstr "Stream" 0) (tcstr "nat" 0)) (tRel 0);
     rarg := 0
   |}].

Example guarded_cofix_accepted :
  check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0 (strip_mfix zeros_block) = Accept.
Proof. vm_compute. reflexivity. Qed.

(** [fix f (n : nat) : nat := match n with O => O | S k => f k end]: a structural call. *)
Definition fnat_block : mfixpoint term :=
  [{|
     dname := nm "f";
     dtype := tProd (nm "n") (tind "nat") (tind "nat");
     dbody :=
       tLambda (nm "n") (tind "nat")
         (tCase {| ci_ind := ind "nat"; ci_npar := 0; ci_relevance := Relevant |}
            {|
              pparams := [];
              puinst := [];
              pcontext := [vass (nm "n") (tind "nat")];
              preturn := tind "nat"
            |} (tRel 0)
            [{| bcontext := []; bbody := tcstr "nat" 0 |};
             {| bcontext := [vass (nm "k") (tind "nat")]; bbody := tApp (tRel 2) (tRel 0) |}]);
     rarg := 0
   |}].

Example structural_fix_accepted :
  check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 Fix 0 (strip_mfix fnat_block) = Accept.
Proof. vm_compute. reflexivity. Qed.

(** [cofix g' : S := (fun _ : nat => mkS 0 g') 0]: the twin of
    [g_beta_proj_block], where the call is a recursive argument of [mkS] under
    a β-redex whose discarded argument holds no call. *)
Definition g'_beta_block : mfixpoint term :=
  [{|
     dname := nm "g'";
     dtype := tind "S";
     dbody :=
       tApp (tLambda anon (tind "nat") (tApp (tApp (tcstr "S" 0) (tcstr "nat" 0)) (tRel 1)))
         (tcstr "nat" 0);
     rarg := 0
   |}].

Example guarded_cofix_under_beta_accepted :
  check_guard_gen (lookup_env Σ) Σ.(retroknowledge) 30 CoFix 0 (strip_mfix g'_beta_block) = Accept.
Proof. vm_compute. reflexivity. Qed.
