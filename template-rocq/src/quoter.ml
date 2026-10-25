open Names
open Entries
open Declarations
open Pp

open Tm_util
open Reification

let inductive_sort mip = mip.mind_sort

let cast_prop = ref (false)

(* whether Set Template Cast Propositions is on, as needed for erasure in Certicoq *)
let is_cast_prop () = !cast_prop

let metarocq_cat = match CWarnings.get_category "metarocq" with
  | There c -> c
  | OtherType -> assert false
  | NotThere -> CWarnings.create_category ~name:"metarocq" ()

let make_warning_if_not_exist w =
  match CWarnings.get_warning w with
  | There w -> w
  | OtherType -> assert false (* used as category *)
  | NotThere -> CWarnings.create_warning ~name:w ~from:[metarocq_cat] ()

let warn_primitive_turned_into_axiom =
  CWarnings.create_in (make_warning_if_not_exist "primitive-turned-into-axiom")
          Pp.(fun prim -> str "Quoting primitive " ++ str prim ++ str " into an axiom.")

let warn_symbol_turned_into_axiom =
  CWarnings.create_in (make_warning_if_not_exist "symbol-turned-into-axiom")
          Pp.(fun prim -> str "Quoting symbol " ++ str prim ++ str " into an axiom.")
let warn_ignoring_private_polymorphic_universes =
  CWarnings.create_in (make_warning_if_not_exist "private-polymorphic-universes-ignored")
          Pp.(fun () -> str "Ignoring private polymorphic universes.")

let toDecl (old: Name.t Constr.binder_annot * ((Constr.constr) option) * Constr.constr) : Constr.rel_declaration =
  let (name,value,typ) = old in
  match value with
  | Some value -> Context.Rel.Declaration.LocalDef (name,value,typ)
  | None -> Context.Rel.Declaration.LocalAssum (name,typ)

let getType env (t:Constr.t) : Constr.t =
    EConstr.to_constr Evd.empty (Retyping.get_type_of env Evd.empty (EConstr.of_constr t))

let hnf_type env ty =
  let rec hnf_type continue ty =
    match Constr.kind ty with
      Constr.Prod (n,t,b) -> Constr.mkProd (n,t,hnf_type true b)
    | Constr.LetIn _
      | Constr.Cast _
      | Constr.App _ when continue ->
       hnf_type false (Reduction.whd_all env ty)
    | _ -> ty
  in
  hnf_type true ty



module type BaseQuoter =
sig
  include Reification

  val mkRel : quoted_int -> t
  val mkVar : quoted_ident -> t
  val mkEvar : quoted_int -> t array -> t
  val mkSort : quoted_sort -> t
  val mkCast : t -> quoted_cast_kind -> t -> t
  val mkProd : quoted_aname -> t -> t -> t
  val mkLambda : quoted_aname -> t -> t -> t
  val mkLetIn : quoted_aname -> t -> t -> t -> t
  val mkApp : t -> t array -> t
  val mkConst : quoted_kernel_name -> quoted_univ_instance -> t
  val mkInd : quoted_inductive -> quoted_univ_instance -> t
  val mkConstruct : quoted_inductive * quoted_int -> quoted_univ_instance -> t
  val mkCase : (quoted_inductive * quoted_int * quoted_relevance) ->
    (quoted_univ_instance * t array * quoted_aname array * t) -> (* predicate: instance, params, binder names, return type *)
     t -> (quoted_aname array * t) list (* branches *) -> t
  val mkProj : quoted_proj -> t -> t
  val mkFix : (quoted_int array * quoted_int) * (quoted_aname array * t array * t array) -> t
  val mkCoFix : (quoted_int array * quoted_int) * (quoted_aname array * t array * t array) -> t
  val mkInt : quoted_int63 -> t
  val mkFloat : quoted_float64 -> t
  val mkString : quoted_pstring -> t
  val mkArray : quoted_univ_level -> t array -> default:t -> ty:t -> t

  val mkBindAnn : quoted_name -> quoted_relevance -> quoted_aname
  val mkName : quoted_ident -> quoted_name
  val mkAnon : unit -> quoted_name

  val quote_ident : Id.t -> quoted_ident
  val quote_name : Name.t -> quoted_name
  val quote_aname : Name.t Constr.binder_annot -> quoted_aname
  val quote_relevance : Sorts.relevance -> quoted_relevance
  val quote_int : int -> quoted_int
  val quote_bool : bool -> quoted_bool
  val quote_sort : Sorts.t -> quoted_sort
  val quote_sort_quality_or_set : UnivGen.QualityOrSet.t -> quoted_sort_quality_or_set
  val quote_cast_kind : Constr.cast_kind -> quoted_cast_kind
  val quote_kn : KerName.t -> quoted_kernel_name
  val quote_inductive : quoted_kernel_name * quoted_int -> quoted_inductive
  val quote_proj : quoted_inductive -> quoted_int -> quoted_int -> quoted_proj

  (* Primitive objects *)
  val quote_int63 : Uint63.t -> quoted_int63
  val quote_float64 : Float64.t -> quoted_float64
  val quote_pstring : Pstring.t -> quoted_pstring

  val quote_constraint_type : Univ.UnivConstraint.kind -> quoted_constraint_type
  val quote_univ_constraint : Univ.UnivConstraint.t -> quoted_univ_constraint
  val quote_univ_level : Univ.Level.t -> quoted_univ_level
  val quote_univ_instance : UVars.Instance.t -> quoted_univ_instance
  val quote_univ_constraints : Univ.UnivConstraints.t -> quoted_univ_constraints
  val quote_univ_context : UVars.UContext.t -> quoted_univ_context
  val quote_contextset : Univ.ContextSet.t -> quoted_contextset
  val quote_variance : UVars.Variance.t -> quoted_variance
  val quote_abstract_univ_context : UVars.AbstractContext.t -> quoted_abstract_univ_context

  val mkMonomorphic_entry : unit -> quoted_universes_entry
  val mkPolymorphic_entry : quoted_univ_context -> quoted_universes_entry

  val mkMonomorphic_ctx : unit -> quoted_universes_decl
  val mkPolymorphic_ctx : quoted_abstract_univ_context -> quoted_universes_decl

  val quote_mind_finiteness : Declarations.recursivity_kind -> quoted_mind_finiteness
  val quote_mutual_inductive_entry :
    quoted_mind_finiteness * quoted_context (* params *) * quoted_ind_entry list *
    quoted_universes_entry * quoted_variance option list option ->
    quoted_mind_entry

  val quote_definition_entry : t option -> t -> quoted_universes_entry -> quoted_definition_entry
  val quote_parameter_entry : t -> quoted_universes_entry -> quoted_parameter_entry
  val quote_constant_entry : (quoted_definition_entry, quoted_parameter_entry) sum -> quoted_constant_entry

  (* val quote_entry : (quoted_constant_entry, quoted_mind_entry) sum option > quoted_entry *)

  val quote_context_decl : quoted_aname -> t option -> t -> quoted_context_decl
  val quote_context : quoted_context_decl list -> quoted_context

  val mk_one_inductive_body :
    quoted_ident *
    quoted_context (* ind indices context *) *
    quoted_sort (* ind sort *) *
    t (* ind type *) *
    quoted_sort_quality_or_set *
    (quoted_ident * quoted_context (* arguments context *) *
      t list (* indices in the conclusion *) *
      t (* constr type *) *
      quoted_int (* arity (w/o lets) *)) list *
    (quoted_ident * quoted_relevance *  t (* projection type *)) list *
    quoted_relevance ->
    quoted_one_inductive_body

  val mk_mutual_inductive_body :
    quoted_mind_finiteness
    -> quoted_int (* number of params (no lets) *)
    -> quoted_context (* parameters context with lets *)
    -> quoted_one_inductive_body list
    -> quoted_universes_decl
    -> quoted_variance list option
    -> quoted_mutual_inductive_body

  val mk_constant_body : t (* type *) -> t option (* body *) -> quoted_universes_decl -> quoted_relevance -> quoted_constant_body

  val mk_inductive_decl : quoted_mutual_inductive_body -> quoted_global_decl

  val mk_constant_decl : quoted_constant_body -> quoted_global_decl

  val empty_global_declarations : unit -> quoted_global_declarations
  val add_global_decl : quoted_kernel_name -> quoted_global_decl -> quoted_global_declarations -> quoted_global_declarations

  type pre_quoted_retroknowledge =
    { retro_int63 : quoted_kernel_name option;
      retro_float64 : quoted_kernel_name option;
      retro_string : quoted_kernel_name option;
      retro_array : quoted_kernel_name option }

  val quote_retroknowledge : pre_quoted_retroknowledge -> quoted_retroknowledge

  val mk_global_env : quoted_contextset -> quoted_global_declarations -> quoted_retroknowledge -> quoted_global_env
  val mk_program : quoted_global_env -> t -> quoted_program
end



module Quoter (Q : BaseQuoter) =
struct

  let push_rel decl (in_prop, env) = (in_prop, Environ.push_rel decl env)
  let push_rel_context ctx (in_prop, env) = (in_prop, Environ.push_rel_context ctx env)

  let get_abstract_inductive_universes iu =
    match iu with
    | Declarations.Monomorphic -> UVars.UContext.empty
    | Polymorphic ctx -> UVars.AbstractContext.repr ctx

  let template_inverse_substitution template =
    let bound_instance =
      UVars.UContext.instance
        (UVars.AbstractContext.repr template.template_context)
    in
    let _, bound_levels =
      UVars.Instance.to_array bound_instance
    in
    let _, default_levels =
      UVars.Instance.to_array template.template_defaults
    in
    let level_substitution =
      assert (Array.length default_levels = Array.length bound_levels);
      let rec add_levels index substitution =
        if index = Array.length default_levels then substitution
        else
          add_levels (index + 1)
            (Univ.Level.Map.add default_levels.(index) bound_levels.(index)
               substitution)
      in
      add_levels 0 Univ.Level.Map.empty
    in
    ((Sorts.QVar.Map.empty, level_substitution),
     UVars.Instance.of_array ([||], bound_levels))

  let named_template_context template =
    let { UVars.quals = _; UVars.univs } =
      UVars.AbstractContext.names template.template_context
    in
    let univs =
      Array.mapi
        (fun index _ ->
           Names.Name (Names.Id.of_string ("template" ^ string_of_int index)))
        univs
    in
    UVars.AbstractContext.make { UVars.quals = [||]; UVars.univs }
      (UVars.UContext.constraints
         (UVars.AbstractContext.repr template.template_context))

  type template_universe_context = {
    mutable universe_levels : Univ.Level.t Univ.Universe.Map.t;
    mutable fresh_definitions : Univ.Universe.t Univ.Level.Map.t;
    mutable fresh_levels : Univ.Level.Set.t;
    mutable fresh_constraints : Univ.UnivConstraints.t;
    mutable next_fresh_level : int;
    (* One global level strictly above every level of the quoted program
       ([quote_term_rec] adds [l < top] for each), used by
       [template_instance ~canonical]. *)
    mutable top_level : Univ.Level.t option;
  }

  let make_template_universe_context () = {
    universe_levels = Univ.Universe.Map.empty;
    fresh_definitions = Univ.Level.Map.empty;
    fresh_levels = Univ.Level.Set.empty;
    fresh_constraints = Univ.UnivConstraints.empty;
    next_fresh_level = 0;
    top_level = None;
  }

  let fresh_template_level graph context =
    let dirpath =
      Names.DirPath.make [Names.Id.of_string "MetaRocq";
                          Names.Id.of_string "Template"]
    in
    let rec fresh () =
      let index = context.next_fresh_level in
      context.next_fresh_level <- index + 1;
      let level =
        Univ.Level.make (Univ.UGlobal.make dirpath "algebraic" index)
      in
      match UGraph.check_declared_universes graph
              (Univ.Level.Set.singleton level) with
      | Ok () -> fresh ()
      | Error _ -> level
    in
    fresh ()

  (* Name of the declaration currently being quoted, used for diagnostics and
     to key the per-declaration extra-level table. *)
  let current_decl_name = ref "<toplevel>"

  (* Per-declaration scope for algebraic template universes whose components
     mention bound universe variables of the enclosing polymorphic
     declaration.  Such a universe cannot be replaced by a fresh *global*
     level (the global context forbids variable levels); instead we add a
     fresh *bound* level [Var (ls_n_orig + k)] to the declaration's own
     abstract universe context, lower-bounded by the components.  Every use
     site of the declaration then supplies, for that extra level, the
     component expression instantiated at the use's own universe instance
     (see [extend_instance_for_decl]). *)
  type local_scope = {
    ls_n_orig : int;
    mutable ls_memo : Univ.Level.t Univ.Universe.Map.t;
    mutable ls_definitions : Univ.Universe.t array;
    mutable ls_exprs : Univ.Universe.t list;        (* fresh-var exprs, reversed *)
    mutable ls_constraints : Univ.UnivConstraints.t;
    mutable ls_next : int;
  }

  let current_local_scope : local_scope option ref = ref None

  (* What the quoted value of one kernel subterm was computed from, besides the
     subterm itself and the global declarations.  [quote_term_remember] uses it
     to decide whether its cache may return that value at another occurrence of
     the same physical subterm; the argument is in the comment there.
     - [qd_depth] is [Environ.nb_rel] of the environment the subterm was quoted
       in.
     - [qd_max_rel] is the largest free de Bruijn index of the subterm, 0 if it
       is closed.  It is a property of the term alone.
     - The flags say that the subterm, or one of its subterms, read that part
       of the context.  [qd_env] and [qd_scope] keep what was read: the
       environment while [qd_retypes] or [qd_graph] holds, the local scope while
       [qd_reads_scope] holds.  A cached record without those flags keeps
       neither, so the cache does not retain environments. *)
  type quote_dependencies = {
    qd_depth : int;
    mutable qd_env : Environ.env;
    mutable qd_scope : local_scope option;
    mutable qd_max_rel : int;
    (* [template_instance] retyped an argument in [qd_env]. *)
    mutable qd_retypes : bool;
    (* [template_universe_level] read [current_local_scope]. *)
    mutable qd_reads_scope : bool;
    (* [template_universe_level] read the universe graph of [qd_env]. *)
    mutable qd_graph : bool;
    (* The subterm refers to a declaration that was still being quoted, whose
       extra universe levels ([extended_constants], [extended_inductives]) were
       not known yet.  Quoting it again later can give another value, so it is
       never cached. *)
    mutable qd_unstable : bool;
  }

  let new_quote_dependencies env =
    { qd_depth = Environ.nb_rel env; qd_env = env;
      qd_scope = !current_local_scope; qd_max_rel = 0; qd_retypes = false;
      qd_reads_scope = false; qd_graph = false; qd_unstable = false }

  (* The record of the subterm being quoted now.  [quote_term_rec] gives each
     declaration it quotes a fresh one, so a declaration's reads are not
     charged to the occurrence that triggered its quotation. *)
  let current_quote_dependencies =
    ref (new_quote_dependencies Environ.empty_env)

  (* Declarations, by canonical kernel name, that [quote_term_rec] has started
     and not finished quoting. *)
  let declarations_in_progress = ref Names.KNset.empty

  let note_declaration_reference kn =
    if Names.KNset.mem kn !declarations_in_progress then
      !current_quote_dependencies.qd_unstable <- true

  (* The cache is used only under an evar map with no evars, no conversion
     problems, no local universes and no flexible universe variables, as made
     by [Evd.from_env].  Under such a map [EConstr.to_constr] and [Retyping]
     find no evar to expand, and the universe substitution they apply is the
     identity, so every usable evar map gives the same quotation. *)
  let quote_cache_usable sigma =
    Evd.is_empty sigma && UState.is_empty (Evd.ustate sigma)

  (* Two rel contexts give every retyping the same result when they have the
     same declarations up to binder names: [Retyping] and [Reduction] read a
     declaration's type and body, never its name.  The walk stops at the first
     physically shared tail. *)
  let rec rel_contexts_agree ctx1 ctx2 =
    ctx1 == ctx2 ||
    match ctx1, ctx2 with
    | Context.Rel.Declaration.LocalAssum (_, t1) :: ctx1,
      Context.Rel.Declaration.LocalAssum (_, t2) :: ctx2 ->
      Constr.equal t1 t2 && rel_contexts_agree ctx1 ctx2
    | Context.Rel.Declaration.LocalDef (_, b1, t1) :: ctx1,
      Context.Rel.Declaration.LocalDef (_, b2, t2) :: ctx2 ->
      Constr.equal b1 b2 && Constr.equal t1 t2 && rel_contexts_agree ctx1 ctx2
    | _ -> false

  (* Whether a value cached with dependencies [deps] is the value quoting the
     same subterm would compute now, in [env]. *)
  let quote_dependencies_hold deps env =
    (not deps.qd_retypes
     || (Environ.named_context_val env
         == Environ.named_context_val deps.qd_env
         && (deps.qd_max_rel <= 0
             || rel_contexts_agree (Environ.rel_context env)
                  (Environ.rel_context deps.qd_env))))
    && (not deps.qd_reads_scope || !current_local_scope == deps.qd_scope)
    && (not deps.qd_graph
        || Environ.universes env == Environ.universes deps.qd_env)

  (* Charge the reads of a subterm, quoted at rel depth [depth], to [parent]. *)
  let add_quote_dependencies parent child depth =
    let max_rel = child.qd_max_rel - (depth - parent.qd_depth) in
    if max_rel > parent.qd_max_rel then parent.qd_max_rel <- max_rel;
    if child.qd_retypes then parent.qd_retypes <- true;
    if child.qd_reads_scope then parent.qd_reads_scope <- true;
    if child.qd_graph then parent.qd_graph <- true;
    if child.qd_unstable then parent.qd_unstable <- true

  (* Drop what a finished record does not need before the cache keeps it. *)
  let release_quote_dependencies deps =
    if not (deps.qd_retypes || deps.qd_graph) then
      deps.qd_env <- Environ.empty_env;
    if not deps.qd_reads_scope then deps.qd_scope <- None

  (* Declarations whose abstract universe context we extended with extra bound
     levels, together with the component expressions (over the declaration's
     original bound variables) that those levels stand for, in index order. *)
  let extended_constants : Univ.Universe.t list Names.KerName.Map.t ref =
    ref Names.KerName.Map.empty

  let extended_inductives : Univ.Universe.t list Names.KerName.Map.t ref =
    ref Names.KerName.Map.empty

  let universe_has_var_component universe =
    List.exists
      (fun (level, _) -> not (Option.is_empty (Univ.Level.var_index level)))
      (Univ.Universe.repr universe)

  let normalize_local_universe scope universe =
    let rec expand_component shift level =
      match Univ.Level.var_index level with
      | Some index
        when index >= scope.ls_n_orig
          && index < scope.ls_n_orig + Array.length scope.ls_definitions ->
        List.concat_map
          (fun (component, component_shift) ->
             expand_component (shift + component_shift) component)
          (Univ.Universe.repr
             scope.ls_definitions.(index - scope.ls_n_orig))
      | _ -> [level, shift]
    in
    Univ.Universe.unrepr
      (List.concat_map
         (fun (level, shift) -> expand_component shift level)
         (Univ.Universe.repr universe))

  let local_fresh_var scope universe =
    let universe = normalize_local_universe scope universe in
    match
      try Some (Univ.Universe.Map.find universe scope.ls_memo)
      with Not_found -> None
    with
    | Some level -> level
    | None ->
      let level = Univ.Level.var (scope.ls_n_orig + scope.ls_next) in
      scope.ls_next <- scope.ls_next + 1;
      let constraints =
        List.fold_left
          (fun constraints (component, shift) ->
             let kind =
               match shift with
               | 0 -> Univ.UnivConstraint.Le
               | 1 -> Univ.UnivConstraint.Lt
               | _ ->
                 CErrors.user_err
                   Pp.(str "Quoting template universe offsets above one is not supported.")
             in
             Univ.UnivConstraints.add (component, kind, level) constraints)
          scope.ls_constraints (Univ.Universe.repr universe)
      in
      scope.ls_memo <- Univ.Universe.Map.add universe level scope.ls_memo;
      scope.ls_definitions <-
        Array.append scope.ls_definitions [| universe |];
      scope.ls_exprs <- universe :: scope.ls_exprs;
      scope.ls_constraints <- constraints;
      level
  let extend_abstract_context auctx scope =
    let repr = UVars.AbstractContext.repr auctx in
    let { UVars.quals; UVars.univs } =
      UVars.AbstractContext.names auctx
    in
    let extra =
      Array.init scope.ls_next
        (fun k ->
           Names.Name
             (Names.Id.of_string ("template_alg" ^ string_of_int k)))
    in
    let new_pcon =
      Univ.UnivConstraints.fold
        (fun cstr pcon -> PConstraints.add_univ cstr pcon)
        scope.ls_constraints
        (UVars.UContext.constraints repr)
    in
    UVars.AbstractContext.make
      { UVars.quals; UVars.univs = Array.append univs extra } new_pcon

  (* [auctx] with [Var k <= top] for each of its bound levels.  Every instance
     the quoted program gives a polymorphic declaration is made of levels at
     most [top]: [top] itself (canonical template instances), global levels
     below it (constrained in [quote_term_rec]), and bound levels of other
     polymorphic declarations (constrained here).  So the extra constraints
     reject no use site, and inside the declaration they let PCUIC derive
     [Type@{Var k} <= Type@{top}] where a canonical instance needs it. *)
  let constrain_below_top top auctx =
    let repr = UVars.AbstractContext.repr auctx in
    let _, levels = UVars.Instance.to_array (UVars.UContext.instance repr) in
    let pcon =
      Array.fold_left
        (fun pcon level ->
           PConstraints.add_univ (level, Univ.UnivConstraint.Le, top) pcon)
        (UVars.UContext.constraints repr) levels
    in
    UVars.AbstractContext.make (UVars.AbstractContext.names auctx) pcon

  (* Every universe level is at least [Set], so [max(Set, u1, ..., un)]
     equals [max(u1, ..., un)] when a non-[Set] component is present.  Removing
     the redundant component before minting representatives prevents list's
     intrinsic [max(Set, u)] result sort from introducing a spurious second
     universe parameter. *)
  let simplify_template_universe universe =
    let components = Univ.Universe.repr universe in
    if List.exists
         (fun (level, _) -> not (Univ.Level.equal level Univ.Level.set))
         components
    then
      Univ.Universe.unrepr
        (List.filter
           (fun (level, _) -> not (Univ.Level.equal level Univ.Level.set))
           components)
    else universe
  let normalize_global_universe context universe =
    let rec expand_component shift level =
      match
        try Some (Univ.Level.Map.find level context.fresh_definitions)
        with Not_found -> None
      with
      | Some definition ->
        List.concat_map
          (fun (component, component_shift) ->
             expand_component (shift + component_shift) component)
          (Univ.Universe.repr definition)
      | None -> [level, shift]
    in
    Univ.Universe.unrepr
      (List.concat_map
         (fun (level, shift) -> expand_component shift level)
         (Univ.Universe.repr universe))



  let template_universe_level ?context env universe =
    let universe = simplify_template_universe universe in
    let universe =
      match context with
      | Some context -> normalize_global_universe context universe
      | None -> universe
    in
    let universe = simplify_template_universe universe in
    let is_top level =
      match context with
      | Some { top_level = Some top; _ } -> Univ.Level.equal level top
      | _ -> false
    in
    (* Every level of the program other than [top] is at most [top], so a
       maximum with a [top] component and no [top+n] component is [top].  This
       keeps [top] out of the fresh levels. *)
    let components = Univ.Universe.repr universe in
    if List.exists (fun (level, shift) -> Int.equal shift 0 && is_top level)
         components
       && not (List.exists (fun (level, shift) -> shift > 0 && is_top level)
                 components)
    then Option.get (Option.get context).top_level
    else
    match Univ.Universe.level universe with
    | Some level -> level
    | None ->
      if universe_has_var_component universe then begin
        (* Polymorphic scope: components include bound universe variables. *)
        !current_quote_dependencies.qd_reads_scope <- true;
        match !current_local_scope with
        | Some scope -> local_fresh_var scope universe
        | None ->
          CErrors.user_err
            Pp.(str "Quoting algebraic template universe "
                ++ Univ.Universe.pr Univ.Level.raw_pr universe
                ++ str " with bound-variable components, in declaration "
                ++ str !current_decl_name
                ++ str ", outside any polymorphic declaration, is not supported.")
      end else begin
        !current_quote_dependencies.qd_graph <- true;
        let graph = Environ.universes (snd env) in
        let components = Univ.Universe.repr universe in
        (* Prefer reusing an already-declared level when the universe graph
           proves the algebraic expression equal to one of its components. *)
        let graph_equal_level =
          match
            UGraph.check_declared_universes graph
              (Univ.Universe.levels
                 ~init:Univ.Level.Set.empty universe)
          with
          | Error _ -> None
          | Ok () ->
            let rec find = function
              | [] -> None
              | (level, shift) :: rest ->
                if Int.equal shift 0
                   && UGraph.check_eq graph universe (Univ.Universe.make level)
                then Some level
                else find rest
            in
            find components
        in
        match graph_equal_level with
        | Some level -> level
        | None ->
          match context with
          | None ->
            CErrors.user_err
              Pp.(str "Quoting algebraic template universe "
                  ++ Univ.Universe.pr Univ.Level.raw_pr universe
                  ++ str " is not supported.")
          | Some context ->
            (* Global scope: introduce one fresh global level [l] with the
               lower-bound constraints [component <= l] (or [< l] for a unit
               shift).  Setting [v(l)] to the largest [v(component_i) + shift_i]
               satisfies these, so adding [l] is a conservative extension of the
               universe graph. *)
            match
              try Some (Univ.Universe.Map.find universe context.universe_levels)
              with Not_found -> None
            with
            | Some level -> level
            | None ->
              let level = fresh_template_level graph context in
              let constraints =
                List.fold_left
                  (fun constraints (component, shift) ->
                     let kind =
                       match shift with
                       | 0 -> Univ.UnivConstraint.Le
                       | 1 -> Univ.UnivConstraint.Lt
                       | _ ->
                         CErrors.user_err
                           Pp.(str "Quoting template universe offsets above one is not supported.")
                     in
                     Univ.UnivConstraints.add (component, kind, level) constraints)
                  context.fresh_constraints components
              in
              context.universe_levels <-
                Univ.Universe.Map.add universe level context.universe_levels;
              context.fresh_definitions <-
                Univ.Level.Map.add level universe context.fresh_definitions;
              context.fresh_levels <-
                Univ.Universe.levels
                  ~init:(Univ.Level.Set.add level context.fresh_levels)
                  universe;
              context.fresh_constraints <- constraints;
              level
      end

  (* At a use site of a declaration whose abstract universe context we
     extended, append one level per recorded component expression. *)
  let extend_instance ?context env exprs pu =
    let instance = ref pu in
    List.iter
      (fun e ->
         let e' = UVars.subst_instance_universe !instance e in
         let level = template_universe_level ?context env e' in
         let quals, levels = UVars.Instance.to_array !instance in
         instance :=
           UVars.Instance.of_array (quals, Array.append levels [| level |]))
      exprs;
    !instance

  (* At a use site [c@{pu}] of a declaration [c] whose abstract context was
     extended, append the corresponding extra levels. *)
  let extend_instance_for_decl ?context env kn pu =
    note_declaration_reference kn;
    match
      try Some (Names.KerName.Map.find kn !extended_constants)
      with Not_found -> None
    with
    | None -> pu
    | Some exprs -> extend_instance ?context env exprs pu

  let extend_instance_for_inductive ?context env mind pu =
    let kn = Names.MutInd.canonical (fst mind) in
    note_declaration_reference kn;
    match
      try Some (Names.KerName.Map.find kn !extended_inductives)
      with Not_found -> None
    with
    | None -> pu
    | Some exprs -> extend_instance ?context env exprs pu

  (* PCUIC sorts can contain algebraic universes, but template-inductive
     instances cannot.  Use the same representative level for both: whenever
     a template instance at [u] is represented by [lambda_u], rewrite each
     explicit sort [Type@{u}] (and [QType@{u}]) in the translated declaration
     to [Type@{lambda_u}].  In particular, this keeps the translated type of a
     polymorphic body such as [iffT] aligned with its translated [prod]
     instance. *)
  let quote_sort_with_template ?universe_context env = function
    | Sorts.Type universe ->
      let level =
        template_universe_level ?context:universe_context env universe
      in
      Q.quote_sort
        (Sorts.make Sorts.Quality.qtype (Univ.Universe.make level))
    | Sorts.QSort (quality, universe) ->
      let level =
        template_universe_level ?context:universe_context env universe
      in
      Q.quote_sort
        (Sorts.qsort quality (Univ.Universe.make level))
    | sort -> Q.quote_sort sort


  (* [~canonical] is for an occurrence where PCUIC compares the instance
     exactly: a [Case] ([`Case]), or an [Ind]/[Construct] applied to fewer
     arguments than its full arity ([`Partial]; [global_variance_gen],
     PCUICEquality.v:46-74).  The kernel stores no instance there, and the
     instance inferred from the arguments' types is fixed at quotation: after
     PCUIC substitutes into the arguments, one kernel term can carry two
     instances (a [match .. in prod _ _] reached two ways; [eq@{Set} Z] against
     [eq@{RelationClasses.21} Z] in [Z.eq_equiv]).  So a level bound by a given
     argument becomes the program's top level, which is above every argument
     type and does not depend on it.
     - [`Case]: every bound level.  The instance only types the predicate's
       binder and the parameters, which are below [top].
     - [`Partial]: the levels that are not in the inductive's conclusion sort.
       A level in the conclusion reaches the occurrence's type, where [top]
       could exceed what the context allows, so it keeps the inferred level. *)
  let template_instance ?universe_context ?canonical env sigma mind
      args default_instance =
    let mib = Environ.lookup_mind (fst mind) (snd env) in
    match mib.Declarations.mind_template with
    | None -> default_instance
    | Some template ->
      let bound_instance =
        UVars.UContext.instance
          (UVars.AbstractContext.repr template.template_context)
      in
      let _, bound_levels =
        UVars.Instance.to_array bound_instance
      in
      let concl_levels = Sorts.levels template.template_concl in
      (* A template constraint bounds its level from above by a global level
         (kernel/inductive.ml, [instantiate_template_constraints]), which [top]
         would violate.  Such levels keep the inferred instance. *)
      let constrained_levels =
        Univ.UnivConstraints.fold
          (fun (u, _, v) levels ->
             Univ.Level.Set.add u (Univ.Level.Set.add v levels))
          (UVars.UContext.univ_constraints
             (UVars.AbstractContext.repr template.template_context))
          Univ.Level.Set.empty
      in
      let keeps_inference kind bound =
        Univ.Level.Set.mem bound constrained_levels
        || (kind = `Partial && Univ.Level.Set.mem bound concl_levels)
      in
      (* The canonical substitution maps each level bound by a given argument
         to [top] and each level bound by a missing argument to its default,
         as the kernel does.  It reads no argument. *)
      let canonical_level =
        match canonical, universe_context with
        | Some kind, Some { top_level = Some top; _ } ->
          let _, _, (_, substitution) =
            Inductive.instantiate_template_universes mib
              (List.map
                 (fun _ ~default:_ ->
                    Inductive.TemplateUniv (Univ.Universe.make top))
                 (Array.to_list args))
          in
          (fun bound ->
             match Univ.Level.var_index bound with
             | _ when keeps_inference kind bound -> None
             | None -> assert false
             | Some index ->
               Some
                 (template_universe_level ?context:universe_context env
                    (Int.Map.get index substitution)))
        | _ -> (fun _ -> None)
      in
      let needs_inference =
        Array.exists (fun bound -> Option.is_empty (canonical_level bound))
          bound_levels
      in
      (* Mirror the kernel's [make_param_univs] (kernel/typeops.ml:417-431):
         the template universe bound by a parameter is the conclusion sort of
         the argument's type viewed as an arity, so a parameter such as
         [P : A -> Type@{u}] (e.g. [sigT]) binds [u]. *)
      let argument_universe arg ~default:_ =
        !current_quote_dependencies.qd_retypes <- true;
        let type_of_argument =
          EConstr.to_constr sigma
            (Retyping.get_type_of (snd env) sigma (EConstr.of_constr arg))
        in
        match snd (Reduction.dest_arity (snd env) type_of_argument) with
        | Sorts.Prop -> Inductive.TemplateProp
        | Sorts.Set -> Inductive.TemplateUniv Univ.Universe.type0
        | Sorts.Type universe -> Inductive.TemplateUniv universe
        | Sorts.QSort (quality, universe) ->
          Inductive.TemplateAboveProp (quality, universe)
        | Sorts.SProp | exception Reduction.NotArity ->
          CErrors.user_err
            Pp.(str "Could not infer a template-inductive universe from its parameter.")
      in
      (* Retype the arguments only when some level is inferred from them. *)
      let universe_substitution =
        if needs_inference then
          let _, _, (_, substitution) =
            Inductive.instantiate_template_universes mib
              (List.map argument_universe (Array.to_list args))
          in
          substitution
        else Int.Map.empty
      in
      let levels =
        Array.map
          (fun bound ->
             match canonical_level bound with
             | Some level -> level
             | None ->
               match Univ.Level.var_index bound with
               | None -> assert false
               | Some index ->
                 template_universe_level ?context:universe_context env
                   (Int.Map.get index universe_substitution))
          bound_levels
      in
      UVars.Instance.of_array ([||], levels)

  let template_default_substitution ?universe_context env sigma mind args =
    let mib = Environ.lookup_mind (fst mind) (snd env) in
    match mib.Declarations.mind_template with
    | None -> None
    | Some template ->
      let actual_instance =
        template_instance ?universe_context env sigma mind args
          UVars.Instance.empty
      in
      let _, defaults = UVars.Instance.to_array template.template_defaults in
      let _, actuals = UVars.Instance.to_array actual_instance in
      assert (Array.length defaults = Array.length actuals);
      let rec add_levels index substitution =
        if index = Array.length defaults then substitution
        else
          add_levels (index + 1)
            (Univ.Level.Map.add defaults.(index) actuals.(index) substitution)
      in
      Some (Sorts.QVar.Map.empty,
            add_levels 0 Univ.Level.Map.empty)

  let normalize_template_type ?universe_context env sigma body ty =
    let head, args = Constr.decompose_app body in
    match Constr.kind head with
    | Constr.Ind (mind, _) ->
      begin match
        template_default_substitution ?universe_context env sigma mind args
      with
      | None -> ty
      | Some substitution -> Vars.subst_univs_level_constr substitution ty
      end
    | Constr.Construct ((mind, _), _) ->
      begin match
        template_default_substitution ?universe_context env sigma mind args
      with
      | None -> ty
      | Some substitution -> Vars.subst_univs_level_constr substitution ty
      end
    | _ -> ty

  let quote_universes_entry = function
    | Monomorphic_entry -> Q.mkMonomorphic_entry ()
    | Polymorphic_entry ctx -> Q.mkPolymorphic_entry (Q.quote_univ_context ctx)

  let quote_universes_decl decl templ =
    match decl with
    | Monomorphic -> Q.mkMonomorphic_ctx ()
    | Polymorphic ctx -> Q.mkPolymorphic_ctx (Q.quote_abstract_univ_context ctx)

  let quote_ugraph ?kept ?(extra_constraints = Univ.UnivConstraints.empty)
      (g : UGraph.t) =
    debug Pp.(fun () -> str"Quoting ugraph");
    let levels, cstrs, eqs =
      match kept with
      | None ->
        let cstrs, eqs = UGraph.constraints_of_universes g in
        UGraph.domain g, cstrs, eqs
      | Some l ->
        debug Pp.(fun () -> str"Quoting graph restricted to: " ++ Univ.Level.Set.pr Univ.Level.raw_pr l);
        (* Feedback.msg_debug Pp.(str"Graph is: "  ++ UGraph.pr_universes Univ.Level.raw_pr (UGraph.repr g)); *)
        let dom = UGraph.domain g in
        let kept = Univ.Level.Set.inter dom l in
        let kept = Univ.Level.Set.remove Univ.Level.set kept in
        let cstrs = time Pp.(str"Computing graph restriction") (UGraph.constraints_for ~kept) g in
        l, cstrs, []
    in
    let levels, cstrs =
      List.fold_right (fun eqs acc ->
        match Univ.Level.Set.elements eqs with
        | [] -> acc
        | x :: [] -> acc
        | x :: rest ->
          List.fold_right (fun p (levels, cstrs) ->
            (Univ.Level.Set.add p levels, Univ.UnivConstraints.add (x, Univ.UnivConstraint.Eq, p) cstrs)) rest acc)
        eqs (levels, cstrs)
    in
    let cstrs = Univ.UnivConstraints.union cstrs extra_constraints in
    let levels = Univ.Level.Set.add Univ.Level.set levels in
    debug Pp.(fun () -> str"Universe context: " ++ Univ.ContextSet.pr Univ.Level.raw_pr (levels, cstrs));
    time (Pp.str"Quoting universe context")
      (fun uctx -> Q.quote_contextset uctx) (levels, cstrs)

  let quote_inductive' (ind, i) : Q.quoted_inductive =
    Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical ind), Q.quote_int i)

  let quote_rel_decl quote_term acc env sigma = function
      | Context.Rel.Declaration.LocalAssum (na, t) ->
        let t', acc = quote_term acc env sigma t in
        (Q.quote_context_decl (Q.quote_aname na) None t', acc)
      | Context.Rel.Declaration.LocalDef (na, b, t) ->
        let b', acc = quote_term acc env sigma b in
        let t', acc = quote_term acc env sigma t in
        (Q.quote_context_decl (Q.quote_aname na) (Some b') t', acc)

  let quote_rel_context quote_term acc env sigma ctx =
      let decls, env, acc =
        List.fold_right (fun decl (ds, env, acc) ->
            let x, acc = quote_rel_decl quote_term acc env sigma decl in
            (x :: ds, push_rel decl env, acc))
          ctx ([],env,acc) in
      Q.quote_context decls, acc

  let quote_binder b =
    Q.quote_aname b

  let quote_name_annots nas =
    Array.map quote_binder nas

  let quote_terms quote_term acc env sigma ts =
    let acc, ts =
      CArray.fold_left_map (fun acc t -> let (x, acc) = quote_term acc env sigma t in acc, x) acc ts
    in ts, acc

  let cofixpoint_arities ts =
    let cofix_arity t =
      let ctx, _concl = Term.decompose_prod_decls t in
      Context.Rel.nhyps ctx
    in Array.map cofix_arity ts

  (* A hash of the top of a kernel term: at most [depth] levels deep and at
     most four children per node, so it costs O(1). [Constr.hash] traverses the
     whole term, which is exponential in the depth of sharing on large proofs. *)
  let rec bounded_constr_hash depth trm =
    let open Hashset.Combine in
    let sub trm = if depth <= 1 then 0 else bounded_constr_hash (depth - 1) trm in
    let sub_array terms =
      let n = Array.length terms in
      let hash_at acc i = combine acc (sub (Array.unsafe_get terms i)) in
      if n <= 4 then CArray.fold_left_i (fun i acc _ -> hash_at acc i) n terms
      else hash_at (hash_at (hash_at (hash_at n 0) 1) (n - 2)) (n - 1)
    in
    match Constr.kind trm with
    | Constr.Rel i -> combinesmall 1 i
    | Constr.Var id -> combinesmall 2 (Id.hash id)
    | Constr.Sort s -> combinesmall 3 (Sorts.hash s)
    | Constr.Cast (c, _, t) -> combinesmall 4 (combine (sub c) (sub t))
    | Constr.Prod (_, t, b) -> combinesmall 5 (combine (sub t) (sub b))
    | Constr.Lambda (_, t, b) -> combinesmall 6 (combine (sub t) (sub b))
    | Constr.LetIn (_, v, t, b) -> combinesmall 7 (combine3 (sub v) (sub t) (sub b))
    | Constr.App (f, args) -> combinesmall 8 (combine (sub f) (sub_array args))
    | Constr.Const (c, u) -> combinesmall 9 (combine (Constant.CanOrd.hash c) (UVars.Instance.hash u))
    | Constr.Ind (ind, u) -> combinesmall 10 (combine (Ind.CanOrd.hash ind) (UVars.Instance.hash u))
    | Constr.Construct (c, u) -> combinesmall 11 (combine (Construct.CanOrd.hash c) (UVars.Instance.hash u))
    | Constr.Case (ci, _, pars, _, _, c, brs) ->
      combinesmall 12 (combine4 (Ind.CanOrd.hash ci.Constr.ci_ind) (sub_array pars) (Array.length brs) (sub c))
    | Constr.Fix ((_, i), (_, tys, bodies)) -> combinesmall 13 (combine3 i (sub_array tys) (sub_array bodies))
    | Constr.CoFix (i, (_, tys, bodies)) -> combinesmall 14 (combine3 i (sub_array tys) (sub_array bodies))
    | Constr.Proj (p, _, c) -> combinesmall 15 (combine (Projection.CanOrd.hash p) (sub c))
    | Constr.Evar (e, _) -> combinesmall 16 (Evar.hash e)
    | Constr.Meta n -> combinesmall 17 n
    | Constr.Int i -> combinesmall 18 (Uint63.hash i)
    | Constr.Float f -> combinesmall 19 (Float64.hash f)
    | Constr.String s -> combinesmall 20 (Pstring.hash s)
    | Constr.Array (_, elems, def, ty) -> combinesmall 21 (combine3 (sub_array elems) (sub def) (sub ty))

  let initial_quote_cache_size = 1 lsl 10
  let max_quote_cache_size = 1 lsl 22

  let quote_term_remember ?universe_context
      ?(remember_universe_levels = fun _ -> ())
      (add_constant : KerName.t -> 'a -> 'a)
      (add_inductive : Names.inductive -> Declarations.mutual_inductive_body -> 'a -> 'a) =
    (* Kernel terms are hash-consed DAGs; quoting them as trees duplicates every
       shared subterm. [quote_term] caches the quoted value of each kernel
       subterm by physical equality, so a shared subterm is quoted once and its
       quoted value is shared. OCaml values are immutable, so sharing changes
       no value.

       A cached value is returned only where quoting would compute the same
       value. Besides the subterm and the global declarations, quoting reads
       the following (recorded in [quote_dependencies], checked by
       [quote_dependencies_hold]):
       - The rel and named contexts, when [template_instance] retypes an
         argument. The rel context matters only if the subterm has a free
         [Rel]: the binders inside a closed subterm come from the subterm
         itself. Such a value is reused only under the same named context and
         a rel context with the same declarations ([rel_contexts_agree]).
       - [current_local_scope], for an algebraic universe over bound
         variables. Reused only in the same scope, whose memo already holds the
         levels the first quotation minted.
       - The environment's universe graph, for an algebraic universe over
         global levels. Reused only under the same graph.
       - [extended_constants]/[extended_inductives], which gain an entry when a
         declaration finishes quoting. A value that read a declaration still in
         progress is not cached ([qd_unstable]); every other entry is final.
       - [sigma]: the cache is used only under an evar map that
         [quote_cache_usable] accepts, and all such maps give the same result.
       A term's dependencies include those of its subterms. A hit skips the
       [add_constant]/[add_inductive] and [remember_universe_levels] calls of
       the subterm, which its miss made on this same closure; all of them only
       add to sets.

       The cache is direct-mapped: a slot holds one subterm and a collision
       evicts it, so a lookup costs O(1) whatever the hash quality. With a
       chained table and a bounded hash, bucket scans took 78% of quotation time
       on large objects. The arrays start filled with the first entry, which is
       a valid entry in every slot, and double up to [max_quote_cache_size] as
       entries are added. *)
    let cache_keys = ref [||] and cache_values = ref [||] and cache_adds = ref 0 in
    let cache_slot keys trm = bounded_constr_hash 4 trm land (Array.length keys - 1) in
    let cache_find trm =
      let keys = !cache_keys in
      if Array.length keys = 0 then None
      else
        let slot = cache_slot keys trm in
        if Array.unsafe_get keys slot == trm then Some (Array.unsafe_get !cache_values slot)
        else None
    in
    let cache_store keys values trm quoted =
      let slot = cache_slot keys trm in
      Array.unsafe_set keys slot trm;
      Array.unsafe_set values slot quoted
    in
    let cache_add trm quoted =
      let size = Array.length !cache_keys in
      if size = 0 then begin
        cache_keys := Array.make initial_quote_cache_size trm;
        cache_values := Array.make initial_quote_cache_size quoted
      end else begin
        if !cache_adds >= 2 * size && size < max_quote_cache_size then begin
          let keys = Array.make (2 * size) trm and values = Array.make (2 * size) quoted in
          let old_values = !cache_values in
          Array.iteri (fun slot key -> cache_store keys values key (Array.unsafe_get old_values slot)) !cache_keys;
          cache_keys := keys;
          cache_values := values;
          cache_adds := 0
        end;
        incr cache_adds;
        cache_store !cache_keys !cache_values trm quoted
      end
    in
    let remember_instance instance =
      let _, levels = UVars.Instance.to_array instance in
      let universe_levels =
        Array.fold_left
          (fun levels level -> Univ.Level.Set.add level levels)
          Univ.Level.Set.empty levels
      in
      remember_universe_levels universe_levels
    in
    let remember_sort = function
      | Sorts.Type universe | Sorts.QSort (_, universe) ->
        remember_universe_levels
          (Univ.Universe.levels ~init:Univ.Level.Set.empty universe)
      | _ -> ()
    in
    let rec quote_term (acc : 'a) env sigma trm =
      let parent = !current_quote_dependencies in
      let depth = Environ.nb_rel (snd env) in
      let usable = quote_cache_usable sigma in
      let hit =
        if not usable then None
        else match cache_find trm with
          | Some (quoted, deps) when quote_dependencies_hold deps (snd env) ->
            Some (quoted, deps)
          | _ -> None
      in
      match hit with
      | Some (quoted, deps) ->
        add_quote_dependencies parent deps depth;
        quoted, acc
      | None ->
        let deps = new_quote_dependencies (snd env) in
        current_quote_dependencies := deps;
        let quoted, acc =
          try quote_term_uncached acc env sigma trm
          with e ->
            let e = Exninfo.capture e in
            current_quote_dependencies := parent;
            Exninfo.iraise e
        in
        current_quote_dependencies := parent;
        add_quote_dependencies parent deps depth;
        if usable && not deps.qd_unstable then begin
          release_quote_dependencies deps;
          cache_add trm (quoted, deps)
        end;
        quoted, acc
    and quote_term_uncached (acc : 'a) env sigma trm =
      let aux acc env trm =
      match Constr.kind trm with
      | Constr.Rel i ->
        !current_quote_dependencies.qd_max_rel <- i;
        (Q.mkRel (Q.quote_int (i - 1)), acc)
      | Constr.Var v -> (Q.mkVar (Q.quote_ident v), acc)
      | Constr.Evar (n,args) ->
        let args = Evd.expand_existential0 sigma (n, args) in
	      let (args',acc) = quote_terms quote_term acc env sigma (Array.of_list args) in
         (Q.mkEvar (Q.quote_int (Evar.repr n)) args', acc)
      | Constr.Sort s ->
        let () = remember_sort s in
        (Q.mkSort (quote_sort_with_template ?universe_context env s), acc)
      | Constr.Cast (c,k,t) ->
              let (c',acc) = quote_term acc env sigma c in
              let (t',acc) = quote_term acc env sigma t in
        let k' = Q.quote_cast_kind k in
        (Q.mkCast c' k' t', acc)

      | Constr.Prod (n,t,b) ->
              let (t',acc) = quote_term acc env sigma t in
        let env = push_rel (toDecl (n, None, t)) env in
        let (b',acc) = quote_term acc env sigma b in
        (Q.mkProd (Q.quote_aname n) t' b', acc)

      | Constr.Lambda (n,t,b) ->
	      let (t',acc) = quote_term acc env sigma t in
              let (b',acc) = quote_term acc (push_rel (toDecl (n, None, t)) env) sigma b in
        (Q.mkLambda (Q.quote_aname n) t' b', acc)

      | Constr.LetIn (n,e,t,b) ->
	      let (e',acc) = quote_term acc env sigma e in
	      let (t',acc) = quote_term acc env sigma t in
	      let (b',acc) = quote_term acc (push_rel (toDecl (n, Some e, t)) env) sigma b in
      	(Q.mkLetIn (Q.quote_aname n) e' t' b', acc)

      | Constr.App (f,xs) ->
        begin match Constr.kind f with
        | Constr.Ind (mind, pu) ->
          let () = remember_instance pu in
          let mib = Environ.lookup_mind (fst mind) (snd env) in
          let acc = add_inductive mind mib acc in
          let pu =
            let mip = mib.Declarations.mind_packets.(snd mind) in
            let canonical =
              Array.length xs
              < mib.Declarations.mind_nparams + mip.Declarations.mind_nrealargs
            in
            let canonical = if canonical then Some `Partial else None in
            template_instance ?universe_context ?canonical env sigma mind xs pu
          in
          let pu =
            extend_instance_for_inductive ?context:universe_context env mind pu
          in
          let () = remember_instance pu in
          let xs', acc = quote_terms quote_term acc env sigma xs in
          (Q.mkApp
             (Q.mkInd (quote_inductive' mind) (Q.quote_univ_instance pu))
             xs',
           acc)
        | Constr.Construct ((mind, c), pu) ->
          let () = remember_instance pu in
          let mib = Environ.lookup_mind (fst mind) (snd env) in
          let acc = add_inductive mind mib acc in
          let pu =
            let mip = mib.Declarations.mind_packets.(snd mind) in
            let canonical =
              Array.length xs
              < mib.Declarations.mind_nparams
                + mip.Declarations.mind_consnrealargs.(c - 1)
            in
            let canonical = if canonical then Some `Partial else None in
            template_instance ?universe_context ?canonical env sigma mind xs pu
          in
          let pu =
            extend_instance_for_inductive ?context:universe_context env mind pu
          in
          let () = remember_instance pu in
          let xs', acc = quote_terms quote_term acc env sigma xs in
          (Q.mkApp
             (Q.mkConstruct
                (quote_inductive' mind, Q.quote_int (c - 1))
                (Q.quote_univ_instance pu))
             xs',
           acc)
        | _ ->
          let f', acc = quote_term acc env sigma f in
          let xs', acc = quote_terms quote_term acc env sigma xs in
          (Q.mkApp f' xs', acc)
        end

      | Constr.Const (c,pu) ->
        let () = remember_instance pu in
        let kn = Constant.canonical c in
        (* Quote the declaration first so that, if its abstract context was
           extended with extra bound levels, [extend_instance_for_decl] can
           supply them here. *)
        let acc = add_constant kn acc in
        let pu = extend_instance_for_decl ?context:universe_context env kn pu in
        let () = remember_instance pu in
        (Q.mkConst (Q.quote_kn kn) (Q.quote_univ_instance pu), acc)

      | Constr.Construct ((mind,c),pu) ->
        let () = remember_instance pu in
        let mib = Environ.lookup_mind (fst mind) (snd env) in
        let acc = add_inductive mind mib acc in
        let pu =
          template_instance ?universe_context env sigma mind [||] pu
        in
        let pu =
          extend_instance_for_inductive ?context:universe_context env mind pu
        in
        let () = remember_instance pu in
        (Q.mkConstruct
           (quote_inductive' mind, Q.quote_int (c - 1))
           (Q.quote_univ_instance pu),
         acc)

      | Constr.Ind (mind,pu) ->
        let () = remember_instance pu in
        let mib = Environ.lookup_mind (fst mind) (snd env) in
        let acc = add_inductive mind mib acc in
        let pu =
          template_instance ?universe_context env sigma mind [||] pu
        in
        let pu =
          extend_instance_for_inductive ?context:universe_context env mind pu
        in
        let () = remember_instance pu in
        (Q.mkInd (quote_inductive' mind) (Q.quote_univ_instance pu), acc)

      | Constr.Case (ci,u,pars, ((predctx, pred), relevance), iv, discr, brs) ->
        let () = remember_instance u in
        let mind = ci.Constr.ci_ind in
        let mib = Environ.lookup_mind (fst mind) (snd env) in
        let acc = add_inductive mind mib acc in
        let ind = Q.quote_inductive (Q.quote_kn (Names.MutInd.canonical (fst mind)),
                                      Q.quote_int (snd mind)) in
        let npar = Q.quote_int ci.Constr.ci_npar in
        let q_relevance = Q.quote_relevance relevance in
        let acc, q_pars = CArray.fold_left_map (fun acc par -> let (qt, acc) = quote_term acc env sigma par in acc, qt) acc pars in
        let pu =
          template_instance ?universe_context ~canonical:`Case env sigma mind
            pars u
        in
        let pu =
          extend_instance_for_inductive ?context:universe_context env mind pu
        in
        let () = remember_instance pu in
        let qu = Q.quote_univ_instance pu in
        let pctx = CaseCompat.case_predicate_context (snd env) ci u pars predctx in
        let qpctx = quote_name_annots predctx in
        let (qpred,acc) = quote_term acc (push_rel_context pctx env) sigma pred in
        let (qdiscr,acc) = quote_term acc env sigma discr in
        let cbrs = CaseCompat.case_branches_contexts (snd env) ci u pars brs in
        let (branches,acc) =
          CArray.fold_left2 (fun (bodies,acc) (brnas, brctx, bbody) narg ->
            let (qbody,acc) = quote_term acc (push_rel_context brctx env) sigma bbody in
            let qctx = quote_name_annots brnas in
              ((qctx, qbody) :: bodies, acc))
          ([],acc) cbrs ci.Constr.ci_cstr_nargs in
        (Q.mkCase (ind, npar, q_relevance) (qu, q_pars, qpctx, qpred) qdiscr (List.rev branches), acc)

      | Constr.Fix fp -> quote_fixpoint acc env sigma fp
      | Constr.CoFix fp -> quote_cofixpoint acc env sigma fp
      | Constr.Proj (p,_,c) ->
         let ind = quote_inductive' (Projection.inductive p) in
         let pars = Q.quote_int (Projection.npars p) in
         let arg  = Q.quote_int (Projection.arg p)   in
         let p' = Q.quote_proj ind pars arg in
         let t', acc = quote_term acc env sigma c in
         let mib = Environ.lookup_mind (fst (Projection.inductive p)) (snd env) in
         (Q.mkProj p' t', add_inductive (Projection.inductive p) mib acc)
      | Constr.Int i -> (Q.mkInt (Q.quote_int63 i), acc)
      | Constr.Float f -> (Q.mkFloat (Q.quote_float64 f), acc)
      | Constr.String s -> (Q.mkString (Q.quote_pstring s), acc)
      | Constr.Meta _ -> failwith "Meta not supported by TemplateRocq"
      | Constr.Array (u, ar, def, ty) ->
        let () = remember_instance u in
        let u = match UVars.Instance.to_array u with (_, [| u |]) -> u | _ -> assert false in
        let def', acc = quote_term acc env sigma def in
        let ty', acc = quote_term acc env sigma ty in
        let acc, arr' = CArray.fold_left_map (fun acc t -> let t', acc = quote_term acc env sigma t in acc, t') acc ar in
        Q.mkArray (Q.quote_univ_level u) arr' ~default:def' ~ty:ty', acc
      in
      aux acc env trm
    and quote_recdecl (acc : 'a) env sigma b (ns,ts,ds) =
      let ctxt =
        CArray.map2_i (fun i na t -> (Context.Rel.Declaration.LocalAssum (na, Vars.lift i t))) ns ts in
      let envfix = push_rel_context (CArray.rev_to_list ctxt) env in
      let ns' = Array.map quote_binder ns in
      let b' = Q.quote_int b in
      let ts', acc = quote_terms quote_term acc env sigma ts in
      let ds', acc = quote_terms quote_term acc envfix sigma ds in
      ((b',(ns',ts',ds')), acc)
    and quote_fixpoint acc env sigma ((a,b),decl) =
      let a' = Array.map Q.quote_int a in
      let (b',decl'),acc = quote_recdecl acc env sigma b decl in
      (Q.mkFix ((a',b'),decl'), acc)
    and quote_cofixpoint acc env sigma (a,(_, ts, _ as decl)) =
      let arities = cofixpoint_arities ts in
      let qarities = Array.map Q.quote_int arities in
      let (a',decl'),acc = quote_recdecl acc env sigma a decl in
      (Q.mkCoFix ((qarities,a'),decl'), acc)
    and quote_minductive_type (acc : 'a) env sigma (t : MutInd.t) mib =
      let uctx = get_abstract_inductive_universes mib.Declarations.mind_universes in
      let inst = UVars.UContext.instance uctx in
      let template_substitution, output_instance, quoted_universes, base_auctx =
        match mib.Declarations.mind_template with
        | None ->
          let base_auctx =
            match mib.Declarations.mind_universes with
            | Declarations.Polymorphic auctx -> Some auctx
            | Declarations.Monomorphic -> None
          in
          None, inst,
          quote_universes_decl mib.Declarations.mind_universes None,
          base_auctx
        | Some template ->
          let substitution, instance = template_inverse_substitution template in
          let auctx = named_template_context template in
          Some substitution, instance,
          Q.mkPolymorphic_ctx
            (Q.quote_abstract_univ_context auctx),
          Some auctx
      in
      let substitute_constr term =
        match template_substitution with
        | None -> term
        | Some substitution -> Vars.subst_univs_level_constr substitution term
      in
      let substitute_context context =
        match template_substitution with
        | None -> context
        | Some substitution ->
          Vars.subst_univs_level_context substitution context
      in
      let substitute_sort sort =
        match template_substitution with
        | None -> sort
        | Some substitution ->
          UVars.subst_sort_level_sort substitution sort
      in
      let indtys =
        (CArray.map_to_list (fun oib ->
           let ty =
             substitute_constr
               (Inductive.type_of_inductive ((mib,oib),inst))
           in
           (Context.Rel.Declaration.LocalAssum
              (Context.annotR (Names.Name oib.mind_typename), ty)))
          mib.mind_packets)
      in
      let envind = push_rel_context (List.rev indtys) env in
      let ref_name = Q.quote_kn (MutInd.canonical t) in
      let ntyps = Array.length mib.mind_packets in
      let (ls,acc) =
        List.fold_left (fun (ls,acc) oib ->
          let named_ctors =
            CList.combine3
              (Array.to_list oib.mind_consnames)
              (Array.to_list oib.mind_nf_lc)
              (Array.to_list oib.mind_consnrealargs)
          in
          let indty =
            substitute_constr
              (Inductive.type_of_inductive ((mib,oib),inst))
          in
          let indices, pars =
            let ctx = substitute_context oib.mind_arity_ctxt in
            CList.chop (List.length ctx - List.length mib.mind_params_ctxt) ctx
          in
          let indices, acc = quote_rel_context quote_term acc (push_rel_context pars env) sigma indices in
          let indty, acc = quote_term acc env sigma indty in
          let indsort =
            quote_sort_with_template ?universe_context env
              (substitute_sort (inductive_sort oib))
          in
          let (reified_ctors,acc) =
            List.fold_left (fun (ls,acc) (nm,(ctx, ty),ar) ->
              let ctx = substitute_context ctx in
              let ty = substitute_constr ty in
              let ty = Term.it_mkProd_or_LetIn ty ctx in
              let ty = Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntyps t ty in
              let ctx, concl = Term.decompose_prod_decls ty in
              let argctx, parsctx =
                CList.chop (List.length ctx - List.length mib.mind_params_ctxt) ctx
              in
              let envcstr = push_rel_context parsctx envind in
              let qargctx, acc = quote_rel_context quote_term acc envcstr sigma argctx in
              let qindices, acc =
                let hd, args = Constr.decompose_app concl in
                let pars, args = CArray.chop mib.mind_nparams args in
                let envconcl = push_rel_context argctx envcstr in
                quote_terms quote_term acc envconcl sigma args
              in
              let (ty,acc) = quote_term acc envind sigma ty in
              ((Q.quote_ident nm, qargctx, Array.to_list qindices, ty, Q.quote_int ar) :: ls, acc))
              ([],acc) named_ctors
          in
          let projs, acc =
            match mib.Declarations.mind_packets with
            (* TODO handle mutual records *)
            | [| { mind_record = PrimRecord { id; projections ; relevances; tys ; has_eta = _ } } |] ->
                let ctxwolet =
                  substitute_context
                    (Vars.smash_rel_context mib.mind_params_ctxt)
                in
                let indty =
                  Constr.mkApp (Constr.mkIndU ((t,0),output_instance),
                    Context.Rel.instance Constr.mkRel 0 ctxwolet)
                in
                let indbinder =
                  Context.Rel.Declaration.LocalAssum
                    (Context.annotR (Names.Name id),indty)
                in
                let envpars = push_rel_context (indbinder :: ctxwolet) env in
                let ps, acc =
                  CArray.fold_right3 (fun proj ty rel (ls,acc) ->
                    let ty, acc =
                      quote_term acc envpars sigma (substitute_constr ty)
                    in
                    let na = Q.quote_ident (Names.Label.to_id proj) in
                    let rel = Q.quote_relevance rel in
                    ((na, rel, ty) :: ls, acc)) projections tys relevances ([],acc)
                in ps, acc
            | _ -> [], acc
          in
          (* TODO quote the real squash data instead of approximating with a quality or set *)
          let kelim = match oib.Declarations.mind_squashed with
            | None -> UnivGen.QualityOrSet.qtype
            | Some _ -> UnivGen.QualityOrSet.of_sort oib.mind_sort
          in
          let sf = Q.quote_sort_quality_or_set kelim in
            (Q.quote_ident oib.mind_typename, indices, indsort, indty, sf,
             (List.rev reified_ctors), projs, Q.quote_relevance oib.mind_relevance) :: ls, acc)
        ([],acc) (Array.to_list mib.mind_packets)
      in
      let nparams = Q.quote_int mib.Declarations.mind_nparams in
      let paramsctx, acc =
        quote_rel_context quote_term acc env sigma
          (substitute_context mib.Declarations.mind_params_ctxt)
      in
      let constrain auctx =
        match mib.Declarations.mind_template, universe_context with
        | None, Some { top_level = Some top; _ } -> constrain_below_top top auctx
        | _ -> auctx
      in
      let uctx =
        match base_auctx, !current_local_scope with
        | Some auctx, Some scope when scope.ls_next > 0 ->
          let new_auctx = constrain (extend_abstract_context auctx scope) in
          extended_inductives :=
            Names.KerName.Map.add (MutInd.canonical t)
              (List.rev scope.ls_exprs) !extended_inductives;
          Q.mkPolymorphic_ctx (Q.quote_abstract_univ_context new_auctx)
        | Some auctx, _ when Option.is_empty mib.Declarations.mind_template ->
          Q.mkPolymorphic_ctx (Q.quote_abstract_univ_context (constrain auctx))
        | _ -> quoted_universes
      in
      let var =
        match mib.Declarations.mind_template with
        | Some template ->
          (* Template universes are irrelevant for conversion in the kernel
             (kernel/indTyping.ml treats them as irrelevant).  Translating the
             inductive as universe-polymorphic therefore requires Irrelevant
             variance on every template level, so that two occurrences with
             different template instances stay convertible in PCUIC (e.g.
             list@{BinList.21} A vs list@{List.21} A). *)
          let { UVars.quals = _; UVars.univs } =
            UVars.AbstractContext.names template.template_context
          in
          let template_variances =
            CList.map
              (fun _ -> Q.quote_variance UVars.Variance.Irrelevant)
              (Array.to_list univs)
          in
          let extra_variances =
            match !current_local_scope with
            | Some scope ->
              Array.to_list
                (Array.make scope.ls_next
                   (Q.quote_variance UVars.Variance.Irrelevant))
            | None -> []
          in
          Some (template_variances @ extra_variances)
        | None ->
          Option.map (CArray.map_to_list Q.quote_variance)
            mib.Declarations.mind_variance
      in
      let bodies = List.map Q.mk_one_inductive_body (List.rev ls) in
      let finite = Q.quote_mind_finiteness mib.Declarations.mind_finite in
      let mind = Q.mk_mutual_inductive_body finite nparams paramsctx bodies uctx var in
      ref_name, Q.mk_inductive_decl mind, acc
    in ((fun acc env -> quote_term acc (false, env)),
        (fun acc env t mib ->
        quote_minductive_type acc (false, env) t mib))

  let quote_term env sigma trm =
    let (fn,_) = quote_term_remember (fun _ () -> ()) (fun _ _ () -> ()) in
    fst (fn () env sigma trm)

  let quote_mind_decl env sigma trm mib =
    let (_,fn) = quote_term_remember (fun _ () -> ()) (fun _ _ () -> ()) in
    let (_, indd, _) = fn () env sigma trm mib in indd

  type defType =
    Ind of Names.inductive * mutual_inductive_body
  | Const of KerName.t

  let universes_of_ctx ctx =
    Context.Rel.fold_inside (fun univs d -> Univ.Level.Set.union univs
      (Context.Rel.Declaration.fold_constr (fun c univs -> Univ.Level.Set.union univs (Vars.universes_of_constr c)) d univs))
      ~init:Univ.Level.Set.empty ctx

  let universes_of_mib mib =
    let pars = mib.mind_params_ctxt in
    let univs = universes_of_ctx pars in
    Array.fold_left
      (fun univs oib ->
         let univs =
           Univ.Level.Set.union univs
             (universes_of_ctx oib.mind_arity_ctxt)
         in
         let univs =
           Array.fold_left
             (fun univs cty ->
                Univ.Level.Set.union univs (Vars.universes_of_constr cty))
             univs oib.mind_user_lc
         in
         Array.fold_left
           (fun univs (ctx, cty) ->
              let univs =
                Univ.Level.Set.union univs (universes_of_ctx ctx)
              in
              Univ.Level.Set.union univs (Vars.universes_of_constr cty))
           univs oib.mind_nf_lc)
      univs mib.mind_packets

  let quote_term_rec ~bypass ~opaque_access ?(with_universes=true) ?(with_restriction=true) env sigma trm =
    let visited_terms = ref Names.KNset.empty in
    let visited_types = ref Mindset.empty in
    let universes = ref Univ.Level.Set.empty in
    let constants = ref [] in
    let template_defaults = ref Univ.Level.Set.empty in
    let template_universe_context = make_template_universe_context () in
    let () =
      current_decl_name := "<toplevel>";
      current_local_scope := None;
      extended_constants := Names.KerName.Map.empty;
      extended_inductives := Names.KerName.Map.empty;
      declarations_in_progress := Names.KNset.empty;
      current_quote_dependencies := new_quote_dependencies Environ.empty_env;
      template_universe_context.top_level <-
        Some (fresh_template_level (Environ.universes env)
                template_universe_context)
    in
    let top =
      match template_universe_context.top_level with
      | Some top -> top
      | None -> assert false
    in
    (* Quote declaration [kn] with [f], from a fresh dependency root: what the
       declaration reads is not a dependency of the subterm whose quotation
       reached it.  While [f] runs, [kn] is in progress, so a subterm referring
       to it is not cached (see [quote_dependencies.qd_unstable]). *)
    let quote_declaration kn f =
      let saved_dependencies = !current_quote_dependencies in
      let saved_in_progress = !declarations_in_progress in
      current_quote_dependencies := new_quote_dependencies Environ.empty_env;
      declarations_in_progress := Names.KNset.add kn saved_in_progress;
      let restore () =
        current_quote_dependencies := saved_dependencies;
        declarations_in_progress := saved_in_progress
      in
      match f () with
      | result -> restore (); result
      | exception e ->
        let e = Exninfo.capture e in
        restore ();
        Exninfo.iraise e
    in
    let add quote_term quote_type trm acc =
      match trm with
      | Ind ((mi,idx), mib) ->
        let t = mi in
        if Mindset.mem t !visited_types then ()
        else quote_declaration (MutInd.canonical mi) @@ fun () ->
          begin
            visited_types := Mindset.add t !visited_types;
            let saved_decl_name = !current_decl_name in
            current_decl_name := Pp.string_of_ppcmds (MutInd.print mi);
            let saved_local_scope = !current_local_scope in
            let original_universe_count =
              match mib.Declarations.mind_template,
                    mib.Declarations.mind_universes with
              | Some template, _ ->
                snd (UVars.AbstractContext.size template.template_context)
              | None, Declarations.Polymorphic auctx ->
                snd (UVars.AbstractContext.size auctx)
              | None, Declarations.Monomorphic -> 0
            in
            current_local_scope :=
              if Int.equal original_universe_count 0 then None
              else
                Some { ls_n_orig = original_universe_count;
                       ls_memo = Univ.Universe.Map.empty;
                       ls_definitions = [||];
                       ls_exprs = [];
                       ls_constraints = Univ.UnivConstraints.empty;
                       ls_next = 0 };
            let univs = universes_of_mib mib in
            let () = universes := Univ.Level.Set.union univs !universes in
            begin match mib.Declarations.mind_template with
            | None -> ()
            | Some template ->
              let _, defaults =
                UVars.Instance.to_array template.template_defaults
              in
              Array.iter
                (fun level ->
                   template_defaults :=
                     Univ.Level.Set.add level !template_defaults)
                defaults
            end;
            let (kn,d,acc) =
              try quote_type acc env sigma mi mib
              with e ->
                Feedback.msg_debug (str"Exception raised while checking " ++ MutInd.print mi);
                raise e
            in
            constants := (kn,d) :: !constants;
            current_local_scope := saved_local_scope;
            current_decl_name := saved_decl_name
          end
      | Const kn ->
        if Names.KNset.mem kn !visited_terms then ()
        else quote_declaration kn @@ fun () ->
          begin
            visited_terms := Names.KNset.add kn !visited_terms ;
            let saved_decl_name = !current_decl_name in
            current_decl_name := Pp.string_of_ppcmds (KerName.print kn);
            let saved_local_scope = !current_local_scope in
            let () =
              current_local_scope :=
                (match (Environ.lookup_constant (Names.Constant.make kn kn) env)
                         .const_universes with
                 | Declarations.Polymorphic auctx ->
                   Some { ls_n_orig = snd (UVars.AbstractContext.size auctx);
                          ls_memo = Univ.Universe.Map.empty;
                          ls_definitions = [||];
                          ls_exprs = [];
                          ls_constraints = Univ.UnivConstraints.empty;
                          ls_next = 0 }
                 | Declarations.Monomorphic -> None)
            in
            let c = Names.Constant.make kn kn in
            let cd = Environ.lookup_constant c env in
            let body = match cd.const_body with
              | Undef _ -> None
              | Primitive t ->
                  warn_primitive_turned_into_axiom (CPrimitives.to_string t);
                  None
              | Symbol _ ->
                  warn_symbol_turned_into_axiom (Constant.debug_to_string c);
                  None
              | Def cs -> Some cs
              | OpaqueDef lc ->
                if bypass then
                  let c, univs = Global.force_proof opaque_access lc in
                  match univs with
                  | Opaqueproof.PrivateMonomorphic () -> Some c
                  | Opaqueproof.PrivatePolymorphic csts ->
                    let () =
                      if not (Univ.ContextSet.is_empty csts) then
                        warn_ignoring_private_polymorphic_universes ()
                    in Some c
                else None
            in
            let tm, acc =
              match body with
              | None -> None, acc
              | Some tm ->
                let univs = Vars.universes_of_constr tm in
                let () = universes := Univ.Level.Set.union univs !universes in
                try let (tm, acc) = quote_term acc (Global.env ()) (Evd.from_env @@ Global.env ()) tm in
                  (Some tm, acc)
                with e ->
                  Feedback.msg_debug (str"Exception raised while checking body of " ++ KerName.print kn);
                  raise e
            in
            let ty, acc =
              let ty =
                match body with
                | None -> cd.const_type
                | Some body ->
                  let global_env = Global.env () in
                  let global_evm = Evd.from_env global_env in
                  let type_of_body =
                    EConstr.to_constr global_evm
                      (Retyping.get_type_of global_env global_evm
                         (EConstr.of_constr body))
                  in
                  normalize_template_type
                    ~universe_context:template_universe_context
                    (false, global_env) global_evm body type_of_body
              in
              let univs = Vars.universes_of_constr ty in
              let () = universes := Univ.Level.Set.union univs !universes in
              (try quote_term acc (Global.env ()) (Evd.from_env @@ Global.env ()) ty
                with e ->
                  Feedback.msg_debug (str"Exception raised while checking type of " ++ KerName.print kn);
                  raise e)
            in
            let rel = Q.quote_relevance cd.const_relevance in
            let uctx =
              match cd.const_universes, !current_local_scope with
              | Declarations.Polymorphic auctx, Some scope when scope.ls_next > 0 ->
                (* Extend this declaration's abstract universe context with the
                   fresh bound levels introduced for its algebraic template
                   instances, and their lower-bound constraints. *)
                let repr = UVars.AbstractContext.repr auctx in
                let { UVars.quals; UVars.univs } =
                  UVars.AbstractContext.names auctx
                in
                let extra =
                  Array.init scope.ls_next
                    (fun k ->
                       Names.Name
                         (Names.Id.of_string ("template_alg" ^ string_of_int k)))
                in
                let new_univs = Array.append univs extra in
                let new_pcon =
                  Univ.UnivConstraints.fold
                    (fun cstr pcon -> PConstraints.add_univ cstr pcon)
                    scope.ls_constraints
                    (UVars.UContext.constraints repr)
                in
                let new_auctx =
                  UVars.AbstractContext.make
                    { UVars.quals; UVars.univs = new_univs } new_pcon
                in
                Q.mkPolymorphic_ctx
                  (Q.quote_abstract_univ_context
                     (constrain_below_top top new_auctx))
              | Declarations.Polymorphic auctx, _ ->
                Q.mkPolymorphic_ctx
                  (Q.quote_abstract_univ_context (constrain_below_top top auctx))
              | _ -> quote_universes_decl cd.const_universes None
            in
            let () =
              match !current_local_scope with
              | Some scope when scope.ls_next > 0 ->
                extended_constants :=
                  Names.KerName.Map.add kn (List.rev scope.ls_exprs)
                    !extended_constants
              | _ -> ()
            in
            let cst_bdy = Q.mk_constant_body ty tm uctx rel in
            let decl = Q.mk_constant_decl cst_bdy in
            constants := (Q.quote_kn kn, decl) :: !constants;
            current_local_scope := saved_local_scope;
            current_decl_name := saved_decl_name
          end
    in
    let (quote_rem,quote_typ) =
      let a = ref (fun _ _ _ -> assert false) in
      let b = ref (fun _ _ _ -> assert false) in
      let (x,y) =
	      quote_term_remember ~universe_context:template_universe_context
          ~remember_universe_levels:(fun levels ->
            universes := Univ.Level.Set.union levels !universes)
          (fun x () -> add !a !b (Const x) ())
          (fun y mib () -> add !a !b (Ind (y, mib)) ())
      in
      a := x ;
      b := y ;
      (x,y)
    in
    let (tm, _) = quote_rem () env sigma trm in
    let decls = List.fold_right (fun (kn, d) acc -> Q.add_global_decl kn d acc) !constants (Q.empty_global_declarations ()) in
    let univs =
      if with_universes then
        if with_restriction then
          let univs =
            Univ.Level.Set.union (Vars.universes_of_constr trm) !universes
          in
          let univs =
            Univ.Level.Set.union univs template_universe_context.fresh_levels
          in
          let univs =
            Univ.Level.Set.filter
              (fun l -> Option.is_empty (Univ.Level.var_index l)) univs
          in
          let template_constraints =
            Univ.Level.Set.fold
              (fun level constraints ->
                 Univ.UnivConstraints.add
                   (Univ.Level.set, Univ.UnivConstraint.Le, level)
                   constraints)
              !template_defaults
              template_universe_context.fresh_constraints
          in
          (* A fresh level [a] stands for the algebraic universe [D_a] it was
             minted for, and has only the lower bounds [c <= a] of its
             components.  Add its upper bounds: [a <= l] for each kept level
             or fresh level [l] with [D_a <= D_l] in the environment's graph
             ([D_l = l] for a kept level).  Under the valuation
             [v(a) = v(D_a)] each of them holds, so the extension stays
             conservative.  Without them PCUIC cannot derive what the kernel
             checks on [D_a] itself, such as a record field of sort
             [max(u, v)] below the record's sort [max(u, v, w)]
             (a record whose field sort is a strict sub-maximum). *)
          let template_constraints =
            let graph = Environ.universes env in
            let definitions = template_universe_context.fresh_definitions in
            let definition_of level =
              match Univ.Level.Map.find_opt level definitions with
              | Some definition -> definition
              | None -> Univ.Universe.make level
            in
            let candidates =
              Univ.Level.Map.fold
                (fun level _ candidates -> Univ.Level.Set.add level candidates)
                definitions
                (Univ.Level.Set.inter univs (UGraph.domain graph))
            in
            let provably_leq u v =
              try UGraph.check_leq graph u v with _ -> false
            in
            time Pp.(str "Computing fresh template upper bounds")
              (Univ.Level.Map.fold
                 (fun fresh definition constraints ->
                    Univ.Level.Set.fold
                      (fun level constraints ->
                         if Univ.Level.equal fresh level
                            || not (provably_leq definition (definition_of level))
                         then constraints
                         else
                           Univ.UnivConstraints.add
                             (fresh, Univ.UnivConstraint.Le, level) constraints)
                      candidates constraints)
                 definitions)
              template_constraints
          in
          (* [top] is a new level with only incoming edges, so adding it keeps
             the graph acyclic: a conservative extension. *)
          let template_constraints =
            Univ.Level.Set.fold
              (fun level constraints ->
                 Univ.UnivConstraints.add
                   (level, Univ.UnivConstraint.Lt, top) constraints)
              (Univ.Level.Set.remove top
                 (Univ.Level.Set.add Univ.Level.set univs))
              template_constraints
          in
          let univs = Univ.Level.Set.add top univs in
          quote_ugraph ~kept:univs ~extra_constraints:template_constraints
            (Environ.universes env)
        else quote_ugraph (Environ.universes env)
      else
        (debug Pp.(fun () -> str"Skipping universes: ");
         time (Pp.str"Quoting empty universe context")
           (fun uctx -> Q.quote_contextset uctx) Univ.ContextSet.empty)
    in
    let retro =
      let retro = Environ.retroknowledge env in
      let quote_retro = Option.map (fun c -> Q.quote_kn (Names.Constant.canonical c)) in
      let pre =
        { Q.retro_int63 = quote_retro retro.Retroknowledge.retro_int63 ;
          Q.retro_float64 = quote_retro retro.Retroknowledge.retro_float64 ;
          Q.retro_string = quote_retro retro.Retroknowledge.retro_string ;
          Q.retro_array = quote_retro retro.Retroknowledge.retro_array }
      in Q.quote_retroknowledge pre
    in
    let env = Q.mk_global_env univs decls retro in
    Q.mk_program env tm

  let quote_rel_context env sigma ctx =
    fst (quote_rel_context (fun acc env sigma t -> (quote_term (snd env) sigma t, acc)) () ((), env) sigma ctx)

  let quote_one_ind envA envC (mi:Entries.one_inductive_entry) =
    let iname = Q.quote_ident mi.mind_entry_typename  in
    let arity = quote_term envA (Evd.from_env envA) mi.mind_entry_arity in
    let consnames = List.map Q.quote_ident (mi.mind_entry_consnames) in
    let constypes = List.map (quote_term envC (Evd.from_env envC)) (mi.mind_entry_lc) in
    (iname, arity, consnames, constypes)

  let quote_mind_params env (params: Constr.rel_context) =
    let qparams = quote_rel_context env (Evd.from_env env) params in
    (Environ.push_rel_context params env, qparams)

  let mind_params_as_types ((env,t):Environ.env*Constr.t) (params:Constr.rel_context) :
        Environ.env*Constr.t =
    (env, Term.it_mkProd_or_LetIn t params)

(*
  let empty_segment = Cooking.empty_cooking_info
  let quote_mut_ind env (mi:Declarations.mutual_inductive_body) =
   let t= Discharge.process_inductive empty_segment (Names.Cmap.empty,Names.Mindmap.empty) mi in
    let mf = Q.quote_mind_finiteness t.mind_entry_finite in
    let mp = (snd (quote_mind_params env (t.mind_entry_params))) in
    (* before quoting the types of constructors, we need to enrich the environment with the inductives *)
    let one_arities =
      List.map
        (fun x -> (x.mind_entry_typename,
                   snd (mind_params_as_types (env,x.mind_entry_arity) (t.mind_entry_params))))
        t.mind_entry_inds in
    (* env for quoting constructors of inductives. First push inductices, then params *)
    let envC = List.fold_left (fun env p -> Environ.push_rel (toDecl (Context.annotR (Names.Name (fst p)), None, snd p)) env) env (one_arities) in
    let envC = Environ.push_rel_context t.mind_entry_params envC in
    (* env for quoting arities of inductives -- just push the params *)
    let envA = Environ.push_rel_context t.mind_entry_params env in
    let is = List.map (quote_one_ind envA envC) t.mind_entry_inds in
    let uctx = quote_universes_entry t.mind_entry_universes in
    let variance = Option.map (CArray.map_to_list Q.quote_variance) t.mind_entry_variance in
    Q.quote_mutual_inductive_entry (mf, mp, is, uctx, variance) *)

  let quote_constant_body_aux bypass opaque_access env evm (cd : constant_body) =
    let ty = quote_term env evm cd.const_type in
    let body =
      match cd.const_body with
      | Undef _ -> None
      | Def cs -> Some (quote_term env evm cs)
      | OpaqueDef cs ->
        if bypass
        then Some (quote_term env evm (fst (Global.force_proof opaque_access cs)))
        else None
      | Primitive _ -> failwith "Primitive types not supported by TemplateRocq"
      | Symbol _ -> failwith "Symbols are not supported by TemplateRocq"
    in
    (ty, body)

  let quote_constant_body bypass opaque_access env evm cd =
    let ty, body = quote_constant_body_aux bypass opaque_access env evm cd in
    Q.mk_constant_body ty body (quote_universes_decl cd.const_universes None)
      (Q.quote_relevance cd.const_relevance)

  let quote_constant_entry bypass opaque_access env evm cd =
    let (ty, body) = quote_constant_body_aux bypass opaque_access env evm cd in
    let uctx = match cd.const_universes with
      | Polymorphic auctx -> Polymorphic_entry (UVars.AbstractContext.repr auctx)
      | Monomorphic -> Monomorphic_entry
    in
    let univs = quote_universes_entry uctx in
    match body with
    | None -> Q.quote_constant_entry (Right (Q.quote_parameter_entry ty univs))
    | Some body -> Q.quote_constant_entry (Left (Q.quote_definition_entry (Some ty) body univs))

  (* let quote_entry_aux bypass env evm (name:string) =
    let (dp, nm) = split_name name in
    match Nametab.locate (Libnames.make_qualid dp nm) with
    | Globnames.ConstRef c ->
      let cd = Environ.lookup_constant c env in
      (*CHANGE :  template polymorphism for definitions was removed.
                  See: https://github.com/coq/coq/commit/d9530632321c0b470ece6337cda2cf54d02d61eb *)
      Q.quote_entry (Left (quote_constant_entry bypass env evm cd))
    | Globnames.IndRef ni ->
      let c = Environ.lookup_mind (fst ni) env in (* FIX: For efficienctly, we should also export (snd ni)*)
      let miq = quote_mut_ind env c in
      Q.quote_entry (Right miq)
    | Globnames.ConstructRef _ -> raise Not_found (* FIX?: return the enclusing mutual inductive *)
    | Globnames.VarRef _ -> raise Not_found


  let quote_entry_of bypass env evm t =
    try Some (quote_entry_aux bypass env evm t)
    with Not_found -> None *)
end
