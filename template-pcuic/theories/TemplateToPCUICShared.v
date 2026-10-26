(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config Primitive EnvMap.
From MetaRocq.Template Require AstUtils TemplateProgram.
From MetaRocq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.

(** * The Template-to-PCUIC translation, computed so that it keeps sharing

  [trans_shared] is [TemplateToPCUIC.trans] with every node wrapped in
  [memo_trans].  In Rocq, [memo_trans Σ t k] is [k tt], so [trans_shared] is
  [trans] ([trans_shared_eq]) and every statement about [trans] holds of it.

  At extraction, [memo_trans] is the trusted OCaml memo [Trans_memo.memo]: it
  returns, for a physically shared Template subterm, the PCUIC value already
  computed for it, so a shared subterm is translated once and its translation
  is shared too.  [trans_memo_release] is the identity in Rocq; at extraction it
  drops the memo's table once a whole program is translated, so the table does
  not keep the Template program alive. *)

Definition memo_trans {A} (Σ : global_env_map) (t : Ast.term) (k : unit -> A) : A := k tt.

Definition trans_memo_release {A} (x : A) : A := x.

Section TransShared.
  Context (Σ : global_env_map).

  Fixpoint trans_shared (t : Ast.term) {struct t} : term :=
  memo_trans Σ t (fun _ =>
  match t with
  | Ast.tRel n => tRel n
  | Ast.tVar n => tVar n
  | Ast.tEvar ev args => tEvar ev (List.map trans_shared args)
  | Ast.tSort u => tSort u
  | Ast.tConst c u => tConst c u
  | Ast.tInd c u => tInd c u
  | Ast.tConstruct c k u => tConstruct c k u
  | Ast.tLambda na T M => tLambda na (trans_shared T) (trans_shared M)
  | Ast.tApp u v => mkApps (trans_shared u) (List.map trans_shared v)
  | Ast.tProd na A B => tProd na (trans_shared A) (trans_shared B)
  | Ast.tCast c kind t => tApp (tLambda (mkBindAnn nAnon rel_of_Type) (trans_shared t) (tRel 0)) (trans_shared c)
  | Ast.tLetIn na b t b' => tLetIn na (trans_shared b) (trans_shared t) (trans_shared b')
  | Ast.tCase ci p c brs =>
    let p' := Ast.map_predicate id trans_shared trans_shared p in
    let brs' := List.map (Ast.map_branch trans_shared) brs in
    match TransLookup.lookup_inductive Σ ci.(ci_ind) with
    | Some (mdecl, idecl) =>
      let tp := trans_predicate ci.(ci_ind) mdecl idecl p'.(Ast.pparams) p'.(Ast.puinst) p'.(Ast.pcontext) p'.(Ast.preturn) in
      let tbrs :=
        map2 (fun cdecl br => trans_branch ci.(ci_ind) mdecl cdecl br.(Ast.bcontext) br.(Ast.bbody))
                  idecl.(ind_ctors) brs' in
      tCase ci tp (trans_shared c) tbrs
    | None =>
      tCase ci {| pparams := p'.(Ast.pparams);
                  puinst := p'.(Ast.puinst);
                  pcontext := map (fun na => vass na (tSort Sort.type0)) p'.(Ast.pcontext);
                  preturn := p'.(Ast.preturn) |}
          (trans_shared c) []
    end
  | Ast.tProj p c => tProj p (trans_shared c)
  | Ast.tFix mfix idx =>
    let mfix' := List.map (map_def trans_shared trans_shared) mfix in
    tFix mfix' idx
  | Ast.tCoFix mfix idx =>
    let mfix' := List.map (map_def trans_shared trans_shared) mfix in
    tCoFix mfix' idx
  | Ast.tInt n => tPrim (primInt; primIntModel n)
  | Ast.tFloat n => tPrim (primFloat; primFloatModel n)
  | Ast.tString n => tPrim (primString; primStringModel n)
  | Ast.tArray l v d ty => tPrim (primArray; primArrayModel
    {| array_level := l;
       array_value := List.map trans_shared v;
       array_default := trans_shared d;
       array_type := trans_shared ty |})
  end).

  Definition trans_decl_shared (d : Ast.Env.context_decl) :=
    {| decl_name := d.(decl_name);
      decl_body := option_map trans_shared d.(decl_body);
      decl_type := trans_shared d.(decl_type) |}.

  Definition trans_local_shared Γ := List.map trans_decl_shared Γ.

  Definition trans_constructor_body_shared (d : Ast.Env.constructor_body) :=
    {| cstr_name := d.(Ast.Env.cstr_name);
      cstr_args := trans_local_shared d.(Ast.Env.cstr_args);
      cstr_indices := map trans_shared d.(Ast.Env.cstr_indices);
      cstr_type := trans_shared d.(Ast.Env.cstr_type);
      cstr_arity := d.(Ast.Env.cstr_arity) |}.

  Definition trans_projection_body_shared (d : Ast.Env.projection_body) :=
    {| proj_name := d.(Ast.Env.proj_name);
        proj_type := trans_shared d.(Ast.Env.proj_type);
        proj_relevance := d.(Ast.Env.proj_relevance) |}.

  Definition trans_one_ind_body_shared (d : Ast.Env.one_inductive_body) :=
    {| ind_name := d.(Ast.Env.ind_name);
      ind_relevance := d.(Ast.Env.ind_relevance);
      ind_indices := trans_local_shared d.(Ast.Env.ind_indices);
      ind_sort := d.(Ast.Env.ind_sort);
      ind_type := trans_shared d.(Ast.Env.ind_type);
      ind_kelim := d.(Ast.Env.ind_kelim);
      ind_ctors := List.map trans_constructor_body_shared d.(Ast.Env.ind_ctors);
      ind_projs := List.map trans_projection_body_shared d.(Ast.Env.ind_projs) |}.

  Definition trans_constant_body_shared bd :=
    {| cst_type := trans_shared bd.(Ast.Env.cst_type);
       cst_body := option_map trans_shared bd.(Ast.Env.cst_body);
       cst_universes := bd.(Ast.Env.cst_universes);
       cst_relevance := bd.(Ast.Env.cst_relevance) |}.

  Definition trans_minductive_body_shared md :=
    {| ind_finite := md.(Ast.Env.ind_finite);
      ind_npars := md.(Ast.Env.ind_npars);
      ind_params := trans_local_shared md.(Ast.Env.ind_params);
      ind_bodies := map trans_one_ind_body_shared md.(Ast.Env.ind_bodies);
      ind_universes := md.(Ast.Env.ind_universes);
      ind_variance := md.(Ast.Env.ind_variance) |}.

  Definition trans_global_decl_shared (d : Ast.Env.global_decl) :=
    match d with
    | Ast.Env.ConstantDecl bd => ConstantDecl (trans_constant_body_shared bd)
    | Ast.Env.InductiveDecl bd => InductiveDecl (trans_minductive_body_shared bd)
    end.
End TransShared.

Definition trans_global_decls_shared env (d : Ast.Env.global_declarations) : global_env_map :=
  fold_right (fun decl Σ' =>
    let decl' := on_snd (trans_global_decl_shared Σ') decl in
    TemplateToPCUIC.add_global_decl Σ' decl') env d.

Definition trans_global_env_shared (d : Ast.Env.global_env) : global_env_map :=
  let init := empty_trans_env d.(Ast.Env.universes) d.(Ast.Env.retroknowledge) in
  trans_global_decls_shared init d.(Ast.Env.declarations).

(** ** The shared translation is the translation

    [memo_trans Σ t k] unfolds to [k tt].  After that delta and a beta step, the
    body of the fixpoint [trans_shared Σ] is the body of [trans Σ], so the two
    fixpoints are convertible; each shared definition below is the original
    one with [trans_shared] for [trans], so it is convertible to the original
    too.  Every equation therefore holds by [reflexivity], which the kernel
    checks again at [Qed]. *)

Lemma trans_shared_eq Σ t : trans_shared Σ t = trans Σ t.
Proof. reflexivity. Qed.

Lemma trans_decl_shared_eq Σ d : trans_decl_shared Σ d = trans_decl Σ d.
Proof. reflexivity. Qed.

Lemma trans_local_shared_eq Σ Γ : trans_local_shared Σ Γ = trans_local Σ Γ.
Proof. reflexivity. Qed.

Lemma trans_constructor_body_shared_eq Σ d :
  trans_constructor_body_shared Σ d = trans_constructor_body Σ d.
Proof. reflexivity. Qed.

Lemma trans_projection_body_shared_eq Σ d :
  trans_projection_body_shared Σ d = trans_projection_body Σ d.
Proof. reflexivity. Qed.

Lemma trans_one_ind_body_shared_eq Σ d :
  trans_one_ind_body_shared Σ d = trans_one_ind_body Σ d.
Proof. reflexivity. Qed.

Lemma trans_constant_body_shared_eq Σ bd :
  trans_constant_body_shared Σ bd = trans_constant_body Σ bd.
Proof. reflexivity. Qed.

Lemma trans_minductive_body_shared_eq Σ md :
  trans_minductive_body_shared Σ md = trans_minductive_body Σ md.
Proof. reflexivity. Qed.

Lemma trans_global_decl_shared_eq Σ d :
  trans_global_decl_shared Σ d = trans_global_decl Σ d.
Proof. reflexivity. Qed.

(** The environment is built by the same fold with the same [add_global_decl]
    and convertible declaration translations. *)
Lemma trans_global_decls_shared_eq env d :
  trans_global_decls_shared env d = trans_global_decls env d.
Proof. reflexivity. Qed.

Lemma trans_global_env_shared_eq d : trans_global_env_shared d = trans_global_env d.
Proof. reflexivity. Qed.
