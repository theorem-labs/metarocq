(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICReflect PCUICTyping
  PCUICArityRed.
From MetaRocq.SafeChecker Require Import PCUICErrors.

Import MonadNotation.

(** * Checking strict positivity, including nested inductive types

  The functions below decide the positivity relations of
  [common/theories/EnvironmentTyping.v] ([positive_cstr_arg], [positive_args],
  [positive_nested_ctors], [positive_nested_cstr] and [positive_cstr]) soundly: a
  [Checked tt] answer yields a derivation, a [TypeError] answer says nothing.

  The only things they need from the global environment are the declarations of a
  nesting inductive and of the constants that weak-head reduction unfolds, so they take
  a lookup function as a parameter; [PCUICSafeChecker] instantiates it with the abstract
  environment.  This keeps the checker and its soundness proof independent of the rest
  of the safe checker.

  A constructor argument type is put in weak-head normal form when its syntax alone does
  not show it positive, as Rocq's kernel does ([check_strict_positivity],
  kernel/indtypes.ml).  The terms of the nested walk are not well typed, so the typed
  reduction of the safe checker cannot be used: [whd_fuel] is an untyped weak-head
  machine on a fuel, which follows the relation [whd_rel true] rule by rule.

  Positivity checking reduces let-ins and, in the nested case, walks the constructors of
  another inductive type, which are not subterms of the term being checked.  The check is
  therefore structurally recursive on a fuel rather than on the term.  Every call spends
  one unit, including the calls that walk a list of arguments or of constructors, so the
  fuel bounds the length of one call path, which grows with both the nesting depth and
  the length of those lists.  Running out of fuel is a rejection, never an acceptance, so
  the fuel is an incompleteness and not a hole in soundness. *)

Implicit Types (mdecl : mutual_inductive_body) (NI : nested_insts) (Γ : context).

(** Far beyond the call depth that any declaration Rocq produces needs.  It bounds the
    calls of one path of the positivity check, and also the steps of one reduction path
    of [whd_fuel]: a reduction that needs more steps is refused, as when no rule applies.
    It is written with small numerals: with the numeral [10000], the extracted module
    referred to the [app] of the module [Decimal] where list append was meant, and OCaml
    refused to compile it. *)
Definition positivity_fuel := Nat.pow 10 4.

(** ** Decision procedures for the side conditions *)

(** An occurrence of an enclosing nesting variable must repeat the recorded instance. *)
Definition nested_inst_okb NI Γ (x : nat) (l : list term) : bool :=
  existsb (fun e =>
    [&& Nat.ltb e.(ni_level) #|Γ|, Nat.eqb x (#|Γ| - S e.(ni_level)),
        eqb (firstn e.(ni_npars) l) (map (lift0 (#|Γ| - e.(ni_level))) e.(ni_args)) &
        forallb (closedn #|Γ|) (skipn e.(ni_npars) l)]) NI.

Lemma nested_inst_okb_spec NI Γ x l :
  nested_inst_okb NI Γ x l -> nested_inst_ok NI Γ x l.
Proof.
  rewrite /nested_inst_okb /nested_inst_ok.
  induction NI as [|e NI IH]; cbn => //.
  case he: [&& _, _, _ & _] => /= h.
  - exists 0, e.
    move/and4P: he => [] hlvl hx hfi hcl.
    split.
    + reflexivity.
    + now apply Nat.ltb_lt.
    + now apply Nat.eqb_eq.
    + now apply (eqb_eq (A:=list term)).
    + exact hcl.
  - destruct (IH h) as [j [e' [hnth h1 h2 h3 h4]]]. exists (S j), e'; split => //.
Qed.

(** The candidate uniformity witness: the constructor's body with a fresh variable in place
    of every occurrence of the nesting inductive applied to its first [k] parameter
    variables.  Nothing is proved about this function: the checker tests the equations of
    [nested_uniform_cstr] on its result, so a wrong candidate can only make a test fail. *)
Section AbstractRec.
  Context (ind_var : nat) (k : nat) (pvars : list term).

  Fixpoint abstract_rec (d : nat) (t : term) {struct t} : term :=
    match t with
    | tApp f a =>
      (* Walk the application spine, so that the recursion stays structural. *)
      let fix spine (h : term) (args args' : list term) {struct h} : term :=
        match h with
        | tApp h' x => spine h' (x :: args) (abstract_rec d x :: args')
        | tRel i =>
          if Nat.eqb i (S ind_var + d) && eqb (firstn k args) (map (lift0 (S d)) pvars)
          then mkApps (tRel d) (skipn k args')
          else mkApps h args'
        | _ => mkApps (abstract_rec d h) args'
        end in
      spine f [a] [abstract_rec d a]
    | tProd na ty b => tProd na (abstract_rec d ty) (abstract_rec (S d) b)
    | tLambda na ty b => tLambda na (abstract_rec d ty) (abstract_rec (S d) b)
    | tLetIn na b ty b' => tLetIn na (abstract_rec d b) (abstract_rec d ty) (abstract_rec (S d) b')
    | _ => t
    end.
End AbstractRec.

Definition check_nested_uniform_cstr (mdecl' : mutual_inductive_body) (k : nat)
  (cdecl' : constructor_body) : bool :=
  let params := ind_params mdecl' in
  match decompose_prod_n_assum [] #|params| (cstr_type cdecl') with
  | Some (_, rest) =>
    let pvars := firstn k (to_extended_list params) in
    (* Abstract every uniform occurrence.  An occurrence left behind is the inductive's
       own variable at [S #|params|], which the closedness test refuses. *)
    let rest1 := abstract_rec #|params| k pvars 0 (lift0 1 rest) in
    [&& eqb (cstr_type cdecl') (it_mkProd_or_LetIn params rest),
        eqb rest (subst [mkApps (tRel #|params|) pvars] 0 rest1) &
        closedn (S #|params|) rest1]
  | None => false
  end.

Lemma check_nested_uniform_cstr_spec mdecl' k cdecl' :
  check_nested_uniform_cstr mdecl' k cdecl' -> nested_uniform_cstr mdecl' k cdecl'.
Proof.
  rewrite /check_nested_uniform_cstr /nested_uniform_cstr.
  destruct decompose_prod_n_assum as [[params' rest]|] => //.
  move/and3P=> [] heq hsub hcl.
  eexists rest, _. split; [apply (eqb_eq (A:=term)), heq|apply (eqb_eq (A:=term)), hsub|exact hcl].
Qed.

(** The single-body condition is not tested here: it follows from the lookup (see
    [check_positive_app_sound]). *)
Definition check_nested_uniform (mdecl' : mutual_inductive_body) (idecl' : one_inductive_body)
  (k : nat) : bool :=
  Nat.leb k (context_assumptions (ind_params mdecl')) &&
  forallb (check_nested_uniform_cstr mdecl' k) (ind_ctors idecl').

Lemma check_nested_uniform_spec mdecl' idecl' k :
  ind_bodies mdecl' = [idecl'] ->
  check_nested_uniform mdecl' idecl' k -> nested_uniform mdecl' idecl' k.
Proof.
  rewrite /check_nested_uniform /nested_uniform => hb.
  move/andP=> [] hk hc. apply Nat.leb_le in hk.
  split => //. eapply forallb_All in hc. eapply All_impl; [exact hc|].
  cbn; intros. now apply check_nested_uniform_cstr_spec.
Qed.

Definition check_nested_variance mdecl : bool :=
  match ind_variance mdecl with
  | None => true
  | Some v => forallb (fun x => match x with Variance.Covariant => false | _ => true end) v
  end.

Lemma check_nested_variance_spec mdecl :
  check_nested_variance mdecl -> nested_variance_ok mdecl.
Proof.
  rewrite /check_nested_variance /nested_variance_ok.
  destruct ind_variance as [v|] => //.
  move/forallb_Forall => h. eapply Forall_impl; [exact h|].
  cbn; intros x. now destruct x.
Qed.

(** The split [k]: one more than the position of the last argument that mentions the
    block, so that the arguments from [k] on are block-free, as the kernel requires of a
    nested occurrence's non-uniform arguments and indices ([check_positivity_nested] in
    kernel/indtypes.ml). *)
Definition nested_split (n : nat) (args : list term) : nat :=
  fst (fold_left (fun acc a =>
         (if closedn n a then fst acc else S (snd acc), S (snd acc))) args (0, 0)).

(** A declaration with one body, read through the lookup at [inductive_ind ind], is that
    body. *)
Lemma single_body_eq {mdecl' : mutual_inductive_body} {n idecl'} :
  #|ind_bodies mdecl'| = 1 ->
  nth_error (ind_bodies mdecl') n = Some idecl' ->
  ind_bodies mdecl' = [idecl'].
Proof.
  destruct (ind_bodies mdecl') as [|b [|b' l]] => //= _.
  destruct n as [|n]; cbn; [congruence|].
  now rewrite nth_error_nil.
Qed.
(** The binder of the context entry that stands for a nesting inductive.  The rule reads
    only its position, so any name and relevance will do. *)
Definition nested_binder : aname := mkBindAnn nAnon Relevant.


Section Check.
  (** The global environment's declarations, by name. *)
  Context (lookup : kername -> option global_decl).
  (** The operation table: the registered primitive operation of a constant.  Weak-head
      reduction REFUSES on a registered operation ([None] below) rather than firing it:
      the relation [whd_rel true] fires a saturated literal application, which this
      untyped machine does not implement, and answering "stuck" there would be unsound.
      Refusing is sound and costs only completeness: positivity is refused for a
      constructor argument type whose weak-head reduction meets a registered operation
      (the row-Q2 risk named in the design, §12). *)
  Context (lookup_op : kername -> option prim_op).

  (** The declaration of a nesting inductive. *)
  Definition lookup_ind (ind : inductive) :
    typing_result (mutual_inductive_body × one_inductive_body) :=
    match lookup ind.(inductive_mind) with
    | Some (InductiveDecl mdecl') =>
      match nth_error (ind_bodies mdecl') ind.(inductive_ind) with
      | Some idecl' => ret (mdecl', idecl')
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.

  (** ** Weak-head reduction

    [whd_fuel fuel Γ t args] reduces [t] applied to [args] in [Γ] with the rules of
    [whd_rel true], one rule per step, and returns the head and arguments the relation
    stops at.  It returns [None] when no rule applies (a variable outside [Γ], a constant
    that the lookup does not declare as a constant, a match or projection on a
    constructor that has no matching branch or field, a cofixpoint that does not unfold)
    or when the fuel runs out.  The machine shares nothing, so a reduction that the
    kernel's lazy machine does in linear time can take exponential time here: the fuel
    bounds the depth of the reduction, not the total work. *)
  Fixpoint whd_fuel (fuel : nat) Γ (t : term) (args : list term) {struct fuel}
    : option (term × list term) :=
    match fuel with
    | 0 => None
    | S fuel =>
      match t with
      | tRel c =>
        match nth_error Γ c with
        | Some d =>
          match d.(decl_body) with
          | Some b => whd_fuel fuel Γ (lift0 (S c) b) args
          | None => Some (tRel c, args)
          end
        | None => None
        end
      | tLetIn na b B t => whd_fuel fuel Γ (subst0 [b] t) args
      | tConst c u =>
        match lookup c with
        | Some (ConstantDecl decl) =>
          match decl.(cst_body) with
          | Some body => whd_fuel fuel Γ (subst_instance u body) args
          | None =>
            match lookup_op c with
            | Some _ => None
            | None => Some (tConst c u, args)
            end
          end
        | _ => None
        end
      | tApp f a => whd_fuel fuel Γ f (a :: args)
      | tLambda na A t =>
        match args with
        | a :: args => whd_fuel fuel Γ (subst0 [a] t) args
        | [] => Some (tLambda na A t, [])
        end
      | tFix mfix idx =>
        match unfold_fix mfix idx with
        | Some (narg, fn) =>
          match nth_error args narg with
          | Some c =>
            match whd_fuel fuel Γ c [] with
            | Some (tConstruct ind n ui, cargs) =>
              whd_fuel fuel Γ fn
                (firstn narg args ++ mkApps (tConstruct ind n ui) cargs :: skipn (S narg) args)
            | Some (t', cargs) =>
              Some (tFix mfix idx, firstn narg args ++ mkApps t' cargs :: skipn (S narg) args)
            | None => None
            end
          | None => Some (tFix mfix idx, args)
          end
        | None => Some (tFix mfix idx, args)
        end
      | tCase ci p c brs =>
        match whd_fuel fuel Γ c [] with
        | Some (tConstruct ind n ui, cargs) =>
          if eqb ind ci.(ci_ind) then
            match nth_error brs n with
            | Some br =>
              if Nat.eqb #|cargs| (ci.(ci_npar) + context_assumptions br.(bcontext)) then
                whd_fuel fuel Γ (iota_red ci.(ci_npar) p cargs br) args
              else None
            | None => None
            end
          else None
        | Some (tCoFix mfix idx, cargs) =>
          match unfold_cofix mfix idx with
          | Some (narg, fn) => whd_fuel fuel Γ (tCase ci p (mkApps fn cargs) brs) args
          | None => None
          end
        | Some (t', cargs) => Some (tCase ci p (mkApps t' cargs) brs, args)
        | None => None
        end
      | tProj p c =>
        match whd_fuel fuel Γ c [] with
        | Some (tConstruct ind 0 u, cargs) =>
          if eqb ind p.(proj_ind) then
            match nth_error cargs (p.(proj_npars) + p.(proj_arg)) with
            | Some a => whd_fuel fuel Γ a args
            | None => None
            end
          else None
        | Some (tCoFix mfix idx, cargs) =>
          match unfold_cofix mfix idx with
          | Some (narg, fn) => whd_fuel fuel Γ (tProj p (mkApps fn cargs)) args
          | None => None
          end
        | Some (t', cargs) => Some (tProj p (mkApps t' cargs), args)
        | None => None
        end
      | t => Some (t, args)
      end
    end.

  (** The context in which the rules of [positive_cstr_arg] reduce. *)
  Definition positivity_context mdecl Γ : context := arities_context (ind_bodies mdecl) ,,, Γ.

  (** An argument of a variable head, in weak-head normal form unless it is closed or
      does not reduce. *)
  Definition whd_arg mdecl Γ (a : term) : term :=
    if closedn #|Γ| a then a
    else match whd_fuel positivity_fuel (positivity_context mdecl Γ) a [] with
         | Some (h, l) => mkApps h l
         | None => a
         end.

  (** The number of leading arguments of the variable [x] that are kept as written: for an
      enclosing nesting variable, its instantiating arguments, which [nested_inst_okb]
      compares with the recorded instance as written (Rocq's kernel drops them,
      [drop_params] in kernel/inductive.ml); for any other variable, none. *)
  Definition kept_args NI Γ (x : nat) : nat :=
    match List.find (fun e => Nat.ltb e.(ni_level) #|Γ| && Nat.eqb x (#|Γ| - S e.(ni_level))) NI with
    | Some e => e.(ni_npars)
    | None => 0
    end.

  (** The arguments of the variable [x], the ones after the kept ones in weak-head normal
      form. *)
  Definition whd_var_args mdecl NI Γ (x : nat) (args : list term) : list term :=
    let n := kept_args NI Γ x in
    firstn n args ++ map (whd_arg mdecl Γ) (skipn n args).

  (** The heads after which a reduct is checked again. *)
  Definition positivity_head (t : term) : bool :=
    match t with
    | tProd _ _ _ | tRel _ | tInd _ _ => true
    | _ => false
    end.

  (** The reduction cases of [positive_cstr_arg] for a term that is neither a product nor
      a let, with the recursive check [rec] and the syntactic application check [app]
      passed as arguments.  A variable head has its arguments reduced; if that changes
      some of them, the result is checked again (a closed result is then accepted),
      else the syntactic check decides.  An inductive head is checked as written.  Any
      other head is reduced, and the reduct is checked again when it is closed or has a
      head that the rules read. *)
  Definition check_positive_whd (rec app : term -> typing_result unit) mdecl NI Γ (t : term)
    : typing_result unit :=
    match decompose_app t with
    | (tRel k, args) =>
      let args' := whd_var_args mdecl NI Γ k args in
      if eqb args' args then app t else rec (mkApps (tRel k) args')
    | (tInd _ _, _) => app t
    | _ =>
      match whd_fuel positivity_fuel (positivity_context mdecl Γ) t [] with
      | Some (h, l) =>
        if closedn #|Γ| (mkApps h l) || positivity_head h then rec (mkApps h l)
        else raise (Msg "Positivity: the block occurs under a head that is neither a member of the block nor an inductive")
      | None => raise (Msg "Positivity: the block occurs under a head that is neither a member of the block nor an inductive")
      end
    end.

  (** The application case of [positive_cstr_arg], with the recursive checks it needs
      passed as arguments, so that it can be reasoned about once for every head. *)
  Definition check_positive_app
    (args_check : nested_insts -> context -> list term -> typing_result unit)
    (ctors_check : nested_insts -> context -> list term -> nat -> list term -> typing_result unit)
    mdecl NI Γ (t : term) : typing_result unit :=
    match decompose_app t with
    | (tRel hdrel, args) =>
      if (Nat.leb #|Γ| hdrel) && (Nat.ltb hdrel (#|Γ| + #|ind_bodies mdecl|)) then
        match nth_error (List.rev mdecl.(ind_bodies)) (hdrel - #|Γ|) with
        | Some i =>
          if forallb (closedn #|Γ|) args then
            if Nat.eqb (ind_realargs mdecl i) #|args| then ret tt
            else raise (Msg "Partial application of inductive")
          else raise (Msg "Conclusion arguments refer to the inductive type being defined")
        | None => raise (Msg "Conclusion is not an inductive type")
        end
      else if nested_inst_okb NI Γ hdrel args then ret tt
      else raise (Msg "Positivity: the block occurs in an argument of a variable that is not an inductive of the block")
    | (tInd ind u, args) =>
      let k := nested_split #|Γ| args in
      mi <- lookup_ind ind ;;
      if negb (Nat.eqb #|ind_bodies (fst mi)| 1) then
        raise (Msg "Nested positivity: the nested inductive is mutual")
      else if negb (check_nested_variance mdecl) then
        raise (Msg "Nested positivity: the block has a covariant universe level")
      else if negb (check_nested_uniform (fst mi) (snd mi) k) then
        raise (Msg "Nested positivity: the block occurs in an argument that is not a uniform parameter")
      else if negb (Nat.leb k #|args| && forallb (closedn #|Γ|) (skipn k args)) then
        raise (Msg "Nested positivity: the block occurs in an argument that is not a uniform parameter")
      else
        args_check NI Γ (firstn k args) ;;
        ctors_check
          ({| ni_level := #|Γ|; ni_npars := k; ni_args := firstn k args |} :: NI)
          (vass nested_binder (mkApps (tInd ind u) (firstn k args)) :: Γ)
          (map (lift0 1) (firstn k args))
          (context_assumptions (ind_params (fst mi)) - k)
          (map (fun c => subst_instance u (cstr_type c)) (ind_ctors (snd mi)))
    | _ => raise (Msg "Positivity: the block occurs under a head that is neither a member of the block nor an inductive")
    end.

  (** The conclusion of a constructor of a nesting inductive. *)
  Definition check_nested_concl NI Γ (t : term) : typing_result unit :=
    match decompose_app t with
    | (tRel x, l) =>
      if nested_inst_okb NI Γ x l then ret tt
      else raise (Msg "Nested positivity: a constructor of the nesting inductive does not conclude at its own instance")
    | _ => raise (Msg "Nested positivity: a constructor of the nesting inductive does not conclude at its own instance")
    end.

  Fixpoint check_positive_cstr_arg (fuel : nat) mdecl NI Γ (t : term) {struct fuel}
    : typing_result unit :=
    match fuel with
    | 0 => raise (Msg "Nested positivity: out of fuel")
    | S fuel =>
      if closedn #|Γ| t then ret tt
      else
      match t with
      | tProd na ty t =>
        if closedn #|Γ| ty then check_positive_cstr_arg fuel mdecl NI (vass na ty :: Γ) t
        else
          (* A domain that mentions the block is accepted when its weak-head normal form
             does not. *)
          match whd_fuel positivity_fuel (positivity_context mdecl Γ) ty [] with
          | Some (h, l) =>
            if closedn #|Γ| (mkApps h l) then
              check_positive_cstr_arg fuel mdecl NI (vass na ty :: Γ) t
            else raise (Msg "Non-positive occurrence.")
          | None => raise (Msg "Non-positive occurrence.")
          end
      | tLetIn na b ty t => check_positive_cstr_arg fuel mdecl NI Γ (subst0 [b] t)
      | t => check_positive_whd (check_positive_cstr_arg fuel mdecl NI Γ)
               (check_positive_app (check_positive_args fuel mdecl)
                  (check_positive_nested_ctors fuel mdecl) mdecl NI Γ) mdecl NI Γ t
      end
    end

  with check_positive_args (fuel : nat) mdecl NI Γ (l : list term) {struct fuel}
    : typing_result unit :=
    match fuel with
    | 0 => raise (Msg "Nested positivity: out of fuel")
    | S fuel =>
      match l with
      | [] => ret tt
      | t :: l =>
        check_positive_cstr_arg fuel mdecl NI Γ t ;;
        check_positive_args fuel mdecl NI Γ l
      end
    end

  with check_positive_nested_ctors (fuel : nat) mdecl NI Γ (ps : list term) (nskip : nat)
    (cs : list term) {struct fuel} : typing_result unit :=
    match fuel with
    | 0 => raise (Msg "Nested positivity: out of fuel")
    | S fuel =>
      match cs with
      | [] => ret tt
      | c :: cs =>
        check_positive_nested_cstr fuel mdecl NI Γ ps nskip c ;;
        check_positive_nested_ctors fuel mdecl NI Γ ps nskip cs
      end
    end

  with check_positive_nested_cstr (fuel : nat) mdecl NI Γ (ps : list term) (nskip : nat)
    (t : term) {struct fuel} : typing_result unit :=
    match fuel with
    | 0 => raise (Msg "Nested positivity: out of fuel")
    | S fuel =>
      match t, ps, nskip with
      | tLetIn na b ty t, _, _ => check_positive_nested_cstr fuel mdecl NI Γ ps nskip (subst0 [b] t)
      | tProd na ty t, p :: ps, _ => check_positive_nested_cstr fuel mdecl NI Γ ps nskip (subst0 [p] t)
      | tProd na ty t, [], S n => check_positive_nested_cstr fuel mdecl NI (vass na ty :: Γ) [] n t
      | tProd na ty t, [], 0 =>
        check_positive_cstr_arg fuel mdecl NI Γ ty ;;
        check_positive_nested_cstr fuel mdecl NI (vass na ty :: Γ) [] 0 t
      | t, [], 0 => check_nested_concl NI Γ t
      | _, _, _ => raise (Msg "Nested positivity: the nesting inductive has fewer parameters than the occurrence has arguments")
      end
    end.

  (** A whole constructor type. *)
  Fixpoint check_positive_cstr (fuel : nat) mdecl (n : nat) Γ (t : term) {struct fuel}
    : typing_result unit :=
    match fuel with
    | 0 => raise (Msg "Nested positivity: out of fuel")
    | S fuel =>
      match t with
      | tProd na ty t =>
        check_positive_cstr_arg positivity_fuel mdecl [] Γ ty ;;
        check_positive_cstr fuel mdecl n (vass na ty :: Γ) t
      | tLetIn na b ty t => check_positive_cstr fuel mdecl n Γ (subst0 [b] t)
      | t =>
        let '(hd, indices) := decompose_app t in
        if eqb hd (tRel (#|ind_bodies mdecl| - S n + #|Γ|)) then
          if forallb (closedn #|Γ|) indices then ret tt
          else raise (Msg "Arguments of the inductive in the conclusion of a constructor mention the inductive itself")
        else raise (Msg "Conclusion of constructor is not the right inductive type")
      end
    end.

  (** ** Soundness *)

  Context (Σ : global_env) (lookup_spec : forall kn, lookup kn = lookup_env Σ kn)
    (lookup_op_spec : forall kn, lookup_op kn = prim_op_of Σ kn).

  Lemma bind_checked_tt {A} (m : typing_result A) (f : A -> typing_result unit) :
    @bind typing_result _ A unit m f = Checked tt -> ∑ a, (m = Checked a) × (f a = Checked tt).
  Proof. destruct m as [a|e] => //= h. now exists a. Qed.

  Lemma lookup_ind_spec ind mi :
    lookup_ind ind = Checked mi -> declared_inductive Σ ind (fst mi) (snd mi).
  Proof.
    rewrite /lookup_ind.
    destruct lookup as [[|mdecl']|] eqn:look => //.
    destruct nth_error eqn:hnth => //.
    intros [= <-]. split => //.
    eapply declared_minductive_from_gen. red. rewrite -lookup_spec. exact look.
  Qed.

  Lemma whd_fuel_sound fuel Γ t args h l :
    whd_fuel fuel Γ t args = Some (h, l) -> whd_rel true Σ Γ t args h l.
  Proof.
    induction fuel as [|fuel IH] in Γ, t, args, h, l |- *; [discriminate|].
    cbn [whd_fuel].
    destruct t as [n|i|n l'|u|na A B|na A t|na b B t|f a|k ui|ind ui|ind n ui|ci p c brs|p c
      |mfix idx|mfix idx|prim]; intros e;
      try solve [injection e as <- <-; now apply whd_stop].
    - (* tRel *)
      destruct (nth_error Γ n) as [d|] eqn:hn; [|discriminate].
      destruct (decl_body d) as [b|] eqn:hb.
      + eapply whd_rel_unfold; [exact hn|exact hb|now apply IH].
      + injection e as <- <-. eapply whd_rel_assum; [exact hn|exact hb].
    - (* tLambda *)
      destruct args as [|a args].
      + injection e as <- <-. now apply whd_stop.
      + apply whd_beta. now apply IH.
    - (* tLetIn *)
      apply whd_zeta; [reflexivity|now apply IH].
    - (* tApp *)
      apply whd_app. now apply IH.
    - (* tConst *)
      destruct (lookup k) as [[decl|]|] eqn:hl; try discriminate.
      rewrite lookup_spec in hl.
      destruct (cst_body decl) as [body|] eqn:hb.
      + eapply whd_delta; [exact hl|exact hb|now apply IH].
      + destruct (lookup_op k) as [op|] eqn:ho; [discriminate|].
        injection e as <- <-. eapply whd_axiom; [exact hl|exact hb|].
        now rewrite -lookup_op_spec.
    - (* tCase *)
      destruct (whd_fuel fuel Γ c []) as [[t' cargs]|] eqn:hc; [|discriminate].
      apply IH in hc.
      destruct t' as [| | | | | | | | | |ind n ui| | | |mfix idx|];
        try solve [injection e as <- <-;
        eapply whd_case_stuck; [exact hc|reflexivity|reflexivity]].
      + (* a constructor *)
        destruct (eqb ind (ci_ind ci)) eqn:hind; [|discriminate].
        apply eqb_eq in hind. subst ind.
        destruct (nth_error brs n) as [br|] eqn:hbr; [|discriminate].
        destruct (Nat.eqb #|cargs| (ci_npar ci + context_assumptions (bcontext br))) eqn:hlen;
          [|discriminate].
        apply Nat.eqb_eq in hlen.
        eapply whd_iota; [exact hc|exact hbr|exact hlen|now apply IH].
      + (* a cofixpoint *)
        destruct (unfold_cofix mfix idx) as [[narg fn]|] eqn:hu; [|discriminate].
        eapply whd_case_cofix; [exact hc|exact hu|now apply IH].
    - (* tProj *)
      destruct (whd_fuel fuel Γ c []) as [[t' cargs]|] eqn:hc; [|discriminate].
      apply IH in hc.
      destruct t' as [| | | | | | | | | |ind n ui| | | |mfix idx|];
        try solve [injection e as <- <-;
        eapply whd_proj_stuck; [exact hc|reflexivity|reflexivity]].
      + (* constructor 0 *)
        destruct n as [|n]; [|injection e as <- <-;
          eapply whd_proj_stuck; [exact hc|reflexivity|reflexivity]].
        destruct (eqb ind (proj_ind p)) eqn:hind; [|discriminate].
        apply eqb_eq in hind. subst ind.
        destruct (nth_error cargs (proj_npars p + proj_arg p)) as [a|] eqn:ha; [|discriminate].
        eapply whd_proj; [exact hc|exact ha|now apply IH].
      + (* a cofixpoint *)
        destruct (unfold_cofix mfix idx) as [[narg fn]|] eqn:hu; [|discriminate].
        eapply whd_proj_cofix; [exact hc|exact hu|now apply IH].
    - (* tFix *)
      destruct (unfold_fix mfix idx) as [[narg fn]|] eqn:hu.
      + destruct (nth_error args narg) as [c|] eqn:hn.
        * destruct (whd_fuel fuel Γ c []) as [[t' cargs]|] eqn:hc; [|discriminate].
          apply IH in hc.
          destruct t' as [| | | | | | | | | |ind n ui| | | | |]; try solve [injection e as <- <-;
            eapply whd_fix_stuck; [exact hu|exact hn|exact hc|reflexivity]].
          eapply whd_fix_iota; [exact hu|exact hn|exact hc|now apply IH].
        * injection e as <- <-. eapply whd_fix_noarg; [exact hu|exact hn].
      + injection e as <- <-. now apply whd_fix_nounfold.
  Qed.

  Lemma whd_arg_sound mdecl Γ a :
    arg_whd Σ (arities_context (ind_bodies mdecl) ,,, Γ) a (whd_arg mdecl Γ a).
  Proof.
    rewrite /whd_arg /arg_whd.
    destruct (closedn #|Γ| a); [now left|].
    destruct whd_fuel as [[h l]|] eqn:hw; [|now left].
    right. exists h, l. split; [exact (whd_fuel_sound _ _ _ _ _ _ hw)|reflexivity].
  Qed.

  Lemma whd_var_args_sound mdecl NI Γ x l :
    All2 (arg_whd Σ (arities_context (ind_bodies mdecl) ,,, Γ)) l (whd_var_args mdecl NI Γ x l).
  Proof.
    rewrite /whd_var_args. generalize (kept_args NI Γ x) as n.
    induction l as [|a l IH]; intros [|n]; cbn; try constructor.
    - apply whd_arg_sound.
    - exact (IH 0).
    - by left.
    - apply IH.
  Qed.

  Lemma check_positive_whd_sound rec app mdecl NI Γ t :
    (forall t, rec t = Checked tt -> positive_cstr_arg Σ mdecl NI Γ t) ->
    (forall t, app t = Checked tt -> positive_cstr_arg Σ mdecl NI Γ t) ->
    check_positive_whd rec app mdecl NI Γ t = Checked tt ->
    positive_cstr_arg Σ mdecl NI Γ t.
  Proof.
    intros hrec happ. rewrite /check_positive_whd.
    destruct (decompose_app t) as [hd args] eqn:da.
    pose proof (decompose_app_inv da) as eqt.
    destruct hd as [n| | | | | | | | | | | | | | |]; cbv beta iota zeta;
      (* any head but a variable or an inductive: the reduct is checked *)
      try solve [
        destruct whd_fuel as [[rh rl]|] eqn:hw; [|discriminate];
        destruct (closedn #|Γ| (mkApps rh rl) || positivity_head rh); [|discriminate];
        intros hr; eapply pos_arg_red; [exact (whd_fuel_sound _ _ _ _ _ _ hw)|now apply hrec]].
    - (* a variable head: its arguments, reduced *)
      destruct (eqb (whd_var_args mdecl NI Γ n args) args); [apply happ|].
      intros hr. rewrite eqt.
      eapply pos_arg_rel_red; [exact (whd_var_args_sound mdecl NI Γ n args)|now apply hrec].
    - (* an inductive head *)
      apply happ.
  Qed.

  Lemma check_positive_app_sound args_check ctors_check mdecl NI Γ t :
    (forall NI Γ l, args_check NI Γ l = Checked tt -> positive_args Σ mdecl NI Γ l) ->
    (forall NI Γ ps nskip cs, ctors_check NI Γ ps nskip cs = Checked tt ->
       positive_nested_ctors Σ mdecl NI Γ ps nskip cs) ->
    check_positive_app args_check ctors_check mdecl NI Γ t = Checked tt ->
    positive_cstr_arg Σ mdecl NI Γ t.
  Proof.
    intros hargs hctors.
    rewrite /check_positive_app.
    destruct (decompose_app t) as [hd args] eqn:da.
    pose proof (decompose_app_inv da) as eqt. rewrite {}eqt.
    destruct hd; try discriminate.
    - (* a member of the block, or an enclosing nesting variable *)
      destruct ((#|Γ| <=? n) && (n <? #|Γ| + #|ind_bodies mdecl|)) eqn:isind.
      + destruct nth_error as [i|] eqn:hnth; [|discriminate].
        destruct (forallb (closedn #|Γ|) args) eqn:cla; [|discriminate].
        destruct (Nat.eqb (ind_realargs mdecl i) #|args|) eqn:hra; [|discriminate].
        intros _. move/andP: isind => [] /Nat.leb_le le /Nat.ltb_lt lt.
        econstructor 2.
        * symmetry. now apply Nat.eqb_eq.
        * now eapply forallb_All.
        * repeat split => //.
      + destruct (nested_inst_okb NI Γ n args) eqn:hni; [|discriminate].
        intros _. econstructor 3. now apply nested_inst_okb_spec.
    - (* a nested inductive *)
      intros h. apply bind_checked_tt in h as [mi [hl h]].
      destruct (Nat.eqb #|ind_bodies (fst mi)| 1) eqn:hone; [|discriminate]; cbn in h.
      destruct (check_nested_variance mdecl) eqn:hv; [|discriminate]; cbn in h.
      destruct (check_nested_uniform (fst mi) (snd mi) (nested_split #|Γ| args)) eqn:hu;
        [|discriminate]; cbn in h.
      destruct (Nat.leb (nested_split #|Γ| args) #|args| &&
                forallb (closedn #|Γ|) (skipn (nested_split #|Γ| args) args)) eqn:hk;
        [|discriminate]; cbn in h.
      apply bind_checked_tt in h as [[] [ha hc]].
      move/andP: hk => [] /Nat.leb_le hkle hcl.
      pose proof (lookup_ind_spec _ _ hl) as decl.
      have hb : ind_bodies (fst mi) = [snd mi].
      { apply Nat.eqb_eq in hone. exact (single_body_eq hone (proj2 decl)). }
      eapply (pos_arg_nested Σ mdecl NI Γ ind ui args (fst mi) (snd mi)
                (nested_split #|Γ| args) nested_binder).
      + exact decl.
      + now apply check_nested_uniform_spec.
      + now apply check_nested_variance_spec.
      + exact hkle.
      + now eapply forallb_All.
      + now apply hargs.
      + now apply hctors.
  Qed.

  Lemma check_nested_concl_sound mdecl NI Γ t :
    check_nested_concl NI Γ t = Checked tt ->
    positive_nested_cstr Σ mdecl NI Γ [] 0 t.
  Proof.
    rewrite /check_nested_concl.
    destruct (decompose_app t) as [hd l] eqn:da.
    pose proof (decompose_app_inv da) as eqt. rewrite {}eqt.
    destruct hd; try discriminate.
    destruct (nested_inst_okb NI Γ n l) eqn:hni; [|discriminate].
    intros _. constructor 5. now apply nested_inst_okb_spec.
  Qed.

  Lemma check_positive_sound fuel :
    (forall mdecl NI Γ t, check_positive_cstr_arg fuel mdecl NI Γ t = Checked tt ->
       positive_cstr_arg Σ mdecl NI Γ t) ×
    (forall mdecl NI Γ l, check_positive_args fuel mdecl NI Γ l = Checked tt ->
       positive_args Σ mdecl NI Γ l) ×
    (forall mdecl NI Γ ps nskip cs,
       check_positive_nested_ctors fuel mdecl NI Γ ps nskip cs = Checked tt ->
       positive_nested_ctors Σ mdecl NI Γ ps nskip cs) ×
    (forall mdecl NI Γ ps nskip t,
       check_positive_nested_cstr fuel mdecl NI Γ ps nskip t = Checked tt ->
       positive_nested_cstr Σ mdecl NI Γ ps nskip t).
  Proof.
    induction fuel as [|fuel IH]; [repeat split; intros; discriminate|].
    destruct IH as (IHarg & IHargs & IHctors & IHcstr).
    repeat split.
    - intros mdecl NI Γ t h. cbn [check_positive_cstr_arg] in h.
      destruct (closedn #|Γ| t) eqn:cl; [now constructor 1|].
      destruct t; cbv beta iota in h; try solve [refine (check_positive_whd_sound _ _ mdecl NI Γ _ _ _ h);
        [intros ? hr; now apply IHarg
        |intros ? ha; eapply check_positive_app_sound;
           [exact (IHargs mdecl)|exact (IHctors mdecl)|exact ha]]].
      + (* tProd *)
        destruct (closedn #|Γ| t1) eqn:clty.
        * constructor 6; [exact clty|]. now apply IHarg.
        * (* a domain whose weak-head normal form is closed *)
          destruct (whd_fuel positivity_fuel (positivity_context mdecl Γ) t1 []) as [[h' l]|] eqn:hw;
            [|discriminate].
          destruct (closedn #|Γ| (mkApps h' l)) eqn:clr; [|discriminate].
          eapply pos_arg_ass_red; [exact (whd_fuel_sound _ _ _ _ _ _ hw)|exact clr|].
          now apply IHarg.
      + (* tLetIn *)
        constructor 5. now apply IHarg.
    - intros mdecl NI Γ l h. cbn [check_positive_args] in h.
      destruct l as [|t l]; [constructor|].
      apply bind_checked_tt in h as [[] [h1 h2]].
      constructor; [now apply IHarg|now apply IHargs].
    - intros mdecl NI Γ ps nskip cs h. cbn [check_positive_nested_ctors] in h.
      destruct cs as [|c cs]; [constructor|].
      apply bind_checked_tt in h as [[] [h1 h2]].
      constructor; [now apply IHcstr|now apply IHctors].
    - intros mdecl NI Γ ps nskip t h. cbn [check_positive_nested_cstr] in h.
      destruct ps as [|p0 ps0], nskip as [|n0]; destruct t; try discriminate h;
        try solve [now apply check_nested_concl_sound];
        (* tLetIn *)
        try solve [constructor 2; now apply IHcstr];
        (* tProd, an instantiating argument *)
        try solve [constructor 1; now apply IHcstr];
        (* tProd, a parameter pushed without a check *)
        try solve [constructor 3; now apply IHcstr].
      (* tProd, no argument and no parameter left: a constructor argument *)
      apply bind_checked_tt in h as [[] [h1 h2]].
      constructor 4; [now apply IHarg|now apply IHcstr].
  Qed.

  Lemma check_positive_cstr_sound fuel mdecl n Γ t :
    check_positive_cstr fuel mdecl n Γ t = Checked tt ->
    positive_cstr Σ mdecl n Γ t.
  Proof.
    induction fuel as [|fuel IH] in Γ, t |- *; [discriminate|].
    cbn [check_positive_cstr].
    destruct t; try solve [
      destruct (decompose_app _) as [hd indices] eqn:da;
      pose proof (decompose_app_inv da) as eqt;
      destruct (eqb hd _) eqn:hhd; [|discriminate];
      destruct (forallb (closedn #|Γ|) indices) eqn:cli; [|discriminate];
      intros _; rewrite eqt; apply eqb_eq in hhd; subst hd;
      constructor 1; now eapply forallb_All].
    - (* tProd *)
      intros h. apply bind_checked_tt in h as [[] [h1 h2]].
      constructor 3.
      + now eapply (fst (check_positive_sound positivity_fuel)).
      + now apply IH.
    - (* tLetIn *)
      intros h. constructor 2. now apply IH.
  Qed.
End Check.

(** ** Unit tests for what the test suite cannot reach through [MetaRocq SafeCheck] *)

(** Running out of fuel is a rejection with its own message: three nested products with two
    units of fuel. *)
Lemma check_positive_out_of_fuel lookup lookup_op mdecl :
  check_positive_cstr_arg lookup lookup_op 2 mdecl [] []
    (tProd nested_binder (tSort Sort.type0) (tProd nested_binder (tSort Sort.type0)
      (tProd nested_binder (tSort Sort.type0) (tRel 3))))
  = TypeError (Msg "Nested positivity: out of fuel").
Proof. reflexivity. Qed.

(** Weak-head reduction out of fuel answers [None]: a beta-redex needs three units, one
    for the application, one for the contraction and one for the result, so two units
    are not enough. *)
Lemma whd_fuel_out_of_fuel lookup lookup_op na A t a :
  whd_fuel lookup lookup_op 2 [] (tApp (tLambda na A t) a) [] = None.
Proof. reflexivity. Qed.

(** A nested occurrence in a block with a covariant universe level is refused for that
    reason: the arguments of an inductive application are compared by conversion, which a
    covariant level does not give (see [positive_cstr_arg_subst]). *)
Lemma check_positive_covariant_refused lookup args_check ctors_check mdecl NI Γ t ind u args mi :
  decompose_app t = (tInd ind u, args) ->
  lookup_ind lookup ind = Checked mi ->
  #|ind_bodies (fst mi)| = 1 ->
  ind_variance mdecl = Some [Variance.Covariant] ->
  check_positive_app lookup args_check ctors_check mdecl NI Γ t
  = TypeError (Msg "Nested positivity: the block has a covariant universe level").
Proof.
  intros hd hl hone hv.
  rewrite /check_positive_app hd hl /= hone /= /check_nested_variance hv //.
Qed.
