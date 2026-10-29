(* Distributed under the terms of the MIT license. *)
(** * βη reduction and the statements of the βη-confluence route

   The definitions [beta_eta1] and [beta_eta], and the statements the route is built
   from: [C4_statement] (βη-confluence up to [upto_domain], refuted), the two
   carrier-generic Hindley–Rosen statements (A) and (B), [C1b_statement] (refuted)
   and [U8_statement] (proved). No proofs here; each statement is proved or refuted
   in the file named next to it below. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction PCUICOnFreeVars
     PCUICTyping PCUICEtaDefs.
From Equations.Type Require Import Relation Relation_Properties.

Import PCUICOnFreeVars (is_open_term, is_closed_context).

(** ** Definitions (as upstream MetaRocq branch [eta_postpo] defines them in
    [pcuic/theories/PCUICEtaReduction.v]; that file is not in this tree). *)

Definition beta_eta1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
  union (red1 Σ Γ) eta1.

Definition beta_eta (Σ : global_env) (Γ : context) : term -> term -> Type :=
  clos_refl_trans (beta_eta1 Σ Γ).

(** [C4_statement] is FALSE: [C4_false : C4_statement -> False] ([PCUICEtaC1b]).
    Its witness [c4_s] reaches two βη-normal forms that are not
    [upto_domain]-related, because a β step leaves a variable in a λ domain and that
    blocks η. Widening the comparison does not help
    ([betaeta_confluence_mod_E2_false], same file). [C1b_statement] below is false
    too ([C1b_false]). The βη-confluence that holds is exact confluence on
    canonical-domain terms, [canon_beta_eta_confluence] ([PCUICEtaCanonC4]), used
    through [I5_statement] ([PCUICEtaI5]) and proved as [I5_FollowKernel]
    ([PCUICEtaI5EtaL]). [C4_statement] is kept as the statement the refutations
    refute. *)

(** ** C4 / I4: the statement as originally posed.

   PREMISES: [wf Σ], [is_closed_context Γ], [is_open_term Γ t]. [beta_eta] preserves
   the scoping premises ([beta_eta_is_open_term], [PCUICEtaScope]). *)

Definition C4_statement : Type :=
  forall (cf : checker_flags) (Σ : global_env) (wfΣ : wf Σ)
         (Γ : context) (t u v : term),
    is_closed_context Γ -> is_open_term Γ t ->
    beta_eta Σ Γ t u -> beta_eta Σ Γ t v ->
    ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × upto_domain u' v'.

(** ** Hindley–Rosen decomposition.

   βη-confluence factors through two carrier-generic theorems, with no MetaRocq and
   no AST.

   (A) STRONG COMMUTATION ⇒ COMMUTATION, MODULO E.
       From the one-step commutation
         R t v → S t u → ∑ w w', clos_refl R u w × clos_refl_trans S v w'
                                    × E w w'
       conclude the closure form (clos_refl_trans R against clos_refl_trans S,
       joined modulo E). Every step of the induction transports E across, which is
       where the hypotheses "E commutes with R" and "E commutes with S" are used.
       Proved: [HR_strong_commutation_modulo] ([PCUICEtaHRCommutationA1]).

   (B) HINDLEY–ROSEN MODULO E.
       R confluent + S confluent modulo E + (A)'s commutation
       ⇒ union R S confluent modulo E.
       Proved: [HR_modulo] ([PCUICEtaHRModulo]).

   The hypothesis shapes are asymmetric, as the lemmas that instantiate them are:
   the E-commutations give [clos_refl] (their one-step forms are false), and the
   strong commutation gives [clos_refl R] on one leg and [clos_refl_trans S] on the
   other.

   WHERE EACH PIECE IS:
     strong commutation (C3) — [red1_eta1_strong_commutation] ([PCUICEtaC3BR]),
                               up to [upto_domain_r]
     E vs R (C1a)            — [red1_upto_domain_r_bodies], [red1_upto_domain_r_fixed]
                               ([PCUICEtaC1aR]), for [upto_domain_r]
     E vs S (C1b)            — REFUTED for [upto_domain]: [C1b_false] ([PCUICEtaC1b])
     η is SN (U6)            — [eta1_size] ([PCUICEtaU8])
     η local confluence (U7) — [eta1_local_confluence] ([PCUICEtaU8]), exact
     η confluence (U8)       — [eta1_confluence] (exact) and [eta1_confluence_upto]
                               ([PCUICEtaU8]), by Newman from U6 and U7
     scoping (P-SCOPE)       — [beta_eta1_on_free_vars], [beta_eta_is_open_term]
                               ([PCUICEtaScope])
     (A), (B)                — as above
     instantiation           — [canon_beta_eta_confluence] ([PCUICEtaCanonC4]): (A)
                               and (B) at [E := eq], on canonical-domain terms

   NEWMAN TRAP: upstream MetaRocq branch [eta_postpo], in
   [pcuic/theories/PCUICEtaReduction.v], proves a local βη-confluence lemma
   ([beta_eta_local_confluence]) and leaves [beta_eta_confluence] Admitted; neither
   is in this tree. Lifting local to global confluence by Newman is invalid there,
   because βη is not SN (β is not). Newman is valid for U8, because η alone is SN
   ([eta1_size]). *)

(** ** Abstract theorem signatures, relativized to an invariant [Q].

   C3 holds only for well-scoped terms, so an abstract theorem stated for all
   elements could not consume it. Every hypothesis is therefore required only on
   [Q]-elements, and [R]/[S] must preserve [Q]. Instantiation:
     [Q t := is_open_term Γ t]  ([is_closed_context Γ] is constant: Γ is fixed)
     [R]/[S] preserve [Q]       by [beta_eta1_on_free_vars] ([PCUICEtaScope])
   Each relativized hypothesis is weaker than its global form, so a global lemma
   instantiates it directly.

   [E] needs no [Q]-invariance: every [E]-related pair the proof feeds to a
   hypothesis consists of two reducts of a [Q]-element, hence both [Q].

   HYPOTHESIS SHAPES:
   - E vs R, E vs S: [clos_refl] on the moved step (the one-step forms are false).
   - strong commutation: the C3 shape, [R t v -> S t u -> ∑ w w', clos_refl R u w ×
     clos_refl_trans S v w' × E w w'], with [clos_refl R] on one leg against
     [clos_refl_trans S] on the other.
   - In the conclusions, the R-reduct is completed by S and the S-reduct by R,
     as in C3. *)

Definition HR_strong_commutation_modulo_statement : Type :=
  forall (A : Type) (R S E : A -> A -> Type) (Q : A -> Type),
    (* Q is invariant under R and S *)
    (forall t u, Q t -> R t u -> Q u) ->
    (forall t u, Q t -> S t u -> Q u) ->
    (* E is an equivalence *)
    CRelationClasses.Reflexive E ->
    CRelationClasses.Symmetric E ->
    CRelationClasses.Transitive E ->
    (* E commutes with R, on Q-elements *)
    (forall t t' u, Q t -> Q t' -> E t t' -> R t u -> ∑ u', clos_refl R t' u' × E u u') ->
    (* E commutes with S, on Q-elements *)
    (forall t t' u, Q t -> Q t' -> E t t' -> S t u -> ∑ u', clos_refl S t' u' × E u u') ->
    (* strong commutation, on Q-elements: the C3 shape *)
    (forall t u v, Q t -> R t v -> S t u ->
       ∑ w w', clos_refl R u w × clos_refl_trans S v w' × E w w') ->
    (* conclusion: R* against S*, joined modulo E *)
    forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans S t v ->
      ∑ u' v', clos_refl_trans S u u' × clos_refl_trans R v v' × E u' v'.

Definition HR_modulo_statement : Type :=
  forall (A : Type) (R S E : A -> A -> Type) (Q : A -> Type),
    (forall t u, Q t -> R t u -> Q u) ->
    (forall t u, Q t -> S t u -> Q u) ->
    CRelationClasses.Reflexive E ->
    CRelationClasses.Symmetric E ->
    CRelationClasses.Transitive E ->
    (* E commutes with R and with S (needed to glue tiles) *)
    (forall t t' u, Q t -> Q t' -> E t t' -> R t u -> ∑ u', clos_refl R t' u' × E u u') ->
    (forall t t' u, Q t -> Q t' -> E t t' -> S t u -> ∑ u', clos_refl S t' u' × E u u') ->
    (* R is confluent on Q (base [red_confluence]) *)
    (forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans R t v ->
       ∑ w, clos_refl_trans R u w × clos_refl_trans R v w) ->
    (* S is confluent modulo E on Q *)
    (forall t u v, Q t -> clos_refl_trans S t u -> clos_refl_trans S t v ->
       ∑ u' v', clos_refl_trans S u u' × clos_refl_trans S v v' × E u' v') ->
    (* R* and S* commute modulo E on Q — exactly theorem (A)'s conclusion *)
    (forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans S t v ->
       ∑ u' v', clos_refl_trans S u u' × clos_refl_trans R v v' × E u' v') ->
    (* conclusion: union R S confluent modulo E on Q *)
    forall t u v, Q t -> clos_refl_trans (union R S) t u -> clos_refl_trans (union R S) t v ->
      ∑ u' v', clos_refl_trans (union R S) u u' × clos_refl_trans (union R S) v v' × E u' v'.

(** ** The statements [C1b_statement] and [U8_statement].

   They live here, in a confluence-free file, so that a statement is never heavier
   than what it states. [C1b_statement] is refuted ([C1b_false], [PCUICEtaC1b]);
   [U8_statement] is proved ([eta1_confluence_upto], [PCUICEtaU8]). *)

Definition C1b_statement : Type :=
  forall (t t' u : term),
    upto_domain t t' -> eta1 t u ->
    ∑ u', clos_refl eta1 t' u' × upto_domain u u'.

(** U8: η confluence modulo [upto_domain]. Unscoped, as η is context-free.
    [eta1_confluence_upto] proves it from exact η confluence ([eta1_confluence],
    by Newman from [eta1_size] and the exact local confluence
    [eta1_local_confluence]) and [upto_domain_refl]; it does not use C1b. *)
Definition U8_statement : Type :=
  forall (t u v : term),
    clos_refl_trans eta1 t u -> clos_refl_trans eta1 t v ->
    ∑ u' v', clos_refl_trans eta1 u u' × clos_refl_trans eta1 v v' × upto_domain u' v'.

