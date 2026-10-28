(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane: βη confluence up to [upto_domain] (C4/I4).

   SHARED DEFINITIONS FILE — one owner (EtaL2), every C4 prover Requires it.
   No proofs here; proofs go in consumer files. A proof of a neighbouring
   statement proves nothing (C3's lesson applied from commit one).

   The statement and the Hindley–Rosen decomposition are fixed before fan-out.
   Consumers stage what they need as [Context] hypotheses with the exact
   signatures below and keep moving; proofs land as siblings. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction PCUICOnFreeVars
     PCUICTyping PCUICEtaDefs.
From Equations.Type Require Import Relation Relation_Properties.

Import PCUICOnFreeVars (is_open_term, is_closed_context).

(** ** Definitions (upstream [origin/eta_postpo:PCUICEtaReduction.v:574-575]). *)

Definition beta_eta1 (Σ : global_env) (Γ : context) : term -> term -> Type :=
  union (red1 Σ Γ) eta1.

Definition beta_eta (Σ : global_env) (Γ : context) : term -> term -> Type :=
  clos_refl_trans (beta_eta1 Σ Γ).

(** ######################################################################
    RETIRED (2026-10-28). [C4_statement] below is FALSE and is no longer a
    target of any lane.
    WHY: [C4_false : C4_statement -> False] (PCUICEtaC1b.v; fork
    wip/c4-C4C1b-2026-10-28 @ 99136ff0, cherry-picked onto
    wip/eta-l2-c4-canon-2026-10-28 as ce081fa7). Its witness [c4_s] reaches two
    βη-normal forms that are not [upto_domain]-related, because a β step leaves a
    variable in a λ domain and that blocks η. Widening the comparison does not
    help: [betaeta_confluence_mod_E2_false] (same file, the gate's [t0]).
    [C1b_statement] (below) is false too ([C1b_false]).
    REPLACED BY: exact βη-confluence on canonical-domain terms,
    [canon_beta_eta_confluence] (PCUICEtaCanonC4.v, c13e90d3), used through the
    restated I5 [I5_statement] (PCUICEtaI5.v), proved as [I5_FollowKernel]
    (PCUICEtaI5EtaL.v, f1f86e47); lanes/eta/plan.md §6.2. It is kept UNCHANGED
    only as the statement that the mechanised refutations refute.
    ###################################################################### *)

(** ** C4 / I4 — the public statement.

   PREMISES: [wf Σ], [is_closed_context Γ], [is_open_term Γ t]. All three are
   genuine (C3 forced them; they thread through the induction because [beta_eta]
   preserves scoping — P-SCOPE, proved separately). *)

Definition C4_statement : Type :=
  forall (cf : checker_flags) (Σ : global_env) (wfΣ : wf Σ)
         (Γ : context) (t u v : term),
    is_closed_context Γ -> is_open_term Γ t ->
    beta_eta Σ Γ t u -> beta_eta Σ Γ t v ->
    ∑ u' v', beta_eta Σ Γ u u' × beta_eta Σ Γ v v' × upto_domain u' v'.

(** ** Hindley–Rosen decomposition.

   C4 factors through TWO carrier-generic theorems — no MetaRocq, no AST,
   independently checkable. This is where the rewriting-theory risk lives
   (plan §6 rank 4: "HR modulo an equivalence needs the equivalence to commute
   with both relations").

   HYPOTHESIS SHAPES ARE ASYMMETRIC AND MUST MATCH THE LEMMAS WE HAVE:
   - C1a/C1b give [clos_refl] (one-step forms are FALSE, B3(b)).
   - C3 gives [clos_refl R] on one leg and [clos_refl_trans S] on the other.
   Getting these wrong yields a correct abstract proof that cannot be
   instantiated — which is the specific failure to design out.

   (A) STRONG COMMUTATION ⇒ COMMUTATION, MODULO E.
       From the one-step commutation
         R t v → S t u → ∑ w w', clos_refl R u w × clos_refl_trans S v w'
                                    × E w w'
       conclude the closure form (clos_refl_trans R vs clos_refl_trans S,
       joined modulo E). This is the hard half: every step of the induction
       must transport E across, which is where C1a/C1b are consumed.

   (B) HINDLEY–ROSEN MODULO E.
       R confluent + S confluent-modulo-E + (A)'s commutation
       ⇒ union R S confluent modulo E.

   INSTANTIATION:
     R := red1 Σ Γ    (β)        — confluent by [red_confluence] (base, PROVED)
     S := eta1         (η)        — confluent modulo [upto_domain] by U8
     E := upto_domain              — equivalence (refl/sym/trans landed)
     strong commutation := C3      — in flight

   DEPENDENCIES (each a separate prover slot):
     C3                 — strong commutation (in flight; the 11-01 go/no-go)
     C1a                — E vs R (ABSENT; reflexive-closure form, [upto_domain_ctx])
     C1b                — E vs S (ABSENT; reflexive-closure form)
     U6                 — [eta1_size] (η is SN — validates Newman for U8)
     U7                 — [eta1_local_confluence] up to [upto_domain] (PROVED upstream)
     U8                 — η confluence modulo E (Newman from U6 + U7 + C1b)
     P-SCOPE            — [beta_eta] preserves [is_closed_context]/[is_open_term]
                          (the row nobody had listed; all three C3 hardenings came
                          from scoping, so expecting C4 to harden there too is an
                          inference from evidence)
     (A)                — abstract, two independent provers (MetaRocq-free)
     (B)                — abstract, one prover (MetaRocq-free)
     P-INST             — instantiation + premise threading (EtaL2)

   NEWMAN TRAP (recorded before anyone reads upstream :2200):
     upstream has [beta_eta_local_confluence] PROVED at :2200 next to
     [beta_eta_confluence] Admitted at :2217. Lifting local→global by Newman is
     INVALID: βη is not SN (β is not). The local lemma is also built from C2
     ([red1_eta1_diamond]) whose both-sides form the plan already rejects.
     Contrast: Newman IS valid for U8, because η alone IS SN (U6, [eta1_size]).
     Valid for U8, invalid for C4. *)

(** ** Abstract theorem signatures — RELATIVIZED TO AN INVARIANT [Q].

   WHY [Q]: C3 holds only for well-scoped terms, so an abstract theorem stated
   for ALL elements cannot consume it — the specific failure "correct abstract
   theorem that cannot be instantiated". Every hypothesis is therefore required
   only on [Q]-elements, and [R]/[S] must preserve [Q]. Instantiation:
     [Q t := is_open_term Γ t]  ([is_closed_context Γ] is constant: Γ is fixed)
     [R]/[S] preserve [Q]       <- P-SCOPE ([PCUICEtaScope]: [beta_eta1_on_free_vars])
   Relativizing costs nothing: each relativized hypothesis is WEAKER than its
   global form, so a global lemma (e.g. base [red_confluence], or C1a/C1b as the
   plan states them, without scoping) instantiates it directly.

   [E] needs no [Q]-invariance: every [E]-related pair the proof feeds to a
   hypothesis consists of two reducts of a [Q]-element, hence both [Q].

   HYPOTHESIS SHAPES, matching the lemmas we will actually have:
   - E vs R, E vs S: [clos_refl] on the moved step (C1a/C1b; one-step forms are
     FALSE, B3(b)).
   - strong commutation: VERBATIM C3 ([red1_eta1_strong_commutation],
     [PCUICEtaC3B]): [R t v -> S t u -> ∑ w w', clos_refl R u w ×
     clos_refl_trans S v w' × E w w'] — [clos_refl R] on one leg against
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
    (* E commutes with R, on Q-elements (C1a shape) *)
    (forall t t' u, Q t -> Q t' -> E t t' -> R t u -> ∑ u', clos_refl R t' u' × E u u') ->
    (* E commutes with S, on Q-elements (C1b shape) *)
    (forall t t' u, Q t -> Q t' -> E t t' -> S t u -> ∑ u', clos_refl S t' u' × E u u') ->
    (* strong commutation, on Q-elements: VERBATIM the C3 shape *)
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
    (* S is confluent modulo E on Q (U8) *)
    (forall t u v, Q t -> clos_refl_trans S t u -> clos_refl_trans S t v ->
       ∑ u' v', clos_refl_trans S u u' × clos_refl_trans S v v' × E u' v') ->
    (* R* and S* commute modulo E on Q — exactly theorem (A)'s conclusion *)
    (forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans S t v ->
       ∑ u' v', clos_refl_trans S u u' × clos_refl_trans R v v' × E u' v') ->
    (* conclusion: union R S confluent modulo E on Q *)
    forall t u v, Q t -> clos_refl_trans (union R S) t u -> clos_refl_trans (union R S) t v ->
      ∑ u' v', clos_refl_trans (union R S) u u' × clos_refl_trans (union R S) v v' × E u' v'.

(** ** Pinned statements for the C1a, C1b and U8 provers.

   They live HERE, in the confluence-free shared file, not in the assembly
   ([PCUICEtaC4], which Requires [PCUICConfluence]): a statement must never be
   heavier than what it states. Each prover states its theorem AS the named
   statement. *)

(** C1a at a FIXED context: all C4 needs ([HR_A_instantiable] takes it at
    [Γ' := Γ]). The one-step form is FALSE (B3(b)); [clos_refl] is required. *)
Definition C1a_fixed_statement : Type :=
  forall (Σ : global_env) (Γ : context) (t t' u : term),
    upto_domain t t' -> red1 Σ Γ t u ->
    ∑ u', clos_refl (red1 Σ Γ) t' u' × upto_domain u u'.

Definition C1b_statement : Type :=
  forall (t t' u : term),
    upto_domain t t' -> eta1 t u ->
    ∑ u', clos_refl eta1 t' u' × upto_domain u u'.

(** U8: η confluence modulo [upto_domain]. Unscoped, as η is context-free and
    upstream's U7 ([eta1_local_confluence], origin/eta_postpo
    PCUICEtaReduction.v:152) is unscoped. NOTE: upstream U7 is EXACT local
    confluence ([∑ v, eta u1 v × eta u2 v], no [upto_domain]), so U8 may be
    proved exactly by Newman from U6 + U7 and then weakened by [upto_domain_refl]
    — C1b is not needed for U8. Newman IS valid here: η alone is SN (U6).
    U7 is NOT in our tree: it exists only upstream, on the 2020 AST, and must
    be PORTED (the plan's "PROVED" referred to upstream). *)
Definition U8_statement : Type :=
  forall (t u v : term),
    clos_refl_trans eta1 t u -> clos_refl_trans eta1 t v ->
    ∑ u' v', clos_refl_trans eta1 u u' × clos_refl_trans eta1 v v' × upto_domain u' v'.

