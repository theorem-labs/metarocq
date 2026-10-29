(* Distributed under the terms of the MIT license. *)
(** * Well-typed substitutions over [typingE]

  [well_substE] is the copy of [well_subst] ([PCUICInstDef]) with [typing] replaced by
  [typingE]: every image [σ x] is typed in [typingE] at the instantiated type of the
  [x]-th declaration, and the substitution preserves the let-bound variables
  ([usubst], unchanged: it is syntactic). *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICSigmaCalculus
     PCUICInstDef PCUICTypingEta.

Implicit Types cf : checker_flags.
Local Open Scope sigma_scope.

Definition well_substE {cf} Σ (Γ : context) σ (Δ : context) :=
  (forall x decl,
    nth_error Γ x = Some decl ->
    Σ ;;; Δ |-E σ x : ((lift0 (S x)) (decl_type decl)).[ σ ]) ×
  usubst Γ σ Δ.
