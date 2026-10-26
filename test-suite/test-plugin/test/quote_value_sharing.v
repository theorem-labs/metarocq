From MetaRocq.TestPlugin Require Import Loader.
From MetaRocq.Template Require Import All.
From Stdlib Require Import List PeanoNat Ring_polynom Ring_theory.
From Corelib Require Import CRelationClasses.

(* The quoter quotes each natural, string, module path, kernel name and
   inductive once and reuses the value. Each command below quotes its term
   twice through the production SafeCheck path: once with those values rebuilt
   at every occurrence, as the quoter did before they were shared, and once
   shared. It fails unless the two quoted programs are structurally equal, and
   unless repeated values really are one OCaml value. *)

MetaRocq Test Quote Sharing nat.
MetaRocq Test Quote Sharing (3 + 1).
MetaRocq Test Quote Sharing Ast.term.
MetaRocq Test Quote Sharing @List.map.
MetaRocq Test Quote Sharing @List.rev_append.
MetaRocq Test Quote Sharing @PeanoNat.Nat.add_comm.
MetaRocq Test Quote Sharing @PeanoNat.Nat.le_add_r.
MetaRocq Test Quote Sharing (forall (A : Type) (P : A -> Prop), { a : A | P a }).

(* Template-polymorphic inductives: a record field, an applied template
   inductive, a template product, and a polymorphic use at an algebraic
   instance. *)
Record template_list_record := { template_list_field : list nat }.
MetaRocq Test Quote Sharing template_list_record.
MetaRocq Test Quote Sharing (list nat).
MetaRocq Test Quote Sharing (prod nat nat).
MetaRocq Test Quote Sharing @Stdlib.setoid_ring.Ring_theory.div_theory.

Definition template_iffT_nat := iffT nat nat.
MetaRocq Test Quote Sharing template_iffT_nat.

Definition template_sigT_nat := {n : nat & nat}.
MetaRocq Test Quote Sharing template_sigT_nat.

(* Proof terms large enough to repeat names and indices many times. *)
MetaRocq Test Quote Sharing @Stdlib.setoid_ring.Ring_polynom.CFactor.
MetaRocq Test Quote Sharing @Stdlib.setoid_ring.Ring_polynom.Mcphi_ok.
MetaRocq Test Quote Sharing @Stdlib.setoid_ring.Ring_polynom.Mphi_ok.
