(* Distributed under the terms of the MIT license. *)
(** * Concrete instances of the premises of [trans_on_prim_decl]

    [trans_on_prim_decl] ([PCUICExpandLetsCorrectness]) states that the
    expand-lets translation preserves the [on_prim_decl] condition of a
    declaration.  Its premises are: [wf Σ0], the well-formedness of
    [trans_global_env Σ0] at [cf' cf], and the [on_global_decl] and
    [on_prim_decl] conditions of the declaration at [(Σ0, ud)].

    Each premise is proved here for the declaration [land] of
    [PCUICPrimInstances.Σ_po], at the prefix it is checked against
    ([Σ0 := Σ_po_int], [ud := Monomorphic_ctx]), and the lemma is then applied
    to them.  No proof uses [trans_wf]. *)

From MetaRocq.Utils Require Import utils.
From Stdlib Require Import ssreflect.
From MetaRocq.Common Require Import config Primitive PrimitiveOps.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICCumulativitySpec
  PCUICPrimInstances PCUICExpandLets PCUICExpandLetsCorrectness.

Import ListNotations.

Section CfGeneric.
Context {cf : checker_flags}.

(** The declarations of a well-formed environment with a first declaration:
    the tail's declarations and the data of the first one. *)
Lemma po_on_global_decls_cons_inv {univs retro Σ kn d} :
  on_global_decls cumulSpec0 (lift_typing typing) univs retro ((kn, d) :: Σ) ->
  on_global_decls cumulSpec0 (lift_typing typing) univs retro Σ ×
  on_global_decls_data cumulSpec0 (lift_typing typing) univs retro Σ kn d.
Proof. intros h. inversion h; subst. split; assumption. Qed.

(** Premise [wfΣ0 : wf Σ0] of [trans_on_prim_decl], at [Σ0 := Σ_po_int], for
    any checker flags. *)
Lemma Σ_po_int_wf : wf Σ_po_int.
Proof.
  destruct Σ_po_wf_ext as [[hu [hr hd]] _].
  split; [exact hu|]. split; [exact hr|].
  exact (po_on_global_decls_cons_inv hd).1.
Qed.

End CfGeneric.

Local Existing Instance default_checker_flags.

(** The translation leaves [Σ_po_int] unchanged: it has no let-in. *)
Lemma trans_global_env_Σ_po_int : trans_global_env Σ_po_int = Σ_po_int.
Proof. reflexivity. Qed.

(** Premise [wfT : @wf (cf' cf) (trans_global_env Σ0)] of
    [trans_on_prim_decl], at [Σ0 := Σ_po_int]. *)
Lemma trans_Σ_po_int_wf : @wf (cf' default_checker_flags) (trans_global_env Σ_po_int).
Proof. rewrite trans_global_env_Σ_po_int. exact (@Σ_po_int_wf (cf' default_checker_flags)). Qed.

(** Premise [on_global_decl cumulSpec0 (lift_typing typing) (Σ0, ud) kn d] of
    [trans_on_prim_decl], for [land] at [Σ0 := Σ_po_int],
    [ud := Monomorphic_ctx]. *)
Lemma Σ_po_land_on_global_decl :
  on_global_decl cumulSpec0 (lift_typing typing) (Σ_po_int, Monomorphic_ctx)
    po_land_kn (ConstantDecl po_land_body).
Proof.
  destruct Σ_po_wf_ext as [[_ [_ hd]] _].
  destruct (po_on_global_decls_cons_inv hd).2. assumption.
Qed.

(** [trans_on_prim_decl] applied to its premises for [land]: the translated
    declaration satisfies [on_prim_decl] in the translated prefix.  The
    premise [on_prim_decl cumulSpec0 (Σ0, ud) kn d] is
    [PCUICPrimInstances.Σ_po_land_on_prim_decl]. *)
Lemma trans_Σ_po_land_on_prim_decl :
  on_prim_decl (@cumulSpec0 (cf' default_checker_flags))
    (trans_global_env Σ_po_int, Monomorphic_ctx) po_land_kn
    (trans_global_decl (ConstantDecl po_land_body)).
Proof.
  exact (trans_on_prim_decl Σ_po_int_wf trans_Σ_po_int_wf Monomorphic_ctx po_land_kn
    (ConstantDecl po_land_body) Σ_po_land_on_global_decl Σ_po_land_on_prim_decl).
Qed.
