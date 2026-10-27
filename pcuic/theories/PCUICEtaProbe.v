From Stdlib Require Import CRelationClasses.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICReduction PCUICEtaDefs.
From Equations.Type Require Import Relation Relation_Properties.
Set Default Goal Selector "!".

Lemma probe_cr (R : term -> term -> Type) x y : R x y -> clos_refl R x y.
Proof. intros r. constructor. exact r. Abort.

Lemma probe_cr_refl (R : term -> term -> Type) x : clos_refl R x x.
Proof. constructor 2. Abort.

Lemma probe_eta x : eta x x.
Proof. apply rt_refl. Abort.

Lemma probe_eta_step x y : eta1 x y -> eta x y.
Proof. intros. apply rt_step. assumption. Abort.
