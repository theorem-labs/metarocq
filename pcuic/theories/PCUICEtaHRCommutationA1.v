(* Distributed under the terms of the MIT license. *)
(** * Theorem (A): strong commutation implies commutation, modulo an equivalence

   [HR_strong_commutation_modulo] proves [HR_strong_commutation_modulo_statement]
   ([PCUICEtaBetaEta], Required here for the statement alone).

   Carrier-generic: the proof uses only the relation library of [Equations.Type]
   and the statement's own hypotheses, no PCUIC definition, no reduction and no
   confluence result. There are no section variables and nothing is assumed:
   every lemma below is closed, its hypotheses are explicit arguments, and every
   proof ends in [Qed]. The lemmas take the three equivalence laws of [E]
   unfolded ([forall x, E x x], ...); the [CRelationClasses] classes of the
   statement are convertible to these forms.

   Route. Three diagram-pasting inductions, each on the direct form of
   [clos_refl_trans] ([rt_step] / [rt_refl] / [rt_trans]), so a composite
   derivation is handled by pasting the two induction-hypothesis tiles side by
   side:
   1. [crt_E_transport]: for any relation [T] that preserves [Q] and whose
      [clos_refl] commutes with [E] on [Q]-elements, [E] transports a [T*]
      derivation: [E t t' -> T* t u -> ∑ u', T* t' u' × E u u']. Used twice, at
      [T := S] and at [T := R].
   2. [refl_R_vs_crt_S]: [R^=] against [S*] (induction on [S*]); a composite
      pastes two tiles and transports the lower [S*] leg across [E] by (1) at [S].
   3. [crt_R_vs_crt_S]: [R*] against [S*] (induction on [R*]); a single step is
      (2) at [r_step]; a composite pastes two tiles and transports the right [R*]
      leg across [E] by (1) at [R].

   The [Q] invariant. The [E]-commutation hypotheses demand [Q] at both ends of
   the [E] pair. Every induction carries [Q] of its source elements as an explicit
   premise of the induction hypothesis, and every term the proof meets is an
   [R]/[S]-reduct (through [clos_refl] / [clos_refl_trans]) of a [Q]-element, so
   its [Q] follows from [cr_Q] / [crt_Q]. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.PCUIC Require Import PCUICEtaBetaEta.
From Equations.Type Require Import Relation.

(** ** [Q] is preserved along [clos_refl] and [clos_refl_trans]. *)

Lemma cr_Q {A : Type} (T : A -> A -> Type) (Q : A -> Type) :
  (forall t u, Q t -> T t u -> Q u) ->
  forall t u, Q t -> clos_refl T t u -> Q u.
Proof.
  intros HT t u Ht h. destruct h as [y h|].
  - exact (HT _ _ Ht h).
  - exact Ht.
Qed.

Lemma crt_Q {A : Type} (T : A -> A -> Type) (Q : A -> Type) :
  (forall t u, Q t -> T t u -> Q u) ->
  forall t u, Q t -> clos_refl_trans T t u -> Q u.
Proof.
  intros HT t u Ht h. revert Ht.
  induction h as [x y h|x|x y z h1 IH1 h2 IH2]; intros Hx.
  - exact (HT _ _ Hx h).
  - exact Hx.
  - exact (IH2 (IH1 Hx)).
Qed.

Lemma cr_crt {A : Type} (T : A -> A -> Type) t u :
  clos_refl T t u -> clos_refl_trans T t u.
Proof.
  intros h. destruct h as [y h|].
  - exact (@rt_step _ _ _ _ h).
  - exact (@rt_refl _ _ _).
Qed.

(** ** (1) [E] transports a [T*] derivation, on [Q]-elements. *)

Lemma crt_E_transport {A : Type} (T E : A -> A -> Type) (Q : A -> Type) :
  (forall t u, Q t -> T t u -> Q u) ->
  (forall x y z, E x y -> E y z -> E x z) ->
  (forall t t' u, Q t -> Q t' -> E t t' -> T t u -> ∑ u', clos_refl T t' u' × E u u') ->
  forall t t' u, Q t -> Q t' -> E t t' -> clos_refl_trans T t u ->
    ∑ u', clos_refl_trans T t' u' × E u u'.
Proof.
  intros HQT HEtr HET t t' u Ht Ht' He h.
  revert He. revert Ht'. revert t'. revert Ht.
  induction h as [x y h|x|x y z h1 IH1 h2 IH2]; intros Hx t' Ht' He.
  - (* one step: the hypothesis itself *)
    destruct (HET _ _ _ Hx Ht' He h) as [y' [h' He']].
    exists y'. split; [exact (cr_crt _ _ _ h') | exact He'].
  - (* refl *)
    exists t'. split; [exact (@rt_refl _ _ _) | exact He].
  - (* x ->* y ->* z: transport the first leg, then the second from (y, y') *)
    destruct (IH1 Hx t' Ht' He) as [y' [hy' Hey]].
    pose proof (crt_Q T Q HQT _ _ Hx h1) as Hy.
    pose proof (crt_Q T Q HQT _ _ Ht' hy') as Hy'.
    destruct (IH2 Hy y' Hy' Hey) as [z' [hz' Hez]].
    exists z'. split; [exact (@rt_trans _ _ _ _ _ hy' hz') | exact Hez].
Qed.

(** ** (2) [R^=] against [S*], joined modulo [E]. *)

Lemma refl_R_vs_crt_S {A : Type} (R S E : A -> A -> Type) (Q : A -> Type) :
  (forall t u, Q t -> R t u -> Q u) ->
  (forall t u, Q t -> S t u -> Q u) ->
  (forall x, E x x) ->
  (forall x y z, E x y -> E y z -> E x z) ->
  (forall t t' u, Q t -> Q t' -> E t t' -> S t u -> ∑ u', clos_refl S t' u' × E u u') ->
  (forall t u v, Q t -> R t v -> S t u ->
     ∑ w w', clos_refl R u w × clos_refl_trans S v w' × E w w') ->
  forall t u v, Q t -> clos_refl R t v -> clos_refl_trans S t u ->
    ∑ w w', clos_refl R u w × clos_refl_trans S v w' × E w w'.
Proof.
  intros HQR HQS HErf HEtr HES Htile t u v Ht hR hS.
  revert hR. revert v. revert Ht.
  induction hS as [x y hS|x|x y z h1 IH1 h2 IH2]; intros Hx v hR.
  - (* one S step x -> y against R^= x v *)
    destruct hR as [v' hR'|].
    + exact (Htile _ _ _ Hx hR' hS).
    + exists y, y. split; [exact (@r_refl _ _ _)|split].
      * exact (@rt_step _ _ _ _ hS).
      * exact (HErf y).
  - (* S* is refl *)
    exists v, v. split; [exact hR|split].
    + exact (@rt_refl _ _ _).
    + exact (HErf v).
  - (* x ->S* y ->S* z, R^= x v *)
    (* upper tile: R^= y w1, S* v w1', E w1 w1' *)
    destruct (IH1 Hx v hR) as [w1 [w1' [hw1 [hw1' Hew1]]]].
    pose proof (crt_Q S Q HQS _ _ Hx h1) as Hy.
    (* lower tile from y: R^= z w2, S* w1 w2', E w2 w2' *)
    destruct (IH2 Hy w1 hw1) as [w2 [w2' [hw2 [hw2' Hew2]]]].
    (* transport S* w1 w2' across E w1 w1' *)
    pose proof (cr_Q R Q HQR _ _ Hy hw1) as Hw1.
    pose proof (cr_Q R Q HQR _ _ Hx hR) as Hv.
    pose proof (crt_Q S Q HQS _ _ Hv hw1') as Hw1'.
    destruct (crt_E_transport S E Q HQS HEtr HES _ _ _ Hw1 Hw1' Hew1 hw2')
      as [z' [hz' Hez']].
    exists w2, z'. split; [exact hw2|split].
    + exact (@rt_trans _ _ _ _ _ hw1' hz').
    + exact (HEtr _ _ _ Hew2 Hez').
Qed.

(** ** (3) [R*] against [S*], joined modulo [E]. *)

Lemma crt_R_vs_crt_S {A : Type} (R S E : A -> A -> Type) (Q : A -> Type) :
  (forall t u, Q t -> R t u -> Q u) ->
  (forall t u, Q t -> S t u -> Q u) ->
  (forall x, E x x) ->
  (forall x y, E x y -> E y x) ->
  (forall x y z, E x y -> E y z -> E x z) ->
  (forall t t' u, Q t -> Q t' -> E t t' -> R t u -> ∑ u', clos_refl R t' u' × E u u') ->
  (forall t t' u, Q t -> Q t' -> E t t' -> S t u -> ∑ u', clos_refl S t' u' × E u u') ->
  (forall t u v, Q t -> R t v -> S t u ->
     ∑ w w', clos_refl R u w × clos_refl_trans S v w' × E w w') ->
  forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans S t v ->
    ∑ u' v', clos_refl_trans S u u' × clos_refl_trans R v v' × E u' v'.
Proof.
  intros HQR HQS HErf HEsy HEtr HER HES Htile t u v Ht hR hS.
  revert hS. revert v. revert Ht.
  induction hR as [x y hR|x|x y z h1 IH1 h2 IH2]; intros Hx v hS.
  - (* one R step x -> y against S* x v: (2) at r_step *)
    destruct (refl_R_vs_crt_S R S E Q HQR HQS HErf HEtr HES Htile _ _ _ Hx
                (@r_step _ _ _ _ hR) hS) as [w [w' [hw [hw' Hew]]]].
    exists w', w. split; [exact hw'|split].
    + exact (cr_crt _ _ _ hw).
    + exact (HEsy _ _ Hew).
  - (* R* is refl *)
    exists v, v. split; [exact hS|split].
    + exact (@rt_refl _ _ _).
    + exact (HErf v).
  - (* x ->R* y ->R* z, S* x v *)
    (* left tile: S* y y1, R* v v1, E y1 v1 *)
    destruct (IH1 Hx v hS) as [y1 [v1 [hy1 [hv1 Hey1]]]].
    pose proof (crt_Q R Q HQR _ _ Hx h1) as Hy.
    (* right tile from y: S* z z1, R* y1 y2, E z1 y2 *)
    destruct (IH2 Hy y1 hy1) as [z1 [y2 [hz1 [hy2 Hez1]]]].
    (* transport R* y1 y2 across E y1 v1 *)
    pose proof (crt_Q S Q HQS _ _ Hy hy1) as Hy1.
    pose proof (crt_Q S Q HQS _ _ Hx hS) as Hv.
    pose proof (crt_Q R Q HQR _ _ Hv hv1) as Hv1.
    destruct (crt_E_transport R E Q HQR HEtr HER _ _ _ Hy1 Hv1 Hey1 hy2)
      as [v2 [hv2 Hev2]].
    exists z1, v2. split; [exact hz1|split].
    + exact (@rt_trans _ _ _ _ _ hv1 hv2).
    + exact (HEtr _ _ _ Hez1 Hev2).
Qed.

(** ** Theorem (A), as the shared statement. The [CRelationClasses] laws are
    passed as they are: each is convertible to the unfolded form the lemmas above
    take. *)

Theorem HR_strong_commutation_modulo : HR_strong_commutation_modulo_statement.
Proof.
  unfold HR_strong_commutation_modulo_statement.
  intros A R S E Q HQR HQS HErf HEsy HEtr HER HES Htile.
  exact (crt_R_vs_crt_S R S E Q HQR HQS HErf HEsy HEtr HER HES Htile).
Qed.

(* Print Assumptions HR_strong_commutation_modulo. *)
