(* Distributed under the terms of the MIT license. *)
(** * BET-315 eta lane, C4 theorem (A): strong commutation implies commutation,
    modulo an equivalence [E], relativised to an invariant [Q].

   Proves [HR_strong_commutation_modulo_statement] ([PCUICEtaBetaEta]) as stated
   there. The proof is carrier-generic: it uses no MetaRocq AST, only the shared
   statement and the [Type]-valued closures of [Equations.Type.Relation].

   ROUTE: tile pasting. One notion, [tile Q E X Y X' Y'] ("an X-step and a Y-step
   from a Q-element close, the X-reduct by Y', the Y-reduct by X', up to E"), and
   one pasting lemma, [tile_paste], which closes a tile under [clos_refl_trans]
   on its Y side by induction on the [rt_step]/[rt_refl]/[rt_trans] derivation
   (the [rt_trans] case glues two sub-tiles side by side and transports the
   seam across [E]). [tile_paste] is used twice, once in each direction, with
   [tile_flip] to swap the axes between the two uses:

     C3 tile                    : tile (R^=) S     (R^=) S*   [tile_base]
     paste horizontally         : tile (R^=) S*    (R^=) S*   [tile_paste]
     flip, restrict, widen      : tile S*    R     S*    R*   [tile_flip, tile_mono]
     paste vertically           : tile S*    R*    S*    R*   [tile_paste]
     flip                       : tile R*    S*    R*    S*   = the conclusion

   Generalising the C3 tile's [R]-input to [clos_refl R] is what makes the
   horizontal pasting self-feeding: each sub-tile's [clos_refl R] output is the
   next sub-tile's input, so the induction needs no case split on it.

   THE [Q] INVARIANT. The [E]-transport hypotheses demand [Q] at both ends of the
   [E]-pair. Every element the proof touches is reached from the starting
   [Q]-element by [R]- and [S]-steps, so [Q] is threaded explicitly:
   [crt_preserves] / [cr_preserves] lift step-preservation to the closures, and
   [crt_transport] keeps [Q] on both sides of the moving [E]-pair at every step. *)

From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.PCUIC Require Import PCUICEtaBetaEta.

(** ** Closures preserve the invariant. *)

Lemma cr_preserves {A : Type} (Q : A -> Type) (X : A -> A -> Type) :
  (forall t u, Q t -> X t u -> Q u) ->
  forall t u, Q t -> clos_refl X t u -> Q u.
Proof.
  intros HQ t u q h. destruct h as [u0 s|].
  - exact (HQ _ _ q s).
  - exact q.
Qed.

Lemma crt_preserves {A : Type} (Q : A -> Type) (X : A -> A -> Type) :
  (forall t u, Q t -> X t u -> Q u) ->
  forall t u, Q t -> clos_refl_trans X t u -> Q u.
Proof.
  intros HQ t u q h. revert q.
  induction h as [t0 u0 s | t0 | t0 m u0 h1 IH1 h2 IH2]; intros q.
  - exact (HQ _ _ q s).
  - exact q.
  - exact (IH2 (IH1 q)).
Qed.

(** ** Closure inclusions. *)

Lemma cr_of {A : Type} (X : A -> A -> Type) :
  forall t u, X t u -> clos_refl X t u.
Proof. intros t u h. apply r_step. exact h. Qed.

Lemma crt_of_cr {A : Type} (X : A -> A -> Type) :
  forall t u, clos_refl X t u -> clos_refl_trans X t u.
Proof.
  intros t u h. destruct h as [u0 s|].
  - apply rt_step. exact s.
  - apply rt_refl.
Qed.

(** ** Transport of a [clos_refl_trans] derivation across [E].

   From the one-step form ([clos_refl] on the moved step, the C1a/C1b shape),
   on [Q]-elements. Both ends of the moving [E]-pair stay [Q]: the left end is
   reached by [X]-steps from a [Q]-element, the right end by [clos_refl X]-steps
   from one. *)

Lemma crt_transport {A : Type} (Q : A -> Type) (E X : A -> A -> Type) :
  (forall t u, Q t -> X t u -> Q u) ->
  (forall t t' u, Q t -> Q t' -> E t t' -> X t u ->
     { u' : A & prod (clos_refl X t' u') (E u u') }) ->
  forall t t' u, Q t -> Q t' -> E t t' -> clos_refl_trans X t u ->
     { u' : A & prod (clos_refl_trans X t' u') (E u u') }.
Proof.
  intros HQ HE t t' u q q' e h. revert t' q q' e.
  induction h as [t0 u0 s | t0 | t0 m u0 h1 IH1 h2 IH2]; intros t' q q' e.
  - destruct (HE _ _ _ q q' e s) as [u' [s' e']].
    exists u'. split.
    + exact (crt_of_cr X _ _ s').
    + exact e'.
  - exists t'. split.
    + apply rt_refl.
    + exact e.
  - destruct (IH1 t' q q' e) as [m' [s1 e1]].
    pose proof (crt_preserves Q X HQ _ _ q h1) as qm.
    pose proof (crt_preserves Q X HQ _ _ q' s1) as qm'.
    destruct (IH2 m' qm qm' e1) as [u' [s2 e2]].
    exists u'. split.
    + eapply rt_trans; [exact s1 | exact s2].
    + exact e2.
Qed.

(** ** Tiles. *)

(** [tile Q E X Y X' Y']: from a [Q]-element [t], an [X]-step to [x] and a
    [Y]-step to [y] close: [x] by [Y'] to [a], [y] by [X'] to [b], [E a b]. *)
Definition tile {A : Type} (Q : A -> Type) (E X Y X' Y' : A -> A -> Type) : Type :=
  forall t x y, Q t -> X t x -> Y t y ->
    { a : A & { b : A & prod (Y' x a) (prod (X' y b) (E a b)) } }.

Lemma tile_flip {A : Type} (Q : A -> Type) (E X Y X' Y' : A -> A -> Type) :
  (forall x y, E x y -> E y x) ->
  tile Q E X Y X' Y' -> tile Q E Y X Y' X'.
Proof.
  intros Es T t x y q hx hy.
  destruct (T t y x q hy hx) as [a [b [ya [xb e]]]].
  exists b, a. split; [exact xb | split; [exact ya | exact (Es _ _ e)]].
Qed.

Lemma tile_mono {A : Type} (Q : A -> Type) (E X Y X' Y' X0 Y0 X1 Y1 : A -> A -> Type) :
  (forall t u, X0 t u -> X t u) ->
  (forall t u, Y0 t u -> Y t u) ->
  (forall t u, X' t u -> X1 t u) ->
  (forall t u, Y' t u -> Y1 t u) ->
  tile Q E X Y X' Y' -> tile Q E X0 Y0 X1 Y1.
Proof.
  intros iX iY oX oY T t x y q hx hy.
  destruct (T t x y q (iX _ _ hx) (iY _ _ hy)) as [a [b [ya [xb e]]]].
  exists a, b. split; [exact (oY _ _ ya) | split; [exact (oX _ _ xb) | exact e]].
Qed.

(** The C3 tile, with its [R]-input widened to [clos_refl R]. *)
Lemma tile_base {A : Type} (Q : A -> Type) (E R S : A -> A -> Type) :
  (forall x, E x x) ->
  (forall x y, E x y -> E y x) ->
  (forall t u v, Q t -> R t v -> S t u ->
     { w : A & { w' : A & prod (clos_refl R u w) (prod (clos_refl_trans S v w') (E w w')) } }) ->
  tile Q E (clos_refl R) S (clos_refl R) (clos_refl_trans S).
Proof.
  intros Er Es H t x y q hx hy.
  destruct hx as [x0 r|].
  - destruct (H t y x0 q r hy) as [w [w' [rw [sw e]]]].
    exists w', w. split; [exact sw | split; [exact rw | exact (Es _ _ e)]].
  - exists y, y. split; [apply rt_step; exact hy | split; [apply r_refl | apply Er]].
Qed.

(** The pasting lemma: a tile whose [Y]-side output is [clos_refl_trans Y]
    and whose [X]-side output is its own [X]-input closes under
    [clos_refl_trans] on the [Y] side. Induction on the [Y]-derivation in the
    [rt_step]/[rt_refl]/[rt_trans] form; in the [rt_trans] case the second
    sub-tile is fed the first's [X]-output, and the first's [Y]-closing
    derivation is extended by transporting the second's across [E]. *)
Lemma tile_paste {A : Type} (Q : A -> Type) (E X Y : A -> A -> Type) :
  (forall x, E x x) ->
  (forall x y, E x y -> E y x) ->
  (forall x y z, E x y -> E y z -> E x z) ->
  (forall t u, Q t -> X t u -> Q u) ->
  (forall t u, Q t -> Y t u -> Q u) ->
  (forall t t' u, Q t -> Q t' -> E t t' -> clos_refl_trans Y t u ->
     { u' : A & prod (clos_refl_trans Y t' u') (E u u') }) ->
  tile Q E X Y X (clos_refl_trans Y) ->
  tile Q E X (clos_refl_trans Y) X (clos_refl_trans Y).
Proof.
  intros Er Es Et HQX HQY TY T t x y q hx hy. revert x q hx.
  induction hy as [t0 y0 s | t0 | t0 m y0 h1 IH1 h2 IH2]; intros x q hx.
  - exact (T t0 x y0 q hx s).
  - exists x, x. split; [apply rt_refl | split; [exact hx | apply Er]].
  - (* first sub-tile, over [t0 ->Y* m] *)
    destruct (IH1 x q hx) as [a1 [b1 [ya1 [xb1 e1]]]].
    pose proof (crt_preserves Q Y HQY _ _ q h1) as qm.
    (* second sub-tile, over [m ->Y* y0], fed the first's X-output [b1] *)
    destruct (IH2 b1 qm xb1) as [a2 [b2 [ya2 [xb2 e2]]]].
    (* seam: move [b1 ->Y* a2] across [E b1 a1]; both ends are Q *)
    pose proof (HQX _ _ qm xb1) as qb1.
    pose proof (crt_preserves Q Y HQY _ _ (HQX _ _ q hx) ya1) as qa1.
    destruct (TY b1 a1 a2 qb1 qa1 (Es _ _ e1) ya2) as [c [ya1c e3]].
    exists c, b2. split.
    + eapply rt_trans; [exact ya1 | exact ya1c].
    + split; [exact xb2 | exact (Et _ _ _ (Es _ _ e3) e2)].
Qed.

(** ** Theorem (A). *)

Theorem HR_strong_commutation_modulo : HR_strong_commutation_modulo_statement.
Proof.
  unfold HR_strong_commutation_modulo_statement.
  intros A R S E Q HQR HQS Er Es Et C1a C1b H.
  pose proof (crt_transport Q E R HQR C1a) as TR.
  pose proof (crt_transport Q E S HQS C1b) as TS.
  (* C3 tile with a [clos_refl R] input *)
  pose proof (tile_base Q E R S Er Es H) as T1.
  (* paste along S* *)
  pose proof (tile_paste Q E (clos_refl R) S Er Es Et
                (cr_preserves Q R HQR) HQS TS T1) as T2.
  (* swap the axes; restrict the R-input to one step; widen the R-output to R* *)
  pose proof (tile_flip Q E (clos_refl R) (clos_refl_trans S)
                (clos_refl R) (clos_refl_trans S) Es T2) as T3.
  pose proof (tile_mono Q E
                (clos_refl_trans S) (clos_refl R) (clos_refl_trans S) (clos_refl R)
                (clos_refl_trans S) R (clos_refl_trans S) (clos_refl_trans R)
                (fun t u h => h) (cr_of R) (fun t u h => h) (crt_of_cr R) T3) as T4.
  (* paste along R* *)
  pose proof (tile_paste Q E (clos_refl_trans S) R Er Es Et
                (crt_preserves Q S HQS) HQR TR T4) as T5.
  (* swap back: R* against S* *)
  exact (tile_flip Q E (clos_refl_trans S) (clos_refl_trans R)
           (clos_refl_trans S) (clos_refl_trans R) Es T5).
Qed.
