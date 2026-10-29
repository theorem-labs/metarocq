(* Distributed under the terms of the MIT license. *)
(** * Theorem (B): Hindley-Rosen modulo an equivalence

   A closed proof of [HR_modulo_statement] ([PCUICEtaBetaEta]). Carrier-generic:
   nothing below mentions a term, a context or a reduction of PCUIC. The file
   Requires [PCUICEtaBetaEta] only to obtain the statement.

   Route (no strong normalisation anywhere; Newman is not used):
   - [hr_transport]: an [E]-step moves across a [(union R S)*] sequence, from the
     two E-commutation hypotheses ([clos_refl] form), on [Q]-elements.
   - [hr_commute_R] / [hr_commute_S]: one block [X*] ([X] = [R] or [S]) against
     one union step, joined modulo [E], from R-confluence, S-confluence modulo E
     and the R*/S* commutation (theorem (A)'s conclusion, a premise here).
   - [hr_strip]: one block [X*] against a whole union sequence (induction on the
     sequence; the tiles are glued by [hr_transport]).
   - [hr_union_confluent]: union sequence against union sequence (induction on
     the left sequence, [hr_strip] for each step, glued by [hr_transport]).
   [Q] is discharged on every term in play because only R- and S-steps create
   terms, both preserve [Q], and every [E]-related pair is formed of two reducts
   of [Q]-elements. *)

(* [utils] only for the [∑]/[×] notations the statement is written in; the
   Equations import is the one [PCUICEtaBetaEta] resolves [clos_refl_trans],
   [clos_refl] and [union] against. *)
From MetaRocq.Utils Require Import utils.
From Equations.Type Require Import Relation.
From MetaRocq.PCUIC Require Import PCUICEtaBetaEta.

Section HRModulo.
  Context {A : Type} (R S E : A -> A -> Type) (Q : A -> Type).
  Context (QR : forall t u, Q t -> R t u -> Q u).
  Context (QS : forall t u, Q t -> S t u -> Q u).
  Context (Erefl : CRelationClasses.Reflexive E).
  Context (Esym : CRelationClasses.Symmetric E).
  Context (Etrans : CRelationClasses.Transitive E).
  Context (ER : forall t t' u, Q t -> Q t' -> E t t' -> R t u ->
                  ∑ u', clos_refl R t' u' × E u u').
  Context (ES : forall t t' u, Q t -> Q t' -> E t t' -> S t u ->
                  ∑ u', clos_refl S t' u' × E u u').
  Context (Rconf : forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans R t v ->
                     ∑ w, clos_refl_trans R u w × clos_refl_trans R v w).
  Context (Sconf : forall t u v, Q t -> clos_refl_trans S t u -> clos_refl_trans S t v ->
                     ∑ u' v', clos_refl_trans S u u' × clos_refl_trans S v v' × E u' v').
  Context (RS : forall t u v, Q t -> clos_refl_trans R t u -> clos_refl_trans S t v ->
                  ∑ u' v', clos_refl_trans S u u' × clos_refl_trans R v v' × E u' v').

  Local Abbreviation U := (union R S).

  Lemma hr_rt_Q (X : A -> A -> Type) :
    (forall t u, Q t -> X t u -> Q u) ->
    forall t u, Q t -> clos_refl_trans X t u -> Q u.
  Proof.
    intros HX t u Ht H. revert Ht.
    induction H as [x y H | x | x y z H1 IH1 H2 IH2]; intros Ht.
    - exact (HX _ _ Ht H).
    - exact Ht.
    - exact (IH2 (IH1 Ht)).
  Qed.

  Lemma hr_QU : forall t u, Q t -> U t u -> Q u.
  Proof.
    intros t u Ht [H|H].
    - exact (QR _ _ Ht H).
    - exact (QS _ _ Ht H).
  Qed.

  Lemma hr_rt_map (X Y : A -> A -> Type) :
    (forall a b, X a b -> Y a b) ->
    forall a b, clos_refl_trans X a b -> clos_refl_trans Y a b.
  Proof.
    intros HXY a b H.
    induction H as [x y H | x | x y z H1 IH1 H2 IH2].
    - apply rt_step. exact (HXY _ _ H).
    - apply rt_refl.
    - eapply rt_trans; [exact IH1 | exact IH2].
  Qed.

  Lemma hr_rt_R_U : forall a b, clos_refl_trans R a b -> clos_refl_trans U a b.
  Proof. apply hr_rt_map. intros a b H. left. exact H. Qed.

  Lemma hr_rt_S_U : forall a b, clos_refl_trans S a b -> clos_refl_trans U a b.
  Proof. apply hr_rt_map. intros a b H. right. exact H. Qed.

  (** An [E]-step moves across a union sequence. *)
  Lemma hr_transport :
    forall a b, clos_refl_trans U a b ->
    forall a', Q a -> Q a' -> E a a' ->
    ∑ b', clos_refl_trans U a' b' × E b b'.
  Proof.
    intros a b H.
    induction H as [x y H | x | x y z H1 IH1 H2 IH2]; intros a' Ha Ha' He.
    - destruct H as [H|H].
      + destruct (ER _ _ _ Ha Ha' He H) as [b' [Hb' Eb]].
        exists b'. split; [|exact Eb].
        destruct Hb' as [b'' Hb'|]; [apply rt_step; left; exact Hb' | apply rt_refl].
      + destruct (ES _ _ _ Ha Ha' He H) as [b' [Hb' Eb]].
        exists b'. split; [|exact Eb].
        destruct Hb' as [b'' Hb'|]; [apply rt_step; right; exact Hb' | apply rt_refl].
    - exists a'. split; [apply rt_refl | exact He].
    - destruct (IH1 a' Ha Ha' He) as [y' [Hy' Ey]].
      assert (Qy : Q y) by exact (hr_rt_Q U hr_QU _ _ Ha H1).
      assert (Qy' : Q y') by exact (hr_rt_Q U hr_QU _ _ Ha' Hy').
      destruct (IH2 y' Qy Qy' Ey) as [z' [Hz' Ez]].
      exists z'. split; [eapply rt_trans; [exact Hy' | exact Hz'] | exact Ez].
  Qed.

  (** One [R*] block against one union step. *)
  Lemma hr_commute_R :
    forall t u v, Q t -> clos_refl_trans R t u -> U t v ->
    ∑ u' v', clos_refl_trans U u u' × clos_refl_trans R v v' × E u' v'.
  Proof.
    intros t u v Ht Hu [Hv|Hv].
    - assert (Hv' : clos_refl_trans R t v) by (apply rt_step; exact Hv).
      destruct (Rconf t u v Ht Hu Hv') as [w [Hw1 Hw2]].
      exists w, w. split; [exact (hr_rt_R_U _ _ Hw1) | split; [exact Hw2 | exact (Erefl w)]].
    - assert (Hv' : clos_refl_trans S t v) by (apply rt_step; exact Hv).
      destruct (RS t u v Ht Hu Hv') as [a [b [Ha [Hb Eab]]]].
      exists a, b. split; [exact (hr_rt_S_U _ _ Ha) | split; [exact Hb | exact Eab]].
  Qed.

  (** One [S*] block against one union step. *)
  Lemma hr_commute_S :
    forall t u v, Q t -> clos_refl_trans S t u -> U t v ->
    ∑ u' v', clos_refl_trans U u u' × clos_refl_trans S v v' × E u' v'.
  Proof.
    intros t u v Ht Hu [Hv|Hv].
    - assert (Hv' : clos_refl_trans R t v) by (apply rt_step; exact Hv).
      destruct (RS t v u Ht Hv' Hu) as [a [b [Ha [Hb Eab]]]].
      exists b, a. split; [exact (hr_rt_R_U _ _ Hb) | split; [exact Ha | exact (Esym _ _ Eab)]].
    - assert (Hv' : clos_refl_trans S t v) by (apply rt_step; exact Hv).
      destruct (Sconf t u v Ht Hu Hv') as [a [b [Ha [Hb Eab]]]].
      exists a, b. split; [exact (hr_rt_S_U _ _ Ha) | split; [exact Hb | exact Eab]].
  Qed.

  (** One block [X*] against a whole union sequence. *)
  Lemma hr_strip (X : A -> A -> Type)
    (QX : forall t u, Q t -> X t u -> Q u)
    (CX : forall t u v, Q t -> clos_refl_trans X t u -> U t v ->
          ∑ u' v', clos_refl_trans U u u' × clos_refl_trans X v v' × E u' v') :
    forall t v, clos_refl_trans U t v ->
    forall u, Q t -> clos_refl_trans X t u ->
    ∑ u' v', clos_refl_trans U u u' × clos_refl_trans X v v' × E u' v'.
  Proof.
    intros t v H.
    induction H as [x y H | x | x m z H1 IH1 H2 IH2]; intros u Ht Hu.
    - exact (CX _ _ _ Ht Hu H).
    - exists u, u. split; [apply rt_refl | split; [exact Hu | exact (Erefl u)]].
    - destruct (IH1 u Ht Hu) as [a [b [Ha [Hb Eab]]]].
      assert (Qm : Q m) by exact (hr_rt_Q U hr_QU _ _ Ht H1).
      destruct (IH2 b Qm Hb) as [c [d [Hc [Hd Ecd]]]].
      assert (Qb : Q b) by exact (hr_rt_Q X QX _ _ Qm Hb).
      assert (Qu : Q u) by exact (hr_rt_Q X QX _ _ Ht Hu).
      assert (Qa : Q a) by exact (hr_rt_Q U hr_QU _ _ Qu Ha).
      destruct (hr_transport b c Hc a Qb Qa (Esym _ _ Eab)) as [c' [Hc' Ec]].
      exists c', d. split; [eapply rt_trans; [exact Ha | exact Hc'] |].
      split; [exact Hd | exact (Etrans _ _ _ (Esym _ _ Ec) Ecd)].
  Qed.

  (** The union is confluent modulo [E] on [Q]. *)
  Lemma hr_union_confluent :
    forall t u, clos_refl_trans U t u ->
    forall v, Q t -> clos_refl_trans U t v ->
    ∑ u' v', clos_refl_trans U u u' × clos_refl_trans U v v' × E u' v'.
  Proof.
    intros t u H.
    induction H as [x y H | x | x m z H1 IH1 H2 IH2]; intros v Ht Hv.
    - destruct H as [H|H].
      + assert (Hy : clos_refl_trans R x y) by (apply rt_step; exact H).
        destruct (hr_strip R QR hr_commute_R x v Hv y Ht Hy) as [a [b [Ha [Hb Eab]]]].
        exists a, b. split; [exact Ha | split; [exact (hr_rt_R_U _ _ Hb) | exact Eab]].
      + assert (Hy : clos_refl_trans S x y) by (apply rt_step; exact H).
        destruct (hr_strip S QS hr_commute_S x v Hv y Ht Hy) as [a [b [Ha [Hb Eab]]]].
        exists a, b. split; [exact Ha | split; [exact (hr_rt_S_U _ _ Hb) | exact Eab]].
    - exists v, v. split; [exact Hv | split; [apply rt_refl | exact (Erefl v)]].
    - destruct (IH1 v Ht Hv) as [a [b [Ha [Hb Eab]]]].
      assert (Qm : Q m) by exact (hr_rt_Q U hr_QU _ _ Ht H1).
      destruct (IH2 a Qm Ha) as [c [d [Hc [Hd Ecd]]]].
      assert (Qa : Q a) by exact (hr_rt_Q U hr_QU _ _ Qm Ha).
      assert (Qv : Q v) by exact (hr_rt_Q U hr_QU _ _ Ht Hv).
      assert (Qb : Q b) by exact (hr_rt_Q U hr_QU _ _ Qv Hb).
      destruct (hr_transport a d Hd b Qa Qb Eab) as [d' [Hd' Ed]].
      exists c, d'. split; [exact Hc |].
      split; [eapply rt_trans; [exact Hb | exact Hd'] | exact (Etrans _ _ _ Ecd Ed)].
  Qed.

End HRModulo.

(** Theorem (B), closed. *)
Theorem HR_modulo : HR_modulo_statement.
Proof.
  unfold HR_modulo_statement.
  intros A R S E Q QR QS Erefl Esym Etrans ER ES Rconf Sconf RS t u v Ht Hu Hv.
  exact (hr_union_confluent R S E Q QR QS Erefl Esym Etrans ER ES Rconf Sconf RS
           t u Hu v Ht Hv).
Qed.

(* Print Assumptions HR_modulo. *)
