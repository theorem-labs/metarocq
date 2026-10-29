(* Distributed under the terms of the MIT license. *)
(** * [beta_eta] preserves scoping

   Needed so that (A)'s induction can re-apply C3
   ([red1_eta1_strong_commutation], which carries [is_closed_context Γ] and
   [is_open_term Γ t]) at every step of a multi-step reduction.

   [is_closed_context Γ] is preserved trivially: [Γ] is fixed ([red1 Σ Γ]; [eta1]
   is context-free). Only [is_open_term Γ t] varies. [red1]'s half is base's
   ([red1_on_free_vars_cb], [Typing/PCUICClosedTyp]). The new content is that
   [eta1] preserves [on_free_vars], whose [eta_red] case needs

     on_free_vars (shiftnP 1 p) (lift0 1 t) -> on_free_vars p t,

   the window-converse of [on_free_vars_lift]. Base does not have it, and it is
   not derivable from [on_free_vars_lift]: [shiftnP 1 p] and [strengthenP 0 1 p]
   differ exactly at index 0, and "index 0 is not free in [lift0 1 t]" is the
   content itself (its unconditional form would be [on_free_vars xpredT], which is
   false). So [on_free_vars_lift_weakenP] proves it by the same induction as
   [on_free_vars_lift], with [weakenP] (true on the lifted window) in place of
   [strengthenP] (false on it).

   The premises are the ones C4 already carries: [ClosedBodies Σ], which every
   well-formed environment satisfies ([wf_ClosedBodies]; [wfE_ClosedBodies] for
   [wfE]), [is_closed_context Γ] and [is_open_term Γ t]. *)

From Stdlib Require Import ssreflect ssrbool.
From Equations.Type Require Import Relation Relation_Properties.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICInduction PCUICSigmaCalculus PCUICOnFreeVars PCUICOnOne PCUICReduction
     PCUICTyping PCUICClosedTyp PCUICEtaDefs PCUICEtaBetaEta PCUICClosedBodies.
From Equations Require Import Equations.

(** ** The window-converse of [on_free_vars_lift]. *)

Definition weakenP k n (p : nat -> bool) : nat -> bool :=
  fun i => if i <? k then p i else if i <? k + n then true else p (i - n).

Lemma shiftnP_weakenP k' k n p :
  shiftnP k' (weakenP k n p) =1 weakenP (k' + k) n (shiftnP k' p).
Proof.
  intros i. rewrite /shiftnP /weakenP.
  repeat nat_compare_specs => /= //.
  all: try lia_f_equal.
Qed.

Lemma on_free_vars_lift_weakenP (p : nat -> bool) n k t :
  on_free_vars (weakenP k n p) (lift n k t) = on_free_vars p t.
Proof.
  intros. revert t n k p.
  induction t using PCUICInduction.term_forall_list_ind; simpl => //; intros;
    rewrite ?forallb_map; try eapply All_forallb_eq_forallb; tea; simpl.
  2-6:try now rewrite ?shiftnP_weakenP ?IHt1 ?IHt2 ?IHt3.
  - rename n0 into i. rewrite /weakenP.
    repeat nat_compare_specs => //.
    all: try lia_f_equal.
  - rtoProp; solve_all. len; rewrite !shiftnP_weakenP e IHt.
    f_equal; solve_all. f_equal; solve_all. f_equal; solve_all. f_equal.
    solve_all.
    f_equal; solve_all.
    len. now rewrite !shiftnP_weakenP.
  - unfold test_def in *. simpl; intros ? [].
    len; rewrite shiftnP_weakenP. f_equal; eauto.
  - unfold test_def in *. simpl; intros ? [].
    len; rewrite shiftnP_weakenP. f_equal; eauto.
  - solve_all.
Qed.

Lemma shiftnP1_weakenP p : shiftnP 1 p =1 weakenP 0 1 p.
Proof.
  intros i. rewrite /shiftnP /weakenP.
  repeat nat_compare_specs => //.
Qed.

(** ** [eta1] preserves [on_free_vars], for EVERY predicate. *)

Lemma OnOne2_forallb {A} (R : A -> A -> Type) (p : A -> bool) l l' :
  OnOne2 R l l' -> (forall x y, R x y -> p x -> p y) -> forallb p l -> forallb p l'.
Proof.
  induction 1; cbn; intros HR H; move/andP: H => [h1 h2]; apply/andP; split; eauto.
Qed.

(** No goal pattern: after [rtoProp] the goal may be [forallb .. = true] rather
    than [is_true (forallb ..)], and [match goal] is syntactic. *)
Local Ltac simple_onone2 :=
  eapply OnOne2_forallb;
  [ eassumption
  | intros ?x ?y [? ?IH] ?h; cbv beta in IH; now apply IH
  | eassumption ].

(** [rtoProp] also turns a boolean-conjunction GOAL into a Prop conjunction, so
    split both forms; and beta-reduce the motive in the induction hypotheses. *)
Local Ltac split_goal :=
  repeat match goal with
         | |- is_true (_ && _) => apply/andP; split
         | |- _ /\ _ => split
         end.

Local Ltac simple_cong := cbv beta in *; rtoProp; split_goal; eauto.

Lemma eta1_on_free_vars t u : eta1 t u -> forall P, on_free_vars P t -> on_free_vars P u.
Proof.
  induction 1 using eta1_ind_all; intros P' Hfv.
  (* Unfold BEFORE the first bullet: once a bullet closes a goal, the rest are
     bullet-blocked and an [all:] there applies to ZERO goals, silently.
     [on_free_vars] does not unfold under plain [cbn]; [test_prim] is an
     Equations definition (needs [simp]); then reduce the record updates. *)
  all: cbn [on_free_vars] in Hfv |- *.
  all: try (simp test_prim in Hfv); try (simp test_prim).
  all: cbn [set_pparams set_preturn set_array_value set_array_default set_array_type
            pparams preturn pcontext puinst array_value array_default array_type
            array_level] in Hfv |- *.
  (* ORDER-INDEPENDENT. Positional bullets broke: the prelude above can close a
     goal outright, silently shifting every later bullet onto the wrong case.
     Each alternative must CLOSE its goal ([solve]), so this is sound whichever
     goal it lands on. *)
  all: first
    [ (* eta_red: the one substantive case *)
      solve [ move/andP: Hfv => [_ /andP [Ht _]];
              rewrite (on_free_vars_ext _ _ _ (shiftnP1_weakenP P')) in Ht;
              by rewrite on_free_vars_lift_weakenP in Ht ]
    | (* single-subterm congruences *)
      solve [ simple_cong ]
    | (* evar *)
      solve [ simple_onone2 ]
    | (* case params: the context test reads #|pparams|, preserved by OnOne2 *)
      solve [ match goal with X : OnOne2 _ _ _ |- _ => have Hlen := OnOne2_length X end;
              rewrite -Hlen; rtoProp; split_goal; try assumption; simple_onone2 ]
    | (* array values *)
      solve [ rtoProp; split_goal; try assumption; simple_onone2 ]
    | (* case branches: bcontext preserved, bbody by IH *)
      solve [ rtoProp; split_goal; try assumption;
              eapply OnOne2_forallb; [eassumption| |eassumption];
              intros x y [[_ IH] Heq] h; cbv beta in IH; move/andP: h => [h1 h2];
              rewrite -Heq; apply/andP; split; [exact h1|now apply IH] ]
    | (* fix/cofix, type or body: #|mfix| preserved; the unchanged component is
         equal by the tuple equality, the changed one goes by IH *)
      solve [ match goal with X : OnOne2 _ _ _ |- _ => rewrite -(OnOne2_length X) end;
              eapply OnOne2_forallb; [eassumption| |eassumption];
              intros x y [[_ IH] Heq] h; cbv beta in IH;
              move: h; rewrite /test_def => /andP [h1 h2];
              injection Heq as Hn Hb Hr; rewrite -Hb;
              apply/andP; split; solve [now apply IH | assumption] ] ].
Qed.

(** ** [beta_eta] preserves scoping (P-SCOPE). *)

Lemma beta_eta1_on_free_vars {cf : checker_flags} {Σ : global_env} {wfΣ : ClosedBodies Σ} {P Γ t u} :
  on_ctx_free_vars P Γ -> beta_eta1 Σ Γ t u -> on_free_vars P t -> on_free_vars P u.
Proof.
  intros HΓ [Hr|He] Ht.
  - eapply (@red1_on_free_vars_cb cf _ (empty_ext Σ) _ _ _ wfΣ); eassumption.
  - eapply eta1_on_free_vars; eassumption.
Qed.

Lemma beta_eta_on_free_vars {cf : checker_flags} {Σ : global_env} {wfΣ : ClosedBodies Σ} {P Γ t u} :
  on_ctx_free_vars P Γ -> beta_eta Σ Γ t u -> on_free_vars P t -> on_free_vars P u.
Proof.
  intros HΓ H. induction H; intros Ht; eauto.
  eapply beta_eta1_on_free_vars; eassumption.
Qed.

(** The form C4 / (A)'s induction consumes. *)
Lemma beta_eta_is_open_term {cf : checker_flags} {Σ : global_env} {wfΣ : ClosedBodies Σ} {Γ t u} :
  is_closed_context Γ -> beta_eta Σ Γ t u -> is_open_term Γ t -> is_open_term Γ u.
Proof.
  intros HΓ. eapply beta_eta_on_free_vars; tea.
  now rewrite on_free_vars_ctx_on_ctx_free_vars.
Qed.
