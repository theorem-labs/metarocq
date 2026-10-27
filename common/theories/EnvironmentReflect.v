(* Distributed under the terms of the MIT license. *)
From Stdlib Require Import ssreflect ssrbool ssrfun Morphisms Setoid.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Primitive Universes Environment Reflect.
From Equations.Prop Require Import Classes EqDecInstances.

Ltac Tauto.intuition_solver ::= auto with *.

Module EnvironmentReflect (T : Term) (Import E : EnvironmentSig T) (Import TDec : TermDecide T) (Import EDec : EnvironmentDecide T E).

  Local Notation extendsb_decls_part Σ Σ'
    := (forallb (fun d => let c := d.1 in skipn (#|lookup_envs Σ' c| - #|lookup_envs Σ c|) (lookup_envs Σ' c) == lookup_envs Σ c) (declarations Σ)) (only parsing).
  Local Notation strictly_extendsb_decls_part Σ Σ'
    := (skipn (#|Σ'.(declarations)| - #|Σ.(declarations)|) Σ'.(declarations) == Σ.(declarations)) (only parsing).

  Lemma extends_decls_partT (Σ Σ' : global_env)
    : reflectT (extends_decls_part Σ Σ') (extendsb_decls_part Σ Σ').
  Proof.
    case: (@forallbP _ _ _ _ (fun _ => eqb_specT _ _)) => H; constructor.
    all: setoid_rewrite Forall_forall in H.
    { move => c.
      specialize (fun d => H (c, d)).
      cbn [fst] in *.
      specialize (fun pf : { d : _ | In (c, d) _ } => H (proj1_sig pf) (proj2_sig pf)).
      destruct (lookup_envs Σ c) eqn:H'.
      { eexists; rewrite app_nil_r; reflexivity. }
      rewrite <- H; clear H.
      { eexists; symmetry; apply firstn_skipn. }
      unfold lookup_envs in *.
      move: H'; elim: (declarations Σ); cbn [lookup_globals] => //= ??.
      case: eqb_specT => ?; subst.
      all: move => H H'; try destruct (H H'); rdest; eauto. }
    { intro H'; apply H; clear H; intros [c ?]; specialize (H' c).
      destruct H' as [decls H'].
      cbn [fst].
      rewrite H' length_app Nat.add_sub skipn_all_app //. }
  Qed.

  Lemma strictly_extends_decls_partT (Σ Σ' : global_env)
    : reflectT (strictly_extends_decls_part Σ Σ') (strictly_extendsb_decls_part Σ Σ').
  Proof.
    case: eqb_specT => H; constructor.
    { rewrite -H.
      eexists; symmetry; apply firstn_skipn. }
    { move => [Σ'' H'].
      move: H. rewrite H' length_app Nat.add_sub skipn_all_app //. }
  Qed.

  (** Decides [extends_prim_fresh]: it quantifies over all kernames, but only
      those in [Σ']'s operation table can satisfy its premise, so the finite
      table is enough. *)
  Definition extendsb_prim_fresh (Σ Σ' : global_env) : bool
    := forallb (fun '(c, _) =>
         (Retroknowledge.prim_op_of Σ.(retroknowledge) c
            == Retroknowledge.prim_op_of Σ'.(retroknowledge) c)
         || match lookup_env Σ c with None => true | Some _ => false end)
         Σ'.(retroknowledge).(Retroknowledge.retro_ops).

  Lemma extends_prim_freshT Σ Σ'
    : reflectT (extends_prim_fresh Σ Σ') (extendsb_prim_fresh Σ Σ').
  Proof.
    destruct (extendsb_prim_fresh Σ Σ') eqn:hb; constructor.
    - intros c op h.
      have hin := Retroknowledge.lookup_op_spec _ _ _ h.
      have H := proj1 (forallb_forall _ _) hb _ hin. cbn beta in H.
      destruct (orb_true_elim _ _ H) as [He|Hl].
      + apply eqb_eq in He. left. now rewrite He.
      + right. destruct (lookup_env Σ c) eqn:hl; [discriminate|reflexivity].
    - intros hp.
      have ht : extendsb_prim_fresh Σ Σ' = true.
      { rewrite /extendsb_prim_fresh. apply (proj2 (forallb_forall _ _)).
        intros [c op0] hin.
        destruct (Retroknowledge.lookup_op_in _ _ _ hin) as [op1 h1].
        change (Retroknowledge.prim_op_of (retroknowledge Σ') c = Some op1) in h1.
        apply orb_true_intro. destruct (hp c op1 h1) as [h2|h2].
        + left. rewrite h1 h2. apply eqb_refl.
        + right. now rewrite h2. }
      rewrite ht in hb. discriminate.
  Qed.
  Definition extendsb (Σ Σ' : global_env) : bool
    := Σ.(universes) ⊂?_cs Σ'.(universes)
       && extendsb_decls_part Σ Σ'
       && Retroknowledge.extendsb Σ.(retroknowledge) Σ'.(retroknowledge)
       && extendsb_prim_fresh Σ Σ'.

  Definition extends_declsb (Σ Σ' : global_env) : bool
    := (Σ.(universes) == Σ'.(universes))
       && extendsb_decls_part Σ Σ'
       && (Σ.(retroknowledge) == Σ'.(retroknowledge)).

  Definition extends_strictly_on_declsb (Σ Σ' : global_env) : bool
    := (Σ.(universes) ⊂?_cs Σ'.(universes))
       && strictly_extendsb_decls_part Σ Σ'
       && Retroknowledge.extendsb Σ.(retroknowledge) Σ'.(retroknowledge)
       && extendsb_prim_fresh Σ Σ'.

  Definition strictly_extends_declsb (Σ Σ' : global_env) : bool
    := (Σ.(universes) == Σ'.(universes))
       && strictly_extendsb_decls_part Σ Σ'
       && (Σ.(retroknowledge) == Σ'.(retroknowledge)).

  Lemma extendsT Σ Σ' : reflectT (extends Σ Σ') (extendsb Σ Σ').
  Proof.
    rewrite /extends/extendsb.
    case: extends_decls_partT => hd; case: Retroknowledge.extendsT => hr;
      case: ContextSet.subsetP => hu; case: extends_prim_freshT => hp; cbn;
      constructor; first [ split; assumption | intros [? ? ? ?]; contradiction ].
  Qed.

  Lemma extends_declsT Σ Σ' : reflectT (extends_decls Σ Σ') (extends_declsb Σ Σ').
  Proof.
    rewrite /extends_decls/extends_declsb.
    case: extends_decls_partT; case: eqb_specT; case: eqb_specT; cbn;
      constructor; intuition.
  Qed.

  Lemma extends_strictly_on_declsT Σ Σ' : reflectT (extends_strictly_on_decls Σ Σ') (extends_strictly_on_declsb Σ Σ').
  Proof.
    rewrite /extends_strictly_on_decls/extends_strictly_on_declsb.
    case: strictly_extends_decls_partT => hd; case: Retroknowledge.extendsT => hr;
      case: ContextSet.subsetP => hu; case: extends_prim_freshT => hp; cbn;
      constructor; first [ split; assumption | intros [? ? ? ?]; contradiction ].
  Qed.

  Lemma strictly_extends_declsT Σ Σ' : reflectT (strictly_extends_decls Σ Σ') (strictly_extends_declsb Σ Σ').
  Proof.
    rewrite /strictly_extends_decls/strictly_extends_declsb.
    case: strictly_extends_decls_partT; case: eqb_specT; case: eqb_specT; cbn;
      constructor; intuition.
  Qed.

  Lemma extends_spec Σ Σ' : extendsb Σ Σ' <~> extends Σ Σ'.
  Proof.
    case: extendsT; split; intuition congruence.
  Qed.

  Lemma extends_decls_spec Σ Σ' : extends_declsb Σ Σ' <~> extends_decls Σ Σ'.
  Proof.
    case: extends_declsT; split; intuition congruence.
  Qed.

  Lemma extends_strictly_on_decls_spec Σ Σ' : extends_strictly_on_declsb Σ Σ' <~> extends_strictly_on_decls Σ Σ'.
  Proof.
    case: extends_strictly_on_declsT; split; intuition congruence.
  Qed.

  Lemma strictly_extends_decls_spec Σ Σ' : strictly_extends_declsb Σ Σ' <~> strictly_extends_decls Σ Σ'.
  Proof.
    case: strictly_extends_declsT; split; intuition congruence.
  Qed.

  Definition compatible_globalsb (Σ Σ' : global_declarations) : bool
    := KernameSet.for_all
         (fun c => lookup_globals Σ c == lookup_globals Σ' c)
         (KernameSet.inter (declared_kername_set Σ) (declared_kername_set Σ')).

  Definition compatibleb (Σ Σ' : global_env) : bool
    := Retroknowledge.compatible Σ.(retroknowledge) Σ'.(retroknowledge)
       && compatible_globalsb Σ.(declarations) Σ'.(declarations).

  Lemma compatible_globalsP Σ Σ' : reflect (compatible_globals Σ Σ') (compatible_globalsb Σ Σ').
  Proof.
    rewrite /compatible_globals/compatible_globalsb.
    lazymatch goal with
    | [ |- context[KernameSet.for_all ?f ?s] ]
      => generalize (@KernameSet.for_all_spec s f _)
    end.
    rewrite /KernameSet.For_all.
    case: KernameSet.for_all; move => [H1 H2]; constructor.
    all: first [ specialize (H1 eq_refl); rename H1 into H | clear H1 ].
    all: try pose proof (fun x => diff_false_true (H2 x)) as H; clear H2.
    all: move: H.
    all: setoid_rewrite KernameSet.inter_spec.
    all: setoid_rewrite declared_kername_set_spec.
    all: setoid_rewrite <- lookup_globals_nil.
    1: move => H c; move: (H c); clear H.
    2: move => H nH; apply H => c; move: (nH c); clear H nH.
    all: case: eqb_spec.
    all: intuition.
  Qed.

  Lemma compatible_globals_spec Σ Σ' : compatible_globalsb Σ Σ' <-> compatible_globalsb Σ Σ'.
  Proof. case: compatible_globalsP; intuition. Qed.

  Lemma compatibleP Σ Σ' : reflect (compatible Σ Σ') (compatibleb Σ Σ').
  Proof.
    rewrite /compatible/compatibleb.
    case: compatible_globalsP; destruct Retroknowledge.compatible; cbn; constructor; intuition.
  Qed.

  Lemma compatible_spec Σ Σ' : compatibleb Σ Σ' <-> compatibleb Σ Σ'.
  Proof. case: compatibleP; intuition. Qed.

End EnvironmentReflect.

Module Type EnvironmentReflectSig (T : Term) (E : EnvironmentSig T) (TDec : TermDecide T) (EDec : EnvironmentDecide T E).
  Include EnvironmentReflect T E TDec EDec.
End EnvironmentReflectSig.
