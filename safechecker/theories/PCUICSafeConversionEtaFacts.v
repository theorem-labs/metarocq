(* Distributed under the terms of the MIT license. *)
(* BET-64 ETAK (EtaConvFacts, for the K3 integrator EtaConv): the helper lemmas that the
   obligations of the η conversion checker [PCUICSafeConversionEta] use. Standalone: it
   imports no SafeChecker file, and nothing about the abstract environment, the checker's
   Equations or [reduce_stack]. The stack is the one of [PCUICPositionEta] (imported last).

   1. View algebra (untyped)
      - [eta_rename_tApp]                    (helper)
      - [eta_rename_mkApps]
      - [zipp_eta_decompose]
      - [decompose_stack_eta_appstack_snd]
      - [zipp_eta_appstack_snd]
      - [rigid_head]                         (definition: tLambda, tProd, tSort, tPrim)
      - [eta_rename_isLambda], [eta_rename_rigid_head], [eta_rename_isApp]
      - [eta_rename_lift_closed]             (EtaK1's K1 arm, EtaK1-patch.md §4)
   2. whnf and the virtual tail (untyped, [RedFlags.nodelta])
      - [eta_head_ok]                        (definition: the runtime check of G2b)
      - [mkApps_eq_notApp], [rigid_head_mkApps], [whne_nodelta_not_rigid],
        [whnf_rigid_mkApps_nil], [whnf_fixapp_eta_virtuals]   (helpers)
      - [whnf_mkApps_eta_virtuals]
      - [whnf_zipp_eta_rigid]
   3. Typed facts over an abstract well-typedness predicate
      - [ConvTypedFacts wt wfP]              (class: the NAMED HYPOTHESIS of this file;
                                              fields [ctf_context], [ctf_case_brs_length]
                                              (plan row T6 for [welltypedE]) and
                                              [ctf_wf_universes] (a T-row typingE fact))
      - [conv_typed_facts_base]              (its instance at base [welltyped] / [wf_ext];
                                              it does NOT discharge the [welltypedE] instance)
      - [ConvTypedFactsE]                    (class: its GENUINE field [ctf_contextE], the field
                                              [ctf_context] at [welltypedE]/[wf_extE]; the other
                                              two are proved there, PCUICEtaTypedFactsProved)
      - [wt_zipc_zipp], [wt_zipc_stack_context]   (derived, generic in wt/wfP)
   4. Facts at [welltypedE] that need no hypothesis
      - [welltypedE_tRel_vass]
      - [whnf_tRel_vass]
   5. Reduction under the η stack (section [EtaStackRed]; base: PCUICReduction.red1_context,
      red_context_zip, PCUICSafeLemmata.cored_context)
      - [red1_context_eta]                   (premise [no_Eta_arg π])
      - [red_context_zip_eta]                (every stack: Eta_arg drops the focus)
      - [cored_context_eta]                  (premise [no_Eta_arg π])

   Named hypotheses and their instances:
      [ConvTypedFacts wt wfP]  --  instance [conv_typed_facts_base : ConvTypedFacts welltyped wf_ext]
      [ConvTypedFactsE]        --  the same base instance, for its one field at base
   The η-context facts [wf_localE_push_real], [wf_localE_eta_step], [eta_rename_typing] are
   EtaPosK4's (PCUICPositionEtaTyping, section EtaTypingE), not restated here.
   Section [EtaStackRed]'s only [Context] is the environment Σ (not a hypothesis). There is
   no [Admitted], no [Axiom]. *)
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import config.
From MetaRocq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICCases PCUICLiftSubst PCUICTyping
     PCUICNormal PCUICInversion PCUICWfUniverses PCUICTypingEta PCUICEquality PCUICReduction PCUICSafeLemmata.
(* LAST: the η stack shadows base PCUICPosition's for the unqualified names. *)
From MetaRocq.PCUIC Require Import PCUICPositionEta.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags).

(* ===================================================================== *)
(* 1. View algebra (untyped)                                             *)
(* ===================================================================== *)

Lemma eta_rename_tApp π d u v :
  eta_rename π d (tApp u v) = tApp (eta_rename π d u) (eta_rename π d v).
Proof. rewrite !eta_rename_rename. reflexivity. Qed.

Lemma eta_rename_mkApps π d t l : eta_rename π d (mkApps t l) = mkApps (eta_rename π d t) (map (eta_rename π d) l).
Proof.
  induction l as [|a l IH] in t |- *; [reflexivity|].
  cbn [mkApps map]. rewrite IH eta_rename_tApp. reflexivity.
Qed.

Lemma zipp_eta_decompose t π :
  zipp_eta t π = mkApps (eta_rename (decompose_stack π).2 0 (zipp t π)) (eta_virtuals (eta_run (decompose_stack π).2)).
Proof.
  unfold zipp_eta, zipp, decompose_stack_eta.
  destruct (decompose_stack π) as [args ρ] eqn:e. cbn [fst snd].
  apply decompose_stack_eq in e. subst π.
  rewrite eta_rename_appstack mkApps_app eta_rename_mkApps. reflexivity.
Qed.

(* the real side after reduction: π' := appstack args ρ, ρ := (decompose_stack π).2 *)
Lemma decompose_stack_eta_appstack_snd args π :
  decompose_stack_eta (appstack args (decompose_stack π).2) =
  (map (eta_rename (decompose_stack π).2 0) args ++ eta_virtuals (eta_run (decompose_stack π).2), drop_eta_run (decompose_stack π).2).
Proof.
  apply decompose_stack_eta_eq.
  rewrite decompose_stack_appstack decompose_stack_snd_idem. cbn [fst snd].
  rewrite app_nil_r. reflexivity.
Qed.

Lemma zipp_eta_appstack_snd t args π :
  zipp_eta t (appstack args (decompose_stack π).2) =
  mkApps (eta_rename (decompose_stack π).2 0 (mkApps t args)) (eta_virtuals (eta_run (decompose_stack π).2)).
Proof.
  unfold zipp_eta. rewrite eta_rename_appstack decompose_stack_eta_appstack_snd. cbn [fst].
  rewrite mkApps_app eta_rename_mkApps. reflexivity.
Qed.

(* The head shapes that are weak-head normal only bare (no argument, no virtual). *)
Definition rigid_head (t : term) : bool :=
  match t with tLambda _ _ _ | tProd _ _ _ | tSort _ | tPrim _ => true | _ => false end.

Lemma eta_rename_isLambda π d t : isLambda (eta_rename π d t) = isLambda t.
Proof. rewrite eta_rename_rename. destruct t; reflexivity. Qed.

Lemma eta_rename_rigid_head π d t : rigid_head (eta_rename π d t) = rigid_head t.
Proof. rewrite eta_rename_rename. destruct t; reflexivity. Qed.

Lemma eta_rename_isApp π d t : isApp (eta_rename π d t) = isApp t.
Proof. rewrite eta_rename_rename. destruct t; reflexivity. Qed.

(* A term that every lift fixes (a closed term) is fixed by every [eta_rename]. *)
Lemma eta_rename_lift_closed π d t :
  (forall n k, lift n k t = t) -> eta_rename π d t = t.
Proof.
  intros hl. induction π as [|se π IH] in d |- *; [reflexivity|].
  destruct (is_eta_frame se) eqn:he.
  - destruct se; try discriminate he.
    + rewrite eta_rename_Eta_app hl. apply IH.
    + reflexivity.
  - rewrite (eta_rename_real _ _ _ _ he). apply IH.
Qed.

(* ===================================================================== *)
(* 2. whnf and the virtual tail (untyped; RedFlags.nodelta)              *)
(* ===================================================================== *)

(* the runtime check EtaConv adds in _isconv_red (G2b): a rigid head may carry no pending η run *)
Definition eta_head_ok (t : term) (ρ : stack) : bool := Nat.eqb (eta_run ρ) 0 || negb (rigid_head t).

(* A term that is not an application is a [mkApps] only with no argument. *)
Lemma mkApps_eq_notApp t hd args : t = mkApps hd args -> isApp t = false -> args = [] /\ hd = t.
Proof.
  destruct args as [|a args _] using rev_ind; intros e ht.
  - split; [reflexivity | exact (eq_sym e)].
  - rewrite mkApps_app in e. subst t. cbn in ht. discriminate ht.
Qed.

Lemma rigid_head_mkApps t l : rigid_head (mkApps t l) = true -> l = [] /\ rigid_head t = true.
Proof.
  destruct l as [|a l _] using rev_ind.
  - intros h. split; [reflexivity | exact h].
  - rewrite mkApps_app. cbn. intros h. discriminate h.
Qed.

(* Under nodelta ([beta = true]) no neutral has a rigid head. *)
Lemma whne_nodelta_not_rigid (Σ : global_env) Γ t :
  whne RedFlags.nodelta Σ Γ t -> rigid_head t = true -> False.
Proof.
  intros w. destruct w; intros hr.
  all: first
    [ cbn in hr; discriminate hr
    | apply rigid_head_mkApps in hr as [_ hr]; cbn in hr; discriminate hr
    | match goal with e : RedFlags.beta RedFlags.nodelta = false |- _ => cbn in e; discriminate e end ].
Qed.

(* A rigid head is weak-head normal only without arguments. *)
Lemma whnf_rigid_mkApps_nil (Σ : global_env) Γ h l :
  rigid_head h = true -> whnf RedFlags.nodelta Σ Γ (mkApps h l) -> l = [].
Proof.
  intros hr hw.
  assert (ha : isApp h = false) by (destruct h; first [reflexivity | discriminate hr]).
  remember (mkApps h l) as T eqn:eT.
  revert eT. destruct hw; intros eT.
  all: first
    [ (* a bare shape: tSort, tProd, tLambda, tPrim *)
      exact (proj1 (mkApps_eq_notApp _ _ _ eT eq_refl))
    | (* an application spine of another head *)
      exfalso; apply mkApps_eq_inj in eT as [eh _];
      [ subst h; discriminate hr | reflexivity | rewrite ha; reflexivity ]
    | (* a neutral *)
      exfalso;
      match goal with w : whne _ _ _ _ |- _ =>
        rewrite eT in w; apply whne_mkApps_inv in w; [|rewrite ha; reflexivity];
        destruct w as [[w | (? & ? & ? & ? & -> & _)] | (? & ? & ? & ? & -> & _)];
        [ exact (whne_nodelta_not_rigid _ _ _ w hr) | discriminate hr | discriminate hr ]
      end ].
Qed.

(* A fixpoint whose recursive argument the appended virtuals supply is stuck on a variable
   without body: neutral. Otherwise it stays unsaturated. *)
Lemma whnf_fixapp_eta_virtuals (Σ : global_env) Γ mfix idx v m :
  (forall k, k < m -> option_map decl_body (nth_error Γ k) = Some None) ->
  (exists d, nth_error mfix idx = Some d /\ nth_error v (rarg d) = None) \/ nth_error mfix idx = None ->
  whnf RedFlags.nodelta Σ Γ (mkApps (tFix mfix idx) (v ++ eta_virtuals m)).
Proof.
  (* the goal is in Type: case on the computational [nth_error], read the Prop premise
     only inside Prop sub-goals *)
  intros hΓ hfix.
  destruct (nth_error mfix idx) as [d|] eqn:hd; [| apply whnf_fixapp; right; exact hd].
  assert (hn : nth_error v (rarg d) = None).
  { destruct hfix as [[d' [hd' hn]] | hn]; [| congruence].
    assert (d' = d) as -> by congruence. exact hn. }
  destruct (nth_error (v ++ eta_virtuals m) (rarg d)) as [a|] eqn:hn'.
  - pose proof hn' as hnth.
    apply nth_error_None in hn.
    rewrite (nth_error_app_ge _ _ _ hn) in hn'.
    pose proof (nth_error_Some_length hn') as hlt. rewrite eta_virtuals_length in hlt.
    rewrite (virtual_focus_nth _ _ hlt) in hn'. injection hn' as ha. subst a.
    apply whnf_ne. eapply whne_fixapp; [exact hd | exact hnth |].
    unfold virtual_focus. apply whne_rel. apply hΓ. lia.
  - apply whnf_fixapp. left. exists d. split; [exact hd | exact hn'].
Qed.

Lemma whnf_mkApps_eta_virtuals {cf} (Σ : global_env) Γ hd args m :
  whnf RedFlags.nodelta Σ Γ (mkApps hd args) -> isApp hd = false ->
  (forall k, k < m -> option_map decl_body (nth_error Γ k) = Some None) ->
  (m = 0 \/ rigid_head hd = false) ->
  whnf RedFlags.nodelta Σ Γ (mkApps (mkApps hd args) (eta_virtuals m)).
Proof.
  intros hw ha hΓ hm.
  (* the goal is in Type: case on the boolean, read the Prop premise in a Prop sub-goal *)
  destruct (rigid_head hd) eqn:hr.
  { assert (hm0 : m = 0) by (destruct hm as [hm|hm]; [exact hm | congruence]).
    subst m. exact hw. }
  remember (mkApps hd args) as T eqn:eT.
  revert eT. destruct hw; intros eT.
  all: first
    [ (* a neutral stays neutral *)
      apply whnf_mkApps; assumption
    | (* a bare rigid shape: excluded by [hr] *)
      exfalso; destruct (mkApps_eq_notApp _ _ _ eT eq_refl) as [_ eh]; subst hd; discriminate hr
    | (* a constant head is neutral under nodelta *)
      apply whnf_mkApps; apply whne_mkApps; apply whne_const_nodelta; reflexivity
    | rewrite -mkApps_app;
      first [ apply whnf_cstrapp | apply whnf_indapp | apply whnf_cofixapp
            | apply whnf_fixapp_eta_virtuals; assumption ] ].
Qed.

(* a rigid head is whnf only bare: no spine and no pending virtual argument *)
Lemma whnf_zipp_eta_rigid {cf} (Σ : global_env) Γ t π :
  whnf RedFlags.nodelta Σ Γ (zipp_eta t π) -> rigid_head t = true ->
  (decompose_stack π).1 = [] /\ eta_run (decompose_stack π).2 = 0.
Proof.
  intros hw hr. unfold zipp_eta, decompose_stack_eta in hw.
  destruct (decompose_stack π) as [args ρ] eqn:e. cbn [fst snd] in hw |- *.
  assert (hr' : rigid_head (eta_rename π 0 t) = true) by (rewrite eta_rename_rigid_head; exact hr).
  pose proof (whnf_rigid_mkApps_nil Σ Γ _ _ hr' hw) as hnil.
  apply app_eq_nil in hnil as [h1 h2].
  split.
  - destruct args as [|a args]; [reflexivity | cbn in h1; discriminate h1].
  - apply (f_equal (@List.length term)) in h2. rewrite eta_virtuals_length in h2. exact h2.
Qed.

(* ===================================================================== *)
(* 3. Typed facts over an abstract well-typedness predicate               *)
(* ===================================================================== *)

(* The η stack version of base [welltyped_context] and the branch count of a well-typed
   [tCase] (plan row T6 for the E instance), and the universes of a typed term (a T-row
   fact; the checker paths may not take a base [wf Σ] premise, so the E [welltyped_wf]
   is this field at [welltypedE]). *)
(* Explicitly [: Prop] (stream lead, 12:20Z): a future Type-valued field is then a compile error,
   not an argument that survives extraction. *)
Class ConvTypedFacts {cf : checker_flags} (wt : global_env_ext -> context -> term -> Prop) (wfP : global_env_ext -> Type) : Prop := {
  ctf_context : forall Σ Γ t π, wfP Σ -> no_Eta_arg π -> wt Σ Γ (zipc t π) -> wt Σ (Γ ,,, stack_context π) t;   (* T6 *)
  ctf_case_brs_length : forall Σ Γ ci p c brs, wfP Σ -> wt Σ Γ (tCase ci p c brs) ->
      exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|;  (* T6 *)
  ctf_wf_universes : forall Σ Γ t, wfP Σ -> wt Σ Γ t -> wf_universes Σ t;   (* T-row: universes of an E-typed term *) }.

(* The base instance shows that the hypotheses [ConvTypedFacts] are consistent and that the
   lemmas over them are about something real. It does NOT discharge the instantiation at
   [welltypedE]/[wf_extE]: that instance needs the typingE facts of plan rows T1 (subject
   reduction over typingE) and T6, which remain hypotheses until those rows land.
   Not a known-false form: no field reads a conversion witness ([conv_witnessE]) or a
   fixpoint/cofixpoint head shape, so the closed-only witness refutation (a [dtype] that is
   η-convertible to [Π (x : tInd I u). B] but keeps a λ in every reduct) does not apply.
   At [welltypedE] the fields are the typingE forms of the base proofs below:
   [ctf_case_brs_length] inverts [typeE_Case], whose [case_branch_typing] is an [All2i] over
   [ind_ctors]; [ctf_context] is subterm typing, which base proves by inversion, validity
   and context conversion, whose typingE forms are the T1/T6 facts named above;
   [ctf_wf_universes] is base [typing_wf_universes] ([PCUICWfUniverses.wf_types], an
   induction on the derivation), whose [type_Cumul] case uses only the induction hypotheses
   of the two typing premises (the preamble's [auto] closes it), never the conversion. *)
#[export] Instance conv_typed_facts_base {cf} : ConvTypedFacts welltyped wf_ext.
Proof.
  constructor.
  - intros Σ Γ t π wfΣ hna h.
    exact (PCUICPositionEta.welltyped_context Σ (wf_ext_wf Σ wfΣ) Γ (t, π) hna h).
  - intros Σ Γ ci p c brs wfΣ [T typ].
    apply (inversion_Case Σ (wf_ext_wf Σ wfΣ)) in typ as (mdecl & idecl & decli & indices & [] & _).
    exists mdecl, idecl. split; [exact decli|].
    apply All2i_length in brs_ty. lia.
  - intros Σ Γ t wfΣ [T typ].
    pose proof (typing_wf_universes (wf_ext_wf Σ wfΣ) typ) as h.
    apply andb_prop in h as [h _]. exact h.
Qed.

(* The GENUINE part of [ConvTypedFacts] at [wt := welltypedE], [wfP := wf_extE]: its field
   [ctf_contextE] is [ctf_context] above with [wt] replaced by [welltypedE] and [wfP] by
   [wf_extE], nothing else changed. The two other fields are proved at that instantiation
   ([PCUICEtaTypedFactsProved.ctf_case_brs_length_proved], [ctf_wf_universes_proved]);
   [PCUICSafeConversionEta.conv_typed_facts_E] builds [ConvTypedFacts welltypedE wf_extE] from
   an instance of this class and those two lemmas (the kernel checking that construction checks
   [ctf_contextE] against [ctf_context] at [welltypedE]). It is the named hypothesis
   [conv_factsE] of [PCUICSafeConversionEta]'s section [Conversion]. Explicitly [: Prop].
   Satisfying instance: [conv_typed_facts_base] proves the same statement at base [welltyped] /
   [wf_ext]; it shows it consistent and does NOT discharge it at [welltypedE] (rows T1/T6). *)
Class ConvTypedFactsE {cf : checker_flags} : Prop := {
  ctf_contextE : forall Σ Γ t π, wf_extE Σ -> no_Eta_arg π -> welltypedE Σ Γ (zipc t π) -> welltypedE Σ (Γ ,,, stack_context π) t;   (* T6 *) }.

Lemma wt_zipc_zipp {cf wt wfP} {CF : ConvTypedFacts wt wfP} Σ Γ t π : wfP Σ -> no_Eta_arg π ->
  wt Σ Γ (zipc t π) -> wt Σ (Γ ,,, stack_context π) (zipp t π).
Proof.
  intros wfΣ hna h.
  unfold zipp. destruct (decompose_stack π) as [args ρ] eqn:e.
  apply decompose_stack_eq in e. subst π.
  rewrite no_Eta_arg_appstack in hna. rewrite zipc_appstack in h. rewrite stack_context_appstack.
  exact (ctf_context Σ Γ (mkApps t args) ρ wfΣ hna h).
Qed.

Lemma wt_zipc_stack_context {cf wt wfP} {CF : ConvTypedFacts wt wfP} Σ Γ t π ρ args : wfP Σ -> no_Eta_arg π ->
  decompose_stack π = (args, ρ) -> wt Σ Γ (zipc t π) -> wt Σ (Γ ,,, stack_context π) (mkApps t args).
Proof.
  intros wfΣ hna e h.
  apply decompose_stack_eq in e. subst π.
  rewrite no_Eta_arg_appstack in hna. rewrite zipc_appstack in h. rewrite stack_context_appstack.
  exact (ctf_context Σ Γ (mkApps t args) ρ wfΣ hna h).
Qed.

(* ===================================================================== *)
(* 4. Facts at welltypedE that need no hypothesis                         *)
(* ===================================================================== *)

(* the η companion (plan I7 rev 10/13): a virtual focus is a declared assumption of the η context *)
Lemma welltypedE_tRel_vass {cf} Σ Γ n decl : wf_localE Σ Γ -> nth_error Γ n = Some decl -> welltypedE Σ Γ (tRel n).
Proof.
  intros wfΓ hn. econstructor. eapply typeE_Rel; eassumption.
Qed.

Lemma whnf_tRel_vass {cf} fl Σ Γ n decl : nth_error Γ n = Some decl -> decl_body decl = None -> whnf fl Σ Γ (tRel n).
Proof.
  intros hn hb. apply whnf_ne. apply whne_rel. rewrite hn. cbn. rewrite hb. reflexivity.
Qed.

(* ===================================================================== *)
(* 5. Reduction under the η stack: the E counterparts of                 *)
(*    PCUICReduction.red1_context / red_context_zip and                  *)
(*    PCUICSafeLemmata.cored_context (base stack). Every frame but       *)
(*    Eta_arg passes a one-step reduct of the focus to the whole term     *)
(*    (Eta_app is transparent); Eta_arg drops the focus, so the [red]    *)
(*    version holds for every stack and the [red1]/[cored] versions need *)
(*    [no_Eta_arg].                                                      *)
(* ===================================================================== *)

Section EtaStackRed.
  Context {cf : checker_flags} (Σ : global_env_ext).

  Lemma red1_context_eta Γ t u π : no_Eta_arg π ->
    red1 Σ (Γ ,,, stack_context π) t u -> red1 Σ Γ (zipc t π) (zipc u π).
  Proof.
    revert t u. induction π as [|a π IHπ]; intros u v hna h; [exact h|].
    cbn [no_Eta_arg] in hna. apply andb_prop in hna as [ha hna].
    simpl in *.
    destruct a; cbn [is_Eta_arg negb] in ha; try discriminate ha.
    all: apply IHπ; [exact hna|]; simpl; pcuic.
    - destruct mfix as ((?&[])&?); cbn in *;
        [apply fix_red_ty|apply fix_red_body].
      all: apply OnOne2_app; constructor; cbn; auto.
      intuition auto.
      rewrite fix_context_fix_context_alt map_app.
      unfold def_sig at 2.
      cbn.
      rewrite -app_context_assoc; auto.
    - destruct mfix as ((?&[])&?); cbn in *;
        [apply cofix_red_ty|apply cofix_red_body].
      all: apply OnOne2_app; constructor; cbn; auto.
      intuition auto.
      rewrite fix_context_fix_context_alt map_app.
      unfold def_sig at 2.
      cbn.
      rewrite -app_context_assoc; auto.
    - destruct p; cbn in *.
      + apply case_red_param; cbn.
        apply OnOne2_app.
        constructor; auto.
      + apply case_red_return; cbn.
        rewrite -app_assoc in h; auto.
    - destruct brs as ((?&[])&?); cbn in *.
      + apply case_red_brs.
        apply OnOne2_app.
        constructor; cbn.
        rewrite -app_assoc in h; auto.
    - now apply array_red_type; cbn in *.
    - now apply array_red_def; cbn in *.
    - apply array_red_val; cbn in *.
      eapply OnOne2_app. now constructor.
  Qed.

  Lemma red_context_zip_eta Γ t u π :
    red Σ (Γ ,,, stack_context π) t u -> red Σ Γ (zipc t π) (zipc u π).
  Proof.
    revert t u. induction π as [|a π IHπ]; intros u v h; [exact h|].
    cbn [zipc].
    destruct (is_Eta_arg a) eqn:ha.
    - destruct a; try discriminate ha. cbn [fill_hole]. reflexivity.
    - apply IHπ.
      have e : Γ ,,, stack_context (a :: π) = (Γ ,,, stack_context π) ,,, stack_context [a].
      { rewrite /app_context /stack_context /=. now rewrite app_nil_r app_assoc. }
      have h1 : forall x y, red1 Σ (Γ ,,, stack_context (a :: π)) x y ->
          red1 Σ (Γ ,,, stack_context π) (fill_hole x a) (fill_hole y a).
      { intros x y r. rewrite e in r.
        exact (red1_context_eta (Γ ,,, stack_context π) x y [a]
                 (ltac:(cbn; rewrite ha; reflexivity)) r). }
      rst_induction h; eauto using h1.
  Qed.

  Lemma cored_context_eta Γ t u π : no_Eta_arg π ->
    cored Σ (Γ ,,, stack_context π) t u -> cored Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros hna h. induction h.
    - constructor. now apply red1_context_eta.
    - eapply cored_trans.
      + exact IHh.
      + now apply red1_context_eta.
  Qed.
End EtaStackRed.
