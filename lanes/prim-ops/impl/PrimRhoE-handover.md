# PrimRhoE handover

Captured 2026-10-27T17:30:30Z. Task: [BET-319](dispatch://BET-319), row E, primitive-operation parallel reduction/confluence. Parent: `PrimSpec2`; lane lead: `ArityLane`.

## Why this handover exists

PrimSpec2 explicitly stopped this agent for model-governance reasons and is re-dispatching the identical task to a default-model agent. This is **not a completed implementation**. No commit or push. All edits are saved in the shared worktree. Apart from this parent-requested handover, this agent edited only:

- `pcuic/theories/PCUICParallelReduction.v`
- `pcuic/theories/PCUICParallelReductionConfluence.v`

Machine-local worktree: `/mnt/nvme/sami/tmp/prim-ops-DE`, branch supplied by parent: `frac/prim-ops-DE`. It contains the parent's other uncommitted work; do not reset it.

## Clock and checkpoint

Recorded start: `date -u` returned **2026-10-27T17:22:13Z**. Recorded handover clock: **2026-10-27T17:30:30Z**. This recorded window is 497 seconds (8m17s, about 0.138 h); initial brief/skill reading preceded the first recorded clock. Three builds ran in the background while source work continued. There was no deliberate idle wait.

The 10-hour checkpoint has **not been reached**. No GREEN/AMBER/RED verdict has been established: `rho` has not compiled yet because its dependency fails first. No RED/not-yet-literal goal has been observed. No fallback request was made or approved.

Binding brief/design are outside this worktree:

- `/mnt/nvme/sami/frac-verify/bet64-upstream-01a170d9/lanes/prim-ops/impl/HELPERS.md`: no admissions/axioms/weakenings, Azure-only builds, strict file ownership.
- `/mnt/nvme/sami/frac-verify/bet64-upstream-01a170d9/lanes/prim-ops/design-opt1.md`: whole design read; §13 defines checkpoint/fallback. Parent reports its row-12 change log now records the constant inversion correction below.

## Constructor: unchanged from parent's signature

In `PCUICParallelReduction.v:269-276`:

```coq
| pred_prim_op c decl u op ls r v :
  pred1_ctx Γ Γ' ->
  prim_op_of Σ c = Some op ->
  declared_constant Σ c decl ->
  cst_body decl = None ->
  PrimitiveOps.prim_op_denote op ls = Some r ->
  PCUICPrimitiveRed.readback Σ (PrimitiveOps.po_shape (PrimitiveOps.info op)) r = Some v ->
  pred1 Γ Γ' (mkApps (tConst c u) (map PCUICPrimitiveRed.term_of_lit ls)) v
```

No recursive argument term reductions occur in this constructor; source arguments and readback are ground. Context relation is the first premise.

## `pred1_ind_all_ctx`: clause and proof are added

The exact new clause is at `PCUICParallelReduction.v:483-491`, immediately after `pred_rel_refl` and before `pred_iota`:

```coq
(forall Γ Γ' c decl u op ls r v,
    pred1_ctx Γ Γ' ->
    Pctx Γ Γ' ->
    prim_op_of Σ c = Some op ->
    declared_constant Σ c decl ->
    cst_body decl = None ->
    PrimitiveOps.prim_op_denote op ls = Some r ->
    PCUICPrimitiveRed.readback Σ (PrimitiveOps.po_shape (PrimitiveOps.info op)) r = Some v ->
    P Γ Γ' (mkApps (tConst c u) (map PCUICPrimitiveRed.term_of_lit ls)) v) ->
```

Important positional discipline: instead of renumbering every old `Xk`, the scheme proof now explicitly introduces the new clause as **`Hprim`**:

```coq
intros P Pctx Pctxover P' Hctx Hctxover X X0 X1 X2 Hprim. intros.
```

This preserves all old anonymous `X3` onward names, including `X21` used for the recursive derivation. One context bullet was inserted after the `pred_rel_refl` bullet:

```coq
- apply Hctx, (on_contexts_impl a). exact a. intros. apply (aux _ _ _ _ X21).
```

The build has passed this whole scheme, `pred1_pred1_ctx`, and the renaming theorem. This is observed from later compile failures, not a claim that the whole file builds.

### Users threaded in `PCUICParallelReduction.v`

1. `pred1_pred1_ctx` (current ~793): extra `_`; existing automation closes its primitive case.
2. `pred1_rename` (current ~1139): extra `_`; primitive case is removed **before** the existing numbered `12:{...}` and `15:{...}` selections. It uses new `pred1_prim_op_map` (current ~901), with explicit nine-premise discharge. This compiled through the renaming theorem in builds `e-scheme2` and `e-rho1`.
3. `strong_substitutivity` (current ~2059): extra `_`; new case after the rel-refl case, before iota. **This currently fails**; details below.

`pred1_prim_op_map` transports both sides through one term map that fixes ground terms, commutes with `mkApps`, and fixes constants. It is proved and compiled. It works for renaming, but cannot directly handle strong substitution because the two sides use different maps `inst σ` and `inst τ`.

## Latest failure: fix this first

Latest executed command, through the mandated wrapper:

```sh
/mnt/nvme/sami/frac-verify/bet64-upstream-01a170d9/lanes/arity-delta/m.sh '/mnt/frac/work/prim-ops/spec-e-build.sh e-rho1 pcuic -- theories/PCUICParallelReduction.vo theories/PCUICParallelReductionConfluence.vo' </dev/null
```

Exact Azure log: **`/mnt/frac/work/prim-ops/out/spec-e-e-rho1.log`**.

Its own final lines:

```text
make: *** [Makefile.rocq:815: theories/PCUICParallelReduction.vo] Error 1
make: *** [theories/PCUICParallelReduction.vo] Deleting file 'theories/PCUICParallelReduction.glob'
make: Target 'theories/PCUICParallelReductionConfluence.vo' not remade because of errors.
STATUS pcuic 2
EXIT 0
```

`EXIT 0` is the wrapper/container shell exit, **not** a green target. The relevant status is `STATUS pcuic 2`.

Failure at `PCUICParallelReduction.v:2136`, `eapply pred_prim_op`:

```text
Unable to unify "PrimitiveOps.prim_op_denote ?op ?ls = Some ?r" with "term".
```

Relevant context:

```coq
Γ, Γ' : list context_decl
c : kername
decl : constant_body
u : Instance.t
op : PrimitiveOps.prim_op
ls : list PrimitiveOps.prim_lit
r : PrimitiveOps.prim_result
v : term
X, X0 : pred1_ctx Σ Γ Γ'
H : prim_op_of Σ c = Some op
H0 : declared_constant Σ c decl
H1 : cst_body decl = None
H2 : PrimitiveOps.prim_op_denote op ls = Some r
H3 : PCUICPrimitiveRed.readback Σ (PrimitiveOps.po_shape (PrimitiveOps.info op)) r = Some v
P, Q : nat -> bool
Δ, Δ' : context
σ, τ : nat -> term
onis : on_free_vars Q (mkApps (tConst c u) (map PCUICPrimitiveRed.term_of_lit ls)).[σ]
Hrel : pred1_subst P Q Γ Γ' Δ Δ' σ τ
a : on_free_vars P (tConst c u)
b : forallb (on_free_vars P) (map PCUICPrimitiveRed.term_of_lit ls)
hv : v.[τ] = v
```

Current failing case:

```coq
- assert (hv : v.[τ] = v).
  { destruct (prim_ground_readback H3) as [[[] ->]|[? [? ->]]]; reflexivity. }
  rewrite hv inst_mkApps /=.
  rewrite (map_prim_ground (inst σ) ls).
  + eapply pred_prim_op; eauto using pred1_subst_pred1_ctx.
  + intros ? [[[] ->]|[? [? ->]]]; reflexivity.
```

[INFERENCE] The unsupplied proof argument of `map_prim_ground` in that rewrite is creating side goals/evars in an unexpected order. First try supplying the ground-fixing proof **inside** the lemma application, or assert a fully typed map equality before rewriting it. Then apply `pred_prim_op` with all premises explicit if needed. Do not retry the one-map transport helper directly: `e-scheme2` correctly failed with `Unable to unify "inst τ" with "inst σ"`.

Earlier build records:

- `e-scheme1`, `/mnt/frac/work/prim-ops/out/spec-e-e-scheme1.log`: `STATUS pcuic 2`, renaming numbered case shift because primitive transport automation did not close. Fixed by explicit premise branches instead of `eauto` before a fixed-size tactic bracket.
- `e-scheme2`, `/mnt/frac/work/prim-ops/out/spec-e-e-scheme2.log`: `STATUS pcuic 2`, direct one-map helper in strong substitution mismatched σ/τ. Replaced with the current separate ground rewrites.

No target has a STATUS 0 yet. No `Print Assumptions` check was run. No admission, axiom, or unapproved statement change was added by this agent.

## `rho` work: saved but not compiled

`PCUICParallelReductionConfluence.v` now imports `PrimitiveOps` and `PCUICPrimitiveRed` explicitly. New definitions/lemmas near the start of `Section Rho` (~352-448):

- `rho_prim_app : term -> option term`: decomposes the **original** application, checks a constant head, `lookup_env` returning a constant declaration, `prim_op_of`, literal traversal `map_option_out (map lit_of_term args)`, bodilessness, denotation, and readback. It fires only exact saturation, because denotation rejects other arities.
- `literals_readback` and `rho_prim_app_redex`.
- `literals_readback_inv`, `rho_prim_app_inv`, `lit_of_term_rename`, `rho_prim_app_rename`, `rho_prim_app_construct`, `rho_prim_app_cofix`.

**Design choice made by this agent, not a user approval:** rather than modify `PCUICViews.v` (outside ownership) or replace its entire view type, the existing `fix_lambda_app_other` arm is refined by an inner primitive recognition match:

```coq
| fix_lambda_app_other t u nisfixlam :=
  match rho_prim_app (tApp t u) with
  | Some v => v
  | None => tApp (rho Γ t) (rho Γ u)
  end
```

Thus `view_lambda_fix_app` itself still has its original three constructors. There is a primitive computation arm inside its non-lambda/non-fix arm, **not a new constructor of the original view type**. This was chosen to keep old lambda/fix behavior and equation numbering stable while recognizing the required redex. Its proofs are unverified; the new agent should assess it against the task's view-extension requirement, not assume that requirement has been discharged.

Also saved, not compiled:

- `rho_prim_ground` after rho's notations (~801).
- Adaptations of `rho_app_construct`/`rho_app_cofix` to show the recognizer returns None.
- Adaptation of the ordinary-application branch of `rho_rename` (~1837), using recognizer invariance and ground readback.
- `pred1_on_free_vars` induction gets `all:try solve [prim_ground_reduct; reflexivity]`.
- `triangle_gen`'s explicit `pred1_ind_all_ctx` application gets one more `_`.

**Not implemented yet:** the primitive equality lemma for `rho` itself, the primitive triangle case, and the new branch of the application congruence triangle. The original inversions in the first 300 lines also still need to be compiled and repaired for the new constructor.

### Sync freshness

`e-rho1` included the recognizer, `literals_readback`, `rho_prim_app_redex`, and the initial rho arm, but the latest helper additions (`literals_readback_inv` onward), `rho_prim_ground`, and rename/construct/cofix proof adaptations were saved **after** that build's sync. They exist in the shared worktree, not yet in `trees/spec-e`. Re-sync before building them.

## Authorized constant-inversion correction

Live-source finding: `pred1_mkApps_tConst_axiom` assumed only a declared constant with `cst_body=None`. That is false after adding the rule: a registered bodiless `Stringlength` applied to a string literal reduces to an integer literal, not a constant-headed application.

ArityLane authorized the exact new premise:

```coq
prim_op_of Σ cst = None ->
```

It is saved between `cst_body cb = None ->` and the `pred1` premise (~189). **The proof is not repaired yet.** Its additional hypothesis also shifts anonymous equality names in its positional proof. The new primitive case must be excluded by non-registration after extracting the head equality.

Binding condition from ArityLane: every caller supplies non-registration or explicitly handles the operation case. Parent reports:

- `PCUICConfluence.v:3925` `red_mkApps_tConst_axiom` has the same new premise.
- Its `pred1_mkApps_tConst_axiom` call near :3938 and both induction-hypothesis uses supply that premise.
- `safechecker/PCUICSafeConversion.v:39` `closed_red_mkApps_tConst_axiom`, used near :1647-1648, is row J's responsibility; registered-but-stuck operations belong to row J's separate rigidity lemma.
- Parent recorded the finding/fix/call chain in design change-log row 12.

These parent reports were received directly in this session; this agent did not edit their files or recheck their current contents.

## Suggested continuation after the first failure

These are unproved implementation directions, not measured results:

1. Finish `PCUICParallelReduction.v` by fixing the exact strong-substitution rewrite above, then rebuild both targets.
2. Repair the early `pred1` inversions (including the authorized constant inversion), using constant-head discrimination for the added constructor. Empty literal operation lists cannot denote a result (destruct the operation or derive arity from `prim_op_denote_args`).
3. Compile the recognizer helpers and rho. Add a lemma saying rho of a registered bodiless saturated literal application is the readback; use `rho_prim_app_redex`, the existing non-lambda/fix view, and a reverse-list split to expose the final `tApp`.
4. The primitive triangle case should then be equality rewriting plus `pred1_refl_gen` on the readback.
5. Application-congruence triangle: for recognizer None, retain the current `pred_app` proof. For Some, `rho_prim_app_inv` says the original source is a saturated literal spine. [INFERENCE] Prove literal `pred1` reducts are identical and prove a strict prefix of a bodiless primitive literal spine cannot fire: any such firing contradicts the fixed arity from `prim_op_denote_args`. Then the intermediate application has the same literal redex and `pred_prim_op` closes it. This works on **original literals**; no need for rho to discover not-yet-literal arguments has been observed.

## Build/tool notes

Only Azure `bet64-mem` is allowed for builds. Dedicated tree `/mnt/frac/work/prim-ops/trees/spec-e`, script `/mnt/frac/work/prim-ops/spec-e-build.sh`, containers `prim-spece-<tag>`. Do not touch parent's `trees/spec` or `prim-spec-*` containers.

The parent's full-diff tar sync recipe was used three times, with `TMPDIR=/mnt/nvme/sami/tmp`. It streams directly to Azure; no local tar/log was created. The build script extracts with `tar -m`, so syncing the full diff updates dependency mtimes and rebuilds those dependencies. Each run here was about 94-98 seconds.

`read ssh://sami@10.0.0.26/...` failed because the read tool does not pick up the dedicated key; no SSH capability hosts are configured. Remote logs were read with `m.sh 'cat <exact-log>' </dev/null`, and the resulting tool artifact was searched with the grep tool for `Error:|STATUS pcuic`. The latest local tool artifact is `artifact://3033` (session-local; remote log is the durable reference).

CodeGraph was attempted first; the tool reports `CodeGraph CLI is unavailable on PATH`. Source exploration used read/grep afterward. No interactive proof server was started. All three background builds have completed; there is no running build owned by this agent.
