# C3Prover3 — running log for C3 (Hindley strong commutation of β with one η step, modulo `upto_domain`)

Prover: C3Prover3 (independent, duplicated effort accepted).
Branch: `frac/eta-c3-C3Prover3` from `frac/integ-all2` `56b92b56`.
Worktree: `/mnt/nvme/sami/tmp/eta-c3-C3Prover3`.
Route chosen: **induction on the β-step with `red1_ind_all`, reusing the *structure* of upstream C2's
`red1_eta1_diamond` script with the stronger one-sided conclusion.** (Suggested emphasis was pred1/rho;
after the audit below the direct red1-induction route closes all four unlocking cases cleanly, so I run
that; pred1/rho is kept as a fallback method, §"Fallback".)

Statement (exactly, against the shared `PCUICEtaDefs.v` `eta1`/`upto_domain`, C3Prover1's file —
I do NOT retype the definitions, per the lane lead 16:14Z):
```
C3 : red1 Σ Γ t v -> eta1 t u ->
     ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
```
Diamond (β below, η on top of `t`):
```
        t
     β /   \ η
      v      u
   η* |      | clos_refl (≤1) β
      w' ~~~ w     (upto_domain)
```
Mapping to upstream C2 `red1_eta1_diamond {Σ Γ t u v} : red1 t u -> eta1 t v -> ∑ u' v', beta_eta u u'
× beta_eta v v' × upto_domain u' v'`:  **C3's `u` = C2's `v` (η-reduct); C3's `v` = C2's `u`
(β-reduct).** C3 strengthens C2 by forbidding β on the β-reduct side (`clos_refl_trans eta1`, η-only)
and bounding the η-reduct side to `clos_refl (red1)` (≤1 β).

---

## Build-free audit of the four unlocking cases (`red_fix`, `red_cofix_case`, `red_cofix_proj`, `red_proj`)

Method: read upstream C2's script `origin/eta_postpo:pcuic/theories/PCUICEtaReduction.v:1475-2198`
(local copy `/tmp/c3_etaredux_postpo.v`), and for every join C2 produces in these four cases, record
**which side gets β and which gets η**, then check it fits C3's one-sided shape. The gate's worry is
"any case where C2's script uses β on the η side is a C3 counterexample candidate." Result: **none of
the four unlocking cases uses β on the β-reduct side; the only β is one re-fire on the η-reduct side.**

Why the postponement counterexample does NOT bite C3: the counterexample
`t := tApp (tFix [λx:B. tRel 0] 0) (λ_:A. (tConstruct ind 0 ui (lift0 1 a)) (tRel 0))`
(`plan-gate.md` B3(a)) is about η *creating* a redex (η-reduct fires a fixpoint the original could
not). In C3 we induct on the β-step of `t`, so the β-redex **pre-exists on `t`**; the η-step can only
be orthogonal to it or inside its head defs, never create it. "A redex created by η appears only on
the η side, which it need not match" — exactly C3's asymmetry.

### Case `red_fix`  (C2 `/tmp/c3_etaredux_postpo.v:1508-1565`)
`t = mkApps (tFix mfix idx) args`, `unfold_fix mfix idx = Some(narg,fn)`, `is_constructor narg args`,
`v = mkApps fn args`. Outer term is a `tApp` (args non-empty — `is_constructor narg []` is false), so
`t` is not a top-level `eta_redex`. `eta1 t u` splits by `eta1_mkApps_inv` (`:1223-1234`):

- **(b) η in an argument** `args → args'` (OnOne2, one arg `a_j → a_j'`):
  `u = mkApps (tFix mfix idx) args'`. `is_constructor narg args'` still holds — if `j = narg` then
  `a_narg` is constructor-headed (`is_constructor` true on `t`), hence NOT a top `eta_redex`
  (`eta_redex` is a `tLambda`), so the η is a congruence deeper inside `a_narg` and preserves the
  constructor head (C2 proves this at `:1558-1565`, `isConstruct_app_App`). So `u` re-fires `red_fix`
  in **one** step → `w = mkApps fn args'`.  On the β-reduct side `v = mkApps fn args → η w' = mkApps
  fn args'` by one app-congruence η step. `w = w'`.  ⇒ η-side `clos_refl red1` = 1 step; β-side
  `clos_refl_trans eta1` = 1 step.  ✔ (C2: `pretac (mkApps fn l')`, `:1556`.)

- **(a) η in the head `tFix`** `eta1 (tFix mfix idx)(tFix mfix' idx)` (fix_eta_ty or fix_eta_body;
  no `eta_red`, `tFix ≠ tLambda`): `u = mkApps (tFix mfix' idx) args`. `rarg` is preserved by `eta1`
  on `mfix` (the OnOne2 keeps `(dname,dbody/dtype,rarg)`), so `unfold_fix mfix' idx = Some(narg,fn')`
  with `fn' = subst0 (fix_subst mfix')(dbody d')`; `is_constructor narg args` unchanged ⇒ `u` re-fires
  `red_fix` in **one** step → `w = mkApps fn' args`.  On the β-reduct side we need
  `v = mkApps fn args →η* w' = mkApps fn' args`, i.e.
  `subst0 (fix_subst mfix)(dbody d) →η* subst0 (fix_subst mfix')(dbody d')`.  The single η step in
  `mfix` gives (i) `eta1 (tFix mfix j)(tFix mfix' j)` for **every** `j` (same OnOne2 witness, different
  idx) ⇒ `All2 (clos_refl_trans eta1)(fix_subst mfix)(fix_subst mfix')`; and (ii) `dbody d →η? dbody
  d'` (one η if the change is in def idx's body, else equal). Closing `subst0` under η in both the
  list and the body gives η*.  `w = w'`.  ✔
  **In C2 this is `subst_beta_eta`/`beta_eta_subst0` applied to `eta1` steps only — NO β on this side**
  (`:1519-1555`; the `beta_eta` there is `union red1 eta1` instantiated at the η injection).

### Case `red_cofix_case`  (C2 `:1567-1618`)
`t = tCase ip p (mkApps (tCoFix mfix idx) args) brs`, `unfold_cofix mfix idx = Some(narg,fn)`,
`v = tCase ip p (mkApps fn args) brs`. `eta1 t u` inverts to a case congruence:
- η in the predicate (pparams/preturn) or a branch body: discriminee unchanged ⇒ `u` re-fires
  `red_cofix_case` in one step → `w =` (unfolded cofix, η'd predicate/branch); `v → η w' = w`
  (replay the same predicate/branch η step). ✔ orthogonal.
- η in the discriminee `mkApps (tCoFix mfix idx) args`: `eta1_mkApps_inv` → head (cofix_eta_ty/body,
  giving `mfix'`, `unfold_cofix mfix' idx = Some(narg,fn')`) or an arg. Same two shapes as `red_fix`,
  with `cofix_subst` in place of `fix_subst` (C2 `:1572-1617`). η-side = one `red_cofix_case` re-fire;
  β-side = η* via `subst0`-congruence of the single η step. ✔ no β on the β-reduct side.

### Case `red_cofix_proj`  (C2 `:1621-1670`)
`t = tProj p (mkApps (tCoFix mfix idx) args)`. `eta1 t u` is a `proj` congruence into the discriminee
only ⇒ `eta1_mkApps_inv` → head or arg, identical to `red_cofix_case`'s discriminee sub-case. ✔

### Case `red_proj`  (C2 `:1672-1678`)
`t = tProj p (mkApps (tConstruct ind 0 u) args)`, `v = arg_sel` (the `proj_npars+proj_arg`-th arg).
`eta1 t u` is `proj` congruence → `eta1_mkApps_inv`; head case is `eta1 (tConstruct …) M'` which is
impossible (`tConstruct` has no `eta1` step), so **only** the arg case: `args → args'`,
`u = tProj p (mkApps (tConstruct ind 0 u) args')`, re-fires `red_proj` in one step →
`w = args'_sel`.  If `j = sel`: `v = arg_sel = arg_j → η arg_j' = w' = w`. If `j ≠ sel`:
`w = arg_sel = v`, β-side 0 η steps. ✔  (C2: `OnOne2_nth_error`, `tac v'`, `:1676-1678`.)

### Audit verdict
All four unlocking cases satisfy C3. **No β step ever appears on the β-reduct (`v`) side; it carries
η* only.** The η-reduct (`u`) side needs exactly one `red1` re-fire (`clos_refl`). No counterexample.
This matches `plan.md` §3 C3's INFERENCE "a redex created by η appears only on the η side, which it
need not match", and the fallback note "any case where C2's script uses β on the η side is a
counterexample candidate" finds **no** such case in the four.

---

## Context hypotheses this route will assume (U-rows; discharged by L7 / shared closure file)
Listed with statements; each is a standard η-closure fact (U2/U4, "PROVED 2020 AST"). None is C3 or a
weakening of C3. I will prove them from the shared file's closure lemmas when available; until then
they are `Context` in a `Section`:
- **CH1 (U4 / `eta1_mkApps_inv`)** — may come from shared file:
  `eta1 (mkApps M l) N -> (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l')`.
- **CH2 (U2 subst-in-body)** `clos_refl_trans eta1 t t' -> clos_refl_trans eta1 (subst0 s t)(subst0 s t')`.
- **CH3 (U2 subst-in-list)** `All2 (clos_refl_trans eta1) s s' -> clos_refl_trans eta1 (subst0 s t)(subst0 s' t)`.
- **CH4 (U4 fix_subst congruence)** `eta1 (tFix mfix i)(tFix mfix' i) ->
  All2 (clos_refl_trans eta1)(fix_subst mfix)(fix_subst mfix')` (and the `cofix_subst` twin).
- **CH5 (U4 app/proj/case congruence closure of `clos_refl_trans eta1`)** — lift one-step congruences
  of `eta1` to `clos_refl_trans eta1` (needed to replay the orthogonal η on the β-reduct side under
  `mkApps`, `tCase`, `tProj`).
`red1`-side re-fire uses only base `red1` constructors (`red_fix`/`red_cofix_case`/`red_cofix_proj`/
`red_proj`) — no hypothesis.

## Status
- 2026-10-27: worktree + branch created; build-free audit of the four unlocking cases DONE (above),
  verdict: all four hold, no β on the β-reduct side, no counterexample. Waiting on C3Prover1's shared
  `PCUICEtaDefs.v` (`wip/eta-c3-defs-2026-10-27`) hash to start the mechanised proof; not pushed yet.
- Next: on hash arrival — merge defs, `Require` it, write `PCUICEtaReductionC3.v` with the
  `red1_ind_all` induction; prove the four unlocking cases first, then the ~60 congruences.

## Fallback (pred1/rho), if the red1-induction route stalls on a congruence case
Commute `eta1` with `pred1` (parallel β-reduction, `PCUICParallelReduction.v`), where one `pred1`
step contracts a set of non-overlapping β-redexes and η is a diamond against it; then transfer to
`red1` via `red1 ⊆ pred1 ⊆ red` (`red_pred1`, `pred1_red`) and β-confluence `red_confluence`
(`PCUICConfluence.v:3938`). Kept as method, not a restatement — the landed lemma is still C3 on
`eta1`/`upto_domain`.
