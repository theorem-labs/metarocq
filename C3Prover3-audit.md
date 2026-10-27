# C3Prover3 — running log for C3 (Hindley strong commutation of β with one η step, modulo `upto_domain`)

Prover: C3Prover3 (independent, duplicated effort accepted).
Branch: `frac/eta-c3-C3Prover3` from `frac/integ-all2` `56b92b56`.
Worktree: `/mnt/nvme/sami/tmp/eta-c3-C3Prover3`.
Audit snapshot pushed: fork `wip/c3-C3Prover3-2026-10-27` (commit `30c45f41`, first line marks
"DOES NOT BUILD, audit only").

**Verdict status convention (lane lead 2026-10-27 ask 2):** every case verdict below is marked
**[INFERENCE]** — it is build-free reading of upstream C2's script, "read and believed", NOT yet
mechanised against the shared `eta1`/`upto_domain`. The 11-01 go/no-go distinguishes read-and-believed
from proved; these flip to [PROVED] only when the Rocq file builds.

Route chosen: **induction on the β-step with `red1_ind_all`, reusing the *structure* of upstream C2's
`red1_eta1_diamond` script with the stronger one-sided conclusion.** (Suggested emphasis was pred1/rho;
after the audit the direct red1-induction route closes all four unlocking cases AND the binder critical
pairs cleanly, so I run that; pred1/rho kept as fallback method — see §Fallback.) I do NOT retype the
definitions (lane lead 16:14Z); I `Require` C3Prover1's `PCUICEtaDefs.v` once it lands.

Statement (exactly):
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

## THE orthogonality argument (why postponement's counterexample does not transfer — keep this)

Postponement's counterexample (`plan-gate.md` B3(a),
`t := tApp (tFix [λx:B. tRel 0] 0) (λ_:A. (tConstruct ind 0 ui (lift0 1 a)) (tRel 0))`) is about η
**creating** a redex: the η-reduct fires a fixpoint the original could not. **C3 inducts on the
β-step of `t`, so the β-redex pre-exists on `t`.** The η-step is therefore either orthogonal to that
redex or lies inside its head definitions; it can never be what creates the redex. Hence on the
β-reduct (`v`) side we only ever **replay** the η step (η*), and on the η-reduct (`u`) side we
**re-fire** the same, pre-existing β-redex (≤1 `red1`). "A redex created by η appears only on the η
side, which [C3] need not match." This single fact is why postponement is false but C3 holds, and the
go/no-go rests on it.

---

## Build-free audit — the four unlocking cases  [all INFERENCE]

Evidence = upstream C2 `origin/eta_postpo:pcuic/theories/PCUICEtaReduction.v` (local `/tmp/c3_etaredux_postpo.v`).
For each join I record **which side gets β, which gets η**. Result: **no unlocking case puts β on the
β-reduct (`v`) side; the only β is one re-fire on the η-reduct (`u`) side.**

### `red_fix`  (C2 `:1508-1565`)  [INFERENCE: holds]
`t = mkApps (tFix mfix idx) args`, `is_constructor narg args`, `v = mkApps fn args`. `t` is a `tApp`
(args non-empty), not a top `eta_redex`. `eta1 t u` splits by `eta1_mkApps_inv`:
- η in an arg `args → args'`: `is_constructor narg args'` preserved (if `j=narg`, `a_narg` is
  constructor-headed so η is a congruence deeper in, not a top `eta_redex`; C2 `:1558-1565`,
  `isConstruct_app_App`). `u` re-fires `red_fix` → `w = mkApps fn args'` (1 β). `v = mkApps fn args →η
  w' = mkApps fn args'` (1 η). `w=w'`. ✔
- η in head `tFix` (fix_eta_ty/body; no `eta_red`): `rarg` preserved, `unfold_fix mfix' idx =
  Some(narg,fn')`, `u` re-fires `red_fix` → `w = mkApps fn' args` (1 β). β-side: `subst0 (fix_subst
  mfix)(dbody d) →η* subst0 (fix_subst mfix')(dbody d')` — single η in `mfix` gives
  `All2 η (fix_subst mfix)(fix_subst mfix')` and `dbody d →η? dbody d'`, closed under `subst0`. `w=w'`.
  ✔  In C2 this is `subst_beta_eta`/`beta_eta_subst0` applied to **eta1 steps only** — no β on the v
  side (`:1519-1555`).

### `red_cofix_case` (`:1567-1618`) / `red_cofix_proj` (`:1621-1670`)  [INFERENCE: holds]
`cofix_subst` twin of `red_fix`. Predicate (pparams/preturn) or branch-body η is **orthogonal**
(discriminee unchanged) → re-fire + replay. Discriminee η → `eta1_mkApps_inv` → head (cofix_eta_ty/
body, `unfold_cofix mfix' = Some(narg,fn')`) or arg, identical to `red_fix`. ✔

### `red_proj`  (C2 `:1672-1678`)  [INFERENCE: holds]
`t = tProj p (mkApps (tConstruct ind 0 u) args)`, `v = arg_sel`. η is `proj` congruence →
`eta1_mkApps_inv`; head case `eta1 (tConstruct …) _` is impossible (no `eta1` step on `tConstruct`),
so **only** the arg case → re-fire `red_proj` → `w = args'_sel` (1 β); `v = arg_sel →η≤1 w'`. ✔

---

## Build-free audit — the binder β/η critical pairs (the real danger zone)  [all INFERENCE]

The "redex created/destroyed by η at a binder" cases are where a C3 counterexample, if any, would
hide. Audited; **all close for C3 with no β on the `v` side.**

### `red_beta`  (C2 `:1476-1483`)  [INFERENCE: holds — the critical pair is benign]
`t = tApp (tLambda na A b) a`, `v = b{0:=a}`. `eta1 t u`:
- **`eta_red` at the λ** (`b = tApp (lift0 1 s)(tRel 0)`, `u = tApp s a`): `v = b{0:=a} = tApp
  ((lift0 1 s){0:=a})(a) = tApp s a = u` (by `simpl_subst`, `lift0_id`). **β-reduct = η-reduct**;
  join with 0 steps. ✔  (C2 `:1477`.)  — this is the famous β/η critical pair; trivial for C3.
- η in domain `A→A'`: `u →β v` (β ignores domain) — 1 β on u, 0 η on v. ✔
- η in body `b→b'`: `u →β b'{0:=a}`; `v = b{0:=a} →η b'{0:=a}` (`eta_subst`, η-only). ✔
- η in arg `a→a'`: `u →β b{0:=a'}`; `v = b{0:=a} →η b{0:=a'}` (`subst_eta`, η-only). ✔

### `abs_red_l` (β in λ-domain)  (C2 `:1679-1683`)  [INFERENCE: holds]
Congruence; η in domain/body uses IH; η=eta_red degenerate. One step each side, modulo domain. ✔

### `abs_red_r` (β in λ-body — β exposing a fix/β-redex UNDER an η-binder)  (C2 `:1685-1725`)  [INFERENCE: holds — deepest case]
`t = tLambda na N M`, `red1 (Γ,,vass na N) M M'`, `v = tLambda na N M'`. `eta1 t u`:
- **`eta_red`** (`M = tApp (lift0 1 s)(tRel 0)`, `u = s`): β fires inside the η-redex body. Sub-cases
  of the body β-step:
  - β in `lift0 1 s` (s itself β-steps): C2 `red1_strengthening` (`:1718`) gives `s →β s0` under `Γ`
    (1 red1 on `u=s`); `v = eta_redex na N s0 →η s0` (1 `eta_red`). `w=w'=s0`. ✔
  - whole `tApp (lift0 1 s)(tRel 0)` is a β-redex (`lift0 1 s` a λ): `s = tLambda na1 v1 v2`,
    `v = tLambda na N v2` (`lift_subst0_Rel`), `u = s = tLambda na1 v1 v2`. Join with **0 steps both
    sides** via `upto_domain (tLambda na N v2)(tLambda na1 v1 v2)` (bodies `v2`, domains ignored). ✔
  - `lift0 1 s = mkApps (tFix mfix idx) args` and **red_fix fires** (`:1690-1717`): `u = s` re-fires
    `red_fix` (is_constructor transfers through the lift, `:1699-1711`) → `w = mkApps fn0 args0`
    (1 β on u); `v = eta_redex na N (mkApps fn0 args0) →η mkApps fn0 args0` (1 `eta_red`) → `w'=w`. ✔
    **This is "β exposes a fix under an η-binder" — the sharpest interaction — and it still carries no
    β on the v side.**
- η in domain `N→N'`: `u = tLambda na N' M →β tLambda na N' M'` (body β insensitive to the vass TYPE
  [INFERENCE: red1 body steps use the context's vdef bodies, not vass types]); `v = tLambda na N M'`;
  `upto_domain` joins (0 η on v). ✔
- η in body `M→M''`: both β and η in the body → IH join, lift under `tLambda`. ✔

### `letin` / `tCase` / `tProj` congruences  (C2 `:1727-1811`)
Plain congruences: η and β act on sibling subterms (orthogonal → single-sided replay each side) or on
the same subterm (IH join). No β on the v side. ✔ [INFERENCE]

### `tFix`-ty/body and `tCoFix`-ty/body congruences  (C2 `:1899-2198`)  [INFERENCE: holds]
Audited (`:1899-2013` read). β and η both act on the `mfix` `OnOne2` structure. When they hit
**different** defs the joins are single-sided orthogonal replays (`OnOne2_All2 … beta_eta`, each step
η on the v side / β on the u side); when they hit the **same** def the body is joined by the **IH**
(`eapply p1 in X1 as [u' [v' …]]`, `:1993`), which in C3's formulation is already one-sided. C2 carries
`upto_types`/`upto_domain` bookkeeping on the two `fix_context`s (`:1934-1937,:1967-1969`); for C3 this
is absorbed by the conclusion's `upto_domain` plus "red1 body steps are insensitive to the vass TYPE".
**No new β on the β-reduct (v) side. No counterexample.** The `evar`/`array` cases are the same
OnOne2/IH pattern.

---

## Context hypotheses this route assumes (with upstream status; for L2 to land WITH the definitions)

Each is a standard η-closure fact (U2/U4), none is C3 or a weakening of C3. Stated against the shared
`eta1`/`upto_domain`; `eta := clos_refl_trans eta1`.

| id | statement | upstream status |
|---|---|---|
| CH1 `eta1_mkApps_inv` | `eta1 (mkApps M l) N -> (∑ M', eta1 M M' × N = mkApps M' l) + (∑ l', OnOne2 eta1 l l' × N = mkApps M l')` | **PROVED** `origin/eta_postpo:PCUICEtaReduction.v:1223-1234` (old AST); 9.2 port is a trivial `induction l` |
| CH2 `eta_subst` (body) | `eta t t' -> eta (subst s k t)(subst s k t')` | **PROVED** upstream (`eta_postpo`, used `PCUICEtaReduction.v:1009,1481,1489`); def in conv/subst file |
| CH3 `subst_eta` (list) | `All2 eta s s' -> eta (subst s k t)(subst s' k t)` | **PROVED** upstream (used `:1046,1483,1486`) |
| CH4 `eta_fix_subst`/`eta_cofix_subst` | `eta1 (tFix mfix i)(tFix mfix' i) -> All2 eta (fix_subst mfix)(fix_subst mfix')` (+ cofix) | **DERIVED inline** in C2 (`induction #|mfix|; constructor; …`, `:1521-1529`); package as a lemma |
| CH5 η congruence closures | `eta`-monotone versions of `eta_Lambda`,`eta_App`,`eta_mkApps`,`eta_Case`,`eta_Proj` (lift one-step `eta1` congruences to `eta`) | **β-eta versions PROVED** upstream (`beta_eta_Lambda :658`, `beta_eta_mkApps :965`, …); η-only analogs are a 1-line `clos_refl_trans` map |
| CH6 `red1_strengthening` (for `abs_red_r`/`eta_red`) | `red1 Σ (Γ,,,[vass na N]) (lift0 1 t) u -> ∑ u', u = lift0 1 u' × red1 Σ Γ t u'` | **PROVED** upstream (`PCUICBasicStrengthening`, used C2 `:1718`); base has `PCUICBasicStrengthening`? CONFIRM on 9.2 |

Re-fires on the `u` side use only base `red1` constructors — no hypothesis. `clos_refl` combinator:
CONFIRM it is in scope (base imports `Equations.Type.Relation`, which has `clos_refl_trans`; `clos_refl`
is what upstream `red01` used, `origin/eta_postpo:PCUICConversion.v:36-42`). If absent, define the plain
relation combinator locally (not a definition of eta1/upto_domain).

Base lemma names confirmed on `56b92b56`: `OnOne2_nth_error` (`PCUICNormal.v:1810`), `fix_subst`/
`unfold_fix`/`is_constructor`/`isConstruct_app` (`Syntax/PCUICCases.v:370,378,418`), `simpl_subst`/
`simpl_subst'` (`PCUICLiftSubst.v:192,493`), `red1_ind_all` (`PCUICReduction.v:161`), `red :=
clos_refl_trans red1` (`:364`).

## Status / next
- 2026-10-27: worktree+branch; **full build-free audit of every structurally-distinct case family
  DONE** [INFERENCE: all hold, NO counterexample anywhere]: the four unlocking cases (`red_fix`,
  `red_cofix_case`, `red_cofix_proj`, `red_proj`), the binder critical pairs (`red_beta`, `abs_red_l`,
  `abs_red_r` incl. β-exposes-fix-under-η-binder), and the `letin`/`tCase`/`tProj`/`tFix`/`tCoFix`/
  `evar`/`array` congruences. Invariant across all: **β never lands on the β-reduct (v) side; it carries
  η* only; the single β is one `red1` re-fire on the η-reduct (u) side.** Reported to `agent://ArityLane`.
  Snapshots pushed to fork.
- 2026-10-27 (later): **the four unlocking cases are now FULLY UNCONDITIONAL and axiom-clean** —
  commit `129847df`, EXIT 0, `Print Assumptions` = only `PrimString`/`PrimInt63`/`PrimFloat`, no
  `Admitted`/`Axiom`, NO Section Context hypotheses. All CH1-CH6 + CH4f/CH4c discharged: CH2 Required
  from EtaL2's `PCUICEtaConfluence`; CH4f/CH4c proved locally from EtaL2's `eta_subst` + local
  `All2_eta_fix_subst`/`cofix` + `eta1_tFix_inv`/`tCoFix_inv`. Still NO base confluence/rho/pred1.
  (Earlier in the day they were conditional on {CH4f,CH4c}; now unconditional.)
  `pcuic/theories/PCUICEtaReductionC3.v` on branch `frac/eta-c3-C3Prover3` (fork, commit `669950e0`)
  proves `C3_red_fix`, `C3_red_cofix_case`, `C3_red_cofix_proj`, `C3_red_proj` — each a standalone
  lemma over the matching `red1` redex with C3's exact conclusion
  (`clos_refl (red1 Σ Γ) u w × eta v w' × upto_domain w w'`). **Build: `rocq 9.2+rc2`, image
  `bet64-base`, `theories/PCUICEtaReductionC3.vo` EXIT 0 (2026-10-27T16:45:20Z).**
  `Print Assumptions` on all four: only `PrimString.string`/`PrimInt63.int`/`PrimFloat.float` (the
  AST's primitive types, in every MetaRocq lemma) — **no `Admitted`, no `Axiom`, and none of the CH
  hypotheses leak as axioms** (they are explicit lemma parameters after section discharge).
  It `Require`s the shared `PCUICEtaDefs.v` (adopted verbatim at C3Prover1's green commit `89f517bc`;
  its WIP `f28e6504` had a `!`-goal-selector slip in `eta1_ind_all`'s `case_eta_brs`, already fixed in
  `89f517bc`). The CH Context hypotheses actually used (U-rows): CH1 `eta1_mkApps_inv`, CH2
  `upto_domain_refl`, CH3 `eta1_isConstruct_app`, CH4f/CH4c `(co)fix-unfold commutes with η up to η*`,
  CH5a/CH5b `eta` congruence under `mkApps` (head / one arg), CH6 `OnOne2`-eta `nth_error`
  (reflexive-closure form). `onone2_eta_is_constructor` is PROVED locally from CH3+CH6.
- 2026-10-27: discharged the structural U4 facts **CH1 `eta1_mkApps_inv`, CH5a `eta_mkApps_head`,
  CH5b `eta_mkApps_args`, CH6 `onone2_eta_nth_error` as REAL local proofs** (pure `eta1`-congruence
  from `PCUICEtaDefs`); build still EXIT 0 (commit `0ff98361`, fork). These four are now UNCONDITIONAL.

### AUTHORITATIVE C3 statement (re-hardened 2nd fix via EtaL2, 2026-10-27 — prove verbatim in the assembly)
```
Lemma C3 : forall {cf : checker_flags} (Σ : global_env) (Γ : context) (t u v : term),
  wf Σ ->
  is_closed_context Γ -> is_open_term Γ t ->
  red1 Σ Γ t v -> eta1 t u ->
  ∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'.
```
Two independent falsifications forced the premises, both in the CONGRUENCE cases (not the four
unlocking ones):
1. UNSCOPED form FALSE on ill-scoped branch contexts (EtaC3D fuzz, 31,273 cases) → `is_closed_context`
   / `is_open_term` (the tCase congruence cases).
2. SCOPED-but-wf-free form FALSE: an open constant body in Σ (`cst_body = Some (tRel 0)`) lets
   `red_delta` destroy the η-redex inside a congruence; term/context scoping cannot exclude it →
   add **`wf Σ`** (exactly C2's premise, `origin/eta_postpo:PCUICEtaReduction.v:1471`). C4 supplies
   `wf` with no mismatch (base `red_confluence` is `wf`-only).
**Correction to my build-free audit:** the `abs_red_r`/congruence cases I marked `[INFERENCE: holds]`
were believed under implicit well-scoping; #2 shows the honest statement needs `wf Σ`. This is exactly
why those verdicts carried `[INFERENCE]` and not `[PROVED]` — read-and-believed ≠ proved; the falsifier
caught it.
**My four unlocking cases are UNAFFECTED** (EtaL2 confirms: no tCase congruence, no `red_delta`), so my
standalone helper lemmas stay premise-free; the assembly carries `wf Σ`/scoping at top level.

### ⚠ Conditional-proof status (stream-lead rule 16:50Z — `Print Assumptions` cannot show parameters)
The four C3 unlocking-case lemmas are **PROVED, CONDITIONAL ON** exactly these two remaining Section
`Context` hypotheses (they do NOT appear in `Print Assumptions`):
- **CH4f `eta1_fix_unfold`** : `eta1 (tFix mfix idx) N -> unfold_fix mfix idx = Some(narg,fn) -> ∑ mfix' fn', [× N = tFix mfix' idx, unfold_fix mfix' idx = Some(narg,fn') & eta fn fn']` — U2/U4.
- **CH4c `eta1_cofix_unfold`** : the `tCoFix`/`unfold_cofix` twin — U2/U4.

Both reduce to EtaL2's single primitive `eta_subst`
(`All2 eta s s' -> eta b b' -> eta (subst0 s b) (subst0 s' b')`), **confirmed with EtaL2 to be stated
generally enough** (it takes `All2 eta` over the whole `subst0` list, which covers the
`fix_subst`/`cofix_subst` fold), so there is **no gap and no separate owner**: CH4f = `eta_subst`
applied to `All2 eta (fix_subst mfix) (fix_subst mfix')` and `eta (dbody d) (dbody d')`, the former
being a LOCAL pointwise congruence (each entry `tFix mfix j -> tFix mfix' j` is one `eta1` step from
the same `OnOne2`, via `fix_eta_ty`/`fix_eta_body` at index `j`).
*Not discharged locally yet by deliberate choice:* the convenient `nth_error_fix_subst` lives in
`PCUICParallelReductionConfluence`, and importing it would make C3 inherit the base confluence/rho
development — which the lead explicitly valued that this proof does NOT. So CH4 waits for `eta_subst`
rather than pull that weight.

**UNCONDITIONAL now (real local proofs in the file; commits `0ff98361`, `89e789a0`, `a08e28a1`):**
CH1 `eta1_mkApps_inv`, CH2 `upto_domain_refl` (term induction), **CH3 `eta1_isConstruct_app`**
(from `eta1_mkApps_inv` + `decompose_app_inv`/`decompose_app_mkApps`), CH5a `eta_mkApps_head`,
CH5b `eta_mkApps_args`, CH6 `onone2_eta_nth_error`.
No `Admitted`, no `Axiom`; `Print Assumptions` shows only the AST primitive types.
**Foundation note:** this proof depends on NOTHING from the base confluence development
(no `red_confluence`, no `rho`, no `pred1`) — the direct `red1_ind_all` route only.
- Next: discharge CH4f/CH4c locally from EtaL2's `eta_subst` the moment it lands (that makes the four
  cases UNCONDITIONAL); then assemble the full `red1_ind_all` induction in the HARDENED form
  (four branches = these four lemmas; ~60 congruence branches per the audit above).

## Fallback (pred1/rho)
Commute `eta1` with `pred1` (`PCUICParallelReduction.v`: one `pred1` contracts a set of non-overlapping
β-redexes, η a diamond against it), transfer via `red1 ⊆ pred1 ⊆ red` and β-CR `red_confluence`
(`PCUICConfluence.v:3938`). Method only; the landed lemma stays C3 on `eta1`/`upto_domain`.
