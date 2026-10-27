# C3 falsification log — C3Falsifier (BET-315 eta lane, L2 duplicate / falsifier)

Branch `frac/eta-c3-C3Falsifier` from `frac/integ-all2` `56b92b56`; working copy on the fork
(`theorem-labs/metarocq`) as `wip/c3-falsify-2026-10-27`. The lane dir
`/mnt/nvme/sami/frac-verify/bet64-upstream-01a170d9/lanes/eta/` is NOT a git repo, so everything is
mirrored into the worktree before each commit.

Two jobs: (1) the build-free gate-C7 audit, done early → `lanes/eta/c3-audit.md`; (2) falsify C3,
below. **No counterexample found.**

## Job 2 — falsification of C3 on the four 9.2 `tCase` reduction rows

The lane lead (2026-10-27) named the four 9.2 `tCase` reduction rows as C3's concentrated residual
risk, because they are the only places in 9.2 where a reduction's *context* is computed from the
term being reduced (`inst_case_predicate_context p`, `inst_case_branch_context p br`) or where the
predicate parameters are substituted into a context and `expand_lets`-duplicated (`iota_red`). I
TESTED each, in Rocq, on the build box, against the lane's shared `eta1`/`upto_domain`
(`PCUICEtaDefs.v`, C3Prover1, `wip/eta-c3-defs-2026-10-27` `fb0ec681`) — not a retyped copy.

**File: `pcuic/theories/PCUICEtaC3Falsify.v`, builds GREEN on `bet64-mem` (EXIT 0, commit
`818ff73d`).** Each row is stated as its own C3 square — the premises of that `red1` constructor,
an arbitrary `eta1` step on the same term, and the C3 conclusion
`∑ w w', clos_refl (red1 Σ Γ) u w × clos_refl_trans eta1 v w' × upto_domain w w'` — with the
**strongest** induction hypothesis assumed (full C3, `IH : C3 Σ`). That is a sound *feasibility*
test: if a square cannot close even with the strongest IH, the obstruction is a genuine C3
counterexample. **It is NOT a proof of C3** (it assumes C3 as the IH and assumes the U-row closure
lemmas as `Context` hypotheses). No `Admitted`, no `Axiom`; `Print Assumptions` of all five lemmas
shows only `PrimString.string`/`PrimInt63.int`/`PrimFloat.float`, the base-PCUIC primitives.

### Result per row — all close within C3's budget, no counterexample

| row | lemma | how it closes | hardest subcase |
|---|---|---|---|
| `case_red_param` | `c3_case_red_param` | param/param collision via `onone2_param_square` (IH on the colliding `pparams` entry) | both steps in `pparams` |
| `case_red_return` | `c3_case_red_return` | **context-moving.** When η hits `pparams` it moves `inst_case_predicate_context`; `red1_eta_ctx_strong` replays the β step in the moved context with ONE `red1` (η-leg budget), β-leg pays η only (`case_eta_param` + η\* inside `preturn`) | η in `pparams` moves the β step's context |
| `case_red_discr` | `c3_case_red_discr` | discriminee IH; all other η subcases disjoint | η in discriminee = IH at the discriminee (see §"fix under η-binder") |
| `case_red_brs` | `c3_case_red_brs` | **branch-context.** η on a branch (`case_eta_brs`) never changes `bcontext`, and `inst_case_branch_context` reads only `bcontext`(+`pparams`/`puinst`), so a branch η step does NOT move the branch's reduction context → ordinary IH square in a FIXED context (`onone2_brs_square`). The only context move is via `case_eta_param`, handled like `case_red_return` (`brs_red_move`) | η in `pparams` moves every branch context |
| `red_iota` | `c3_red_iota` | every η position reflected in `iota_red`: `pparams` via `inst_case_branch_context`, spine `args` via the subst list, branch body via `expand_lets`; `preturn` is dropped (trivial); η on the `tConstruct` head is impossible (`eta1_mkApps_inv` left disjunct is absurd) | let-bound params: η in `pparams` → `expand_lets` of a moved context |

### Why the four rows do NOT hide a counterexample (the structural reason)

Two facts, both now mechanically checked, collapse the "context computed from the term" worry:

1. **η never changes a case/branch context's *shape*.** `case_eta_brs` is
   `on_Trel_eq eta1 bbody bcontext`: it rewrites a branch *body*, never its `bcontext`. And
   `inst_case_branch_context`/`inst_case_predicate_context` read only `pparams`, `puinst` and the
   (b)context's *declarations*, never a body being reduced. So the ONLY way an η step moves a
   reduction context is by changing `pparams` (`case_eta_param`). That single move is handled
   uniformly by `red1_eta_ctx_strong` (the C3-budget restatement of upstream's `red1_eta_ctx`,
   audit §3.1): it replays the other side's `red1` in the η-moved context with **one** step, and
   the moved context's effect on the result is paid by η\* (`eta_ctx_inst_case_context`,
   `eta_rt_expand_lets`, `eta_rt_subst_*`). This is exactly the `case_red_return`/`case_red_brs`
   pattern, and it is the same shape that closes everywhere else in the 2020 diamond script.

2. **`upto_domain` on `tCase` already matches this.** The shared `utd_Case` compares `pparams` and
   `preturn` by `upto_domain`, `pcontext`/`bcontext` by `eq_context_upto_names`, bodies by
   `upto_domain` — so the join `upto_domain w w'` is reflexive on every square above (both joins are
   literally equal), never straining the context comparison. No square needed `upto_domain` to do
   work on a context.

### The critical pair the lead named: "a β step that exposes a fix under an η-binder inside a case"

Concretely: `t = tCase ci p d brs` with `d = tLambda na A (tApp (lift0 1 (mkApps (tCoFix mfix idx)
coargs)) (tRel 0))` (an η-redex whose body is a cofix application). η-contracting `d` gives
`u = tCase ci p (mkApps (tCoFix mfix idx) coargs) brs`, which **can** then `red_cofix_case`. The β
step on `t` can only act *inside* `d` (`case_red_discr` then a step within the λ), because `d` is a
`tLambda`, not a (co)fix application, so `red_cofix_case` does **not** fire on `t` itself.

In my file this is the **`case_eta_discr` branch of `c3_case_red_discr`**: it applies `IH` to the
discriminee pair `(d-reduct, d-η-reduct)`. So the tCase wrapper adds nothing — the critical pair
**reduces to the discriminee-level C3**, which is precisely the audit's `abs_red_r × eta_red`
*unlocking* case (the one that killed postponement, `c3-audit.md` §2.1(a)/§2.3). The lane lead
reports those four unlocking cases now proven by the other provers, so this critical pair is closed:
the cofix that η unlocks is consumed by C3's *one* permitted `red1` on the η-reduct, and the β-reduct
pays η only. **No counterexample.**

The same holds for a fix/`red_proj` exposed by η inside a discriminee: `red_cofix_proj`/`red_proj`
need a `tProj` node and `red_fix` needs a `tApp`-headed spine, none of which `t`'s top node is, so
the β step is always a congruence (`case_red_*`) over the discriminee, and the unlocked step lives on
the η-reduct leg inside C3's one-`red1` budget (`c3-audit.md` §2.3).

## Candidates ruled out (what the 11-01 go/no-go uses to size residual risk)

Every tCase candidate I could construct is ruled out, and *how*:

1. **`case_red_param` vs `case_eta_param` (param/param critical pair).** Ruled out by
   `onone2_param_square` + IH; tested, closes. The two steps are on the same `pparams` list; the
   colliding entry is joined by IH, the rest by disjoint OnOne2.
2. **`case_red_return` vs `case_eta_param` (predicate context moves).** Ruled out: `red1_eta_ctx_strong`
   replays in the moved `inst_case_predicate_context`; one `red1`, η-only other leg. Tested, closes.
3. **`case_red_brs` vs `case_eta_param` (every branch context moves at once).** Ruled out:
   `brs_red_move` replays the single β branch step in the moved context; the β-reduct pays one
   `case_eta_param` + η\* on the reduced branch. Tested, closes.
4. **`case_red_brs` vs `case_eta_brs` (two branch bodies, same or different branch).** Ruled out:
   `onone2_brs_square`; same branch → IH in a FIXED context (η preserves `bcontext`), different
   branch → disjoint. Tested, closes.
5. **`red_iota` vs `case_eta_param` (let-bound parameters: η in a parameter that `expand_lets`
   duplicates).** Ruled out: `eta_rt_iota_params` (U2 `expand_lets`/`subst` closure); one `red_iota`,
   η-only other leg. Tested, closes. *This is the one the gate's risk-6/F-8 flags for the checker's
   K1; for C3 it is benign.*
6. **`red_iota` vs `case_eta_discr` (η in the discriminee spine `args`).** Ruled out: `eta1_mkApps_inv`
   (η on `tConstruct` head is impossible), then `eta_rt_iota_args` (η in the subst list). Tested,
   closes.
7. **`red_iota` vs `case_eta_brs` (η in the selected branch body).** Ruled out: `OnOne2_nth_error`
   locates the branch; `bcontext` preserved so the length side-condition survives; `eta_rt_iota_body`
   (`expand_lets` body closure). Tested, closes.
8. **`red_iota`/`case_red_*` vs `case_eta_return` (η in `preturn`).** Ruled out as trivial: `iota_red`
   does not read `preturn`, so the β-reduct leg is reflexive.
9. **β exposes a (co)fix/proj under an η-binder inside the discriminee.** Ruled out: subsumed by
   `c3_case_red_discr`'s `case_eta_discr` (IH at the discriminee); the discriminee-level pair is the
   audit's unlocking case, proven. See § above.

## Assumptions used (all plan U-rows or the C3-budget `red1_eta_ctx`; none is an axiom)

`Context` hypotheses of `PCUICEtaC3Falsify.v`, each discharged by the plan's U-rows:
`upto_domain_refl` (U1); `eq_context_upto_names_refl` (base); `eta1_mkApps_inv` (= upstream
`eta1_mkApps_inv`, PROVED); `eta_rt_subst_list`, `eta_rt_subst_term`, `eta_ctx_inst_case_context`,
`eta_rt_expand_lets`, `eta_rt_expand_lets_body`, `eta_ctx_assumptions` (U2 closure);
`red1_eta_ctx_strong` (the C3-budget form of upstream `red1_eta_ctx`, audit §3.1);
`eta_rt_iota_args`, `eta_rt_iota_params`, `eta_rt_iota_body` (U2 closure specialised to `iota_red`);
and `IH : C3 Σ` (the induction hypothesis of C3's own `red1_ind_all`). The U-row closure lemmas are
the ordinary substitution/`expand_lets` stability of η (plan rows U2/U4); proving them is L1's U
batch, not part of this falsification.

## Verdict

**No counterexample to C3 on any of the four `tCase` rows.** All four close within C3's asymmetric
budget (≤ 1 `red1` on the η-reduct leg, η\* on the β-reduct leg), mechanically, with the strongest
IH, no `Admitted`/`Axiom`. Combined with the empty gate-C7 audit (`c3-audit.md`) and the two peers'
independent audits/executable model, the four `tCase` rows do not hold a C3 counterexample; the
residual C3 work is proof engineering (C3's own asymmetric induction + the U-row closure lemmas),
not a falsification risk.
