# C3 falsifier audit (gate C7, plan §5 "C3's falsifier audit, build-free")

Author: C3Falsifier (L2 duplicate prover), started 2026-10-27. Build-free: no Rocq was run for
this section. Branch `frac/eta-c3-C3Falsifier` from `frac/integ-all2` `56b92b56`; the file is also
committed to `wip/c3-falsify-2026-10-27` on the fork (`theorem-labs/metarocq`) as
`lanes/eta/c3-audit.md`, because `/mnt/nvme/sami/frac-verify/bet64-upstream-01a170d9/` is not a git
repository.

**Due date of this section: 2026-10-29 12:00Z. It is finished early and reported early.**

## 0. The question the gate asks, and the answer

> every case of `origin/eta_postpo:pcuic/theories/PCUICEtaReduction.v:1475-2198` whose script takes
> a β or ι step on the η side, with line numbers. An empty list means the `red1_ind_all` reuse is
> viable; a non-empty one puts each entry under the plan's §6 rank 1 that day.

**The list is EMPTY.** Not one of the 27 `red1_ind_all` cases of `red1_eta1_diamond`
(`:1475-2198`), and not one of their ~70 η-subcases, spends a β or ι step where C3 allows only η;
and not one of them spends more than one β/ι step where C3 allows at most one. The 2020 script is
*already* a Hindley strong-commutation proof: every case closes the square with **≤ 1 `red1` step
on the η-reduct and η-steps only on the β-reduct**, which is exactly C3's shape. See §2 for the
case-by-case evidence and §3 for the five obstacles to reuse that are *not* β-on-the-η-side.

Consequence for the plan: **no entry is added to §6 rank 1 by this audit on 2026-10-29.** The
`red1_ind_all` reuse is viable with respect to the step budget. The reuse is *not* free; §3 lists
what must be strengthened or newly written, including 7 cases of 9.2's `red1` that the 2020 script
does not contain at all.

## 1. Method, and the two step budgets

Upstream C2 (`:1471-1473`) and C3 name their terms in opposite order. Fixing upstream's names
(`red1 Σ Γ t u`, `eta1 t v`):

| | upstream C2 (`:1473`) | C3 (plan §3, row C3) |
|---|---|---|
| from the **β-reduct** `u` | `beta_eta Σ Γ u u'` | `clos_refl_trans eta1 u w'` — **η only, unbounded** |
| from the **η-reduct** `v` | `beta_eta Σ Γ v v'` | `clos_refl (red1 Σ Γ) v w` — **≤ 1 β/ι, and no η** |
| join | `upto_domain u' v'` | `upto_domain w w'` |

So the plan's phrase "**β on the η side**" = a `red1` step on the path that C3 reserves for η, i.e.
on the **β-reduct** `u` — upstream's *first* goal. That is the primary list (§2, column "β-reduct →
join"). Because C3's *other* edge is budgeted too (≤ 1 `red1`, **no** η), I also audited upstream's
second goal; that is the secondary list (column "η-reduct → join"). Both lists are empty.

`tac t` (`:1220`) = `pretac t` (`:1219`) + the `beta_eta` automation (`:579-589`), and `pretac t`
is `exists t, t; repeat split; [..|try reflexivity]`: it picks **one** join `t` for both sides and
discharges `upto_domain t t` by reflexivity, leaving goal 1 = `beta_eta Σ Γ u t` and goal 2 =
`beta_eta Σ Γ v t`. The `beta_eta` automation has both `Hint Constructors red1 : beta_eta` (`:591`)
and `Hint Constructors eta1 : beta_eta` (`:590`), so it *could* hide a β step on either side; a
build-free audit therefore cannot read the step off the tactic. Instead, for every case I computed
`u`, `v` and the chosen join `t` from the case's own term shapes and compared them. That is what
the "steps needed" columns below record. Where the script leaves a goal to an explicit sub-proof
(`:1477`, `:1510-1555`, `:1572-1617`, `:1625-1670`, `:1714-1717`, `:1718-1719`, `:1738-1743`), the
sub-proof names the step and the reading is direct, not inferred.

## 2. The 27 cases

Case order is `red1_ind_all`'s (`origin/eta_postpo:pcuic/theories/PCUICConversionDef.v:109-196`,
27 constructors). "β-reduct → join" is the C3-η edge (budget: η\*); "η-reduct → join" is the
C3-β edge (budget: ≤ 1 `red1`). `refl` = the two terms are literally equal, zero steps.

| # | red1 case | η subcase | lines | β-reduct → join | η-reduct → join | within C3? |
|---|---|---|---|---|---|---|
| 1 | `red_beta` | `eta_red` on the λ (the redex *is* an η-redex) | 1476-1478 | refl (after `simpl_subst`, `lift0_id`) | refl | ✔ |
| 1 | `red_beta` | `abs_eta_l` (λ domain) | 1479 | refl | 1 × `red_beta` | ✔ |
| 1 | `red_beta` | `abs_eta_r` (λ body) | 1480-1481 | η\* (`eta_subst`, `:1481`) | 1 × `red_beta` | ✔ |
| 1 | `red_beta` | `app_eta_r` (argument) | 1482-1483 | η\* (`subst_eta`, `:1483`) | 1 × `red_beta` | ✔ |
| 2 | `red_zeta` | `letin_eta_def` | 1485-1486 | η\* (`subst_eta`) | 1 × `red_zeta` | ✔ |
| 2 | `red_zeta` | `letin_eta_ty` | 1487 | refl | 1 × `red_zeta` | ✔ |
| 2 | `red_zeta` | `letin_eta_body` | 1488-1489 | η\* (`eta_subst`) | 1 × `red_zeta` | ✔ |
| 3 | `red_rel` | — (no `eta1` from `tRel`) | 1490 | vacuous | vacuous | ✔ |
| 4 | `red_iota` | `case_eta_peta` (predicate) | 1492 | refl (`iota_red` drops `p`) | 1 × `red_iota` | ✔ |
| 4 | `red_iota` | `case_eta_discr` → η in `args` | 1493-1497 | η\* (`beta_eta_mkApps`, `All2_skipn`) | 1 × `red_iota` | ✔ |
| 4 | `red_iota` | `case_eta_brs` | 1498-1506 | η\* or refl (`OnOne2_nth_error`) | 1 × `red_iota` | ✔ |
| 5 | `red_fix` | `fix_eta_ty` on the head | 1508-1530 | η\* (`subst_beta_eta` over `fix_subst`) | 1 × `red_fix` | ✔ |
| 5 | `red_fix` | `fix_eta_body` on the head | 1531-1555 | η\* (`beta_eta_subst0` + `subst_beta_eta`) | 1 × `red_fix` | ✔ |
| 5 | `red_fix` | η in `args` | 1556-1565 | η\* | 1 × `red_fix` (`is_constructor` re-proved `:1558-1565`) | ✔ |
| 6 | `red_cofix_case` | `case_eta_peta` | 1568 | refl | 1 × `red_cofix_case` | ✔ |
| 6 | `red_cofix_case` | `cofix_eta_ty`/`_body` on the head | 1571-1617 | η\* (as #5) | 1 × `red_cofix_case` | ✔ |
| 6 | `red_cofix_case` | η in `args` | 1570 | η\* | 1 × `red_cofix_case` | ✔ |
| 6 | `red_cofix_case` | `case_eta_brs` | 1618 | η\* | 1 × `red_cofix_case` | ✔ |
| 7 | `red_cofix_proj` | `cofix_eta_ty`/`_body` on the head | 1624-1670 | η\* (as #5) | 1 × `red_cofix_proj` | ✔ |
| 7 | `red_cofix_proj` | η in `args` | 1623 | η\* | 1 × `red_cofix_proj` | ✔ |
| 8 | `red_delta` | — (no `eta1` from `tConst`) | 1672 | vacuous | vacuous | ✔ |
| 9 | `red_proj` | η in `args` (head `tConstruct` is η-inert) | 1673-1678 | η\* or refl | 1 × `red_proj` | ✔ |
| 10 | `abs_red_l` | `eta_red` | 1680 | 1 × `eta_red` | refl | ✔ |
| 10 | `abs_red_l` | `abs_eta_l` | 1681-1682 | IH, lifted by `tLambda` | IH, lifted | ✔ |
| 10 | `abs_red_l` | `abs_eta_r` | 1683 | 1 × `abs_eta_r` | 1 × `abs_red_l` | ✔ |
| **11** | **`abs_red_r`** | **`eta_red` ∧ the body is a `red_beta` redex** | **1686-1689** | **refl** | **refl** (joins differ only in the λ domain/name — `upto_domain`) | ✔ |
| **11** | **`abs_red_r`** | **`eta_red` ∧ the body is a `red_fix` redex** — *the postponement killer* | **1690-1717** | **1 × `eta_red` (`:1714-1717`)** | **1 × `red_fix`** | ✔ |
| 11 | `abs_red_r` | `eta_red` ∧ `app_red_l` under the lift | 1718-1719 | 1 × `eta_red` | 1 × `red1` (via `red1_strengthening`) | ✔ |
| 11 | `abs_red_r` | `eta_red` ∧ `app_red_r` on `tRel 0` | 1720-1722 | vacuous | vacuous | ✔ |
| 11 | `abs_red_r` | `abs_eta_l` | 1723 | 1 × `abs_eta_l` | 1 × `abs_red_r` | ✔ |
| 11 | `abs_red_r` | `abs_eta_r` | 1724-1725 | IH, lifted | IH, lifted | ✔ |
| 12 | `letin_red_def` | `letin_eta_def` | 1728-1729 | IH, lifted | IH, lifted | ✔ |
| 12 | `letin_red_def` | `letin_eta_ty`/`_body` | 1730-1731 | 1 × η congruence | 1 × `letin_red_def` | ✔ |
| 13 | `letin_red_ty` | all three | 1732-1736 | IH or 1 × η congruence | IH or 1 × `letin_red_ty` | ✔ |
| 14 | `letin_red_body` | `letin_eta_def` | 1738-1740 | 1 × η + η\* (2nd component of `red1_eta_ctx`) | 1 × `red1` in the η-context (1st component) | ✔ (see §3.1) |
| 14 | `letin_red_body` | `letin_eta_ty` | 1741-1743 | as above | as above | ✔ (see §3.1) |
| 14 | `letin_red_body` | `letin_eta_body` | 1744-1745 | IH, lifted | IH, lifted | ✔ |
| 15 | `case_red_pred` | `case_eta_peta` | 1747-1749 | IH, lifted | IH, lifted | ✔ |
| 15 | `case_red_pred` | `case_eta_discr`/`_brs` | 1750-1751 | 1 × η congruence | 1 × `case_red_pred` | ✔ |
| 16 | `case_red_discr` | all three | 1752-1757 | IH or 1 × η congruence | IH or 1 × `case_red_discr` | ✔ |
| 17 | `case_red_brs` | `case_eta_peta`/`_discr` | 1760-1761 | 1 × η congruence | 1 × `case_red_brs` | ✔ |
| 17 | `case_red_brs` | `case_eta_brs`, same branch | 1768-1772 | IH, lifted | IH, lifted | ✔ |
| 17 | `case_red_brs` | `case_eta_brs`, different branches | 1773-1782 | 1 × `case_eta_brs` (`OnOne2_impl`) | 1 × `case_red_brs` | ✔ |
| 17 | `case_red_brs` | `case_eta_brs`, list recursion | 1783-1785 | IH, lifted | IH, lifted | ✔ |
| 18 | `proj_red` | `proj_eta` | 1787-1789 | IH, lifted | IH, lifted | ✔ |
| 19 | `app_red_l` | `app_eta_l` / `app_eta_r` | 1790-1793 | IH / 1 × `app_eta_r` | IH / 1 × `app_red_l` | ✔ |
| 20 | `app_red_r` | `app_eta_l` / `app_eta_r` | 1794-1797 | 1 × `app_eta_l` / IH | 1 × `app_red_r` / IH | ✔ |
| 21 | `prod_red_l` | `prod_eta_l` / `_r` | 1798-1801 | IH / 1 × η congruence | IH / 1 × `prod_red_l` | ✔ |
| 22 | `prod_red_r` | `prod_eta_l` / `_r` | 1802-1805 | 1 × η congruence / IH | 1 × `prod_red_r` / IH | ✔ |
| 23 | `evar_red` | `evar_eta`, all four list positions | 1807-1829 | IH or 1 × `evar_eta` | IH or 1 × `evar_red` | ✔ |
| 24 | `fix_red_ty` | `fix_eta_ty` (same/other/rec) | 1832-1873 | IH or 1 × `fix_eta_ty` | IH or 1 × `fix_red_ty` | ✔ |
| 24 | `fix_red_ty` | `fix_eta_body` | 1874-1916 | 1 × `fix_eta_body` | 1 × `fix_red_ty` | ✔ |
| 25 | `fix_red_body` | `fix_eta_ty` | 1919-1962 | 1 × `fix_eta_ty` | 1 × `fix_red_body` in the η-changed `fix_context` (`upto_types`, `:1934-1937`) | ✔ |
| 25 | `fix_red_body` | `fix_eta_body` | 1963-2013 | IH or 1 × `fix_eta_body` | IH or 1 × `fix_red_body` | ✔ |
| 26 | `cofix_red_ty` | both | 2016-2100 | as #24 | as #24 | ✔ |
| 27 | `cofix_red_body` | both | 2103-2197 | as #25 | as #25 | ✔ |

### 2.1 The three cases worth reading in full

These are the ones a reader will distrust, so the computation is written out.

**(a) `abs_red_r` × `eta_red` × `red_fix` (`:1690-1717`) — the case that killed η-postponement.**
`t = tLambda na N (mkApps (tFix mfix idx) args)` where `mkApps (tFix mfix idx) args` is
`tApp (lift0 1 s) (tRel 0)` for `s = mkApps (tFix x idx) x0` (`lift_Apps_Fix_inv`, `:1696`), and
`is_constructor narg x0` is re-proved for the *unlifted* spine at `:1699-1712`. The β step is
`red_fix` under the λ: `u = tLambda na N (mkApps fn args)`. The η step is at the top:
`v = s = mkApps (tFix x idx) x0`. Join `t₀ := mkApps fn₀ x0` (`tac (mkApps t x0)`, `:1713`).
*β-reduct → join:* `:1714-1717`, **exactly one `eta1`** — `eta_red na (mkApps fn₀ x0) N`, after
`rewrite lift_mkApps`, because `mkApps fn args = lift0 1 (mkApps fn₀ x0)` wrapped by the λ and
applied to `tRel 0`. *η-reduct → join:* **exactly one `red_fix`** (`unfold_fix x idx`,
`is_constructor narg x0`). Both budgets met with equality. This is precisely why postponement dies
and commutation survives: the fix redex that η unlocks is consumed by C3's *one permitted* β step
on the η-reduct, and the β-reduct pays for it with *one* η step, not with β.

**(b) `abs_red_r` × `eta_red` × `red_beta` (`:1686-1689`).**
`t = tLambda na N (tApp (lift0 1 (tLambda na₁ v₁ v₂)) (tRel 0))`. β: `subst10 (tRel 0) (lift 1 1 v₂)
= v₂` (`lift_subst0_Rel`, `:1688`), so `u = tLambda na N v₂`. η: `v = tLambda na₁ v₁ v₂`.
**Zero steps on both sides**; the two joins are `tLambda na N v₂` and `tLambda na₁ v₁ v₂`, which are
**not** equal — they differ in the λ domain *and* the binder name, and are joined only by
`upto_domain` (`utd_Lambda`). This case is the single strongest reason the lemma has to be stated
modulo `upto_domain` at all; it is also the reason `upto_domain` must ignore the binder
**annotation**, not just the domain (plan I2).

**(c) `fix_red_body` × `fix_eta_ty` (`:1919-1962`).** The β step reduces a fix *body* in
`Γ ,,, fix_context mfix0`; the η step changes a fix *type*, hence changes `fix_context`. The join is
a single `mfix2` (`:1930`, one join, not two) and the η-reduct's step is the same body reduction
re-played in `Γ ,,, fix_context mfix3`, licensed by `upto_types_fix_context` (`:1934-1937`,
`:1450-1457`) and `red1_upto_types` (`:1407`). Still **one** `red1`: `upto_types` changes only
assumption *types*, which `red1` does not read. The β-reduct pays **one** `fix_eta_ty`.

## 3. What is *not* β-on-the-η-side but still blocks a literal reuse

The gate asked one question and the answer is "empty". These five items are the honest remainder:
they are reuse costs, not counterexample candidates, and none of them goes to §6 rank 1.

**3.1 `red1_eta_ctx` (`:1068-1070`) is stated too weakly for C3.** Today:
`red1 Σ Γ t u -> eta_ctx Γ Δ -> ∑ u', beta_eta Σ Δ t u' × beta_eta Σ Δ u u'`. Used at `:1738` and
`:1741` (case 14). C3 needs the split form
`red1 Σ Γ t u -> eta_ctx Γ Δ -> ∑ u', clos_refl (red1 Σ Δ) t u' × clos_refl_trans eta1 u u'`.
It is true in that form [INFERENCE, from reading `:1072-1146`]: the catch-all `:1073-1074` is
`red1_beta_eta` of the *same* single step (reflexivity on the second component), the `red_rel` case
`:1075-1083` gives one `red1` in `Δ` plus `lift0 (S i)` of the context's η-steps, and every other
case is a congruence over the induction hypothesis. L2 must re-prove it, not import it.

**3.2 `red1_strengthening` (used `:1718`) is `Admitted` upstream** —
`origin/eta_postpo:pcuic/theories/PCUICBasicStrengthening.v:982-986`, the plan's **U5**. Exactly one
subcase of C3 needs it (case 11, `abs_red_r` × `eta_red` × `app_red_l`), and it is unavoidable
there: the β step lives under `lift0 1`, and only strengthening pulls it back to `Γ`. Any C3 that
does not prove U5 carries U5 as a `Context` hypothesis.

**3.3 The `beta_eta` automation cannot be reused as such.** `clos_refl (red1 Σ Γ)` is **not**
transitive and does not contain `eta1`, so the `:579-594` hint database (which mixes both
constructor sets and `beta_eta_trans`) will close C3 goals by illegal routes or not at all. C3 needs
two separate databases — one for `clos_refl (red1 Σ Γ)` (apply at most one constructor, then stop)
and one for `clos_refl_trans eta1` — and the congruence lemmas `beta_eta_Lambda`/`_App`/`_Case`/…
(`:990-1000`, `ap_beta_eta`) duplicated for each. This is the bulk of the scripting work and the
reason the plan calls C3 "L, research" rather than "M".

**3.4 Seven cases of 9.2's `red1` have no counterpart in the 2020 script.** The 2020 `red1`
(`PCUICConversionDef.v:109-196`) has 27 constructors; 9.2's (`pcuic/theories/PCUICReduction.v:41-152`
on `56b92b56`) has **31**, and three of the shared ones changed shape:

| 9.2 constructor | line (56b92b56) | 2020 counterpart | what C3 must newly prove |
|---|---|---|---|
| `case_red_param` | `:94-96` | none (2020 `p` is a plain term) | η in a `pparams` entry vs β in another; and η in `pparams` vs `red_iota`, where the parameter is substituted into `inst_case_branch_context` and then `expand_lets`-duplicated — the β-reduct side needs **η\*, not one η** |
| `case_red_return` | `:98-100` | `case_red_pred` (`:164`), but now **under `Γ ,,, inst_case_predicate_context p`** | the return reduction is context-dependent, and η in `pparams` changes that context ⇒ a `red1_eta_ctx`-style lemma for `inst_case_predicate_context` |
| `case_red_brs` | `:105-109` | `:166-168`, but now **under `Γ ,,, inst_case_branch_context p br`** | same, for branch contexts, plus `bcontext` preservation |
| `red_iota` | `:53-57` | `:124-126` (no `expand_lets`, no `bcontext`) | `iota_red ci.(ci_npar) p args br` reads `p.(pparams)`, `p.(puinst)` and `br.(bcontext)`; **this is where let-bound parameters enter** (`expand_lets` substitutes a let body, duplicating any η-redex in it) |
| `red_proj` | `:82-84` | `:152-154` | cosmetic (projection record) |
| `array_red_val` | `:139-142` | none (`tPrim` did not exist) | an `OnOne2` congruence, same shape as `evar_red` |
| `array_red_def` | `:144-147` | none | a plain congruence |
| `array_red_type` | `:149-152` | none | a plain congruence |

The three `array_*` cases are routine congruences (shape of #19/#23). The four `tCase` rows are
**not** routine: they are the only places in 9.2 where a reduction's *context* is computed from the
term being reduced, so an η step in `pparams` moves the context in which the other side's step must
be re-played. They are the right place to hunt for a counterexample, and they are where this
auditor's falsification work (§4 of this file, separate section) is aimed. Note that `eta1` itself
must also grow the 9.2 congruences (`case_eta_param`, `case_eta_return`, `array_eta_*`) — that is
plan row **U3**, not C3.

**3.5 The script's `upto_domain` joins are produced by two different witnesses in 11 cases**
(`exists a, b` with `a ≠ b`: `:1682`, `:1689`, `:1725`, `:1729`, `:1735`, `:1745`, `:1748`, `:1755`,
`:1766`, `:1789`, `:1792`, `:1797`, `:1800`, `:1805`, `:1812`, `:1843`, `:1975`, `:2027`, `:2070`,
`:2159`). C3 keeps that shape (`∑ w w'`), so no change is needed — recorded only because a reader
checking "one join or two" will otherwise have to re-derive it.

## 4. Verdict for the 2026-10-29 gate

- **β-or-ι-on-the-η-side list: EMPTY** (primary reading, upstream goal 1 / C3's `clos_refl_trans
  eta1` edge).
- **Over-budget-on-the-β-edge list: EMPTY** (secondary reading, upstream goal 2 / C3's `clos_refl
  (red1 Σ Γ)` edge; every case uses 0 or 1 `red1` there, never 2, never mixed with η).
- Therefore **nothing is added to plan §6 rank 1 by this audit**, and the `red1_ind_all` reuse is
  viable *as to the step budget*. The reuse costs are §3.1-3.5; the residual risk for C3 is
  concentrated in the four 9.2 `tCase` rows of §3.4, which the 2020 proof never had to face.
