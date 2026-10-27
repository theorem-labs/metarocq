# K1 / F-8 — let-bound inductive parameters: can the checker diverge from the kernel?

Author: C3Falsifier, 2026-10-27. Assignment (lane lead): the checker's K1 path
(`MustExpand` for under-applied `tInd`/`tConstruct` with unequal instances) against the gate's
risk-6 / F-8 — the kernel η-expands with `it_mkLambda_or_LetIn` over `mind_arity_ctxt` (so a
let-bound parameter becomes a `tLetIn` carrying its body), while the plan's K1 fast path compares
only the **assumption** binder types at `Conv` plus the full instance. Can K1 be made to **disagree
with the kernel** on a well-typed term — unsound-accept, or loop/refuse a kernel-accepted term?

**Answer: no unsound-accept is possible from let-bound parameters.** F-8 is **incompleteness-only**
(K1 compares instances at `Conv` while the kernel uses variance), never unsoundness. One **required
clause** must be stated in the plan's K1 row for this to hold (below). Measured on the Rocq 9.2
kernel; K1 is spec-only (no Rocq exists — confirmed with `ArityLane.EtaK4`, who owns K3/K4), so the
ground truth is kernel verdicts, exactly as the plan validates KF by table + F1 tests
(`plan-gate.md` B1: there is no formal model of `kernel/conversion.ml`, so a full mechanisation of
"K1 ⊆ kernel" is precluded; kernel measurement is the right artefact here).

## Method

Rocq 9.2 kernel (image `upstream-9.2.0-deps`, `rocq repl`), probe
`lanes/eta/k1_letparam_probe.v`. Verdicts via **`exact_no_check`**, which bypasses the conservative
elaborator and hands the term straight to the kernel (the kernel still typechecks every added
`Definition`), so "`… is defined`" = the **kernel** accepts the conversion, and a universe-constraint
error = the kernel/elaborator refuses. Three placements of an isolated universe `w` in a cumulative
inductive with a let-bound parameter, each compared **under-applied** (the only case that triggers
`MustExpand`) at **different** instances `w1 ≠ w2`:

```coq
Set Universe Polymorphism.  Set Polymorphic Inductive Cumulativity.
(* (a) dead let: w only in an unused let C *)
Cumulative Inductive BoxW@{u w}  (A : Type@{u}) (C := Type@{w} : Type@{w+1})        : Type@{max(u,w+1)} := boxw (a:A).
(* (c) w only in the conclusion sort (rides on the head instance) *)
Cumulative Inductive BoxWc@{u w} (A : Type@{u})                                     : Type@{max(u,w+1)} := boxwc (a:A).
(* (b) live let feeding an assumption binder E : C (= Type@{w}) *)
Cumulative Inductive BoxWb@{u w} (A : Type@{u}) (C := Type@{w} : Type@{w+1}) (E : C) : Type@{max(u,w+1)} := boxwb (a:A).
```

The let-param survives into the arity with its body, as Rocq prints it:
`BoxW@{u w} : Type@{u} -> let C := Type@{w} in Type@{max(u,w+1)}` and
`BoxWb@{u w} (A : Type@{u}) (C : Type@{w+1} := Type@{w}) (E : C) : Type@{max(u,w+1)}`.

## Measured kernel verdicts

| placement | term compared (w1 ≠ w2, u shared) | kernel verdict | log line |
|---|---|---|---|
| (a) dead let | `BoxW@{u w1} ≡ BoxW@{u w2}` (0 args) | **ACCEPT** | `a_diffw_k is defined` |
| (c) conclusion sort | `BoxWc@{u w1} ≡ BoxWc@{u w2}` (0 args) | **ACCEPT** | `c_diffw_k is defined` |
| (b) live assumption binder | `BoxWb@{u w1} A ≡ BoxWb@{u w2} A` (1 of 2 args) | **cannot be formed** without `w1=w2` | `Universe constraints are not implied by the ones declared: w1 = Wd` (both elaborator and `exact_no_check`) |
| (b) control, `w1=w2` | `BoxWb@{u w} A ≡ BoxWb@{u w} A` | **ACCEPT** | `b_pos is defined` |

(The elaborator is conservative — e.g. for (a) it infers `w1 = w2` on the typed `eq_refl`,
`boxw_diffw` — but the kernel via `exact_no_check` accepts (a)/(c) with `w1 ≠ w2`. Kernel is ground
truth under decision C.)

## What each verdict means for K1

Every occurrence of a let-param universe `w` falls into exactly one of three positions, and in each
the kernel and a correctly-specified K1 **agree**:

1. **Dead let (a).** The kernel **zeta-drops** the dead let before comparison (measured: it accepts
   `w1 ≠ w2`), so `w` never reaches a `Conv`-compared position. K1 clause (1) reads only the
   assumption binder `A : Type@{u}` and never sees `w` → K1 also accepts. **Agreement.**
2. **Conclusion sort / head instance (c).** `w` rides on the inductive head's instance
   `tInd@{u w}`; the kernel governs it by **cumulativity variance** at full arity (measured: accepts
   `w1 ≠ w2`). K1 clause (2) is that same `global_variance_gen` / `cmp_opt_variance` check
   (`PCUICEquality.v:46-57,:78-83`). **Agreement.**
3. **Live assumption binder (b).** `w` sits in the **type** of a still-unapplied binder `E : Type@{w}`,
   i.e. a **Π-domain** of the under-applied head's type. Π-domains are **invariant under
   conversion**, so `BoxWb@{u w1} A` and `BoxWb@{u w2} A` are at **different types** unless `w1=w2`
   — the kernel itself refuses to place them at a common type without `w1=w2` (measured, even via
   `exact_no_check`). Therefore **the comparison never arises in a well-typed term** with `w1 ≠ w2`,
   and the checker's conversion is only ever invoked inside a typing derivation (compared subterms
   are at convertible types). **No unsound accept is expressible.**

So a let-bound parameter **cannot** drive a K1 unsound-accept: a let-universe is either dropped (a),
variance-governed on the head (c), or pinned equal by Π-domain invariance of the head's type (b).
F-8 is **incompleteness-only** — K1's clause-(2) comparison is at `Conv` while the kernel expands
and uses cumulativity, so K1 **refuses** some kernel-accepted under-applied *cumulative* pairs
(returned as `Refused_c`, honest under decision C). That incompleteness is the broader
"K1 at `Conv` vs kernel variance" gap; let-bound parameters add nothing to the **soundness** risk.

## The one required clause (belt-and-braces; EtaK4's de-Bruijn point)

The (b) soundness relies on K1 forming the "remaining assumption binder types" by
**zeta-substituting the let-param bodies** (equivalently, comparing over the **smashed / expanded**
telescope `smash_context [] (ind_params ,,, ind_indices)`, not the raw context with `vdef` decls
intact). A naive K1 that iterated the raw telescope and compared a later binder's type as the raw
let-**variable** (the de Bruijn ref to `C`, syntactically identical on both sides) would (i) be
de-Bruijn-ill-formed and (ii) accept trivially where the kernel, after zeta, compares
`E : Type@{w1}` vs `Type@{w2}`. The typing guard of (b) already prevents an *unsound* outcome on
well-typed inputs, but the plan should state the zeta explicitly so no implementation takes the
naive path.

**Plan §3 K1 row currently says** clause (1) compares the remaining binder types "instantiated at
`u` and `u'` and with each side's **present arguments** substituted for the earlier binders" — that
covers substituting the *applied* args, but **not** zeta of **let bodies** into later decls.
**Recommendation:** amend the K1 row (and the F-8 note) to read "K1 zeta-reduces the parameter/arity
telescope (substitutes let-bound parameter bodies) before comparing the remaining assumption binder
types — equivalently, compares over `smash_context`'d `ind_params ,,, ind_indices`." With that
clause, K1 is sound wrt let-bound parameters (measured) and strictly less complete than the kernel
(documented, safe under C).

## Candidates ruled out

1. **Unsound-accept via a dead let-universe.** Ruled out: kernel drops it and accepts, K1 doesn't
   see it and accepts — agreement, and nothing is refused to be "wrongly accepted". (`a_diffw_k`.)
2. **Unsound-accept via a let-universe on the head/conclusion.** Ruled out: cumulativity variance
   governs it on both sides. (`c_diffw_k`.)
3. **Unsound-accept via a let-universe in a live binder type.** Ruled out: Π-domain invariance makes
   the two under-applied heads differ in type; the kernel refuses to even form the comparison
   without `w1=w2` (`exact_no_check` cannot bypass it). (`b_diffw`, `b_diffw_k`, positive control
   `b_pos`.)
4. **Loop / non-termination on a let-param term.** Not applicable to K1's clause (1)/(2): they are a
   decidable `eqb_term_upto_univ` over a finite instantiated telescope plus a finite instance
   comparison — "no recursive machine call" (plan K1 row). No fixpoint/unfolding is entered, so no
   loop surface exists in the let-param path.

## Verdict

**No counterexample.** Let-bound inductive parameters cannot make the checker's K1 accept a
conversion the kernel refuses (measured for dead and head-instance lets; forced by Π-domain
invariance for binder lets, measured). F-8 is incompleteness-only and safe under decision C,
**provided** the K1 row states the zeta-substitution clause above (the one concrete change this
investigation asks of the plan). Probe preserved at `lanes/eta/k1_letparam_probe.v`; verdicts in
`/mnt/frac/work/arity-scope/eta/out/k1_letparam-v{3,5,6}.out` and `k1_pos.out` on bet64-mem.
