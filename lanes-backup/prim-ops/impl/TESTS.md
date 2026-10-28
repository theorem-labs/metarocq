# BET-319 row P: the test table

> **Row P's branch is `frac/prim-ops-PrimTests2` @ `84a1a856`.** Merge that one.
> `frac/prim-ops-PrimTests` @ `37d6f6d3` and `frac/prim-ops-PrimTests-run` are **STALE** —
> three amends behind, without Part T, without `po_C3`, and with the Part E proof pinned to
> row F's superseded constructor shape — and **must not be merged**. They are left in place
> deliberately, as the record of what row P looked like before those were added
> (lane lead's ruling: no force-push, no deletion; the fix is `OWNERS.tsv`, which now
> records `…-PrimTests2`).
>
> By hash, `84a1a856` is the row-P commit `25168711` **plus** a merge of the lane line
> `frac/prim-ops` `97f339f7`, so it also touches `common/theories/Environment.v` and
> `pcuic/theories/PCUICPrimitiveRed.v` — not only the three test files. That lane line is
> stale (it predates trunk tip `1a0d825e`), but it is harmless in the composition: B2
> brings `1a0d825e` and the newer trunk wins on both files, which is why the merge was
> conflict-free.

Owner: PrimTests. Files: `test-suite/prim_ops.v`, `test-suite/prim_ops_spec.v`,
`test-suite/_RocqProject.in`. Row-P commit `25168711`; branch tip `84a1a856`.
Design: `lanes/prim-ops/design-opt1.md` §9.

Every case below has an expected verdict **per set of §8 rows landed**, and an observed
verdict per measured state. The machine-readable form is
[`tests-expected.tsv`](tests-expected.tsv); the gate that enforces it is
[`check-tests.sh`](check-tests.sh). **This file is the prose form of that table, not a
second source of truth**: change `tests-expected.tsv` and this file together.

## The gate

```
lanes/prim-ops/impl/check-tests.sh <tag> "<rows landed>" [<commit>]
# e.g. before merging row H into frac/prim-ops:
lanes/prim-ops/impl/check-tests.sh h1 "A B C D E F G K O" <tip of frac/prim-ops-HM>
```

It streams `git archive <commit>` to bet64-mem (nothing bulky is written on
sami-rocqperf), builds the tree in `/mnt/frac/work/prim-ops/trees/tests`, runs both test
files through `rocq repl`, reads **one named verdict per case** out of the two logs, and
compares each with what `tests-expected.tsv` requires for the rows named on the command
line. It exits:

- `0` — every case as expected;
- `1` — at least one case off. Each offender is printed as
  `FAIL <file>/<case> … GREEN-BEFORE-ITS-ROW | STILL-RED-AFTER-ITS-ROW | MUST-NEVER-TURN`,
  which is the finding to report to the lane lead;
- `2` — the run itself failed (no tree, build failure, no verdicts at all).

How a verdict is read. In `prim_ops.v` the cases are the `MetaRocq SafeCheck` commands in
file order, and the verdicts are the messages the run prints in the same order
(`accepted` / `refused` / `failholds` / `notfailed`). In `prim_ops_spec.v` each case
prints its own named verdict, `po_<case>_ok = true|false`, so the pairing is by name and
not by order; `true` is `ok`. Each case also has an assertion `po_<case>_holds`, which is
what makes `make -C test-suite` fail; the printed verdict is what makes a *red* run
readable case by case.

**A refusal is checked for its reason, not only for being a refusal.** Before the
environment condition exists, every doctored environment is refused anyway as soon as the
program contains a statement that needs an operation to reduce. Every control in
`prim_ops_spec.v` therefore asks the refusal to name the declaration it came from —
`toplevel` for the retroknowledge-only conditions, the kername of the declaration whose
clause is violated otherwise — and each subject has a program of its own in which it is
the only declaration that can fail.

## Row sets

| name | rows | from |
|---|---|---|
| step 3 | A B C D E F G H K O | design §11 item 3, "first end-to-end build" |
| step 4 | A B C D E F G H I K O Q Q2 | design §11 item 4, the machine fires |
| step 4J | A B C D E F G H I J K O Q Q2 | design §11 item 4, conversion fires before answering no |

## States measured

| state | what is in the tree | image / commit | when (UTC) |
|---|---|---|---|
| S0 | no BET-319 row at all | image `integ-outcome` | 2026-10-27 15:52 |

`prim_ops_spec.v` cannot run at S0, and cannot run on any tree before the safechecker
builds. At S0 its whole column is "not runnable", which the gate reports as `notok` for
every case — the correct reading, since no control of that file holds there.

### The gate composition (PrimSpec2 owns it; this is the authoritative list)

trunk `1a0d825e` (A, B, C, extendsA, the Q/Q2 helpers) ⊕ B2 `34e5b87f` ⊕ DE `7405dd0d`
⊕ HM `40b3bf95` ⊕ FG `c86ebbac` ⊕ KO `464246cb` ⊕ L `7e7dda1d` ⊕ PrimChecker `82947fb6`
⊕ P `25168711`. All of them merge with no conflict; my composition tip is `61aaf5dd`.
`frac/prim-ops-extendsA` must **not** be merged separately: B2 is built on the trunk
commit that already carries it, so it arrives transitively (verified:
`git merge-base --is-ancestor 999e5334 61aaf5dd`).

### Why the gate cannot run yet — two frontiers, both real

They are not rival measurements; they are different target sets, and **both must clear**.

**1. In `make all` order the first break is `listDec`, in `template-rocq`.** On composition
tip `61aaf5dd` (`out/compose2-build.log`, per-directory logs in `out/compose2/`):
`utils_STATUS=0  common_STATUS=0  template-rocq_STATUS=2`, everything after it 2 by
dependency. Verbatim:
`make[1]: *** No rule to make target 'gen-src/listDec.cmx', needed by 'gen-src/environmentTyping.cmx'.`
Cause: row H decides `Retroknowledge.wf_retro`, whose first conjunct is
`NoDup (map fst retro_ops)` (`common/theories/Environment.v:308`); `EnvironmentTyping.v:4`
therefore carries `From Stdlib Require Import ListDec.` and `dec_wf_retro` calls
`ListDec.NoDup_dec Kername.eq_dec`. But `gen-src/listDec.ml{,i}` is absent from
`template-rocq/_PluginProject.in` and `ListDec` from `gen-src/metarocq_template_plugin.mlpack`
— the design §5 step already applied to `PrimitiveOps` (`_PluginProject.in:217-220`,
mlpack `:106`; `List0` is the same shape at `:117-118`/`:11`). **Settled: Main ruled on
2026-10-28 "remove the dependency, do not add the plumbing", so this is ROW H's fix, not
row K's** — the plumbing route is explicitly not being taken. PrimEnv2 has replaced the
call with `dec_NoDup_kername` over `Kername.eq_dec` and reports `common STATUS 0` with
zero `listDec` references; **not yet landed**. PrimQuoter2 verified the dependency has a
single source: `EnvironmentTyping.v:4` and `:1290`, with `open ListDec` appearing only in
`gen-src/environmentTyping.ml{,i}`, whose `.d` files are the only things wanting
`gen-src/listDec.cmx`. `frac/prim-ops-KO` stays at `464246cb`. **Do not re-run the
composition until PrimEnv2's row-H commit lands.**

**2. Within `pcuic` the first break is `PCUICNormal.v:465`** (`[Focus] Wrong bullet`), with
everything green through `PCUICSR` (PrimSpec2, `out/dehm-k8.log`, a `common`+`pcuic`-only
build, which never builds `template-rocq` and so could not have seen `listDec`). **Row F is
not landed**: `frac/prim-ops-FG`'s tip `c86ebbac` is row G, and `whnf_whne_dec`'s
primitive case is unfinished.

**3. Expected next, once `listDec` clears**: `quotation` STATUS 2,
`ToTemplate/QuotationOf/Common/EnvironmentTyping/Sig.v:98: Cannot import functor … Sig.GM`.
Landed HM `40b3bf95` touches no `quotation/` file; PrimEnv2's wip `17209e31` has the four
that fix it (PrimSpec2).

**4. A claim I made and withdrew: the safechecker plugin's lists.** I predicted that
`safechecker-plugin`'s `_PluginProject.in`/mlpack would need `listDec`/`primitiveOps` too,
and the lane lead first reported it as verified. **Both of us were wrong to call it
verified, and the claim is withdrawn.** A grep showing the modules absent from a list is
not evidence that they are needed: `out/compose2/safechecker-plugin.log` never reached
extraction at all — it stopped at `No rule to make target '../pcuic/theories/Bidirectional/BDToPCUIC.vo'`,
behind the pcuic/row-F frontier — so no missing-module error could have surfaced
(PrimQuoter2). Under design change-log v10, template-provided `Common` modules resolve over
`OCAMLPATH` and are *correctly* absent from that mlpack, so absence is probably right.
`listDec` becomes moot there once row H lands; `primitiveOps` is PrimQuoter2's open check,
to be settled by an end-to-end build once `pcuic` compiles, not by reading a list.

So `safechecker` and `safechecker-plugin` are not reachable, and neither test file can run.

### The pre-H state is NOT separable — only the with-H state will be measured

I had planned a second run with `frac/prim-ops-HM` dropped, to show the D\* and TR\*
controls read RED before row H rather than being green for the wrong reason. That is not
possible, for two independent reasons (PrimSpec2):
- row G's `sr_prim_op` calls HM's `lookup_on_global_env_prim_decl`;
- B2's two hunks destructure `on_global_env` as a **triple**, a shape only HM's
  `wf_retro` conjunct creates.
Dropping HM therefore breaks FG and B2 at compile time: the result is a broken tree, not a
pre-H reading. **Consequence for the reader: for D1-D11 and TR1-TR5 the "before" column is
reasoned, not measured.** What still backs them is that each asserts the refusal's
declaration id rather than the mere fact of refusal, so a refusal arriving by any other
route does not satisfy them.

## `test-suite/prim_ops.v`

| case | what it pins | turned by | before | after | S0 |
|---|---|---|---|---|---|
| `po_chunk_bytes` | LemmaPin_14's `wseg_fast` → `chunks_ok`; `length`, then `to_Z`'s per-bit `eqb (land i 1) 0` — arguments that are not literals | step 4 | refused | accepted | refused ✓ |
| `po_decode_ok` | LemmaPin_4's bounds and nybble tests: `of_Z` (`lsl`, `lor`), `length`, `ltb`, `eqb`, `sub`, `get`, `leb` | step 4 | refused | accepted | refused ✓ |
| `po_byte_digit` | LemmaPin_1's decoded byte: `get`, `to_Z` | step 4 | refused | accepted | refused ✓ |
| `po_fetch_word` | the post-route-1 wall `Opendnp3.Clf0Code.F_11350`: two bytes composed little-endian | step 4 | refused | accepted | refused ✓ |
| `po_eq_refl_args` | `eqb` on equal arguments | step 3 | refused | accepted | refused ✓ |
| `po_leb_equal` | `leb 2 2 = true` — separates `leb` from `ltb` | step 3 | refused | accepted | refused ✓ |
| `po_ltb_equal` | `ltb 2 2 = false` — separates `ltb` from `leb` | step 3 | refused | accepted | refused ✓ |
| `po_ltb_unsigned` | the comparison is unsigned | step 3 | refused | accepted | refused ✓ |
| `po_leb_unsigned` | the same for `leb` | step 3 | refused | accepted | refused ✓ |
| `po_sub_wraps` | `sub 0 1 = max_int` | step 3 | refused | accepted | refused ✓ |
| `po_land_masks` | `land 6 3 = 2` | step 3 | refused | accepted | refused ✓ |
| `po_lor_sets` | `lor 6 3 = 7` | step 3 | refused | accepted | refused ✓ |
| `po_lsl_63` | shift by 63 | step 3 | refused | accepted | refused ✓ |
| `po_lsr_63` | shift by 63 | step 3 | refused | accepted | refused ✓ |
| `po_get_out_of_range` | `get` out of range is 0 | step 3 | refused | accepted | refused ✓ |
| `po_lsl_shifts` | `lsl 1 1 = 2` — separates `lsl` from `lsr` (the shift-by-63 pair does not) | step 3 | refused | accepted | refused ✓ |
| `po_lsr_shifts` | `lsr 2 1 = 1` — the other half of that separator | step 3 | refused | accepted | refused ✓ |
| `po_length_empty` | `length "" = 0` | step 3 | refused | accepted | refused ✓ |
| `po_unregistered_lxor` | `lxor` is outside the table | never | failholds | failholds | failholds ✓ |
| `po_unregistered_ltsb` | `ltsb` is outside the table | never | failholds | failholds | failholds ✓ |
| `po_unregistered_asr` | `asr` is outside the table | never | failholds | failholds | failholds ✓ |
| `po_conv_same_op` | `eqb 1 2 = eqb 2 1` — conversion's same-constant `no` branch must fire first | step 4J | refused | accepted | refused ✓ |
| `po_conv_diff_op` | `eqb 1 1 = leb 1 1` — conversion's two-constants `no` branch | step 4J | refused | accepted | refused ✓ |
| `po_saturated_by_beta` | `(fun f => f 2) (eqb 1) = false`: beta makes the application saturated | step 3 | refused | accepted | refused ✓ |
| `po_beta_arg` | `eqb ((fun x => x) 1) 2 = false`: the argument is a beta redex, so no weak-head constructor may cover the application and the machine must reduce the argument first (§6's fourth constructor; statement from ArityLane.PrimWhnfSR) | step 4 | refused | accepted | refused ✓ |
| `po_stuck_reflexive` | `forall x, eqb x 1 = eqb x 1`: a stuck application convertible to itself | never | accepted | accepted | accepted ✓ |
| `po_no_computation` | `eqb x x = eqb x x`: no computation at all | never | accepted | accepted | accepted ✓ |

**An acceptance of any part-C case at any state is a finding**: it means a quoter arm maps
a kernel operation the table does not contain.

## `test-suite/prim_ops_spec.v`

| case | §9.2 item | what it pins | turned by | before | after | S0 |
|---|---|---|---|---|---|---|
| `po_names_found` | — | every kername and inductive the controls patch was found: a control cannot pass by patching nothing | never | ok | ok | not runnable |
| `po_A0` | — | the program that computes nothing is accepted: the harness itself is sound | never | ok | ok | not runnable |
| `po_A1` | — | positive twin of `po_C1`: `ltb 2 2 = false` accepted | step 3 | notok | ok | not runnable |
| `po_A2` | — | positive twin of `po_C2`: `eqb (lsl 1 1) 2 = true` accepted | step 3 | notok | ok | not runnable |
| `po_A3` | — | positive twin of `po_B2`: `eqb 1 = eqb 1` accepted, syntactically, at every state | never | ok | ok | not runnable |
| `po_A4` | — | positive twin of `po_B3`: the beta-argument application accepted | step 4 | notok | ok | not runnable |
| `po_B1` | first bullet | `po_ltb_equal`'s statement replaced by `ltb 2 2 = true`: refused at that declaration, not convertible | never | ok | ok | not runnable |
| `po_B2` | D2 control | an `eq_refl`'s statement replaced by `eqb 1 = eqb 2`: two unsaturated applications, conversion must answer no and prove it | never | ok | ok | not runnable |
| `po_B3` | — | the same for the beta-argument application | never | ok | ok | not runnable |
| `po_C1_moved` | — | the quoter really put `ltb` in the table, so the swap below moved something | K | notok | ok | not runnable |
| `po_C1` | swap | `ltb`'s entry moved to `Int63le`: `ltb 2 2 = false` must now be refused | never | ok | ok | not runnable |
| `po_C2_moved` | — | the same for `lsl` | K | notok | ok | not runnable |
| `po_C2` | swap | `lsl`'s entry moved to `Int63lsr`: `eqb (lsl 1 1) 2 = true` must now be refused | never | ok | ok | not runnable |
| `po_C3` | — | the table is keyed on the declaration the quoter reads, not on a type: a user axiom of `eqb`'s type is **not** registered while the real `eqb` is (`axiom_lookup_none`, PrimQuoter2) | K | notok | ok | not runnable |
| `po_D1` | — | two operations on one constant: the table's kernames must be distinct | H | notok | ok | not runnable |
| `po_D2` | (ii) | an operation registered on a constant that has a body | H | notok | ok | not runnable |
| `po_D3` | (i) | `eqb` registered with the declared type `int -> int -> int` | H K | notok | ok | not runnable |
| `po_D4` | (iv) | `retro_bool` at packet 1 of a two-packet mutual block whose packet 1 has a constructor with an argument | H | notok | ok | not runnable |
| `po_D5` | (ix) | `retro_bool = None` with `eqb` registered: the result has nothing to be read back to | H K | notok | ok | not runnable |
| `po_D6` | (vi) | `retro_int63 = retro_string`, with the wrong-tag saturated application as the term | H | notok | ok | not runnable |
| `po_D7` | (vii) | `retro_bool` naming a kername declared nowhere | H K | notok | ok | not runnable |
| `po_D8` | (iii) | a three-constructor inductive registered as `retro_bool` | H | notok | ok | not runnable |
| `po_D9` | (viii) | two constructors named neither `true` nor `false` | H | notok | ok | not runnable |
| `po_D10` | (viii) | two constructors named `false` and `true` **in that order** — the orientation separator, the slice-1 analogue of the `Lt`/`Gt` separators | H | notok | ok | not runnable |
| `po_D11` | (v) | `retro_int63` naming a constant with a body, so `primitive_invariants` of the integer tag fails | H K | notok | ok | not runnable |
| `po_E1` | §6 | the weak-head constructor for a saturated application with a rigid non-literal argument (`whnf_primapp_rigid`). No Rocq definition produces such a term — the argument is ill-typed — so it is a unit lemma over a hand-written environment | F | notok | ok | not runnable |
| `po_TA1` | row H pt 2 | **completeness**: a delta-alias in a domain (`po_myint` unfolds to `int`). Must stay **accepted** | never | ok | ok | not runnable |
| `po_TA2` | row H pt 2 | **completeness**: a delta-alias in the codomain. The real `PrimString.get`, whose stored codomain is the definition `char63`, takes this route | never | ok | ok | not runnable |
| `po_TA3` | row H pt 2 | **completeness**: a beta redex in a domain | never | ok | ok | not runnable |
| `po_TA4` | row H pt 2 | **completeness**: a `let` in a domain | never | ok | ok | not runnable |
| `po_TA5` | row H pt 2 | **completeness**: named binders — every real operation's kernel type has them (`x`, `y`), so the whole table depends on this one | never | ok | ok | not runnable |
| `po_TR1` | row H pt 2 | a wrong argument type (`string` where the tag is `primInt`) | H K | notok | ok | not runnable |
| `po_TR2a` | row H pt 2 | too few arguments for the operation's arity | H K | notok | ok | not runnable |
| `po_TR2b` | row H pt 2 | too many | H K | notok | ok | not runnable |
| `po_TR3` | row H pt 2 | an irrelevant first binder (buildable only as an AST patch, `po_irrelevant`) | H K | notok | ok | not runnable |
| `po_TR4` | row H pt 2 | a wrong result type (`int` where the shape is `SBool`) | H K | notok | ok | not runnable |
| `po_TR5` | row H pt 2 | a result inductive of `bool`'s shape that is **not** the registered one | H K | notok | ok | not runnable |
| `po_E2` *(pending)* | §6 counterexample | **the term that refuted version 7's single `cannot_fire` constructor** (from PrimWhnfSR2): `eqb ((fun x => x) 1) 2`, i.e. `mkApps (tConst eq u) [tApp (tLambda na int (tRel 0)) (tPrim 1); tPrim 2]`. Statement: `whnf RedFlags.default Σ Γ t -> False`. It is written with `-> False`, not `~ whnf …`, because `whnf` is in `Type` and `~` would be a universe inconsistency (`Type <= Prop`). PrimWhnfSR2's compiler found this. The statement is false under v7, where the non-literal argument made `t` neutral. It is true under the four constructors, because the argument is a beta redex, so neither `whnf_primapp_rigid` nor `whne_primapp_stuck` applies. This is the row-F test. A red1 step alone would not do, because it holds under v7 too. **Lemma agreed with PrimWhnfSR2** (`PCUICNormal.v`, Section Normal): `whnf_primapp_beta_arg Γ c u decl op na A b x ls rest : RedFlags.delta flags = true -> RedFlags.beta flags = true -> lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = None -> prim_op_of Σ c = Some op -> #|ls| + S #|rest| = arity op -> whnf Γ (mkApps (tConst c u) (map term_of_lit ls ++ tApp (tLambda na A b) x :: rest)) -> False`. The two flag premises are needed because without delta the head is neutral and without beta the redex is a whnf; both hold by `reflexivity` at `RedFlags.default`. It is derived from `not_whnf_primapp_arg` and `not_whnf_beta`. On PrimWhnfSR2's combined tree the lemma and both helpers compile, but `PCUICNormal.vo` as a whole does not yet: `whnf_whne_dec` is unfinished. **Not pinned yet**: I pin it when PrimWhnfSR2 sends the hash of the row-F commit that builds. Surface twin: `po_beta_arg` in `prim_ops.v` | F | notok | ok | not written |

## Not covered by slice 1

The two `compare` `Lt`/`Gt` separators of §9.2 are **slice 2** and are not in either file.
Slice 1's `prim_op` has no `Int63compare` or `Stringcompare`, no `SCmp` shape and no
`retro_cmp` field (`common/theories/PrimitiveOps.v:21-31`, `common/theories/Environment.v:40-61`),
so neither control can be written against this branch. The lane lead confirmed this scope
call. **Slice 1's gate therefore does not cover them, and a green run of `check-tests.sh`
is not evidence that the two hand-written `compare` realizers have the right orientation.**
Their slice-2 statements, to be added verbatim when `SCmp` exists:

```coq
Definition po_cmp_lt : PrimInt63.compare 0 Uint63Axioms.max_int = Lt := eq_refl.
Definition po_cmp_gt : PrimInt63.compare Uint63Axioms.max_int 0 = Gt := eq_refl.
Definition po_scmp_lt : PrimString.compare "a"%pstring "b"%pstring = Lt := eq_refl.
Definition po_scmp_gt : PrimString.compare "b"%pstring "a"%pstring = Gt := eq_refl.
```

The slice-1 analogue that *is* covered is `po_D10`: the boolean readback is positional, and
`po_D10` is the control that an environment whose two constructors are named `false` then
`true` is refused.

The machine controls of §9.2 (`eqb 1` is whnf and not neutral; `eqb x 1` is neutral; under
`nodelta` the application is not reduced) are not in this file yet: they are unit lemmas
over row F's constructors and row I/Q's `reduce_stack`, and go in beside `po_E1` when
those rows land.

## Open points to watch

1. **Which row turns `po_saturated_by_beta`.** The table follows design §11 item 3, which
   says §9.1 goes green at the first end-to-end build "except the four part-A
   reproductions … and `po_conv_same_op`/`po_conv_diff_op`". That puts
   `po_saturated_by_beta` at step 3 although its argument needs beta before the operation
   fires — the same shape as `po_beta_arg`, which row F's owner (ArityLane.PrimWhnfSR)
   places at step 4. One of the two is wrong. The gate will say which at the first state
   that has step 3 and not step 4, and that answer is a finding for the lane lead either
   way: if `po_saturated_by_beta` is still refused at step 3, design §11 item 3 is wrong;
   if it is accepted, `po_beta_arg`'s row set is wrong.
2. **The part-B row set.** Step 3 has no row I or Q, so for the fourteen literal-argument
   cases to be accepted, firing must reach them through conversion rather than through the
   machine. If they are still refused at step 3 the design's §11 item 3 is optimistic and
   the table moves to step 4; that too is a finding, not a silent edit.

## Findings reported so far

None. S0 matched `tests-expected.tsv` in all 27 cases of `prim_ops.v`.
