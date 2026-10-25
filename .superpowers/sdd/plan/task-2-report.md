# Task 2 — R1 report

Status: **DONE.**

## Commit 1: `bd0deb5a` — Fix quoter cache and declaration state

Files: `quoter.ml`, `g_template_rocq.mlg`, `g_metarocq_safechecker.mlg`, `safechecker_test.v`.

## Commit 2: `2470a01e` — Fix scope propagation, recursive-declaration fixture, and archive red evidence

Files: `quoter.ml`, `constr_quoter.ml`, `g_template_rocq.mlg`, `safechecker_test.v`.

## Commit 3: `7227c2bf` — Drop corpus-specific names from comments

Files: `quoter.ml` (coordinator comment rename).

## F8/D3 closure: design property, not a discriminating regression

The original F8 defect (`astra-deep-review.md:153-163`) required four separate mutable refs (`current_decl_name`, `current_local_scope`, `current_quote_dependencies`, `declarations_in_progress`), where name and scope were restored only on success while dependencies and in-progress were restored on both exits. A nonrecursive `tmQuote` call (which does not go through `quote_term_rec`'s reset) could then read the leaked name and scope.

The refactored code eliminates this partial-restoration path by construction:

- All four fields are now in one `declaration_state` record (`quoter.ml:339-344`).
- `with_declaration_state` saves and restores the complete record on both normal return and exception (`quoter.ml:354-364`).
- Every `quote_term` call wraps its uncached path in `with_declaration_state` (`quoter.ml:1180-1182`), so even if an inner `quote_declaration` boundary were removed, the enclosing term wrapper restores the full state when any exception escapes.
- `quote_term_rec` also resets all state at entry (`quoter.ml:1655-1672`).

There is no single-revert mutant of the new code that can expose the original partial-restoration leak through any external entry point. The fixture (`test_declaration_state_restore`) is retained as an **integration smoke test** that verifies the hook-through-`quote_term_rec` → `quote_declaration` → nonrecursive `quote_term` path exercises the production state boundary. It is not a discriminating red-to-green regression, and no red-to-green claim is made for it. The earlier report's attribution of the `template_list_prod` failure to cross-quoter state leaking is withdrawn: the Constr and Ast quoter functor instances have separate `current_declaration_state` references.

## Red-to-green evidence (four discriminating causes)

| Regression | Red output (`merged/logs/r1/red/r1-r2/red-suite.log`) | Green output (`merged/logs/r1/green/green-suite.log`) |
|---|---|---|
| Cache typing flags | `Cache reused a quotation across changed typing flags.` | `Cache typing-flag regression passed.` |
| Ambient graph | `constraints not satisfiable` | `Environment is well-formed` |
| Scope cache | `Scope-dependent parent cache stored no scope identity.` | `Scope-dependent cache regression passed.` |
| Timeout | `Fresh upper-bound pass swallowed Control.Timeout.` | `Fresh upper-bound timeout regression passed.` |

Red image: `frac-v12-r1-r2-red` (`sha256:39fde2481159189d4f024c83a5fbe48470357331930b19e5a328a912118ff7a1`). Source and image manifests: `merged/logs/r1/red/r1-r2/red-source.manifest`, `red-image.manifest`.

## VM lifecycle

- `frac-metarocq-r188` started `2026-10-25T13:43:50Z`, stopped `2026-10-25T15:21:10Z`, restarted `2026-10-25T15:22:30Z`, left running for coordinator guard test.
