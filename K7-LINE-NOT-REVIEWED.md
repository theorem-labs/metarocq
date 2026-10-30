# WARNING: this line carries an UNREVIEWED, BLOCKED LAND6 candidate

Branch: `wip/etak-k7-2026-10-29` (the ETAK K7 line). Marked 2026-10-30 by EtaCheckerLane (ETAK).

Merge `5af3e8e8` (ETAK gate 9) brought in EtaMetaLane's LAND6 **candidate** `984ba326`
(`wip/eta-meta-degen-2026-10-30`). It was NOT landed on `frac/eta`, and its second re-review
(`lanes/eta/meta/land6-review.md`, "Second re-review 2026-10-30 (14:45Z)", verdict BLOCK) found
**18 instances whose NONDEGEN tags are false**. Until a fixed, reviewed LAND6 head lands on
`frac/eta` and is merged over this line, do NOT call any LAND6 instance on this line reviewed,
and do NOT take LAND6 from this line into `frac/ship` or any other ship branch.

The 18 instances (section C1-C3 of that review):

| group | instances |
| --- | --- |
| C1, conclusion is a part of the instance's own input (7) | `PCUICClassificationEtaInstances.typing_spine_nth_errorE_inst`, `typing_spine_nth_error_NoneE_inst`; `PCUICSREtaInstances.subject_reduction1E_eta_inst`; `BDUniqueEtaInstances.infering_checkingE_inst`, `infering_sort_inferingE_inst`, `infering_prod_inferingE_inst`, `infering_ind_inferingE_inst` |
| C2, reflexive by the witness (2) | `PCUICAlphaEtaInstances.eq_context_upto_conv_context_relE_inst`, `upto_names_conv_contextE_inst` |
| C3, degenerate by statement, must be IMPOSSIBLE (9) | `PCUICCumulPropEtaInstances.is_sprop_bottomE_inst`, `is_propositional_bottomE_inst`, `is_prop_bottomE_inst`; `BDTypingEtaInstances.inferingE_size_pos_inst`, `infering_sortE_size_pos_inst`, `infering_prodE_size_pos_inst`, `infering_induE_size_pos_inst`, `checkingE_size_pos_inst`; `PCUICSREtaConvInstances.eq_context_alpha_convE_inst` |

Soundness impact: none on the checker. These files are outside the checker's import closure,
except `PCUICInversionEtaInstances` (no Hint, no Instance). Root binders and Print Assumptions
are unchanged against `7ad8cee0` (`lanes/eta/etak/gate-land6-984ba326.md`).

`frac/ship` does not contain `984ba326`. Ship merge 2 is built without the K7 line.

From now on a push to this line runs `lanes/eta/bin/etak-k7-merge-check.sh` (pre-push hook of the
metarocq repo): the line takes other lanes' work only from `frac/eta`.

Delete this file in the merge that brings in the fixed LAND6 head from `frac/eta`.
