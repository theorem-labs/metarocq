# WARNING: this line carries an UNREVIEWED, BLOCKED LAND6 candidate

Branch: `wip/etak-k7-2026-10-29` (the ETAK K7 line). Marked 2026-10-30 by EtaCheckerLane (ETAK);
AMENDED 2026-10-30 ~17:50Z after Land6Review's final review of the fixed head `ff20a493`.

Merge `5af3e8e8` (ETAK gate 9) brought in EtaMetaLane's LAND6 **candidate** `984ba326`
(`wip/eta-meta-degen-2026-10-30`). It was NOT landed on `frac/eta`. Two reviews in
`lanes/eta/meta/land6-review.md` found **45 instances on this line whose NONDEGEN tags are false**:
the 18 of the second re-review (14:45Z, C1-C3) and 27 more found by the final review (17:40Z, B1-B2),
which were unchanged from `984ba326` to `ff20a493` and so are on this line too. **The 45 are what
review has FOUND, not what the line contains**: three full passes found 16, 17, then 27, so more may
exist. A NONDEGEN tag is a reader judgment, and the measured reader miss rate is in
`lanes/eta/meta/reader-catch-rate.tsv`. Until a fixed LAND6 head lands on `frac/eta` and is merged
over this line, do NOT call any LAND6 instance on this line reviewed, and do NOT take LAND6 from this
line into `frac/ship` or any other ship branch.

## Second re-review (14:45Z), 18 rows (all closed at `ff20a493` per the 17:45Z row-by-row verdict; still OPEN on this line)

| group | instances |
| --- | --- |
| C1, conclusion is a part of the instance's own input (7) | `PCUICClassificationEtaInstances.typing_spine_nth_errorE_inst`, `typing_spine_nth_error_NoneE_inst`; `PCUICSREtaInstances.subject_reduction1E_eta_inst`; `BDUniqueEtaInstances.infering_checkingE_inst`, `infering_sort_inferingE_inst`, `infering_prod_inferingE_inst`, `infering_ind_inferingE_inst` |
| C2, reflexive by the witness (2) | `PCUICAlphaEtaInstances.eq_context_upto_conv_context_relE_inst`, `upto_names_conv_contextE_inst` |
| C3, degenerate by statement, must be IMPOSSIBLE (9) | `PCUICCumulPropEtaInstances.is_sprop_bottomE_inst`, `is_propositional_bottomE_inst`, `is_prop_bottomE_inst`; `BDTypingEtaInstances.inferingE_size_pos_inst`, `infering_sortE_size_pos_inst`, `infering_prodE_size_pos_inst`, `infering_induE_size_pos_inst`, `checkingE_size_pos_inst`; `PCUICSREtaConvInstances.eq_context_alpha_convE_inst` |

## Final review (17:40Z), 27 rows (OPEN on this line AND at `ff20a493`)

| group | instances |
| --- | --- |
| B1, degenerate: the lemma's work is the identity on the witness and the conclusion is a piece of an input (13) | SR identity-β family: `PCUICSREtaInstances.sr_red1E_beta_inst`, `subject_reductionE_inst`, `subject_reduction1_closedE_inst`, `subject_reduction_closedE_inst`, `isType_red1E_inst`, `isType_redE_inst`, `wf_local_red1E_inst`, `wf_local_redE_inst`, `lift_judgment_SRE_inst`; `PCUICClassificationEtaInstances.subject_reduction_evalE_inst`; `PCUICValidityEtaInstances.isType_Sort_invE_inst`; `PCUICCumulPropEtaInstances.cumul_prop_cumul_pb_lE_inst`, `cumul_prop_prod_invE_inst` |
| B2, target statement-trivial, must be IMPOSSIBLE (14) | `BDTypingEtaInstances.JoinE_ws_cumul_pbE_inst`, `checkE_Cumul_ws_inst`, `All2_ws_cumul_pbE_JoinE_inst`; `BDFromPCUICEtaInstances.conv_checkE_eta_inst`, `conv_lift_judgmentE_inst`, `conv_lift_judgment_univE_inst`, `ws_cumul_ctx_pbE_vass_inst`; `BDToPCUICEtaInstances.wf_local_local_relE_inst`; `PCUICCumulPropEtaInstances.cumul_prop_is_openE_inst`; `PCUICAlphaEtaInstances.type_Cumul'E_inst`; `PCUICValidityEtaInstances.type_ctx_wf_univE_inst`; `PCUICPrincipalityEtaInstances.isWfArity_sortE_inst`; `PCUICProgressEtaInstances.declared_constructor_ind_declE_inst`; `PCUICSREtaInstances.isType_prim_tag_constantE_inst` |

Soundness impact: none on the checker. These files are outside the checker's import closure,
except `PCUICInversionEtaInstances` (no Hint, no Instance). Root binders and Print Assumptions
are unchanged against `7ad8cee0` (`lanes/eta/etak/gate-land6-984ba326.md`) and at the trial merge
of `ff20a493` (`lanes/eta/etak/gate-land6fix-ff20a493.md`).

`frac/ship` does not contain `984ba326`.

A push to this line runs `lanes/eta/bin/etak-k7-merge-check.sh` (pre-push hook of the metarocq
repo): the line takes other lanes' work only from `frac/eta`.

DELETION RULE (lead 2026-10-30 17:45Z; condition (2) restated 19:05Z): delete this file in the K7 merge
of a LAND6 head that has landed on `frac/eta`, ONLY if:
(1) THE GATE: that head's FOCUSED review (every changed instance, plus a seeded sample of n = 60
    unchanged instances) names each of the 45 rows above CLOSED (rebuilt) or TRUE (IMPOSSIBLE retag).
    Any row it does not close is NAMED in an amended marker, never dropped. As of `11092806`,
    `PCUICValidityEtaInstances.isType_Sort_invE_inst` is NOT CLOSED: every typing of `tSort s` stores
    `wf_sort` in its base `typeE_Sort` and the lemma returns that field, so the row must become IMPOSSIBLE.
(2) A RECORDING DUTY, not a pass mark: the final focused review's sample result (misses of 60, the
    residual, its 95% upper bound, and the seed) is (i) written INLINE in the NONDEGEN header of all 17
    instance files, (ii) recorded in the ledger `dispatch://BET-64/artifact/eta-reader-catch-rate-tsv`,
    and (iii) quoted in the K7 merge body. The three copies must be character-identical (checked before
    the merge); if they ever disagree, the header is authoritative, because it travels with the code.
(3) the landed head's NONDEGEN header says the tag is a reader judgment.
The merge body carries the 45-row table and states that the 45 are what review found, and that the
sample bounds the residual rate, not at zero. If (1) fails, amend this file to the rows that remain;
if only (2) or (3) fails, keep this file in reduced form (no rows, only the sample result and the
reader-judgment statement) until it holds.
