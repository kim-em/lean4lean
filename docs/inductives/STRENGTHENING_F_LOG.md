# Direction F log: consolidation to the sharpest checked statement

Branch `agent/verify-inductives-strengthening3-F` (worktree `lean4lean-strength3-F`), off
`agent/verify-inductives-strengthening3`. Brief: discharge the guard descents that
`cancel_iff_typedFront_B3` (`EtaClosure.lean`) assumes (`UnfoldingCheckDescends`,
`CaseRedexDescends`, `MajorEtaDescends`), restate direction E's spine exposure over the proved
`EtaNE` closure, and assemble the final theorem (`Strengthening/Final.lean`) with its exact
hypothesis list. Files under `Lean4Lean/Theory/Typing/Strengthening/` are at zero `sorry` in every
commit; new work goes to new files (`Descents.lean`, `Final.lean`, ...).

## Step 0: merge of the integration branch

Merged `kim-em/agent/verify-inductives-strengthening3` at 8f0f2206 (fast-forward; mainline's
removal of unused hypotheses, `IsDefEqU.closed_telescope_instOuter` lost its `OnCtx` argument).
`lake build Lean4Lean.Theory` clean after the merge.

## Step 2 (done first, see step 1 for the reason): `CaseRedexDescends` (`Descents.lean`)

`caseRedexDescends : TypedFrontN env → GenericRulesTyped₀ env → CaseRedexDescends` (checked;
axioms `propext`, `Classical.choice`, `Quot.sound`). Contents, following B2's table row for
`ParRed.schema`:

* `source : CaseStep`: the closed typings `lhs/rhs : type` in `Γ` from
  `GenericRulesTyped₀.caseStep_premises` (E); `CaseArguments` by strong induction on the capture
  index: the capture is an argument of one of the two spines of the typed application below
  (`case_capture_wf`, `VExpr.WF.args_of_mkApps`), its specialized domain
  `instantiateParams (domains[j].instL lv) (caps.take j)` is a type below by
  `IsType.instOuter_telescope` over the specialized domain telescope (`caseRule_domains_ctx`:
  `IsType.wrapForalls_inv` of the closed left-hand side's type, `body_exact`), and the above
  typing (`instantiateParams_liftN` with `CaseStep.domains_closed`) is brought down by
  `TypedFrontN.retype`.
* the symbol and length fields are rename-invariant; `guard` is `TypedFrontN.independent`
  between `actual.expr` (typed below by hypothesis) and `rule.lhs lv caps` (typed below by
  `CaseStep.defeq` of the descended step).

So `CaseRedexDescends` is exactly `TypedFront` plus the closed rule typings, as B2 predicted.
