# Goal statement for `agent/verify-inductives`

Paste the block below into `/goal`. It is the standing instruction for every
session on this branch (Kim, 2026-10-06: "Don't stop to ask me questions, get
the entire thing done. We're following Mario's plan.").

Amendments confirmed by Kim on 2026-10-08: item (1) covers the branch's own
development, so the `sorry` declarations inherited from Mario's prototypes
under `Lean4Lean/Experimental/` (present on `master`) are excluded; item (3)
includes canonical `Nonempty`/`Classical.choice` (`VEnv.HasCanonicalChoice`),
because the E1 route replaces declarative strengthening by the
projection-walk corner, proved from choice (both constants are installed by
`Init.Prelude`; realizability `VEnvs.WF.hasCanonicalChoice`). A choice-free
proof is pursued as a bonus on `agent/verify-inductives-strengthening`.
Obligations (a) to (c) below are the ones that were open when the statement
was written; all three are closed on the branch (HANDOFF.md "Final state").

```text
Finish branch agent/verify-inductives of lean4lean (worktree
~/worktrees/lean4lean/lean4lean-agent-verify-inductives; push to remote kim-em).

DONE means all of: (1) `lake build` of the whole project reports zero
"declaration uses sorry" and `grep -rn sorry Lean4Lean` finds none outside
comments, excluding the prototypes under Lean4Lean/Experimental/ inherited
from master (Kim, 2026-10-08); (2) no axioms beyond those already in Verify/Axioms.lean; (3) the
top-level theorem `addDecl.WF_of_canonicalEq` (Lean4Lean/Verify/Environment.lean)
holds with exactly the hypotheses `ves.WF env`, canonical `Eq` present
(`VEnv.HasCanonicalEq` at each safety level), canonical `Nonempty`/
`Classical.choice` present (`VEnv.HasCanonicalChoice` at each safety level;
added by the recorded decision of 2026-10-06, HANDOFF.md) and
`decl.IsModelled env ves`, with no proofs hidden in hypotheses, structure
fields or certificates;
(4) `lake build Lean4Lean.Tests`, `lake build Lean4Lean.Experimental`, the fresh
replays (`lean4lean --fresh Init.Prelude` = 1975, `--fresh Init.Core` = 3953) and
`scripts/check-inductive-audit.py --self-test` and `--require-complete` all pass;
(5) HANDOFF.md describes the final state. Nothing short of this is "done";
never describe a route or phase as done, only as "buildable with hypotheses H".

REMAINING OBLIGATIONS (the only sorries, all in Lean4Lean/Theory/Typing):
(a) `VEnv.WF.headInversion` (HeadInversion.lean): follow Mario's plan, the
    shape logical relation / Coquand-Huber adequacy of Lean4Lean/Experimental/
    ShapeLogRel*.lean and Experimental/UniqueTyping.lean, ported to this
    branch's VExpr (elim, proj, extra rules, K-like Eq.rec, singleton
    families, projections, structure eta, unit-like) and repaired where
    docs/inductives/PHASE1_SPIKE.md shows the checked K/singleton step forces
    equality reflection (cast-pushing reduction inside the relation, or a
    better repair found on the way). Deliver all eight HeadInversion fields.
(b) `strengthening_of_canonicalEq` (UniqueTyping.lean): strengthening for
    environments containing canonical Eq (falsification study first, then
    singleton eta and a conversion-certificate calculus, per
    docs/inductives/BASE_OBLIGATIONS_DESIGN.md section 3). If the study
    refutes it, find the weakest true hypothesis that real environments
    satisfy, restate, record, and continue.
(c) `FullStep.strip` (FullReduction.lean): general confluence (branch
    agent/verify-inductives-cr).

RULES. Never stop to ask Kim a question; make the decision, record it and its
rationale in HANDOFF.md, and continue. No size or time budgets anywhere: agents
run to completion or to a genuine mathematical obstacle (a statement believed
false, or a precisely stated missing metatheorem), and an obstacle means
redesign and continue, not hand back. Opus subagents write, compile and fix all
Lean; the lead directs, checks statements for honesty, and gets second opinions
on designs from Astra (`codex exec -m gpt-6-astra`). If a statement is false or
unprovable, correct it minimally and repair consumers; never weaken
`addDecl.WF_of_canonicalEq` or the generative specification (Theory/Inductive/*)
beyond decisions recorded in HANDOFF.md; never add input-naming hypotheses;
never hide a conjecture in a structure field. The executable must not diverge
from the C++ kernel (no new rejections, changed constructions or reordered
checks) except for the scoped-cache change of branch agent/verify-inductives-e1,
which is un-parked as the alternative to declarative strengthening (HANDOFF
2026-10-06); the countermodel on agent/verify-inductives-base is parked. Do not
delete or disable tests. Commit each verified step (message ends with only
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`), push to kim-em, keep
HANDOFF.md current, and at each milestone run the full build, tests, replays and
audit. Never post to GitHub or Zulip without an approved draft.
```
