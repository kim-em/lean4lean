# Open proofs

The verification of `addDecl` (`Lean4Lean.addDecl.WF`) and everything stated on top of it is
conditional on two theorems whose proofs are `sorry` (and the fresh-replay theorems on a further
hypothesis, see `IsDefEqU.weakN_iff` below). They are the `openProofs` of
`scripts/inductive-audit-inventory.json`; `scripts/check-inductive-audit.py --require-complete`
checks that every `sorry` reached from an audit root is one of them and that each of them is still
reached. Paths are relative to `Lean4Lean/`.

| theorem | origin | reached by |
|---|---|---|
| `IsDefEqU.weakN_iff` | master, with canonical `Eq` | replays on top of imports with `Eq`; fresh replays |
| `VEnv.WF.patsStrong` | PR #43 | everything that uses the strong system |

## `IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean`)

**Statement.** Context strengthening in an environment with canonical `Eq`: in a well-formed
environment that has the prelude's `Eq`, `Eq.refl` and `Eq.rec` with its ι rule
(`VEnv.HasCanonicalEq`, `Theory/CanonicalEq.lean`), if two terms that do not mention `n` binders
of a context are definitionally equal in that context, they are definitionally equal in the
context without those binders. This is master's statement with the hypothesis
`heq : env.HasCanonicalEq` added.

**Use.** The executable keeps the C++ kernel's caches and equivalence manager across binders.
The checker verification moves the facts they record out of a binder's scope with context
strengthening (`VEnv.Strengthening`), which it reads from its environment: the invariant
`VEnvs.WF` (`Verify/Environment/Model.lean`) and the checker's `CheckerEnv` carry
`VEnv.StrengtheningAbove`, strengthening in every well-formed extension of the model, which is
monotone along the extensions a declaration makes. `VEnv.HasCanonicalEq.strengtheningAbove`
derives it from canonical `Eq` with this theorem; it is reached through
`VEnvs.WFCore.toWF_of_canonicalEq` by `replayPure.WF_fromImports` and
`addDecl.WF_of_canonicalEq`, and through `VEnv.EqFreeStrengthening.strengtheningAbove` by the
fresh-replay theorems. `addDecl.WF` and the rest of the checker verification take strengthening
from the invariant and do not reach it; `reduceRecursor.WF` and the confluence theorem do not use
strengthening at all.

**Why it is open.** It is not known to be true or false. Master's statement, without
`HasCanonicalEq`, was argued false by the predecessor branch (PR #53) for well-formed
environments without `Eq`: in the environment that `Tests/CacheScope.lean` builds (two singleton
`Prop` families `I`, `J` with large elimination over `P : F c → Prop`, and no `Eq`), the types
`SI := I.rec K p` and `SJ := J.rec K r` are definitionally equal under a binder `q : P v` (proof
irrelevance and ι reduction through `K v q`), while a groupoid interpretation of the context
without `q` (one object with automorphism group `Z/3` acting on a three-element fiber) separates
them. The larger-context derivation was checked in Lean; the separation is argued on paper, not
formalised. That environment has no `Eq`, so the sharpened statement claims nothing about it;
with canonical `Eq` the countermodel disappears (`P v` can be extracted from `p`), but no proof is
known: PR #53 reduced the statement to strengthening for endpoints typed at a common type without
closing it. `addDecl.preludeEq_hasCanonicalEq` (`Verify/CanonicalEq.lean`) shows that the
hypothesis is met by the environments that check the real prelude's `Eq`.

**Fresh replay.** A `--fresh` replay checks the prelude's declarations before `Eq` (`id`,
`PUnit`, `True`, `False`, `Not`, ...) with the same persistent caches, and every exit from a
binder moves the caches' facts with strengthening (`State.WF.restrict` in
`RecM.WF.withLocalDecl`, `M.WF.withLocalDecl` and `RecM.WF.withLetDecl`, through
`VContext.strengthening`, `Verify/TypeChecker/Basic.lean`; `lowerClosedBody` in
`Verify/TypeChecker/IsDefEq.lean`; the projection walk `TrExprS.lowerClosedBV`; the equivalence
manager `State.WF.eqv_uniq`). Canonical `Eq` cannot supply it there, so `replayFresh.WF` and
`replayFresh.WF_target` take strengthening in every well-formed environment without canonical
`Eq` (`VEnv.EqFreeStrengthening`) as a hypothesis. For an arbitrary source table this hypothesis
is argued false, by the same countermodel: replaying the `Tests/CacheScope.lean` declarations
fresh needs no `Eq`, and the persistent caches accept its seeded `result`.

**What would close it.** A proof of the sharpened statement under canonical `Eq`. That would
leave the fresh-replay theorems conditional on `VEnv.EqFreeStrengthening`; making them
unconditional needs either strengthening for the specific `Eq`-free environments the prelude
builds before `Eq`, or a verification that never moves a typing fact to a smaller context
(PR #53's scoped caches and constructor-telescope certificates; an executable change, slower
than the C++ kernel's caching).

## `VEnv.WF.patsStrong` (`Theory/Typing/EnvLemmas.lean`)

**Statement.** `env.WF → env.PatsStrong`: subject reduction of the registered ι rules in the
strong system, in every environment the strong typing of constants walks through (a prefix
`env₁` of `env` with `env.WFPrefix env₁`, and its extensions by constants alone inside `env`).

**Use.** `VEnv.WF.orderedStrong` builds `OrderedStrong` from it, and every lemma of the strong
system takes `OrderedStrong`: `IsDefEq.strong`, the substitution theorems, the inversion lemmas,
and every lemma of the observation model. Through them it is reached by every root that reaches
head inversion, uniqueness of typing, the checker verification or confluence.

**Why it is open.** A proof by induction along the history works with an invariant that excludes
`PatsStrongOn` (a prototype on PR #43 proves this part), but its key step aligns the
constructor's parameters with the recursor's inside a strong derivation, so that the fields can be
retyped there. That needs head inversion with *strong* conclusions. The observation model gives
head inversion with weak conclusions only, and is itself built on `OrderedStrong`.

**What would close it.** Either head inversion with strong conclusions (new metatheory), or a
change to the calculus: a premise on `IsDefEq.pat` that the reduct is typed. With the premise,
`patsStrong` is no longer needed and the one new obligation is that the reducts of the registered
rules are typed in the weak system, which the observation model supports (tried on PR #43: +90/-129
lines over 12 files). The premise is a design decision for the calculus.

**Statement defect.** `WFPrefix` admits prefixes that are not well-formed: a `decl` step may
reorder the history, so a prefix can mention a constant it does not contain. The hypothesis should
be `env₁.WF`; the `WFPrefix` and `≤ env` bounds are not used by `VEnv.WF.strong`.
