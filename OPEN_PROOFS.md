# Open proofs

The verification of `addDecl` (`Lean4Lean.addDecl.WF`) and everything stated on top of it is
conditional on one theorem whose proof is `sorry`. It is the `openProofs` entry of
`scripts/inductive-audit-inventory.json`; `scripts/check-inductive-audit.py --require-complete`
checks that every `sorry` reached from an audit root is it and that it is still reached. Paths
are relative to `Lean4Lean/`.

| theorem | origin | reached by |
|---|---|---|
| `IsDefEqU.weakN_iff` | master | the checker verification |

## `IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean`)

**Statement.** Context strengthening: in a well-formed environment, if two terms that do not
mention `n` binders of a context are definitionally equal in that context, they are
definitionally equal in the context without those binders.

**Use.** The executable keeps the C++ kernel's caches and equivalence manager across binders.
The checker verification moves the facts they record out of a binder's scope with this theorem,
through `VEnv.WF.strengthening` (`Verify/Typing/ConditionallyTyped.lean`) and
`VContext.strengthening` (`Verify/TypeChecker/Basic.lean`). It is master's statement, used as
master uses it, at Mario's direction. Every root of the checker verification reaches it
(`addDecl.WF`, `whnf.WF`, the inductive pipeline, the replay theorems); `reduceRecursor.WF` and
the confluence theorem do not.

**Why it is open.** It is not known to be true. The predecessor branch (PR #53) argued that it is
false for well-formed environments without `Eq`. In the environment that
`Tests/CacheScope.lean` builds (two singleton `Prop` families `I`, `J` with large elimination
over `P : F c → Prop`), the types `SI := I.rec K p` and `SJ := J.rec K r` are definitionally
equal under a binder `q : P v` (proof irrelevance and ι reduction through `K v q`), while a
groupoid interpretation of the context without `q` (one object with automorphism group `Z/3`
acting on a three-element fiber) separates them. The larger-context derivation was checked in
Lean; the separation is argued on paper, not formalised. With canonical `Eq` this countermodel
disappears (`P v` can be extracted from `p`), but no proof is known: PR #53 reduced the statement
to strengthening for endpoints typed at a common type without closing it.

**What would close it.** Either a proof under canonical `Eq` (add `VEnv.HasCanonicalEq` to the
hypotheses, which `addDecl.preludeEq_hasCanonicalEq` supplies for the real prelude; this at least
removes the countermodel), or a verification that never moves a typing fact to a smaller context
(PR #53's scoped caches and constructor-telescope certificates; an executable change, slower
than the C++ kernel's caching).
