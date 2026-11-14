# Open proofs

The verification of `addDecl` (`Lean4Lean.addDecl.WF`) and everything stated on top of it is
conditional on one theorem whose proof is `sorry` and whose statement, as it stands, is false
(see below). It is the `openProofs` entry of
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

**Status: the statement is false.** `Eq.rec` at a constant motive is a non-left-linear rule
(`@Eq.rec T a (fun _ _ => T) E b h ≡ E` exactly when `a ≡ b`), and `VDecl.mutualDef` admits
looping definitions, so Klop's counterexample to confluence applies. With canonical `Eq`, axioms
`T : Type`, `E : T`, `P : Prop`, `H : ∀ x y : T, x = y` and definitions
`C x := @Eq.rec T x (fun _ _ => T) E (C x) (H x (C x))` and `Fix p := C (Fix p)`, a hypothesis
`z : P` gives the fixed point `Fix z` of `C`, hence `Fix z ≡ E` and `C E ≡ E`, while `C E ≡ E` is
not derivable in the empty context. `Theory/Typing/Strengthening/Klop.lean` and the directory
beside it prove this: the derivation under the binder, a well-formed environment with canonical
`Eq` and exactly these declarations, and a model of that environment in which `C E` and `E`
have different denotations. The results are `not_weakN_iff_of_canonicalEq` and
`not_weakN_iff_of_setModel`: the statement of `IsDefEqU.weakN_iff` is false, also with
`VEnv.HasCanonicalEq` added to its hypotheses. They have no `sorry`, use only the three standard
axioms, and are strict roots of the audit. Their one hypothesis is a `SetModel`, an applicative
set theory with dependent products, separation, replacement, pairing and unions and no universe
of sets; `ZFSet.{0}` is one, but this repository does not depend on Mathlib, so the instance is
not built here.

**What the refutation does not cover.** The example needs a looping definition. Strengthening
restricted to well-formed environments with canonical `Eq` and no `mutualDef` is neither refuted
nor proved. Without `Eq` there is a second countermodel, argued on paper and not formalised, that
needs no looping definition: in the environment that `Tests/CacheScope.lean` builds (two
singleton `Prop` families `I`, `J` with large elimination over `P : F c → Prop`), the types
`SI := I.rec K p` and `SJ := J.rec K r` are definitionally equal under a binder `q : P v` (proof
irrelevance and ι reduction through `K v q`), while a groupoid interpretation of the context
without `q` (one object with automorphism group `Z/3` acting on a three-element fiber) separates
them. With canonical `Eq` that countermodel disappears, because `P v` can be extracted from `p`.

**What would close it.** `addDecl.WF` covers every declaration form, `mutualDefnDecl` included,
so no restriction of the statement that excludes looping definitions can carry the verification
as it is stated. The remaining routes are a verification that never moves a typing fact to a
smaller context (PR #53's scoped caches and constructor-telescope certificates; an executable
change, slower than the C++ kernel's caching), or a verification restricted to environments
without looping definitions together with a proof of the restricted statement.

**The restricted statement.** For well-formed environments with canonical `Eq`, the statement
reduces to strengthening for two propositions typed below the new binders (branches
`agent/iota-strengthA`, confluence-based, and `agent/iota-strengthB`, model-based; both checked
and `sorry`-free). A strict normal equality between lifted terms descends with no hypothesis, core
reduction steps above a lift descend, and eta and proof irrelevance are not obstacles; what
remains is a matched beta-redex pair in the confluence join whose arguments are lambdas, that
is, aligning the domains of two lifted abstractions with no type information. The remaining
obligation holds in every normalising fragment; by the Klop example it fails in some
environment with looping definitions.

**Fresh replay.** The executable keeps its caches across binders unconditionally, as the C++
kernel does, so every binder exit of the checker moves cache facts with this theorem, whichever
declaration is being checked. The prelude's declarations before `Eq` (`id`, `PUnit`, `True`,
`Not`, ...) have binders, so `replayFresh.WF` and `replayFresh.WF_target` use the theorem in
environments without `Eq`, which is the case the second countermodel concerns. Restricting the
theorem to environments with canonical `Eq` therefore cannot cover fresh replay: a sharpened variant
(branch `agent/iota-canoneq`) makes `addDecl.WF` depend only on the restricted statement but has
to give the fresh-replay theorems the explicit hypothesis that strengthening holds in well-formed
environments without `Eq`. The uses are `State.WF.restrict` through `VContext.strengthening`
(`Verify/TypeChecker/Basic.lean`), `lowerClosedBody` (`Verify/TypeChecker/IsDefEq.lean`),
`TrExprS.lowerClosedBV` (`Verify/TypeChecker/Projection.lean`), `State.WF.eqv_uniq`
(`Verify/EquivManager.lean`) and two places in `Verify/Environment/Primitive/Recursion.lean`.

