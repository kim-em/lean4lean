# Open proofs

The verification of `addDecl` (`Lean4Lean.addDecl.WF`) and everything stated on top of it is
conditional on three theorems whose proofs are `sorry`. They are the `openProofs` of
`scripts/inductive-audit-inventory.json`; `scripts/check-inductive-audit.py --require-complete`
checks that every `sorry` reached from an audit root is one of them and that each of them is still
reached. Paths are relative to `Lean4Lean/`.

| theorem | origin | reached by |
|---|---|---|
| `IsDefEqU.weakN_iff` | master | the checker verification |
| `VEnv.WF.patsStrong` | PR #43 | everything that uses the strong system |
| `VEnv.Model.PatValid.nested` | this branch | head inversion, hence uniqueness of typing |

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

## `VEnv.Model.PatValid.nested` (`Theory/Typing/HeadInjectivity/Model/PatSound.lean`)

**Statement.** The ι rules registered by a nested inductive declaration (one whose compilation
has container specializations installed below it) are valid in the observation model of every
later well-formed environment, given validity of the environment before the declaration. The
ordinary case (`Model.PatValid.ordinary`, `Model/IotaHistory.lean`) is proved; the history
induction `VEnv.WF'.envValid` (`Model/EnvValid.lean`) dispatches each inductive step to one of the
two.

**Use.** It is the `pat` case of the model's soundness (`Model.sound`), hence of
`VEnv.WF.chainHeadInjectivity` and `VEnv.WF.headSeparationModel`, hence of
`VEnv.WF.headInversion`, `IsDefEq.uniq`, the injectivity lemmas, the checker verification and
confluence.

**Why it is open.** The generic part of the ordinary proof applies unchanged
(`PatValid.of_rule`, `PatValid.of_rule_empty`, `iotaArgRel_of`); what is missing is the static
data of a restored equation, which the nested verification has not yet been made to supply.

**What would close it.** The restored blocks must provide:
* `IotaStatic` of the restored recursor's type, including that the minor ending in the restored
  constructor is that rule's minor and no later minor ends in it;
* uniqueness of the rule per recursor and constructor;
* `ProjMajor` and `FamSort` for the major's family when it is a container family;
* the hypotheses `hNS`, `hDP`, `hDF` of `iotaArgRel_of`, relating the container constructor's
  installed type to the restored template's field domains.
