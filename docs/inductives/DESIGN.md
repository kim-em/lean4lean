# Verified inductive declarations: design

This document describes what this pull request proves, how the proof is organised, and what it
changes in the specification and in the executable. Paths are relative to the repository root.
Line counts are approximate and refer to the final tree.

The pull request adds about 330k lines of Lean. Two thirds of it is the refinement proof of
the executable inductive checker (`Lean4Lean/Verify/Inductive/`, 218k lines). The rest is the
metatheory (`Lean4Lean/Theory/Typing/`, 73k added), the generative specification of inductive
types (`Lean4Lean/Theory/Inductive/` and `Lean4Lean/Theory/Inductive.lean`, 15k), the
verification of quotients, the canonical hypotheses and the checker changes
(`Lean4Lean/Verify/` outside `Inductive/`, 19k), executable changes (2k) and tests (2k).

## 1. The result

### 1.1 The theorem

`Lean4Lean/Verify/Environment.lean`:

```lean
theorem addDecl.WF_of_canonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq)
    (decl : Declaration) (hdecl : decl.IsModelled env ves) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

Every declaration form is covered, including ordinary, mutual and nested inductive
declarations and quotient initialization. The dependency cone has no `sorry`. The theorem is
a thin wrapper around

```lean
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (hcorner : ∀ safety, ProjectionCorner safety env (ves.venv safety))
    (hq : ∀ safety, (ves.venv safety).QuotReady)
    (decl : Declaration) (hdecl : decl.IsModelled env ves) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WFCore env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        VEnvs.CertPres env env' ves ves'
```

`VEnvs.WF` is the core invariant `VEnvs.WFCore` together with the constructor-telescope
certificates `VEnvs.CtorCert` (section 5.3); the wrapper discharges `hcorner` from the
certificates, derives `hq` from `heq` (`VEnv.HasCanonicalEq.quotReady`), and carries the
certificates to the output through `CertPres`. The iterable form `addDecl.WFHasCanonicalEq`
also returns `HasCanonicalEq` for `ves'` (monotone along `≤`), so the theorem applies again
to the next declaration of a replay. `addDecl.WF_of_canonicalChoice` is the variant over
`VEnvs.WFCore` alone, which assumes canonical `Nonempty`/`Classical.choice` instead of the
certificates.

"Sound" means refinement: whenever the executable `addDecl` returns an environment, that
environment is modelled, at every safety level, by an abstract environment that is well formed
in the sense of `VEnv.WF` and extends the previous model. `VEnv.WF` is the generative
specification of section 2: it says which declarations, with which generated recursors,
projections and computation rules, may be added. The theorem does not address consistency of
the declarative theory `VEnv.IsDefEq` itself.

For inductive declarations there is also a source-facing statement,
`addInductiveDeclaration.finalResultWF` (same file). It returns an `InductiveFinalResult`,
whose `specification` field ties the output to an abstract `VEnv.AddInduct` of the exact
translation of the submitted source declaration (`TrInductDeclCore`), so a model cannot be
attributed to a different (for example lowered) declaration. It assumes that the source has
no loose bound variables (`SourceBVarClosed`), which the executable does not check;
`finalPreservesWF`, used by `addDecl.WF`, does not need it.

### 1.2 End to end: the replay driver

`lake exe lean4lean` runs `Lean4Lean.Replay.replayCore` (`Lean4Lean/Replay.lean`), which walks
the source constants in dependency order, adds a declaration rebuilt from each with
`Lean4Lean.addDecl`, compares the generated constructors and recursors with the source's, and
finally checks that every replayed constant is present and agrees with the source. The core is
generic in a monad that only runs logging and `--compare` hooks; its state and result carry the
evidence (`Replayed`: the environment is a fold of successful `addDecl` calls; `ReplayResult`: the
agreement check passed), so the theorems of `Lean4Lean/Verify/Replay.lean` cover the executable's
run as well as the pure instance. `replayFresh.WF` states that a successful `--fresh` replay of a
constant table (default fuel) yields an environment modelled by well-formed `VEnvs` in which every
safe, non-partial source constant is present and `==` to the source constant (`Expr.eqv`, so up to
binder names and annotations). It has no hypothesis beyond the source table: the walk is turned
into a `Replay` from `Kernel.Environment.empty` (`Replay.WF_empty`). The kernel's `checkEqType`
compares `Eq` only up to `Expr.eqv` and does not look at `Eq.rec` or at safety, so before the step
that initializes the quotient module the driver also checks that `Eq`, `Eq.refl` and `Eq.rec` are
the prelude's (`hasProductionEq`, sound for `HasProductionEq`). `replayFromImports.WF` states the same on top of
imports whose well-formedness and canonical `Eq` are assumed: imports are trusted in that mode.

### 1.3 The hypotheses

- `wf : ves.WF env` is the invariant being preserved. `VEnvs.WF`
  (`Lean4Lean/Verify/TypeChecker.lean`) is the core invariant `VEnvs.WFCore` together with
  the constructor telescope certificates (`VEnvs.CtorCert`). The core gains fields in this pull
  request: closure of mutual inductives, presence of constructor owners, semantic coherence of
  installed constructors with the abstract model, and inductive provenance (which carries
  projection-registry coherence). It holds for the empty environment the executable replays
  from (`VEnvs.WF.empty`, `Lean4Lean/Verify/Environment.lean`): every field is vacuous there
  except the translation, and an environment without constructors carries the certificates
  vacuously (`VEnvs.WF.ofNoCtors`). There is no invariant about the type-annotation wrappers:
  the inductive checker strips `optParam`, `autoParam`, `outParam` and `semiOutParam` from
  binder domains only when the environment at that point declares the name as the prelude's
  definition (`Kernel.Environment.isTypeAnnotationWrapper`), and each strip is justified from
  the definition it looked up (`TypeAnnotationWrappers.of_env`). This differs from the C++
  kernel, which strips by name, only where a wrapper name is declared with another definition
  (`divergences.md`).
- `heq : HasCanonicalEq` (`Lean4Lean/Theory/CanonicalEq.lean`): `Eq`, `Eq.refl` and `Eq.rec`
  are present with the prelude's types, and the iota rule of `Eq.rec` is a stored equation.
  It is used only in the quotient case (section 6); `addDecl.WF_quotReadyAt` assumes quotient
  readiness only for `quotDecl`.
- There is no choice hypothesis: the constructor certificates of `VEnvs.WF` resolve the
  projection-walk corner (section 5.3). `addDecl.WF_of_canonicalChoice` keeps the form that
  assumes `HasCanonicalChoice` (`Lean4Lean/Theory/CanonicalChoice.lean`) instead, over
  `VEnvs.WFCore`.
- `hdecl : decl.IsModelled env ves` is `True` for every declaration. It is kept so that the
  statement keeps its shape; it can be dropped.

A replay from the empty environment is covered by `Replay.WF_empty`
(`Lean4Lean/Verify/CanonicalEqRealization.lean`): every environment reached by adding a list
of declarations one at a time with the checked `addDecl`, starting from
`Kernel.Environment.empty`, has a well-formed model, provided each `quotDecl` comes after the
prelude's `Eq`, `Eq.refl` and `Eq.rec` (`HasProductionEq`, a decidable property of the
executable environment; before `Eq` exists `quotDecl` has no model).

Canonical `Eq` holds in every environment obtained by replaying `Init.Prelude` past `Eq`.
Realizability is proved up to a fact about the concrete production declaration that is checked
by a test: `addDecl.eqBootstrapHasCanonicalEq` (`Lean4Lean/Verify/CanonicalEqRealization.lean`)
takes as hypothesis that the executable installs `Eq.rec` with the production type, which
`Lean4Lean/Tests/CanonicalEq.lean` checks. The honest reading of the theorem is therefore:
`addDecl` is sound for environments that contain the prelude's `Eq`, and every declaration of
a replay from the empty environment is sound (`Replay.WF_empty`).

No hypothesis names the declaration being checked or supplies a semantic fact about it.
Inductive declarations carry no premise at all: their abstract declaration, normalized
signature, compilation certificate and case eliminators are reconstructed from the execution.

### 1.4 Acceptance checks

| check | expected |
|---|---|
| `lake build` | no "declaration uses `sorry`" |
| `lake build Lean4Lean.Tests` | green |
| `lake build Lean4Lean.Experimental` | green; 56 inherited `sorry` declarations (section 9) |
| `lake exe lean4lean --fresh Init.Prelude` | 1975 declarations checked |
| `lake exe lean4lean --fresh Init.Core` | 3953 declarations checked |
| `lake exe lean4lean Init.Core` | 1035 declarations checked |
| `python3 scripts/check-inductive-audit.py --self-test` | passes |
| `python3 scripts/check-inductive-audit.py --require-complete` | "No sorry dependencies; all remaining axioms are listed." |

The audit (`scripts/InductiveAudit.lean`, driven by `scripts/check-inductive-audit.py`) walks
the transitive dependency closure of a fixed list of roots, including opaque theorem bodies and
the types of dependencies. The roots are the top-level theorems, the replay theorems of section
1.2, the three inductive dispatch theorems, `addQuot.WF`, the checker's `whnf` and recursor
reduction theorems, and `IsDefEq.full_church_rosser`. It fails on any `sorry` and on any axiom
not listed in `scripts/inductive-audit-inventory.json`. A second set of strict roots (the
generator definitions of section 2 and a few foundational lemmas) may depend only on the three
standard axioms. The self-test checks that the walker finds a `sorry` behind an opaque body and
an axiom used only in a type.

## 2. The generative specification of inductive types

### 2.1 The calculus

`VExpr` gains two constructors (`Lean4Lean/Theory/VExpr.lean`):

```lean
  | elim (block : Name) (owner : Nat) (us : List VLevel)
  | proj (typeName : Name) (index : Nat) (struct : VExpr)
```

`VEnv` gains a projection table `projections : Name → VProjectionInfo → Prop` and an
eliminator table `eliminators : Name → CaseSchema → Prop`. `VEnv.IsDefEq`
(`Lean4Lean/Theory/Typing/Basic.lean`) gains six rules:

- `projDF`: congruence and typing of `.proj S i e`. The field type is computed from the
  registered constructor telescope instantiated by the parameters and by the projections of
  the major onto the earlier fields (`VProjectionInfo.fieldType`). The rule carries the
  guard `(info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero`: a data field of a
  structure that may be a proposition has no projection.
- `projIota`: a projection of a constructor application is the field.
- `structEta` and `unitLike`: eta for index-free structures, and definitional equality of
  any two elements of an index-free structure without fields.
- `elimDF` and `elimIota`: typing and computation of an abstract case eliminator. Its type
  and equations are generated from its registered schema (no type or equation is stored), and
  its universe instantiation must satisfy `CaseSchema.Permission`, which requires the
  specialized source sort to be never zero or the target to be `≈ 0`.

Projections are primitive, as in the kernel; `.proj` is what the checker's `Expr.proj`
translates to. Native recursors remain constants with stored iota equations (`defeqs`).
Abstract eliminators exist only in the abstract theory: the executable never sees `.elim`.
They are per-family case analysis principles (no induction hypotheses), and they are what
inhabits the projection-walk corner (section 5.3).

### 2.2 Declarations and their well-formedness

The declaration data is syntax only (`Lean4Lean/Theory/DeclarationData.lean`): `VInductDecl`
(universe count, parameter count, families with index counts, result levels and
constructors, `isUnsafe`) and the derived `projectionEntries` (one entry for each family with
exactly one constructor). `VInductDecl.WF env decl` (`Lean4Lean/Theory/Inductive.lean`) is
`decl.SourceWF env ∧ decl.FormationEvidence env`: the source judgment (headers typed, a common
parameter telescope, constructor types typed in the environment with the headers, raw
constructor shapes) together with either ordinary formation (positivity, universe bounds) or a
finite nested expansion into an ordinary well-formed declaration
(`Lean4Lean/Theory/Inductive/Formation.lean`).

Recursors and equations are never accepted as input. `InductiveSignature`
(`Lean4Lean/Theory/Inductive/SignatureData.lean`) is a normalized signature: parameters,
families with index telescopes, constructors with fields classified as external or
recursive. A pure generator produces from it, for an `Instance` (universe levels, elimination
level, recursor names), every motive, minor premise, induction hypothesis, recursor type and
iota equation. `Signature.Models` relates a signature to the source declaration: same names,
arities and result levels, constructor types definitionally equal in the environment with the
family headers, and every field definitionally a strictly positive normal form.
`Instance.Admissible` fixes the elimination universe: every family is never zero, or the
target is `≈ 0`, or singleton elimination holds and the target is a free universe parameter.

`CompilationData` (`Lean4Lean/Theory/Inductive/Compilation.lean`) ties one compilation
together: source and expanded declaration, the signature modelling the expanded declaration,
an admissible instance, typing of the generated induction hypotheses and family
applications, and the restoration (`Lean4Lean/Theory/Inductive/Restoration.lean`) that maps
generated syntax of auxiliary families back to applications of their containers, with
recursor renaming. The installed block's recursors and rules are exactly the restored
generated ones. `CompiledInductive` makes the certificate a finite tree: each container used
by a nested declaration is itself certified by an earlier `CompiledInductive`
(`CertifiedSpecializations`), so no environment lookup can serve as provenance.

### 2.3 Installation order and the abstract `AddInduct`

```lean
def VInductBlock.install (env : VEnv) (block : VInductBlock) : Option VEnv := do
  let env ← env.addConstVals block.types
  let env ← env.addConstVals block.ctors
  let env := env.addEliminators block.eliminators
  let env := env.addProjections block.projections
  let env ← env.addConstVals block.recursors
  return env.addDefEqRules block.rules
```

`VEnv.AddInduct env decl env'` holds when `decl.WF env`, the block is a compilation of the
declaration (`CompilesTo`), the block is well typed stage by stage (`VInductBlock.WF`: types
in `env`, constructors in the types environment, recursors in the environment with
constructors, eliminators and projections, rules in the environment with recursors),
the eliminators are certified (`VInductBlock.EliminatorsWF`), and `install` succeeds.

`VEnv.WF'` (`Lean4Lean/Theory/Typing/Env.lean`) has, besides `empty` and `decl`, two
constructors that describe the intermediate environments of an installation:
`inductEliminators` registers a certified case schema once the declaration's constants are
present, and `inductProjections` registers the projection entries of a declaration whose
constructors and case eliminator are present. The checker runs that happen after the
constructors are declared and before the recursors are installed (the window) therefore run
in a well-formed environment, which every checker theorem requires.

A case schema (`Lean4Lean/Theory/Inductive/CaseSchema.lean`) is the normalized signature with
its restoration and its original family names; its per-family view and generated case type
and equations are computed. `CaseSchema.Certified` is `CaseCompilationData`: the part of a
compilation that fixes the schema (formation, model, restoration correspondence and scoping,
installed source constants, family typing), without anything about the generated native
recursors, which `elimDF`/`elimIota` never read.

### 2.4 Restrictions of the specification to what Lean produces

Each item below closes a gap through which well-formed environments could be inconsistent or
non-confluent, or adds a premise that every Lean declaration satisfies and the proof needs.
None weakens the top-level theorem.

- **Free elimination universe for singleton elimination** (`Instance.FreeTarget`,
  `Lean4Lean/Theory/Inductive/Signature.lean`). Without it a large-eliminating proposition
  could have only a recursor with motive universe `succ u`. Its proof fields then cannot be
  extracted into `Prop`, its iota rule has no reconstruction step, and the equation coverage
  that the confluence proof needs fails.
  `getElimLevel` always produces a fresh universe parameter.
- **Structure compatibility** (`CaseSchema.StructCompat`, a premise of `inductEliminators`).
  Without it a schema could add constructors to a registered structure: register
  `structure Unit` with `Unit.mk`, add an axiom `other : Unit`, register a schema for
  `inductive Unit | mk | other`; the generic equations and `unitLike` then derive
  `Prop ≡ (Prop → Prop)` (`Lean4Lean/Theory/Typing/SchemaStructCompat.lean`).
- **Projection coherence** (`VInductDecl.ProjectionsCoherent` and
  `CaseSchema.ProjNamesRegistered`, premises of `inductEliminators`). A structure's
  projections and its case schema must come from the same declaration, and a schema may only
  project out of registered structures. Otherwise projections with constructor `S.a` and a
  case rule for an unrelated axiom `S.b : S` make `elim S (m, x) S.b` and
  `elim S (m, x) S.a` definitionally equal without a common reduct
  (`Lean4Lean/Theory/Typing/EliminatorCoherence.lean`).
- **Case eliminators at the constructor boundary.** Every block with families registers one
  certified case eliminator, keyed by its first family, between constructors and projections;
  a block may omit both eliminators and projections only if it has no families. Hence every
  registered structure has a registered case eliminator at every point of every history
  (`VEnv.WF.projections_eliminated`), which the corner needs, including during the window.
  The certificate is the case-only `CaseCompilationData` because the full `CompilationData`
  includes the typing of the generated recursors, which the window computes.
- **Header agreement** (`CaseSchema.HeaderAgreement`). The restored normalized header of each
  original family is definitionally equal to its declared type. The corner for indexed
  structures needs the restored case type's index telescope to agree with the declared one.
- **Window typings are stated in the window environment.** `Instance.RecursiveTypesWF` and
  `FamilyTypesWF` are required in the environment with constructors, the declaration's own
  case eliminators and its projection entries, because that is where the executable checks
  the generated types. Stating them in a smaller environment or context would need
  strengthening (section 5). For the same reason `Models` does not compare family types:
  only constructor types are compared, and family applications are required to be well typed.
- **Restored eliminators in renaming replacement.** The transport of window derivations from
  a lowered nested declaration to its source
  (`Lean4Lean/Theory/Inductive/RestorationRenamingOnCtx.lean`) allows a lowered schema to be
  matched by a registered source schema with the same signature whose restoration agrees with
  the replacement.

## 3. The verified installation pipeline

### 3.1 Dispatch

`addInductiveDeclaration.finalPreservesWF` (`Lean4Lean/Verify/Environment.lean`) splits on
the executable's own branch selection. Primitive declarations (`Bool` and `Nat`, recognized
by `Primitive.checkInductive`) go through `Lean4Lean/Verify/Inductive/Primitive*.lean`. For
other declarations the verified lowering result decides: no auxiliary families means the
ordinary path (`OrdinaryFinalDispatch.lean`), otherwise the nested path
(`Nested/EndToEnd.lean`, `NestedFinalSpecification.lean`). All three produce an
`InductiveFinalResult`.

### 3.2 Phases of the ordinary path

- **Headers** (`Lean4Lean/Verify/Inductive/Header/`, 9k). The header loops of
  `Inductive/Add.lean` check each family type, the common parameters and the result
  universes. The proof materializes the abstract headers and their source translation.
- **Constructors** (`Constructor/`, 7k). Each constructor type is checked in the environment
  with the headers; positivity, the universe bound on fields and the result shape are
  verified, and each field is related to its strictly positive normal form (the
  `positiveFields` clause of `Models`).
- **Constructor boundary** (`ConstructorBoundary.lean`). From the data available once the
  constructors are declared, the proof computes the source signature
  (`ConstructorBoundary.sourceSignature`, with `sourceSignature_models`) and the
  declaration's case eliminator `(first family, CaseSchema.ofCompilation decl signature [])`.
  Its certificate is kept in a monotone form that replays in every larger environment in
  which the declaration installs. The window environment
  `(ctors.addEliminators es).addProjections P` is shown well formed by `inductEliminators`
  and `inductProjections`. The executable is unchanged by this: it has no case eliminators.
- **Recursors** (`Recursor/`, 51k; `Completed*.lean`, 33k). The executable's recursor
  construction (first and second pass over the fields, elimination level, motives, minors,
  induction hypotheses, rules) is shown to produce exactly the translation of the abstract
  generator's output for one canonical `Instance`
  (`Recursor/Realization.lean`, `RecursorMetadataRealization.lean`). Typing of the generated
  recursor types is not derived from the generator: it is read off the executable's check of
  each generated recursor type (`checkRecursorTypes`), which supplies `RecursiveTypesWF` in
  the window environment; `FamilyTypesWF` likewise comes from checker runs in the window.
  Rules are proved well typed in the recursor
  environment (`EquationWF.lean`, `RuleTranslation*.lean`).
- **Assembly** (`CompletedBlockCertificate.lean`, `Run/`). The phases assemble into
  `VInductDecl.CompilesTo`, `VInductBlock.WF`, `EliminatorsWF` and the final `AddInduct`, and
  into the safety-indexed `VEnvs.WF` of the output.

Embedded checker runs of the inductive checker see a narrow local context
(`AddInductive.Context.checkLCtx`, verified in `Lean4Lean/Verify/Inductive/Context.lean`):
only the binders a run may need (parameters, indices, fields), never majors, motives, minors
or induction hypotheses. Every checker fact is thus produced in the context in which the
proof uses it, and is transported to larger contexts by weakening. A checker run only consults
free variables reachable from its inputs, so the results agree with runs in the larger
context.

### 3.3 Nested declarations

Nested declarations are verified by lowering and restoration (`Nested/`, 91k).
`Nested/Lowering.lean` and `Nested/Replacement.lean` (an exact, cache-independent
specification of `Expr.replace`) verify the replacement of maximal nested occurrences by
fresh auxiliary families and its correspondence with the abstract nested expansion. The
lowered declaration runs the ordinary pipeline, including its own constructor boundary. The
restoration loop is then verified: restored constructors, restored recursor types and
restored rules (`Nested/Restoration*.lean`, `Nested/EquationRestoration*.lean`). The
typing of restored equations is transported from the lowered recursor environment by a
context-carrying renaming restoration substitution (`Nested/RestoredEquationWF.lean`), which
replaces each auxiliary head by its restoration lambda and renames recursors and projection
type names.

The source block registers its own case eliminator: the boundary signature of the lowered
run, under the same key, restored by the nested compilation's restoration
(`Nested/CaseEliminators.lean`), certified from the validated run.

The executable validates the restoration before installing it: restored constructor
parameter prefixes, restored recursor types, and restored rules, each rule as a closed
equation whose two sides are type checked and compared, together with a structural check that
the rule is guarded (`validateRestoredRecursorRules`, `guardedIotaCheck`). Rules are
validated in a copy of the restored environment in which every restored recursor has no rules
(`stripRecursorRules`), because the abstract iota equations are only added once the rules
are known to be well formed. The proof consumes these checks as evidence
(`Nested/StrippedValidity.lean`, `Nested/CheckedGuardedIota.lean`).

The parametric nested applications `I Ds` (leanprover/lean4#14577) are type-checked
(`validateNestedAuxiliaries`), as in the C++ kernel. For a nested occurrence of a family with
indices, `I Ds` is a type family and its auxiliary family is itself indexed. The proof closes
each application with lambdas over the lowering parameters and its inferred type with foralls
over the same parameters (`ClosedValidatedNestedAuxiliaries`, `Nested/Lowering.lean`), which
is well formed in both cases, and uses only the resulting typing of the restored head
(`GeneratedFamilyHeadRealization`).

### 3.4 Reconstructed and checked facts

Everything about an inductive declaration's abstract counterpart is reconstructed from the
execution: the `VInductDecl` (by translating the submitted syntax), the normalized signature
and instance, the restoration tables, the case schemas and their certificates. Three kinds of
typing facts are not proved from the generator but read off runtime checks that the
executable performs: the type of each generated recursor (`checkRecursorType`), the restored
nested recursor types and constructor parameters, and the restored nested rules. On every
declaration the checker accepts these checks succeed; they turn a generic generator
correctness theorem, which would need strengthening and uniqueness at arbitrary generated
syntax, into a type check of a closed term.

## 4. Metatheory

### 4.1 Head inversion

`VEnv.HeadInversion` (`Lean4Lean/Theory/Typing/HeadInversionDefs.lean`) is stated over
`TypeChain`s, chains of definitional equalities each typed at a sort: sorts are injective,
Pi types are injective in domain and body, rigid heads (constants heading no rule) are
injective in name, levels and arguments, type formers are injective along their declared
telescope, and sort, Pi and distinct rigid heads are never related. The eighth field,
`proj_fieldType`, is the projection case of uniqueness of types: a field type instantiates
the earlier fields by projections, some of which may be untypable under the `projDF` guard,
so the case cannot be derived by substitution.

`VEnv.WF.headInversion` (`Lean4Lean/Theory/Typing/HeadInversion.lean`) holds for every
well-formed environment, without canonical `Eq`. Uniqueness of types (`IsDefEq.uniq`,
`Lean4Lean/Theory/Typing/UniqueTyping.lean`) and every inversion lemma of
`Lean4Lean/Theory/Typing/Injectivity.lean` derive from it. The checker verification uses
uniqueness throughout.

A logical relation with Coquand-Huber adequacy, as in the shape logical relation prototype in
`Lean4Lean/Experimental/`, cannot deliver the injectivity half here: any sound compositional
model must interpret an eliminator on a proof major by reading through to its iota result, and
Pi adequacy then forces the iota check, which for `Eq.rec` is equality reflection (the
evidence is in `Lean4Lean/Experimental/Spike/`). The proof uses soundness of a model only.

**The glued observation model** (`Lean4Lean/Theory/Typing/HeadInjectivity/Model/`, 15k). A
term denotes a set of atomic observations, glued with declarative equivalence classes of
terms in a fixed target context `Δ`. `TyCls Δ A` is the class of types related to `A` by a
`TypeChain`; `ElCls Δ D a` the closure of `a` under definitional equalities typed at a member
of the type class `D`. A typed element class collapses to a single definitional equality at
one type (`ElCls.collapse`). Observations (`Model/Obs.lean`) record a sort's level, a Pi
type's domain class and the class and observations of each codomain instance at a typed key,
a function's result at an argument of a given class, a rigid spine's head, levels, arity,
sort and argument classes, constructor heads and arguments, and field observations of
structure values. Observations are typed against the observations of the type
(`TypedOb`), which makes proofs observationally empty. `Obs` (`Model/Interp.lean`) is an
inductive predicate over a valuation consisting of an anchor substitution into `Δ` and
observation sets for the variables; every head's observations are filtered by typing at its
type.

`Model.sound` states that for a strong derivation `Γ ⊢ t ≡ t' : T` and related anchors, the
observations of `t` and `t'` agree up to subsumption and are typed at observations of `T`.
Extraction (`Model/Extract.lean`) applies soundness at the identity valuation and at the
weakening valuation: a chain from `Pi A B` to `Pi A' B'` makes their domain classes equal,
giving `TypeChain Γ A A'`, and their codomain classes at the fresh variable equal, giving
`TypeChain (A :: Γ) B B'`; rigid spines give their argument classes. The same model gives
separation (`VEnv.WF.headSeparationModel`, `Model/Separation.lean`): a sort has a `sort`
observation, a Pi type a `piDom` observation, a rigid spine neither.

Computation rules are handled by one pattern-rule clause (`Model/RuleSound.lean`): every
stored rule (delta, quotient, native iota after restoration, generic case equation) is a
lambda telescope over a head applied to bound variables, ignored terms and a constructor
major. Fields are bound in one of three modes. When the major's family is not a proposition
at the instance, they come from the major's constructor observations. When it is a
proposition with large (singleton) elimination, the major is ignored and data fields are read
from the indices at which they occur literally, proof fields being proofs and so
observationally empty. When the family is projection-registered, constructor spines carry
only field observations (structure eta forces this), so the rule is identified from the
head type and fields are bound from the major's field observations (`Model/EtaBind.lean`).

**History induction.** Several semantic facts used by these cases come from derivations in
earlier environments that are not subderivations of the node being interpreted: a native
family's recorded result sort, the propositional typing of a singleton's proof fields, the
soundness of a projection entry's constructor telescope and family header. Soundness is
therefore proved along the declaration history (`WF'.ruleValid`, `Model/Staged.lean`): each
rule, eliminator rule and projection entry is valid in the model of the final environment
because the derivations of the environment preceding its declaration are sound there, by the
induction hypothesis. `HeadsClosed` and `ProjsClosed` carry the facts that no later
declaration adds a rule headed by an existing constant or a projection entry for an existing
rule constructor. Constructor arities are read from the model (`Model/Arity.lean`):
definitionally equal Pi telescopes ending in rigid spines have equal length, which a purely
syntactic argument cannot give without head inversion.

**The syntactic layer** (`HeadInjectivity/{Core,Uniqueness,FieldType,Fields}.lean`) turns the
chain-level injectivity delivered by the model (`HeadInjectivityCore`) into the injectivity
fields of `HeadInversion`. Uniqueness up to chains and a congruence property are proved by
one induction on the strong typing derivation, which makes `proj_fieldType` provable:
unused, untypable earlier projections never occur in the field type, so the induction never
visits them. None of these files imports uniqueness or confluence.

### 4.2 Confluence

`FullReduction.church_rosser` (`Lean4Lean/Theory/Typing/LevelledReduction.lean`, 4.7k) is
proved by decreasing diagrams (`Lean4Lean/Theory/LevelledConfluence.lean`) over a split of the
full step relation into four levels: normal equality without eta (levels, proof
irrelevance), parallel reduction (beta, native and schema patterns), parallel delta
(native and quotient prefix unfolding, projection of constructor applications), and parallel
eta expansion. Function eta is not restricted to non-head positions, because the transports
of computation through normal equality need expansions in function position.

`VEnv.WF.params` (`Lean4Lean/Theory/Typing/WFParams.lean`) is the concrete instance for a
well-formed environment, and

```lean
theorem WF.church_rosser {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) : ...
```

Canonical `Eq` is needed for equation coverage: a native singleton equation at a universe
specialization whose source is `Prop` is joined by reconstructing the constructor, and its
proof fields are extracted by the recursor into `Prop` with the earlier data fields cast
along `Eq`. In the well-formed `Eq`-free environment of `Lean4Lean/Theory/Typing/Countermodel/`
that equation is not joinable (argued, not checked in Lean). Coherence of eliminators with projections
(`VEnv.WF.eliminatorsCoherent`) is also needed. Confluence is not in the dependency cone of
the top-level theorem.

## 5. Strengthening, scoped caches and the corner

### 5.1 Why declarative strengthening is not used

The checker verification on `master` uses inverse weakening (`IsDefEqU.weakN_iff`, a `sorry`):
a conversion established in `Γ, q : Q` between terms not mentioning `q` holds in `Γ`. This is
false in general. Take opaque `C : Type`, `F : C → Type`, `c : C`, `P : F c → Prop`,
`leftMap rightMap : F c → F c`, and the two singleton families
`I, J : (n : C) → F n → F n → Prop` with constructors `mk (v : F c) (h : P v)` landing at
`I c v (leftMap v)` and `J c v (rightMap v)`. In the context
`K, v, p : I c v (leftMap v), r : J c v (rightMap v)`, let `SI := I.rec K p` and
`SJ := J.rec K r` at motive `Type`. After adding `q : P v`, proof irrelevance and iota give
`SI ≡ K v q ≡ SJ`. A groupoid interpretation of the smaller context (one object with
automorphism group `Z/3` acting on the fiber `{0, 1, 2}`) separates `SI` and `SJ`.
The environment and the larger-context derivation were checked in Lean while this was
studied; the separation itself is argued on paper, not formalised. With canonical `Eq` this countermodel disappears, since
`P v` can be extracted from `p`, but no proof of strengthening is known: every organisation
of the needed conversion-elimination theorem for typed eta and definitional proof
irrelevance is circular, and the calculus does not normalize. The verification is
organised so that it never
moves a typing fact to a smaller context.

### 5.2 Scoped caches

Every binder of the checker saves and restores the context-relative state
(`TypeChecker.State.leaveScope`, `Lean4Lean/TypeChecker.lean`): the inference caches, the
`whnf` caches, the equivalence manager and the failure cache are put back on leaving the
binder; the name generator stays advanced and the `unfold` cache, which depends only on the
environment, is kept. `isDefEqLambda` and `isDefEqForall` always compare bodies under a binder.
With this, the cache invariant is simply "every entry is derivable in the current context"
(`VState.WF`, `VState.WF.leaveScope` in `Lean4Lean/Verify/TypeChecker/Basic.lean`).

Without scoping no invariant of that form holds. `docs/inductives/CacheScopeExperiment.lean`
builds the countermodel environment above (no `Eq`) and a closed definition of type `SJ` with
value `let seed := fun (q : P v) => ... ; (zz : SI)`, where the body of `seed` forces the
comparisons `SI ≡ ... ≡ SJ` under `q`. The C++ kernel accepts this definition and rejects it
without `seed`; the unscoped lean4lean checker accepted it too; the scoped checker rejects
it. So the scoped checker can reject a declaration the C++ kernel accepts. Such a declaration
relies on a conversion fact outside the scope where it holds: `SI ≡ SJ` is derivable under `q`
but not in the outer context, so it is the C++ acceptance that is non-local. Both fresh replays
of `Init.Prelude` and `Init.Core` are unaffected. This is one of several divergences of the
executable; `divergences.md` lists all of them, with an audit table of every executable change
(section 7.2).

Two primitive checks were adjusted for the same reason (`Lean4Lean/Primitive.lean`): the
pieces of a `reflectNatNat` condition and the functional of a well-founded definition are
checked in the outer context, rather than relying on facts established under the gadget's
binders.

### 5.3 The projection-walk corner

`inferProj` walks the constructor telescope of a structure. Past a field binder whose body
does not depend on it, the walk keeps the body without substituting anything, so the
verification must translate the remainder without that binder. When the field's projection
is typable it inhabits the binder and substitution does this. Otherwise (a data field of a
structure that may be a proposition, which the kernel still walks past) a translation of the
remainder in the smaller context is needed, and general strengthening is not available
(section 5.1). Two proofs resolve this.

The proof used by `addDecl.WF_of_canonicalEq` re-derives the smaller-context translation from
the checker's own acceptance of the constructor type. A frame lemma for the executable
(`Lean4Lean/Verify/TypeChecker/Frame*.lean`: a successful run in a local context with extra
declarations that never occur in its inputs, caches or environment is the same run without
them) and a ghost-telescope verification (`Verify/TypeChecker/GhostTelescope.lean`) show that
when a constructor type is checked, every unused binder of its telescope can be deleted from
the translation. The result is recorded as a depth-bounded certificate `TelTrN`
(`Verify/Typing/TelescopeTranslation.lean`), one per visible constructor at every safety
level (`VEnvs.CtorCert`); the bound is the constructor's own arity, which is what the walk
consumes. The certificates hold vacuously for an environment without constructors, are
preserved by every declaration (`VEnvs.CertPres`), and the walk uses the delete branch of the
certificate at each non-dependent field. Nested declarations need the stored constructor type
to agree with the checked source type up to binder names
(`Verify/Inductive/Nested/ConstructorTypeRoundTrip.lean`), because reusing an auxiliary
renames binders inside reused occurrences, as in the C++ kernel.

The alternative proof, used by `addDecl.WF_of_canonicalChoice`, inhabits the binder `D`
instead (`VEnv.WF.corner_inhabit_choice`,
`Lean4Lean/Theory/Typing/ProjectionCornerChoice.lean`): eliminate the major into `Prop` with
the structure's registered case eliminator, motive `fun _ => Nonempty D` and minor
`fun fields => Nonempty.intro field_j`, then apply `Classical.choice`. The projections that
`D` mentions pass the guard, so they are proof fields and the minor is typed by `projIota`
and proof irrelevance. Substitution of the inhabitant removes the binder
(`projectionWalkCorner_choice`, `Lean4Lean/Verify/Typing/ProjectionCorner.lean`, via
`TrExprS.weakBV_inv₁_inhabited`). Indexed structures use the indexed case type, which is a
type by header agreement (`ProjectionCornerIndexed*.lean`).

This is why every block registers a case eliminator before its projections: the corner can
arise in any checker run that sees a registered structure, including the runs in the window
before the native recursors exist.

Choice is needed because `Nonempty D` is a propositional fact, not a term of `D`; for
`S := Nonempty D` the corner is literally strengthening across `d : D` under the hypothesis
`Nonempty D`. No known proof avoids both choice and a strengthening or conversion-locality
argument.

## 6. The quotient declaration

`addQuot.WF` (`Lean4Lean/Verify/QuotInit.lean`) covers `quotDecl`. On an environment with
`quotInit = false` the executable is `checkEqType`, four name checks and the installation of
`Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind`. Their types, built with
`withLocalDecl`/`mkForall` from a fresh name generator, are computed literally and translated
to the abstract constants of `Lean4Lean/Theory/Quot.lean`; every safety-indexed model is
extended by `VEnv.addQuot`.

The abstract rule `VDecl.WF.quot` needs `QuotReady` (abstract `Eq` with its canonical type),
and the quotient constants are safe, so every safety level must type `Quot.lift`, whose type
mentions `Eq`. `checkEqType` checks the shape of `Eq` and `Eq.refl` but not their safety: an
environment whose `Eq` is an unsafe inductive of the right shape passes it, and its safe model
has no `Eq`. Hence `addQuot.WF` takes `QuotReady` at every level, supplied by `HasCanonicalEq`.
The executable now declares the major of `Quot.ind` with an explicit binder, matching the C++
kernel and Lean's declaration; `Lean4Lean/Tests/QuotInit.lean` compares the installed types
with the kernel's including binder info.

## 7. Trusted base and executable changes

### 7.1 Axioms

`#print axioms addDecl.WF_of_canonicalEq` shows 32 axioms: `propext`, `Quot.sound`,
`Classical.choice`, and the 29 implementation axioms of `scripts/inductive-audit-inventory.json`:

- 25 in `Lean4Lean/Verify/Axioms.lean`, equations identifying compiled implementations with
  their Lean models: `Expr` operations (`instantiate*`, `abstractRange`, `abstractN`,
  `lowerLooseBVars`, `looseBVarRange`, `hasLooseBVar`, `replace`, `eqv`, `mkData`,
  `mkAppData`), `Level` operations (`normalize`, `hasMVar`, `hasParam`,
  `isExplicitSubsumedAux`, lawful `BEq`), `PersistentArray`, `PersistentHashMap`,
  `Std.TreeMap.all` and `Syntax.structEq`;
- the two pointer-equality axioms of `Lean4Lean/PtrEq.lean`;
- two native `bv_decide` certificates in `Lean4Lean/Verify/Expr.lean`.

All of these exist on `master` except one: `master`'s
`Lean.Expr.abstract_eq` equated `Expr.abstract` with sequential abstraction, which is false
(`(Expr.bvar 0).abstract #[.fvar x]` is `.bvar 0`, the model gives `.bvar 1`). It is replaced
by `abstractN_eq`, an exact model of simultaneous abstraction that leaves loose bound
variables unshifted; the sequential model is used only where closedness and distinctness make
the two agree. No axiom is added.

### 7.2 Executable changes

Every behavioural change to the executable is classified in the audit table at the end of
`divergences.md`: a refactor with the C++ kernel's decisions, a divergence documented there, or
(with an entry) a divergence found by the audit. Scoped caches (section 5.2) are not the only
divergence, but they are the only one that can change a decision against the C++ kernel on an
environment whose type-annotation wrappers are the prelude's: they reject a term whose
acceptance needs a conversion fact outside its scope. The wrapper stripping below can change a decision only on an environment that redefines a
wrapper name. The other changes cannot change a decision except through checker fuel, as follows.

- **Redundant guards**, each listed in `divergences.md`: `reduceProjCore` requires the
  constructor to be the structure's unique constructor; `tryEtaStructCore`
  requires the listed constructor and applies structure eta only at never-zero sorts;
  `isDefEqUnitLike` and `toCtorWhenK` check the arity of the type's spine; `inferProj`
  rejects field indices beyond `numFields`; constructor owner and `isUnsafe` agreement are
  checked wherever a structure's constructor is looked up; `toCtorWhenStruct` and
  `expandEtaStruct` return the term unchanged where the C++ kernel has `unreachable!`. Each
  guard lets the verification justify a step from the registry entry alone, without
  injectivity or head separation. All are redundant on well-formed environments and
  well-typed terms with one exception: structure eta is not applied to a structure whose
  universe is neither always nor never zero (`Sort u`), so a conversion that needs it there
  is rejected.
- **Inductive checker** (`Lean4Lean/Inductive/Add.lean`): restructured into explicit loops
  with total fresh-name searches, narrow checker contexts (section 3.2), unreachable arity
  guards in recursor construction, and recursor rules built from the first constructor
  traversal. Each generated recursor type is type-checked (`checkRecursorTypes`); the kernel
  of the pinned toolchain does not do this, upstream does since leanprover/lean4#14808, which
  also checks rule type preservation, which lean4lean proves instead. Nested auxiliary types
  are named `_nested.i` rather than `_nested.J_i` (internal names only). The nested
  restoration validation of section 3.3 re-checks restored declarations in side environments,
  additionally re-checks constructor parameter prefixes, and validates restored rules in the
  stripped environment with guardedness, shape and equation-type checks, all stricter than the
  C++ kernel's revalidation (leanprover/lean4#14621). The nested applications `I Ds`
  themselves are only type-checked, as in the C++ kernel.
- **Caching**: `whnf` results are cached only for applications, constants, lambdas and
  projections (`Lean4Lean/WHNFCacheKey.lean`), which keeps the cache invariant within reach
  of the translation; this affects performance only.
- **Transparent re-implementations** used by the executable so that proofs can see through
  them: `Expr.findAny` (in place of `Expr.find?`) and `consumeTypeAnnotationsVerified` (in
  place of `consumeTypeAnnotations`).
- **Type-annotation wrappers**: a wrapper application in a binder domain is stripped only when
  the environment declares the wrapper as the prelude's definition
  (`Kernel.Environment.isTypeAnnotationWrapper`); otherwise the domain is checked literally.
  The C++ kernel strips by name. This differs only on environments that declare one of the
  four names with another definition, where the C++ stripping is unsound and can change a
  decision (`Lean4Lean/Tests/TypeAnnotationWrappers.lean`). It replaces an environment
  invariant, so that the empty environment satisfies `VEnvs.WF` (section 1.2).
- `Quot.ind`'s major binder is explicit (section 6), and projections are compared by
  structure name in `isDefEqCore'` and the equivalence manager; both now match the C++ kernel.
- **Primitive recognizer** (`Lean4Lean/Primitive.lean`): extra `checkType` calls read the closed
  pieces of a condition and a well-founded functional in the outer context (section 5.2);
  they concern only reserved primitive names.

## 8. Tests

`Lean4Lean/Tests/` adds executable and specification tests:

- executable oracles: `RecursorOracle.lean` (generated recursor types, metadata and every rule
  compared with the kernel's for a set of declarations), `RecursiveInductive.lean`,
  `NestedRecursorReduction.lean`, `KNormalization.lean`, `ProjectionInference.lean`, `ProjectionReduction.lean`,
  `ProjectionWithoutCasesOn.lean`, `QuotInit.lean`, additions to `NestedInductive.lean` and
  `KernelHardening.lean`;
- realizability: `CanonicalEq.lean`, `CanonicalChoice.lean`;
- the specification: `InductiveSignature.lean` (generated minors and hypotheses),
  `InductiveCompilation.lean`, `InductiveRestoration.lean` (simultaneous substitution),
  `InductiveTheory.lean`, `TypedInductiveCompilation.lean` (the compilation judgment is
  inhabited without unproved theorems), `SpecializedRecursorShape.lean`,
  `ProjectionSpecialization.lean` (a projection that becomes large after universe
  specialization while the native recursor eliminates only into `Prop`);
- negative tests: `InductiveEquationRejection.lean`, `RecursorMetadata.lean`,
  `RestoredRecursorMetadata.lean` (corrupted metadata admits no certificate).
- nested indexed families: `NestedIndexedFamily.lean` (nested occurrences of indexed families,
  and indexed families with parameters inside nested blocks; the generated types,
  constructors and recursors are compared with the kernel's).

`Replay.lean` runs the pure replay core on a hand-built constant table (an axiom, an inductive
type, a definition, an inductive predicate and a theorem) from the empty environment and checks
the added declarations and the agreement of every source constant; corrupting a source
constructor, recursor or inductive type is rejected by the corresponding check.

`docs/inductives/CacheScopeExperiment.lean` is run with `lake env lean` (section 5.2).

## 9. Open

- **Declarative strengthening with canonical `Eq`** is open: no counterexample and no proof.
  Nothing in the verification uses it; the corner is resolved by the constructor certificates
  (section 5.3), which apply to environments built by the checker rather than to arbitrary
  well-formed abstract environments.
- **Realizability** of the canonical hypotheses relies on test-checked facts about the
  production declarations (section 1.3).
- **Confluence without `Eq`.** Non-joinability in the countermodel is argued, not checked.
- **Inherited prototype sorries.** `Lean4Lean.Experimental` has 56 `sorry` declarations in the
  prototypes (`Thierry`, `Thierry2`, `LogRel`, `DomainTheory`, `MoreStepIndexed`, `Stronger`,
  `SExpr`, `ParallelReduction`, `Stratified`, `StratifiedUntyped`), all inherited from
  `master`, which has at least as many. None is in the cone.
  The ported files (`SExpr`, `NormalEq`, `ParallelReduction`, `Stratified`,
  `StratifiedUntyped`, the shape logical relation) build against the extended `VExpr`; the
  global axiom `Params.extra_pat` of `SExpr.lean` is now a hypothesis class.
- **Legacy shape records.** `VInductDecl.CompilesTo` still carries `OrdinaryShape` and
  `NestedShape` beside the finite compilation certificate; they are redundant and could be
  removed.
- **Executable cost.** `guardedIotaCheck` expands natural-number literals in nested
  constructor types, so a large literal makes it slow. Replay performance relative to `master`
  has not been profiled.

## 10. Reading guide

Suggested order, with sizes.

1. The statements: `Lean4Lean/Verify/Environment.lean` (370 lines), `Lean4Lean/Theory/CanonicalEq.lean`,
   `Lean4Lean/Theory/CanonicalChoice.lean`, `VEnvs.WF` in `Lean4Lean/Verify/TypeChecker.lean`.
2. The calculus: `Lean4Lean/Theory/VExpr.lean`, `Lean4Lean/Theory/Typing/Basic.lean` (150),
   `Lean4Lean/Theory/VEnv.lean`, `Lean4Lean/Theory/Typing/Env.lean` (`VEnv.WF'`).
3. The specification: `Lean4Lean/Theory/DeclarationData.lean`, `Lean4Lean/Theory/InductBlock.lean`,
   `Lean4Lean/Theory/Inductive.lean` (1k; `VInductDecl.WF`, `AddInduct`, `EliminatorsWF`),
   `Lean4Lean/Theory/Inductive/{SignatureData,Signature,Compilation,Restoration,CaseSchema,CaseFormation}.lean`
   (1.5k together), then `Formation.lean` (2k).
4. The corrections: `Lean4Lean/Theory/Typing/EliminatorCoherence.lean`,
   `SchemaStructCompat.lean`, `Instance.FreeTarget` in `Signature.lean`.
5. The checker changes: the diff of `Lean4Lean/TypeChecker.lean` (1k), `VState.WF` and
   `leaveScope` in `Lean4Lean/Verify/TypeChecker/Basic.lean` (2k), `divergences.md`,
   `docs/inductives/CacheScopeExperiment.lean`.
6. The corner: `Lean4Lean/Verify/Typing/ProjectionCorner.lean`,
   `Lean4Lean/Theory/Typing/ProjectionCornerChoice.lean`, then `ProjectionCorner*.lean` (4.4k).
7. Head inversion: `HeadInversionDefs.lean`, `HeadInversion.lean`, then
   `HeadInjectivity/Model/{Classes,Obs,Interp,Sound}.lean` (3.2k), `RuleSound.lean`,
   `EtaBind.lean`, `ProjSound.lean`, `Staged.lean`, `Separation.lean`, and the syntactic layer
   `HeadInjectivity/{Uniqueness,FieldType}.lean` (18k in total for the directory).
8. Confluence (outside the cone): `Lean4Lean/Theory/LevelledConfluence.lean`,
   `Lean4Lean/Theory/Typing/LevelledReduction.lean` (4.7k), `WFParams.lean`.
9. The inductive checker: `Lean4Lean/Inductive/Add.lean` (2.2k), then the pipeline:
   `Lean4Lean/Verify/Inductive/ConstructorBoundary.lean` (1k), `Context.lean` (3.5k),
   `Header/` (9k), `Constructor/` (7k), `Recursor/` (51k), `Completed*.lean` (33k), `Run/` (5k),
   `Nested/` (91k, starting from `CaseEliminators.lean`, `EndToEnd.lean`,
   `RestoredEquationWF.lean`, `StrippedValidity.lean`).
10. Quotients: `Lean4Lean/Verify/QuotInit.lean` (630).
11. The audit: `scripts/check-inductive-audit.py`, `scripts/inductive-audit-inventory.json`.

Most of the 218k lines under `Lean4Lean/Verify/Inductive/` are refinement bookkeeping between
the executable's `Expr`/`LocalContext` state and the abstract judgments; the design decisions
are in items 1 to 7 and in the module docstrings of the files named in section 3.
