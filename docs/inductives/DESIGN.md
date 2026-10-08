# Verified inductive declarations: design

This document describes what this pull request proves, how the proof is organised, and what it
changes in the specification and in the executable. Paths are relative to the repository root.
Line counts are approximate and refer to the final tree.

The pull request adds about 330k lines of Lean. Two thirds of it is the refinement proof of
the executable inductive checker (`Lean4Lean/Verify/Inductive/`, 165k lines). The rest is the
metatheory (`Lean4Lean/Theory/Typing/`, 73k added), the generative specification of inductive
types (`Lean4Lean/Theory/Inductive/` and `Lean4Lean/Theory/Inductive.lean`, 15k), the
verification of quotients, the canonical hypotheses and the checker changes
(`Lean4Lean/Verify/` outside `Inductive/`, 19k), executable changes (2k) and tests (2k).

## 1. The result

### 1.1 The theorem

`Lean4Lean/Verify/Environment.lean`:

```lean
theorem addDecl.WF_of_canonicalEq {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq) (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

Every declaration form is covered, including ordinary, mutual and nested inductive
declarations and quotient initialization. The dependency cone has no `sorry`. The theorem is
a thin wrapper around

```lean
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WFCore env)
    (htels : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (hq : ∀ safety, (ves.venv safety).QuotReady)
    (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WFCore env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        VEnvs.CtorTelescopesPreserved env env' ves ves'
```

`VEnvs.WF` is the core invariant `VEnvs.WFCore` together with the constructor-telescope
certificates `VEnvs.AllCtorTelescopes` (section 5.3); the wrapper discharges `htels` from the
certificates, derives `hq` from `heq` (`VEnv.HasCanonicalEq.quotReady`), and carries the
certificates to the output through `CtorTelescopesPreserved`. The iterable form `addDecl.WFHasCanonicalEq`
also returns `HasCanonicalEq` for `ves'` (monotone along `≤`), so the theorem applies again
to the next declaration of a replay.

"Sound" means refinement: whenever the executable `addDecl` returns an environment, that
environment is modelled, at every safety level, by an abstract environment that is well formed
in the sense of `VEnv.WF` and extends the previous model. `VEnv.WF` is the generative
specification of section 2: it says which declarations, with which generated recursors,
projections and computation rules, may be added. The theorem does not address consistency of
the declarative theory `VEnv.IsDefEq` itself.

For inductive declarations there is also a source-facing statement,
`addInductiveDeclaration.finalResultWF` (same file). It returns an `InductiveExtension`,
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
into an `AddDeclChain` from `Kernel.Environment.empty` (`AddDeclChain.WF_empty`). The kernel's `checkEqType`
compares `Eq` only up to `Expr.eqv` and does not look at `Eq.rec` or at safety, so before the step
that initializes the quotient module the driver also checks that `Eq`, `Eq.refl` and `Eq.rec` are
the prelude's (`hasPreludeEq`, sound for `HasPreludeEq`). `replayFromImports.WF` states the same on top of
imports whose well-formedness and canonical `Eq` are assumed: imports are trusted in that mode.

### 1.3 The hypotheses

- `wf : ves.WF env` is the invariant being preserved. `VEnvs.WF`
  (`Lean4Lean/Verify/TypeChecker.lean`) is the core invariant `VEnvs.WFCore` together with
  the constructor telescope certificates (`VEnvs.AllCtorTelescopes`). The core gains fields in this pull
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
- There is no hypothesis about the projection-walk corner: the constructor certificates of
  `VEnvs.WF` resolve it (section 5.3).

A replay from the empty environment is covered by `AddDeclChain.WF_empty`
(`Lean4Lean/Verify/Replay.lean`): every environment reached by adding a list
of declarations one at a time with the checked `addDecl`, starting from
`Kernel.Environment.empty`, has a well-formed model, provided each `quotDecl` comes after the
prelude's `Eq`, `Eq.refl` and `Eq.rec` (`HasPreludeEq`, a decidable property of the
executable environment; before `Eq` exists `quotDecl` has no model).

Canonical `Eq` holds in every environment obtained by replaying `Init.Prelude` past `Eq`.
Realizability is proved up to a fact about the concrete production declaration that is checked
by a test: `addDecl.preludeEq_hasCanonicalEq` (`Lean4Lean/Verify/CanonicalEq.lean`)
takes as hypothesis that the executable installs `Eq.rec` with the production type, which
`Lean4Lean/Tests/PreludeEq.lean` checks. The honest reading of the theorem is therefore:
`addDecl` is sound for environments that contain the prelude's `Eq`, and every declaration of
a replay from the empty environment is sound (`AddDeclChain.WF_empty`).

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
They are per-family case analysis principles (no induction hypotheses).

### 2.2 Declarations and their well-formedness

The declaration data is syntax only (`Lean4Lean/Theory/DeclarationData.lean`): `VInductDecl`
(universe count, parameter count, families with index counts, result levels and
constructors, `isUnsafe`) and the derived `projectionEntries` (one entry for each family with
exactly one constructor). `VInductDecl.WF env decl` (`Lean4Lean/Theory/Inductive.lean`) is
`decl.SourceWF env ∧ decl.FormationWF env`: the source judgment (headers typed, a common
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
(`ContainersInstalled`), so no environment lookup can serve as provenance.
`VInductDecl.CompilesTo env decl block` is the record that installation reads: the block's
families, constructors and projection entries are those of the declaration, its installed
names are distinct, and `CompiledInductive` derives the block.

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
the eliminators are certified (`VInductBlock.EliminatorsWF`: either the declaration has no
families and the block registers no eliminator, or it registers exactly one, with a
`CaseSchema.Registered` certificate and projecting only out of structures registered at the
constructor stage), and `install` succeeds.

`VEnv.WF'` (`Lean4Lean/Theory/Typing/Env.lean`) has, besides `empty` and `decl`, two
constructors that describe the intermediate environments of an installation:
`inductEliminators` registers a certified case schema once the declaration's constants are
present, and `inductProjections` registers the projection entries of a declaration whose
constructors and case eliminator are present. The checker runs that happen after the
constructors are declared and before the recursors are installed (the window) therefore run
in a well-formed environment, which every checker theorem requires. The registry facts that
every well-formed environment satisfies (each schema keeps its registration certificate, a key
fixes its schema, schemas project only out of registered structures, every registered
structure has a registered schema) are the fields of `VEnv.RegistryInv`, proved by one
induction over the history (`VEnv.WF'.registryInv`,
`Lean4Lean/Theory/Inductive/CaseRegistration.lean`).

A case schema (`Lean4Lean/Theory/Inductive/CaseSchema.lean`) is the normalized signature with
its restoration and its original family names; its per-family view and generated case type
and equations are computed. `CaseSchema.Certified` is `CaseCompilationData`: the part of a
compilation that fixes the schema (formation, model, restoration correspondence and scoping,
installed source constants, family typing), without anything about the generated native
recursors, which `elimDF`/`elimIota` never read. Every registration point carries
`CaseSchema.Registered schema base source block key`: the `Certified` certificate, the key
(the name of the first original family) and `HeaderAgreement`.

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
  a block registers no eliminator only if its declaration has no families. Hence every
  registered structure has a registered case eliminator at every point of every history
  (`VEnv.WF.projections_eliminated`), including during the window.
  The certificate is the case-only `CaseCompilationData` because the full `CompilationData`
  includes the typing of the generated recursors, which the window computes.
- **Header agreement** (`CaseSchema.HeaderAgreement`). The restored normalized header of each
  original family is definitionally equal to its declared type.
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
by `Primitive.checkInductive`) go through `Lean4Lean/Verify/Inductive/Primitive/`. For
other declarations the verified lowering result decides: no auxiliary families means the
ordinary path (`Install/OrdinaryExtension.lean`), otherwise the nested path
(`Nested/Restoration/SourceTranslations.lean`, `NestedFinalSpecification.lean`). All three produce an
`InductiveExtension`.

### 3.2 Phases of the ordinary path

- **Headers** (`Lean4Lean/Verify/Inductive/Header/`, 7k). The header loops of
  `Inductive/Add.lean` check each family type, the common parameters and the result
  universes. The proof materializes the abstract headers and their source translation.
- **Constructors** (`Constructor/`, 5.5k). Each constructor type is checked in the environment
  with the headers; positivity, the universe bound on fields and the result shape are
  verified, and each field is related to its strictly positive normal form (the
  `positiveFields` clause of `Models`).
- **Constructor boundary** (`Constructor/CheckedFormation.lean`). From the data available once the
  constructors are declared, the proof computes the source signature
  (`CheckedFormation.sourceSignature`, with `sourceSignature_models`) and the
  declaration's case eliminator `(first family, CaseSchema.ofCompilation decl signature [])`.
  Its certificate is kept in the monotone form `VInductDecl.CaseEliminators env decl reserved
  es`: `EliminatorsWF` over every extension of the source environment in which the
  `reserved` names are fresh and the declaration installs (an ordinary declaration reserves
  no names, a nested one the names fresh in its production environment). Its views are
  `EliminatorsReplay` at one environment, used to rebase the block certificate onto larger
  safety models, and `EliminatorsWF` at the source environment. The window environment
  `(ctors.addEliminators es).addProjections P` is shown well formed by `inductEliminators`
  and `inductProjections` (`VInductBlock.EliminatorsWF.windowWF`). The executable is
  unchanged by this: it has no case eliminators.
- **Recursors** (`Recursor/`, 42k; `Rules/`, 27k). The executable's recursor
  construction (first and second pass over the fields, elimination level, motives, minors,
  induction hypotheses, rules) is shown to produce exactly the translation of the abstract
  generator's output for one canonical `Instance`
  (`Recursor/Entries/TrRecursorVal.lean`, `Recursor/Metadata.lean`). Typing of the generated
  recursor types is not derived from the generator: it is read off the executable's check of
  each generated recursor type (`checkRecursorTypes`), which supplies `RecursiveTypesWF` in
  the window environment; `FamilyTypesWF` likewise comes from checker runs in the window.
  Rules are proved well typed in the recursor
  environment (`Rules/EquationWF.lean`, `Rules/Translation.lean`, `Rules/RuleTranslations.lean`).
- **Assembly** (`Install/BlockCertificate.lean`, `Install/`). The phases assemble into one
  `BlockCertificate` (shared by the ordinary, primitive and nested paths), which
  yields `VInductDecl.CompilesTo`, `VInductBlock.WF`, `EliminatorsWF`, the final `AddInduct`
  and the safety-indexed `VEnvs.WF` of the output.

Embedded checker runs of the inductive checker see a narrow local context
(`AddInductive.Context.checkLCtx`, verified in `Lean4Lean/Verify/Inductive/Context.lean`):
only the binders a run may need (parameters, indices, fields), never majors, motives, minors
or induction hypotheses. Every checker fact is thus produced in the context in which the
proof uses it, and is transported to larger contexts by weakening. A checker run only consults
free variables reachable from its inputs, so the results agree with runs in the larger
context.

### 3.3 Nested declarations

Nested declarations are verified by lowering and restoration (`Nested/`, 65k).
`Nested/Lowering/Basic.lean` and `Nested/Restoration/ExprReplace.lean` (an exact, cache-independent
specification of `Expr.replace`) verify the replacement of maximal nested occurrences by
fresh auxiliary families and its correspondence with the abstract nested expansion. The
lowered declaration runs the ordinary pipeline, including its own constructor boundary. The
restoration loop is then verified: restored constructors, restored recursor types and
restored rules (`Nested/Restoration*.lean`, `Nested/EquationRestoration*.lean`). The
typing of restored equations is transported from the lowered recursor environment by a
context-carrying renaming restoration substitution (`Nested/Restoration/Equations/WF.lean`), which
replaces each auxiliary head by its restoration lambda and renames recursors and projection
type names.

The source block registers its own case eliminator: the boundary signature of the lowered
run, under the same key, restored by the nested compilation's restoration
(`Nested/CaseEliminators/Certificate.lean`), certified from the validated run.

The executable validates the restoration before installing it: restored constructor
types, restored recursor types, and the right-hand side of each restored rule, as the
C++ kernel does (`validateRestoredRecursorRules`).
Rules are validated in a copy of the restored environment in which every restored recursor
has no rules (`stripRecursorRules`), because the abstract iota equations are only added once
the rules are known to be well formed (`Nested/Restoration/Validation/StrippedEnvironment.lean`). The proof reads only
the translation of each restored right-hand side off this pass. The abstract rules are the
restorations of the generated equations: their nested-iota shape and guardedness come from
the generator through restoration (`Nested/Restoration/Equations/GeneratedGuard.lean`, `sourceNestedIotaRule`),
their well-formedness from the restoration substitution, and the final assembly extends the
rule-free assembly base by them (`Nested/Restoration/Equations/RestoredRulesBase.lean`). The translation of the
restored right-hand sides can also be obtained by preservation, without the executable check
(`restoredRuleRhs_translates`, `Nested/Restoration/Equations/RuleRhsTranslation.lean`), which would let the
check run in the complete restored environment as in the C++ kernel; that route still assumes
that the lowered rules keep the auxiliary family names out of the arguments copied by
restoration (`Restoration/RestorableNameAvoidance.lean` proves this for every other restorable name).

The common-parameter prefix of a source constructor is not re-checked. Lowering keeps it
verbatim, the ordinary pipeline checks it for the lowered constructor in the lowered header
environment, and the header stage of the restoration substitution
(`Nested/Restoration/HeaderRenaming.lean`), which replaces each auxiliary header by its restoration
lambda, transports that check to the source header environment, where it fixes the
parameters and the prefix (`NestedRun.nativeSourceParameterWF`).

The parametric nested applications `I Ds` (leanprover/lean4#14577) are type-checked
(`validateNestedAuxiliaries`), as in the C++ kernel. For a nested occurrence of a family with
indices, `I Ds` is a type family and its auxiliary family is itself indexed. The proof closes
each application with lambdas over the lowering parameters and its inferred type with foralls
over the same parameters (`ClosedNestedOccurrencesTyped`, `Nested/Lowering/Basic.lean`), which
is well formed in both cases, and uses only the resulting typing of the restored head
(`AuxiliaryHeadTyping`).

### 3.4 Reconstructed and checked facts

Everything about an inductive declaration's abstract counterpart is reconstructed from the
execution: the `VInductDecl` (by translating the submitted syntax), the normalized signature
and instance, the restoration tables, the case schemas and their certificates. Three kinds of
typing facts are not proved from the generator but read off runtime checks that the
executable performs: the type of each generated recursor (`checkRecursorType`), the restored
nested constructor and recursor types, and the restored nested rules. On every
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
Pi adequacy then forces the iota check, which for `Eq.rec` is equality reflection. The proof
uses soundness of a model only.

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
therefore proved along the declaration history (`WF'.ruleValid`, `Model/EnvValid.lean`): each
rule, eliminator rule and projection entry is valid in the model of the final environment
because the derivations of the environment preceding its declaration are sound there, by the
induction hypothesis. `HeadsClosed` and `ProjsClosed` carry the facts that no later
declaration adds a rule headed by an existing constant or a projection entry for an existing
rule constructor. Constructor arities are read from the model (`Model/TeleArity.lean`):
definitionally equal Pi telescopes ending in rigid spines have equal length, which a purely
syntactic argument cannot give without head inversion.

**The syntactic layer** (`HeadInjectivity/{Core,Uniqueness,FieldType,Fields}.lean`) turns the
chain-level injectivity delivered by the model (`ChainHeadInjectivity`) into the injectivity
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
along `Eq`. In a well-formed `Eq`-free environment (the one of section 5.1) that equation is
not joinable (argued, not checked in Lean). Coherence of eliminators with projections
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

Without scoping no invariant of that form holds. `Lean4Lean/Tests/CacheScope.lean`
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

The primitive recognizer (`Lean4Lean/Primitive.lean`) reads the closed pieces of a
`reflectNatNat` condition, and the functional of a well-founded definition, only under binders
(the condition gadget's, the measure telescope's). The verification brings those readings to the
outer context without strengthening: every such binder is inhabited there (by `Nat.zero`, or by
the gadget's own arguments at it), and substituting the inhabitant leaves a term that does not
mention the binder alone (`TrExprS.peel_outer`, `MLCtx.trExprS_dropN_nat`).

### 5.3 The projection-walk corner

`inferProj` walks the constructor telescope of a structure. Past a field binder whose body
does not depend on it, the walk keeps the body without substituting anything, so the
verification must translate the remainder without that binder. When the field's projection
is typable it inhabits the binder and substitution does this. Otherwise (a data field of a
structure that may be a proposition, which the kernel still walks past) a translation of the
remainder in the smaller context is needed, and general strengthening is not available
(section 5.1).

The proof re-derives the smaller-context translation from the checker's own acceptance of the
constructor type. A frame lemma for the executable
(`Lean4Lean/Verify/TypeChecker/Frame*.lean`: a successful run in a local context with extra
declarations that never occur in its inputs, caches or environment is the same run without
them) and a ghost-telescope verification (`Verify/TypeChecker/GhostTelescope.lean`) show that
when a constructor type is checked, every unused binder of its telescope can be deleted from
the translation. The result is recorded as a depth-bounded certificate `TelTrN`
(`Verify/Typing/TelescopeTranslation.lean`), one per visible constructor at every safety
level (`VEnvs.AllCtorTelescopes`); the bound is the constructor's own arity, which is what the walk
consumes. The certificates hold vacuously for an environment without constructors, are
preserved by every declaration (`VEnvs.CtorTelescopesPreserved`), and the walk uses the delete branch of the
certificate at each non-dependent field. Nested declarations need the stored constructor type
to agree with the checked source type up to binder names
(`Verify/Inductive/Nested/Restoration/InstalledConstructorTypes.lean`), because reusing an auxiliary
renames binders inside reused occurrences, as in the C++ kernel.

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
  constructor owner
  agreement is checked wherever a structure's constructor is looked up, and `isUnsafe` agreement
  wherever the family's visibility is not already known (not in `reduceProjCore`,
  `isDefEqUnitLike` or `expandEtaStruct`); `toCtorWhenStruct` and
  `expandEtaStruct` return the term unchanged where the C++ kernel throws, and when the type
  of the major premise's type does not reduce to a sort. Each
  guard lets the verification justify a step from the registry entry alone, without
  injectivity or head separation. All are redundant on well-formed environments and
  well-typed terms with one exception: structure eta is not applied to a structure whose
  universe is neither always nor never zero (`Sort u`), so a conversion that needs it there
  is rejected.
- **Inductive checker** (`Lean4Lean/Inductive/Add.lean`): restructured into explicit loops
  with total fresh-name searches, narrow checker contexts (section 3.2), unreachable arity
  and result-type guards in recursor construction (kept: the verification cannot show that
  two `whnf` runs agree), and recursor rules built from the first constructor
  traversal. Each generated recursor type is type-checked (`checkRecursorTypes`); the kernel
  of the pinned toolchain does not do this, upstream does since leanprover/lean4#14808, which
  also checks rule type preservation, which lean4lean proves instead. Nested auxiliary types
  are named `_nested.i` rather than `_nested.J_i` (internal names only). The nested
  restoration validation of section 3.3 re-checks restored declarations in side environments
  and type-checks the right-hand sides of the restored rules in the
  stripped environment, as the C++ kernel's revalidation (leanprover/lean4#14621) does in the
  complete restored environment. The nested applications `I Ds`
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

## 8. Tests

`Lean4Lean/Tests/` adds executable and specification tests:

- executable oracles: `RecursorOracle.lean` (generated recursor types, metadata and every rule
  compared with the kernel's for a set of declarations), `RecursiveInductive.lean`,
  `NestedRecursorReduction.lean`, `KNormalization.lean`, `ProjectionInference.lean`, `ProjectionReduction.lean`,
  `ProjectionWithoutCasesOn.lean`, `QuotInit.lean`, additions to `NestedInductive.lean` and
  `KernelHardening.lean`;
- realizability: `CanonicalEq.lean`;
- the specification: `InductiveSignature.lean` (generated minors and hypotheses),
  `InductiveCompilation.lean`, `InductiveRestoration.lean` (simultaneous substitution),
  `InductiveTheory.lean`, `TypedInductiveCompilation.lean` (the compilation judgment is
  inhabited without unproved theorems), `SpecializedRecursorShape.lean`,
  `ProjectionSpecialization.lean` (a projection that becomes large after universe
  specialization while the native recursor eliminates only into `Prop`);
- negative tests: `SortEquationRejection.lean`, `CorruptRecursorMetadata.lean`,
  `CorruptRestoredRecursorMetadata.lean` (corrupted metadata admits no certificate).
- nested indexed families: `NestedIndexedFamily.lean` (nested occurrences of indexed families,
  and indexed families with parameters inside nested blocks; the generated types,
  constructors and recursors are compared with the kernel's).

`Replay.lean` runs the pure replay core on a hand-built constant table (an axiom, an inductive
type, a definition, an inductive predicate and a theorem) from the empty environment and checks
the added declarations and the agreement of every source constant; corrupting a source
constructor, recursor or inductive type is rejected by the corresponding check.

`Lean4Lean/Tests/CacheScope.lean` pins the output of the experiment of section 5.2.

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
- **Executable cost.** Replay performance relative to `master` has not been profiled.

## 10. Reading guide

Suggested order, with sizes.

1. The statements: `Lean4Lean/Verify/Environment.lean` (370 lines), `Lean4Lean/Theory/CanonicalEq.lean`,
   `VEnvs.WF` in `Lean4Lean/Verify/TypeChecker.lean`.
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
   `Lean4Lean/Tests/CacheScope.lean`.
6. The corner: `Lean4Lean/Verify/Typing/TelescopeTranslation.lean` (`TelTrN`),
   `CtorTelescopes` in `TelescopeTranslationLemmas.lean`, `instantiateProjectionFields.WF_tel` in
   `Lean4Lean/Verify/TypeChecker/Projection.lean`, then `Verify/TypeChecker/GhostTelescope.lean`.
7. Head inversion: `HeadInversionDefs.lean`, `HeadInversion.lean`, then
   `HeadInjectivity/Model/{Classes,Obs,Interp,Sound}.lean` (3.2k), `RuleSound.lean`,
   `EtaBind.lean`, `ProjSound.lean`, `EnvValid.lean`, `Separation.lean`, and the syntactic layer
   `HeadInjectivity/{Uniqueness,FieldType}.lean` (18k in total for the directory).
8. Confluence (outside the cone): `Lean4Lean/Theory/LevelledConfluence.lean`,
   `Lean4Lean/Theory/Typing/LevelledReduction.lean` (4.7k), `WFParams.lean`.
9. The inductive checker: `Lean4Lean/Inductive/Add.lean` (2.2k), then the pipeline:
   `Lean4Lean/Verify/Inductive/Constructor/CheckedFormation.lean` (1k), `Context.lean` (3.5k),
   `Header/` (7k), `Constructor/` (5.5k), `Recursor/` (42k), `Rules/` (27k), `Install/` (5k),
   `Primitive/` (4.5k), `Prelude/` (1k),
   `Nested/` (65k, starting from `CaseEliminators/Certificate.lean`, `Restoration/SourceTranslations.lean`,
   `Restoration/Equations/WF.lean`, `Restoration/Validation/StrippedEnvironment.lean`).
10. Quotients: `Lean4Lean/Verify/QuotInit.lean` (630).
11. The audit: `scripts/check-inductive-audit.py`, `scripts/inductive-audit-inventory.json`.

Most of the 165k lines under `Lean4Lean/Verify/Inductive/` are refinement bookkeeping between
the executable's `Expr`/`LocalContext` state and the abstract judgments; the design decisions
are in items 1 to 7 and in the module docstrings of the files named in section 3.
