# Verified inductive declarations: design

This document describes what this pull request proves, how the proof is organised, and what it
changes in the specification and in the executable. Paths are relative to the repository root.
Line counts are approximate and refer to the final tree.

The pull request adds about 250k lines of Lean. Two thirds of it is the refinement proof of
the executable inductive checker (`Lean4Lean/Verify/Inductive/`, 165k lines). The rest is the
metatheory (`Lean4Lean/Theory/Typing/`, 45k added), the generative specification of inductive
types (`Lean4Lean/Theory/Inductive/` and `Lean4Lean/Theory/Inductive.lean`, 11k), the
verification of quotients, the canonical hypotheses and the checker changes
(`Lean4Lean/Verify/` outside `Inductive/`, 19k), executable changes (2k) and tests (3k).

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
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (hq : ∀ safety, (ves.venv safety).QuotReady)
    (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety)
```

The wrapper derives `hq` from `heq` (`VEnv.HasCanonicalEq.quotReady`). The constructor-telescope
certificates (section 5.3) are not a separate hypothesis: they follow from the installed blocks
recorded in `VEnvs.WF` (`VEnvs.WF.ctorTelescopes`). The iterable form `addDecl.WFHasCanonicalEq`
also returns `HasCanonicalEq` for `ves'` (monotone along `≤`), so the theorem applies again
to the next declaration of a replay.

The checker has two cache modes (`Lean4Lean/CacheMode.lean`), a runtime tag in the `cacheMode`
field of `FuelConfig`:

```lean
structure GlobalCacheLicense : Type where
  ok : ∀ env : VEnv, env.WF → env.HasCanonicalEq → env.Strengthening
inductive CacheMode where
  | scoped
  | global (license : GlobalCacheLicense)
```

The default `.scoped` restores the context-relative caches when a binder is closed; `.global`
keeps them for the whole run as the C++ kernel does, and can be selected only with a license, a
proof of context strengthening (section 5.1) of which no inhabitant is known. The theorem holds in
both modes:

```lean
theorem addDecl.WF_of_canonicalEq_mode {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (heq : ∀ safety, (ves.venv safety).HasCanonicalEq) (decl : Declaration) (mode : CacheMode) :
    (addDecl env decl (check := true) (fuel := { cacheMode := mode })).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety
```

and `addDecl.WF_of_canonicalEq` is its instance at `.scoped`, since `{}` is `{ cacheMode := .scoped }`
(section 5.2).

"Sound" means refinement: whenever the executable `addDecl` returns an environment, that
environment is modelled, at every safety level, by an abstract environment that is well formed
in the sense of `VEnv.WF` and extends the previous model. `VEnv.WF` is the generative
specification of section 2: it says which declarations, with which generated recursors,
projections and computation rules, may be added. The theorem does not address consistency of
the declarative theory `VEnv.IsDefEq` itself.

For inductive declarations there is also a source-facing statement,
`addInductiveDeclaration.WF_spec` (same file). It returns an `InductiveExtension`,
whose `specification` field ties the output to an abstract `VEnv.AddInduct` of the exact
translation of the submitted source declaration (`TrInductDeclCore`), so a model cannot be
attributed to a different (for example lowered) declaration. It assumes that the source has
no loose bound variables (`SourceBVarClosed`), which the executable does not check;
`WF_preserves`, used by `addDecl.WF`, does not need it.

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
compares the type of `Eq` with the prelude's up to `Expr.eqv` but does not look at its safety, so
before the step that initializes the quotient module the driver also checks that `Eq` is safe,
with one universe parameter and a type `==` to the prelude's (`hasCanonicalEqType`, sound for
`HasCanonicalEqType`: every translation of the type is the canonical one, since `TrExprS.eqv`
moves it to the prelude's syntax, whose syntactic translation `TrSyn` is the canonical type). This
is exactly what the abstract model of `quotDecl` consumes (`QuotReady`); nothing is required of
`Eq.refl` or `Eq.rec`. `replayPure.WF_fromImports` states the same for the
pure replay `replayPure` on top of imports whose well-formedness and canonical `Eq` are assumed:
imports are trusted in that mode. It does not cover the module loading of the executable's
`replayFromImports` (`importModulesCore`, `finalizeImport`), only the replay that follows it.
A targeted replay (`decl := some d`, replaying only the constants `d` depends on) fails unless `d`
is a safe, non-partial source constant, and its result records that `d` was checked
(`ReplayResult.target`); `replayFresh.WF_target` states that `d` is then present and agrees with
the source constant. Which constants make up the dependency cone of `d` is not characterized.

### 1.3 The hypotheses

- `wf : ves.WF env` is the invariant being preserved. `VEnvs.WF`
  (`Lean4Lean/Verify/Environment/Model.lean`) is one abstract environment per safety level,
  related to the kernel environment by the translation `TrEnv`, with the primitives, and with
  every inductive constant accounted for by an installed block (`InstalledBlocks`, section
  3.4). It holds for the empty environment the executable replays from (`VEnvs.WF.empty`,
  `Lean4Lean/Verify/Environment.lean`): there are no blocks, and only the translation is not
  vacuous. There is no invariant about the type-annotation wrappers:
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
- There is no hypothesis about the constructor telescopes walked by projection inference:
  the installed blocks of `VEnvs.WF` carry a certificate for every constructor (section 5.3).

A replay from the empty environment is covered by `AddDeclChain.WF_empty`
(`Lean4Lean/Verify/Replay.lean`): every environment reached by adding a list
of declarations one at a time with the checked `addDecl`, starting from
`Kernel.Environment.empty`, has a well-formed model, provided each `quotDecl` comes after a safe
`Eq` with the canonical type (`HasCanonicalEqType`, established by the executable check
`hasCanonicalEqType`; before `Eq` exists `quotDecl` has no model).

Canonical `Eq` holds in every environment obtained by replaying `Init.Prelude` past `Eq`.
Realizability is proved up to a fact about the prelude's concrete declaration that is checked
by a test: `addDecl.preludeEq_hasCanonicalEq` (`Lean4Lean/Verify/CanonicalEq.lean`)
takes as hypothesis that the executable installs `Eq.rec` with the prelude's type, which
`Lean4Lean/Tests/PreludeEq.lean` checks. The honest reading of the theorem is therefore:
`addDecl` is sound for environments that contain the prelude's `Eq`, and every declaration of
a replay from the empty environment is sound (`AddDeclChain.WF_empty`).

- The cache mode: in the default scoped mode nothing is assumed. The mode-parametric forms
  (`addDecl.WF_mode`, section 5.2) assume the mode is sound for the input models
  (`CacheMode.Sound`), which in the global mode is canonical `Eq`; `WF_of_canonicalEq_mode` has it
  from `heq`. The fuel-generic inductive dispatch theorems carry the same assumption as `hmode`,
  true for every scoped configuration.

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
the types of dependencies. The roots are the top-level theorems (in both cache modes), the replay theorems of section
1.2, the three inductive dispatch theorems, `addQuot.WF`, the checker's `whnf` and recursor
reduction theorems, the prefix-unfolding and quotient theorems (`PrefixUnfold.defeq`,
`QuotPrefixUnfold.defeq`, `QuotRegistered.propInhabitant_app`), `NormalEq.parRed`,
`RecursorConstruction.typeTranslations` and `IsDefEq.full_church_rosser`. It fails on any `sorry` and on any axiom
not listed in `scripts/inductive-audit-inventory.json`. A second set of strict roots (the
generator definitions of section 2, a few foundational lemmas, and the confluence theorem
`VEnv.WF.church_rosser` of section 4.2 with `WF.params`, `WF.equationCoverage` and
`WF.singletonCoverage`) may depend only on the three standard axioms. The self-test checks that the walker finds a `sorry` behind an opaque body and
an axiom used only in a type.

Timing against `master` (merge base `8223d223`, same toolchain, same machine;
`lake exe lean4lean --fresh M`, median of three runs, wall time and peak RSS from GNU `time -v`;
the branch in its default scoped cache mode):

| replay | `master` | branch |
|---|---|---|
| `--fresh Init.Prelude` (1975 declarations) | 0.45 s, 124 MiB | 0.55 s, 130 MiB |
| `--fresh Init.Core` (3953 declarations) | 0.62 s, 124 MiB | 0.75 s, 132 MiB |
| `--fresh Init.System.IO` (43609 declarations) | 31.2 s, 362 MiB | 55.9 s, 333 MiB |

On the two small replays most of the difference is driver startup, not checking: the same binary
run directly on a nonexistent module (which scans the search path for `.olean` files, more of them
in the branch's build directory) takes 0.20 s on `master` and 0.29 s on the branch. The slowdown on
`Init.System.IO` is the scoped caches (section 5.2). The global mode cannot be selected in the
executable (it needs a `GlobalCacheLicense`), so it has no row; an uncommitted build of the branch
whose configuration parser accepted the global mode with a `sorry` license, for timing only,
replayed `Init.System.IO` in 29.2 s (median of three), below `master`, and `Init.Prelude` and
`Init.Core` in 0.52 s and 0.71 s. The extra checks of the branch (`checkRecursorTypes`, the
side-environment re-checks of section 3.3) therefore cost nothing measurable on this corpus. A
`perf` profile agrees: the branch's flat profile has the same functions in the same proportions
as `master`'s (`whnfCore'`, `inferType'`, `EquivManager.isEquiv`, `reduceRecursor`, instantiation
and reference counting), with 1.8 times as many samples, i.e. the same work repeated after the
caches are restored at binder exits rather than a new hot spot. No declaration of these replays
takes lean4lean over a second on `master`; on the branch two do (`Array.extract_append` proof
terms, 1.5 to 1.8 s).

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
translates to. Recursors remain constants with stored iota equations (`defeqs`).
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
iota equation. `InductiveSignature.Models` relates a signature to the source declaration: same names,
arities and result levels, constructor types definitionally equal in the environment with the
family headers, and every field definitionally a strictly positive normal form in the branch its
classification names (`classifiedFields`, `VInductDecl.ClassifiedFieldNormalForm`): an `external`
field is definitionally a type that mentions no family of the block, a `recursive` field a
telescope over family-free domains ending in a family applied to the parameters and family-free
indices. The generator therefore gives an induction hypothesis to exactly the fields whose
positive normal form ends in a family. The recorded shape of a recursive field (binders, target
family, indices) is constrained by the typing of its generated induction hypothesis
(`Instance.GeneratedIHsWellTyped`): in a well-formed recursor-checking environment in which the
families are rigid, it has the target family and binder count of the field's normal form, and
binders and indices definitionally equal to the normal form's, compared in the context of the
induction hypothesis (`Instance.recursiveShape_correspondence`,
`Lean4Lean/Theory/Inductive/RecursiveShapeCorrespondence.lean`).
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
`VInductDecl.CompilesTo env decl block`, the judgment that installation reads, abbreviates
`CompiledInductive env decl block`. That the block's families, constructors and projection
entries are those of the declaration, and that its installed names are distinct, are accessor
theorems (`CompilesTo.types`, `.ctors`, `.projections`, `.names`) proved by induction on
`CompiledInductive`, whose `replay` constructor preserves source and block.

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
`CaseSchema.RegistrationCertificate` and projecting only out of structures registered at the
constructor stage), and `install` succeeds. `VDecl.WF.induct` takes only the `AddInduct`;
`VEnv.AddInduct.sourceWF` recovers `decl.WF env` from it.

`VEnv.WF'` (`Lean4Lean/Theory/Typing/Env.lean`) has, besides `empty` and `decl`, two
constructors that describe the intermediate environments of an installation:
`inductEliminators` registers a certified case schema once the declaration's constants are
present, and `inductProjections` registers the projection entries of a declaration whose
constructors and case eliminator are present. The checker runs that happen after the
constructors are declared and before the recursors are installed (in the recursor-checking
environment) therefore run
in a well-formed environment, which every checker theorem requires. The registry facts that
every well-formed environment satisfies (each schema keeps its registration certificate, a key
fixes its schema, schemas project only out of registered structures, every registered
structure has a registered schema) are the fields of `VEnv.RegistryInv`, proved by one
induction over the history (`VEnv.WF'.registryInv`,
`Lean4Lean/Theory/Inductive/CaseRegistration.lean`).

A case schema (`Lean4Lean/Theory/Inductive/CaseSchema.lean`) is the normalized signature with
its restoration and its source family names; its per-family view and generated case type
and equations are computed. `CaseSchema.Certified` is `CaseCompilationData`: the part of a
compilation that fixes the schema (formation, model, restoration correspondence and scoping,
installed source constants, family typing), without anything about the generated
recursors, which `elimDF`/`elimIota` never read. Every registration point carries
`CaseSchema.RegistrationCertificate schema base source block key`: the `Certified` certificate, the key
(the name of the first source family) and `HeaderAgreement`.

Restoration is a partial syntactic operation, `Restoration.expr`. Its metatheory goes through
one interface for relating environments, the environment interpretation
(`Lean4Lean/Theory/Typing/Interpretation.lean`). A `VEnv.Interpretation` maps the syntax of a
source environment into a target: each constant is either interpreted by a closed
universe-polymorphic term (instantiated at the occurrence's universes, so a constant may become
an application) or renamed; projection owners and abstract eliminators (key and owner) are
renamed. `I.Sound envS envL P` collects the obligations: closed interpreting terms
(`Interpretation.Closed`); each interpreted constant has the interpretation of its type up to
definitional equality (`ConstClause`); each definitional-equality rule holds after
interpretation at every admissible universe instantiation (`DefEqClause`); and the eliminator
and projection rules hold after interpretation in every target context satisfying the context
invariant `P` (`EliminatorClause`, `ProjectionClause`). The transport theorem,
`Interpretation.Sound.isDefEq`, is proved once: for every invariant closed under the context
extensions of the typing rules (`VEnv.CtxInvariant`), a sound interpretation maps every
derivation of `envL` from a context whose image satisfies `P` to a derivation of `envS`
(`Sound.hasType` and `Sound.isDefEqCtx` follow). Two invariants are used: `fun _ _ => True`,
the context-free transport, and `VEnv.TypedCtx`, well-formed contexts, which admits rules that
hold only up to beta subject reduction. A sound interpretation for an invariant is sound for
every stronger one (`Sound.weaken`). That no interpreting term is a Pi type
(`Interpretation.PreservesTelescopes`) is a separate shape condition, needed only where a
projection field type is computed by walking a constructor telescope
(`VProjectionInfo.fieldType_interpret`, `ProjectionClause.of_fixed`).

The restoration interpretation (`Restoration.interpretation`,
`Lean4Lean/Theory/Inductive/RestorationInterpretation.lean`) interprets each auxiliary head
(family or constructor) by its lambda telescope `λ params, J levels args` over the common
parameters and renames every other constant and every projection owner by the recursor
renaming (`Restoration.renaming`). `Restoration.Agrees r I` says that `I` interprets exactly the
heads of `r`, in this way, and otherwise renames as `r` does; then `r.expr e` is a beta reduct of
`I.expr e` for every `e` whose projection owners `I` fixes (`Restoration.Agrees.go_betaRed`),
hence definitionally equal to it at every type in a well-formed context
(`Restoration.Agrees.expr_simAt`). A `Restoration.Substitution envS envL r I`, a sound
interpretation for well-formed contexts that agrees with `r`, therefore transports closed typing
judgments and equations of `envL` to their restorations in `envS` (`Restoration.expr_hasType`,
`Restoration.equation_wf`, `Restoration.expr_isDefEqU`).

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
- **Case eliminators after the constructors.** Every block with families registers one
  certified case eliminator, keyed by its first family, between constructors and projections;
  a block registers no eliminator only if its declaration has no families. Hence every
  registered structure has a registered case eliminator at every point of every history
  (`VEnv.WF.projections_eliminated`), including in the recursor-checking environment.
  The certificate is the case-only `CaseCompilationData` because the full `CompilationData`
  includes the typing of the generated recursors, which is computed in the recursor-checking
  environment.
- **Header agreement** (`CaseSchema.HeaderAgreement`). The restored normalized header of each
  source family is definitionally equal to its declared type.
- **Fields are classified by their positive normal form** (`Models.classifiedFields`). Without
  it a signature could mark a recursive field `external`: for `N | z | s : N → N` with the
  argument of `s` external, the generated eliminator has a successor minor `∀ n, motive (s n)`
  without induction hypothesis, a well-typed eliminator that is not Lean's recursor.
  `Lean4Lean/Tests/RecursiveFieldClassification.lean` shows that this signature no longer models
  `N`. The executable decides the classification twice, by the positivity check in the
  environment with the headers and by `isRecArg` in the recursor's checking context; it checks
  that the two agree (section 3.2).
- **Recursor typings are stated in the recursor-checking environment.** `Instance.GeneratedIHsWellTyped` and
  `FamilyTypesWF` are required in the environment with constructors, the declaration's own
  case eliminators and its projection entries, because that is where the executable checks
  the generated types. Stating them in a smaller environment or context would need
  strengthening (section 5). For the same reason `Models` does not compare family types:
  only constructor types are compared, and family applications are required to be well typed.
- **Restored eliminators.** The transport of recursor-checking derivations from a lowered
  nested declaration to its source allows a lowered schema to be matched by a registered source
  schema with the same signature whose restoration agrees with the interpretation
  (`VEnv.RestoredEliminator.clause`, `Lean4Lean/Theory/Inductive/RestorationInterpretation.lean`).
  Its rules hold only up to beta subject reduction, so it is an eliminator clause for
  well-formed contexts (`VEnv.TypedCtx`).

## 3. The verified installation pipeline

### 3.1 Dispatch

`addInductiveDeclaration.WF_preserves` (`Lean4Lean/Verify/Environment.lean`) splits on
the executable's own branch selection. Primitive declarations (`Bool` and `Nat`, recognized
by `Primitive.checkInductive`) go through `Lean4Lean/Verify/Inductive/Primitive/`. For
other declarations the verified lowering result decides: no auxiliary families means the
ordinary path (`Install/OrdinaryExtension.lean`), otherwise the nested path
(`Nested/Install/Result.lean`, `Nested/Restoration/SourceTranslations.lean`). All three produce an
`InductiveExtension`.

### 3.2 Phases of the ordinary path

- **Headers** (`Lean4Lean/Verify/Inductive/Header/`, 7k). The header loops of
  `Inductive/Add.lean` check each family type, the common parameters and the result
  universes. The proof materializes the abstract headers and their source translation.
- **Constructors** (`Constructor/`, 5.5k). Each constructor type is checked in the environment
  with the headers; positivity, the universe bound on fields and the result shape are
  verified, and each field is related to its strictly positive normal form in the branch the
  positivity check reports (`checkPositivity` returns whether the field is recursive, and
  `checkConstructors` returns these classifications; the `classifiedFields` clause of `Models`).
- **Checked formation** (`Constructor/CheckedFormation.lean`). From the data available once the
  constructors are declared, the proof computes the source signature
  (`CheckedFormation.sourceSignature`, with `sourceSignature_models`) and the
  declaration's case eliminator `(first family, CaseSchema.ofCompilation decl signature [])`.
  Its certificate is kept in the monotone form `VInductDecl.CaseEliminators env decl reserved
  es`: `EliminatorsWF` over every extension of the source environment in which the
  `reserved` names are fresh and the declaration installs (an ordinary declaration reserves
  no names, a nested one the names fresh in its kernel environment). Its views are
  `EliminatorsReplay` at one environment, used to rebase the block certificate onto larger
  safety models, and `EliminatorsWF` at the source environment. The recursor-checking environment
  `(ctors.addEliminators es).addProjections P` is shown well formed by `inductEliminators`
  and `inductProjections` (`VInductBlock.EliminatorsWF.recursorCheckingEnvWF`). The executable is
  unchanged by this: it has no case eliminators.
- **Recursors** (`Recursor/`, 42k; `Rules/`, 27k). The executable's recursor
  construction (motive pass and minor pass over the fields, elimination level, motives, minors,
  induction hypotheses, rules) is shown to produce exactly the translation of the abstract
  generator's output for one `Instance`
  (`Recursor/Entries/TrRecursorVal.lean`, `Recursor/Metadata.lean`). Typing of the generated
  recursor types is not derived from the generator: it is read off the executable's check of
  each generated recursor type (`checkRecursorTypes`), which supplies `GeneratedIHsWellTyped` in
  the recursor-checking environment; `FamilyTypesWF` likewise comes from checker runs there.
  The minor pass classifies each field again (`isRecArg`, in the recursor's checking context
  and the environment with the constructors); `checkRecursiveFields` requires, for a safe
  declaration, that the fields given induction hypotheses are exactly those the positivity
  check classified as recursive. The two classifications are `whnf` runs on the same field
  types in different environments and universe parameters, and with the fields opened as
  different free variables. That renaming is what prevents a proof: `whnf` asks `isDefEq`
  for K-like iota, and `isDefEq` decides through the equivalence manager's hash test and
  pointer-equality tests, which are not invariant under renaming in the model
  (`Tests/FVarRenamingEquivManager.lean`), while a definitional argument cannot recover the
  syntactic parameter test of `isValidIndApp?`. So the agreement is checked rather than proved
  (`RecursorConstruction.recursiveFieldsChecked`; `divergences.md` gives the details). With
  it the classification of the generation signature is that of the checked formation (`SignatureSpec.classified`, `sourceClasses`), and
  its fields inherit the classified normal forms of the source fields. On the primitive path the
  classifications are computed from the run (`PrimitiveHeaderEnvironment.checkedClasses`), using
  that `whnf` returns an inductive constant unchanged
  (`Verify/Inductive/Constructor/PositivityConstant.lean`).
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
lowered declaration runs the ordinary pipeline, including its own checked formation. The
restoration loop is then verified: restored constructors, restored recursor types and
restored rules (`Nested/Restoration/`, with the rules in `Nested/Restoration/Equations/`). The
typing of restored equations is transported from the lowered recursor environment by the
restoration substitution of the run (`NestedRun.restoredEquationSubstitution`,
`Nested/Restoration/Equations/WF.lean`): the restoration interpretation of section 2.3 is sound
from the lowered recursor environment into the recursor environment of the source block, for
well-formed contexts. Soundness is built along the lowered installation. The header stage
(`NestedRun.headerInterpretationSound`, `Nested/Restoration/HeaderRenaming.lean`) holds in every
context: base constants and source headers are fixed, auxiliary headers are interpreted by
their restoration lambdas. The constructor stage (`constructorInterpretationSound`) keeps the
source constructors (whose source types are definitionally equal to the interpreted lowered
types, by restoration at the header stage), interprets the auxiliary constructors, and adds the
lowered eliminator as a restored eliminator and the lowered projections; the projections of
auxiliary structure-like families are renamed to their containers and hold only up to beta
reduction of the restoration lambdas (`ProjectionClause.of_specialization`,
`Nested/Restoration/AuxiliaryProjections.lean`), as do those of source structures
(`ProjectionClause.of_ctorType_betaRed`, `Nested/Restoration/Equations/ProjectionRenaming.lean`).
The recursor stage keeps the lowered recursors under their restored names
(`Restoration.interpretation_ofAddConstants_recursors`). The source constructor types are
restored through the variant keeping projection owners (`Restoration.constInterpretation`), sound
from the lowered header environment into the source header environment in every context
(`Restoration.constInterpretation_substitution`, `Nested/Restoration/SourceConstructors.lean`).
Lowering needs no interpretation: the lowered declaration is re-checked by the ordinary
pipeline, and lowering is related to the source only syntactically (`Expr.replace`) and by the
abstract nested expansion.

The source block registers its own case eliminator: the checked-formation signature of the lowered
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
rule-free assembly base by them (`Nested/Restoration/Equations/RestoredRulesBase.lean`).

The common-parameter prefix of a source constructor is not re-checked. Lowering keeps it
verbatim, the ordinary pipeline checks it for the lowered constructor in the lowered header
environment, and the header stage of the restoration interpretation
(`Nested/Restoration/HeaderRenaming.lean`), which interprets each auxiliary header by its
restoration lambda, transports that check to the source header environment, where it fixes the
parameters and the prefix (`NestedRun.sourceCoreParameterWF`).

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

What an installation leaves behind is recorded once, as a descriptor of the installed block
(`InstalledBlock`, `Lean4Lean/Verify/Environment/Blocks.lean`): its kernel headers,
constructors and recursors, the abstract declaration with the abstract family and
constructor of each kernel header and constructor, the case eliminators and projections it
registers, the telescope certificate of each constructor, and the stage reached. The stages
follow the executable: at `.headers` the headers are installed and the constructors they list
are absent, which is how their types are checked; at `.constructors` the constructors are
installed and the block's case eliminators and projections registered (the
recursor-checking environment, and the side environments of nested restoration, where the
recursors may already be present); at `.complete` the abstract block is installed
(`VEnv.InstalledBelow`) and every constructor agrees with its family on the common
parameters. A descriptor has a kernel side, which every observer sees, and an abstract side
for the observers that see the block; recursor alignment is required for the recursors the
observer sees.

The environment invariant `InstalledBlocks safety env venv stage` says that every inductive
header, constructor and recursor of `env` belongs to a well-formed descriptor of at least
`stage`, and that every projection entry registered in `venv` was registered by a visible
descriptor. `VEnvs.WF` and `VEnvAt` carry it at `.complete`; the checking invariant
`CheckingEnv.Valid`, and the checker context `VContext`, at `.headers`, since a staged
environment carries partial descriptors. Every lookup the checker reads is a projection of it:
mutual closure, constructor owners, listed constructors (and their presence when every block
has its constructors), the projection registry in both directions
(`InstalledBlocks.projectionRegistryCoherent`, and `InstalledBlocks.projectionHeader`: a
structure with a registry entry is a visible header listing exactly the registered
constructor), recursor alignment (`InstalledBlocks.recursorEnvCoherent`), the presence of the
constructors of every recursor's major inductive (`InstalledBlocks.recursorMajorCtors`), the
constructor telescopes, constructor parameter agreement and the installed families. Each
installation step extends the invariant once: an unrelated constant keeps every descriptor
(`InstalledBlocks.addFresh`, `addDefinitions`), a header installed on its own is its own
descriptor at `.headers` (`addFreshListed`), and the installation of a declaration up to the
constructor stage or completely adds the descriptor read off it (`addCtorStage`,
`addInduct`, both instances of `addBlock`), on the ordinary, primitive, prelude and nested
paths alike. A primitive batch installs atomically and has no checking invariant between its
header and its constructors (`AtomicAddConstants`, `LocalContextWF`); the invariant is
re-established at the end of the batch.

### 3.5 Shared proof infrastructure

The phase certificates remain in the inductive checker, while generic expression, context and
abstract typing facts live below it. Adapters import these shared facts and connect them to
the phase certificates. Theorem interfaces carry the hypotheses needed by their conclusions;
redundant arguments are removed together with their caller arguments.

| Responsibility | Modules |
| --- | --- |
| Abstract telescope syntax, lifting and application spines | `Theory/VExpr/Telescope.lean`, `Theory/VExpr/TelescopeLemmas.lean` |
| Abstract telescope typing and context conversion | `Theory/Typing/Telescope.lean` |
| Guarded iota closure and abstract case certificates | `Theory/Inductive/GuardedIotaLemmas.lean`, `Theory/Inductive/CaseEliminators.lean` |
| Source expression telescope shapes and typed transport | `Verify/Expr/Telescope.lean`, `Verify/Typing/Telescope.lean` |
| Concrete local-context inclusion | `Verify/LocalContext/SubContext.lean` |
| Syntactic translation (`TrSyn`, `trSyn?`) and the typed layer (`TrResidual`, `TrTyped`) | `Verify/Typing/Syntactic/{Context,Levels,Basic,Transport,Typed,TypedAPI}.lean` |
| Constructor telescope certificates (`TelWF`, `TelTrN`, `CtorTelescopeAt`, section 5.3) | `Verify/Typing/TelescopeTranslation.lean`, `Verify/Typing/TelescopeTranslationLemmas.lean` |
| Checker context structure and semantic embeddings | `Verify/TypeChecker/MLCtxLemmas.lean`, `Verify/TypeChecker/CheckingContext.lean`, `Verify/Typing/CheckingContext.lean` |
| Semantics shared by ordinary and recursor frames | `Verify/Inductive/Context/Semantics.lean` |
| Installation lookup effects and matched family/constructor indices | `Verify/Inductive/Install/Metadata.lean`, `Verify/Inductive/SourceAlignment.lean` |

`ContextWF` and `RecursorContextWF` separately certify the ordinary and recursor universe
contracts. Their operations use `ContextSemantics c Us` for the shared context proofs.
Ordinary frames retain
`typeCheckerLParams = none`; recursor frames retain `some recLparams` and the explicit
`RecursorLParams` origin certificate. `BindingContextWF` remains the separate operational
certificate. The existing projection equalities still hold by reduction.

A lowered run's header, constructor and recursor certificates are transported together through
`LoweredRun.Phases` (`Nested/Lowering/Phases.lean`). `NestedRun` exposes that package and its
lowering context through `Nested/Install/RunView.lean`; consumers use these named views instead
of rebuilding dependent sigma casts. The shared parameter context lives in
`Install/ParameterContext.lean`.

The selected induction-hypothesis comparison in `Rules/RecursiveResults.lean` separates source
provenance (`HypothesisSource`), exact replay equations (`HypothesisReplay`), translation and
closed typing (`HypothesisTyping`), and the opened residual comparison (`HypothesisResidual`).
`HypothesisFrame` and `HypothesisDomainFrame` carry these obligations to the RHS proof through
named fields, which consumers use directly. Translation and
typing after inserting earlier hypotheses use one shared proof, so the domain comparison and
RHS consumer no longer reconstruct that context transport independently.

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
well-formed environment, without canonical `Eq`. Every inversion lemma of
`Lean4Lean/Theory/Typing/Injectivity.lean` derives from it. Uniqueness of types
(`IsDefEq.uniq`, `Lean4Lean/Theory/Typing/UniqueTyping.lean`) is the uniqueness and collapse
of the syntactic layer (`HeadInjectivity/Uniqueness.lean`, described below) applied to the
chain-level core `VEnv.WF.chainHeadInjectivity`. The checker verification uses uniqueness
throughout.

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
stored rule (delta, quotient, recursor iota after restoration, generic case equation) is a
lambda telescope over a head applied to bound variables, ignored terms and a constructor
major. Fields are bound in one of three modes. When the major's family is not a proposition
at the instance, they come from the major's constructor observations. When it is a
proposition with large (singleton) elimination, the major is ignored and data fields are read
from the indices at which they occur literally, proof fields being proofs and so
observationally empty. When the family is projection-registered, constructor spines carry
only field observations (structure eta forces this), so the rule is identified from the
head type and fields are bound from the major's field observations (`Model/EtaBind.lean`).

**History induction.** Several semantic facts used by these cases come from derivations in
earlier environments that are not subderivations of the node being interpreted: an installed
family's recorded result sort, the propositional typing of a singleton's proof fields, the
soundness of a projection entry's constructor telescope and family header. Soundness is
therefore proved along the declaration history (`WF'.envValid`, `Model/EnvValid.lean`): each
rule, eliminator rule and projection entry is valid in the model of the final environment
because the derivations of the environment preceding its declaration are sound there, by the
induction hypothesis. `HeadsClosed` and `ProjsClosed` carry the facts that no later
declaration adds a rule headed by an existing constant or a projection entry for an existing
rule constructor. Constructor arities are read from the model (`Model/TeleArity.lean`):
definitionally equal Pi telescopes ending in rigid spines have equal length, which a purely
syntactic argument cannot give without head inversion.

**The syntactic layer** (`HeadInjectivity/{ChainInjectivity,Uniqueness,FieldType,Fields}.lean`) turns the
chain-level injectivity delivered by the model (`ChainHeadInjectivity`) into the injectivity
fields of `HeadInversion`. Uniqueness up to chains and a congruence property are proved by
one induction on the strong typing derivation, which makes `proj_fieldType` provable:
unused, untypable earlier projections never occur in the field type, so the induction never
visits them. None of these files imports uniqueness or confluence.

### 4.2 Confluence

`FullReduction.church_rosser` (`Lean4Lean/Theory/Typing/LevelledReduction.lean`, 4.6k) is
proved by decreasing diagrams (`Lean4Lean/Theory/LevelledConfluence.lean`) over a split of the
full step relation into four levels: normal equality without eta (levels, proof
irrelevance), parallel reduction (beta, recursor and case-schema patterns), parallel delta
(recursor and quotient prefix unfolding, projection of constructor applications), and parallel
eta expansion. Function eta is not restricted to non-head positions, because the transports
of computation through normal equality need expansions in function position.

The result for the declarative judgment is `IsDefEq.church_rosser` and
`IsDefEq.full_church_rosser` (`Lean4Lean/Theory/Typing/FullChurchRosser.lean`): two
definitionally equal terms reduce to normally equal terms. Both are stated under two
hypothesis classes: `Params` (`ChurchRosser.lean`: the environment, its well-formedness, the
registered recursor data and the stored patterns with their properties) and
`FullEquationCoverage` (`FullReduction.lean`: both sides of every installed equation reduce
to normally equal terms).

`VEnv.WF.church_rosser` (`Lean4Lean/Theory/Typing/Confluence/WFParams.lean`) instantiates both
classes for every well-formed environment with canonical `Eq`:

```lean
theorem VEnv.WF.church_rosser {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) (H : env.IsDefEq U Γ e₁ e₂ A) :
    letI := henv.params U
    ∃ e₁' e₂', FullReduction Γ e₁ e₁' ∧ FullReduction Γ e₂ e₂' ∧ NormalEq Γ e₁' e₂'
```

The instance `WF.params` reads its data off a head registry chosen along the declaration
history (`WF.headRegistry`, `Confluence/RegistryOfWF.lean`). Its patterns
(`ConcretePattern`, `Confluence/Patterns.lean`) are the definition unfoldings, the generated
iota rules of the registered recursors (`GeneratedIotaPattern`) and, when the quotient is
declared, the quotient rule; every field of `Params` is a theorem. Soundness of a generated
iota rule (`GeneratedIotaPattern.sound`, `Confluence/GeneratedIotaSoundness.lean`) is the iota
theorem for the restored recursor, constructor and rule shapes of the compilation that
registered the recursor. The structure-major fields (`ConcretePattern.struct_major`,
`ConcretePattern.iota_params`, `CaseRedex.struct_major`) follow from declaration provenance
and from the coherence of eliminators with projections (`VEnv.WF.eliminatorsCoherent`),
which is part of well-formedness.

`WF.equationCoverage` derives `FullEquationCoverage` from the registry for every installed
equation except the one case `WF.SingletonCoverage` names: the equation of a
large-eliminating singleton recursor at a universe specialization whose source is `Prop`.
There the generated iota rule's guard fails, and `WF.singletonCoverage` joins the equation by
the singleton prefix unfolding (`RecursorRegistered.zero_join`,
`Confluence/SingletonCoverage.lean`), which reconstructs the constructor from the major.
The proof fields of the reconstructed constructor are extracted by the recursor itself into
`Prop`, and since a field's type may mention the earlier data fields, the extraction casts
those along `Eq`. This is the only use of `HasCanonicalEq`. In a well-formed `Eq`-free
environment (the one of section 5.1) that equation is not joinable (argued, not checked in
Lean).

`WF.church_rosser` and its coverage lemmas are audit roots (section 1.4) and depend only on
the standard axioms. Confluence is not in the dependency cone of the top-level theorem of
section 1.1.

## 5. Strengthening, cache modes and constructor telescopes

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
irrelevance is circular, and the calculus does not normalize. In the default cache mode the
verification is organised so that it never moves a typing fact to a smaller context; the global
cache mode, which does, takes strengthening as the content of its license (section 5.2).

The second attempt (`STRENGTHENING_ATTEMPT_2026-10-09b.md`, `Theory/Typing/Strengthening/`)
reduces the statement, with every step checked, to `TypedFront` (strengthening for endpoints
typed below at a common type) given two environment typings (`GenericTypesTyped₀`,
`GenericRulesTyped₀`) and one `Prop`-structure field closure (`ProjFieldFrontPropN`), each
itself a closed-telescope strengthening (`Strengthening/Final.lean`,
`cancel_iff_typedFront_final`); every guard of every reduction rule descends under
`TypedFront`, eta reducts are handled by the eta-chain closure, and the certificate route is
closed for syntactic ranks. Still no proof and no counterexample.

### 5.2 Cache modes

The checker's cache mode (`CacheMode`, a field of `FuelConfig`) decides what happens to the
context-relative state when a binder is closed (`State.exitScope`, `Lean4Lean/TypeChecker.lean`).

In the default scoped mode every binder saves and restores it (`State.leaveScope`): the inference
caches, the `whnf` caches, the equivalence manager and the failure cache are put back on leaving the
binder; the name generator stays advanced and the `unfold` cache, which depends only on the
environment, is kept. `isDefEqLambda` and `isDefEqForall` always compare bodies under a binder.
Every cache entry is then derivable in the current context, and the binder exit needs nothing
(`State.WF.leaveScope` in `Lean4Lean/Verify/TypeChecker/Basic.lean`).

In the global mode the state of the body is kept, as in the C++ kernel, whose caches belong to the
whole run, and `isDefEqLambda`/`isDefEqForall` open a binder only when a body has loose bound
variables, as `is_def_eq_binding` does. The cache invariants are conditional
(`Lean4Lean/Verify/Typing/ConditionallyTyped.lean`): an entry whose key mentions only variables of
the current context is derivable in it. The equivalence manager's facts hold in the current
context extended by variables of closed binders (`EqvScope`). Closing a binder
(`State.WF.restrict`) moves the entries whose keys avoid the binder out of it by strengthening
(`ConditionallyHasType.weakN_inv` and `ConditionallyWHNF.weakN_inv`, through
`TrExprS.restrictFV'_inv`); using a fact of the equivalence manager (`State.WF.eqv_uniq`) and
comparing closed bodies outside their binder (`lowerClosedBody`) strengthen in the same way. The
strengthening is `license.ok venv wf heq`, for the checker's environment `venv`, which has
canonical `Eq` whenever the input models do (`CacheMode.Sound`, recorded in `State.WF`). These are
the only uses of the license. The universe-support and parameter-uniformity cache invariants are
syntactic and are restricted without it. The frame lemma and the constructor-telescope
certificates of section 5.3 serve both modes unchanged.

The mode-parametric statements are `addDecl.WF_of_canonicalEq_mode`, `addDecl.WFHasCanonicalEq_mode`,
`addDecl.WF_mode` (with `hmode : ∀ safety, mode.Sound (ves.venv safety)`) and
`replayPure.WF_fromImports_mode`; the statements at `fuel := {}` are their scoped instances. There
is no global-mode form of `replayFresh.WF`: a fresh replay checks the prelude's declarations before
`Eq` exists, where the license gives no strengthening, and the countermodel of section 5.1 shows
that none holds in general there. What a global-mode fresh replay would need is strengthening for
the environments of the prelude before canonical `Eq`, which is false in some well-formed
environments.

Without restoring, no invariant of the scoped form holds. `Lean4Lean/Tests/CacheScope.lean`
builds the countermodel environment above (no `Eq`) and a closed definition of type `SJ` with
value `let seed := fun (q : P v) => ... ; (zz : SI)`, where the body of `seed` forces the
comparisons `SI ≡ ... ≡ SJ` under `q`. The C++ kernel accepts this definition and rejects it
without `seed`; the scoped mode rejects it (the global mode would accept it). So the executable as
run can reject a declaration the C++ kernel accepts. Such a declaration relies on a conversion
fact outside the scope where it holds: `SI ≡ SJ` is derivable under `q` but not in the outer
context, so it is the C++ acceptance that is non-local. Both fresh replays of `Init.Prelude` and
`Init.Core` are unaffected, and `Lean4Lean/Tests/CacheMode.lean` checks that the mode plumbing is
the identity in the scoped mode. This is one of several divergences of the executable;
`divergences.md` lists all of them, with an audit table of every executable change (section 7.2).

The primitive recognizer (`Lean4Lean/Primitive.lean`) reads the closed pieces of a
`reflectNatNat` condition, and the functional of a well-founded definition, only under binders
(the condition gadget's, the measure telescope's). The verification brings those readings to the
outer context without strengthening: every such binder is inhabited there (by `Nat.zero`, or by
the gadget's own arguments at it), and substituting the inhabitant leaves a term that does not
mention the binder alone (`TrExprS.peel_outer`, `MLCtx.trExprS_dropN_nat`).

### 5.3 Constructor telescopes for the projection walk

`inferProj` walks the constructor telescope of a structure. Past a field binder whose body
does not depend on it, the walk keeps the body without substituting anything, so the
verification must translate the remainder without that binder. When the field's projection
is typable it inhabits the binder and substitution does this. Otherwise (a data field of a
structure that may be a proposition, which the kernel still walks past) a translation of the
remainder in the smaller context is needed, and general strengthening is not available
(section 5.1).

The syntax of that translation is free: translation is a function of the source syntax and the
context (`TrSyn`, computed by `trSyn?`, `Verify/Typing/Syntactic/Basic.lean`), and a source that
does not mention a binder translates without it, to the lowered result (`TrSyn.lower`). A typed
translation is exactly a syntactic translation whose result is well typed, together with the
typing of dead let values and the presence of literal types (`TrResidual`;
`TrExprS.iff_typed`, `Verify/Typing/Syntactic/Typed.lean`). What remains to be supplied at a
deleted binder is therefore one typing judgment: the residual telescope is well typed in the
context without the binder.

The certificate of a constructor `ci` is

```
def CtorTelescopeAt (venv : VEnv) (ci : ConstructorVal) : Prop :=
  ∃ T, trSyn? ci.levelParams [] ci.type = some T ∧
    TelWF venv ci.levelParams (AddInductive.constructorArity ci.type) [] ci.type T
```

the computed translation of the stored type with `TelWF`
(`Verify/Typing/TelescopeTranslation.lean`): the typing of the translation and of every residual
telescope obtained by deleting unused binders of the leading `forallE` spine, each in its own
context, with the residual obligations of the source. The depth is the constructor's own arity,
which is what the walk consumes. There is one certificate per visible constructor at every safety
level (`CtorTelescopes`, derived from the installed blocks of `VEnvs.WF` by
`VEnvs.WF.ctorTelescopes`). The walk (`instantiateProjectionParameters.WF_tel`,
`instantiateProjectionFields.WF_tel` in `Verify/TypeChecker/Projection.lean`) carries the pair
`TelTrN` of the syntactic translation and `TelWF`, substitutes at parameters and dependent fields
(`TelTrN.inst`) and deletes at non-dependent fields (`TelTrN.delete_closed`); the transports
(`Verify/Typing/TelescopeTranslationLemmas.lean`) are each a `TrSyn` lemma for the syntax and a
typing lemma for `TelWF`.

The typing at deleted binders is re-derived from the checker's own acceptance of the constructor
type. A locality theorem for the executable (`Methods.withFuel_locality`, stated with
`M.PreservesGhostRestriction` in `Lean4Lean/Verify/TypeChecker/Frame*.lean`: a successful run in
a local context with extra declarations that never occur in its inputs, caches or environment is
the same run without them) and a ghost-telescope verification
(`Verify/TypeChecker/GhostTelescope.lean`, `checkType.WF_telTr`) show that when a constructor
type is checked, the run read in the local context without the deleted binders types every
residual telescope. Nested declarations need the stored constructor type to agree with the
checked source type up to binder names (`Verify/Inductive/Nested/Restoration/InstalledConstructorTypes.lean`,
`TelTrN.eqv`), because reusing an auxiliary renames binders inside reused occurrences, as in the
C++ kernel.

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
(with an entry) a divergence found by the audit. The default scoped cache mode (section 5.2) is not the only
divergence, but it is the only one that can change a decision against the C++ kernel on an
environment whose type-annotation wrappers are the prelude's: it rejects a term whose
acceptance needs a conversion fact outside its scope. The executable also implements the C++
behaviour, the global cache mode, which is selected only with a `GlobalCacheLicense`; no
inhabitant of it exists, so the global mode is verified but cannot be run. The wrapper stripping below can change a decision only on an environment that redefines a
wrapper name. The other changes cannot change a decision except through checker fuel, as follows.

- **Redundant guards**, each listed in `divergences.md`: `tryEtaStructCore` applies
  structure eta only at never-zero sorts; `toCtorWhenStruct` returns the term unchanged when
  the type of the major premise's type does not reduce to a sort. `expandEtaStruct` also
  returns it unchanged where the C++ kernel throws on an absent constructor, a branch that is
  unreachable: the major inductive of every present recursor has its constructors present
  (`VContext.expandEtaStruct_ctor`). The checking context carries, as
  projections of its installed blocks (section 3.4), the constructor listing in both
  directions: every present constructor is listed by its present owner with the owner's
  `isUnsafe` (`ConstructorOwnersPresent`), and every name a present header lists is, if
  present, a constructor of that header with its `isUnsafe` (`ListedConstructorsCoherent`). With it, `inferProj`, `tryEtaStructCore`,
  `isDefEqUnitLike` and `expandEtaStruct` read structures and constructors as the C++ kernel
  does. The listing holds in the staged environments of an inductive declaration because
  the declaration's constructor names are absent from the environment in which their types
  are checked; the executable checks that only when it declares the constructors, and the
  proof takes it from the success of that later step (`declareConstructors.namesAbsent`).
  The registry is read in both directions too: a structure with an abstract projection
  registry entry is a visible header listing exactly the registered constructor
  (`InstalledBlocks.projectionHeader`), so `reduceProjCore` checks, like `reduce_proj_core`,
  only that the head constructor belongs to the structure. All the guards are redundant on well-formed environments and
  well-typed terms with one exception: structure eta is not applied to a structure whose
  universe is neither always nor never zero (`Sort u`), so a conversion that needs it there
  is rejected.
- **Inductive checker** (`Lean4Lean/Inductive/Add.lean`): restructured into explicit loops
  with total fresh-name searches, narrow checker contexts (section 3.2), unreachable arity
  and result-type guards in recursor construction (kept: the verification cannot show that
  two `whnf` runs agree), the comparison of the minor pass's field classification with the
  positivity check's (`checkRecursiveFields`: the two runs differ by a renaming of free
  variables, under which the decisions of `isDefEq` are not provably invariant), and recursor
  rules built from
  the first constructor traversal. Each generated recursor type is type-checked (`checkRecursorTypes`); the kernel
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
- realizability: `PreludeEq.lean`;
- the specification: `InductiveSignature.lean` (generated minors and hypotheses),
  `InductiveCompilation.lean`, `InductiveRestoration.lean` (simultaneous substitution),
  `InductiveTheory.lean`, `TypedInductiveCompilation.lean` (the compilation judgment is
  inhabited without unproved theorems), `SpecializedRecursorShape.lean`,
  `ProjectionSpecialization.lean` (a projection that becomes large after universe
  specialization while the recursor eliminates only into `Prop`);
- negative tests: `SortEquationRejection.lean`, `CorruptRecursorMetadata.lean`,
  `CorruptRestoredRecursorMetadata.lean` (corrupted metadata admits no certificate),
  `RecursiveFieldClassification.lean` (a signature marking a recursive field `external` does
  not model its declaration);
- name dependence of the checker: `FVarRenamingEquivManager.lean` (the equivalence manager's
  hash test answers differently on a renaming of two free variables, which is why the two
  field classifications are compared rather than proved equal).
- nested indexed families: `NestedIndexedFamily.lean` (nested occurrences of indexed families,
  and indexed families with parameters inside nested blocks; the generated types,
  constructors and recursors are compared with the kernel's).

`Replay.lean` runs the pure replay core on a hand-built constant table (an axiom, an inductive
type, a definition, an inductive predicate and a theorem) from the empty environment and checks
the added declarations and the agreement of every source constant; corrupting a source
constructor, recursor or inductive type is rejected by the corresponding check.

`Lean4Lean/Tests/CacheScope.lean` pins the output of the experiment of section 5.2, and
`Lean4Lean/Tests/CacheMode.lean` checks that the cache-mode plumbing is the identity in the scoped
mode (the default configuration is the scoped one, and replays of oracle dependency cones agree
between the default and the explicitly scoped configuration).

## 9. Open

- **Declarative strengthening with canonical `Eq`** is open: no counterexample and no proof.
  Nothing in the verification uses it; the constructor telescopes walked by projection
  inference are covered by the constructor certificates
  (section 5.3), which apply to environments built by the checker rather than to arbitrary
  well-formed abstract environments.
- **Realizability** of the canonical hypotheses relies on test-checked facts about the
  prelude's declarations (section 1.3).
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

1. The statements: `Lean4Lean/Verify/Environment.lean` (440 lines), `Lean4Lean/Theory/CanonicalEq.lean`,
   `VEnvs.WF` in `Lean4Lean/Verify/Environment/Model.lean`, and `InstalledBlocks` in
   `Lean4Lean/Verify/Environment/Blocks.lean`.
2. The calculus: `Lean4Lean/Theory/VExpr.lean`, `Lean4Lean/Theory/Typing/Basic.lean` (150),
   `Lean4Lean/Theory/VEnv.lean`, `Lean4Lean/Theory/Typing/Env.lean` (`VEnv.WF'`).
3. The specification: `Lean4Lean/Theory/DeclarationData.lean`, `Lean4Lean/Theory/InductBlock.lean`,
   `Lean4Lean/Theory/Inductive.lean` (640; `VInductDecl.WF`, `AddInduct`, `EliminatorsWF`),
   `Lean4Lean/Theory/Inductive/{SignatureData,Signature,Compilation,Restoration,CaseSchema,CaseFormation}.lean`
   (1.3k together), then `Formation.lean` (1.6k).
4. The corrections: `Lean4Lean/Theory/Typing/EliminatorCoherence.lean`,
   `SchemaStructCompat.lean`, `Instance.FreeTarget` in `Signature.lean`.
5. The checker changes: `Lean4Lean/CacheMode.lean`, the diff of `Lean4Lean/TypeChecker.lean`
   (1k), `State.WF`, `State.WF.leaveScope`, `State.WF.restrict` and `State.WF.exitScope` in
   `Lean4Lean/Verify/TypeChecker/Basic.lean` (2k), `divergences.md`,
   `Lean4Lean/Tests/CacheScope.lean`, `Lean4Lean/Tests/CacheMode.lean`.
6. Constructor telescopes: `Lean4Lean/Verify/Typing/TelescopeTranslation.lean` (`TelWF`,
   `TelTrN`), `CtorTelescopeAt` in `TelescopeTranslationLemmas.lean`, `instantiateProjectionFields.WF_tel` in
   `Lean4Lean/Verify/TypeChecker/Projection.lean`, then `Verify/TypeChecker/GhostTelescope.lean`.
7. Head inversion: `HeadInversionDefs.lean`, `HeadInversion.lean`, then
   `HeadInjectivity/Model/{Classes,Obs,Interp,Sound}.lean` (3k), `RuleSound.lean`,
   `EtaBind.lean`, `ProjSound.lean`, `EnvValid.lean`, `Separation.lean`, and the syntactic layer
   `HeadInjectivity/{ChainInjectivity,Uniqueness,FieldType}.lean` (16k in total for the directory).
8. Confluence (outside the cone): `Lean4Lean/Theory/LevelledConfluence.lean`,
   `Lean4Lean/Theory/Typing/LevelledReduction.lean` (4.6k), `FullReduction.lean`,
   `FullChurchRosser.lean`, then its instance for well-formed environments in
   `Lean4Lean/Theory/Typing/Confluence/` (11k): `WFParams.lean` (the theorem), `Params.lean`,
   `Patterns.lean`, `RegistryOfWF.lean`, `GeneratedIotaSoundness.lean` (1.2k),
   `GeneratedIotaCoverage.lean` and `SingletonCoverage.lean` (1k).
9. The inductive checker: `Lean4Lean/Inductive/Add.lean` (1.6k), then the pipeline:
   `Lean4Lean/Verify/Inductive/Constructor/CheckedFormation.lean` (1k), `Context.lean` (3k),
   `Header/` (7k), `Constructor/` (5.5k), `Recursor/` (42k), `Rules/` (27k), `Install/` (5k),
   `Primitive/` (4.5k), `Prelude/` (1k),
   `Nested/` (65k, starting from `CaseEliminators/Certificate.lean`, `Restoration/SourceTranslations.lean`,
   `Restoration/Equations/WF.lean`, `Restoration/Validation/StrippedEnvironment.lean`), whose
   restoration metatheory is `Lean4Lean/Theory/Typing/Interpretation.lean` and
   `Lean4Lean/Theory/Inductive/RestorationInterpretation.lean` (1.4k together).
10. Quotients: `Lean4Lean/Verify/QuotInit.lean` (630).
11. The audit: `scripts/check-inductive-audit.py`, `scripts/inductive-audit-inventory.json`.

Most of the 165k lines under `Lean4Lean/Verify/Inductive/` are refinement bookkeeping between
the executable's `Expr`/`LocalContext` state and the abstract judgments; the design decisions
are in items 1 to 7 and in the module docstrings of the files named in section 3.
