import Lean4Lean.Theory.Inductive.Compilation
import Lean4Lean.Theory.Inductive.CaseFormation

namespace Lean4Lean

/-- Legacy shape facts retained during proof migration. These constrain names,
arities, and ordered coverage, but leave motive/minor domains and equation
syntax underspecified. They cannot justify installation by themselves. -/
structure VInductDecl.OrdinaryShape
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  projections : block.projections = decl.projectionEntries
  recursors : List.Forall₂ (fun type recursor =>
    Nonempty (decl.RecursorShape type recursor))
    decl.types block.recursors
  rules : ∃ envTypes envCtors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule (envCtors.addProjections block.projections)
        block owned.1 owned.2 rule))
      decl.ownedConstructors block.rules
  names : List.Nodup ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- Ordinary installation requires both its direct generator and the shared
finite compilation derivation. Legacy shape facts remain available during
proof migration, but do not justify installation by themselves. -/
structure VInductDecl.OrdinaryCompilation
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop
    extends VInductDecl.OrdinaryShape env decl block where
  canonical : InductiveSignature.Compiles env decl block
  finite : CompiledInductive env decl block

/-- Legacy nested shape facts used by the proof migration. Auxiliary RHS
guardedness does not fix equation syntax; this record cannot justify an
installation without the independent finite compilation derivation. -/
structure VInductDecl.NestedShape
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock) where
  main : VInductiveType
  rest : List VInductiveType
  types_source : decl.types = main :: rest
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  projections : block.projections = decl.projectionEntries
  primaryRecursors : List VConstVal
  auxiliaryRecursors : List VConstVal
  recursors_eq : block.recursors = primaryRecursors ++ auxiliaryRecursors
  primary_recursors : List.Forall₂ (fun type recursor =>
    Nonempty (decl.NestedRecursorShape type recursor))
    decl.types primaryRecursors
  primaryRules : List VDefEq
  auxiliaryRules : List VDefEq
  rules_eq : block.rules = primaryRules ++ auxiliaryRules
  primary_rules : ∃ envTypes envCtors,
    env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.NestedIotaRule block owned.1 owned.2 rule))
      decl.ownedConstructors primaryRules
  auxiliary_guarded : ∀ rule ∈ auxiliaryRules,
    rule.rhs.GuardedRuleRhs (block.recursors.map (·.name))
  names : List.Nodup ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- Only a finite, canonically generated nested derivation can justify
installation. Legacy shape evidence is retained for downstream proof migration. -/
structure VInductDecl.NestedCompilation
    (env : VEnv) (decl : VInductDecl) (block : VInductBlock)
    extends VInductDecl.NestedShape env decl block where
  canonical : CompiledInductive env decl block

/-- Abstract compilation, separate from the executable compiler. Both paths
require the shared finite derivation; ordinary compilation also retains its
direct generation witness for downstream proofs. -/
inductive VInductDecl.CompilesTo (env : VEnv) : VInductDecl → VInductBlock → Prop
  | ordinary : VInductDecl.OrdinaryCompilation env decl block →
      VInductDecl.CompilesTo env decl block
  | nested : VInductDecl.NestedCompilation env decl block →
      VInductDecl.CompilesTo env decl block

/-- Both installation paths expose the same finite generation judgment. -/
theorem VInductDecl.CompilesTo.compiled
    (H : VInductDecl.CompilesTo env decl block) : CompiledInductive env decl block := by
  cases H with
  | ordinary H => exact H.finite
  | nested H => exact H.canonical

theorem VInductDecl.OrdinaryShape.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (Hblock : block.WF env')
    (H : decl.OrdinaryShape env block) :
    decl.OrdinaryShape env' block := by
  rcases H.rules with
    ⟨oldTypes, oldCtors, holdTypes, holdCtors, holdRules⟩
  rcases Hblock with
    ⟨envTypes, envCtors, _envRecursors, htypes, hctors, _hrecs, _⟩
  have htypesLE := VEnv.addConstVals_mono henv holdTypes htypes
  have hctorsLE := VEnv.addConstVals_mono htypesLE holdCtors hctors
  exact { H with
    rules := ⟨envTypes, envCtors, htypes, hctors,
      Lean4Lean.List.Forall₂.imp
      (fun _ _ h => let ⟨rule⟩ := h;
        ⟨rule.mono (VEnv.addProjections_mono hctorsLE)⟩)
      holdRules⟩ }

theorem InductiveSignature.Instance.RecursiveTypesWF.mono {s : InductiveSignature}
    {g : InductiveSignature.Instance s} {env env' : VEnv}
    (H : g.RecursiveTypesWF env) (hle : env ≤ env') :
    g.RecursiveTypesWF env' :=
  fun index j hj => (H index j hj).mono hle

theorem InductiveSignature.FamilyTypesWF.mono {s : InductiveSignature}
    {env env' : VEnv} {uvars : Nat}
    (H : s.FamilyTypesWF env uvars) (hle : env ≤ env') :
    s.FamilyTypesWF env' uvars :=
  fun owner => ⟨(H owner).1.mono fun h => h.mono hle, (H owner).2.mono hle⟩

theorem InductiveSignature.Models.mono
    {s : InductiveSignature} {env env' envTypes' : VEnv} {decl : VInductDecl}
    (H : s.Models env decl) (henv : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes') :
    s.Models env' decl := by
  rcases H.constructors with ⟨envTypes, htypesOld, hctors⟩
  have hle := VEnv.addConstVals_mono henv htypesOld htypes
  refine { H with
    families := ?_
    constructors := ⟨envTypes', htypes, ?_⟩
    positiveFields := ?_ }
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ _ h => h) H.families
  · exact Lean4Lean.List.Forall₂.imp
      (fun _ _ h => ⟨h.1, h.2.1, h.2.2.mono hle⟩) hctors
  · rcases H.positiveFields with hunsafe | ⟨envTypesPos, htypesPos, hpos⟩
    · exact .inl hunsafe
    · refine .inr ⟨envTypes', htypes, ?_⟩
      intro ctor hc i hi
      obtain ⟨normalized, hnormal, hshape⟩ := hpos ctor hc i hi
      exact ⟨normalized,
        hnormal.mono (VEnv.addConstVals_mono henv htypesPos htypes), hshape⟩

theorem InductiveSignature.Instance.Admissible.mono
    {s : InductiveSignature} {g : s.Instance} {env env' : VEnv}
    (H : g.Admissible env) (henv : env ≤ env') : g.Admissible env' := by
  refine { H with elimination := ?_ }
  rcases H.elimination with h | h | ⟨⟨hn, hc, hfields⟩, hfree⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨⟨hn, hc, ?_⟩, hfree⟩)
    intro ctor hctor i hi
    exact (hfields ctor hctor i hi).imp (fun h => h.mono henv) id

theorem InductiveSignature.Compiles.mono
    {env env' envTypes' envCtors' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : Compiles env decl block) (henv : env ≤ env')
    (htypes : env'.addConstVals decl.typeConstants = some envTypes')
    (hctors : envTypes'.addConstVals decl.constructorConstants = some envCtors') :
    Compiles env' decl block := by
  rcases H.generated with
    ⟨s, g, envTypes, hmodel, htypesOld, hadmissible, ⟨envCtors, hctorsOld, hrec, hfam⟩, hrest⟩
  have htypesLE := VEnv.addConstVals_mono henv htypesOld htypes
  have hprojLE := VEnv.addProjections_mono (entries := decl.projectionEntries)
    (VEnv.addConstVals_mono htypesLE hctorsOld hctors)
  exact ⟨s, g, envTypes', hmodel.mono henv htypes, htypes,
    hadmissible.mono htypesLE,
    ⟨envCtors', hctors, hrec.mono hprojLE, hfam.mono hprojLE⟩, hrest⟩

theorem VInductDecl.OrdinaryCompilation.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env') (Hblock : block.WF env')
    (H : decl.OrdinaryCompilation env block) :
    decl.OrdinaryCompilation env' block := by
  have hfinite := H.finite.mono henv Hblock
  rcases Hblock with ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrest⟩
  refine { H.toOrdinaryShape.mono henv
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrest⟩ with
    canonical := H.canonical.mono (envTypes' := envTypes) (envCtors' := envCtors) henv ?_ ?_
    finite := hfinite }
  · simpa [H.types] using htypes
  · simpa [H.ctors] using hctors

theorem VInductDecl.CompilesTo.mono
    {env env' : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (henv : env ≤ env')
    (Hblock : block.WF env')
    (H : decl.CompilesTo env block) : decl.CompilesTo env' block := by
  cases H with
  | ordinary H => exact .ordinary (H.mono henv Hblock)
  | nested H =>
    have hcanonical := H.canonical.mono henv Hblock
    rcases H.primary_rules with
      ⟨_oldTypes, _oldCtors, _holdTypes, _holdCtors, holdRules⟩
    rcases Hblock with
      ⟨envTypes, envCtors, _envRecursors, htypes, hctors, _hrecs, _⟩
    exact .nested { H with
      canonical := hcanonical
      primary_rules := ⟨envTypes, envCtors, htypes, hctors,
        holdRules⟩ }

theorem VInductDecl.CompilesTo.types
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    block.types = decl.typeConstants := by
  cases H with
  | ordinary H => exact H.types
  | nested H => exact H.types

theorem VInductDecl.CompilesTo.ctors
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    block.ctors = decl.constructorConstants := by
  cases H with
  | ordinary H => exact H.ctors
  | nested H => exact H.ctors

theorem VInductDecl.CompilesTo.projections
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    block.projections = decl.projectionEntries := by
  cases H with
  | ordinary H => exact H.projections
  | nested H => exact H.projections

theorem VInductDecl.CompilesTo.names
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) :
    ((block.types ++ block.ctors ++ block.recursors).map (·.name)).Nodup := by
  cases H with
  | ordinary H => exact H.names
  | nested H => exact H.names

theorem VInductDecl.CompilesTo.sourceNames
    {env : VEnv} {decl : VInductDecl} {block : VInductBlock}
    (H : decl.CompilesTo env block) : decl.sourceNames.Nodup := by
  have hprefix : ((block.types ++ block.ctors).map (·.name)).Nodup := by
    apply List.Nodup.sublist (l₂ :=
      (block.types ++ block.ctors ++ block.recursors).map (·.name))
    · simpa [List.map_append, List.append_assoc] using
      (List.prefix_append
        ((block.types ++ block.ctors).map (·.name))
        (block.recursors.map (·.name))).sublist
    · exact H.names
  simpa [VInductDecl.sourceNames, H.types, H.ctors, List.map_append]
    using hprefix

/-! ## Ordinary-or-nested formation derivations

Nested formation refers only to prior, finitely derived installed inductive
blocks. Keeping installation provenance in the same mutual derivation as
formation avoids both an uncheckable environment lookup and a definitional
cycle through `AddInduct`. -/

/-- Exact construction of one direct auxiliary constructor before its own
body is recursively lowered. -/
structure VInductDecl.DirectAuxConstructor
    (env : VEnv) (U : Nat)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (containerFamily auxiliaryFamily : VInductiveType)
    (source target : VConstVal) : Prop where
  name : target.name = source.name.replacePrefix containerFamily.name
    auxiliaryFamily.name
  uvars : target.uvars = auxiliaryFamily.uvars
  type : env.IsDefEqU U [] target.type
    (VExpr.wrapForalls sourceParams
      (VExpr.instantiateForallPrefix (source.type.instL levels) baseArgs))

/-- A rigid head used to package two corresponding argument lists as one
expression relation.  Unlike a bound variable, it is stable when the
surrounding constructor telescope is lifted. -/
def VInductDecl.nestedTrailingMarker : VExpr :=
  .const `_nested.trailing []

mutual

/-- Formation evidence is either the ordinary judgment or a finite nested
expansion into an independently ordinary well-formed declaration. -/
inductive VInductDecl.FormationEvidence : VEnv → VInductDecl → Prop
  | ordinary {env decl} : VInductDecl.FormationWF env decl →
      VInductDecl.FormationEvidence env decl
  | nested {base env decl} : VInductDecl.NestedFormationWF base decl →
      base ≤ env →
      VInductDecl.FormationEvidence env decl

/-- Cycle-free provenance for a prior container block. The prior declaration
has its own finite source/formation derivation, compiles to the exact block,
and that well-formed block occurs below the ambient environment. -/
inductive VEnv.InstalledInductCertificate : VEnv → VInductDecl → Prop
  | intro {env container base block installed} :
      VInductDecl.SourceWF base container →
      VInductDecl.FormationEvidence base container →
      container.CompilesTo base block →
      block.WF base →
      VInductBlock.install base block = some installed →
      installed ≤ env →
      VEnv.InstalledInductCertificate env container

/-- One legal maximal nested-application replacement. The generated family
is an exact parameter specialization of a family in a previously installed
container block, and its direct constructors are the corresponding exact
specializations with deterministic production names.  The executable
lowering certificate separately retains that some concrete parameter syntax
mentions the finite lowering queue.  That occurrence is intentionally not a
premise here: `TrExprS` erases metadata and let types/values and interprets
projections opaquely, so a concrete occurrence need not survive in `VExpr`.
Such an erased-only occurrence may generate a semantically unused auxiliary;
this remains sound because the prior-container specialization is exact and
ordinary formation checks the complete expanded finite block. -/
inductive VInductDecl.NestedAuxiliarySource :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | intro {env sourceTypesEnv source generated depth input output container
      containerFamily auxiliaryFamily sourceParams baseArgs levels
      auxiliaryLevels inputBaseArgs sourceTrailing targetTrailing} :
      env.addConstVals source.typeConstants = some sourceTypesEnv →
      VEnv.InstalledInductCertificate sourceTypesEnv container →
      containerFamily ∈ container.types →
      auxiliaryFamily ∈ generated →
      sourceParams.length = source.nparams →
      baseArgs.length = container.nparams →
      (∀ arg ∈ baseArgs, arg.ClosedN source.nparams) →
      levels.length = container.uvars →
      (∀ level ∈ levels, level.WF source.uvars) →
      auxiliaryFamily.uvars = source.uvars →
      sourceTypesEnv.IsDefEqU source.uvars [] auxiliaryFamily.type
        (VExpr.wrapForalls sourceParams
          (VExpr.instantiateForallPrefix
            (containerFamily.type.instL levels) baseArgs)) →
      List.Forall₂
        (VInductDecl.DirectAuxConstructor sourceTypesEnv source.uvars sourceParams
          baseArgs levels containerFamily auxiliaryFamily)
        containerFamily.ctors auxiliaryFamily.ctors →
      auxiliaryLevels.length = source.uvars →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker
          (baseArgs.map (fun arg => arg.liftN depth 0)))
        (VExpr.mkApps VInductDecl.nestedTrailingMarker inputBaseArgs) →
      VInductDecl.NestedExprWFExpansion env source generated
        (source.nparams + depth)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker sourceTrailing)
        (VExpr.mkApps VInductDecl.nestedTrailingMarker targetTrailing) →
      input = VExpr.mkApps (.const containerFamily.name levels)
        (inputBaseArgs ++ sourceTrailing) →
      output = VExpr.mkApps (.const auxiliaryFamily.name auxiliaryLevels)
        (source.paramVars depth ++ targetTrailing) →
      VInductDecl.NestedAuxiliarySource env source generated depth input output

/-- Specialized structural expansion used inside the mutual formation
derivation. It has a forgetful map to `VExpr.NestedExprExpansion`; spelling it
out here is required by Lean's strict-positivity checker for the mutual leaf. -/
inductive VInductDecl.NestedExprWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → VExpr → VExpr → Prop
  | hit {env source generated depth relativeDepth input output} :
      depth = source.nparams + relativeDepth →
      VInductDecl.NestedAuxiliarySource env source generated relativeDepth
        input output →
      VInductDecl.NestedExprWFExpansion env source generated depth input output
  | bvar {env source generated index depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.bvar index) (.bvar index)
  | sort {env source generated level depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.sort level) (.sort level)
  | const {env source generated name levels depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.const name levels) (.const name levels)
  | elim {env source generated block owner levels depth} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.elim block owner levels) (.elim block owner levels)
  | proj {env source generated typeName index depth sourceMajor targetMajor} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceMajor targetMajor →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.proj typeName index sourceMajor)
        (.proj typeName index targetMajor)
  | app {env source generated depth sourceFn targetFn sourceArg targetArg} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceFn targetFn →
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceArg targetArg →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.app sourceFn sourceArg) (.app targetFn targetArg)
  | lam {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.lam sourceDomain sourceBody) (.lam targetDomain targetBody)
  | forallE {env source generated depth sourceDomain targetDomain sourceBody
      targetBody} :
      VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain →
      VInductDecl.NestedExprWFExpansion env source generated (depth + 1)
        sourceBody targetBody →
      VInductDecl.NestedExprWFExpansion env source generated depth
        (.forallE sourceDomain sourceBody) (.forallE targetDomain targetBody)

/-- Strictly-positive counterpart of `NestedForallPrefixExpansion` for the
mutually defined nested-formation leaf. -/
inductive VInductDecl.NestedForallPrefixWFExpansion :
    VEnv → VInductDecl → List VInductiveType →
      Nat → Nat → VExpr → VExpr → Prop
  | nil
      (Hbody : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth 0
        sourceBody targetBody
  | cons
      (Hdomain : VInductDecl.NestedExprWFExpansion env source generated depth
        sourceDomain targetDomain)
      (Hbody : VInductDecl.NestedForallPrefixWFExpansion env source generated
        (depth + 1) arity sourceBody targetBody) :
      VInductDecl.NestedForallPrefixWFExpansion env source generated depth
        (arity + 1) (.forallE sourceDomain sourceBody)
          (.forallE targetDomain targetBody)

/-- Ordered constructor expansion without nesting the mutually defined leaf
inside an external `List.Forall₂`. -/
inductive VInductDecl.NestedConstructorWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VConstVal → List VConstVal → Prop
  | nil {env source generated} :
      VInductDecl.NestedConstructorWFExpansions env source generated [] []
  | cons {env source generated sourceCtor targetCtor sourceCtors targetCtors} :
      targetCtor.name = sourceCtor.name →
      targetCtor.uvars = sourceCtor.uvars →
      VInductDecl.NestedForallPrefixWFExpansion env source generated 0
        source.nparams sourceCtor.type targetCtor.type →
      VInductDecl.NestedExprWFExpansion env source generated 0 sourceCtor.type
        targetCtor.type →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceCtors targetCtors →
      VInductDecl.NestedConstructorWFExpansions env source generated
        (sourceCtor :: sourceCtors) (targetCtor :: targetCtors)

/-- Ordered family expansion for the initial mutual block followed by the
direct, unlowered auxiliary queue. -/
inductive VInductDecl.NestedTypeWFExpansions :
    VEnv → VInductDecl → List VInductiveType →
      List VInductiveType → List VInductiveType → Prop
  | nil {env source generated} :
      VInductDecl.NestedTypeWFExpansions env source generated [] []
  | cons {env source generated sourceType targetType sourceTypes targetTypes} :
      targetType.name = sourceType.name →
      targetType.uvars = sourceType.uvars →
      env.IsDefEqU source.uvars [] sourceType.type targetType.type →
      targetType.numIndices = sourceType.numIndices →
      targetType.resultLevel = sourceType.resultLevel →
      VInductDecl.NestedConstructorWFExpansions env source generated
        sourceType.ctors targetType.ctors →
      VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
        targetTypes →
      VInductDecl.NestedTypeWFExpansions env source generated
        (sourceType :: sourceTypes) (targetType :: targetTypes)

/-- A nested declaration is formed by expanding the original families and a
finite queue of direct auxiliary sources into a declaration satisfying the
ordinary source and formation judgments. -/
inductive VInductDecl.NestedFormationWF : VEnv → VInductDecl → Prop
  | intro {env source expanded generated} :
      VInductDecl.SourceWF env expanded →
      VInductDecl.FormationWF env expanded →
      VInductDecl.SourceParameterWF env source →
      expanded.uvars = source.uvars →
      expanded.nparams = source.nparams →
      expanded.isUnsafe = source.isUnsafe →
      VInductDecl.NestedTypeWFExpansions env source generated
        (source.types ++ generated) expanded.types →
      VInductDecl.NestedFormationWF env source

end

/-- Constructor expressions count every enclosing forall binder, whereas
`NestedAuxiliarySource` counts only constructor-field binders below the common
parameter prefix.  This wrapper is the explicit boundary between those two
depth conventions. -/
def VInductDecl.NestedAuxiliarySourceAbsolute
    (env : VEnv) (source : VInductDecl)
    (generated : List VInductiveType) (depth : Nat)
    (input output : VExpr) : Prop :=
  ∃ relativeDepth,
    depth = source.nparams + relativeDepth ∧
    VInductDecl.NestedAuxiliarySource env source generated relativeDepth
      input output


theorem VExpr.getAppFnArgs_mkApps_const (name : Name) (levels : List VLevel)
    (args : List VExpr) :
    (VExpr.mkApps (.const name levels) args).getAppFnArgs =
      (.const name levels, args) := by
  suffices h : ∀ (fn : VExpr) (pre : List VExpr),
      fn.getAppFnArgs = (.const name levels, pre) →
      (VExpr.mkApps fn args).getAppFnArgs = (.const name levels, pre ++ args) by
    simpa using h (.const name levels) [] (by simp)
  induction args with
  | nil =>
    intro fn pre h
    simpa [VExpr.mkApps] using h
  | cons arg args ih =>
    intro fn pre h
    have := ih (.app fn arg) (pre ++ [arg]) (by simp [VExpr.getAppFnArgs_app, h])
    simpa [VExpr.mkApps, List.append_assoc] using this

/-- Every generated-family leaf replaces a source expression by an
application headed by one of the generated auxiliary families. -/
theorem VInductDecl.NestedAuxiliarySourceAbsolute.headConst
    {env : VEnv} {source : VInductDecl} {generated : List VInductiveType}
    {depth : Nat} {input output : VExpr}
    (H : VInductDecl.NestedAuxiliarySourceAbsolute env source generated depth
      input output) :
    ∃ auxiliary ∈ generated, ∃ levels args,
      output.getAppFnArgs = (.const auxiliary.name levels, args) := by
  rcases H with ⟨relativeDepth, _hdepth, H⟩
  cases H with
  | intro _ _ _ hgen _ _ _ _ _ _ _ _ _ _ _ _ houtput =>
    exact ⟨_, hgen, _, _, by rw [houtput]; exact VExpr.getAppFnArgs_mkApps_const _ _ _⟩

theorem List.Forall₂.map_eq_of {α β γ : Type _} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (H : List.Forall₂ R l₁ l₂)
    (f : α → γ) (g : β → γ) (hf : ∀ a b, R a b → f a = g b) :
    l₁.map f = l₂.map g := by
  induction H with
  | nil => rfl
  | cons h _ ih => simp [hf _ _ h, ih]

/-- Raw constructor shapes of the original families follow from the raw
shapes of the expanded declaration through the ordered nested expansion. -/
theorem VInductDecl.rawShapesOfNestedExpansions
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      (source.types ++ generated) expanded.types)
    (Hraw : ∀ type ∈ expanded.types, ∀ ctor ∈ type.ctors,
      expanded.RawCtorShape type ctor)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnodup : (expanded.types.map (·.name)).Nodup) :
    ∀ type ∈ source.types, ∀ ctor ∈ type.ctors, source.RawCtorShape type ctor := by
  have hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name) :=
    (Lean4Lean.List.Forall₂.map_eq_of Htypes (·.name) (·.name)
      (fun _ _ h => h.name.symm)).symm
  intro type htype ctor hctor
  rcases Lean4Lean.List.Forall₂.forall_exists_l Htypes type
      (List.mem_append_left _ htype) with ⟨target, htarget, Hexp⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_l Hexp.constructors ctor hctor with
    ⟨targetCtor, htargetCtor, Hctor⟩
  exact VInductDecl.RawCtorShape.ofNestedExpansion
    (fun h => VInductDecl.NestedAuxiliarySourceAbsolute.headConst h)
    huvars hnparams hnames hnodup htype htarget Hexp.name Hexp.numIndices
    Hctor.type (Hraw target htarget targetCtor htargetCtor)

/-- Constructor telescope lengths agree positionally across the ordered
nested expansion of the original families. -/
theorem VInductDecl.constructorArityPrefixOfNestedExpansions
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      (source.types ++ generated) expanded.types)
    (Hraw : ∀ type ∈ expanded.types, ∀ ctor ∈ type.ctors,
      expanded.RawCtorShape type ctor)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hnodup : (expanded.types.map (·.name)).Nodup) :
    source.ConstructorArityPrefix expanded := by
  have hnames : expanded.types.map (·.name) =
      (source.types ++ generated).map (·.name) :=
    (Lean4Lean.List.Forall₂.map_eq_of Htypes (·.name) (·.name)
      (fun _ _ h => h.name.symm)).symm
  intro familyIdx hsource hexpanded ctorIdx hsourceCtor hexpandedCtor
  have hprefix : familyIdx < (source.types ++ generated).length := by
    simp only [List.length_append]
    omega
  have Hexp := Lean4Lean.List.Forall₂.getElem_of Htypes familyIdx hprefix hexpanded
  have hget : (source.types ++ generated)[familyIdx] = source.types[familyIdx] :=
    List.getElem_append_left hsource
  rw [hget] at Hexp
  have Hctor := Lean4Lean.List.Forall₂.getElem_of Hexp.constructors ctorIdx
    hsourceCtor hexpandedCtor
  exact (VInductDecl.RawCtorShape.ofNestedExpansion_core
    (fun h => VInductDecl.NestedAuxiliarySourceAbsolute.headConst h)
    huvars hnparams hnames hnodup (List.getElem_mem hsource)
    (List.getElem_mem hexpanded) Hexp.name Hexp.numIndices Hctor.type
    (Hraw _ (List.getElem_mem hexpanded) _ (List.getElem_mem hexpandedCtor))).2

/-- Abstract well-formedness always retains the original source judgment;
formation is a finite ordinary-or-nested derivation. -/
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧ decl.FormationEvidence env

theorem VInductDecl.WF.originalConstructors
    {env : VEnv} {decl : VInductDecl}
    (H : decl.WF env) :
    ∃ envTypes,
      env.addConstVals decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes :=
  H.1.originalConstructors

/-- Source constructor typing at the exact header environment named by an
installation. -/
theorem VInductDecl.SourceWF.constructorsWF_at
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes := by
  rcases H.originalConstructors with ⟨envTypes', htypes', hwf⟩
  cases Option.some.inj (htypes'.symm.trans htypes)
  exact hwf

/-- Both ordinary and nested formation evidence retain the source
parameter judgment at any environment in which the headers install. -/
theorem VInductDecl.FormationEvidence.sourceParameterWF
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.FormationEvidence env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    decl.SourceParameterWF env := by
  cases H with
  | ordinary H => exact H.sourceParameterWF
  | nested H hle =>
    cases H with
    | intro _ _ Hparams _ _ _ _ =>
      exact Hparams.mono_of_addConstVals hle htypes

theorem VInductDecl.WF.sourceParameterWF
    {env envTypes : VEnv} {decl : VInductDecl}
    (H : decl.WF env)
    (htypes : env.addConstVals decl.typeConstants = some envTypes) :
    decl.SourceParameterWF env :=
  H.2.sourceParameterWF htypes

/-- Forget the mutual positivity encoding and recover the reusable generic
expression carrier. -/
theorem VInductDecl.NestedExprWFExpansion.toNestedExprExpansion
    {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {depth : Nat} {input output : VExpr}
    (H : VInductDecl.NestedExprWFExpansion env source generated depth input
      output) :
    VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      depth input output := by
  exact VInductDecl.NestedExprWFExpansion.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun env source generated depth input output _ =>
      VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth input output)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun hdepth Hleaf _ => .hit ⟨_, hdepth, Hleaf⟩)
    (by exact .bvar)
    (by exact .sort)
    (by exact .const)
    (by exact .elim)
    (fun _ ihMajor => .proj ihMajor)
    (fun _ _ ihFn ihArg => .app ihFn ihArg)
    (fun _ _ ihDomain ihBody => .lam ihDomain ihBody)
    (fun _ _ ihDomain ihBody => .forallE ihDomain ihBody)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    H

/-- Forget the specialized constructor-list encoding. -/
theorem VInductDecl.NestedConstructorWFExpansions.toForall₂
    {env : VEnv} {source : VInductDecl}
    {generated : List VInductiveType} {sourceCtors targetCtors : List VConstVal}
    (H : VInductDecl.NestedConstructorWFExpansions env source generated
      sourceCtors targetCtors) :
    List.Forall₂
      (VInductDecl.NestedConstructorExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        source.nparams)
      sourceCtors targetCtors := by
  exact VInductDecl.NestedConstructorWFExpansions.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun env source generated depth input output _ =>
      VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth input output)
    (motive_5 := fun env source generated depth arity input output _ =>
      VExpr.NestedForallPrefixExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth arity input output)
    (motive_6 := fun env source generated sourceCtors targetCtors _ =>
      List.Forall₂
        (VInductDecl.NestedConstructorExpansion
          (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
          source.nparams)
        sourceCtors targetCtors)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun hdepth Hleaf _ => .hit ⟨_, hdepth, Hleaf⟩)
    (by exact .bvar)
    (by exact .sort)
    (by exact .const)
    (by exact .elim)
    (fun _ ihMajor => .proj ihMajor)
    (fun _ _ ihFn ihArg => .app ihFn ihArg)
    (fun _ _ ihDomain ihBody => .lam ihDomain ihBody)
    (fun _ _ ihDomain ihBody => .forallE ihDomain ihBody)
    (fun _ ihBody => .nil ihBody)
    (fun _ _ ihDomain ihBody => .cons ihDomain ihBody)
    (by exact .nil)
    (fun hname huvars _ _ _ ihParams ihType ihTail =>
      .cons ⟨hname, huvars, ihParams, ihType⟩ ihTail)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    H

/-- Forget the specialized family-list encoding. -/
theorem VInductDecl.NestedTypeWFExpansions.toForall₂
    {env : VEnv} {source : VInductDecl}
    {generated sourceTypes targetTypes : List VInductiveType}
    (H : VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
      targetTypes) :
    List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      sourceTypes targetTypes := by
  exact VInductDecl.NestedTypeWFExpansions.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun env source generated depth input output _ =>
      VExpr.NestedExprExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth input output)
    (motive_5 := fun env source generated depth arity input output _ =>
      VExpr.NestedForallPrefixExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        depth arity input output)
    (motive_6 := fun env source generated sourceCtors targetCtors _ =>
      List.Forall₂
        (VInductDecl.NestedConstructorExpansion
          (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
          source.nparams)
        sourceCtors targetCtors)
    (motive_7 := fun env source generated sourceTypes targetTypes _ =>
      List.Forall₂
        (VInductDecl.NestedTypeExpansion env source
          (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
        sourceTypes targetTypes)
    (motive_8 := fun _ _ _ => True)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (fun hdepth Hleaf _ => .hit ⟨_, hdepth, Hleaf⟩)
    (by exact .bvar)
    (by exact .sort)
    (by exact .const)
    (by exact .elim)
    (fun _ ihMajor => .proj ihMajor)
    (fun _ _ ihFn ihArg => .app ihFn ihArg)
    (fun _ _ ihDomain ihBody => .lam ihDomain ihBody)
    (fun _ _ ihDomain ihBody => .forallE ihDomain ihBody)
    (fun _ ihBody => .nil ihBody)
    (fun _ _ ihDomain ihBody => .cons ihDomain ihBody)
    (by exact .nil)
    (fun hname huvars _ _ _ ihParams ihType ihTail =>
      .cons ⟨hname, huvars, ihParams, ihType⟩ ihTail)
    (by exact .nil)
    (fun hname huvars htype hindices hlevel _ _ ihCtors ihTail =>
      .cons ⟨hname, huvars, htype, hindices, hlevel, ihCtors⟩ ihTail)
    (by intros; trivial)
    H

theorem VEnv.InstalledInductCertificate.mono
    {env env' : VEnv} {decl : VInductDecl}
    (henv : env ≤ env')
    (H : VEnv.InstalledInductCertificate env decl) :
    VEnv.InstalledInductCertificate env' decl := by
  cases H with
  | intro hsource hformation hcompile hblock hinstall hle =>
    exact .intro hsource hformation hcompile hblock hinstall (hle.trans henv)

/-- Every projection entry derived from an installed declaration is present
in the ambient projection registry.  This is the registry fact carried by an
installation certificate; clients do not need to reconstruct the internal
type/constructor/recursor staging of `VInductBlock.install`. -/
theorem VEnv.InstalledInductCertificate.projection
    {env : VEnv} {decl : VInductDecl} {entry : VProjectionEntry}
    (H : VEnv.InstalledInductCertificate env decl)
    (hentry : entry ∈ decl.projectionEntries) :
    env.projections entry.typeName entry.info := by
  cases H with
  | intro hsource hformation hcompile hblock hinstall hle =>
    unfold VInductBlock.install at hinstall
    simp at hinstall
    rcases hinstall with
      ⟨envTypes, htypes, envCtors, hctors, envRecursors, hrecursors, rfl⟩
    apply hle.projections
    simp only [VEnv.addDefEqRules_projections]
    rw [VEnv.addConstVals_projections hrecursors]
    rw [VEnv.addProjections_iff]
    exact Or.inl ⟨entry, hcompile.projections.symm ▸ hentry, rfl, rfl⟩

/-- An installed declaration exposes each of its family constants at the
exact abstract value recorded by the source declaration. -/
theorem VEnv.InstalledInductCertificate.familyConstant
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledInductCertificate env decl)
    (familyIdx : Nat) (hfamily : familyIdx < decl.types.length) :
    env.constants decl.types[familyIdx].name =
      some decl.types[familyIdx].toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : decl.types[familyIdx].toVConstVal ∈ block.types := by
      rw [Hcompile.types]
      exact List.mem_map.mpr
        ⟨decl.types[familyIdx], List.getElem_mem hfamily, rfl⟩
    have hlookup := VEnv.addConstVals_get htypes hmember
    have hcanonical : VInductBlock.install base block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecursors]
    have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (Hinstall.symm.trans hcanonical)
    subst installed
    apply hle.constants
    simpa only [VEnv.addDefEqRules_constants] using
      (VEnv.addConstVals_le hrecursors).constants
        (VEnv.addEliminators_addProjections_le.constants
          ((VEnv.addConstVals_le hctors).constants hlookup))

/-- Every family of an installed declaration carries the declaration's
universe arity. -/
theorem VEnv.InstalledInductCertificate.typeUvars
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledInductCertificate env decl) :
    ∀ type ∈ decl.types, type.uvars = decl.uvars := by
  cases H with
  | intro Hsource _ _ _ _ _ => exact Hsource.2.2.1

/-- Every constructor of an installed declaration carries the declaration's
universe arity. -/
theorem VEnv.InstalledInductCertificate.constructorUvars
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledInductCertificate env decl) :
    ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars := by
  cases H with
  | intro Hsource _ _ _ _ _ => exact Hsource.2.2.2.1

/-- An installed declaration exposes each of its constructor constants at
the exact abstract value recorded by the source declaration. -/
theorem VEnv.InstalledInductCertificate.constructorConstant
    {env : VEnv} {decl : VInductDecl}
    (H : VEnv.InstalledInductCertificate env decl)
    (familyIdx ctorIdx : Nat) (hfamily : familyIdx < decl.types.length)
    (hctor : ctorIdx < decl.types[familyIdx].ctors.length) :
    env.constants decl.types[familyIdx].ctors[ctorIdx].name =
      some decl.types[familyIdx].ctors[ctorIdx].toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : decl.types[familyIdx].ctors[ctorIdx] ∈ block.ctors := by
      rw [Hcompile.ctors]
      simp only [VInductDecl.constructorConstants, List.mem_flatMap]
      exact ⟨decl.types[familyIdx], List.getElem_mem hfamily,
        List.getElem_mem hctor⟩
    have hlookup := VEnv.addConstVals_get hctors hmember
    have hcanonical : VInductBlock.install base block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecursors]
    have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (Hinstall.symm.trans hcanonical)
    subst installed
    apply hle.constants
    simpa only [VEnv.addDefEqRules_constants] using
      (VEnv.addConstVals_le hrecursors).constants
        (VEnv.addEliminators_addProjections_le.constants hlookup)


/-- The block registers exactly one case eliminator, under the key of its first family, with a
schema certified by the declaration's case-only compilation certificate, projecting only out of
structures registered at the constructor stage. It is installed after the constructors and
before the projections (`VInductBlock.install`). -/
def VInductBlock.EliminatorsWF (env : VEnv) (decl : VInductDecl) (block : VInductBlock) : Prop :=
  ∃ envTypes envCtors, env.addConstVals block.types = some envTypes ∧
    envTypes.addConstVals block.ctors = some envCtors ∧
    ∃ key schema, block.eliminators = [(key, schema)] ∧
      schema.Certified env decl block ∧ decl.types.head?.map (·.name) = some key ∧
      schema.ProjNamesRegistered envCtors key

/-- Relational abstract environment extension for inductive declarations,
including the compiled block witness used by implementation refinement. -/
inductive VEnv.AddInduct (env : VEnv) (decl : VInductDecl) : VEnv → Prop where
  | intro :
    decl.WF env →
    VInductDecl.CompilesTo env decl block →
    VInductBlock.WF env block →
    VInductBlock.EliminatorsWF env decl block →
    VInductBlock.install env block = some env' →
    VEnv.AddInduct env decl env'
