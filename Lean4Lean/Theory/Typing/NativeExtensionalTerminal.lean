import Lean4Lean.Theory.Typing.CanonicalDataEtaProgram
import Lean4Lean.Theory.Typing.NativeTerminalSoundness

/-! Typed extensional replay of an actual registered equation. The replay
uses the original equation header, a concrete typed capture tuple, and the
primitive projections of the actual major. It does not erase relevant fields
or posit that a neutral major has a constructor-headed trace. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredSemantics InductiveSignature NativeRecursorData
open private eta_spine capture_vars open_equality trace_equality
  from Lean4Lean.Theory.Typing.NativeTerminalSoundness
set_option backward.isDefEq.respectTransparency false

/-- Apply the installed closed equation to a concrete original-telescope
substitution. The emitted RHS retains its closed lambda header, exactly as
the ordinary-data machine does. -/
theorem native_applyEquation_original
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {equation : VDefEq} {body : CaseSchema.EquationBody}
    (registered : env.defeqs equation)
    (extracted : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = equation.uvars)
    (left : sourceEnv.HasTypeStrong U [] (equation.lhs.instL levels)
      (equation.type.instL levels) leftStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (equation.type.instL levels)
      (equation.type.instL levels) (.sort level))
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {captures : List VExpr} (captureCount : captures.length = body.domains.length)
    (substitution : Ctx.SubstEq env U target (nativeCaptureSubst captures)
      (nativeCaptureSubst captures) (body.domains.map (·.instL levels)).reverse) :
    env.IsDefEq U target
      ((body.lhs.instL levels).subst (nativeCaptureSubst captures))
      (mkApps (equation.rhs.instL levels) captures)
      ((body.type.instL levels).subst (nativeCaptureSubst captures)) := by
  have parts := CaseSchema.EquationBody.extract_sound extracted
  have raw : env.IsDefEq U [] (equation.lhs.instL levels) (equation.rhs.instL levels)
      (equation.type.instL levels) := .extra registered levelsWF levelCount
  have rhsClosed := raw.hasType.2.closedN henv (by trivial)
  have parsedLeft := left
  have parsedFormation := formation
  rw [← parts.1, ← parts.2.2, instL_wrapLams, instL_wrapForalls] at parsedLeft
  rw [← parts.2.2, instL_wrapForalls] at parsedFormation
  have context := (HasType.native_open henv (by trivial) (parsedLeft.refl.defeq.mono hle)).1
  obtain ⟨_, _, _, _, leftBody⟩ := HasTypeStrong.openDeclaredBody henv hscoped hle earlier
    parsedLeft parsedFormation context
  have beta := TypedBetaTrace.nativeRhs (Γ := []) henv
    (body.domains.map (·.instL levels)) context leftBody
  rw [← parts.2.2, instL_wrapForalls] at raw
  have applied := open_equality henv (body.domains.map (·.instL levels)) raw
  rw [← parts.1, instL_wrapLams] at applied
  have opened := (trace_equality beta).symm.trans applied
  simp only [List.append_nil] at opened
  have instantiated := opened.subst henv substitution hTarget
  rw [eta_spine, subst_mkApps, rhsClosed.liftN_eq (Nat.zero_le _),
    rhsClosed.subst_eq Subst.Fixes.zero] at instantiated
  simpa only [List.length_map, ← captureCount, capture_vars] using instantiated

/-- Structure eta transports the actual major application to the original
equation's exact closed RHS application. The dependent result remains at the
declared type instantiated with the expansion; callers retain its concrete
conversion to their assigned result type. -/
theorem native_structureEta_application
    {env : VEnv} {U : Nat} {target : List VExpr}
    {typeName : Name} {info : VProjectionInfo} {levels : List VLevel}
    {params : List VExpr} {major function result body : VExpr}
    (registered : env.projections typeName info)
    (paramCount : params.length = info.nparams) (noIndices : info.nindices = 0)
    (majorTyped : env.HasType U target major (mkApps (.const typeName levels) params))
    (expandedTyped : env.HasType U target
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj typeName index major)))
      (mkApps (.const typeName levels) params))
    (functionTyped : env.HasType U target function
      (.forallE (mkApps (.const typeName levels) params) body))
    (equation : env.IsDefEq U target
      (.app function (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj typeName index major))))
      result (body.inst (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj typeName index major))))) :
    env.IsDefEq U target (.app function major) result
      (body.inst (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => .proj typeName index major)))) := by
  have eta := IsDefEq.structEta registered paramCount noIndices majorTyped expandedTyped
  exact (IsDefEq.appDF functionTyped eta).symm.trans equation

/-- A complete typed terminal for the extensional machine branch. Every
field in the emitted capture tuple is a projection of the actual major.
The two syntactic alignments retain the original generated equation's
literal major and result; no equality of independently inferred types is
used to construct them. -/
theorem native_structureEta_replay
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {data : NativeRecursorData} {index : Fin data.schema.signature.constructors.size}
    {equation : VDefEq} {parsed : CaseSchema.EquationBody}
    (registered : NativeRecursorRegistered env data)
    (equationSelected : data.equation index = some equation)
    (extracted : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some parsed)
    {chosen : CanonicalDataHead.Selected} {function major : VExpr}
    (selected : CanonicalDataHead.select registry function = some chosen)
    (atMajor : chosen.isMajor = true)
    (rules : chosen.rules = [CanonicalDataHead.Rule.native data index equation])
    (legacyAbsent : CanonicalHead.step registry (.app function major) = none)
    {entry : VProjectionEntry} {info : VProjectionInfo}
    (reverse : registry.structureConstructors (data.ruleConstructor index) = some entry)
    (projection : registry.projections entry.typeName = some info)
    (projectionRegistered : env.projections entry.typeName info)
    (constructor : info.ctorName = data.ruleConstructor index)
    (noIndices : info.nindices = 0)
    (arity : (ruleMajorArguments equation).length = info.nparams + info.numFields)
    (fields : data.schema.signature.constructors[index].fields.length = info.numFields)
    (levelsWF : ∀ level ∈ chosen.levels, level.WF U)
    (levelCount : chosen.levels.length = equation.uvars)
    (prefixCount : data.indexOffset ≤ chosen.arguments.length)
    (left : sourceEnv.HasTypeStrong U [] (equation.lhs.instL chosen.levels)
      (equation.type.instL chosen.levels) leftStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (equation.type.instL chosen.levels)
      (equation.type.instL chosen.levels) (.sort level))
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {params : List VExpr} {familyLevels : List VLevel} {resultBody : VExpr}
    (paramCount : params.length = info.nparams)
    (majorTyped : env.HasType U target major (mkApps (.const entry.typeName familyLevels) params))
    (expandedTyped : env.HasType U target
      (mkApps (.const info.ctorName familyLevels)
        (params ++ (List.range info.numFields).map (fun field => .proj entry.typeName field major)))
      (mkApps (.const entry.typeName familyLevels) params))
    (functionTyped : env.HasType U target function
      (.forallE (mkApps (.const entry.typeName familyLevels) params) resultBody))
    (captureCount : (chosen.arguments.take data.indexOffset ++
        (List.range info.numFields).map (fun field => VExpr.proj entry.typeName field major)).length =
      parsed.domains.length)
    (substitution : Ctx.SubstEq env U target
      (nativeCaptureSubst (chosen.arguments.take data.indexOffset ++
        (List.range info.numFields).map (fun field => .proj entry.typeName field major)))
      (nativeCaptureSubst (chosen.arguments.take data.indexOffset ++
        (List.range info.numFields).map (fun field => .proj entry.typeName field major)))
      (parsed.domains.map (·.instL chosen.levels)).reverse)
    (leftShape : (parsed.lhs.instL chosen.levels).subst
      (nativeCaptureSubst (chosen.arguments.take data.indexOffset ++
        (List.range info.numFields).map (fun field => .proj entry.typeName field major))) =
      .app function (mkApps (.const info.ctorName familyLevels)
        (params ++ (List.range info.numFields).map (fun field => .proj entry.typeName field major))))
    (typeShape : (parsed.type.instL chosen.levels).subst
      (nativeCaptureSubst (chosen.arguments.take data.indexOffset ++
        (List.range info.numFields).map (fun field => .proj entry.typeName field major))) =
      resultBody.inst (mkApps (.const info.ctorName familyLevels)
        (params ++ (List.range info.numFields).map (fun field => .proj entry.typeName field major)))) :
    let rhs := mkApps (equation.rhs.instL chosen.levels)
      (chosen.arguments.take data.indexOffset ++
        (List.range info.numFields).map (fun field => .proj entry.typeName field major))
    CanonicalDataHead.step registry (.app function major) = some ⟨[], rhs⟩ ∧
      env.IsDefEq U target (.app function major) rhs
        (resultBody.inst (mkApps (.const info.ctorName familyLevels)
          (params ++ (List.range info.numFields).map (fun field => .proj entry.typeName field major)))) := by
  dsimp only
  have dispatched : CanonicalDataHead.etaIota registry chosen major =
      some (mkApps (equation.rhs.instL chosen.levels)
        (chosen.arguments.take data.indexOffset ++
          (List.range info.numFields).map (fun field => .proj entry.typeName field major))) := by
    simp only [CanonicalDataHead.etaIota, rules, CanonicalDataHead.Rule.native,
      reverse, projection, bind, Option.bind_some, constructor, noIndices, arity,
      fields, levelCount, prefixCount, and_self, ↓reduceIte]
  refine ⟨?_, ?_⟩
  · simp only [CanonicalDataHead.step, legacyAbsent, selected, atMajor, ↓reduceIte, dispatched]
  · have applied := native_applyEquation_original henv hscoped hle earlier
      (registered.equation_present equationSelected) extracted levelsWF levelCount
      left formation hTarget captureCount substitution
    rw [leftShape, typeShape] at applied
    exact native_structureEta_application projectionRegistered paramCount noIndices
      majorTyped expandedTyped functionTyped applied

end Lean4Lean.AnchoredSource.Adapted
