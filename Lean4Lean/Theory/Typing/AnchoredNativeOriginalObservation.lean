import Lean4Lean.Theory.Typing.AnchoredNativeOriginalOrigins

/-! Initial source observations generated from an actual original equation.
The native parser, capture-origin chain and terminal ledger are conclusions. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData
open AnchoredSource (Footprint Valuation)
open AnchoredSource.Adapted AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Parse the instantiated original equation directly. All arity, projection
selection and capture-machine success checks follow from its compilation. -/
theorem initialProgram
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    (origin : NativeDeclarationOrigin env declarations data)
    (eliminator : env.eliminators data.block data.schema)
    (families : data.schema.signature.families.size = 1)
    (constructors : data.schema.signature.constructors.size ≤ 1)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars) (σ : Subst) :
    ∃ program : SaturatedProgram data,
      data.saturatedProgram levels ((body.lhs.instL levels).getAppFnArgs.2.map (·.subst σ)) = some program ∧
      program.equation = rule ∧ program.equationBody = body ∧ program.levels = levels ∧
      program.prefixArgs = ((body.lhs.instL levels).getAppFnArgs.2.map (·.subst σ)) ∧
      program.trailing = [] ∧
      (body.lhs.instL levels).getAppFnArgs.1 = .const data.name levels := by
  have registered := origin.registered
  have compilation := origin.selectedCompilation
  have admissible := origin.sourceAdmissible families
  have levelArity : (data.sourceLevels levels).length = data.schema.signature.uvars := by
    simpa only [sourceLevels, List.length_map, nativeInstance] using admissible.levels_length
  have identity := origin.restoration.trans (compilation.restoration_of_singleton families)
  obtain ⟨projection, projectionSelected⟩ := compilation.model.projectionData_exists_at
    (show origin.stage.base.WF from ⟨_, origin.stage.earlierHistory⟩).ordered
    compilation.expandedWF origin.compilationBelow (by
      rw [← compilation.typeConstants_of_singleton families, ← compilation.types]
      exact origin.stage.typing.addTypes) identity constructors index owner levelArity
  obtain ⟨actualBody, actualExtract, _, head, arity⟩ :=
    InductiveSignature.VEnv.NativeRecursorRegistered.initialEquationBody
      registered families owner equation
  have bodyEq : actualBody = body := Option.some.inj (actualExtract.symm.trans extracted)
  subst actualBody
  have sourceLengths := CaseSchema.projectionData_singleton_lengths constructors index projectionSelected
  have argumentLength : ((body.lhs.instL levels).getAppFnArgs.2.map (·.subst σ)).length =
      data.majorOffset + 1 := by
    simp only [List.length_map, getAppFnArgs_instL, List.length_map]
    rw [arity, sourceLengths.2.2.2.2]
    rfl
  obtain ⟨program, selected, equationEq, prefixEq, noTrailing⟩ :=
    InductiveSignature.VEnv.NativeRecursorRegistered.initialProgram registered families constructors
      owner equation levelLength projectionSelected _ argumentLength
  have spec := saturatedProgram_spec selected
  have bodyEq : program.equationBody = body := by
    have parsed := spec.2.2.2.2.2.2.2.2.2.1
    rw [equationEq, extracted] at parsed
    exact (Option.some.inj parsed).symm
  refine ⟨program, selected, equationEq, bodyEq, spec.1, prefixEq, noTrailing, ?_⟩
  simp only [getAppFnArgs_instL, head, VExpr.instL]
  rw [VLevel.inst_map_id levelLength]

/-- At an arbitrary realization of the original equation telescope, a RHS
observer and its actual assigned-type certificate produce the LHS observer.
No program, terminal, ledger, or instruction-wise origin producer is assumed. -/
theorem initialObservation
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ (body.domains.map (·.instL levels)).reverse)
    (fits : PairedFits env U registry (body.domains.map (·.instL levels)).reverse
      target locals σ σ available)
    {assigned : VExpr} {structural : Bool}
    (original : origin.stage.typing.recursors.HasTypeStrong U
      (body.domains.map (·.instL levels)).reverse (body.lhs.instL levels) assigned structural)
    {atom : Atom n} {bodyFootprint : Footprint}
    (observed : Obs env U registry target locals σ (body.rhs.instL levels)
      (.singleton atom) bodyFootprint)
    (resources : bodyFootprint.Available available)
    {support : Profile n} {typeFootprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support typeFootprint)
    (typeResources : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ
      (body.lhs.instL levels) (.singleton atom) footprint) ∧
      footprint.Available available := by
  obtain ⟨program, selected, _, bodyEq, levelsEq, prefixEq, noTrailing, head⟩ :=
    origin.initialProgram eliminator singleton.1 singleton.2.1 owner equation extracted levelLength σ
  subst body
  subst levels
  have selfSelected : data.saturatedProgram program.levels
      (program.prefixArgs ++ program.trailing) = some program := by
    simpa only [prefixEq, noTrailing, List.append_nil] using selected
  obtain ⟨origins⟩ := origin.captureOrigins_of_singleton henv eliminator singleton levelsWF
    (signature := signature) owner equation selfSelected
  obtain ⟨headerLevel, originalHeader⟩ := origin.typeStrong signature.typeOrigin
  have formation := originalHeader.instL levelsWF
  have typeClosed : signature.type.Closed :=
    VExpr.WF.closedN origin.stage.typing.recursorsWF.ordered ⟨_, originalHeader.defeq⟩ trivial
  exact origins.initialObservation henv hscoped
    (origin.stage.typing.recursors_le.trans origin.stage.installedBelow) earlier closed hTarget
    substitutions fits lookup notDefinition origin.registered levelsWF typeClosed
    (by simpa only [List.map_nil, VExpr.instL] using formation)
    selected noTrailing original head observed resources certificate typeResources typed

end Lean4Lean.VEnv.NativeDeclarationOrigin
