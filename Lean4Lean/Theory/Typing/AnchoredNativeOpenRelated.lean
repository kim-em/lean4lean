import Lean4Lean.Theory.Typing.AnchoredNativeOriginalObservation
import Lean4Lean.Theory.Typing.AnchoredNativeSeededRegistered
import Lean4Lean.Theory.Typing.AnchoredNativeTerminalInterpretation

/-! The actual original equation yields its open semantic comparison at the
caller's assigned type and exact support. Seeded original argument observations
supply the registered valuation needed by the finite capture replay. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData
open AnchoredSource (Footprint Valuation)
open AnchoredSource.Adapted AnchoredProfiles AnchoredSemantics
open private rebuild_spine from Lean4Lean.Theory.Inductive.CaseReductionData
set_option backward.isDefEq.respectTransparency false

/-- The finite initial capture ledger is interpreted through the original
application spine before native terminal replay. Its registered-result code
retains the conversion back to the original natural assigned result. -/
theorem openRelated_atType
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
    Related env U registry target
      ((body.rhs.instL levels).subst σ) ((body.lhs.instL levels).subst σ)
      (assigned.subst σ) (.singleton atom) support := by
  obtain ⟨program, selected, _, bodyEq, levelsEq, prefixEq, noTrailing, head⟩ :=
    origin.initialProgram eliminator singleton.1 singleton.2.1 owner equation extracted levelLength σ
  subst body
  subst levels
  have selfSelected : data.saturatedProgram program.levels
      (program.prefixArgs ++ program.trailing) = some program := by
    simpa only [prefixEq, noTrailing, List.append_nil] using selected
  have registered := origin.registered
  have hsource := origin.stage.typing.recursorsWF.ordered
  have hle := origin.stage.typing.recursors_le.trans origin.stage.installedBelow
  obtain ⟨origins⟩ := origin.captureOrigins_of_singleton henv eliminator singleton levelsWF
    (signature := signature) owner equation selfSelected
  obtain ⟨headerLevel, originalHeader⟩ := origin.typeStrong signature.typeOrigin
  have formation : origin.stage.typing.recursors.IsDefEqStrong U []
      (signature.type.instL program.levels) (signature.type.instL program.levels)
      (.sort (headerLevel.inst program.levels)) := by
    simpa only [List.map_nil, VExpr.instL] using originalHeader.instL levelsWF
  have typeClosed : signature.type.Closed :=
    VExpr.WF.closedN hsource ⟨_, originalHeader.defeq⟩ trivial
  have payload := earlier formation
  obtain ⟨required, leaf, programEq, witnessesEq, ⟨ledger⟩⟩ :=
    origins.initialTerminal_witnessed henv hscoped hle earlier closed hTarget substitutions fits
      registered typeClosed ⟨formation, payload.joint⟩ payload.leftFormation
      selected noTrailing original head observed resources n
  have argumentLength : (program.equationBody.lhs.instL program.levels).getAppFnArgs.2.length =
      signature.domains.length := by
    have length := leaf.saturated
    simpa only [List.length_map, takeForalls_length signature.telescope] using length
  obtain ⟨state⟩ := HasTypeStrong.seededRegistered henv hscoped hle earlier closed hTarget
    substitutions fits registered typeClosed ⟨formation, payload.joint⟩ payload.leftFormation
    original head ledger certificate typeResources (Nat.le_of_eq argumentLength)
  have rawArguments : Ctx.SubstEq env U target
      (nativeCaptureSubst program.prefixArgs) (nativeCaptureSubst program.prefixArgs)
      signature.domains.reverse := by
    simpa only [prefixEq, argumentLength, List.take_length] using state.substitutions
  have argumentFits : PairedFits env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst program.prefixArgs) state.valuation := by
    simpa only [prefixEq, List.length_map, argumentLength, List.take_length] using state.fits
  have spec := saturatedProgram_spec selfSelected
  have equationOriginal := origin.singletonStrong spec.2.2.2.2.2.2.2.2.1
  have left := equationOriginal.1.instL levelsWF
  have right := equationOriginal.2.instL levelsWF
  obtain ⟨resultLevel, resultFormation⟩ := right.isType' hsource hsource.strong (by trivial)
  have captures := leaf.captures.toCaptures
  have leafBody := leaf.body
  have leafLength := leaf.witnessLength
  have leafPrefix := leaf.witnessPrefix
  have literal := leaf.arguments_eq
  rw [programEq] at captures leafBody leafLength
  have witnessPrefix : leaf.witnesses.take data.indexOffset =
      program.prefixArgs.take data.indexOffset := by
    simpa only [prefixEq] using leafPrefix
  have literal : program.prefixArgs = nativeEquationArguments program leaf.witnesses := by
    simpa only [programEq, prefixEq] using literal
  obtain ⟨result⟩ := captures.terminalRelated henv hscoped hsource hle
    (fun H => (earlier H).joint) hTarget signature registered lookup notDefinition selfSelected
    levelsWF leafLength witnessPrefix literal rfl rawArguments argumentFits state.closed
    left.hasType'.1 right.hasType'.1 resultFormation leafBody state.seedAvailable
  have bridge : TypeRelated env U registry target
      (signature.result.subst (nativeCaptureSubst program.prefixArgs)) (assigned.subst σ) support := by
    simpa only [argumentLength, List.drop_length, wrapForalls, List.foldr_nil, prefixEq] using state.related
  have related := Related.convert henv typed bridge result.related
  have rhsClosed : program.equation.rhs.Closed :=
    VExpr.WF.closedN hsource ⟨_, equationOriginal.2.defeq⟩ trivial
  have rhsScope := (scope_of_extract spec.2.2.2.2.2.2.2.2.2.1 rhsClosed).2.instL
    (ls := program.levels)
  have rhsEq : (program.equationBody.rhs.instL program.levels).subst
      (nativeCaptureSubst leaf.witnesses) =
      (program.equationBody.rhs.instL program.levels).subst σ := by
    rw [witnessesEq]
    exact subst_congr_closedN rhsScope (nativeCaptureSubst_variables _ σ)
  have lhsEq : mkApps (.const data.name program.levels) program.prefixArgs =
      (program.equationBody.lhs.instL program.levels).subst σ := by
    rw [prefixEq, ← subst_const, ← subst_mkApps, ← head]
    rw [rebuild_spine]
  simpa only [rhsEq, lhsEq] using related

end Lean4Lean.VEnv.NativeDeclarationOrigin
