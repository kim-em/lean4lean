import Lean4Lean.Theory.Typing.AnchoredNativeRegisteredCode
import Lean4Lean.Theory.Typing.AnchoredNativeArgumentDomainRequest
import Lean4Lean.Theory.Typing.AnchoredNativeDirectRouting

/-! Select a real converted application argument, walk its finite code
request through the registered header, and route the resulting source row.
The registered domain is recovered from original header formation; it is
never imposed as an assumed type of the original argument child. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

def NativeIndexTemplates.signature {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program) : NativeConstantSignature data program.levels :=
  ⟨templates.recursorType, templates.registeredType, templates.inputDomains,
    templates.result, templates.telescope⟩

/-- A finite registered-prefix row together with the actual original
application child and the original observers backing its local valuation. -/
structure NativeSelectedRegisteredRow
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (σ : Subst) (available : Valuation)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program) (expression : VExpr) (input : Profile n) where
  frame : OriginalApplicationFrame sourceEnv U source expression (data.indexOffset + templates.slot)
  valuation : Valuation
  row : PiRowCertificate env U registry target (List.range (data.indexOffset + templates.slot))
    (nativeCaptureSubst ((expression.getAppFnArgs.2.take (data.indexOffset + templates.slot)).map (·.subst σ)))
    valuation templates.naturalDomain
    (wrapForalls (templates.inputDomains.drop (data.indexOffset + templates.slot + 1)) templates.result)
    ⟨frame.domain.subst σ, frame.argument.subst σ, input⟩ .empty
  observed : NativeObservedValuation env U registry target locals σ available
    (expression.getAppFnArgs.2.take (data.indexOffset + templates.slot)) valuation

/-- All semantic calls are retained original argument/conversion children
or original registered-header formation payloads. The selected row has empty
output, so no fabricated function result demand is needed. -/
theorem HasTypeStrong.selectedRegisteredRow
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (registered : NativeRecursorRegistered env data) (typeClosed : templates.recursorType.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry []
      (templates.recursorType.instL program.levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) []
      (templates.recursorType.instL program.levels))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const data.name program.levels)
    (bound : data.indexOffset + templates.slot < expression.getAppFnArgs.2.length)
    {input : Profile n} {footprint : Footprint}
    (observation : Obs env U registry target locals σ
      expression.getAppFnArgs.2[data.indexOffset + templates.slot] input footprint)
    (resources : footprint.Available available) :
    Nonempty (NativeSelectedRegisteredRow sourceEnv env U registry source target locals σ available
      templates expression input) := by
  obtain ⟨frame, request, ⟨spine⟩⟩ := HasTypeStrong.selectedArgumentDomainSpine
    henv hscoped hle earlier closed hTarget substitutions fits original head
    (data.indexOffset + templates.slot) bound observation resources
  have root : NativeCodeRoot sourceEnv env U registry target locals σ available data.name program.levels
      (expression.getAppFnArgs.2.take (data.indexOffset + templates.slot))
      (request.profile frame.body) := by
    simpa only [frame.arguments_eq] using spine.codeRoot
  have prefixLength : (expression.getAppFnArgs.2.take (data.indexOffset + templates.slot)).length =
      data.indexOffset + templates.slot := by
    simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt bound)]
  have domainBound := (List.getElem?_eq_some_iff.mp templates.naturalOrigin).1
  obtain ⟨state⟩ := root.registered henv hscoped hle closed hTarget
    (signature := templates.signature) registered typeClosed formation header
    (by simpa only [prefixLength, NativeIndexTemplates.signature] using Nat.le_of_lt domainBound)
  have tree := (templates.signature.prefixPayload ⟨level, formation⟩ header
    (data.indexOffset + templates.slot)).1.2
  have literal := templates.signature.prefixResidual_cons templates.naturalOrigin
  have certificate := state.certificate
  have raw := state.substitutions
  have fitted := state.fits
  rw [prefixLength] at certificate raw fitted
  rw [literal] at tree certificate
  obtain ⟨domainLevel, rawDomain, originalDomain⟩ := tree.domain.1
  obtain ⟨bodyLevel, rawBody, originalBody⟩ := tree.codomain.1
  have origins := certificate.piOrigins henv hscoped hTarget state.closed
    (rawDomain.defeq.mono hle) (rawBody.defeq.mono hle) raw fitted
    originalDomain originalBody state.resources
  obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) request.key Profile.empty (List.mem_singleton_self _)
  exact ⟨⟨frame, state.valuation, row, state.observed⟩⟩

/-- Full index preparation from the actual saturated application's original
typing and its field ledger. The finite seed is collected first, then its
empty-output request is routed through every original conversion before the
registered row and declaration chain are assembled. -/
theorem NativeArgumentLedger.prepareRegisteredIndex
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (registered : NativeRecursorRegistered env data) (typeClosed : templates.recursorType.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry []
      (templates.recursorType.instL program.levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) []
      (templates.recursorType.instL program.levels))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const data.name program.levels)
    {captureArguments : List VExpr} {index : Nat} {declared : VExpr}
    (nativeOccurrence : expression.getAppFnArgs.2[data.indexOffset + templates.slot]? = some (.bvar index))
    (captureOccurrence : captureArguments[data.indexOffset + templates.field]? = some (.bvar index))
    (lookup : Lookup source index declared)
    (declaredOrigin : declared = templates.declaredDomain.instOuter
      (captureArguments.take (data.indexOffset + templates.field)))
    (declaredScope : templates.declaredDomain.ClosedN
      (captureArguments.take (data.indexOffset + templates.field)).length)
    {required : Footprint}
    (ledger : NativeArgumentLedger env U registry target locals σ available
      (captureArguments.take (data.indexOffset + templates.field + 1)) required)
    (minimum : Nat) :
    Nonempty (InitialNativeDirectIndexPreparation env U registry target templates locals σ available
      expression.getAppFnArgs.2 captureArguments required minimum) := by
  have captureNext : captureArguments.take (data.indexOffset + templates.field + 1) =
      captureArguments.take (data.indexOffset + templates.field) ++ [.bvar index] := by
    rw [List.take_add_one, captureOccurrence]
    rfl
  have current := captureNext ▸ ledger
  obtain ⟨cover⟩ := current.lastSeed minimum
  have bound := (List.getElem?_eq_some_iff.mp nativeOccurrence).1
  have valueEq := (List.getElem?_eq_some_iff.mp nativeOccurrence).2
  have observation : Obs env U registry target locals σ
      expression.getAppFnArgs.2[data.indexOffset + templates.slot] cover.seed.demand cover.seed.footprint := by
    simpa only [valueEq] using cover.seed.observation
  obtain ⟨selected⟩ := HasTypeStrong.selectedRegisteredRow henv hscoped hle earlier
    closed hTarget substitutions fits templates registered typeClosed formation header original head
    bound observation cover.seed.resources
  have argumentEq : selected.frame.argument = .bvar index :=
    Option.some.inj (selected.frame.selected.symm.trans nativeOccurrence)
  have argument : sourceEnv.HasTypeStrong U source (.bvar index) selected.frame.domain true := by
    exact Eq.mp (congrArg (fun e => sourceEnv.HasTypeStrong U source e selected.frame.domain true)
      argumentEq) selected.frame.argumentTyped
  have row : PiRowCertificate env U registry target (List.range (data.indexOffset + templates.slot))
      (nativeCaptureSubst ((expression.getAppFnArgs.2.take (data.indexOffset + templates.slot)).map (·.subst σ)))
      selected.valuation templates.naturalDomain
      (wrapForalls (templates.inputDomains.drop (data.indexOffset + templates.slot + 1)) templates.result)
      ⟨selected.frame.domain.subst σ, σ index, cover.seed.demand⟩ .empty := by
    simpa only [argumentEq, VExpr.subst] using selected.row
  exact cover.prepareDirectIndex henv hscoped hle (fun H => (earlier H).joint)
    closed hTarget substitutions fits templates nativeOccurrence captureOccurrence argument lookup
    declaredOrigin declaredScope ledger row selected.observed

end Lean4Lean.AnchoredSource.Adapted
