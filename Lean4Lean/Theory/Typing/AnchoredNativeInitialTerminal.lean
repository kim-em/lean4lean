import Lean4Lean.Theory.Typing.AnchoredNativeCaptureOrigins
import Lean4Lean.Theory.Typing.AnchoredNativeApplicationObservation

/-! Assemble the actual initial native terminal from the original equation's
right-hand-side observation. Its source variable leaves supply the capture
ledger; the backward route supplies the native ledger and capture guards. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private native_wrap_scope native_spine_scoped
  from Lean4Lean.Theory.Typing.AnchoredNativeSyntaxTransport
set_option backward.isDefEq.respectTransparency false

theorem NativeCaptureOrigins.prefix_eq
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (origins : NativeCaptureOrigins sourceEnv U source program nativeArguments captureArguments fields) :
    captureArguments.take data.indexOffset = nativeArguments.take data.indexOffset := by
  induction origins with
  | «prefix» same _ => exact same
  | index _ _ _ _ _ _ ih => exact ih
  | proof _ _ _ _ _ _ _ _ ih => exact ih

theorem nativeCaptureSubst_variables (count : Nat) (σ : Subst) (index : Nat) (bound : index < count) :
    nativeCaptureSubst ((vars count 0).map (·.subst σ)) index = σ index := by
  have length : ((vars count 0).map (·.subst σ)).length = count := by simp [vars]
  simp only [nativeCaptureSubst, length, dif_pos bound]
  simp only [List.getElem_map, vars, List.getElem_reverse, List.length_range,
    List.getElem_map, List.getElem_range, Nat.zero_add, subst_bvar]
  congr 1
  omega

theorem initialCaptureLength
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments : List VExpr}
    (selected : data.saturatedProgram levels arguments = some program) :
    program.equationBody.domains.length = data.indexOffset + program.instructions.length := by
  have spec := saturatedProgram_spec selected
  have counts := SaturatedCaptureState.run_counts spec.2.2.2.2.2.2.2.2.2.2.2.1
  have enough : data.indexOffset ≤ program.prefixArgs.length := by
    rw [spec.2.2.1, majorOffset]
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, captureCount, _⟩ := spec
  rw [← captureCount]
  simpa only [List.length_take,
    Nat.min_eq_left enough, List.length_nil, Nat.zero_add] using counts.1

/-- The selected parser result and original declaration provenance suffice
to build the terminal. No terminal observation, native ledger, or raw
all-index argument alignment is a premise. -/
theorem NativeCaptureOrigins.initialTerminal_witnessed
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    (registered : NativeRecursorRegistered env data)
    (typeClosed : signature.type.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry []
      (signature.type.instL program.levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) []
      (signature.type.instL program.levels))
    (selected : data.saturatedProgram program.levels
      (((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map (·.subst σ)) = some program)
    (noTrailing : program.trailing = [])
    {assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source
      (program.equationBody.lhs.instL program.levels) assigned structural)
    (head : (program.equationBody.lhs.instL program.levels).getAppFnArgs.1 =
      .const data.name program.levels)
    (origins : NativeCaptureOrigins sourceEnv U source program
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
      (vars program.equationBody.domains.length 0) program.instructions.length)
    {demand : Profile n} {bodyFootprint : Footprint}
    (body : Obs env U registry target locals σ
      (program.equationBody.rhs.instL program.levels) demand bodyFootprint)
    (resources : bodyFootprint.Available available) (minimum : Nat) :
    ∃ nativeFootprint,
      ∃ terminal : NativeInitialTerminal env U registry target signature
        (((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map (·.subst σ))
        demand nativeFootprint,
      terminal.program = program ∧
      terminal.witnesses = (vars program.equationBody.domains.length 0).map (·.subst σ) ∧
      Nonempty (NativeArgumentLedger env U registry target locals σ available
        (program.equationBody.lhs.instL program.levels).getAppFnArgs.2 nativeFootprint) := by
  have spec := saturatedProgram_spec selected
  have nativeValues : program.prefixArgs =
      (((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map (·.subst σ)) := by
    simpa only [noTrailing, List.append_nil] using spec.2.2.2.1
  have raw := henv.defEqWF (registered.singletonEquation spec.2.2.2.2.2.2.2.2.1)
  have rhsClosed : program.equation.rhs.Closed :=
    VExpr.WF.closedN henv ⟨_, raw.2⟩ trivial
  have lhsClosed : program.equation.lhs.Closed :=
    VExpr.WF.closedN henv ⟨_, raw.1⟩ trivial
  have rhsScope := (scope_of_extract spec.2.2.2.2.2.2.2.2.2.1 rhsClosed).2.instL
    (ls := program.levels)
  have lhsScope : (program.equationBody.lhs.instL program.levels).ClosedN
      program.equationBody.domains.length := by
    have wrapped := (CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1).1
    have scope : program.equationBody.lhs.ClosedN program.equationBody.domains.length := by
      simpa only [Nat.zero_add] using native_wrap_scope (count := 0) _ _ (wrapped ▸ lhsClosed)
    exact scope.instL
  obtain ⟨ledger⟩ := NativeArgumentLedger.variables (env := env) (U := U) (registry := registry)
    (target := target) (locals := locals) (σ := σ) (body.scoped rhsScope) resources
  have captureLength := initialCaptureLength selected
  have captureTake : (vars program.equationBody.domains.length 0).take
      (data.indexOffset + program.instructions.length) = vars program.equationBody.domains.length 0 := by
    apply List.take_of_length_le
    simp only [vars, List.length_map, List.length_reverse, List.length_range, captureLength]
    exact Nat.le_refl _
  have wholeLedger := captureTake.symm ▸ ledger
  let witnesses := (vars program.equationBody.domains.length 0).map (·.subst σ)
  obtain ⟨route⟩ := origins.route henv hscoped hle earlier closed hTarget substitutions fits
    registered signature.typeOrigin typeClosed formation header original head nativeValues
    (witnesses := witnesses) rfl wholeLedger minimum
  have normalized := body.realizePrefix rhsScope (nativeCaptureSubst witnesses)
    (fun i hi => (nativeCaptureSubst_variables _ σ i hi).symm)
  have terminalBody : Obs env U registry target (List.range program.equationBody.domains.length)
      (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL program.levels) demand bodyFootprint := by
    simpa [Footprint.sourceLift, Lift.liftVar] using
      normalized.renameSource .refl (nativeCaptureSubst witnesses) rfl
        (List.range program.equationBody.domains.length)
  refine ⟨route.nativeFootprint, {
    program := program
    selected := selected
    saturated := nativeValues ▸ spec.2.2.1
    noTrailing := noTrailing
    prefix_eq := nativeValues
    witnesses := witnesses
    witnessLength := by simp [witnesses, vars]
    witnessPrefix := ?_
    arguments_eq := ?_
    bodyFootprint := bodyFootprint
    body := terminalBody
    captures := route.support }, rfl, rfl, ⟨route.ledger⟩⟩
  · simpa only [witnesses, List.map_take] using
      congrArg (List.map (·.subst σ)) origins.prefix_eq
  · apply List.map_congr_left
    intro argument member
    exact subst_congr_closedN (native_spine_scoped lhsScope argument member)
      (fun i hi => (nativeCaptureSubst_variables _ σ i hi).symm)

/-- Compatibility projection of the witnessed terminal producer. -/
theorem NativeCaptureOrigins.initialTerminal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    (registered : NativeRecursorRegistered env data)
    (typeClosed : signature.type.Closed)
    (formation : OriginalTypePayload sourceEnv env U registry []
      (signature.type.instL program.levels) (.sort level))
    (header : SourcePiFormation (OriginalTypePayload sourceEnv env U registry) []
      (signature.type.instL program.levels))
    (selected : data.saturatedProgram program.levels
      (((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map (·.subst σ)) = some program)
    (noTrailing : program.trailing = [])
    {assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source
      (program.equationBody.lhs.instL program.levels) assigned structural)
    (head : (program.equationBody.lhs.instL program.levels).getAppFnArgs.1 =
      .const data.name program.levels)
    (origins : NativeCaptureOrigins sourceEnv U source program
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
      (vars program.equationBody.domains.length 0) program.instructions.length)
    {demand : Profile n} {bodyFootprint : Footprint}
    (body : Obs env U registry target locals σ
      (program.equationBody.rhs.instL program.levels) demand bodyFootprint)
    (resources : bodyFootprint.Available available) (minimum : Nat) :
    ∃ nativeFootprint,
      Nonempty (NativeInitialTerminal env U registry target signature
        (((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map (·.subst σ))
        demand nativeFootprint) ∧
      Nonempty (NativeArgumentLedger env U registry target locals σ available
        (program.equationBody.lhs.instL program.levels).getAppFnArgs.2 nativeFootprint) := by
  obtain ⟨required, terminal, _, _, ledger⟩ := NativeCaptureOrigins.initialTerminal_witnessed
    henv hscoped hle earlier closed hTarget substitutions fits registered typeClosed formation header
    selected noTrailing original head origins body resources minimum
  exact ⟨required, ⟨terminal⟩, ledger⟩

/-- Construct the original equation's native left-side observer from its
right-side observer, finite declaration provenance, and actual assigned-type
certificate. The terminal and native ledger are now conclusions internally. -/
theorem NativeCaptureOrigins.initialObservation
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    (registered : NativeRecursorRegistered env data)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    (typeClosed : signature.type.Closed)
    (formation : sourceEnv.IsDefEqStrong U [] (signature.type.instL program.levels)
      (signature.type.instL program.levels) (.sort level))
    (selected : data.saturatedProgram program.levels
      (((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map (·.subst σ)) = some program)
    (noTrailing : program.trailing = [])
    {assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source
      (program.equationBody.lhs.instL program.levels) assigned structural)
    (head : (program.equationBody.lhs.instL program.levels).getAppFnArgs.1 =
      .const data.name program.levels)
    (origins : NativeCaptureOrigins sourceEnv U source program
      (program.equationBody.lhs.instL program.levels).getAppFnArgs.2
      (vars program.equationBody.domains.length 0) program.instructions.length)
    {atom : Atom n} {bodyFootprint : Footprint}
    (body : Obs env U registry target locals σ
      (program.equationBody.rhs.instL program.levels) (.singleton atom) bodyFootprint)
    (resources : bodyFootprint.Available available)
    {support : Profile n} {typeFootprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support typeFootprint)
    (typeResources : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ
      (program.equationBody.lhs.instL program.levels) (.singleton atom) footprint) ∧
      footprint.Available available := by
  have payload := earlier formation
  obtain ⟨required, ⟨leaf⟩, ⟨ledger⟩⟩ := origins.initialTerminal henv hscoped hle earlier
    closed hTarget substitutions fits registered typeClosed ⟨formation, payload.joint⟩
    payload.leftFormation selected noTrailing original head body resources n
  exact HasTypeStrong.nativeObservation henv hscoped hle earlier closed hTarget
    substitutions fits lookup notDefinition registered levelsWF typeClosed formation original head
    leaf ledger certificate typeResources typed

end Lean4Lean.AnchoredSource.Adapted
