import Lean4Lean.Theory.Typing.AnchoredNativeTerminalInterpretation
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedCode

/-! The native terminal retains a certificate of the registered residual
itself. Its finite argument requirements are explicit; capture requirements
alone do not cover a residual mentioning a computed result index. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- Both certificates refer to the original registered result template. The
right certificate is obtained through its original formation child. -/
structure NativeResultSupported (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels)
    (witnesses newValues : List VExpr) (available : Valuation)
    (demand support : Profile n) where
  footprint : Footprint
  certificate : CodeCert env U registry target (List.range program.prefixArgs.length)
    (nativeCaptureSubst program.prefixArgs) signature.result support footprint
  resources : footprint.Available available
  targetFootprint : Footprint
  targetCertificate : CodeCert env U registry target (List.range program.prefixArgs.length)
    (nativeCaptureSubst newValues) signature.result support targetFootprint
  targetResources : targetFootprint.Available available
  typed : demand.HasType support
  typeCode : TypeRelated env U registry target
    (signature.result.subst (nativeCaptureSubst program.prefixArgs))
    (signature.result.subst (nativeCaptureSubst newValues)) support
  witnessed : Related env U registry target
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand support
  related : Related env U registry target
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    (mkApps (.const data.name program.levels) newValues)
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand support
  targetRelated : Related env U registry target
    ((program.equationBody.rhs.instL program.levels).subst (nativeCaptureSubst witnesses))
    (mkApps (.const data.name program.levels) newValues)
    (signature.result.subst (nativeCaptureSubst newValues)) demand support

/-- Retag the checked machine expansion using an actual registered-result
certificate. No raw result-type conversion is promoted to semantic evidence. -/
theorem NativeTerminalRelatedResult.resultSupport
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    {witnesses newValues : List VExpr} {available : Valuation}
    {demand support : Profile n} {footprint : Footprint}
    (terminal : NativeTerminalRelatedResult env U registry target program signature
      witnesses newValues demand)
    (originalResult : GradedJoint env U registry signature.domains.reverse
      signature.result signature.result (.sort resultLevel))
    (closed : available.AtomClosed)
    (rawArguments : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (argumentFits : PairedFits env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) available)
    (certificate : CodeCert env U registry target (List.range program.prefixArgs.length)
      (nativeCaptureSubst program.prefixArgs) signature.result support footprint)
    (resources : footprint.Available available) (typed : demand.HasType support) :
    Nonempty (NativeResultSupported env U registry target program signature witnesses
      newValues available demand support) := by
  obtain ⟨result⟩ := certificate.transfer_graded henv hscoped hTarget closed
    (originalResult target _ _ _ available closed hTarget rawArguments argumentFits).1 resources
  have related := terminal.related.retag henv typed result.related.left_diagonal
  exact ⟨{
    footprint := footprint
    certificate := certificate
    resources := resources
    targetFootprint := result.footprint
    targetCertificate := result.certificate
    targetResources := result.available
    typed := typed
    typeCode := result.related
    witnessed := terminal.witnessed.retag henv typed result.related.left_diagonal
    related := related
    targetRelated := related.convert henv typed result.related }⟩

structure NativePairResultSupported (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {data : NativeRecursorData} (program : SaturatedProgram data)
    (signature : NativeConstantSignature data program.levels)
    (witnesses newValues : List VExpr) (available : Valuation)
    (demand support : Profile n)
    extends NativeResultSupported env U registry target program signature witnesses
      newValues available demand support where
  nativeRelated : Related env U registry target
    (mkApps (.const data.name program.levels) program.prefixArgs)
    (mkApps (.const data.name program.levels) newValues)
    (signature.result.subst (nativeCaptureSubst program.prefixArgs)) demand support
  targetNativeRelated : Related env U registry target
    (mkApps (.const data.name program.levels) program.prefixArgs)
    (mkApps (.const data.name program.levels) newValues)
    (signature.result.subst (nativeCaptureSubst newValues)) demand support

theorem NativeTerminalPairResult.resultSupport
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {signature : NativeConstantSignature data program.levels}
    {witnesses newValues : List VExpr} {available : Valuation}
    {demand support : Profile n} {footprint : Footprint}
    (terminal : NativeTerminalPairResult env U registry target program signature
      witnesses newValues demand)
    (originalResult : GradedJoint env U registry signature.domains.reverse
      signature.result signature.result (.sort resultLevel))
    (closed : available.AtomClosed)
    (rawArguments : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (argumentFits : PairedFits env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) available)
    (certificate : CodeCert env U registry target (List.range program.prefixArgs.length)
      (nativeCaptureSubst program.prefixArgs) signature.result support footprint)
    (resources : footprint.Available available) (typed : demand.HasType support) :
    Nonempty (NativePairResultSupported env U registry target program signature witnesses
      newValues available demand support) := by
  obtain ⟨result⟩ := terminal.toNativeTerminalRelatedResult.resultSupport henv hscoped hTarget
    originalResult closed rawArguments argumentFits certificate resources typed
  have related := terminal.nativeRelated.retag henv typed result.typeCode.left_diagonal
  exact ⟨{ result with
    nativeRelated := related
    targetNativeRelated := related.convert henv typed result.typeCode }⟩

/-- The complete finite capture producer followed by the registered-result
formation child. There is no terminal replay or semantic expansion callback. -/
theorem NativeCaptures.terminalResultSupport
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type}, sourceEnv.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (lookup : registry.natives data.name = some data) (notDefinition : registry.definitions data.name = none)
    (selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program)
    (levelsWF : ∀ level ∈ program.levels, level.WF U)
    {witnesses newValues : List VExpr} {argumentAvailable : Valuation}
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    (witnessPrefix : witnesses.take data.indexOffset = program.prefixArgs.take data.indexOffset)
    (literal : program.prefixArgs = nativeEquationArguments program witnesses)
    (newLength : newValues.length = program.prefixArgs.length)
    (rawArguments : Ctx.SubstEq env U target (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) signature.domains.reverse)
    (argumentFits : PairedFits env U registry signature.domains.reverse target
      (List.range program.prefixArgs.length) (nativeCaptureSubst program.prefixArgs)
      (nativeCaptureSubst newValues) argumentAvailable)
    (closed : argumentAvailable.AtomClosed)
    (left : sourceEnv.HasTypeStrong U [] (program.equation.lhs.instL program.levels)
      (program.equation.type.instL program.levels) leftStructural)
    (right : sourceEnv.HasTypeStrong U [] (program.equation.rhs.instL program.levels)
      (program.equation.type.instL program.levels) rightStructural)
    (formation : sourceEnv.IsDefEqStrong U [] (program.equation.type.instL program.levels)
      (program.equation.type.instL program.levels) (.sort level))
    {demand : Profile n} {footprint nativeFootprint : Footprint}
    (body : Obs env U registry target (List.range program.equationBody.domains.length)
      (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL program.levels) demand footprint)
    (captures : NativeCaptures env U registry target program witnesses program.instructions.length
      footprint nativeFootprint)
    (resources : nativeFootprint.Available argumentAvailable)
    {support : Profile n} {resultFootprint : Footprint}
    (originalResult : GradedJoint env U registry signature.domains.reverse
      signature.result signature.result (.sort resultLevel))
    (certificate : CodeCert env U registry target (List.range program.prefixArgs.length)
      (nativeCaptureSubst program.prefixArgs) signature.result support resultFootprint)
    (resultResources : resultFootprint.Available argumentAvailable)
    (typed : demand.HasType support) :
    Nonempty (NativePairResultSupported env U registry target program signature witnesses
      newValues argumentAvailable demand support) := by
  obtain ⟨terminal⟩ := captures.terminalPair henv hscoped hsource hle earlier hTarget signature
    registered lookup notDefinition selected levelsWF witnessLength witnessPrefix literal newLength
    rawArguments argumentFits closed left right formation body resources
  exact terminal.resultSupport henv hscoped hTarget originalResult closed rawArguments
    argumentFits certificate resultResources typed

end Lean4Lean.AnchoredSource.Adapted
