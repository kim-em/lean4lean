import Lean4Lean.Theory.Typing.AnchoredBoundedNativePlanBinder
import Lean4Lean.Theory.Typing.AnchoredNativePlanInterpretation
import Lean4Lean.Theory.Typing.AnchoredBoundedTerminalInterpretation
import Lean4Lean.Theory.Typing.AnchoredNativeTerminalInterpretation

/-! Interpretation of a finite native telescope plan. Its only semantic
induction premise is the strict declaration-predecessor theorem; equation
and type inputs retain their original raw Strong derivations. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem terminalSupported
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → Joint current fuel env U registry Γ l r A)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (registered : NativeRecursorRegistered env data)
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equations : ∀ equation, data.singletonEquation = some equation →
      Nonempty (NativeOriginalEquation sourceEnv U levels equation))
    {target : List VExpr} {arguments newValues : List VExpr}
    (program : SaturatedProgram data)
    (selected : data.saturatedProgram levels arguments = some program)
    (saturated : arguments.length = data.majorOffset + 1)
    (noTrailing : program.trailing = []) (prefixEq : program.prefixArgs = arguments)
    (witnesses : List VExpr)
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    (witnessPrefix : witnesses.take data.indexOffset = arguments.take data.indexOffset)
    (literal : arguments = nativeEquationArguments program witnesses)
    {demand support : Profile n} {bodyFootprint nativeFootprint : Footprint}
    (body : Obs env U registry target (List.range program.equationBody.domains.length)
      (nativeCaptureSubst witnesses) (program.equationBody.rhs.instL levels) demand bodyFootprint)
    (captures : NativeCaptures env U registry target program witnesses
      program.instructions.length bodyFootprint nativeFootprint)
    (bodyBound : body.nativeDepth current ≤ fuel)
    (capturesBound : captures.nativeDepth current ≤ fuel)
    (hTarget : OnCtx target (env.IsType U))
    (newLength : newValues.length = arguments.length)
    {available : Valuation} (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse)
    (fits : PairedFits current fuel env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst newValues) available)
    (resources : nativeFootprint.Available available)
    (typed : demand.HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments)) support) :
    Related env U registry target (mkApps (.const data.name levels) arguments)
      (mkApps (.const data.name levels) newValues)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      demand support := by
  have spec := saturatedProgram_spec selected
  obtain ⟨original⟩ := equations program.equation spec.2.2.2.2.2.2.2.2.1
  have levelEq := spec.1
  subst levels
  subst arguments
  have fullLength : program.prefixArgs.length = signature.domains.length :=
    saturated.trans (takeForalls_length signature.telescope).symm
  rw [fullLength, List.take_length] at raw fits
  rw [fullLength, List.drop_length] at code ⊢
  simp only [wrapForalls] at code ⊢
  obtain ⟨result, _⟩ := captures.terminalPairBounded henv hscoped hsource hle earlier hTarget signature
    registered lookup notDefinition (by simpa only [noTrailing, List.append_nil] using selected)
    levelsWF witnessLength witnessPrefix literal newLength raw
    (by simpa only [fullLength] using fits) closed
    original.left original.right original.formation body bodyBound capturesBound resources
  exact result.nativeRelated.retag henv typed code

/-- Full native plan adequacy, including all registered binders and the actual
saturated machine. The terminal's literal equation tuple and the supplied
registered type capability are both used; neither is replaced by raw typing
uniqueness or a semantic guard oracle. -/
theorem NativePlan.supported
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → Joint current fuel env U registry Γ l r A)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (registered : NativeRecursorRegistered env data)
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (typeClosed : signature.type.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (signature.type.instL levels)
      (signature.type.instL levels) (.sort typeLevel))
    (equations : ∀ equation, data.singletonEquation = some equation →
      Nonempty (NativeOriginalEquation sourceEnv U levels equation)) :
    NativePlanSupported current fuel env U registry signature n := by
  induction n with
  | zero =>
    intro target arguments newValues demand footprint support available plan planBound hTarget bound
      newLength closed raw fits resources typed code
    cases plan with
    | terminal program selected lhsClosed rhsClosed saturated noTrailing prefixEq witnesses
        witnessLength witnessPrefix alignment literal body captures =>
      exact terminalSupported henv hscoped hsource hle earlier registered lookup notDefinition levelsWF
        equations program selected saturated noTrailing prefixEq witnesses witnessLength witnessPrefix
        literal body captures
        (Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativePlan.nativeDepth] using planBound)).1
        (Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativePlan.nativeDepth] using planBound)).2 hTarget newLength closed raw fits resources typed code
  | succ n lower =>
    intro target arguments newValues demand footprint support available plan planBound hTarget bound
      newLength closed raw fits resources typed code
    cases plan with
    | terminal program selected lhsClosed rhsClosed saturated noTrailing prefixEq witnesses
        witnessLength witnessPrefix alignment literal body captures =>
      exact terminalSupported henv hscoped hsource hle earlier registered lookup notDefinition levelsWF
        equations program selected saturated noTrailing prefixEq witnesses witnessLength witnessPrefix
        literal body captures
        (Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativePlan.nativeDepth] using planBound)).1
        (Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativePlan.nativeDepth] using planBound)).2 hTarget newLength closed raw fits resources typed code
    | binder origin domainCode guard body pack covered =>
      exact NativePlan.binderSupported henv hscoped hle earlier typeClosed typeFormation lower
        origin domainCode (Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativePlan.nativeDepth] using planBound)).1
        guard body (Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [NativePlan.nativeDepth] using planBound)).2 pack covered hTarget newLength closed raw fits resources typed code

end Lean4Lean.AnchoredSource.Adapted.Staged
