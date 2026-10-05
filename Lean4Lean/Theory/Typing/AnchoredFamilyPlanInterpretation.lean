import Lean4Lean.Theory.Typing.AnchoredConstantPlanBinder
import Lean4Lean.Theory.Typing.AnchoredFamilyCaptureInterpretation

/-! A bare family telescope plan is interpreted from its original declaration
header. Binders use the shared finite-plan proof; terminal argument evidence
comes from actual captured variables with their retained domain conversions. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private capture_vars from Lean4Lean.Theory.Typing.AnchoredNativePartialTelescope
set_option backward.isDefEq.respectTransparency false

private theorem captureVariables_subst (arguments : List VExpr) :
    (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst arguments)) =
      arguments := by
  simpa only [constantCaptureVariables, vars, Nat.zero_add] using capture_vars arguments

/-- Interpretation follows rank for binder and padding children, and actual
plan size for same-rank views. The earlier theorem concerns the original
strictly earlier declaration environment only. -/
theorem FamilyPlan.supported
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → GradedJoint env U registry Γ l r A)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (constant : env.HasType U [] (.const name levels) declaredType)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (typeClosed : declaredType.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] declaredType declaredType (.sort typeLevel))
    {target : List VExpr} {arguments newValues : List VExpr}
    {demand support : Profile n} {footprint : Footprint} {available : Valuation}
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint)
    (hTarget : OnCtx target (env.IsType U))
    (bound : arguments.length ≤ signature.domains.length)
    (newLength : newValues.length = arguments.length) (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse)
    (fits : PairedFits env U registry (signature.domains.take arguments.length).reverse target
      (List.range arguments.length) (nativeCaptureSubst arguments)
      (nativeCaptureSubst newValues) available)
    (resources : footprint.Available available) (typed : demand.HasType support)
    (code : TypeRelated env U registry target
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments)) support) :
    Related env U registry target (mkApps (.const name levels) arguments)
      (mkApps (.const name levels) newValues)
      ((wrapForalls (signature.domains.drop arguments.length) signature.result).subst (nativeCaptureSubst arguments))
      demand support := by
  match n, demand, footprint, plan with
  | _ + 1, _, _, .terminal saturated resultSort relevance captures =>
    have sourceContext := signature.prefixCtxStrong typeFormation signature.domains.length
    rw [List.take_length] at sourceContext
    have prefixRaw := (signature.prefixArgumentsEqual henv hTarget constant bound rfl newLength raw).1
    rw [saturated, List.take_length] at raw fits
    have fields := captures.interpret henv hscoped hsource earlier sourceContext hTarget
      closed raw (by simpa only [saturated] using fits) resources
    have rightVars :
        (constantCaptureVariables arguments.length).map (·.subst (nativeCaptureSubst newValues)) =
          newValues := by
      rw [← newLength, captureVariables_subst]
    rw [captureVariables_subst, rightVars] at fields
    rw [saturated, List.drop_length, resultSort] at prefixRaw
    simp only [wrapForalls, subst] at prefixRaw
    exact Related.family henv hscoped typed code
      (RankedData.literalFamilyCode henv hscoped notDefinition notNative notQuotient
        prefixRaw relevance fields)
  | _ + 1, _, _, .binder origin domainCode guard body pack covered =>
    apply ConstantPlanSupported.binder
      (Plan := fun target arguments => FamilyPlan env U registry target name levels signature arguments)
      henv hscoped hle earlier typeClosed typeFormation
      (fun child hTarget bound newLength closed raw fits resources typed code =>
        child.supported henv hscoped hsource hle earlier constant notDefinition notNative
          notQuotient typeClosed typeFormation hTarget bound newLength closed raw fits resources typed code)
      origin domainCode guard
      (fun Δ ρ future => by
        simpa only [Profile.rename_singleton] using body.future henv future typeClosed)
      pack covered hTarget newLength closed raw fits resources typed code
  | _, _, _, .view child change =>
    have inverse := change.inverse henv
    have before := child.supported henv hscoped hsource hle earlier constant
      notDefinition notNative notQuotient typeClosed typeFormation hTarget bound newLength
      closed raw fits resources (inverse.mapType_typed typed) (inverse.codeMap henv hscoped code)
    exact (change.termMap henv hscoped hTarget before).retag henv typed code
  | _ + 1, _, _, .pad child =>
    have before := child.supported henv hscoped hsource hle earlier constant
      notDefinition notNative notQuotient typeClosed typeFormation hTarget bound newLength
      closed raw fits resources typed.pad_inv (code.down henv)
    exact (before.pad henv).retag henv typed code
termination_by (n, sizeOf plan)
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted
