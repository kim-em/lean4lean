import Lean4Lean.Theory.Typing.AnchoredBoundedConstantPlanBinder
import Lean4Lean.Theory.Typing.AnchoredBoundedConstructorTerminalInterpretation

/-! A constructor telescope plan is interpreted from its original declaration
header. Binders use the shared finite-plan proof; terminal argument evidence
comes from actual captured variables with their retained domain conversions. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
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
theorem ConstructorPlan.supported
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A → Joint current fuel env U registry Γ l r A)
    {info : VConstant} {name : Name} {levels : List VLevel}
    {signature : ConstantTelescope (info.type.instL levels)}
    (lookup : env.constants name = some info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelLength : levels.length = info.uvars)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (typeClosed : info.type.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (info.type.instL levels) (info.type.instL levels) (.sort typeLevel))
    {target : List VExpr} {arguments newValues : List VExpr}
    {demand support : Profile n} {footprint : Footprint} {available : Valuation}
    (plan : Adapted.ConstructorPlan env U registry target name levels signature arguments demand footprint)
    (planBound : plan.nativeDepth current ≤ fuel)
    (hTarget : OnCtx target (env.IsType U))
    (bound : arguments.length ≤ signature.domains.length)
    (newLength : newValues.length = arguments.length) (closed : available.AtomClosed)
    (raw : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
      (signature.domains.take arguments.length).reverse)
    (fits : PairedFits current fuel env U registry (signature.domains.take arguments.length).reverse target
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
  | _ + 1, _, _, .terminal saturated resultShape relevant captures resultCode =>
    have raw' : Ctx.SubstEq env U target (nativeCaptureSubst arguments) (nativeCaptureSubst newValues)
        signature.domains.reverse := by simpa only [saturated, List.take_length] using raw
    have fits' : PairedFits current fuel env U registry signature.domains.reverse target
        (List.range arguments.length) (nativeCaptureSubst arguments) (nativeCaptureSubst newValues) available := by
      simpa only [saturated, List.take_length] using fits
    have code' := code
    simp only [saturated, List.drop_length, wrapForalls] at code' ⊢
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by
      simpa only [Adapted.ConstructorPlan.nativeDepth] using planBound)
    exact FamilyCaptures.constructorSupported henv hscoped hsource earlier lookup levelsWF levelLength
      ⟨notDefinition, notNative, Or.inr notQuotient⟩ resultShape typeFormation saturated newLength
      captures bounds.1 resultCode bounds.2 hTarget closed raw' fits' resources typed code'
  | _ + 1, _, _, .binder origin domainCode guard body pack covered =>
    have bounds := Nat.max_le.mp (show max _ _ ≤ fuel from by simpa only [Adapted.ConstructorPlan.nativeDepth] using planBound)
    apply ConstantPlanSupported.binder
      (Plan := fun target arguments {_n} demand footprint =>
        {child : Adapted.ConstructorPlan env U registry target name levels signature arguments demand footprint //
          child.nativeDepth current ≤ fuel})
      henv hscoped hle earlier typeClosed.instL typeFormation
      (fun child hTarget bound newLength closed raw fits resources typed code =>
        ConstructorPlan.supported henv hscoped hsource hle earlier lookup levelsWF levelLength notDefinition notNative
          notQuotient typeClosed typeFormation child.val child.property
          hTarget bound newLength closed raw fits resources typed code)
      origin domainCode bounds.1 guard
      (fun Δ ρ future => ⟨by
        simpa only [Profile.rename_singleton] using body.future henv future typeClosed.instL, by
        simp only [ConstructorPlan.nativeDepth_mpr, ConstructorPlan.nativeDepth_mp,
          ConstructorPlan.nativeDepth_future]
        exact bounds.2⟩)
      pack covered hTarget newLength closed raw fits resources typed code
  | _, _, _, .view child change =>
    have inverse := change.inverse henv
    have before := ConstructorPlan.supported henv hscoped hsource hle earlier lookup levelsWF levelLength
      notDefinition notNative notQuotient typeClosed typeFormation child (by simpa only [Adapted.ConstructorPlan.nativeDepth] using planBound)
      hTarget bound newLength closed raw fits resources
      (inverse.mapType_typed typed) (inverse.codeMap henv hscoped code)
    exact (change.termMap henv hscoped hTarget before).retag henv typed code
  | _ + 1, _, _, .pad child =>
    have before := ConstructorPlan.supported henv hscoped hsource hle earlier lookup levelsWF levelLength
      notDefinition notNative notQuotient typeClosed typeFormation child (by simpa only [Adapted.ConstructorPlan.nativeDepth] using planBound)
      hTarget bound newLength closed raw fits resources typed.pad_inv (code.down henv)
    exact (before.pad henv).retag henv typed code
termination_by (n, sizeOf plan)
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.Staged
