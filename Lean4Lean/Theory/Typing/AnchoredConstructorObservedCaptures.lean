import Lean4Lean.Theory.Typing.AnchoredConstructorConsumeObservation
import Lean4Lean.Theory.Typing.AnchoredConstructorConsumedCaptures

/-! End-to-end capture extraction starts with an actual source observation.
Its application spine, frozen terminal requests, declaration alignments and
caller resources are recovered together; saturation is derived from the
requested constructor atom rather than assumed by the caller. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature

theorem Obs.constructorCaptures
    {env : VEnv} {info : VConstant} {name : Name}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : ConstantHeaderOrigin env name info)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ left right type}, origin.source.IsDefEqStrong U Γ left right type →
      GradedJoint env U registry Γ left right type)
    {domains familyArguments : List VExpr} {family : Name} {familyLevels : List VLevel}
    (shape : info.type = wrapForalls domains (mkApps (.const family familyLevels) familyArguments))
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (hTarget : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (fits : Fits env U registry source target locals σ σ available)
    {expression : VExpr} {profile : Profile (n + 1)} {footprint : Footprint}
    (observation : Obs env U registry target locals σ expression profile footprint)
    {levels : List VLevel} (head : expression.getAppFnArgs.1 = .const name levels)
    (scope : expression.ClosedN source.length)
    (resources : footprint.Available available)
    {demand : ConstructorData (Profile n)} (member : .ctor demand ∈ profile.atoms) :
    ∃ consumed : ConstructorPlanConsumption env U registry target locals σ available info name levels
      expression.getAppFnArgs.2 (n := n + 1) (.ctor demand),
      Nonempty (ConstructorConsumedCaptures consumed) := by
  obtain ⟨consumed⟩ := observation.consumeConstructor origin henv hscoped (fun H => earlier H)
    shape notDefinition notNative hTarget fits head scope resources member
  obtain ⟨level, formation⟩ := origin.typeInstance consumed.seedWF
  exact ⟨consumed, consumed.constructorSourceCaptures henv hscoped origin.ordered earlier
    formation hTarget closed⟩

end Lean4Lean.AnchoredSource.Adapted
