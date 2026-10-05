import Lean4Lean.Theory.Typing.AnchoredNativeSpineSkeleton
import Lean4Lean.Theory.Typing.AnchoredNativeSkeletonObservation
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope

/-! Construct the original saturated application's source observation from
its actual terminal and argument ledger. The registered header is identified
by lookup uniqueness; its original closed formation, rather than a semantic
strengthening of the application context, supplies the telescope payload. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

theorem HasTypeStrong.nativeObservation
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    (registered : NativeRecursorRegistered env data)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (typeClosed : signature.type.Closed)
    (formation : sourceEnv.IsDefEqStrong U [] (signature.type.instL levels)
      (signature.type.instL levels) (.sort level))
    {expression assigned : VExpr} {structural : Bool}
    (original : sourceEnv.HasTypeStrong U source expression assigned structural)
    (head : expression.getAppFnArgs.1 = .const data.name levels)
    {atom : Atom n} {required : Footprint}
    (leaf : NativeInitialTerminal env U registry target signature
      (expression.getAppFnArgs.2.map (·.subst σ)) (.singleton atom) required)
    (ledger : NativeArgumentLedger env U registry target locals σ available
      expression.getAppFnArgs.2 required)
    {support : Profile n} {typeFootprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support typeFootprint)
    (resources : typeFootprint.Available available)
    (typed : (Profile.singleton atom).HasType support) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ expression (.singleton atom) footprint) ∧
      footprint.Available available := by
  obtain ⟨root, ⟨skeleton⟩⟩ := HasTypeStrong.nativeSkeleton henv hscoped hle earlier
    closed hTarget substitutions fits original head leaf ledger certificate resources typed
  have rootType : root.info.type = signature.type := by
    have same := (hle.constants root.lookup).symm.trans
      (registered.recursorType signature.typeOrigin)
    exact congrArg VConstant.type (Option.some.inj same)
  have rootClosed : (root.info.type.instL levels).Closed := by
    rw [rootType]
    exact typeClosed.instL
  have footprintEmpty : root.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    have impossible := root.certificate.scoped rootClosed index need member
    omega
  have rootCode : CodeCert env U registry target locals σ
      (signature.type.instL levels) root.support [] := by
    rw [← rootType, ← footprintEmpty]
    exact root.certificate
  obtain ⟨observation⟩ := skeleton.source henv hscoped hle hTarget lookup notDefinition
    registered levelsWF typeClosed formation (earlier formation).leftFormation
    rootCode root.typed locals σ
  exact root.path.observe observation (by intro _ _ h; cases h)

end Lean4Lean.AnchoredSource.Adapted
