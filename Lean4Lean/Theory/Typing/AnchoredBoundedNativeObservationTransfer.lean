import Lean4Lean.Theory.Typing.AnchoredBoundedNativePlanInterpretation
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture
import Lean4Lean.Theory.Typing.AnchoredBoundedLevels
import Lean4Lean.Theory.Typing.AnchoredLevels

/-! The actual native source constructor has a checked transfer result.
Its finite registered-type certificate and plan are interpreted from original
declaration proofs. Equivalent universe packets retain the same demand,
support, and empty footprint. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private telescope_eq from Lean4Lean.Theory.Inductive.NativeCommonPrefix
open private levelsTrans from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
set_option backward.isDefEq.respectTransparency false

theorem NativePlan.bareSupported
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Joint current fuel env U registry Γ l r A)
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
      Nonempty (NativeOriginalEquation sourceEnv U levels equation))
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {demand support : Profile n}
    (typed : demand.HasType support)
    (code : TypeRelated env U registry target (signature.type.instL levels)
      (signature.type.instL levels) support)
    (plan : Adapted.NativePlan env U registry target signature [] demand [])
    (planBound : plan.nativeDepth current ≤ fuel) :
    Related env U registry target (.const data.name levels) (.const data.name levels)
      (signature.type.instL levels) demand support := by
  have residual :
      (wrapForalls (signature.domains.drop (0 : Nat)) signature.result).subst
        (nativeCaptureSubst []) = signature.type.instL levels := by
    rw [List.drop_zero, ← telescope_eq signature.telescope]
    exact typeClosed.instL.subst_eq .zero
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
  have fits : PairedFits current fuel env U registry [] target []
      (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) := by
    constructor <;> constructor <;> intro _ _ _ _ lookup <;> cases lookup
  have result := NativePlan.supported henv hscoped hsource hle earlier registered lookup
    notDefinition levelsWF typeClosed typeFormation equations (newValues := [])
    (available := fun _ => []) plan planBound hTarget (Nat.zero_le _) rfl emptyClosed .nil fits
    (by intro _ _ h; cases h) typed (by simpa only [List.length_nil, residual] using code)
  simpa only [mkApps, List.foldl_nil, List.length_nil, residual] using result

/-- The native branch of constant transfer, including its actual output
observation and source-type certificate. The original header and equation
derivations are the only declaration-stage inputs. -/
theorem Obs.nativeTransfer
    {current : Name → Bool} {fuel outputFuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Joint current fuel env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {data : NativeRecursorData} {name : Name} {seedLevels levels levels' : List VLevel}
    (lookup : registry.natives name = some data)
    (notDefinition : registry.definitions name = none)
    (nameEq : data.name = name) (registered : NativeRecursorRegistered env data)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (signature : NativeConstantSignature data seedLevels)
    (typeClosed : signature.type.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (signature.type.instL seedLevels)
      (signature.type.instL seedLevels) (.sort typeLevel))
    (equations : ∀ equation, data.singletonEquation = some equation →
      Nonempty (NativeOriginalEquation sourceEnv U seedLevels equation))
    {demand support : Profile n} {typeRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (signature.type.instL seedLevels) support [])
    (typed : demand.HasType support)
    (plan : Adapted.NativePlan env U registry target signature [] demand [])
    (planBound : plan.nativeDepth current ≤ fuel)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (observationBound : max (plan.nativeDepth current) (certificate.nativeDepth current) +
      (if current name then 1 else 0) ≤ outputFuel) :
    Nonempty (Result current outputFuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (signature.type.instL levels) demand) := by
  subst name
  have seedCode := certificate.closedTypeCodeBounded henv hscoped hTarget typeClosed.instL
    (earlier typeFormation) certificateBound
  have seedRelated := NativePlan.bareSupported henv hscoped hsource hle earlier registered lookup
    notDefinition seedWF typeClosed typeFormation equations hTarget typed seedCode plan planBound
  have seedRight := levelsTrans equivalent rightEquivalent
  have seedSelf : List.Forall₂ (· ≈ ·) seedLevels seedLevels :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)
  have typeSelf := EqUpToLevels.instL_expr signature.type seedWF seedWF seedSelf
  have typeLeft := EqUpToLevels.instL_expr signature.type seedWF levelsWF equivalent
  have code := seedCode.levels henv typeLeft typeLeft
  have conversion := seedCode.levels henv typeSelf typeLeft
  have related := (seedRelated.levels henv (.const seedWF levelsWF equivalent)
    (.const seedWF rightWF seedRight)).convert henv typed conversion
  have rawRelated := (seedRelated.levels henv (.const seedWF rightWF seedRight)
    (.const seedWF rightWF seedRight)).convert henv typed conversion
  have formed : env.IsType U target (signature.type.instL seedLevels) :=
    ⟨_, (typeFormation.defeq.mono hle).hasType.1.weak0 henv⟩
  obtain ⟨actualCertificate, certificateDepth⟩ := (certificate.closedSource typeClosed.instL locals σ).instLevelsDepth
    current henv hTarget typeClosed seedWF levelsWF equivalent formed
  exact ⟨{
    rank := n
    bound := Nat.le_refl n
    rawDemand := demand
    resultFootprint := []
    observation := .native lookup notDefinition rfl registered seedWF rightWF seedRight
      signature typeClosed certificate typed plan
    adapter := by simpa only [raiseProfile_self] using (show NormalProfileAdapter env U registry target demand demand from .refl _)
    resultAvailable := by intro _ _ h; cases h
    support := support
    typeFootprint := []
    certificate := actualCertificate
    typeAvailable := by intro _ _ h; cases h
    typed := by simpa only [raiseProfile_self] using typed
    rawTyped := typed
    typeCode := by simpa only [typeClosed.instL.subst_eq (σ := σ) .zero] using code
    related := by simpa only [subst, typeClosed.instL.subst_eq (σ := σ) .zero,
      raiseProfile_self] using related
    rawRelated := by simpa only [subst, typeClosed.instL.subst_eq (σ := σ) .zero] using rawRelated
    observationBound := by simpa only [Obs.nativeDepth] using observationBound
    certificateBound := by
      rw [certificateDepth, CodeCert.nativeDepth_closedSource]
      exact Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) observationBound) }⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
