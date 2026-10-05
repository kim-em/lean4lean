import Lean4Lean.Theory.Typing.AnchoredBoundedFamilyPlanInterpretation
import Lean4Lean.Theory.Typing.AnchoredBoundedNativeFuture
import Lean4Lean.Theory.Typing.AnchoredBoundedLevels
import Lean4Lean.Theory.Typing.AnchoredClosedTypeCertificate
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceLevels
import Lean4Lean.Theory.Typing.AnchoredLevels

/-! The actual family constant constructor transfers its finite telescope
plan and original header certificate. Equivalent universe packets preserve
the frozen requests and the empty external footprint. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private levelsTrans from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
set_option backward.isDefEq.respectTransparency false

theorem FamilyPlan.bareSupported
    {current : Name → Bool} {fuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Joint current fuel env U registry Γ l r A)
    {info : VConstant} {name : Name} {levels : List VLevel}
    {signature : ConstantTelescope (info.type.instL levels)}
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (levelLength : levels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (typeClosed : info.type.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (info.type.instL levels)
      (info.type.instL levels) (.sort typeLevel))
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {demand support : Profile n}
    (typed : demand.HasType support)
    (code : TypeRelated env U registry target (info.type.instL levels)
      (info.type.instL levels) support)
    (plan : Adapted.FamilyPlan env U registry target name levels signature [] demand [])
    (planBound : plan.nativeDepth current ≤ fuel) :
    Related env U registry target (.const name levels) (.const name levels)
      (info.type.instL levels) demand support := by
  have residual :
      (wrapForalls (signature.domains.drop (0 : Nat)) signature.result).subst
        (nativeCaptureSubst []) = info.type.instL levels := by
    rw [List.drop_zero, ← signature.type_eq]
    exact typeClosed.instL.subst_eq .zero
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ h; cases h
  have fits : PairedFits current fuel env U registry [] target []
      (nativeCaptureSubst []) (nativeCaptureSubst []) (fun _ => []) := by
    constructor <;> constructor <;> intro _ _ _ _ lookup <;> cases lookup
  have result := FamilyPlan.supported henv hscoped hsource hle earlier
    (.const lookup levelsWF levelLength) notDefinition notNative notQuotient
    typeClosed.instL typeFormation (newValues := [])
    (available := fun _ => []) plan planBound hTarget (Nat.zero_le _) rfl emptyClosed .nil fits
    (by intro _ _ h; cases h) typed (by simpa only [List.length_nil, residual] using code)
  simpa only [mkApps, List.foldl_nil, List.length_nil, residual] using result

/-- Family constant transfer consumes its actual declaration header and the
strict declaration-predecessor theorem. No semantic leaf supplier is assumed. -/
theorem Obs.familyTransfer
    {current : Name → Bool} {fuel outputFuel : Nat}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Joint current fuel env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {seedLevels levels levels' : List VLevel}
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (seedLength : seedLevels.length = info.uvars)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (signature : ConstantTelescope (info.type.instL seedLevels))
    (typeClosed : info.type.Closed)
    (typeFormation : sourceEnv.IsDefEqStrong U [] (info.type.instL seedLevels)
      (info.type.instL seedLevels) (.sort typeLevel))
    {demand support : Profile n} {typeRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (info.type.instL seedLevels) support [])
    (typed : demand.HasType support)
    (plan : Adapted.FamilyPlan env U registry target name seedLevels signature [] demand [])
    (planBound : plan.nativeDepth current ≤ fuel)
    (certificateBound : certificate.nativeDepth current ≤ fuel)
    (observationBound : max (plan.nativeDepth current) (certificate.nativeDepth current) ≤ outputFuel) :
    Nonempty (Result current outputFuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (info.type.instL levels) demand) := by
  have seedCode := certificate.closedTypeCodeBounded henv hscoped hTarget typeClosed.instL
    (earlier typeFormation) certificateBound
  have seedRelated := FamilyPlan.bareSupported henv hscoped hsource hle earlier lookup
    notDefinition notNative notQuotient seedLength seedWF typeClosed typeFormation hTarget typed seedCode plan planBound
  have seedRight := levelsTrans equivalent rightEquivalent
  have seedSelf : List.Forall₂ (· ≈ ·) seedLevels seedLevels :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)
  have typeSelf := EqUpToLevels.instL_expr info.type seedWF seedWF seedSelf
  have typeLeft := EqUpToLevels.instL_expr info.type seedWF levelsWF equivalent
  have code := seedCode.levels henv typeLeft typeLeft
  have conversion := seedCode.levels henv typeSelf typeLeft
  have related := (seedRelated.levels henv (.const seedWF levelsWF equivalent)
    (.const seedWF rightWF seedRight)).convert henv typed conversion
  have rawRelated := (seedRelated.levels henv (.const seedWF rightWF seedRight)
    (.const seedWF rightWF seedRight)).convert henv typed conversion
  have formed : env.IsType U target (info.type.instL seedLevels) :=
    ⟨_, (typeFormation.defeq.mono hle).hasType.1.weak0 henv⟩
  obtain ⟨actualCertificate, certificateDepth⟩ := (certificate.closedSource typeClosed.instL locals σ).instLevelsDepth
    current henv hTarget typeClosed seedWF levelsWF equivalent formed
  exact ⟨{
    rank := n
    bound := Nat.le_refl n
    rawDemand := demand
    resultFootprint := []
    observation := .family lookup notDefinition notNative notQuotient seedWF seedLength rightWF seedRight
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
      exact Nat.le_trans (Nat.le_max_right _ _) observationBound }⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
