import Lean4Lean.Theory.Typing.AnchoredBoundedFamilyObservationTransfer
import Lean4Lean.Theory.Typing.AnchoredStageBudgets
import Lean4Lean.Theory.Typing.AnchoredUniformLevels

/-! Family heads preserve every caller budget. Their bounded interpreter
uses the declaration's own filter, while returned source children remain
the exact retained plan and header certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted.Budgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open private levelsTrans from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
set_option backward.isDefEq.respectTransparency false

/-- Family constant transfer consumes its actual declaration header and the
strict declaration-predecessor theorem. No semantic leaf supplier is assumed. -/
theorem Obs.familyTransfer
    {control : Name → Bool} {fuel : Nat} {budgets : Budgets}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Staged.Joint control fuel env U registry Γ l r A)
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
    (planBound : plan.nativeDepth control ≤ fuel)
    (certificateBound : certificate.nativeDepth control ≤ fuel)
    (observationBound : Within budgets (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter))) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (info.type.instL levels) demand) := by
  have seedCode := certificate.closedTypeCodeBounded henv hscoped hTarget typeClosed.instL
    (earlier typeFormation) certificateBound
  have seedRelated := Staged.FamilyPlan.bareSupported henv hscoped hsource hle earlier lookup
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
  obtain ⟨actualCertificate, certificateDepth⟩ := (certificate.closedSource typeClosed.instL locals σ).instLevelsAllDepth
    henv hTarget typeClosed seedWF levelsWF equivalent formed
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
    observationBound := by
      intro filter limit member
      simpa only [Obs.nativeDepth] using observationBound filter limit member
    certificateBound := by
      intro filter limit member
      change actualCertificate.nativeDepth filter ≤ limit
      rw [certificateDepth filter, CodeCert.nativeDepth_closedSource]
      exact Nat.le_trans (Nat.le_max_right _ _) (observationBound filter limit member) }⟩


/-- The original packet fixes finite local control fuel without changing
any returned observer, certificate, or caller budget. -/
theorem Obs.familyFromPrevious
    {control : Name → Bool} {budgets : Budgets}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ fuel, ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Staged.Joint control fuel env U registry Γ l r A)
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
    (observationBound : Within budgets (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter))) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (info.type.instL levels) demand) := by
  let localFuel := max (plan.nativeDepth control) (certificate.nativeDepth control)
  exact Obs.familyTransfer henv hscoped hsource hle (earlier localFuel) hTarget
    lookup notDefinition notNative notQuotient seedLength seedWF levelsWF rightWF equivalent
    rightEquivalent signature typeClosed typeFormation certificate typed plan
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) observationBound

end Lean4Lean.AnchoredSource.Adapted.Budgeted
