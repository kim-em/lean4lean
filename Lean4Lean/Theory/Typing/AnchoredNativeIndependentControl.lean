import Lean4Lean.Theory.Typing.AnchoredBoundedNativeObservationTransfer
import Lean4Lean.Theory.Typing.AnchoredStageBudgets
import Lean4Lean.Theory.Typing.AnchoredUniformLevels

/-! Native evaluation uses its own declaration-local control filter, while
its actual returned observer and certificate preserve ALL caller budgets.
Intermediate certificates from evaluation are used only for target semantics;
they are not substituted for the source packet's retained header child. -/
namespace Lean4Lean.AnchoredSource.Adapted.Budgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
open private levelsTrans from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
set_option backward.isDefEq.respectTransparency false

/-- The native branch of constant transfer, including its actual output
observation and source-type certificate. The original header and equation
derivations are the only declaration-stage inputs. -/
theorem Obs.nativeTransfer
    {control : Name → Bool} {fuel : Nat} {budgets : Budgets}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Staged.Joint control fuel env U registry Γ l r A)
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
    (planBound : plan.nativeDepth control ≤ fuel)
    (certificateBound : certificate.nativeDepth control ≤ fuel)
    (observationBound : Within budgets (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0)) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (signature.type.instL levels) demand) := by
  subst name
  have seedCode := certificate.closedTypeCodeBounded henv hscoped hTarget typeClosed.instL
    (earlier typeFormation) certificateBound
  have seedRelated := Staged.NativePlan.bareSupported henv hscoped hsource hle earlier registered lookup
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
  obtain ⟨actualCertificate, certificateDepth⟩ := (certificate.closedSource typeClosed.instL locals σ).instLevelsAllDepth
    henv hTarget typeClosed seedWF levelsWF equivalent formed
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
    observationBound := by
      intro filter limit member
      simpa only [Obs.nativeDepth] using observationBound filter limit member
    certificateBound := by
      intro filter limit member
      change actualCertificate.nativeDepth filter ≤ limit
      rw [certificateDepth filter, CodeCert.nativeDepth_closedSource]
      exact Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (observationBound filter limit member)) }⟩

/-- An old declaration's completed header theorem is used with its OWN
control filter. The finite original packet fixes the required local fuel;
caller budgets are preserved without being passed through RHS interpretation. -/
theorem Obs.nativeFromPrevious
    {control : Name → Bool} {budgets : Budgets}
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hsource : sourceEnv.Ordered)
    (hle : sourceEnv ≤ env)
    (earlier : ∀ fuel, ∀ {Γ l r A}, sourceEnv.IsDefEqStrong U Γ l r A →
      Staged.Joint control fuel env U registry Γ l r A)
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
    (observationBound : Within budgets (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0)) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (signature.type.instL levels) demand) := by
  let localFuel := max (plan.nativeDepth control) (certificate.nativeDepth control)
  exact Obs.nativeTransfer henv hscoped hsource hle (earlier localFuel) hTarget
    lookup notDefinition nameEq registered seedWF levelsWF rightWF equivalent rightEquivalent
    signature typeClosed typeFormation equations certificate typed plan
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) observationBound

end Lean4Lean.AnchoredSource.Adapted.Budgeted
