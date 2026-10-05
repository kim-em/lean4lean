import Lean4Lean.Theory.Typing.AnchoredDefinitionReplay
import Lean4Lean.Theory.Typing.AnchoredNativeIndependentControl

/-! A definition packet retains its original finite body and declared-type
certificate. Evaluation uses the actual declaration header, at its own fuel;
the same returned source witnesses preserve every caller's depth budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.Budgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private levelsTrans from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
set_option backward.isDefEq.respectTransparency false

theorem Obs.deltaTransfer
    {control : Name → Bool} {fuel : Nat} {budgets : Budgets}
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {declarations : List VDecl} {value : VDefVal}
    (origin : DefinitionDeclarationOrigin env declarations value)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ {Γ l r A}, origin.stage.header.IsDefEqStrong U Γ l r A →
      Staged.Joint control fuel env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {seedLevels levels levels' : List VLevel}
    (lookup : registry.definitions name = some value)
    (nameEq : value.name = name) (registered : DefinitionRegistered env value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = value.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
    {atom : Atom n} {support : Profile n} {typeRealization bodyRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (typed : (Profile.singleton atom).HasType support)
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) [])
    (bodyBound : body.nativeDepth control ≤ fuel)
    (certificateBound : certificate.nativeDepth control ≤ fuel)
    (observationBound : Within budgets (fun filter =>
      max (body.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0)) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (value.type.instL levels) (.singleton atom)) := by
  subst name
  obtain ⟨seedCode, seedRelated⟩ := Staged.definitionSupported origin henv hscoped earlier hTarget
    lookup seedWF seedLength body certificate typed bodyBound certificateBound
  have seedRight := levelsTrans equivalent rightEquivalent
  have seedSelf : List.Forall₂ (· ≈ ·) seedLevels seedLevels :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)
  have typeSelf := EqUpToLevels.instL_expr value.type seedWF seedWF seedSelf
  have typeLeft := EqUpToLevels.instL_expr value.type seedWF levelsWF equivalent
  have code := seedCode.levels henv typeLeft typeLeft
  have conversion := seedCode.levels henv typeSelf typeLeft
  have related := (seedRelated.levels henv (.const seedWF levelsWF equivalent)
    (.const seedWF rightWF seedRight)).convert henv typed conversion
  have rawRelated := (seedRelated.levels henv (.const seedWF rightWF seedRight)
    (.const seedWF rightWF seedRight)).convert henv typed conversion
  obtain ⟨_, typeFormation⟩ := origin.typeInstance seedWF
  have formed : env.IsType U target (value.type.instL seedLevels) :=
    ⟨_, (typeFormation.defeq.mono ((VEnv.addConsts_le origin.stage.headers).trans origin.header_le)).hasType.1.weak0 henv⟩
  obtain ⟨actualCertificate, certificateDepth⟩ :=
    (certificate.closedSource typeClosed.instL locals σ).instLevelsAllDepth
      henv hTarget typeClosed seedWF levelsWF equivalent formed
  exact ⟨{
    rank := n
    bound := Nat.le_refl n
    rawDemand := .singleton atom
    resultFootprint := []
    observation := .delta lookup rfl registered seedWF seedLength rightWF seedRight
      bodyClosed typeClosed certificate typed body
    adapter := by simpa only [raiseProfile_self] using
      (show NormalProfileAdapter env U registry target (.singleton atom) (.singleton atom) from .refl _)
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

/-- An earlier declaration is interpreted at its own original header. Its
finite packet chooses the local fuel, independently of all caller budgets. -/
theorem Obs.deltaAtOrigin
    {budgets : Budgets} {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {declarations : List VDecl} {value : VDefVal}
    (origin : DefinitionDeclarationOrigin env declarations value)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ fuel, ∀ {Γ l r A}, origin.stage.header.IsDefEqStrong U Γ l r A →
      Staged.Joint origin.current fuel env U registry Γ l r A)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {seedLevels levels levels' : List VLevel}
    (lookup : registry.definitions name = some value)
    (nameEq : value.name = name) (registered : DefinitionRegistered env value)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = value.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (bodyClosed : value.value.Closed) (typeClosed : value.type.Closed)
    {atom : Atom n} {support : Profile n} {typeRealization bodyRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (value.type.instL seedLevels) support [])
    (typed : (Profile.singleton atom).HasType support)
    (body : Obs env U registry target [] bodyRealization
      (value.value.instL seedLevels) (.singleton atom) [])
    (observationBound : Within budgets (fun filter =>
      max (body.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0)) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (value.type.instL levels) (.singleton atom)) := by
  exact Obs.deltaTransfer origin henv hscoped (earlier
    (max (body.nativeDepth origin.current) (certificate.nativeDepth origin.current))) hTarget
    lookup nameEq registered seedWF seedLength levelsWF rightWF equivalent rightEquivalent
    bodyClosed typeClosed certificate typed body (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    observationBound

end Lean4Lean.AnchoredSource.Adapted.Budgeted
