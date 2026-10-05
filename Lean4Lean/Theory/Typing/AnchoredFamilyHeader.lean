import Lean4Lean.Theory.Typing.AnchoredConstantHeaders
import Lean4Lean.Theory.Typing.AnchoredFamilyIndependentControl

/-! Family transfer at an original header uses the actual stored formation
stage, completed earlier in declaration induction. Its output retains the
caller's control and finite observer bound.
-/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
set_option backward.isDefEq.respectTransparency false

theorem Obs.familyAtHeader
    {source env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : source ≤ env)
    (headers : OriginalConstantHeaders source env U registry)
    {control : Name → Bool} {fuel : Nat}
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {info : VConstant} {name : Name} {seedLevels levels levels' : List VLevel}
    (constant : source.constants name = some info)
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
    {demand support : Profile n} {typeRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (info.type.instL seedLevels) support [])
    (typed : demand.HasType support)
    (plan : Adapted.FamilyPlan env U registry target name seedLevels signature [] demand [])
    (bound : max (plan.nativeDepth control) (certificate.nativeDepth control) ≤ fuel) :
    Nonempty (Result control fuel env U registry target locals σ τ available
      (.const name levels) (.const name levels') (info.type.instL levels) demand) := by
  obtain ⟨origin, priorControl, earlier⟩ := headers name info constant
  obtain ⟨typeLevel, original⟩ := origin.typeInstance seedWF
  have budget : Budgeted.Within [(control, fuel)] (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter)) := by
    intro filter limit member
    cases List.mem_singleton.mp member
    exact bound
  obtain ⟨result⟩ := Budgeted.Obs.familyFromPrevious henv hscoped origin.ordered
    (origin.sourceBelow.trans below) earlier hTarget (below.constants constant)
    notDefinition notNative notQuotient seedLength seedWF levelsWF rightWF equivalent
    rightEquivalent signature typeClosed original certificate typed plan budget
  exact ⟨result.toStaged (List.mem_singleton_self _)⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
