import Lean4Lean.Theory.Typing.NativeDeclarationProvenance
import Lean4Lean.Theory.Typing.AnchoredNativeIndependentControl

/-! The native stage call consumes the original header recovered by concrete
registry construction.  All instantiated header and equation proof roots are
produced here from that packet; none is supplied by a final-environment lookup
or by a newly invented semantic induction hypothesis. -/
namespace Lean4Lean.VEnv.NativeDeclarationOrigin
open VExpr InductiveSignature NativeRecursorData AnchoredSource.Adapted
variable {levels : List VLevel} {equation : VDefEq}

theorem singletonOriginal
    (origin : NativeDeclarationOrigin env declarations data)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (selected : data.singletonEquation = some equation) :
    Nonempty (NativeOriginalEquation origin.stage.typing.recursors U levels equation) := by
  have hsource := origin.stage.typing.recursorsWF.ordered
  have pair := origin.singletonStrong selected
  have left := pair.1.instL levelsWF
  have right := pair.2.instL levelsWF
  obtain ⟨level, formation⟩ := right.isType' hsource hsource.strong (by trivial)
  exact ⟨{
    leftStructural := true
    rightStructural := true
    level := level
    left := left.hasType'.1
    right := right.hasType'.1
    formation := formation }⟩

theorem signatureFormation
    (origin : NativeDeclarationOrigin env declarations data)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (signature : NativeConstantSignature data levels) :
    ∃ level, origin.stage.typing.recursors.IsDefEqStrong U []
      (signature.type.instL levels) (signature.type.instL levels) (.sort level) := by
  obtain ⟨level, original⟩ := origin.typeStrong signature.typeOrigin
  exact ⟨level.inst levels, original.instL levelsWF⟩

end Lean4Lean.VEnv.NativeDeclarationOrigin

namespace Lean4Lean.AnchoredSource.Adapted.Budgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- The actual old-native recursive call, after obtaining a registry origin.
The premise is the ordinary earlier HEADER theorem at all finite local fuels.
Its source environment and control filter are forced by that original packet.
The caller budgets need not be passed through this earlier semantic work. -/
theorem Obs.nativeAtOrigin
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {declarations : List VDecl} {data : NativeRecursorData}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (earlier : ∀ fuel, ∀ {Γ l r A}, origin.stage.typing.recursors.IsDefEqStrong U Γ l r A →
      Staged.Joint origin.current fuel env U registry Γ l r A)
    {budgets : Budgets} {target : List VExpr}
    (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {name : Name} {seedLevels levels levels' : List VLevel}
    (lookup : registry.natives name = some data)
    (notDefinition : registry.definitions name = none)
    (nameEq : data.name = name)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (rightWF : ∀ level ∈ levels', level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (rightEquivalent : List.Forall₂ (· ≈ ·) levels levels')
    (signature : NativeConstantSignature data seedLevels)
    (typeClosed : signature.type.Closed)
    {demand support : Profile n} {typeRealization : Subst}
    (certificate : CodeCert env U registry target [] typeRealization
      (signature.type.instL seedLevels) support [])
    (typed : demand.HasType support)
    (plan : Adapted.NativePlan env U registry target signature [] demand [])
    (observationBound : Within budgets (fun filter =>
      max (plan.nativeDepth filter) (certificate.nativeDepth filter) + if filter name then 1 else 0)) :
    Nonempty (Result budgets env U registry target locals σ τ available
      (.const name levels) (.const name levels') (signature.type.instL levels) demand) := by
  obtain ⟨typeLevel, typeFormation⟩ := origin.signatureFormation seedWF signature
  exact Obs.nativeFromPrevious henv hscoped origin.stage.typing.recursorsWF.ordered
    (origin.stage.typing.recursors_le.trans origin.stage.installedBelow) earlier hTarget
    lookup notDefinition nameEq origin.registered seedWF levelsWF rightWF
    equivalent rightEquivalent signature typeClosed typeFormation
    (fun _ selected => origin.singletonOriginal seedWF selected)
    certificate typed plan observationBound

end Lean4Lean.AnchoredSource.Adapted.Budgeted
