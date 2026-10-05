import Lean4Lean.Theory.Typing.AnchoredOriginalDefinitionEndpoint
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstSiteProducer

/-! The actual definition origin supplies a finite closed constant original
whose displayed universes are the caller's and whose assigned universes are
the delta query's retained seed. This original is paid by the query-owned
reserve; it is not asserted to be a descendant of the caller's derivation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure OriginalRecordSource
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The universe equality is built from the retained earlier type formation,
then moved to its actual mutual header. No typing or equality result from the
pending caller interpretation is used. -/
theorem DefinitionDeclarationOrigin.displayedConstant
    {env : VEnv} {declarations : List VDecl} {value : VDefVal}
    (origin : DefinitionDeclarationOrigin env declarations value)
    {U : Nat} {seedLevels levels : List VLevel}
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (seedLength : seedLevels.length = value.uvars)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels) :
    Nonempty (ClosedPrimitiveConstant origin.stage.header U value.name levels
      (value.type.instL seedLevels)) := by
  obtain ⟨level, formed⟩ := origin.typeInstance seedWF
  have headerType := formed.mono (VEnv.addConsts_le origin.stage.headers)
  have universeEquality := EqUpToLevels.defeq origin.headerWF.ordered
    origin.headerWF.ordered.strong (by trivial) headerType
    (EqUpToLevels.refl (by trivial) headerType).1
    (EqUpToLevels.instL_expr value.type seedWF levelsWF equivalent)
  obtain ⟨original⟩ := Derivation.reify universeEquality
  have levelWF : level.WF U := by
    exact (headerType.defeq.levelWF (by trivial)).2.2
  have lookup : origin.stage.header.constants value.name = some value.toVConstant :=
    VEnv.addConsts_constants origin.stage.headers value origin.stage.member
  exact ⟨{
    info := value.toVConstant
    lookup := lookup
    assignedLevels := seedLevels
    assignedWF := seedWF
    levelsWF := levelsWF
    equivalent := equivalent
    assignedEq := rfl
    site := .right (.constDF lookup seedWF levelsWF seedLength equivalent levelWF original original) }⟩

end Lean4Lean.AnchoredSource.Adapted
