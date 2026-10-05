import Lean4Lean.Theory.Typing.AnchoredConstantHeaders
import Lean4Lean.Theory.Typing.InductiveDeclarationStages
import Lean4Lean.Theory.Typing.DefinitionStageSelection

/-! Concrete header-bank assembly at the original declaration phases.
Each input theorem is for the preceding original formation environment;
the new bank contains no theorem for an installed equation.
-/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private addConsts_as_values from Lean4Lean.Theory.Typing.NativeConstructorRigidity

namespace OriginalConstantHeaders
variable {base installed env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}

/-- Family types, constructor types, and recursor types were checked at
three different original stages. Retain those exact stages independently. -/
theorem inductiveRecursors
    (stages : VInductBlock.TypingStages base block installed)
    (formed : base.Ordered)
    (headers : OriginalConstantHeaders base env U registry)
    {baseControl typesControl projectionsControl : Name → Bool}
    (baseEarlier : ∀ fuel, ∀ {Γ l r A}, base.IsDefEqStrong U Γ l r A →
      Joint baseControl fuel env U registry Γ l r A)
    (typesEarlier : ∀ fuel, ∀ {Γ l r A}, stages.types.IsDefEqStrong U Γ l r A →
      Joint typesControl fuel env U registry Γ l r A)
    (projectionsEarlier : ∀ fuel, ∀ {Γ l r A},
      (stages.constructors.addProjections block.projections).IsDefEqStrong U Γ l r A →
      Joint projectionsControl fuel env U registry Γ l r A) :
    OriginalConstantHeaders stages.recursors env U registry := by
  have types := headers.addConstVals formed stages.originalTypes stages.addTypes baseEarlier
  have constructors := types.addConstVals stages.typesWF.ordered stages.originalConstructors
    stages.addConstructors typesEarlier
  have projections := constructors.extend (extended := stages.constructors.addProjections block.projections) VEnv.addProjections_le
    (VEnv.addProjections_constants ..)
  exact projections.addConstVals stages.projectionsWF.ordered stages.originalRecursors
    stages.addRecursors projectionsEarlier

/-- Mutual definition headers all retain their common pre-header formation
environment; their bodies remain the separate current-header induction. -/
theorem definition
    (stage : DefinitionTypingStage base declaration installed representative)
    (formed : base.WF)
    (headers : OriginalConstantHeaders base env U registry)
    {control : Name → Bool}
    (earlier : ∀ fuel, ∀ {Γ l r A}, base.IsDefEqStrong U Γ l r A →
      Joint control fuel env U registry Γ l r A) :
    OriginalConstantHeaders stage.header env U registry := by
  apply headers.addConstVals formed.ordered (values := stage.values.map VDefVal.toVConstVal)
    (installed := addConsts_as_values ▸ stage.headers) (earlier := earlier)
  intro entry member
  obtain ⟨value, inValues, rfl⟩ := List.mem_map.mp member
  exact (stage.select inValues).type formed

end OriginalConstantHeaders
end Lean4Lean.AnchoredSource.Adapted.Staged
