import Lean4Lean.Theory.Typing.AnchoredDataAnchors
import Lean4Lean.Theory.Typing.AnchoredDataValueLaws

/-! Constructor witnesses compose through fixed argument anchors after
amalgamating their actual private worlds. No equality of the two displayed
middle constructors, their universe packets, or their parameters is used. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

theorem ConstructorWitness.joinAnchors
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry} {lower : Relations n}
    (henv : env.Ordered) (laws : LowerEquality env U registry lower)
    (first : ConstructorWitness env U registry lower Γ left firstRight type demand)
    (second : ConstructorWitness env U registry lower Γ secondLeft right type demand) :
    Nonempty (ConstructorWitness env U registry lower Γ left right type demand) := by
  obtain ⟨Ω, i, j, firstLeg, secondLeg, maps⟩ := MixedInsertion.amalgam henv
    first.leftExposure.baseWF
    (first.leftExposure.insertion henv) (second.leftExposure.insertion henv)
  obtain ⟨before, context₁, map₁, _, _⟩ :=
    first.transportDisplay henv laws.toLowerTransport firstLeg
  obtain ⟨after, context₂, map₂, _, _⟩ :=
    second.transportDisplay henv laws.toLowerTransport secondLeg
  have contexts : before.context = after.context := context₁.trans context₂.symm
  have commonMap : before.map = after.map := map₁.trans (maps.trans map₂.symm)
  have later := after.arguments
  rw [← contexts, ← commonMap] at later
  exact ⟨{ before with
    rightLevels := after.rightLevels
    rightArguments := after.rightArguments
    rightExposure := by simpa only [contexts, commonMap] using after.rightExposure
    rightTerminal := after.rightTerminal
    rightUniverses := after.rightUniverses
    arguments := before.arguments.joinAnchors laws (before.registryScoped henv) later
    rightHeader := after.rightHeader
    rightBridge := by simpa only [contexts, commonMap] using after.rightBridge }⟩

end Lean4Lean.AnchoredSemantics.RankedData
