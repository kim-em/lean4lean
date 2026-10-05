import Lean4Lean.Theory.Typing.AnchoredDataRelations
import Lean4Lean.Theory.Typing.AnchoredValueDataEligibility

/-! A meaningful existing record witness contains enough actual declaration
evidence for data eligibility; registry completeness is not required. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles

/-- Select the original projection origin belonging to a nonempty field.
Its environment registration and the witness's existing bound supply the
whole record eligibility guard. -/
theorem RecordWitness.valueDataEligible
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    {lower : Relations n} {Γ : List VExpr} {left right type : VExpr}
    {demand : RecordData (Profile n)}
    (witness : RecordWitness env U registry lower Γ left right type demand)
    (meaningful : ∃ entry ∈ demand.fields, Profile.Nonempty entry.2.input) :
    ValueDataEligible env (n := n + 1) (.record demand) := by
  obtain ⟨entry, member, nonempty⟩ := meaningful
  obtain ⟨origin⟩ := witness.leftOrigins entry member
  exact ⟨witness.info, origin.registered, entry, member, witness.bounded entry member, nonempty⟩

end Lean4Lean.AnchoredSemantics.RankedData
