import Lean4Lean.Theory.Typing.AnchoredDataRelations

/-! Left diagonals of the finite data clauses use only left diagonals at the
preceding rank. All private displays and original declaration evidence are
retained literally. -/

namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles

variable {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
  {lower : Relations n} {Γ : List VExpr}

private theorem admission_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (admitted : RequestAdmission env U lower Γ key left right) :
    RequestAdmission env U lower Γ key left left := by
  obtain ⟨anchor, pair, inputTyped, supportTyped, code, anchorRelated, pairRelated⟩ := admitted
  exact ⟨anchor, pair.hasType.1, inputTyped, supportTyped, code, anchorRelated,
    diagonal _ _ _ _ _ _ pairRelated⟩

theorem Arguments.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (arguments : Arguments env U lower Γ keys left right) :
    Arguments env U lower Γ keys left left := by
  induction arguments with
  | nil => exact .nil
  | cons admitted _ ih => exact .cons (admission_diagonal diagonal admitted) ih

def FamilyWitness.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (witness : FamilyWitness env U registry lower Γ left right demand) :
    FamilyWitness env U registry lower Γ left left demand :=
  { witness with
    rightLevel := witness.leftLevel
    rightRelevance := witness.leftRelevance
    path := .refl
    rightType := witness.leftType
    rightLevels := witness.leftLevels
    rightArguments := witness.leftArguments
    rightExposure := witness.leftExposure
    rightTerminal := witness.leftTerminal
    rightUniverses := witness.leftUniverses
    arguments := witness.arguments.left_diagonal diagonal }

theorem FamilyRelation.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (relation : FamilyRelation env U registry lower Γ left right demand) :
    FamilyRelation env U registry lower Γ left left demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := relation Δ ρ future
  exact ⟨witness.left_diagonal diagonal⟩

def ConstructorWitness.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (witness : ConstructorWitness env U registry lower Γ left right type demand) :
    ConstructorWitness env U registry lower Γ left left type demand :=
  { witness with
    rightLevels := witness.leftLevels
    rightArguments := witness.leftArguments
    rightExposure := witness.leftExposure
    rightTerminal := witness.leftTerminal
    rightUniverses := witness.leftUniverses
    arguments := witness.arguments.left_diagonal diagonal
    rightHeader := witness.leftHeader
    rightBridge := witness.leftBridge }

def RecordWitness.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (witness : RecordWitness env U registry lower Γ left right type demand) :
    RecordWitness env U registry lower Γ left left type demand :=
  { witness with
    rightType := witness.leftType
    rightOrigins := witness.leftOrigins
    fields := witness.fields.left_diagonal diagonal }

theorem ConstructorRelation.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (relation : ConstructorRelation env U registry lower Γ left right type demand) :
    ConstructorRelation env U registry lower Γ left left type demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := relation Δ ρ future
  exact ⟨witness.left_diagonal diagonal⟩

theorem RecordRelation.left_diagonal
    (diagonal : ∀ Γ left right type value support,
      lower.term Γ left right type value support →
      lower.term Γ left left type value support)
    (relation : RecordRelation env U registry lower Γ left right type demand) :
    RecordRelation env U registry lower Γ left left type demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := relation Δ ρ future
  exact ⟨witness.left_diagonal diagonal⟩

end Lean4Lean.AnchoredSemantics.RankedData
