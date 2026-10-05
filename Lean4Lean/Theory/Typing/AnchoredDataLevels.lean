import Lean4Lean.Theory.Typing.AnchoredDataExposureLevels
import Lean4Lean.Theory.Typing.AnchoredConstructorDisplayLevels
import Lean4Lean.Theory.Typing.AnchoredDataValueLaws

/-! Fixed data descriptors admit level-equivalent endpoints. The proof uses
only lower-rank endpoint congruence, keeping every frozen argument request. -/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false
variable {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry} {lower : Relations n}

def LowerLevels (U : Nat) (lower : Relations n) : Prop :=
  ∀ {Γ left right left' right' type value support}, EqUpToLevels U left left' →
    EqUpToLevels U right right' → lower.term Γ left right type value support →
      lower.term Γ left' right' type value support

private theorem reflexiveLevels (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (typed : env.HasType U Γ expression type) : EqUpToLevels U expression expression :=
  (EqUpToLevels.refl (CtxStrong.strong henv formed).levelWF (typed.strong henv formed)).1

private theorem path_leftType (path : TypeConversion env U Γ A B)
    (typed : env.IsType U Γ B) : env.IsType U Γ A := by
  induction path with
  | refl => exact typed
  | tail _ edge ih => exact ih ⟨_, edge.hasType.1⟩

theorem admission_levels (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (admitted : RequestAdmission env U lower Γ key left right) :
    RequestAdmission env U lower Γ key left' right' := by
  obtain ⟨anchor, pair, typed, formation, code, first, second⟩ := admitted
  have leftEq := pair.hasType.1.eqUpToLevels henv formed leftLevels
  have rightEq := pair.hasType.2.eqUpToLevels henv formed rightLevels
  exact ⟨anchor.trans leftEq, leftEq.symm.trans (pair.trans rightEq),
    typed, formation, code,
    laws (reflexiveLevels henv formed anchor.hasType.1) leftLevels first,
    laws leftLevels rightLevels second⟩

theorem Arguments.levels (henv : env.Ordered) (formed : OnCtx Γ (env.IsType U))
    (laws : LowerLevels U lower)
    (leftLevels : List.Forall₂ (EqUpToLevels U) left left')
    (rightLevels : List.Forall₂ (EqUpToLevels U) right right')
    (arguments : Arguments env U lower Γ keys left right) :
    Arguments env U lower Γ keys left' right' := by
  induction arguments generalizing left' right' with
  | nil => cases leftLevels; cases rightLevels; exact .nil
  | cons head tail ih =>
    cases leftLevels with
    | cons leftHead leftTail =>
      cases rightLevels with
      | cons rightHead rightTail =>
        exact .cons (admission_levels henv formed laws leftHead rightHead head)
          (ih leftTail rightTail)

theorem FamilyWitness.levels (henv : env.Ordered) (laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (witness : FamilyWitness env U registry lower Γ left right demand) :
    Nonempty (FamilyWitness env U registry lower Γ left' right' demand) := by
  obtain ⟨leftHead, ⟨leftExposure⟩, leftEq⟩ := witness.leftExposure.levels henv leftLevels
  obtain ⟨rightHead, ⟨rightExposure⟩, rightEq⟩ := witness.rightExposure.levels henv rightLevels
  obtain ⟨leftPacket, leftArgs, rfl, _, _, leftPackets, leftArgsEq⟩ := dataHead_levels leftEq
  obtain ⟨rightPacket, rightArgs, rfl, _, _, rightPackets, rightArgsEq⟩ := dataHead_levels rightEq
  have formed := witness.leftExposure.targetWF henv
  obtain ⟨_, leftTyped⟩ := path_leftType witness.leftExposure.sound ⟨_, witness.leftType⟩
  obtain ⟨_, rightTyped⟩ := path_leftType witness.rightExposure.sound ⟨_, witness.rightType⟩
  have sourceLeft := leftTyped.eqUpToLevels henv formed (leftLevels.lift' witness.map)
  have sourceRight := rightTyped.eqUpToLevels henv formed (rightLevels.lift' witness.map)
  exact ⟨{ witness with
    path := (TypeConversion.single sourceLeft.symm).trans (witness.path.trans (.single sourceRight))
    leftLevels := leftPacket, rightLevels := rightPacket
    leftArguments := leftArgs, rightArguments := rightArgs
    leftType := (witness.leftType.eqUpToLevels henv formed leftEq).hasType.2
    rightType := (witness.rightType.eqUpToLevels henv formed rightEq).hasType.2
    leftExposure := leftExposure, rightExposure := rightExposure
    leftTerminal := dataTerminal_levels leftEq witness.leftTerminal
    rightTerminal := dataTerminal_levels rightEq witness.rightTerminal
    leftUniverses := Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') witness.leftUniverses leftPackets
    rightUniverses := Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') witness.rightUniverses rightPackets
    arguments := witness.arguments.levels henv formed laws leftArgsEq rightArgsEq }⟩

theorem FamilyRelation.levels (henv : env.Ordered) (laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (related : FamilyRelation env U registry lower Γ left right demand) :
    FamilyRelation env U registry lower Γ left' right' demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact witness.levels henv laws (leftLevels.lift' ρ) (rightLevels.lift' ρ)

theorem ConstructorWitness.levels (henv : env.Ordered) (_laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (witness : ConstructorWitness env U registry lower Γ left right type demand) :
    Nonempty (ConstructorWitness env U registry lower Γ left' right' type demand) := by
  exact ⟨{ witness with
    leftExposure := witness.leftExposure.changeLevels henv leftLevels
    rightExposure := witness.rightExposure.changeLevels henv rightLevels }⟩

theorem RecordWitness.levels (henv : env.Ordered) (laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (witness : RecordWitness env U registry lower Γ left right type demand) :
    Nonempty (RecordWitness env U registry lower Γ left' right' type demand) := by
  have formed := witness.insertion.targetWF henv witness.baseWF
  refine ⟨{ witness with
    leftType := (witness.leftType.eqUpToLevels henv formed (leftLevels.lift' witness.map)).hasType.2
    rightType := (witness.rightType.eqUpToLevels henv formed (rightLevels.lift' witness.map)).hasType.2
    leftOrigins := ?_, rightOrigins := ?_, fields := ?_ }⟩
  · intro entry member
    obtain ⟨origin⟩ := witness.leftOrigins entry member
    exact ⟨origin.changeLevels henv formed (leftLevels.lift' witness.map)⟩
  · intro entry member
    obtain ⟨origin⟩ := witness.rightOrigins entry member
    exact ⟨origin.changeLevels henv formed (rightLevels.lift' witness.map)⟩
  · apply witness.fields.levels henv formed laws
    · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
        (Lean4Lean.List.Forall₂.rfl fun _ _ => .proj (leftLevels.lift' witness.map)))
    · exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
        (Lean4Lean.List.Forall₂.rfl fun _ _ => .proj (rightLevels.lift' witness.map)))

theorem ConstructorRelation.levels (henv : env.Ordered) (laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (related : ConstructorRelation env U registry lower Γ left right type demand) :
    ConstructorRelation env U registry lower Γ left' right' type demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact witness.levels henv laws (leftLevels.lift' ρ) (rightLevels.lift' ρ)

theorem RecordRelation.levels (henv : env.Ordered) (laws : LowerLevels U lower)
    (leftLevels : EqUpToLevels U left left') (rightLevels : EqUpToLevels U right right')
    (related : RecordRelation env U registry lower Γ left right type demand) :
    RecordRelation env U registry lower Γ left' right' type demand := by
  intro Δ ρ future
  obtain ⟨witness⟩ := related Δ ρ future
  exact witness.levels henv laws (leftLevels.lift' ρ) (rightLevels.lift' ρ)

end Lean4Lean.AnchoredSemantics.RankedData
