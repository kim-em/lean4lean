import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrefixOnly

/-! # Constant or projection heads of erased computational primitives -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params
namespace ProofShape
/-- Primitive computation requires a constant or projection at the head of its
source application spine. Variable-headed applications are excluded. -/
def PrimitiveHead : ProofShape → Prop
  | .const .. | .proj .. => True
  | .app f _ => PrimitiveHead f
  | _ => False

/-- Every visible pattern match retains a constant at its function head. -/
theorem Matches.primitiveHead (H : Matches p e ls captures) : PrimitiveHead e := by
  induction H with
  | const => trivial
  | var _ ih => exact ih
  | app _ _ ih _ => exact ih
end ProofShape
variable [Params]

/-- All ordinary erased primitives have a constant or projection head. -/
theorem erased_iota_primitive_head (H : ErasedIotaPrimitive D a b) : ProofShape.PrimitiveHead a := by
  rcases H with (H | H) | H
  · cases H <;> trivial
  · cases H with
    | select _ _ hm => exact hm.primitiveHead
    | apply _ _ hm => exact hm.primitiveHead
  · cases H with
    | intro _ _ _ hm => exact hm.primitiveHead

/-- Adding any finite number of full K and before-major prefix stages still
cannot create a primitive at a variable-headed application. -/
theorem erased_prefix_K_stage_head : ∀ stage {a b}, ErasedPrefixKStage D stage a b →
    ProofShape.PrimitiveHead a := by
  intro stage
  induction stage with
  | zero => exact erased_iota_primitive_head
  | succ stage ih =>
    intro a b H
    rcases H with H | H | H
    · exact ih H
    · cases H; trivial
    · cases H; trivial

end Lean4Lean.VEnv.Strengthening
