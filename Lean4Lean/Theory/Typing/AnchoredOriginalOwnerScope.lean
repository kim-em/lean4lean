import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureGeneration

/-! The actual common-source scope around an original capture occurrence.
This data survives query-selected frame merges: it records the source map
and complete realization tails, rather than a particular frame constructor trace. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

structure OriginalOwnerScope
    (common : List VExpr) (ownerRaw commonLeft commonRight : Subst) (depth : Nat)
    (context : ContextDerivation sourceEnv U source) where
  scope : List VExpr
  raw : Subst
  left : Subst
  right : Subst
  graph : OriginalCaptureMap (common := scope) context raw
  insertion : Ctx.Lift' (.skipN .refl depth) common scope
  raw_eq : raw = ownerRaw.liftN depth
  leftTail : Subst.lift_l (.skipN .refl depth) left = commonLeft
  rightTail : Subst.lift_l (.skipN .refl depth) right = commonRight

private theorem liftN_comp_tail (raw value : Subst) (depth : Nat) :
    Subst.lift_l (.skipN .refl depth) ((raw.liftN depth).comp value) =
      raw.comp (Subst.lift_l (.skipN .refl depth) value) := by
  funext index
  change ((raw.liftN depth) ((Lift.skipN .refl depth).liftVar index)).subst value = _
  simp only [Lift.liftVar_skipN, Lift.liftVar, Subst.liftN_apply,
    show ¬index + depth < depth by omega, if_false, Nat.add_sub_cancel,
    Subst.comp]
  exact liftN_subst

/-- The full original substitution tail, not only one realized expression,
is fixed by the retained scope. -/
theorem OriginalOwnerScope.leftRealization
    (scope : OriginalOwnerScope common ownerRaw commonLeft commonRight depth context) :
    Subst.lift_l (.skipN .refl depth) (scope.raw.comp scope.left) = ownerRaw.comp commonLeft := by
  rw [scope.raw_eq, liftN_comp_tail, scope.leftTail]

theorem OriginalOwnerScope.rightRealization
    (scope : OriginalOwnerScope common ownerRaw commonLeft commonRight depth context) :
    Subst.lift_l (.skipN .refl depth) (scope.raw.comp scope.right) = ownerRaw.comp commonRight := by
  rw [scope.raw_eq, liftN_comp_tail, scope.rightTail]

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
