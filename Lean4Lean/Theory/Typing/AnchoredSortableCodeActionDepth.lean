import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepth
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionCertificate

/-! Finite code transformations preserve each caller's unfolding depth on
the same returned certificate, including actions that duplicate resources. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

@[simp] theorem SortableCodeAction.nativeDepth_applyCertificate
    (current : Name → Bool)
    (action : SortableCodeAction env U registry target relevant profile next nextProfile)
    {footprint : Footprint}
    (certificate : SortableCert env U registry target locals σ expression relevant profile footprint) :
    (action.applyCertificate certificate).nativeDepth current = certificate.nativeDepth current := by
  induction action generalizing footprint with
  | comp first second firstIH secondIH =>
    exact (secondIH (first.applyCertificate certificate)).trans (firstIH certificate)
  | union first second firstIH secondIH =>
    simp only [SortableCodeAction.applyCertificate, SortableCert.nativeDepth,
      firstIH certificate, secondIH certificate, Nat.max_self]
  | _ => simp only [SortableCodeAction.applyCertificate, SortableCert.nativeDepth,
      SortableObs.nativeDepth]

end Lean4Lean.AnchoredSource.Adapted
