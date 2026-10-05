import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceScope

/-! Finite sortable queries retain only variables occurring in their source
expression, including computational queries nested below native Pi rows. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

mutual
theorem SortableCert.scoped
    (certificate : SortableCert env U registry Γ locals σ expression relevant demand footprint)
    (scope : expression.ClosedN count) : Footprint.Scoped count footprint := by
  match certificate with
  | .ofCode source _ | .seed source _ => exact source.scoped scope
  | .observe observation _ => exact observation.scoped scope
  | .pi domain _ bodies =>
    exact Footprint.Scoped.append (domain.scoped scope.1) (bodies.scoped scope.2)
  | .union left right => exact Footprint.Scoped.append (left.scoped scope) (right.scoped scope)
  | .pad source | .sortPad source | .familyPad source | .unpad source | .down source
  | .support _ source | .map _ source | .select source _ | .focusMinimal source _ _ => exact source.scoped scope
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableRows.scoped
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint)
    (scope : B.ClosedN (count + 1)) : Footprint.Scoped count footprint := by
  match bodies with
  | .nil => exact fun _ _ h => nomatch h
  | .cons _ body normal _ tail =>
    exact Footprint.Scoped.append (normal.scoped (body.scoped scope)) (tail.scoped scope)
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)

theorem SortableObs.scoped
    (observation : SortableObs env U registry Γ locals σ expression demand footprint)
    (scope : expression.ClosedN count) : Footprint.Scoped count footprint := by
  match observation with
  | .family .. => exact fun _ _ h => nomatch h
  | .legacy source => exact source.scoped scope
  | .code _ source => exact source.scoped scope
  | .app fn arg _ _ =>
    exact Footprint.Scoped.append (fn.scoped scope.1) (arg.scoped scope.2)
  | .lam domain _ body normal _ =>
    exact Footprint.Scoped.append (domain.scoped scope.1)
      (normal.scoped (body.scoped scope.2))
  | .union left right => exact Footprint.Scoped.append (left.scoped scope) (right.scoped scope)
  | .action source _ | .view source _ | .pad source | .unpad source | .rowShift source => exact source.scoped scope
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)
end

end Lean4Lean.AnchoredSource.Adapted
