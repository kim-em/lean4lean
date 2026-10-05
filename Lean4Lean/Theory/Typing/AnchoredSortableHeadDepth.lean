import Lean4Lean.Theory.Typing.AnchoredHeadDepth
import Lean4Lean.Theory.Typing.AnchoredSortableCert

/-! Finite depth with an explicit computational-head policy. Every actual
source query/certificate child is traversed; only a named delta/native head
can mask its recursively computed child depth. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

mutual
def SortableCert.headDepth (policy : Name → Nat → Nat)
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) : Nat :=
  match certificate with
  | .ofCode source _ => source.headDepth policy
  | .seed source _ => source.headDepth policy
  | .observe source _ => source.headDepth policy
  | .pi domain _ bodies => max (domain.headDepth policy) (bodies.headDepth policy)
  | .union left right => max (left.headDepth policy) (right.headDepth policy)
  | .pad source | .sortPad source | .familyPad source | .unpad source | .down source
  | .map _ source | .support _ source | .select source _ | .focusMinimal source _ _ =>
    source.headDepth policy
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

def SortableRows.headDepth (policy : Name → Nat → Nat)
    (rows : SortableRows env U registry target locals σ A B relevant ambient rowList footprint) : Nat :=
  match rows with
  | .nil => 0
  | .cons _ body _ _ tail => max (body.headDepth policy) (tail.headDepth policy)
termination_by sizeOf rows
decreasing_by all_goals (simp_wf <;> omega)

def SortableObs.headDepth (policy : Name → Nat → Nat)
    (observation : SortableObs env U registry target locals σ expression demand footprint) : Nat :=
  match observation with
  | .family _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    max (tree.headDepth policy) (certificate.headDepth policy)
  | .legacy source => source.headDepth policy
  | .code _ certificate => certificate.headDepth policy
  | .app fn arg _ _ => max (fn.headDepth policy) (arg.headDepth policy)
  | .lam domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .union left right => max (left.headDepth policy) (right.headDepth policy)
  | .view source _ | .action source _ | .pad source | .unpad source | .rowShift source =>
    source.headDepth policy
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

def SortableFamilyPlan.headDepth (policy : Name → Nat → Nat)
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  match plan with
  | .terminal _ _ _ captures => captures.headDepth policy
  | .binder _ domain _ body _ _ => max (domain.headDepth policy) (body.headDepth policy)
  | .view source _ | .pad source => source.headDepth policy
termination_by sizeOf plan
decreasing_by all_goals (simp_wf <;> omega)
end

mutual
theorem SortableCert.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) : certificate.headDepth policy = 0 := by
  match certificate with
  | .ofCode source _ =>
    rw [SortableCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .seed source _ =>
    rw [SortableCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .observe source _ =>
    rw [SortableCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .pi domain _ bodies =>
    rw [SortableCert.headDepth]
    change max (domain.headDepth policy) (bodies.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, bodies.headDepth_zero policy zero, Nat.max_self, zero]
  | .union left right =>
    rw [SortableCert.headDepth]
    change max (left.headDepth policy) (right.headDepth policy) = 0
    simp only [left.headDepth_zero policy zero, right.headDepth_zero policy zero, Nat.max_self, zero]
  | .pad source | .sortPad source | .familyPad source | .unpad source | .down source
  | .map _ source | .support _ source | .select source _ | .focusMinimal source _ _ =>
    rw [SortableCert.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem SortableRows.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (rows : SortableRows env U registry target locals σ A B relevant ambient rowList footprint) : rows.headDepth policy = 0 := by
  match rows with
  | .nil => simp only [SortableRows.headDepth]
  | .cons _ body _ _ tail =>
    rw [SortableRows.headDepth]
    change max (body.headDepth policy) (tail.headDepth policy) = 0
    simp only [body.headDepth_zero policy zero, tail.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem SortableObs.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (observation : SortableObs env U registry target locals σ expression demand footprint) : observation.headDepth policy = 0 := by
  match observation with
  | .family _ _ _ _ _ _ _ _ _ _ certificate _ tree =>
    rw [SortableObs.headDepth]
    change max (tree.headDepth policy) (certificate.headDepth policy) = 0
    simp only [tree.headDepth_zero policy zero, certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .legacy source =>
    rw [SortableObs.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
  | .code _ certificate =>
    rw [SortableObs.headDepth]
    change certificate.headDepth policy = 0
    simp only [certificate.headDepth_zero policy zero, Nat.max_self, zero]
  | .app fn arg _ _ =>
    rw [SortableObs.headDepth]
    change max (fn.headDepth policy) (arg.headDepth policy) = 0
    simp only [fn.headDepth_zero policy zero, arg.headDepth_zero policy zero, Nat.max_self, zero]
  | .lam domain _ body _ _ =>
    rw [SortableObs.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .union left right =>
    rw [SortableObs.headDepth]
    change max (left.headDepth policy) (right.headDepth policy) = 0
    simp only [left.headDepth_zero policy zero, right.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .action source _ | .pad source | .unpad source | .rowShift source =>
    rw [SortableObs.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem SortableFamilyPlan.headDepth_zero (policy : Name → Nat → Nat) (zero : ∀ name, policy name 0 = 0)
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) : plan.headDepth policy = 0 := by
  match plan with
  | .terminal _ _ _ captures =>
    rw [SortableFamilyPlan.headDepth]
    change captures.headDepth policy = 0
    simp only [captures.headDepth_zero policy zero, Nat.max_self, zero]
  | .binder _ domain _ body _ _ =>
    rw [SortableFamilyPlan.headDepth]
    change max (domain.headDepth policy) (body.headDepth policy) = 0
    simp only [domain.headDepth_zero policy zero, body.headDepth_zero policy zero, Nat.max_self, zero]
  | .view source _ | .pad source =>
    rw [SortableFamilyPlan.headDepth]
    change source.headDepth policy = 0
    simp only [source.headDepth_zero policy zero, Nat.max_self, zero]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

end

def SortableCert.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) : Nat :=
  certificate.headDepth (stratifiedHeadPolicy rank control)
def SortableRows.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (rows : SortableRows env U registry target locals σ A B relevant ambient rowList footprint) : Nat :=
  rows.headDepth (stratifiedHeadPolicy rank control)
def SortableObs.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (observation : SortableObs env U registry target locals σ expression demand footprint) : Nat :=
  observation.headDepth (stratifiedHeadPolicy rank control)
def SortableFamilyPlan.stratifiedDepth (rank : Name → Nat) (control : Nat)
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) : Nat :=
  plan.headDepth (stratifiedHeadPolicy rank control)

theorem SortableCert.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (certificate : SortableCert env U registry target locals σ expression relevant demand footprint) : certificate.stratifiedDepth rank control = 0 := by
  apply certificate.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem SortableRows.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (rows : SortableRows env U registry target locals σ A B relevant ambient rowList footprint) : rows.stratifiedDepth rank control = 0 := by
  apply rows.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem SortableObs.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (observation : SortableObs env U registry target locals σ expression demand footprint) : observation.stratifiedDepth rank control = 0 := by
  apply observation.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

theorem SortableFamilyPlan.stratifiedDepth_above {maximum control : Nat} (rank : Name → Nat)
    (rankBound : ∀ name, rank name ≤ maximum) (above : maximum < control)
    (plan : SortableFamilyPlan env U registry target name levels signature arguments demand footprint) : plan.stratifiedDepth rank control = 0 := by
  apply plan.headDepth_zero (stratifiedHeadPolicy rank control)
  intro name
  exact EquationStratifiedFuel.headDepth_above (Nat.lt_of_le_of_lt (rankBound name) above)

end Lean4Lean.AnchoredSource.Adapted
