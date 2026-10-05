import Lean4Lean.Theory.Typing.AnchoredSortableCert
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceEtaTrace
import Lean4Lean.Theory.Typing.AnchoredCodeAction

/-! Exact finite traces of hereditary observations of a source variable.
Code actions preserve the actual leaf footprint; they are not silently
replaced by reversible profile views. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

inductive SortableVariableTrace (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (i : Nat) : {n : Nat} → Profile n → Footprint → Type where
  | legacy (source : VariableTrace env U registry Γ i demand footprint) :
      SortableVariableTrace env U registry Γ i demand footprint
  | union (left : SortableVariableTrace env U registry Γ i p first)
      (right : SortableVariableTrace env U registry Γ i q second) :
      SortableVariableTrace env U registry Γ i (p.union q) (first ++ second)
  | code (source : SortableVariableTrace env U registry Γ i p footprint)
      (action : SortableCodeAction env U registry Γ relevant p next q)
      (formed : p.HasType (.sort relevant)) :
      SortableVariableTrace env U registry Γ i q footprint
  | action (source : SortableVariableTrace env U registry Γ i (.singleton a) footprint)
      (action : AtomAction env U registry Γ a b) :
      SortableVariableTrace env U registry Γ i (.singleton b) footprint
  | pad (source : SortableVariableTrace env U registry Γ i p footprint) :
      SortableVariableTrace env U registry Γ i p.pad footprint
  | unpad (source : SortableVariableTrace env U registry Γ i p.pad footprint) :
      SortableVariableTrace env U registry Γ i p footprint

noncomputable def CodeCert.sortableVariableTrace
    (certificate : CodeCert env U registry Γ locals σ (.bvar i) demand footprint) :
    SortableVariableTrace env U registry Γ i demand footprint :=
  match certificate with
  | .seed observation _ => .legacy observation.variableTrace
  | .union left right => .union left.sortableVariableTrace right.sortableVariableTrace
  | .pad source => .pad source.sortableVariableTrace
  | .familyPad source => .code source.sortableVariableTrace .familyPad source.formed
  | .unpad source => .unpad source.sortableVariableTrace
  | .down source => .code source.sortableVariableTrace .down source.formed
  | .map v source => .code source.sortableVariableTrace (.map v) source.formed
  | .select source member => .code source.sortableVariableTrace (.select member) source.formed
  | .focusMinimal source minimal bound =>
      .code source.sortableVariableTrace (.focusMinimal minimal bound) source.formed

mutual
noncomputable def SortableCert.variableTrace
    (certificate : SortableCert env U registry Γ locals σ (.bvar i) relevant demand footprint) :
    SortableVariableTrace env U registry Γ i demand footprint :=
  match certificate with
  | .ofCode source _ => source.sortableVariableTrace
  | .observe source _ => source.variableTrace
  | .seed source _ => .legacy source.variableTrace
  | .union left right => .union left.variableTrace right.variableTrace
  | .pad source => .pad source.variableTrace
  | .sortPad source => .code source.variableTrace .sortPad source.formed
  | .familyPad source => .code source.variableTrace .familyPad source.formed
  | .unpad source => .unpad source.variableTrace
  | .down source => .code source.variableTrace .down source.formed
  | .map v source => .code source.variableTrace (.map v) source.formed
  | .support action source => .code source.variableTrace (.support action) source.formed
  | .select source member => .code source.variableTrace (.select member) source.formed
  | .focusMinimal source minimal bound =>
      .code source.variableTrace (.focusMinimal minimal bound) source.formed
termination_by sizeOf certificate

noncomputable def SortableObs.variableTrace
    (observation : SortableObs env U registry Γ locals σ (.bvar i) demand footprint) :
    SortableVariableTrace env U registry Γ i demand footprint :=
  match observation with
  | .legacy source => .legacy source.variableTrace
  | .code _ source => source.variableTrace
  | .union left right => .union left.variableTrace right.variableTrace
  | .view source v => .action source.variableTrace (.view v)
  | .action source action => .action source.variableTrace action
  | .pad source => .pad source.variableTrace
  | .unpad source => .unpad source.variableTrace
  | .rowShift source => .action (.pad source.variableTrace) (.view (.commutePadFn _ _))
termination_by sizeOf observation
end

def SortableVariableTrace.height : {n : Nat} → {p : Profile n} → {fp : Footprint} →
    SortableVariableTrace env U registry Γ i p fp → Nat
  | _, _, _, .legacy source => source.height
  | _, _, _, .union left right => max left.height right.height
  | n, _, _, .code source _ _ => max n source.height
  | _, _, _, .action source _ => source.height
  | n + 1, _, _, .pad source => max (n + 1) source.height
  | _, _, _, .unpad source => source.height

theorem SortableVariableTrace.output_bound
    (trace : SortableVariableTrace env U registry Γ i (demand : Profile n) footprint) :
    n ≤ trace.height := by
  induction trace with
  | legacy source => exact source.output_bound
  | union left right hl hr => exact Nat.le_trans hl (Nat.le_max_left _ _)
  | code | pad => exact Nat.le_max_left _ _
  | action _ _ ih => exact ih
  | unpad _ ih => exact Nat.le_trans (Nat.le_succ _) ih

theorem SortableVariableTrace.indices
    (trace : SortableVariableTrace env U registry Γ i demand footprint)
    (member : (j, need) ∈ footprint) : j = i := by
  induction trace with
  | legacy source => exact source.indices member
  | union left right hl hr =>
    rcases List.mem_append.mp member with h | h
    · exact hl h
    · exact hr h
  | code _ _ _ ih | action _ _ ih | pad _ ih | unpad _ ih => exact ih member

theorem SortableVariableTrace.leaf_bound
    (trace : SortableVariableTrace env U registry Γ i demand footprint)
    (member : (j, need) ∈ footprint) : need.rank ≤ trace.height := by
  induction trace with
  | legacy source => exact source.leaf_bound member
  | union left right hl hr =>
    rcases List.mem_append.mp member with h | h
    · exact Nat.le_trans (hl h) (Nat.le_max_left _ _)
    · exact Nat.le_trans (hr h) (Nat.le_max_right _ _)
  | code _ _ _ ih | pad _ ih => exact Nat.le_trans (ih member) (Nat.le_max_right _ _)
  | action _ _ ih | unpad _ ih => exact ih member

end Lean4Lean.AnchoredSource.Adapted
