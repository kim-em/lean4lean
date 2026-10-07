import Lean4Lean.Theory.Typing.DefinitionOuterStage
import Lean4Lean.Theory.Typing.NativeRecursorRegistration

/-! An installed equation has an actual original checking source before its
first installation, even when the final registry is only pointwise registered.
This requires no common native history and does not assert that the selected
source lies below an arbitrary caller containing only the equation's head. -/
namespace Lean4Lean.VEnv
set_option Elab.async false

structure EquationHeaderOrigin (env : VEnv) (rule : VDefEq) where
  source : VEnv
  ordered : source.Ordered
  formation : rule.WF source
  sourceBelow : source ≤ env
  absent : ¬ source.defeqs rule
  present : env.defeqs rule

namespace EquationHeaderOrigin

def extend (origin : EquationHeaderOrigin env rule) (below : env ≤ extended) :
    EquationHeaderOrigin extended rule :=
  { origin with sourceBelow := origin.sourceBelow.trans below
                present := below.defeqs origin.present }

theorem equationCount_lt (origin : EquationHeaderOrigin env rule) (ordered : env.Ordered) :
    origin.ordered.equationCount < ordered.equationCount :=
  origin.ordered.equationCount_lt_of_new ordered origin.sourceBelow origin.absent origin.present

theorem definitionStage_lt (origin : EquationHeaderOrigin env rule) (ordered : env.Ordered) :
    Prod.Lex Nat.lt Nat.lt origin.ordered.definitionStage ordered.definitionStage := by
  have constants := (origin.ordered.definitionStage_components_le ordered origin.sourceBelow).1
  change origin.ordered.constantCount ≤ ordered.constantCount at constants
  by_cases strict : origin.ordered.constantCount < ordered.constantCount
  · exact .left _ _ strict
  · have same : origin.ordered.constantCount = ordered.constantCount := by omega
    change Prod.Lex Nat.lt Nat.lt
      (origin.ordered.constantCount, origin.ordered.equationCount)
      (ordered.constantCount, ordered.equationCount)
    rw [same]
    exact .right _ (origin.equationCount_lt ordered)

/-- Both source endpoints are strengthened at the selected original source,
not retyped in the final target environment. -/
theorem strong (origin : EquationHeaderOrigin env rule) :
    origin.source.IsDefEqStrong rule.uvars [] rule.lhs rule.lhs rule.type ∧
      origin.source.IsDefEqStrong rule.uvars [] rule.rhs rule.rhs rule.type :=
  ⟨origin.formation.1.strong origin.ordered trivial,
    origin.formation.2.strong origin.ordered trivial⟩

end EquationHeaderOrigin

/-- Duplicate equation installation is skipped, so absence in the selected
original checking source is proved rather than assumed. -/
theorem Ordered.equationHeaderOrigin (ordered : env.Ordered) (present : env.defeqs rule) :
    Nonempty (EquationHeaderOrigin env rule) := by
  classical
  induction ordered with
  | empty => cases present
  | @const previous name value current ordered formation installed ih =>
    obtain ⟨origin⟩ := ih (by rwa [VEnv.addConst_defeqs installed] at present)
    exact ⟨origin.extend (VEnv.addConst_le installed)⟩
  | @defeq previous added ordered formation ih =>
    by_cases old : previous.defeqs rule
    · obtain ⟨origin⟩ := ih old
      exact ⟨origin.extend VEnv.addDefEq_le⟩
    · have same : rule = added := present.resolve_right old
      cases same
      exact ⟨⟨previous, ordered, formation, VEnv.addDefEq_le, old, .inl rfl⟩⟩
  | eliminator _ ih =>
    obtain ⟨origin⟩ := ih present
    exact ⟨origin.extend VEnv.addEliminator_le⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨origin⟩ := ih (by simpa only [VEnv.addEliminators_defeqs, VEnv.addProjections_defeqs] using present)
    exact ⟨origin.extend VEnv.addEliminators_addProjections_le⟩

/-- Pointwise native registration suffices to recover the actual earlier
rule source for the selected singleton equation. It supplies no unrelated
native-history or caller-envelope premise. -/
theorem NativeRecursorRegistered.singletonEquationHeader
    (registered : NativeRecursorRegistered env data) (ordered : env.Ordered)
    (selected : data.singletonEquation = some rule) :
    Nonempty (EquationHeaderOrigin env rule) :=
  ordered.equationHeaderOrigin (registered.singletonEquation selected)

end Lean4Lean.VEnv
