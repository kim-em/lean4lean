import Lean4Lean.Theory.Typing.CanonicalHeadTrace
import Lean4Lean.Theory.Typing.DefinitionHistory
import Lean4Lean.Theory.Typing.NativeRuleRegistration

/-! The scope requirements of the canonical head machine follow from actual
registration in a well-formed environment. Ordinary definitions are extracted
from its declaration history. The native table supplies registration evidence
for its entries; no body-closure or semantic guard assumption is required.
-/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- A selected singleton equation is one of the actually registered native
equations, so environment formation supplies the scope of its right side. -/
theorem NativeRecursorRegistered.singletonEquation_rhs_closed
    {env : VEnv} {data : NativeRecursorData} {equation : VDefEq}
    (henv : env.WF) (H : NativeRecursorRegistered env data)
    (hequation : data.singletonEquation = some equation) : equation.rhs.Closed := by
  unfold NativeRecursorData.singletonEquation at hequation
  dsimp only at hequation
  split at hequation <;> try contradiction
  exact (H.equation_closed henv hequation).2.1

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalHead
open InductiveSignature VEnv

/-- The definition half is the actual history-derived table. The native half
remains the supplied fixed table, checked by `ofHistory_scoped` below. -/
def Registry.ofHistory (declarations : List VDecl)
    (natives : Name → Option NativeRecursorData) : Registry :=
  { definitions := VEnv.definitionRegistry declarations, natives := natives }

/-- Declaration history and concrete native registration produce every scope
fact needed by the machine's total renaming and trace-comparison theorems. -/
theorem Registry.ofHistory_scoped {env : VEnv} {declarations : List VDecl}
    {natives : Name → Option NativeRecursorData}
    (H : env.WF' declarations)
    (hnatives : ∀ name data, natives name = some data → NativeRecursorRegistered env data) :
    (Registry.ofHistory declarations natives).Scoped := by
  have henv : env.WF := ⟨declarations, H⟩
  constructor
  · intro name value hlookup
    exact (H.definitionRegistry_registered hlookup).1.closed henv
  · intro name data hlookup equation hequation
    exact (hnatives name data hlookup).singletonEquation_rhs_closed henv hequation
  · intro name data hlookup index equation hequation
    exact (hnatives name data hlookup).equation_closed henv hequation |>.2.1
  · intro block owner entry hlookup
    cases hlookup

end Lean4Lean.CanonicalHead
