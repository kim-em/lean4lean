import Lean4Lean.Theory.Typing.CanonicalDataHeadRenaming
import Lean4Lean.Theory.Typing.NativeDeclarationProvenance
import Lean4Lean.Theory.Typing.CaseRuleScope
import Lean4Lean.Theory.Inductive.CaseRegistration

/-! Scope for the concrete data machine from actual declaration history and
the original generic case headers. Generated equation scope is derived, rather
than supplied as an additional registry-correctness assumption. -/

namespace Lean4Lean.VEnv
open InductiveSignature

/-- Only ordered equation registration is needed for right-side scope. -/
theorem NativeRecursorRegistered.equation_rhs_closed (ordered : env.Ordered)
    (registered : NativeRecursorRegistered env data)
    (generated : data.equation index = some equation) : equation.rhs.Closed :=
  VExpr.WF.closedN ordered
    ⟨_, (ordered.defEqWF (registered.equation_present generated)).2⟩ trivial

/-- The restoration table is the one checked by the original compilation. -/
theorem WF.eliminator_restoration_scoped {env : VEnv} {schema : CaseSchema}
    (formed : env.WF)
    (lookup : env.eliminators block schema) : schema.restoration.Scoped := by
  obtain ⟨base, source, generated, _, _, certified, _, _⟩ :=
    formed.eliminator_origin lookup
  obtain ⟨expanded, auxiliaries, compilation, _, restoration, _, _⟩ := certified
  rw [restoration]
  exact compilation.restorationScoped

end Lean4Lean.VEnv

namespace Lean4Lean.CanonicalDataHead
open InductiveSignature VEnv

/-- The scope required by every possible selection follows from the actual
native registration and finite original case headers. -/
theorem Registry.scoped_of_headers {env : VEnv} {registry : Registry}
    (formed : env.WF)
    (definitions : ∀ name value, registry.definitions name = some value → value.value.Closed)
    (natives : ∀ name data, registry.natives name = some data →
      NativeRecursorRegistered env data)
    (cases : ∀ block owner entry, registry.cases block owner = some entry →
      env.eliminators block entry.schema ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed) :
    registry.Scoped := by
  refine ⟨definitions, ?_, ?_, ?_⟩
  · intro name data lookup equation generated
    exact (natives name data lookup).singletonEquation_rhs_closed formed generated
  · intro name data lookup index equation generated
    exact (natives name data lookup).equation_rhs_closed formed.ordered generated
  · intro block owner entry lookup rule generated
    obtain ⟨registered, header, selectedHeader, closed⟩ := cases _ _ _ lookup
    exact generated.rhs_closed selectedHeader
      (formed.eliminator_restoration_scoped registered) closed

/-- All tables used by the machine are concrete syntax. Definition bodies
come from the declaration list; the other tables retain their actual lookups. -/
def Registry.ofDataHistory (declarations : List VDecl)
    (natives : Name → Option NativeRecursorData)
    (cases : Name → Nat → Option CaseEntry)
    (projections : Name → Option VProjectionInfo)
    (structureConstructors : Name → Option VProjectionEntry) (quotient : Bool) : Registry :=
  { definitions := definitionRegistry declarations
    natives := natives
    cases := cases
    projections := projections
    structureConstructors := structureConstructors
    quotient := quotient }

/-- The complete machine's scope is produced from the original history and
case headers, including every native constructor equation. -/
theorem Registry.ofDataHistory_scoped
    {env : VEnv} {declarations : List VDecl} {natives : Name → Option NativeRecursorData}
    {cases : Name → Nat → Option CaseEntry} {projections : Name → Option VProjectionInfo}
    {structureConstructors : Name → Option VProjectionEntry} {quotient : Bool}
    (history : NativeRegistryHistory env declarations natives)
    (caseHeaders : ∀ block owner entry, cases block owner = some entry →
      env.eliminators block entry.schema ∧
      ∃ header, entry.schema.genericType entry.owner = some header ∧ header.Closed) :
    (Registry.ofDataHistory declarations natives cases projections structureConstructors quotient).Scoped := by
  have formed : env.WF := ⟨declarations, history.history⟩
  apply Registry.scoped_of_headers formed
  · intro name value lookup
    exact (history.history.definitionRegistry_registered lookup).1.closed formed
  · intro name data lookup
    exact (history.registered lookup).1
  · exact caseHeaders

end Lean4Lean.CanonicalDataHead
