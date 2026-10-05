import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableQueries
import Lean4Lean.Theory.Typing.AnchoredSortableVariableNormalization
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! A paid capture occurrence alone does not certify its declared type.
When that type is an unobserved original variable, no nonempty input can
be aligned there, even if the realized raw value is well typed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem raised_empty {p : Profile n} {N : Nat} (bound : n ≤ N)
    (empty : raiseProfile N bound p = []) : p = [] := by
  induction N with
  | zero =>
    have same : n = 0 := by omega
    subst n
    exact empty
  | succ N ih =>
    by_cases same : n = N + 1
    · subst n
      simpa only [raiseProfile_self] using empty
    · have lower : n ≤ N := by omega
      rw [raiseProfile_step lower] at empty
      exact ih lower (List.map_eq_nil_iff.mp empty)

/-- Rich variable wrappers cannot manufacture a source code demand when
its exact variable slot has no available request. -/
theorem RichCert.variable_empty_of_noNeed
    {node : EndpointState sourceEnv U source (.bvar index) assigned}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile n) footprint)
    (closed : available.AtomClosed) (resources : footprint.Available available)
    (empty : available index = []) : profile = [] := by
  obtain ⟨required, ⟨query⟩, supplied⟩ := certificate.variableQuery closed resources
  let trace := query.variableTrace
  have footprintEmpty : required = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro request member
    obtain ⟨slot, need⟩ := request
    have slotEq := trace.indices member
    subst slot
    have suppliedNeed := supplied index need member
    rw [empty] at suppliedNeed
    exact List.not_mem_nil suppliedNeed
  have adapter := trace.normalize henv hscoped formed trace.height (Nat.le_refl _)
  simp only [footprintEmpty, Footprint.atGrade, List.flatMap_nil] at adapter
  have normalizedEmpty : AdapterNormal.profile (raiseProfile trace.height trace.output_bound profile) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro atom member
    obtain ⟨original, impossible, _⟩ := adapter.origin member
    exact List.not_mem_nil impossible
  apply raised_empty trace.output_bound
  exact List.map_eq_nil_iff.mp normalizedEmpty

/-- This is a source-certificate obstruction, not a claim that the raw
captured value lacks a target typing. A nonempty aligned value necessarily
requires an actual declared-type query at the otherwise empty variable. -/
theorem HeaderValueAlignment.no_unobserved_variable
    {source : List VExpr} {headerSource : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {owner : HeaderOwner field major}
    {domain : EndpointRef headerEnv U headerSource (.bvar index) (.sort level)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable (input : Profile n))
    (closed : headerAvailable.AtomClosed) (empty : headerAvailable index = [])
    (nonempty : input.Nonempty) : False := by
  have supportEmpty := answer.aligned.certificate.variable_empty_of_noNeed henv hscoped formed
    closed answer.aligned.resources empty
  have typed := answer.value.typed
  rw [supportEmpty] at typed
  apply nonempty
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro atom member
  cases n with
  | zero =>
    obtain ⟨other, impossible, _⟩ := typed atom member
    exact List.not_mem_nil impossible
  | succ n =>
    obtain ⟨other, impossible, _⟩ := typed.2.2 atom member
    exact List.not_mem_nil impossible

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
