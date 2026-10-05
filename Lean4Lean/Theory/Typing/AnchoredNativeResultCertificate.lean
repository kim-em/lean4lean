import Lean4Lean.Theory.Typing.NativeResultBridge
import Lean4Lean.Theory.Typing.AnchoredNativeTemplateRealization

/-! A native result certificate must retain the demands on every recursor
argument, including compound constructor result indices. Factoring the
original equation certificate returns those demands and their actual source
observation cuts; it does not assert that field-copy requirements cover them. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem takeForalls_result_scoped
    {expression result : VExpr} {domains : List VExpr} {count depth : Nat}
    (parsed : NativeRecursorData.takeForalls count expression = some (domains, result))
    (scope : expression.ClosedN depth) : result.ClosedN (depth + count) := by
  induction count generalizing expression domains depth with
  | zero =>
    simp only [NativeRecursorData.takeForalls, Option.some.injEq, Prod.mk.injEq] at parsed
    rcases parsed with ⟨rfl, rfl⟩
    exact scope
  | succ count ih =>
    cases expression <;> simp only [NativeRecursorData.takeForalls] at parsed <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨⟨tail, body⟩, parsed, rfl, rfl⟩ := parsed
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih parsed scope.2

theorem NativeConstantSignature.resultScoped
    {data : NativeRecursorData} {levels : List VLevel}
    (signature : NativeConstantSignature data levels) (closed : signature.type.Closed) :
    signature.result.ClosedN (data.majorOffset + 1) := by
  simpa only [Nat.zero_add] using takeForalls_result_scoped signature.telescope closed.instL

/-- The registered result bridge holds before the equation arguments are
realized, so ordinary source factorization applies to the actual syntax. -/
theorem NativeConstantSignature.equationResult_template
    {env : VEnv} {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program) :
    signature.result.instOuter (program.equationBody.lhs.instL program.levels).getAppFnArgs.2 =
      program.equationBody.type.instL program.levels := by
  have bridge := saturatedProgram_resultBridge registered selected signature.typeOrigin
    signature.telescope Subst.id
  rw [VExpr.instOuter_eq_subst]
  change instantiateParams signature.result _ = _
  simpa only [VExpr.subst_id, List.map_id_fun', id_eq] using bridge

/-- Return the literal generic recursor-result certificate and all cuts back
to the original equation certificate. The returned footprint is a real new
requirement to be included in native binder packing. -/
theorem CodeCert.nativeResultTemplate
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (signature : NativeConstantSignature data program.levels)
    (registered : NativeRecursorRegistered env data)
    (selected : data.saturatedProgram program.levels arguments = some program)
    (closed : signature.type.Closed)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ
      (program.equationBody.type.instL program.levels) support footprint) :
    ∃ required,
      Nonempty (CodeCert env U registry target (List.range signature.domains.length)
        (nativeCaptureSubst ((program.equationBody.lhs.instL program.levels).getAppFnArgs.2.map
          (·.subst σ))) signature.result support required) ∧
      Nonempty (ParamsFootprint env U registry target locals σ
        (program.equationBody.lhs.instL program.levels).getAppFnArgs.2 footprint required) := by
  have resultScope := signature.resultScoped closed
  have length := nativeEquationArguments_length (witnesses := []) selected
  simp only [nativeEquationArguments, List.length_map] at length
  rw [← length] at resultScope
  rw [← signature.equationResult_template registered selected] at certificate
  exact certificate.factorNativeTemplate resultScope (List.range signature.domains.length)

end Lean4Lean.AnchoredSource.Adapted
