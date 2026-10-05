import Lean4Lean.Theory.Typing.AnchoredConstructorRegisteredResult

/-! A constructor header's literal domains agree with the registered raw
constructor telescope after universe specialization. This is syntax
normalization from the original declaration, independent of typing inversion. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature

theorem ConstructorResultHeader.registered_domains
    {env : VEnv} (henv : env.Ordered)
    {info : VProjectionInfo} (registered : env.projections name info)
    {levels : List VLevel} {arguments : List VExpr}
    (header : ConstructorResultHeader env info.ctorName name levels arguments) :
    ∃ domains result,
      info.ctorType = wrapForalls domains result ∧
      domains.length = info.nparams + info.numFields ∧
      header.domains = domains.map (·.instL levels) ∧
      mkApps (.const name header.familyLevels) header.familyArguments = result.instL levels := by
  obtain ⟨decl, family, ctor, _, _, _, _, _, parameters, _, _, _, ctorType,
    _, _, _, raw, _⟩ := henv.projectionShape registered
  obtain ⟨domains, result, shape, bound, _, _, arity⟩ := raw.forallArity
  have constant : header.info = { uvars := info.uvars, type := info.ctorType } :=
    Option.some.inj (header.lookup.symm.trans (henv.projectionConstructor registered))
  have telescope := header.telescope
  rw [constant] at telescope
  change info.ctorType.instL levels = _ at telescope
  have terminalZero : (mkApps (.const name header.familyLevels) header.familyArguments).forallArity = 0 :=
    forallArity_eq_zero_of_getAppFnArgs (getAppFnArgs_mkApps_const _ _ _)
  have length := congrArg VExpr.forallArity telescope
  simp only [forallArity_instL, forallArity_wrapForalls, terminalZero, Nat.add_zero] at length
  have domainLength : domains.length = header.domains.length := by
    simpa only [← ctorType, arity] using length
  have layout : domains.length = info.nparams + info.numFields := by
    rw [VProjectionInfo.numFields, ← ctorType, arity]
    omega
  rw [← ctorType, shape, instL_wrapForalls] at telescope
  have equal := congrArg (fun expression => expression.takeForalls header.domains.length) telescope
  rw [← domainLength] at equal
  have mappedLength : (domains.map (·.instL levels)).length = domains.length := List.length_map _
  rw [← mappedLength, takeForalls_wrapForalls] at equal
  rw [mappedLength, domainLength, takeForalls_wrapForalls] at equal
  have parts := Prod.mk.inj (Option.some.inj equal)
  exact ⟨domains, result, ctorType.symm.trans shape, layout, parts.1.symm, parts.2.symm⟩

end Lean4Lean.AnchoredSemantics
