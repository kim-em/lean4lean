import Lean4Lean.Theory.Typing.AnchoredDataExposure
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.ProjectionLemmas
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! A registered structure constructor's result is determined by its literal
declaration telescope. No type uniqueness is used to recover its parameters. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv InductiveSignature

theorem ConstructorResultHeader.registered_result
    {env : VEnv} (henv : env.Ordered)
    {info : VProjectionInfo} (registered : env.projections name info)
    (unindexed : info.nindices = 0)
    {levels : List VLevel} (levelCount : levels.length = info.uvars)
    {arguments : List VExpr}
    (header : ConstructorResultHeader env info.ctorName name levels arguments) :
    arguments.length = info.nparams + info.numFields ∧
      header.result = mkApps (.const name levels) (arguments.take info.nparams) := by
  obtain ⟨decl, family, ctor, member, _, familyName, _, universes,
    parameters, indices, _, ctorName, ctorType, _, _, _, raw, names⟩ :=
    henv.projectionShape registered
  obtain ⟨domains, result, shape, bound, valid, head, arity⟩ := raw.forallArity
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
  have count : arguments.length = info.nparams + info.numFields := by
    rw [← header.saturated, ← domainLength, VProjectionInfo.numFields, ← ctorType, arity]
    omega
  have literal : result.instL levels =
      mkApps (.const name header.familyLevels) header.familyArguments := by
    rw [← ctorType, shape, instL_wrapForalls] at telescope
    have equal := congrArg (fun expression => expression.takeForalls header.domains.length) telescope
    rw [← domainLength] at equal
    have mappedLength : (domains.map (·.instL levels)).length = domains.length := List.length_map _
    rw [← mappedLength, takeForalls_wrapForalls] at equal
    rw [mappedLength, domainLength, takeForalls_wrapForalls] at equal
    exact (Prod.mk.inj (Option.some.inj equal)).2
  have actualHead : (result.instL levels).getAppFnArgs.1 = .const name levels := by
    rw [getAppFnArgs_instL]
    change result.getAppFnArgs.1.instL levels = _
    rw [head, familyName]
    simp only [instL, VLevel.params_map_inst levels (levelCount.trans universes.symm)]
  obtain ⟨actualIndices, instantiated, selected, selectedMember, selectedName, selectedCount⟩ :=
    (valid.instL levels).instOuter (by simpa only [familyName] using actualHead)
      arguments (by rw [← header.saturated, ← domainLength]; omega)
  have same : selected = family := List.eq_of_mem_of_nodup_map
    (VInductDecl.typeNames_nodup names) selectedMember member selectedName
  have noIndices : actualIndices = [] := List.eq_nil_of_length_eq_zero (by
    rw [selectedCount, same, indices, unindexed])
  refine ⟨count, ?_⟩
  rw [noIndices, List.append_nil, familyName, parameters] at instantiated
  rw [literal, VExpr.instOuter_eq_subst] at instantiated
  exact instantiated

theorem ConstructorResultHeader.registered_result_of_name
    {env : VEnv} (henv : env.Ordered)
    {info : VProjectionInfo} (registered : env.projections name info)
    (unindexed : info.nindices = 0)
    {levels : List VLevel} (levelCount : levels.length = info.uvars)
    {constructor : Name} (constructorName : constructor = info.ctorName)
    {arguments : List VExpr}
    (header : ConstructorResultHeader env constructor name levels arguments) :
    arguments.length = info.nparams + info.numFields ∧
      header.result = mkApps (.const name levels) (arguments.take info.nparams) := by
  subst constructor
  exact header.registered_result henv registered unindexed levelCount

end Lean4Lean.AnchoredSemantics
