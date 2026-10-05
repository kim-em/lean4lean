import Lean4Lean.Theory.Typing.AnchoredOriginalCaptureFactor
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilySpine
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! Projection field factoring traverses the actual original field-formation
premise once. All parameter and prior-projection cuts keep that original
endpoint and its captured source environment; no residual typing is created.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

/-- The actual original field-formation endpoint factors in one traversal
through its literal selected declaration row. Parameter and prior-projection
cuts therefore share that original root, even when earlier captures occur
inside later ones. -/
theorem CodeCert.factorProjectionTypeOriginal
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {locals : List Nat} {σ : Subst}
    {info : VProjectionInfo} {name : Name} {domains : List VExpr} {result : VExpr}
    (shape : info.ctorType = wrapForalls domains result)
    (closed : info.ctorType.Closed)
    {levels : List VLevel} {parameters : List VExpr} {index : Nat} {major fieldType : VExpr}
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (fieldBound : info.nparams + index < domains.length)
    (selected : info.fieldType name levels parameters index major = some fieldType)
    {support : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target locals σ fieldType support footprint)
    (root : EndpointRef sourceEnv U source fieldType assigned)
    (newLocals : List Nat) :
    ∃ required, Nonempty (CodeCert env U registry target newLocals
      (nativeCaptureSubst ((parameters ++ (List.range index).map
        (fun field => VExpr.proj name field major)).map (·.subst σ)))
      (domains[info.nparams + index].instL levels) support required) ∧
      Nonempty (CaptureFootprint (env := env) root registry target locals σ
        (parameters ++ (List.range index).map (fun field => VExpr.proj name field major)) 0 0
        (fun initial => (Closure.close root.origin initial).cost) footprint required) := by
  have literal := info.fieldType_eq_instOuter shape levelCount parameterCount fieldBound
    (typeName := name) (major := major)
  have equal := Option.some.inj (selected.symm.trans literal)
  let signature : ConstantTelescope info.ctorType := ⟨domains, result, shape⟩
  have scope := signature.domain_scope closed (List.getElem?_eq_getElem fieldBound)
  have instantiated : (domains[info.nparams + index].instL levels).ClosedN
      (parameters ++ (List.range index).map (fun field => VExpr.proj name field major)).length := by
    simpa only [List.length_append, List.length_map, List.length_range, parameterCount] using scope.instL
  exact CodeCert.factorNativeTemplateOriginal certificate root _ _ equal instantiated newLocals


/-- Reindexing a captured parameter query compares its actual field cut
with the actual assigned-family argument endpoint. Both original children
are explicitly reserved by the original projection rule. -/
theorem CaptureFootprint.projectionParameter_schedule
    {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}
    {registry : CanonicalHead.Registry} {locals : List Nat} {σ : Subst}
    {name : Name} {info : VProjectionInfo} {levels : List VLevel}
    {parameters indices : List VExpr} {index : Nat}
    {sourceMajor major otherMajor fieldType : VExpr} {fieldLevel : VLevel}
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : parameters.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels parameters index sourceMajor = some fieldType)
    (fieldLevelWF : fieldLevel.WF U)
    (field : Derivation sourceEnv U source fieldType fieldType (.sort fieldLevel))
    (leftMajor : Derivation sourceEnv U source sourceMajor major
      (mkApps (.const name levels) (parameters ++ indices)))
    (rightMajor : Derivation sourceEnv U source sourceMajor otherMajor
      (mkApps (.const name levels) (parameters ++ indices)))
    (closed : info.ctorType.Closed)
    (elimination : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    {before required : Footprint}
    (cuts : CaptureFootprint (env := env) (.left field) registry target locals σ
      (parameters ++ (List.range index).map (fun prior => .proj name prior sourceMajor))
      0 0 (fun initial => (Closure.close field.origin initial).cost) before required)
    (parameter : Nat) (bound : parameter < parameters.length) (initial : List Closure) :
    schedule .coherence (cuts.cost initial +
      (Closure.close (familyArgument leftMajor parameter
        (by rw [List.getElem?_append_left bound]; exact List.getElem?_eq_getElem bound)).node.origin
        initial).cost) <
      schedule .fundamental (Closure.close
        (Derivation.projDF registered levelsWF levelCount parameterCount indexCount selected
          fieldLevelWF field leftMajor rightMajor closed elimination).origin initial).cost := by
  apply schedule_strict
  exact Nat.lt_of_le_of_lt (Nat.add_le_add (cuts.cost_le initial)
    (familyArgument_cost_le leftMajor parameter _ initial))
    (original_two_children field.origin leftMajor.origin [rightMajor.origin] initial)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
