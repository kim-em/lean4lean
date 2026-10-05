import Lean4Lean.Theory.Typing.AnchoredNativeTemplateRealization
import Lean4Lean.Theory.Typing.AnchoredConstantTelescope
import Lean4Lean.Theory.Typing.ProjectionLemmas

/-! A primitive field certificate factors through its literal declaration
row. The finite ledger retains each original parameter and earlier projection
observer required by that certificate; raw major typing alone does not supply
those requests. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- Extract the exact original constructor-domain template and its actual
source operand cuts. This is syntax factoring, so it neither assumes new
source semantics nor infers equality between assigned field types. -/
theorem CodeCert.factorProjectionType
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
    (newLocals : List Nat) :
    ∃ required,
      Nonempty (CodeCert env U registry target newLocals
        (nativeCaptureSubst ((parameters ++ (List.range index).map
          (fun field => VExpr.proj name field major)).map (·.subst σ)))
        (domains[info.nparams + index].instL levels) support required) ∧
      Nonempty (ParamsFootprint env U registry target locals σ
        (parameters ++ (List.range index).map (fun field => VExpr.proj name field major)) footprint required) := by
  have literal := info.fieldType_eq_instOuter shape levelCount parameterCount fieldBound
    (typeName := name) (major := major)
  have equal := Option.some.inj (selected.symm.trans literal)
  rw [equal] at certificate
  let signature : ConstantTelescope info.ctorType := ⟨domains, result, shape⟩
  have scope := signature.domain_scope closed (List.getElem?_eq_getElem fieldBound)
  have instantiated : (domains[info.nparams + index].instL levels).ClosedN
      (parameters ++ (List.range index).map (fun field => VExpr.proj name field major)).length := by
    simpa only [List.length_append, List.length_map, List.length_range, parameterCount] using scope.instL
  exact certificate.factorNativeTemplate instantiated newLocals

end Lean4Lean.AnchoredSource.Adapted
