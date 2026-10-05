import Lean4Lean.Theory.Inductive.SaturatedNativeProgram

/-! Raw native observation metadata, independent of source observations. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr
open InductiveSignature NativeRecursorData

/-- Exact syntax provenance for a copied field. The natural domain is read
from the registered recursor input telescope, while the declared domain is
read from the selected equation's capture instruction. Both have already
received this occurrence's universe instantiation. -/
structure NativeIndexTemplates {data : NativeRecursorData}
    (program : SaturatedProgram data) where
  selected : data.saturatedProgram program.levels (program.prefixArgs ++ program.trailing) = some program
  recursorType : VExpr
  registeredType : data.recursorType = some recursorType
  inputDomains : List VExpr
  result : VExpr
  telescope : NativeRecursorData.takeForalls (data.majorOffset + 1)
    (recursorType.instL program.levels) = some (inputDomains, result)
  field : Nat
  slot : Nat
  naturalDomain : VExpr
  declaredDomain : VExpr
  naturalOrigin : inputDomains[data.indexOffset + slot]? = some naturalDomain
  declaredOrigin : program.instructions[field]? = some (.index declaredDomain slot)

/-- Context order for the literal natural-domain formation child. -/
def NativeIndexTemplates.naturalContext {data : NativeRecursorData}
    {program : SaturatedProgram data} (templates : NativeIndexTemplates program) : List VExpr :=
  (templates.inputDomains.take (data.indexOffset + templates.slot)).reverse

/-- Context order for the literal declared-field formation child, including
all native prefix binders and precisely the earlier constructor fields. -/
def NativeIndexTemplates.declaredContext {data : NativeRecursorData}
    {program : SaturatedProgram data} (templates : NativeIndexTemplates program) : List VExpr :=
  ((program.equationBody.domains.take (data.indexOffset + templates.field)).map
    (·.instL program.levels)).reverse

/-- The substitution used by `instantiateParams`, kept explicit so certificate
children retain their original source templates. Arguments are in declaration
order. Beyond the finite telescope this is the ordinary shifted identity. -/
def nativeCaptureSubst (arguments : List VExpr) : Subst := fun i =>
  if h : i < arguments.length then arguments[arguments.length - 1 - i]
  else .bvar (i - arguments.length)

@[simp] theorem nativeCaptureSubst_spec (expression : VExpr) (arguments : List VExpr) :
    expression.subst (nativeCaptureSubst arguments) = instantiateParams expression arguments := rfl

structure NativeConstantSignature (data : NativeRecursorData) (levels : List VLevel) where
  type : VExpr
  typeOrigin : data.recursorType = some type
  domains : List VExpr
  result : VExpr
  telescope : NativeRecursorData.takeForalls (data.majorOffset + 1)
    (type.instL levels) = some (domains, result)

/-- The restored equation's complete native argument tuple at witnessed
captures, including repeated, constant, and compound result indices. -/
def nativeEquationArguments {data : NativeRecursorData}
    (program : SaturatedProgram data) (witnesses : List VExpr) : List VExpr :=
  ((program.equationBody.lhs.instL program.levels).getAppFnArgs.2).map
    (fun argument => argument.subst (nativeCaptureSubst witnesses))

end Lean4Lean.AnchoredSource.Adapted
