import Lean4Lean.Theory.Typing.SingletonExtraction
import Lean4Lean.Theory.Typing.NativeSingletonTyping
import Lean4Lean.Theory.Inductive.RecursorData

/-! # Singleton extraction data of a native recursor

The cast specification and the elimination into `Prop` of a registered native recursor
of a large-eliminating inductive proposition, at an occurrence's universes. Pure
definitions; their well-formedness is `NativeRecursorData.propElim_wf`
(`NativeSingletonPropElim.lean`). -/

namespace Lean4Lean
open VExpr InductiveSignature VEnv

namespace InductiveSignature.NativeRecursorData

/-- Universe instantiation of a cast specification. -/
def _root_.Lean4Lean.CastSpec.instL (S : CastSpec) (ls : List VLevel) : CastSpec where
  fields := S.fields.map (·.instL ls)
  indices := S.indices.map (·.instL ls)
  slot := S.slot
  sorts := S.sorts.map (·.inst ls)

/-- The free elimination universe parameter. -/
def targetParam (data : NativeRecursorData) : Option Nat :=
  match data.target with
  | .param k => some k
  | _ => none

/-- The owner's unique constructor. -/
def singletonCtor (data : NativeRecursorData) : Option (Fin data.schema.signature.constructors.size) :=
  match (List.finRange data.schema.signature.constructors.size).filter
      (fun i => data.schema.signature.constructors[i].owner == data.owner) with
  | [i] => some i
  | _ => none

/-- The sorts of the data fields, chosen at the generic universes. Proof fields get `Prop`. -/
noncomputable def genericSorts (env : VEnv) (data : NativeRecursorData)
    (c : Constructor data.schema.signature.families.size) : List VLevel :=
  (List.range (data.nativeInstance.sFields c).length).map fun i =>
    match fieldSlot (data.nativeInstance.sCtorIndices c) (data.nativeInstance.sFields c).length i with
    | some _ => Classical.epsilon fun u =>
      env.HasType data.uvars
        (data.nativeInstance.params ++ (data.nativeInstance.sFields c).take i).reverse
        ((data.nativeInstance.sFields c).getD i default) (.sort u)
    | none => .zero

/-- The cast specification at the generic universes. -/
noncomputable def castSpecGeneric (env : VEnv) (data : NativeRecursorData) : Option CastSpec := do
  let i ← data.singletonCtor
  let c := data.schema.signature.constructors[i]
  return data.nativeInstance.singletonCast data.owner c (data.genericSorts env c)

/-- The cast specification at an occurrence's universes: the generic one, instantiated. -/
noncomputable def castSpec (env : VEnv) (data : NativeRecursorData) (packed : List VLevel) :
    Option CastSpec :=
  (data.castSpecGeneric env).map (·.instL packed)

/-- The parameter telescope at an occurrence's universes. -/
def propParams (data : NativeRecursorData) (packed : List VLevel) : List VExpr :=
  data.nativeInstance.params.map (·.instL packed)

/-- Elimination into `Prop` through the native recursor itself, at an occurrence's universes
with the free elimination universe set to zero. -/
def propElim (data : NativeRecursorData) (packed : List VLevel) : Option PropElim := do
  let k ← data.targetParam
  let i ← data.singletonCtor
  return (data.nativeInstance.specialize 0 (packed.set k .zero)).singletonElim data.owner
    data.schema.signature.constructors[i] (.const data.name (packed.set k .zero))

end InductiveSignature.NativeRecursorData
end Lean4Lean
