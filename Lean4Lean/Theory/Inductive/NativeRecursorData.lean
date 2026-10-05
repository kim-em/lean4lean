import Lean4Lean.Theory.Inductive.SingletonReconstruction
import Lean4Lean.Theory.Inductive.CaseReductionData

/-! Pure native recursor occurrence metadata. Every field is generated from
one compilation instance and its case schema; no typing relation, matching
oracle, or arbitrary replacement term is part of the data. -/

namespace Lean4Lean.InductiveSignature

structure NativeRecursorData where
  block : Name
  schema : CaseSchema
  owner : Fin schema.signature.families.size
  uvars : Nat
  levels : List VLevel
  target : VLevel

namespace NativeRecursorData

def ofInstance (block : Name) (schema : CaseSchema) (g : Instance schema.signature)
    (owner : Fin schema.signature.families.size) : NativeRecursorData :=
  ⟨block, schema, owner, g.uvars, g.levels, g.targetLevel⟩

def name (data : NativeRecursorData) : Name :=
  data.schema.restoration.recursorName (data.schema.signature.families[data.owner].name.str "rec")

def numParams (data : NativeRecursorData) : Nat := data.schema.signature.params.length

def indexOffset (data : NativeRecursorData) : Nat :=
  data.numParams + data.schema.signature.families.size + data.schema.signature.constructors.size

def numIndices (data : NativeRecursorData) : Nat :=
  data.schema.signature.families[data.owner].indices.length

def majorOffset (data : NativeRecursorData) : Nat := data.indexOffset + data.numIndices

/-- The native instance's actual source universe substitution, including
parameter-specialized auxiliary recursors. -/
def sourceLevels (data : NativeRecursorData) (packed : List VLevel) : List VLevel :=
  data.levels.map (·.inst packed)

/-- Rebuild the constructor at one exactly saturated native occurrence.
Offsets belong to the full mutual native recursor, while field projections
use the selected one-family case schema. Extra application arguments remain
outside this head computation. -/
def reconstruct (data : NativeRecursorData) (U : Nat) (packed fieldSorts : List VLevel)
    (arguments : List VExpr) : Option VExpr := do
  if packed.length != data.uvars || arguments.length != data.majorOffset + 1 then none else
  let major ← arguments[data.majorOffset]?
  data.schema.singletonReconstructAt data.block data.owner U (data.sourceLevels packed) fieldSorts
    (arguments.take data.numParams)
    ((arguments.drop data.indexOffset).take data.numIndices) major

/-- Canonical reconstruction uses index selectors wherever possible and
Prop selectors for every remaining field. The native compilation's singleton
elimination evidence must justify those remaining proof fields. The sort
annotations do not choose any reconstructed value. -/
def reconstructCanonical (data : NativeRecursorData) (U : Nat) (packed : List VLevel)
    (arguments : List VExpr) : Option VExpr := do
  let source ← data.schema.projectionData data.owner (data.sourceLevels packed)
  data.reconstruct U packed (List.replicate source.fields.length .zero) arguments

/-- The reconstructed application has the same native head, universe spine,
parameters, motives, minors, and indices. Only the major is generated anew. -/
def reconstructedApplication (data : NativeRecursorData) (U : Nat)
    (packed fieldSorts : List VLevel) (arguments : List VExpr) : Option VExpr := do
  let constructor ← data.reconstruct U packed fieldSorts arguments
  return VExpr.mkApps (.const data.name packed)
    (arguments.take data.majorOffset ++ [constructor])

/-- Recover a fixed-length native telescope without inspecting the
possibly functional result of the recursor. -/
def takeForalls : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, type => some ([], type)
  | n + 1, .forallE domain body => do
    let (domains, result) ← takeForalls n body
    return (domain :: domains, result)
  | _ + 1, _ => none

/-- The actual native instance retained by finite compilation. -/
def nativeInstance (data : NativeRecursorData) : Instance data.schema.signature := {
  uvars := data.uvars
  levels := data.levels
  targetLevel := data.target
  recursorName := fun owner => data.schema.signature.families[owner].name.str "rec" }

/-- The unique native singleton equation, after exact restoration. -/
def singletonEquation (data : NativeRecursorData) : Option VDefEq := do
  let s := data.schema.signature
  let [ctorIndex] := (List.finRange s.constructors.size).filter
    (fun i => s.constructors[i].owner == data.owner) | none
  data.schema.restoration.equation (data.nativeInstance.equation ctorIndex)

/-- The exact restored recursor type; constrained indices are retained. -/
def recursorType (data : NativeRecursorData) : Option VExpr :=
  data.schema.restoration.expr (data.nativeInstance.recursorType data.owner)

theorem singletonEquation_uvars {data : NativeRecursorData} {equation : VDefEq}
    (h : data.singletonEquation = some equation) : equation.uvars = data.uvars := by
  unfold singletonEquation at h
  dsimp only at h
  split at h <;> try contradiction
  unfold Restoration.equation at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨lhs, _, rhs, _, type, _, h⟩ := h
  cases h
  rfl

theorem takeForalls_length (h : takeForalls count type = some (domains, result)) :
    domains.length = count := by
  induction count generalizing type domains result with
  | zero => simp only [takeForalls, Option.some.injEq, Prod.mk.injEq] at h; cases h.1; rfl
  | succ count ih =>
    cases type <;> simp only [takeForalls] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ds, body⟩, ht, he⟩ := h
    cases he
    simpa using congrArg Nat.succ (ih ht)

/-- Whether the native generic elimination universe admits Type-valued
instances. The source universe is tested at each occurrence, not globally. -/
def largeTarget (data : NativeRecursorData) : Bool :=
  data.target.eval (List.replicate data.uvars 1) != 0

/-- Source sort at the native occurrence's actual universe specialization. -/
def sourceLevel (data : NativeRecursorData) (packed : List VLevel) : VLevel :=
  (data.schema.sourceLevel data.owner data.levels).inst packed

/-- Only unconstrained constructor indices permit a delta function at the
bare recursor constant. A general indexed singleton still needs its actual
indices before reconstruction can be checked. -/
def unconstrainedSingleton (data : NativeRecursorData) : Bool :=
  match data.schema.projectionData data.owner data.levels with
  | none => false
  | some projection => projection.unconstrainedIndices

end NativeRecursorData
end Lean4Lean.InductiveSignature
