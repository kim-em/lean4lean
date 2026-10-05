import Lean4Lean.Theory.Typing.CanonicalDataHead

/-! The extensional structure branch applies the very same generated native
or case equation as ordinary constructor iota. Its fields are the primitive
projections of the exact major being reduced. -/

namespace Lean4Lean.CanonicalDataHead
open VExpr InductiveSignature
set_option backward.isDefEq.respectTransparency false

/-- Supplying the actual family parameters to the eta constructor gives the
exact captures selected by `etaIota`; constructor parameters are not confused
with the recursor's parameter/motive/minor prefix. -/
theorem Rule.run_eta
    {info : VProjectionInfo} {rule : Rule} {selected : Selected} {typeName : Name}
    (constructor : info.ctorName = rule.constructor)
    (arity : rule.constructorArity = info.nparams + info.numFields)
    (fields : rule.fieldCount = info.numFields)
    (levelCount : selected.levels.length = rule.equation.uvars)
    (prefixCount : rule.prefixCount ≤ selected.arguments.length)
    {params : List VExpr} (paramCount : params.length = info.nparams)
    (levels : List VLevel) (major : VExpr) :
    rule.run selected
      (mkApps (.const info.ctorName levels)
        (params ++ (List.range info.numFields).map (fun index => VExpr.proj typeName index major))) =
      some (mkApps (rule.equation.rhs.instL selected.levels)
        (selected.arguments.take rule.prefixCount ++
          (List.range info.numFields).map (fun index => VExpr.proj typeName index major))) := by
  have enough : rule.fieldCount ≤
      (params ++ (List.range info.numFields).map (fun index => VExpr.proj typeName index major)).length := by
    simp only [List.length_append, List.length_map, List.length_range, paramCount, fields]
    omega
  have counts :
      (params ++ (List.range info.numFields).map (fun index => VExpr.proj typeName index major)).length =
        rule.constructorArity := by
    simp only [List.length_append, List.length_map, List.length_range, paramCount, arity]
  have enough' : rule.fieldCount ≤ rule.constructorArity := counts ▸ enough
  unfold Rule.run
  rw [spine_mkApps_exact _ _ (by rfl)]
  simp only [constructor, counts, levelCount,
    prefixCount, enough', and_self, ↓reduceIte]
  congr 2
  simp only [Rule.captures, List.length_append, List.length_map, List.length_range,
    fields, Nat.add_sub_cancel, List.drop_left]

/-- A successful extensional machine step carries an actual generated rule
whose ordinary constructor application computes precisely the emitted RHS.
Typed consumers supply the parameters and universes from their eta origin. -/
theorem etaIota_constructor
    (selected : select registry function = some chosen)
    (reduced : etaIota registry chosen major = some result) :
    ∃ rule entry info, RuleOrigin registry chosen rule ∧
      registry.structureConstructors rule.constructor = some entry ∧
      registry.projections entry.typeName = some info ∧
      info.ctorName = rule.constructor ∧ info.nindices = 0 ∧
      rule.constructorArity = info.nparams + info.numFields ∧
      ∀ (params : List VExpr), params.length = info.nparams → ∀ levels,
        rule.run chosen
          (mkApps (.const info.ctorName levels)
            (params ++ (List.range info.numFields).map
              (fun index => VExpr.proj entry.typeName index major))) = some result := by
  obtain ⟨rule, entry, info, _, origin, reverse, projection, constructor, noIndices,
    arity, fields, levelCount, prefixCount, resultEq⟩ := etaIota_origin selected reduced
  refine ⟨rule, entry, info, origin, reverse, projection, constructor, noIndices, arity, ?_⟩
  intro params paramCount levels
  rw [resultEq]
  exact rule.run_eta constructor arity fields levelCount prefixCount paramCount levels major

end Lean4Lean.CanonicalDataHead
