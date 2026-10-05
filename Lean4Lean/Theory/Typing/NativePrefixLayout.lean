import Lean4Lean.Theory.Typing.NativePrefixArity

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema
variable {levels : List VLevel}

def prefixArguments (data : NativeRecursorData) (args : List VExpr) : List VExpr :=
  let remaining := data.majorOffset + 1 - args.length
  args.map (·.liftN remaining) ++ vars remaining 0

def prefixProjectionArguments (data : NativeRecursorData) (args : List VExpr) : List VExpr :=
  let allArgs := data.prefixArguments args
  allArgs.take data.numParams ++ (allArgs.drop data.indexOffset).take data.numIndices ++ [.bvar 0]

theorem prefixArguments_major {data : NativeRecursorData} (h : args.length ≤ data.majorOffset) :
    (data.prefixArguments args)[data.majorOffset]? = some (.bvar 0) := by
  unfold prefixArguments vars
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.getElem?_map]
  have hb : data.majorOffset - args.length < (List.range (data.majorOffset + 1 - args.length)).reverse.length := by
    simp; omega
  rw [List.getElem?_eq_getElem hb]
  simp only [List.getElem_reverse, List.length_range, List.getElem_range,
    Nat.zero_add, Option.map_some, Option.some.injEq, VExpr.bvar.injEq]
  omega

theorem prefixProgram_layout {data : NativeRecursorData}
    (H : data.prefixProgram U levels args = some program) :
    ∃ source fields,
      data.schema.projectionData data.owner (data.sourceLevels levels) = some source ∧
      source.reconstructionPrefix data.block data.owner.val (data.sourceLevels levels)
        source.fields (List.replicate source.fields.length .zero) [] = some fields ∧
      program.domains.length = data.majorOffset + 1 - args.length ∧
      program.constructor = instantiateParams source.constructor
        ((data.prefixArguments args).take data.numParams ++
          fields.map (fun field => VExpr.mkApps field.value (data.prefixProjectionArguments args))) ∧
      program.captures = (data.prefixArguments args).take data.indexOffset ++
        fields.map (fun field => VExpr.mkApps field.value (data.prefixProjectionArguments args)) := by
  have hbound := (prefixProgram_spec H).1
  unfold prefixProgram at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨type, _, residual, _, ⟨domains, result⟩, htake,
    ctor, hctor, source, hsource, fields, hfields, equation, heq, body, hbody, H⟩ := H
  split at H <;> try contradiction
  cases H
  refine ⟨source, fields, hsource, hfields, takeForalls_length htake, ?_, rfl⟩
  unfold reconstructCanonical at hctor
  simp only [bind, hsource, Option.bind_some] at hctor
  unfold reconstruct at hctor
  split at hctor <;> try contradiction
  change (do let major ← (data.prefixArguments args)[data.majorOffset]?
             data.schema.singletonReconstructAt data.block data.owner U (data.sourceLevels levels)
               (List.replicate source.fields.length .zero)
               ((data.prefixArguments args).take data.numParams)
               (((data.prefixArguments args).drop data.indexOffset).take data.numIndices) major) = some ctor at hctor
  rw [prefixArguments_major hbound] at hctor
  simp only [bind, Option.bind_some] at hctor
  unfold singletonReconstructAt at hctor
  split at hctor <;> try contradiction
  simp only [bind, hsource, Option.bind_some] at hctor
  split at hctor <;> try contradiction
  simp only [hfields, Option.bind_some, Option.pure_def, Option.some.injEq] at hctor
  exact hctor.symm

end Lean4Lean.InductiveSignature.NativeRecursorData
