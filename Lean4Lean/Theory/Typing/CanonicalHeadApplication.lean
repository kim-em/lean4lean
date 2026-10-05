import Lean4Lean.Theory.Typing.CanonicalHeadTrace
import Lean4Lean.Theory.Inductive.Formation

/-! Appending applications preserves an already selected canonical step.
Native saturation continues to stop at the major; the appended argument is
lifted through exactly the same generated proof telescope. -/
namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr

private theorem splitSaturated_append
    (selected : splitSaturated count arguments = some (prefixArgs, trailing)) (last : VExpr) :
    splitSaturated count (arguments ++ [last]) = some (prefixArgs, trailing ++ [last]) := by
  obtain ⟨length, rfl, _, _⟩ := splitSaturated_spec selected
  simp only [splitSaturated, List.length_append, List.length_singleton]
  rw [if_pos (by omega)]
  simp only [List.append_assoc, ← length, List.take_left, List.drop_left]

/-- Saturation metadata and captures are unchanged by a trailing argument. -/
theorem saturatedProgram_append {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program) (last : VExpr) :
    data.saturatedProgram levels (arguments ++ [last]) =
      some { program with trailing := program.trailing ++ [last] } := by
  unfold saturatedProgram at selected
  dsimp only at selected
  split at selected <;> try contradiction
  rename_i hlevels
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨⟨prefixArgs, trailing⟩, hsplit, major, hmajor, source, hsource, h⟩ := selected
  split at h <;> try contradiction
  rename_i hsourceCounts
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨equation, hequation, body, hbody, h⟩ := h
  split at h <;> try contradiction
  rename_i hdomains
  split at h <;> try contradiction
  rename_i hhead
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨state, hrun, h⟩ := h
  cases h
  simp only [saturatedProgram, hlevels, splitSaturated_append hsplit last,
    bind, Option.bind_some, hmajor, hsource, hsourceCounts,
    hequation, hbody, hdomains, hhead, hrun]
  rfl

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.CanonicalHead
open VExpr InductiveSignature NativeRecursorData

private theorem mkApps_last (head : VExpr) (arguments : List VExpr) (last : VExpr) :
    mkApps head (arguments ++ [last]) = .app (mkApps head arguments) last := by
  simp [mkApps, List.foldl_append]

def Output.apply (output : Output) (argument : VExpr) : Output :=
  ⟨output.added, .app output.result (argument.liftN output.added.length)⟩

theorem spineStep_append
    (selected : spineStep registry head arguments = some output) (last : VExpr) :
    spineStep registry head (arguments ++ [last]) = some (output.apply last) := by
  cases spineStep_origin selected with
  | beta =>
    simp only [spineStep, List.cons_append, Output.apply, List.length_nil, liftN_zero, mkApps_last]
  | delta value named levels =>
    simp only [spineStep, value, named, levels, and_self, ↓reduceIte, Output.apply,
      List.length_nil, liftN_zero, mkApps_last]
  | native definition native named program =>
    have h := saturatedProgram_append program last
    simp only [spineStep, definition, native, named, ↓reduceIte, nativeOutput, h,
      Option.map_some, Output.apply, SaturatedProgram.result, List.map_append,
      List.map_singleton, mkApps_last]
    rfl

theorem step_app (selected : step registry expression = some output) (argument : VExpr) :
    step registry (.app expression argument) = some (output.apply argument) := by
  simpa only [step, getAppFnArgs_app] using spineStep_append selected argument

/-- The actual finite trace, including all native fresh proof binders, is
stable under a trailing application. This is the syntactic recursion needed
by function-valued native semantic expansion. -/
theorem Trace.app (trace : Trace registry expression added result) (argument : VExpr) :
    Trace registry (.app expression argument) added (.app result (argument.liftN added.length)) := by
  induction trace generalizing argument with
  | refl => simpa only [List.length_nil, liftN_zero] using Trace.refl (registry := registry)
  | @next expression output added result selected rest ih =>
    have h := Trace.next (step_app selected argument) (ih (argument.liftN output.added.length))
    simpa only [Output.apply, List.length_append, liftN_liftN, Nat.add_comm] using h

end Lean4Lean.CanonicalHead
