import Lean4Lean.Theory.Typing.SingletonReconstructionUniverses
import Lean4Lean.Theory.Inductive.NativePrefixProgram
import Lean4Lean.Theory.Typing.NativeSingletonProgram

/-! Specializing occurrence universes in the actual native prefix program.
The stored equation and parsed equation body remain the installed templates. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema
variable {levels packed : List VLevel} {args : List VExpr} {type : VExpr}

@[simp] theorem sourceLevels_inst (data : NativeRecursorData) :
    data.sourceLevels (levels.map (·.inst packed)) =
      (data.sourceLevels levels).map (·.inst packed) := by
  simp only [sourceLevels, List.map_map, Function.comp_def, VLevel.inst_inst]

theorem reconstruct_instL {data : NativeRecursorData}
    (H : data.reconstruct U levels targets args = some output)
    (hw : ∀ l ∈ packed, l.WF U') :
    data.reconstruct U' (levels.map (·.inst packed)) (targets.map (·.inst packed))
      (args.map (VExpr.instL packed)) = some (output.instL packed) := by
  unfold reconstruct at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨major, hmajor, H⟩ := H
  have H' := singletonReconstructAt_instL H hw
  simp only [List.getElem?_map, hmajor, Option.map_some, bind, Option.bind_some,
    sourceLevels_inst, ← List.map_take, ← List.map_drop]
  exact H'

theorem reconstructCanonical_instL {data : NativeRecursorData}
    (H : data.reconstructCanonical U levels args = some output)
    (hw : ∀ l ∈ packed, l.WF U') :
    data.reconstructCanonical U' (levels.map (·.inst packed))
      (args.map (VExpr.instL packed)) = some (output.instL packed) := by
  unfold reconstructCanonical at H ⊢
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨source, hsource, H⟩ := H
  simp only [sourceLevels_inst, projectionData_instL hsource, bind, Option.bind_some,
    ProjectionData.instL, List.length_map]
  simpa only [List.map_replicate, VLevel.inst] using reconstruct_instL H hw

theorem supplyType_instL (H : supplyType args type = some output) :
    supplyType (args.map (VExpr.instL packed)) (type.instL packed) = some (output.instL packed) := by
  induction args generalizing type with
  | nil => cases H; rfl
  | cons arg args ih =>
    cases type <;> try contradiction
    simp only [supplyType, List.map_cons, VExpr.instL, ← VExpr.instL_instN]
    exact ih H

theorem takeForalls_instL (H : takeForalls count type = some (domains, result)) :
    takeForalls count (type.instL packed) =
      some (domains.map (VExpr.instL packed), result.instL packed) := by
  induction count generalizing type domains result with
  | zero => cases H; rfl
  | succ count ih =>
    cases type <;> try contradiction
    simp only [takeForalls, bind, Option.bind_eq_some_iff] at H
    obtain ⟨⟨ds, body⟩, ht, he⟩ := H
    cases he
    simp only [VExpr.instL, takeForalls, bind, ih ht, Option.bind_some,
      Option.pure_def, List.map_cons]

def PrefixProgram.instL (program : PrefixProgram) (packed : List VLevel) : PrefixProgram :=
  { program with
    domains := program.domains.map (VExpr.instL packed)
    result := program.result.instL packed
    constructor := program.constructor.instL packed
    captures := program.captures.map (VExpr.instL packed)
    levels := program.levels.map (·.inst packed) }

@[simp] theorem PrefixProgram.rhs_instL (program : PrefixProgram) :
    (program.instL packed).rhs = program.rhs.instL packed := by
  simp only [PrefixProgram.instL, PrefixProgram.rhs, VExpr.instL_wrapLams,
    instantiateParams_instL, VExpr.instL_instL]

@[simp] theorem PrefixProgram.type_instL (program : PrefixProgram) :
    (program.instL packed).type = program.type.instL packed := by
  simp only [PrefixProgram.instL, PrefixProgram.type, VExpr.instL_wrapForalls]

theorem prefixProgram_instL {data : NativeRecursorData} {program : PrefixProgram}
    (H : data.prefixProgram U levels args = some program)
    (hw : ∀ l ∈ packed, l.WF U') :
    data.prefixProgram U' (levels.map (·.inst packed)) (args.map (VExpr.instL packed)) =
      some (program.instL packed) := by
  unfold prefixProgram at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨nativeType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    constructor, hconstructor, source, hsource, fields, hfields,
    equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptures
  cases H
  have hsupply' := supplyType_instL (packed := packed) hsupply
  rw [VExpr.instL_instL] at hsupply'
  have htake' := takeForalls_instL (packed := packed) htake
  have hvars (n k : Nat) : (vars n k).map (VExpr.instL packed) = vars n k := by
    simp [vars, List.map_map, Function.comp_def, VExpr.instL]
  let remaining := data.majorOffset + 1 - args.length
  have hall : (args.map (VExpr.instL packed)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (VExpr.instL packed) := by
    simp only [List.map_append, List.map_map, Function.comp_def, VExpr.instL_liftN, hvars]
  have hconstructor' := reconstructCanonical_instL hconstructor hw
  rw [← hall] at hconstructor'
  dsimp only [remaining] at hconstructor'
  have hsource' := projectionData_instL (packed := packed) hsource
  rw [← sourceLevels_inst] at hsource'
  have hfields' := source.reconstructionPrefix_instL (packed := packed) hfields
  simp only [List.map_replicate, VLevel.inst, List.map_nil, ← sourceLevels_inst] at hfields'
  simp only [bind, htype, Option.bind_some, hsupply', htake', hconstructor', hsource',
    ProjectionData.instL, List.length_map, hequation, hbody]
  have hfields'' := hfields'
  simp only [ProjectionData.instL] at hfields''
  rw [hfields'']
  simp only [Option.bind_some]
  simp only [List.length_append, List.length_map, List.length_take] at hcaptures ⊢
  rw [if_neg hcaptures]
  simp only [Option.pure_def, Option.some.injEq, PrefixProgram.instL,
    PrefixProgram.mk.injEq, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_take, List.map_drop, List.map_map,
    Function.comp_def, VExpr.instL_mkApps, ProjectionFunction.instL,
    List.map_cons, List.map_nil, VExpr.instL]

theorem singletonProgram_instL {data : NativeRecursorData} {program : PrefixProgram} {env : VEnv}
    (hr : VEnv.NativeRecursorRegistered env data)
    (H : data.singletonProgram env U levels args = some program) :
    data.singletonProgram env U' (levels.map (·.inst packed)) (args.map (VExpr.instL packed)) =
      some (program.instL packed) := by
  unfold singletonProgram at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨nativeType, htype, residual, hsupply, ⟨domains, result⟩, htake,
    ⟨constructor, fields⟩, hrecon, equation, hequation, body, hbody, H⟩ := H
  split at H <;> try contradiction
  rename_i hcaptures
  cases H
  have hsupply' := supplyType_instL (packed := packed) hsupply
  rw [VExpr.instL_instL] at hsupply'
  have htake' := takeForalls_instL (packed := packed) htake
  have hvars (n k : Nat) : (vars n k).map (VExpr.instL packed) = vars n k := by
    simp [vars, List.map_map, Function.comp_def, VExpr.instL]
  let remaining := data.majorOffset + 1 - args.length
  have hall : (args.map (VExpr.instL packed)).map (·.liftN remaining) ++ vars remaining 0 =
      (args.map (·.liftN remaining) ++ vars remaining 0).map (VExpr.instL packed) := by
    simp only [List.map_append, List.map_map, Function.comp_def, VExpr.instL_liftN, hvars]
  have hrecon' := singletonRecon_instL (packed := packed) hrecon
  rw [← hall] at hrecon'
  dsimp only [remaining] at hrecon'
  simp only [bind, htype, Option.bind_some, hsupply', htake', hrecon', hequation, hbody]
  simp only [List.length_append, List.length_map, List.length_take] at hcaptures ⊢
  rw [if_neg hcaptures]
  simp only [Option.pure_def, Option.some.injEq, PrefixProgram.instL,
    PrefixProgram.mk.injEq, and_true, true_and]
  dsimp only [remaining] at hall
  rw [hall]
  simp only [List.map_append, List.map_take]

end Lean4Lean.InductiveSignature.NativeRecursorData
