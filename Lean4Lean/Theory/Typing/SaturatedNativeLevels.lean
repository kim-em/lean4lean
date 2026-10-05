import Lean4Lean.Theory.Inductive.SaturatedNativeProgram
import Lean4Lean.Theory.Typing.SingletonReconstructionLevelCongruence

/-! The saturated native machine makes the same structural choices at
equivalent universe instances. Its generated proof contexts may differ
literally, but their domains and final expressions remain level equivalent.
This result concerns the actual generator, without a typing or replay premise. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr VEnv CaseSchema

private theorem related_take {R : α → β → Prop} (h : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.take n) (ys.take n) := by
  induction h generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

private theorem related_drop {R : α → β → Prop} (h : List.Forall₂ R xs ys) (n : Nat) :
    List.Forall₂ R (xs.drop n) (ys.drop n) := by
  induction h generalizing n with
  | nil => simp
  | cons h hs ih => cases n with
    | zero => exact .cons h hs
    | succ n => exact ih n

private theorem related_append {R : α → β → Prop}
    (h : List.Forall₂ R xs ys) (h' : List.Forall₂ R xs' ys') :
    List.Forall₂ R (xs ++ xs') (ys ++ ys') := by
  induction h with
  | nil => exact h'
  | cons h hs ih => exact .cons h ih

private theorem related_get {R : α → β → Prop}
    {i : Nat} (h : List.Forall₂ R xs ys) (hx : xs[i]? = some x) :
    ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | cons h hs ih => cases i with
    | zero => cases hx; exact ⟨_, rfl, h⟩
    | succ i => exact ih hx

private theorem related_lift (h : List.Forall₂ (EqUpToLevels U) xs ys) (n : Nat) :
    List.Forall₂ (EqUpToLevels U) (xs.map (·.liftN n)) (ys.map (·.liftN n)) := by
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.weakN) h

inductive CaptureInstruction.LevelEquiv (U : Nat) : CaptureInstruction → CaptureInstruction → Prop
  | index {domain domain' : VExpr} {slot : Nat} : EqUpToLevels U domain domain' →
      LevelEquiv U (.index domain slot) (.index domain' slot)
  | proof {domain domain' : VExpr} : EqUpToLevels U domain domain' →
      LevelEquiv U (.proof domain) (.proof domain')

structure SaturatedCaptureState.LevelEquiv (U : Nat) (state state' : SaturatedCaptureState) : Prop where
  added : List.Forall₂ (EqUpToLevels U) state.added state'.added
  captures : List.Forall₂ (EqUpToLevels U) state.captures state'.captures

theorem SaturatedCaptureState.LevelEquiv.step
    (stateEq : SaturatedCaptureState.LevelEquiv U state state')
    (indicesEq : List.Forall₂ (EqUpToLevels U) indices indices')
    (instructionEq : CaptureInstruction.LevelEquiv U instruction instruction')
    (selected : state.step indices instruction = some next) :
    ∃ next', state'.step indices' instruction' = some next' ∧
      SaturatedCaptureState.LevelEquiv U next next' := by
  cases instructionEq with
  | index domains =>
    simp only [SaturatedCaptureState.step, bind, Option.bind_eq_some_iff] at selected
    obtain ⟨value, hvalue, selected⟩ := selected
    cases selected
    obtain ⟨value', hvalue', values⟩ := related_get indicesEq hvalue
    refine ⟨{ added := state'.added, captures := state'.captures ++ [value'.liftN state'.added.length] },
      by simp only [SaturatedCaptureState.step, hvalue', bind, Option.bind_some]; rfl,
      stateEq.added, related_append stateEq.captures (.cons ?_ .nil)⟩
    rw [← Lean4Lean.List.Forall₂.length_eq stateEq.added]
    exact values.weakN
  | proof domains =>
    cases selected
    exact ⟨_, rfl, .cons (domains.instantiateParams_args stateEq.captures) stateEq.added,
      related_append (related_lift stateEq.captures 1) (.cons .bvar .nil)⟩

theorem SaturatedCaptureState.LevelEquiv.run
    (stateEq : SaturatedCaptureState.LevelEquiv U state state')
    (indicesEq : List.Forall₂ (EqUpToLevels U) indices indices')
    (instructionsEq : List.Forall₂ (CaptureInstruction.LevelEquiv U) instructions instructions')
    (selected : state.run indices instructions = some final) :
    ∃ final', state'.run indices' instructions' = some final' ∧
      SaturatedCaptureState.LevelEquiv U final final' := by
  induction instructionsEq generalizing state state' with
  | nil => cases selected; exact ⟨_, rfl, stateEq⟩
  | cons instructionEq _ ih =>
    simp only [SaturatedCaptureState.run, bind, Option.bind_eq_some_iff] at selected
    obtain ⟨next, hnext, hfinal⟩ := selected
    obtain ⟨next', hnext', nextEq⟩ := stateEq.step indicesEq instructionEq hnext
    obtain ⟨final', hfinal', finalEq⟩ := ih nextEq hfinal
    refine ⟨final', ?_, finalEq⟩
    simp only [SaturatedCaptureState.run, hnext', bind, Option.bind_some]
    exact hfinal'

theorem fieldInstructions_levels (sourceEq : ProjectionData.LevelEquiv U source source')
    (domainsEq : List.Forall₂ (EqUpToLevels U) domains domains') :
    List.Forall₂ (CaptureInstruction.LevelEquiv U)
      (fieldInstructions source domains) (fieldInstructions source' domains') := by
  unfold fieldInstructions
  suffices ∀ start, List.Forall₂ (CaptureInstruction.LevelEquiv U)
      ((domains.zipIdx start).map fun (domain, field) =>
        match source.fieldIndex field with
        | some slot => .index domain slot | none => .proof domain)
      ((domains'.zipIdx start).map fun (domain, field) =>
        match source'.fieldIndex field with
        | some slot => .index domain slot | none => .proof domain) from this 0
  intro start
  induction domainsEq generalizing start with
  | nil => exact .nil
  | cons domainEq _ ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    apply List.Forall₂.cons ?_ (ih _)
    rw [← sourceEq.fieldIndex]
    split
    · exact .index domainEq
    · exact .proof domainEq

structure SaturatedProgram.LevelEquiv (U : Nat) (program program' : SaturatedProgram data) : Prop where
  levels : List.Forall₂ (· ≈ ·) program.levels program'.levels
  levels_left : ∀ level ∈ program.levels, level.WF U
  levels_right : ∀ level ∈ program'.levels, level.WF U
  prefixArgs : List.Forall₂ (EqUpToLevels U) program.prefixArgs program'.prefixArgs
  trailing : List.Forall₂ (EqUpToLevels U) program.trailing program'.trailing
  major : EqUpToLevels U program.major program'.major
  source : ProjectionData.LevelEquiv U program.source program'.source
  equation : program.equation = program'.equation
  equationBody : program.equationBody = program'.equationBody
  instructions : List.Forall₂ (CaptureInstruction.LevelEquiv U) program.instructions program'.instructions
  state : SaturatedCaptureState.LevelEquiv U program.state program'.state

theorem SaturatedProgram.LevelEquiv.rhs (h : SaturatedProgram.LevelEquiv U program program') :
    EqUpToLevels U program.rhs program'.rhs := by
  unfold SaturatedProgram.rhs
  rw [← h.equationBody]
  exact (EqUpToLevels.instL_expr _ h.levels_left h.levels_right h.levels).instantiateParams_args
    h.state.captures

theorem SaturatedProgram.LevelEquiv.result (h : SaturatedProgram.LevelEquiv U program program') :
    EqUpToLevels U program.result program'.result := by
  apply h.rhs.mkApps_args
  rw [← Lean4Lean.List.Forall₂.length_eq h.state.added]
  exact related_lift h.trailing _

theorem saturatedProgram_levels {data : NativeRecursorData} {levels levels' : List VLevel}
    {program : SaturatedProgram data}
    (hl : ∀ level ∈ levels, level.WF U) (hl' : ∀ level ∈ levels', level.WF U)
    (he : List.Forall₂ (· ≈ ·) levels levels')
    (ha : List.Forall₂ (EqUpToLevels U) args args')
    (selected : data.saturatedProgram levels args = some program) :
    ∃ program', data.saturatedProgram levels' args' = some program' ∧
      SaturatedProgram.LevelEquiv U program program' := by
  have hlen := Lean4Lean.List.Forall₂.length_eq he
  have hargslen := Lean4Lean.List.Forall₂.length_eq ha
  have sourceLevelsEq : List.Forall₂ (· ≈ ·) (data.sourceLevels levels) (data.sourceLevels levels') := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.rfl fun _ _ => VLevel.inst_congr rfl he
  have sourceLevelsWF : ∀ level ∈ data.sourceLevels levels, level.WF U :=
    List.forall_mem_map.mpr fun _ _ => VLevel.WF.inst hl
  have sourceLevelsWF' : ∀ level ∈ data.sourceLevels levels', level.WF U :=
    List.forall_mem_map.mpr fun _ _ => VLevel.WF.inst hl'
  unfold saturatedProgram at selected ⊢
  simp only [← hlen]
  split at selected <;> try contradiction
  rename_i hguard
  rw [if_neg hguard]
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨⟨prefixArgs, trailing⟩, hsplit, major, hmajor, source, hsource, selected⟩ := selected
  obtain ⟨hprefixlen, _, rfl, rfl⟩ := splitSaturated_spec hsplit
  have hsplit' : splitSaturated (data.majorOffset + 1) args' =
      some (args'.take (data.majorOffset + 1), args'.drop (data.majorOffset + 1)) := by
    have enough : data.majorOffset + 1 ≤ args.length := by
      simp only [List.length_take] at hprefixlen
      omega
    simp only [splitSaturated, ← hargslen, if_pos enough]
  have prefixEq := related_take ha (data.majorOffset + 1)
  obtain ⟨major', hmajor', majorEq⟩ := related_get prefixEq hmajor
  obtain ⟨source', hsource', sourceEq⟩ := projectionData_levels
    sourceLevelsWF sourceLevelsWF' sourceLevelsEq hsource
  simp only [bind, hsplit', hmajor', hsource', Option.bind_some]
  rw [← Lean4Lean.List.Forall₂.length_eq sourceEq.params,
    ← Lean4Lean.List.Forall₂.length_eq sourceEq.indices,
    ← Lean4Lean.List.Forall₂.length_eq sourceEq.constructorIndices]
  split at selected <;> try contradiction
  rename_i hsourceGuard
  rw [if_neg hsourceGuard]
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨equation, hequation, body, hbody, selected⟩ := selected
  simp only [bind, hequation, hbody, Option.bind_some]
  rw [← Lean4Lean.List.Forall₂.length_eq sourceEq.fields]
  split at selected <;> try contradiction
  rename_i hbodyGuard
  rw [if_neg hbodyGuard]
  split at selected <;> try contradiction
  rename_i hheadGuard
  rw [if_neg hheadGuard]
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨state, hstate, selected⟩ := selected
  cases selected
  have domainsEq : List.Forall₂ (EqUpToLevels U)
      ((body.domains.drop data.indexOffset).map (·.instL levels))
      ((body.domains.drop data.indexOffset).map (·.instL levels')) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact Lean4Lean.List.Forall₂.rfl fun _ _ => EqUpToLevels.instL_expr _ hl hl' he
  have instructionsEq := fieldInstructions_levels sourceEq domainsEq
  have initialEq : SaturatedCaptureState.LevelEquiv U
      ⟨[], (args.take (data.majorOffset + 1)).take data.indexOffset⟩
      ⟨[], (args'.take (data.majorOffset + 1)).take data.indexOffset⟩ :=
    ⟨.nil, related_take prefixEq _⟩
  obtain ⟨state', hstate', stateEq⟩ := initialEq.run
    (related_take (related_drop prefixEq _) _) instructionsEq hstate
  exact ⟨⟨levels', args'.take (data.majorOffset + 1), args'.drop (data.majorOffset + 1),
      major', source', equation, body, _, state'⟩,
    by simp only [bind, hstate', Option.bind_some]; rfl,
    he, hl, hl', prefixEq, related_drop ha _, majorEq, sourceEq, rfl, rfl, instructionsEq, stateEq⟩

end Lean4Lean.InductiveSignature.NativeRecursorData
