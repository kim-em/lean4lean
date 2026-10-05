import Batteries.Tactic.OpenPrivate
import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming

/-! Forward substitution of the actual saturated capture program. Fresh
proof binders remain fresh; each domain is substituted beneath its older
proof binders. Only the original equation telescope scopes are required. -/
namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr
set_option backward.isDefEq.respectTransparency false
open private subst_eq_of_scoped from Lean4Lean.Theory.Inductive.SaturatedNativeRenaming

theorem instantiateParams_subst_scoped {e : VExpr} {arguments : List VExpr}
    (scope : e.ClosedN arguments.length) (σ : Subst) :
    (instantiateParams e arguments).subst σ =
      instantiateParams e (arguments.map (·.subst σ)) := by
  unfold instantiateParams
  rw [subst_subst]
  apply subst_eq_of_scoped scope
  intro i hi
  simp only [Subst.comp, List.length_map, dif_pos hi, List.getElem_map]

def substAdded (σ : Subst) : List VExpr → List VExpr
  | [] => []
  | domain :: older => domain.subst (σ.liftN older.length) :: substAdded σ older

@[simp] theorem substAdded_length (σ : Subst) (added : List VExpr) :
    (substAdded σ added).length = added.length := by
  induction added <;> simp [substAdded, *]

def SaturatedCaptureState.subst (state : SaturatedCaptureState) (σ : Subst) :
    SaturatedCaptureState := {
  added := substAdded σ state.added
  captures := state.captures.map (·.subst (σ.liftN state.added.length)) }

theorem liftN_subst_liftN (e : VExpr) (σ : Subst) (n : Nat) :
    (e.liftN n).subst (σ.liftN n) = (e.subst σ).liftN n := by
  induction n with
  | zero => simp only [Subst.liftN, liftN_zero]
  | succ n ih =>
    rw [liftN_succ, Subst.liftN, lift_subst_lift, ih, ← liftN_succ]

theorem SaturatedCaptureState.step_subst
    {state : SaturatedCaptureState} {instruction : CaptureInstruction}
    (scope : instruction.domain.ClosedN state.captures.length) (σ : Subst)
    (indices : List VExpr) :
    (state.subst σ).step (indices.map (·.subst σ)) instruction =
      (state.step indices instruction).map (·.subst σ) := by
  cases instruction with
  | index domain slot =>
    simp only [step, List.getElem?_map]
    cases h : indices[slot]? <;>
      simp [SaturatedCaptureState.subst, List.map_append, liftN_subst_liftN]
  | proof domain =>
    change domain.ClosedN state.captures.length at scope
    have hd := instantiateParams_subst_scoped scope (σ.liftN state.added.length)
    simp only [step, SaturatedCaptureState.subst, substAdded, List.length_cons, List.map_append,
      List.map_map, List.map_cons, List.map_nil, Subst.liftN, VExpr.subst, Subst.lift,
      Option.map_some, Option.some.injEq, SaturatedCaptureState.mk.injEq]
    refine ⟨by rw [hd], ?_⟩
    congr 1
    exact List.map_congr_left fun e _ => (lift_subst_lift (e := e) (σ := σ.liftN state.added.length)).symm

theorem SaturatedCaptureState.run_subst
    {state : SaturatedCaptureState} {instructions : List CaptureInstruction}
    (scope : InstructionsScoped state.captures.length instructions)
    (σ : Subst) (indices : List VExpr) :
    (state.subst σ).run (indices.map (·.subst σ)) instructions =
      (state.run indices instructions).map (·.subst σ) := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [run, state.step_subst scope.1]
    cases ht : state.step indices instruction with
    | none => simp [run, ht]
    | some next =>
      have hone : state.run indices [instruction] = some next := by simp [run, ht]
      have hc := (run_counts hone).1
      have hnext : InstructionsScoped next.captures.length rest := by
        simpa only [InstructionsScoped, List.length_cons, List.length_nil,
          Nat.zero_add, hc] using scope.2
      simpa [run, ht] using ih hnext

def SaturatedProgram.subst (program : SaturatedProgram data) (σ : Subst) :
    SaturatedProgram data := {
  program with
  prefixArgs := program.prefixArgs.map (·.subst σ)
  trailing := program.trailing.map (·.subst σ)
  major := program.major.subst σ
  state := program.state.subst σ }

private theorem splitSaturated_subst
    (h : splitSaturated count arguments = some (prefixArgs, trailing)) (σ : Subst) :
    splitSaturated count (arguments.map (·.subst σ)) =
      some (prefixArgs.map (·.subst σ), trailing.map (·.subst σ)) := by
  unfold splitSaturated at h ⊢
  simp only [List.length_map]
  split at h <;> try contradiction
  rename_i hcount
  cases h
  simp [hcount, List.map_take, List.map_drop]

/-- The successful metadata parser and its instruction choices are unchanged
under substitution of the actual supplied operands. -/
theorem saturatedProgram_subst {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (h : data.saturatedProgram levels arguments = some program)
    (hs : CaptureDomainsScoped 0 program.equationBody.domains) (σ : Subst) :
    data.saturatedProgram levels (arguments.map (·.subst σ)) = some (program.subst σ) := by
  unfold saturatedProgram at h
  dsimp only at h
  split at h <;> try contradiction
  rename_i hlevels
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨prefixArgs, trailing⟩, hsplit, major, hmajor, source, hsource, h⟩ := h
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
  change CaptureDomainsScoped 0 body.domains at hs
  have hprefix := (splitSaturated_spec hsplit).1
  have henough : data.indexOffset ≤ prefixArgs.length := by
    rw [hprefix, majorOffset]
    omega
  have hinstructions : InstructionsScoped (prefixArgs.take data.indexOffset).length
      (fieldInstructions source ((body.domains.drop data.indexOffset).map (·.instL levels))) := by
    unfold InstructionsScoped
    rw [fieldInstructions_domains, List.length_take, Nat.min_eq_left henough]
    simpa only [Nat.zero_add] using (hs.drop data.indexOffset).instL levels
  have hr := SaturatedCaptureState.run_subst
    (state := { added := [], captures := prefixArgs.take data.indexOffset })
    hinstructions σ ((prefixArgs.drop data.indexOffset).take data.numIndices)
  rw [hrun] at hr
  simp only [SaturatedCaptureState.subst, substAdded, List.length_nil, Subst.liftN,
    Option.map_some] at hr
  have hsplit' := splitSaturated_subst hsplit σ
  simp only [saturatedProgram, hlevels, hsplit', bind,
    Option.bind_some, List.getElem?_map, hmajor, Option.map_some, hsource,
    hsourceCounts, hequation, hbody, hdomains, hhead, ← List.map_drop, ← List.map_take]
  rw [hr]
  rfl

theorem SaturatedProgram.result_subst {program : SaturatedProgram data}
    (scope : program.equationBody.rhs.ClosedN program.state.captures.length) (σ : Subst) :
    (program.subst σ).result =
      program.result.subst (σ.liftN program.state.added.length) := by
  have hr := instantiateParams_subst_scoped (scope.instL (ls := program.levels))
    (σ.liftN program.state.added.length)
  simp only [result, rhs, SaturatedProgram.subst, SaturatedCaptureState.subst,
    substAdded_length, subst_mkApps, List.map_map]
  rw [← hr]
  congr 1
  exact List.map_congr_left fun e _ => (liftN_subst_liftN e σ program.state.added.length).symm

/-- Closedness of the selected original RHS supplies all prefix scopes;
the output includes the exact new telescope and the trailing applications. -/
theorem saturatedProgram_subst_of_closed_rhs {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (selected : data.saturatedProgram levels arguments = some program)
    (scope : program.equation.rhs.Closed) (σ : Subst) :
    data.saturatedProgram levels (arguments.map (·.subst σ)) = some (program.subst σ) ∧
    (program.subst σ).state.added = substAdded σ program.state.added ∧
    (program.subst σ).state.captures =
      program.state.captures.map (·.subst (σ.liftN program.state.added.length)) ∧
    (program.subst σ).result = program.result.subst (σ.liftN program.state.added.length) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, extract, _, _, count, _⟩ := saturatedProgram_spec selected
  obtain ⟨domains, body⟩ := scope_of_extract extract scope
  exact ⟨saturatedProgram_subst selected domains σ, rfl, rfl,
    program.result_subst (by simpa only [count] using body) σ⟩

end Lean4Lean.InductiveSignature.NativeRecursorData
