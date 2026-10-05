import Lean4Lean.Theory.Inductive.SaturatedNativeProgram

/-! Renaming the actual saturated capture execution while retaining its fresh
proof binders. Scope is local to each declared telescope prefix. In particular,
no declared field domain is assumed closed in the empty context.

`scope_of_extract` obtains these scopes from the original wrapped RHS. Its
closure is supplied by the original closed RHS typing child of `Strong.extra`
using `IsDefEq.closedN`; no typing of a generated replay is needed for scope.
The statements below are syntax results, not producers of typed replay guards.
-/

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr

/-- Domains in declaration order, each scoped over its preceding captures. -/
def CaptureDomainsScoped (count : Nat) : List VExpr → Prop
  | [] => True
  | domain :: rest => domain.ClosedN count ∧ CaptureDomainsScoped (count + 1) rest

theorem CaptureDomainsScoped.drop (h : CaptureDomainsScoped count domains) (n : Nat) :
    CaptureDomainsScoped (count + n) (domains.drop n) := by
  induction n generalizing domains count with
  | zero => simpa using h
  | succ n ih =>
    cases domains with
    | nil => trivial
    | cons domain rest =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih h.2

theorem CaptureDomainsScoped.instL (h : CaptureDomainsScoped count domains)
    (levels : List VLevel) :
    CaptureDomainsScoped count (domains.map (·.instL levels)) := by
  induction domains generalizing count with
  | nil => trivial
  | cons domain rest ih => exact ⟨h.1.instL, ih h.2⟩

private theorem scope_wrapLams (domains : List VExpr) (body : VExpr)
    (h : (wrapLams domains body).ClosedN count) :
    CaptureDomainsScoped count domains ∧ body.ClosedN (count + domains.length) := by
  induction domains generalizing count with
  | nil => exact ⟨trivial, by simpa [wrapLams] using h⟩
  | cons domain domains ih =>
    obtain ⟨hs, hb⟩ := ih h.2
    exact ⟨⟨h.1, hs⟩, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb⟩

/-- Extraction retains the original telescope, so closure of the wrapped
RHS gives precisely the domain-prefix scopes and the open RHS scope. -/
theorem scope_of_extract {body : CaseSchema.EquationBody}
    (h : CaseSchema.EquationBody.extract lhs rhs type = some body)
    (hrhs : rhs.Closed) :
    CaptureDomainsScoped 0 body.domains ∧ body.rhs.ClosedN body.domains.length := by
  have hw := (CaseSchema.EquationBody.extract_sound h).2.1
  have hc : (wrapLams body.domains body.rhs).Closed := hw ▸ hrhs
  simpa using scope_wrapLams body.domains body.rhs hc

private theorem subst_eq_of_scoped {e : VExpr} (he : e.ClosedN count)
    (h : ∀ i, i < count → σ i = τ i) : e.subst σ = e.subst τ := by
  induction e generalizing count σ τ with
  | bvar i => exact h i he
  | sort | const | elim => rfl
  | app _ _ ihf iha => simp only [subst, ihf he.1 h, iha he.2 h]
  | proj _ _ _ ih => simp only [subst, ih he h]
  | lam _ _ ihd ihb | forallE _ _ ihd ihb =>
    have hb : ∀ i, i < count + 1 → σ.lift i = τ.lift i := by
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [Subst.lift]; rw [h i (by omega)]
    simp only [subst, ihd he.1 h, ihb he.2 hb]

theorem instantiateParams_rename_scoped {e : VExpr} {arguments : List VExpr}
    (he : e.ClosedN arguments.length) (ρ : Lift) :
    (instantiateParams e arguments).lift' ρ =
      instantiateParams e (arguments.map (·.lift' ρ)) := by
  let σ : Subst := fun i =>
    if hi : i < arguments.length then arguments[arguments.length - 1 - i]
    else .bvar (i - arguments.length)
  change (e.subst σ).lift' ρ = _
  rw [lift'_subst]
  unfold instantiateParams
  dsimp only [σ]
  apply subst_eq_of_scoped he
  intro i hi
  simp only [Subst.lift_r, List.length_map, dif_pos hi, List.getElem_map]

/-- Context order matters: a domain is renamed beneath only its older proof
binders, whereas captures are renamed beneath the entire added context. -/
def renameAdded (ρ : Lift) : List VExpr → List VExpr
  | [] => []
  | domain :: older => domain.lift' (ρ.consN older.length) :: renameAdded ρ older

@[simp] theorem renameAdded_length (ρ : Lift) (added : List VExpr) :
    (renameAdded ρ added).length = added.length := by
  induction added <;> simp [renameAdded, *]

def SaturatedCaptureState.rename (state : SaturatedCaptureState) (ρ : Lift) :
    SaturatedCaptureState := {
  added := renameAdded ρ state.added
  captures := state.captures.map (·.lift' (ρ.consN state.added.length)) }

private theorem liftN_rename (e : VExpr) (ρ : Lift) (n : Nat) :
    (e.liftN n).lift' (ρ.consN n) = (e.lift' ρ).liftN n := by
  rw [← lift'_consN_skipN (k := 0), ← lift'_comp]
  simp only [Lift.consN, Lift.skipN_comp_consN, Lift.refl_comp]
  rw [← lift'_consN_skipN (k := 0), ← lift'_comp]
  simp only [Lift.consN, Lift.comp_skipN, Lift.comp]

private theorem lift_rename (e : VExpr) (ρ : Lift) :
    e.lift.lift' ρ.cons = (e.lift' ρ).lift := liftN_rename e ρ 1

theorem SaturatedCaptureState.step_rename
    {state : SaturatedCaptureState} {instruction : CaptureInstruction}
    (hs : instruction.domain.ClosedN state.captures.length) (ρ : Lift)
    (indices : List VExpr) :
    (state.rename ρ).step (indices.map (·.lift' ρ)) instruction =
      (state.step indices instruction).map (·.rename ρ) := by
  cases instruction with
  | index domain slot =>
    simp only [step, List.getElem?_map]
    cases h : indices[slot]? <;>
      simp [rename, List.map_append, liftN_rename]
  | proof domain =>
    change domain.ClosedN state.captures.length at hs
    have hd := instantiateParams_rename_scoped hs (ρ.consN state.added.length)
    simp only [step, rename, renameAdded, List.length_cons, List.map_append,
      List.map_map, List.map_cons, List.map_nil, Lift.consN, lift', Lift.liftVar,
      Option.map_some, Option.some.injEq, SaturatedCaptureState.mk.injEq]
    refine ⟨by rw [hd], ?_⟩
    congr 1
    exact List.map_congr_left fun e _ => (lift_rename e (ρ.consN state.added.length)).symm

/-- Scope of all remaining declarations; the count advances for both index
and proof captures, independently of the number of fresh proof binders. -/
def InstructionsScoped (count : Nat) (instructions : List CaptureInstruction) : Prop :=
  CaptureDomainsScoped count (instructions.map (·.domain))

theorem SaturatedCaptureState.run_rename
    {state : SaturatedCaptureState} {instructions : List CaptureInstruction}
    (hs : InstructionsScoped state.captures.length instructions)
    (ρ : Lift) (indices : List VExpr) :
    (state.rename ρ).run (indices.map (·.lift' ρ)) instructions =
      (state.run indices instructions).map (·.rename ρ) := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    rw [run, state.step_rename hs.1]
    cases ht : state.step indices instruction with
    | none => simp [run, ht]
    | some next =>
      have hone : state.run indices [instruction] = some next := by simp [run, ht]
      have hc := (run_counts hone).1
      have hnext : InstructionsScoped next.captures.length rest := by
        simpa only [InstructionsScoped, List.length_cons, List.length_nil,
          Nat.zero_add, hc] using hs.2
      simpa [run, ht] using ih hnext

theorem fieldInstructions_domains (source : CaseSchema.ProjectionData)
    (domains : List VExpr) :
    (fieldInstructions source domains).map (·.domain) = domains := by
  simp only [fieldInstructions, List.map_map]
  have h : (fun pair : VExpr × Nat =>
      (match source.fieldIndex pair.2 with
      | some slot => CaptureInstruction.index pair.1 slot
      | none => .proof pair.1).domain) = Prod.fst := by
    funext pair
    cases h : source.fieldIndex pair.2 <;> rfl
  change List.map (fun pair : VExpr × Nat =>
    (match source.fieldIndex pair.2 with
    | some slot => CaptureInstruction.index pair.1 slot
    | none => .proof pair.1).domain) domains.zipIdx = domains
  rw [h]
  exact List.zipIdx_map_fst 0 domains

def SaturatedProgram.rename (program : SaturatedProgram data) (ρ : Lift) :
    SaturatedProgram data := {
  program with
  prefixArgs := program.prefixArgs.map (·.lift' ρ)
  trailing := program.trailing.map (·.lift' ρ)
  major := program.major.lift' ρ
  state := program.state.rename ρ }

private theorem splitSaturated_rename
    (h : splitSaturated count arguments = some (prefixArgs, trailing)) (ρ : Lift) :
    splitSaturated count (arguments.map (·.lift' ρ)) =
      some (prefixArgs.map (·.lift' ρ), trailing.map (·.lift' ρ)) := by
  unfold splitSaturated at h ⊢
  simp only [List.length_map]
  split at h <;> try contradiction
  rename_i hcount
  cases h
  simp [hcount, List.map_take, List.map_drop]

/-- The metadata parser and instruction choices are unchanged. In particular,
success cannot depend on an unrelated context insertion or its proof witnesses. -/
theorem saturatedProgram_rename {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (h : data.saturatedProgram levels arguments = some program)
    (hs : CaptureDomainsScoped 0 program.equationBody.domains) (ρ : Lift) :
    data.saturatedProgram levels (arguments.map (·.lift' ρ)) = some (program.rename ρ) := by
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
  have hr := SaturatedCaptureState.run_rename
    (state := { added := [], captures := prefixArgs.take data.indexOffset })
    hinstructions ρ ((prefixArgs.drop data.indexOffset).take data.numIndices)
  rw [hrun] at hr
  simp only [SaturatedCaptureState.rename, renameAdded, List.length_nil, Lift.consN,
    Option.map_some] at hr
  have hsplit' := splitSaturated_rename hsplit ρ
  simp only [saturatedProgram, hlevels, hsplit', bind,
    Option.bind_some, List.getElem?_map, hmajor, Option.map_some, hsource,
    hsourceCounts, hequation, hbody, hdomains, hhead, ← List.map_drop, ← List.map_take]
  rw [hr]
  rfl

/-- Total parser naturality supplies the converse needed for pullback: a
successful program after renaming comes from a successful original program.
The scope premise belongs to the selected declared equation, not to an
assumed successful base-context execution. -/
theorem saturatedProgram_rename_eq {data : NativeRecursorData}
    {equation : VDefEq} {body : CaseSchema.EquationBody}
    (hequation : data.singletonEquation = some equation)
    (hbody : CaseSchema.EquationBody.extract equation.lhs equation.rhs equation.type = some body)
    (hs : CaptureDomainsScoped 0 body.domains)
    (levels : List VLevel) (arguments : List VExpr) (ρ : Lift) :
    data.saturatedProgram levels (arguments.map (·.lift' ρ)) =
      (data.saturatedProgram levels arguments).map (·.rename ρ) := by
  unfold saturatedProgram
  by_cases hl : (levels.length != data.uvars) = true
  · simp [hl]
  simp only [hl]
  unfold splitSaturated
  simp only [List.length_map]
  by_cases hc : data.majorOffset + 1 ≤ arguments.length
  · simp only [hc, ↓reduceIte, bind, Option.bind_some, ← List.map_take,
      ← List.map_drop, List.getElem?_map]
    cases hm : (arguments.take (data.majorOffset + 1))[data.majorOffset]? with
    | none => simp
    | some major =>
      simp only [Option.map_some, Option.bind_some]
      cases hp : data.schema.projectionData data.owner (data.sourceLevels levels) with
      | none => simp
      | some source =>
        simp only [Option.bind_some]
        by_cases hsource : (source.params.length != data.numParams ||
            source.indices.length != data.numIndices ||
            source.constructorIndices.length != data.numIndices) = true
        · simp [hsource]
        simp only [hsource, hequation, hbody, Option.bind_some]
        by_cases hd : (body.domains.length != data.indexOffset + source.fields.length) = true
        · simp [hd]
        simp only [hd]
        by_cases hh : (body.lhs.getAppFnArgs.1 != .const data.name (VLevel.params data.uvars) ||
            body.lhs.getAppFnArgs.2.length != data.majorOffset + 1) = true
        · simp [hh]
        simp only [hh]
        have henough : data.indexOffset ≤ (arguments.take (data.majorOffset + 1)).length := by
          rw [List.length_take, Nat.min_eq_left hc, majorOffset]
          omega
        have hi : InstructionsScoped
            ((arguments.take (data.majorOffset + 1)).take data.indexOffset).length
            (fieldInstructions source ((body.domains.drop data.indexOffset).map (·.instL levels))) := by
          unfold InstructionsScoped
          rw [fieldInstructions_domains, List.length_take, Nat.min_eq_left henough]
          simpa only [Nat.zero_add] using (hs.drop data.indexOffset).instL levels
        have hr := SaturatedCaptureState.run_rename
          (state := { added := [], captures := (arguments.take (data.majorOffset + 1)).take data.indexOffset })
          hi ρ (((arguments.take (data.majorOffset + 1)).drop data.indexOffset).take data.numIndices)
        simp only [SaturatedCaptureState.rename, renameAdded, List.length_nil, Lift.consN] at hr
        rw [hr]
        cases SaturatedCaptureState.run
          (((arguments.take (data.majorOffset + 1)).drop data.indexOffset).take data.numIndices)
          (fieldInstructions source ((body.domains.drop data.indexOffset).map (·.instL levels)))
          { added := [], captures := (arguments.take (data.majorOffset + 1)).take data.indexOffset } <;> rfl
  · simp [hc]

private theorem mkApps_rename (fn : VExpr) (arguments : List VExpr) (ρ : Lift) :
    (mkApps fn arguments).lift' ρ = mkApps (fn.lift' ρ) (arguments.map (·.lift' ρ)) := by
  induction arguments generalizing fn with
  | nil => rfl
  | cons arg rest ih => exact ih (.app fn arg)

theorem SaturatedProgram.result_rename {program : SaturatedProgram data}
    (hrhs : program.equationBody.rhs.ClosedN program.state.captures.length) (ρ : Lift) :
    (program.rename ρ).result =
      program.result.lift' (ρ.consN program.state.added.length) := by
  have hr := instantiateParams_rename_scoped (hrhs.instL (ls := program.levels))
    (ρ.consN program.state.added.length)
  simp only [result, rhs, rename, SaturatedCaptureState.rename, renameAdded_length,
    mkApps_rename, List.map_map]
  rw [← hr]
  congr 1
  exact List.map_congr_left fun e _ => (liftN_rename e ρ program.state.added.length).symm

/-- A single original closed RHS supplies every scope premise. The result
states the exact fresh context, captures and trailing-application output, so
a typed embedding can retain these proof binders during trace pullback. -/
theorem saturatedProgram_rename_of_closed_rhs {data : NativeRecursorData}
    {levels : List VLevel} {arguments : List VExpr} {program : SaturatedProgram data}
    (h : data.saturatedProgram levels arguments = some program)
    (hrhs : (program.equation.rhs.instL levels).Closed) (ρ : Lift) :
    data.saturatedProgram levels (arguments.map (·.lift' ρ)) = some (program.rename ρ) ∧
    (program.rename ρ).state.added = renameAdded ρ program.state.added ∧
    (program.rename ρ).state.captures =
      program.state.captures.map (·.lift' (ρ.consN program.state.added.length)) ∧
    (program.rename ρ).result = program.result.lift' (ρ.consN program.state.added.length) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hextract, _, _, hcount, _⟩ := saturatedProgram_spec h
  obtain ⟨hdomains, hbody⟩ := scope_of_extract hextract hrhs.instL_rev
  refine ⟨saturatedProgram_rename h hdomains ρ, rfl, rfl, ?_⟩
  exact program.result_rename (by simpa only [hcount] using hbody) ρ

end Lean4Lean.InductiveSignature.NativeRecursorData
