import Lean4Lean.Theory.Typing.AnchoredNativeSyntax
import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming
import Lean4Lean.Theory.Typing.SplitTypedEmbedding
import Lean4Lean.Theory.Typing.RecursorLemmas

/-! Finite telescope scope and renaming for native observation metadata. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false
variable {data : NativeRecursorData} {program : SaturatedProgram data}
variable {expression domain result : VExpr} {domains arguments witnesses : List VExpr}
variable {levels : List VLevel} {count depth index field : Nat} {instruction : CaptureInstruction}

theorem nativeCaptureSubst_rename_prefix (arguments : List VExpr) (ρ : Lift)
    (hi : i < arguments.length) :
    (nativeCaptureSubst arguments).lift_r ρ i =
      nativeCaptureSubst (arguments.map (·.lift' ρ)) i := by
  simp only [Subst.lift_r, nativeCaptureSubst, List.length_map, dif_pos hi, List.getElem_map]

theorem nativeCaptureSubst_rename_expression (scope : expression.ClosedN arguments.length)
    (ρ : Lift) :
    (expression.subst (nativeCaptureSubst arguments)).lift' ρ =
      expression.subst (nativeCaptureSubst (arguments.map (·.lift' ρ))) := by
  rw [lift'_subst]
  exact subst_congr_closedN scope (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)

theorem native_takeForalls_scoped
    (parsed : NativeRecursorData.takeForalls count expression = some (domains, result))
    (scope : expression.ClosedN depth) : CaptureDomainsScoped depth domains := by
  induction count generalizing expression domains result depth with
  | zero =>
    simp only [NativeRecursorData.takeForalls, Option.some.injEq, Prod.mk.injEq] at parsed
    cases parsed.1
    trivial
  | succ count ih =>
    cases expression <;> simp only [NativeRecursorData.takeForalls] at parsed <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨⟨tail, body⟩, hp, he⟩ := parsed
    cases he
    exact ⟨scope.1, ih hp scope.2⟩

theorem native_scoped_get
    (scope : CaptureDomainsScoped depth domains) (origin : domains[index]? = some domain) :
    domain.ClosedN (depth + index) := by
  induction domains generalizing depth index with
  | nil => simp at origin
  | cons A rest ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at origin; subst domain; simpa using scope.1
    | succ index =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih scope.2 origin

theorem NativeConstantSignature.domain_scope (signature : NativeConstantSignature data levels)
    (closed : signature.type.Closed) (origin : signature.domains[index]? = some domain) :
    domain.ClosedN index := by
  simpa only [Nat.zero_add] using native_scoped_get
    (native_takeForalls_scoped signature.telescope closed.instL) origin

def NativeIndexTemplates.rename (templates : NativeIndexTemplates program)
    (closed : program.equation.rhs.Closed) (ρ : Lift) : NativeIndexTemplates (program.rename ρ) := {
  templates with
  selected := by
    simpa only [List.map_append, SaturatedProgram.rename] using
      (saturatedProgram_rename_of_closed_rhs templates.selected closed.instL ρ).1 }

theorem native_instruction_scope
    (selected : data.saturatedProgram levels arguments = some program)
    (closed : program.equation.rhs.Closed)
    (origin : program.instructions[field]? = some instruction) :
    instruction.domain.ClosedN (data.indexOffset + field) := by
  have spec := saturatedProgram_spec selected
  have hs := ((scope_of_extract spec.2.2.2.2.2.2.2.2.2.1 closed).1.drop data.indexOffset).instL levels
  have hi := spec.2.2.2.2.2.2.2.2.2.2.1
  have ho : (program.instructions.map CaptureInstruction.domain)[field]? = some instruction.domain := by
    simp only [List.getElem?_map, origin, Option.map_some]
  rw [hi, fieldInstructions_domains] at ho
  exact native_scoped_get (by simpa only [Nat.zero_add] using hs) ho

theorem NativeIndexTemplates.natural_scope (templates : NativeIndexTemplates program)
    (closed : templates.recursorType.Closed) :
    templates.naturalDomain.ClosedN
      (program.prefixArgs.take (data.indexOffset + templates.slot)).length := by
  have hs := native_scoped_get (native_takeForalls_scoped templates.telescope closed.instL)
    templates.naturalOrigin
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp templates.naturalOrigin
  have hp := (saturatedProgram_spec templates.selected).2.2.1
  have hd := takeForalls_length templates.telescope
  rw [List.length_take, Nat.min_eq_left (by omega)]
  simpa using hs

theorem NativeIndexTemplates.declared_scope (templates : NativeIndexTemplates program)
    (closed : program.equation.rhs.Closed)
    (length : witnesses.length = program.equationBody.domains.length) :
    templates.declaredDomain.ClosedN
      (witnesses.take (data.indexOffset + templates.field)).length := by
  have hs := native_instruction_scope templates.selected closed templates.declaredOrigin
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp templates.declaredOrigin
  have spec := saturatedProgram_spec templates.selected
  have hlen : program.instructions.length = program.equationBody.domains.length - data.indexOffset := by
    rw [spec.2.2.2.2.2.2.2.2.2.2.1]
    simp [fieldInstructions]
  rw [List.length_take, Nat.min_eq_left (by omega)]
  exact hs

private theorem native_wrap_scope (domains : List VExpr) (body : VExpr)
    (scope : (wrapLams domains body).ClosedN count) : body.ClosedN (count + domains.length) := by
  induction domains generalizing count with
  | nil => simpa [wrapLams] using scope
  | cons domain rest ih =>
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih scope.2

private theorem native_spine_scoped (scope : expression.ClosedN count) :
    ∀ value ∈ expression.getAppFnArgs.2, value.ClosedN count := by
  have go : ∀ (e : VExpr) (args : List VExpr), e.ClosedN count →
      (∀ a ∈ args, a.ClosedN count) → ∀ a ∈ (getAppFnArgs.go e args).2, a.ClosedN count := by
    intro e
    induction e with
    | app fn arg ih _ =>
      intro args he ha
      exact ih (arg :: args) he.1 (by intro a hm; cases hm with
        | head => exact he.2
        | tail _ hm => exact ha a hm)
    | _ => intro args _ ha; exact ha
  exact go expression [] scope (by simp)

theorem nativeEquationArguments_rename
    (selected : data.saturatedProgram levels arguments = some program)
    (closed : program.equation.lhs.Closed)
    (length : witnesses.length = program.equationBody.domains.length) (ρ : Lift) :
    nativeEquationArguments (program.rename ρ) (witnesses.map (·.lift' ρ)) =
      (nativeEquationArguments program witnesses).map (·.lift' ρ) := by
  have spec := saturatedProgram_spec selected
  have hw := (CaseSchema.EquationBody.extract_sound spec.2.2.2.2.2.2.2.2.2.1).1
  have hs : (program.equationBody.lhs.instL program.levels).ClosedN witnesses.length := by
    rw [length]
    have base : program.equationBody.lhs.ClosedN program.equationBody.domains.length := by
      simpa only [Nat.zero_add] using native_wrap_scope (count := 0) _ _ (hw ▸ closed)
    exact base.instL
  simp only [nativeEquationArguments, SaturatedProgram.rename, List.map_map]
  apply List.map_congr_left
  intro value hv
  exact (nativeCaptureSubst_rename_expression (native_spine_scoped hs value hv) ρ).symm

theorem nativeEquationArguments_length
    (selected : data.saturatedProgram levels arguments = some program) :
    (nativeEquationArguments program witnesses).length = data.majorOffset + 1 := by
  unfold saturatedProgram at selected
  dsimp only at selected
  split at selected <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at selected
  obtain ⟨⟨prefixArgs, trailing⟩, _, major, _, source, _, selected⟩ := selected
  split at selected <;> try contradiction
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨equation, _, body, _, selected⟩ := selected
  split at selected <;> try contradiction
  split at selected <;> try contradiction
  rename_i hhead
  simp only [Option.bind_eq_some_iff] at selected
  obtain ⟨state, _, he⟩ := selected
  cases he
  simp only [nativeEquationArguments, List.length_map, getAppFnArgs_instL]
  simp only [Bool.or_eq_true, bne_iff_ne, not_or] at hhead
  exact Classical.not_not.mp hhead.2

/-- A typed substitution only reads the finite source context. -/
theorem native_substEq_prefix {env : VEnv} {U : Nat} {target source : List VExpr}
    {σ τ σ' τ' : Subst} (henv : env.Ordered)
    (typed : Ctx.SubstEq env U target σ τ source)
    (left : ∀ i < source.length, σ i = σ' i)
    (right : ∀ i < source.length, τ i = τ' i) :
    Ctx.SubstEq env U target σ' τ' source := by
  induction source generalizing σ τ σ' τ' with
  | nil => exact .nil
  | cons A source ih =>
    cases typed with
    | cons tail formed pair =>
      apply Ctx.SubstEq.cons
        (ih tail (fun i hi => left (i+1) (by simp only [List.length_cons]; omega))
          (fun i hi => right (i+1) (by simp only [List.length_cons]; omega))) formed
      have hs := formed.closedN henv (CtxWF.closed henv tail.wf)
      have he := subst_congr_closedN hs
        (σ := σ.tail) (σ' := σ'.tail)
        (fun i hi => left (i+1) (by simp only [List.length_cons]; omega))
      simpa only [Subst.head, left 0 (by simp), right 0 (by simp), he] using pair

end Lean4Lean.AnchoredSource.Adapted
