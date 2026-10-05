import Lean4Lean.Theory.Inductive.SaturatedNativeProgram
import Lean4Lean.Theory.Inductive.CaseReductionLemmas

/-! The common parameter/motive/minor telescope is literal generated syntax,
including after restoration and universe instantiation. This does not assume
a typed reconstruction of an arbitrary native major.
-/

namespace Lean4Lean.InductiveSignature
open VExpr

private inductive CommonPiPrefix : Nat → VExpr → VExpr → Prop where
  | zero : CommonPiPrefix 0 left right
  | succ : CommonPiPrefix n left right →
      CommonPiPrefix (n + 1) (.forallE domain left) (.forallE domain right)

private theorem CommonPiPrefix.instL
    (h : CommonPiPrefix n left right) (levels : List VLevel) :
    CommonPiPrefix n (left.instL levels) (right.instL levels) := by
  induction h with
  | zero => exact .zero
  | succ _ ih => exact .succ ih

private theorem CommonPiPrefix.restore {r : Restoration} {pre : List VExpr}
    (left : r.expr (wrapForalls pre a) = some a')
    (right : r.expr (wrapForalls pre b) = some b') :
    CommonPiPrefix pre.length a' b' := by
  induction pre generalizing a' b' with
  | nil => exact .zero
  | cons domain rest ih =>
    change (do let d ← r.expr domain; let e ← r.expr (wrapForalls rest a)
               pure (VExpr.forallE d e)) = some a' at left
    change (do let d ← r.expr domain; let e ← r.expr (wrapForalls rest b)
               pure (VExpr.forallE d e)) = some b' at right
    simp only [bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at left right
    obtain ⟨d, hd, a₀, ha, rfl⟩ := left
    obtain ⟨d', hd', b₀, hb, rfl⟩ := right
    cases Option.some.inj (hd'.symm.trans hd)
    exact .succ (ih ha hb)

private theorem CommonPiPrefix.domains
    {leftDomains rightDomains : List VExpr}
    (h : CommonPiPrefix n (wrapForalls leftDomains left) (wrapForalls rightDomains right))
    (hl : n ≤ leftDomains.length) (hr : n ≤ rightDomains.length) :
    leftDomains.take n = rightDomains.take n := by
  induction n generalizing leftDomains rightDomains left right with
  | zero => rfl
  | succ n ih =>
    cases leftDomains with
    | nil => simp at hl
    | cons A As =>
      cases rightDomains with
      | nil => simp at hr
      | cons B Bs =>
        cases h with
        | succ tail =>
          exact congrArg (List.cons A)
            (ih tail (Nat.le_of_succ_le_succ hl) (Nat.le_of_succ_le_succ hr))

private theorem telescope_eq
    (h : NativeRecursorData.takeForalls count expression = some (domains, body)) :
    expression = wrapForalls domains body := by
  induction count generalizing expression domains body with
  | zero =>
    simp only [NativeRecursorData.takeForalls, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ count ih =>
    cases expression <;> simp only [NativeRecursorData.takeForalls] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨tail, result⟩, ht, rfl, rfl⟩ := h
    exact congrArg (VExpr.forallE _) (ih ht)

private theorem instantiate_telescope (domains : List VExpr) (body : VExpr)
    (levels : List VLevel) :
    (wrapForalls domains body).instL levels =
      wrapForalls (domains.map (·.instL levels)) (body.instL levels) := by
  induction domains with
  | nil => rfl
  | cons domain rest ih => exact congrArg (VExpr.forallE (domain.instL levels)) ih

private theorem wrap_foralls_append (pre rest : List VExpr) (body : VExpr) :
    wrapForalls (pre ++ rest) body = wrapForalls pre (wrapForalls rest body) := by
  simp only [wrapForalls, List.foldr_append]

private theorem Instance.restored_commonPrefix
    {s : InductiveSignature} {g : Instance s} {r : Restoration}
    {owner : Fin s.families.size} {index : Fin s.constructors.size}
    {recursorType : VExpr}
    (recursor : r.expr (g.recursorType owner) = some recursorType)
    (equation : r.equation (g.equation index) = some rule) :
    CommonPiPrefix (s.params.length + s.families.size + s.constructors.size)
      recursorType rule.type := by
  have equationType := (Restoration.equation_parts equation).2.2
  let pre := g.params ++ g.motives ++ g.minors
  have result : CommonPiPrefix pre.length recursorType rule.type := by
    apply CommonPiPrefix.restore (r := r) (pre := pre)
    · simpa only [Instance.recursorType, pre, List.append_assoc,
        wrap_foralls_append] using recursor
    · simpa only [Instance.equation, pre, List.append_assoc,
        wrap_foralls_append] using equationType
  simpa only [pre, List.length_append, Instance.params, Instance.motives,
    Instance.minors, List.length_map, List.length_zipIdx, Array.length_toList] using result

namespace NativeRecursorData

/-- The common declaration prefix of a selected saturated program is exactly
the prefix of the registered recursor type, after occurrence instantiation. -/
theorem saturatedProgram_commonPrefix {data : NativeRecursorData}
    {program : SaturatedProgram data} {recursorType : VExpr}
    {levels : List VLevel} {arguments : List VExpr}
    {inputDomains : List VExpr} {result : VExpr}
    (selected : data.saturatedProgram levels arguments = some program)
    (registeredType : data.recursorType = some recursorType)
    (telescope : takeForalls (data.majorOffset + 1) (recursorType.instL levels) =
      some (inputDomains, result)) :
    (program.equationBody.domains.map (·.instL levels)).take data.indexOffset =
      inputDomains.take data.indexOffset := by
  obtain ⟨_, _, prefixLength, _, _, _, _, _, equation, extracted, _, run, count, _⟩ :=
    saturatedProgram_spec selected
  have common : CommonPiPrefix data.indexOffset recursorType program.equation.type := by
    unfold singletonEquation at equation
    dsimp only at equation
    split at equation <;> try contradiction
    exact Instance.restored_commonPrefix registeredType equation
  have nativeLength := takeForalls_length telescope
  have captureCount := (SaturatedCaptureState.run_counts run).1
  have enough : data.indexOffset ≤ program.prefixArgs.length := by
    rw [prefixLength, majorOffset]
    omega
  have equationLength : data.indexOffset ≤ program.equationBody.domains.length := by
    simp only [List.length_take, Nat.min_eq_left enough] at captureCount
    rw [count] at captureCount
    omega
  have instantiated := common.instL levels
  rw [telescope_eq telescope, ← (CaseSchema.EquationBody.extract_sound extracted).2.2,
    instantiate_telescope] at instantiated
  exact (instantiated.domains (by rw [nativeLength, majorOffset]; omega)
    (by simpa only [List.length_map] using equationLength)).symm

end NativeRecursorData
end Lean4Lean.InductiveSignature
