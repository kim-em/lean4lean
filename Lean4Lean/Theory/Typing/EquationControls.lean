import Lean4Lean.Theory.Typing.EquationStratification
import Lean4Lean.Theory.Typing.CanonicalHeadRegistryData

/-! Lawful per-rule controls for the canonical equation packets. A source
cutoff constrains equations, independently of its constants and original proof
size. The name selector agrees with the actual delta/native dispatch order. -/
namespace Lean4Lean.VEnv
set_option Elab.async false

namespace EquationStratification
variable {env source : VEnv}

/-- Every source equation is installed in the fixed target and is at or below
the cutoff. Missing low-ranked equations do not have to be activated. -/
def SourceCutoff (strata : EquationStratification env) (source : VEnv) (cutoff : Nat) : Prop :=
  ∀ rule, source.defeqs rule → ∃ present : env.defeqs rule,
    (strata.select present).ordinal ≤ cutoff

variable {strata : EquationStratification env} {rule : VDefEq}

theorem SourceCutoff.mono (bounded : strata.SourceCutoff source cutoff)
    (larger : cutoff ≤ next) : strata.SourceCutoff source next := by
  intro rule member
  obtain ⟨present, bound⟩ := bounded rule member
  exact ⟨present, Nat.le_trans bound larger⟩

theorem SourceCutoff.source_mono (bounded : strata.SourceCutoff source cutoff)
    (below : earlier ≤ source) : strata.SourceCutoff earlier cutoff := by
  intro rule member
  exact bounded rule (below.defeqs member)

theorem Selected.sourceCutoff (selected : strata.Selected rule) :
    strata.SourceCutoff selected.origin.source (selected.ordinal - 1) := by
  intro previous member
  have present := selected.origin.sourceBelow.defeqs member
  refine ⟨present, ?_⟩
  have strict := selected.earlier_ordinal (strata.select present) member
  omega

theorem fullCutoff (strata : EquationStratification env) :
    strata.SourceCutoff env strata.rules.length := by
  intro rule present
  exact ⟨present, (strata.select present).ordinal_le⟩

noncomputable def ordinalOf (strata : EquationStratification env) (rule : VDefEq) : Nat := by
  classical
  exact if present : env.defeqs rule then (strata.select present).ordinal else 0

theorem ordinalOf_present (strata : EquationStratification env) (present : env.defeqs rule) :
    strata.ordinalOf rule = (strata.select present).ordinal := by
  classical
  simp only [ordinalOf, dif_pos present]

theorem SourceCutoff.absent (bounded : strata.SourceCutoff source cutoff)
    (later : cutoff < strata.ordinalOf rule) : ¬ source.defeqs rule := by
  intro member
  obtain ⟨present, bound⟩ := bounded rule member
  rw [strata.ordinalOf_present present] at later
  omega

/-- The same priority as the actual observation grammar: definition first,
then the selected native singleton equation. -/
def headEquation (registry : CanonicalHead.Registry) (name : Name) : Option VDefEq :=
  match registry.definitions name with
  | some value => some value.toDefEq
  | none => (registry.natives name).bind InductiveSignature.NativeRecursorData.singletonEquation

/-- The rank supplied to the actual query-depth traversal. Unknown or
uninstalled rules have rank zero, below every active control. -/
noncomputable def headOrdinal (strata : EquationStratification env)
    (registry : CanonicalHead.Registry) (name : Name) : Nat :=
  match headEquation registry name with
  | none => 0
  | some rule => strata.ordinalOf rule

theorem ordinalOf_le (strata : EquationStratification env) (rule : VDefEq) :
    strata.ordinalOf rule ≤ strata.rules.length := by
  classical
  unfold ordinalOf
  split
  · exact Selected.ordinal_le _
  · exact Nat.zero_le _

theorem headOrdinal_le (strata : EquationStratification env)
    (registry : CanonicalHead.Registry) (name : Name) :
    strata.headOrdinal registry name ≤ strata.rules.length := by
  unfold headOrdinal
  split
  · exact Nat.zero_le _
  · exact strata.ordinalOf_le _

theorem headOrdinal_definition (strata : EquationStratification env)
    (lookup : registry.definitions name = some value) (present : env.defeqs value.toDefEq) :
    strata.headOrdinal registry name = (strata.select present).ordinal := by
  simp only [headOrdinal, headEquation, lookup, strata.ordinalOf_present present]

theorem headOrdinal_native (strata : EquationStratification env)
    (notDefinition : registry.definitions name = none)
    (lookup : registry.natives name = some data)
    (selected : data.singletonEquation = some rule) (present : env.defeqs rule) :
    strata.headOrdinal registry name = (strata.select present).ordinal := by
  simp only [headOrdinal, headEquation, notDefinition, lookup, Option.bind_some,
    selected, strata.ordinalOf_present present]

noncomputable def headControl (strata : EquationStratification env)
    (registry : CanonicalHead.Registry) (ordinal : Nat) (name : Name) : Bool := by
  classical
  exact match headEquation registry name with
    | none => false
    | some rule => decide (strata.ordinalOf rule = ordinal)

theorem headControl_definition (strata : EquationStratification env)
    (lookup : registry.definitions name = some value) (present : env.defeqs value.toDefEq) :
    strata.headControl registry (strata.select present).ordinal name = true := by
  classical
  simp [headControl, headEquation, lookup, strata.ordinalOf_present present]

theorem headControl_native (strata : EquationStratification env)
    (notDefinition : registry.definitions name = none)
    (lookup : registry.natives name = some data)
    (selected : data.singletonEquation = some rule) (present : env.defeqs rule) :
    strata.headControl registry (strata.select present).ordinal name = true := by
  classical
  simp [headControl, headEquation, notDefinition, lookup, selected,
    strata.ordinalOf_present present]

/-- Every selected caller control strictly above the source cutoff is quiet
on computational rules actually installed in that source. -/
theorem headControl_lawful (bounded : strata.SourceCutoff source cutoff)
    (above : cutoff < ordinal) (selected : headEquation registry name = some rule)
    (active : strata.headControl registry ordinal name = true) :
    ¬ source.defeqs rule := by
  have rank : strata.ordinalOf rule = ordinal := by
    simpa only [headControl, selected, decide_eq_true_eq] using active
  apply bounded.absent
  simpa only [rank] using above

/-- Exhaustive canonical opening classification. The low-rank branch is an
outer cutoff decrease even if the caller happens to omit this equation. The
high-rank branch selects the very named fuel consumed by delta/native syntax. -/
theorem opening (strata : EquationStratification env) (present : env.defeqs rule)
    (bounded : strata.SourceCutoff source cutoff)
    (selected : headEquation registry name = some rule) :
    ((strata.select present).ordinal ≤ cutoff ∧
      (strata.select present).ordinal - 1 < cutoff) ∨
    (cutoff < (strata.select present).ordinal ∧ ¬ source.defeqs rule ∧
      strata.headControl registry (strata.select present).ordinal name = true) := by
  by_cases lower : (strata.select present).ordinal ≤ cutoff
  · have positive := (strata.select present).ordinal_pos
    exact Or.inl ⟨lower, by omega⟩
  · have higher : cutoff < (strata.select present).ordinal := by omega
    refine Or.inr ⟨higher, ?_, ?_⟩
    · apply bounded.absent
      rwa [strata.ordinalOf_present present]
    · classical
      simp [headControl, selected, strata.ordinalOf_present present]

end EquationStratification
end Lean4Lean.VEnv
