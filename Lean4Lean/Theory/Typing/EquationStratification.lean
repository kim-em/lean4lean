import Lean4Lean.Theory.Typing.EquationHeaderProvenance

/-! A finite equation order can be selected from one actual ordering proof,
without a linear declaration history for all projection metadata. Every selected
rule retains its actual checking source, whose equation set is exactly the older
suffix. Arbitrary stored definition origins do not enjoy this property. -/
namespace Lean4Lean.VEnv
set_option Elab.async false

structure EquationStratification (env : VEnv) where
  rules : List VDefEq
  nodup : rules.Nodup
  present : ∀ rule, rule ∈ rules ↔ env.defeqs rule
  origins : ∀ rule ∈ rules, ∃ newer older,
    ∃ origin : EquationHeaderOrigin env rule,
      rules = newer ++ rule :: older ∧
      ∀ previous, origin.source.defeqs previous ↔ previous ∈ older

namespace EquationStratification

def extend (strata : EquationStratification env) (below : env ≤ extended)
    (same : extended.defeqs = env.defeqs) : EquationStratification extended where
  rules := strata.rules
  nodup := strata.nodup
  present := by intro rule; rw [same]; exact strata.present rule
  origins := by
    intro rule member
    obtain ⟨newer, older, origin, shape, source⟩ := strata.origins rule member
    exact ⟨newer, older, origin.extend below, shape, source⟩

noncomputable def add (strata : EquationStratification env)
    (ordered : env.Ordered) (formation : rule.WF env) :
    EquationStratification (env.addDefEq rule) := by
  classical
  by_cases old : env.defeqs rule
  · apply strata.extend VEnv.addDefEq_le
    funext previous
    apply propext
    exact ⟨fun member => member.elim (fun same => same ▸ old) id, Or.inr⟩
  · refine ⟨rule :: strata.rules, List.nodup_cons.mpr
      ⟨fun member => old ((strata.present rule).mp member), strata.nodup⟩, ?_, ?_⟩
    · intro selected
      change selected ∈ rule :: strata.rules ↔ selected = rule ∨ env.defeqs selected
      rw [List.mem_cons, strata.present]
    · intro selected member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨[], strata.rules,
          ⟨env, ordered, formation, VEnv.addDefEq_le, old, Or.inl rfl⟩, rfl, ?_⟩
        intro previous
        exact (strata.present previous).symm
      · obtain ⟨newer, older, origin, shape, source⟩ := strata.origins selected member
        exact ⟨rule :: newer, older, origin.extend VEnv.addDefEq_le,
          congrArg (List.cons rule) shape, source⟩

/-- An original source packet together with its exact location in the chosen
finite rule order. The source may have more constants than another caller. -/
structure Selected (strata : EquationStratification env) (rule : VDefEq) where
  newer : List VDefEq
  older : List VDefEq
  origin : EquationHeaderOrigin env rule
  rules_eq : strata.rules = newer ++ rule :: older
  source_eq : ∀ previous, origin.source.defeqs previous ↔ previous ∈ older

noncomputable def select (strata : EquationStratification env)
    (present : env.defeqs rule) : strata.Selected rule := by
  have available :=  strata.origins rule ((strata.present rule).mpr present)
  let newer := Classical.choose available
  let older := Classical.choose (Classical.choose_spec available)
  let origin := Classical.choose (Classical.choose_spec (Classical.choose_spec available))
  exact ⟨newer, older, origin,
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec available))).1,
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec available))).2⟩

namespace Selected
noncomputable local instance : BEq VDefEq := ⟨fun a b => @decide (a = b) (Classical.propDecidable _)⟩
local instance : LawfulBEq VDefEq where
  eq_of_beq h := by classical exact of_decide_eq_true h
  rfl := by classical exact decide_eq_true rfl
variable {env : VEnv} {strata : EquationStratification env} {rule : VDefEq}

def ordinal (selected : strata.Selected rule) : Nat := selected.older.length + 1

theorem ordinal_pos (selected : strata.Selected rule) : 0 < selected.ordinal := by
  unfold ordinal
  omega

theorem ordinal_le (selected : strata.Selected rule) : selected.ordinal ≤ strata.rules.length := by
  rw [selected.rules_eq, List.length_append, List.length_cons]
  unfold ordinal
  omega

/-- All installed equations of the ACTUAL selected checking source occur
in the strictly older suffix, including when the caller lacks the rule. -/
theorem source_equations (selected : strata.Selected rule) {previous : VDefEq}
    (present : selected.origin.source.defeqs previous) : previous ∈ selected.older :=
  (selected.source_eq previous).mp present

private theorem index_eq (selected : strata.Selected rule) :
    strata.rules.idxOf rule = selected.newer.length := by
  have unique := strata.nodup
  rw [selected.rules_eq, List.nodup_append] at unique
  have absent : rule ∉ selected.newer := fun member =>
    unique.2.2 rule member rule List.mem_cons_self rfl
  rw [selected.rules_eq, List.idxOf_append, if_neg absent, List.idxOf_cons_self,
    Nat.zero_add]

/-- This strict bound is about the actual selected packet, not an assumed
numeric budget or an arbitrary separately supplied definition origin. -/
theorem earlier_ordinal (selected : strata.Selected rule)
    (previous : strata.Selected previousRule)
    (present : selected.origin.source.defeqs previousRule) :
    previous.ordinal < selected.ordinal := by
  have member := selected.source_equations present
  have unique := strata.nodup
  rw [selected.rules_eq, List.nodup_append] at unique
  have absent : previousRule ∉ selected.newer := fun earlier =>
    unique.2.2 previousRule earlier previousRule (List.mem_cons_of_mem _ member) rfl
  have different : previousRule ≠ rule := by
    intro same
    subst previousRule
    exact (List.nodup_cons.mp unique.2.1).1 member
  have index := previous.index_eq
  rw [selected.rules_eq, List.idxOf_append, if_neg absent] at index
  have consIndex : (rule :: selected.older).idxOf previousRule =
      selected.older.idxOf previousRule + 1 := by
    simp only [List.idxOf_cons, beq_eq_false_iff_ne.mpr (Ne.symm different), Bool.cond_false]
  rw [consIndex] at index
  have inBounds := List.idxOf_lt_length_of_mem member
  have currentLength := congrArg List.length selected.rules_eq
  have previousLength := congrArg List.length previous.rules_eq
  simp only [List.length_append, List.length_cons] at currentLength previousLength
  unfold ordinal
  omega

end Selected
end EquationStratification

/-- Projection/eliminator metadata can branch without changing the equation
spine. Duplicate installs are skipped; actual source typing is retained. -/
theorem Ordered.equationStratification (ordered : env.Ordered) :
    Nonempty (EquationStratification env) := by
  induction ordered with
  | empty =>
    exact ⟨⟨[], by simp, by intro rule; change rule ∈ [] ↔ False; simp,
      by intro rule member; cases member⟩⟩
  | @const previous name value current ordered formation installed ih =>
    obtain ⟨strata⟩ := ih
    exact ⟨strata.extend (VEnv.addConst_le installed) (VEnv.addConst_defeqs installed)⟩
  | defeq ordered formation ih =>
    obtain ⟨strata⟩ := ih
    exact ⟨strata.add ordered formation⟩
  | eliminator _ ih =>
    obtain ⟨strata⟩ := ih
    exact ⟨strata.extend VEnv.addEliminator_le rfl⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨strata⟩ := ih
    exact ⟨strata.extend VEnv.addProjections_le (VEnv.addProjections_defeqs ..)⟩

/-- The internal query grammar may fix this packet once from the unchanged
final `Ordered` assumption. No common native-history hypothesis is added. -/
noncomputable def Ordered.equationStrata (ordered : env.Ordered) : EquationStratification env :=
  Classical.choice ordered.equationStratification

end Lean4Lean.VEnv
