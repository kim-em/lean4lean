import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas

/-! Original formation stages for all constant headers.

A constant's closed type was checked before its own fresh installation. This
also covers the family and constructor prefixes within one inductive declaration,
where the length of the declaration list is not a decreasing measure. The finite
constant domain gives a strict measure at every such header edge.
-/
namespace Lean4Lean.VEnv
variable {env : VEnv}

structure ConstantDomain (env : VEnv) where
  names : List Name
  nodup : names.Nodup
  present : ∀ name, name ∈ names ↔ ∃ value, env.constants name = some value

namespace ConstantDomain

variable {env extended : VEnv}

def extend (domain : ConstantDomain env) (same : extended.constants = env.constants) :
    ConstantDomain extended where
  names := domain.names
  nodup := domain.nodup
  present := by intro name; rw [same]; exact domain.present name

def add (domain : ConstantDomain env) {name : Name} {value : VConstant}
    (installed : env.addConst name value = some extended) : ConstantDomain extended where
  names := name :: domain.names
  nodup := by
    apply List.nodup_cons.mpr
    constructor
    · intro member
      obtain ⟨old, lookup⟩ := (domain.present name).mp member
      unfold VEnv.addConst at installed
      rw [lookup] at installed
      cases installed
    · exact domain.nodup
  present := by
    intro selected
    rw [VEnv.addConst_constants_eq installed]
    by_cases same : name = selected
    · subst selected; simp
    · simp only [List.mem_cons, if_neg same]
      simpa only [Ne.symm same, false_or] using domain.present selected

theorem length_le (left : ConstantDomain env) (right : ConstantDomain extended)
    (below : env ≤ extended) : left.names.length ≤ right.names.length :=
  left.nodup.length_le_of_subset (fun name member => by
    obtain ⟨value, lookup⟩ := (left.present name).mp member
    exact (right.present name).mpr ⟨value, below.constants lookup⟩)

theorem length_eq (left right : ConstantDomain env) : left.names.length = right.names.length :=
  Nat.le_antisymm (left.length_le right .rfl) (right.length_le left .rfl)

end ConstantDomain

/-- This traverses the actual constant additions. Equation and metadata
installation do not introduce names. -/
theorem Ordered.constantDomain (formed : env.Ordered) : Nonempty (ConstantDomain env) := by
  induction formed with
  | empty => exact ⟨⟨[], by simp, by intro name; change name ∈ [] ↔ ∃ value, (none : Option VConstant) = some value; simp⟩⟩
  | const _ _ installed ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.add installed⟩
  | defeq _ _ ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.extend rfl⟩
  | eliminator _ ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.extend rfl⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.extend (VEnv.addProjections_constants ..)⟩

noncomputable def Ordered.constantCount (formed : env.Ordered) : Nat :=
  (Classical.choice formed.constantDomain).names.length

/-- Raw provenance retains the original closed formation proof and the
fresh header edge. No semantic result is stored in this packet. A whole block
may share its original formation environment. -/
structure ConstantHeaderOrigin (env : VEnv) (name : Name) (value : VConstant) where
  source : VEnv
  ordered : source.Ordered
  formation : value.WF source
  sourceBelow : source ≤ env
  fresh : source.constants name = none
  constant : env.constants name = some value

namespace ConstantHeaderOrigin
variable {env extended : VEnv} {name : Name} {value : VConstant}

def extend (origin : ConstantHeaderOrigin env name value) (below : env ≤ extended) :
    ConstantHeaderOrigin extended name value :=
  { origin with
    sourceBelow := origin.sourceBelow.trans below
    constant := below.constants origin.constant }

/-- Strict even for a family/constructor prefix of the current declaration. -/
theorem count_lt (origin : ConstantHeaderOrigin env name value) (formed : env.Ordered) :
    origin.ordered.constantCount < formed.constantCount := by
  let source := Classical.choice origin.ordered.constantDomain
  let target := Classical.choice formed.constantDomain
  have absent : name ∉ source.names := by
    intro member
    obtain ⟨value, lookup⟩ := (source.present name).mp member
    rw [origin.fresh] at lookup
    cases lookup
  have unique : (name :: source.names).Nodup := List.nodup_cons.mpr ⟨absent, source.nodup⟩
  have bound := unique.length_le_of_subset (l₂ := target.names) (by
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact (target.present selected).mpr ⟨value, origin.constant⟩
    · obtain ⟨value, lookup⟩ := (source.present selected).mp member
      exact (target.present selected).mpr ⟨value, origin.sourceBelow.constants lookup⟩)
  exact Nat.lt_of_succ_le bound

theorem typeStrong (origin : ConstantHeaderOrigin env name value) :
    ∃ level, origin.source.IsDefEqStrong value.uvars [] value.type value.type (.sort level) := by
  obtain ⟨level, formation⟩ := origin.formation
  exact ⟨level, formation.strong origin.ordered trivial⟩

theorem typeInstance (origin : ConstantHeaderOrigin env name value)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    ∃ level, origin.source.IsDefEqStrong U [] (value.type.instL levels)
      (value.type.instL levels) (.sort level) := by
  obtain ⟨level, original⟩ := origin.typeStrong
  exact ⟨level.inst levels, original.instL levelsWF⟩

end ConstantHeaderOrigin

/-- Lookup recovers the actual original constant constructor, including
constants installed inside an inductive block before its equations. -/
theorem Ordered.constantHeaderOrigin (formed : env.Ordered)
    (lookup : env.constants name = some value) :
    Nonempty (ConstantHeaderOrigin env name value) := by
  induction formed with
  | empty => cases lookup
  | @const source newName newValue header previous formation installed ih =>
    have lookup' := lookup
    rw [VEnv.addConst_constants_eq installed] at lookup'
    dsimp only at lookup'
    by_cases same : newName = name
    · subst newName
      simp only [ite_true, Option.some.injEq] at lookup'
      subst newValue
      refine ⟨⟨source, previous, formation, VEnv.addConst_le installed, ?_, lookup⟩⟩
      unfold VEnv.addConst at installed
      split at installed <;> simp_all
    · rw [if_neg same] at lookup'
      obtain ⟨origin⟩ := ih lookup'
      exact ⟨origin.extend (VEnv.addConst_le installed)⟩
  | defeq _ _ ih =>
    obtain ⟨origin⟩ := ih lookup
    exact ⟨origin.extend VEnv.addDefEq_le⟩
  | eliminator _ ih =>
    obtain ⟨origin⟩ := ih lookup
    exact ⟨origin.extend VEnv.addEliminator_le⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨origin⟩ := ih (by simpa only [VEnv.addProjections_constants] using lookup)
    exact ⟨origin.extend VEnv.addProjections_le⟩

/-- No lookup can appear except from the old environment or a literal
member of the installed block. -/
theorem addConstVals_lookup_origin {base extended : VEnv}
    (installed : base.addConstVals values = some extended)
    (lookup : extended.constants name = some value) :
    base.constants name = some value ∨
      ∃ entry ∈ values, entry.name = name ∧ entry.toVConstant = value := by
  induction values generalizing base with
  | nil => cases installed; exact Or.inl lookup
  | cons entry entries ih =>
    simp only [addConstVals, Option.bind_eq_bind, Option.bind_eq_some_iff] at installed
    obtain ⟨middle, first, rest⟩ := installed
    rcases ih rest with old | added
    · rw [VEnv.addConst_constants_eq first] at old
      dsimp only at old
      by_cases same : entry.name = name
      · simp only [same, ite_true, Option.some.injEq] at old
        exact Or.inr ⟨entry, List.mem_cons_self, same, old⟩
      · exact Or.inl (by simpa only [same, ite_false] using old)
    · obtain ⟨selected, member, sameName, sameValue⟩ := added
      exact Or.inr ⟨selected, List.mem_cons_of_mem _ member, sameName, sameValue⟩

/-- A simultaneously checked block retains the shared original formation
stage, even though its constants are inserted from left to right. -/
def ConstantHeaderOrigin.ofBlock {base extended : VEnv}
    (formed : base.Ordered) (types : ∀ entry ∈ values, entry.toVConstant.WF base)
    (installed : base.addConstVals values = some extended)
    (member : value ∈ values) : ConstantHeaderOrigin extended value.name value.toVConstant where
  source := base
  ordered := formed
  formation := types value member
  sourceBelow := VEnv.addConstVals_le installed
  fresh := VEnv.addConstVals_names_fresh installed value member
  constant := VEnv.addConstVals_get installed member

end Lean4Lean.VEnv
