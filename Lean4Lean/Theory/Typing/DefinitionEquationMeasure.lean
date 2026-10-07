import Lean4Lean.Theory.Typing.ConstantHeaderProvenance
import Lean4Lean.Theory.Typing.DefinitionDeclarationProvenance
import Lean4Lean.Theory.Typing.ProjectionRigidity

/-! The finite set of installed equations supplies an additional declaration
measure. Repeating an equation does not increase the count, while entering a
definition's actual pre-equation header removes its own defining equation. -/
namespace Lean4Lean.VEnv
set_option Elab.async false
variable {env extended source : VEnv} {rule : VDefEq}

structure EquationDomain (env : VEnv) where
  rules : List VDefEq
  nodup : rules.Nodup
  present : ∀ rule, rule ∈ rules ↔ env.defeqs rule

namespace EquationDomain

def extend (domain : EquationDomain env) (same : extended.defeqs = env.defeqs) :
    EquationDomain extended where
  rules := domain.rules
  nodup := domain.nodup
  present := by intro rule; rw [same]; exact domain.present rule

/-- Adding a rule already in the environment leaves its finite set unchanged. -/
noncomputable def add (domain : EquationDomain env) (rule : VDefEq) :
    EquationDomain (env.addDefEq rule) := by
  classical
  by_cases member : rule ∈ domain.rules
  · refine ⟨domain.rules, domain.nodup, ?_⟩
    intro selected
    change selected ∈ domain.rules ↔ selected = rule ∨ env.defeqs selected
    constructor
    · exact fun present => .inr ((domain.present selected).mp present)
    · intro present
      rcases present with rfl | present
      · exact member
      · exact (domain.present selected).mpr present
  · refine ⟨rule :: domain.rules, List.nodup_cons.mpr ⟨member, domain.nodup⟩, ?_⟩
    intro selected
    change selected ∈ rule :: domain.rules ↔ selected = rule ∨ env.defeqs selected
    rw [List.mem_cons, domain.present]

theorem length_le (left : EquationDomain env) (right : EquationDomain extended)
    (below : env ≤ extended) : left.rules.length ≤ right.rules.length :=
  left.nodup.length_le_of_subset (fun rule member =>
    (right.present rule).mpr (below.defeqs ((left.present rule).mp member)))

theorem length_eq (left right : EquationDomain env) : left.rules.length = right.rules.length :=
  Nat.le_antisymm (left.length_le right .rfl) (right.length_le left .rfl)

theorem length_lt_of_new (left : EquationDomain env) (right : EquationDomain extended)
    (below : env ≤ extended) (absent : ¬ env.defeqs rule) (present : extended.defeqs rule) :
    left.rules.length < right.rules.length := by
  have fresh : rule ∉ left.rules := fun member => absent ((left.present rule).mp member)
  have unique : (rule :: left.rules).Nodup := List.nodup_cons.mpr ⟨fresh, left.nodup⟩
  have bounded := unique.length_le_of_subset (l₂ := right.rules) (by
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact (right.present selected).mpr present
    · exact (right.present selected).mpr (below.defeqs ((left.present selected).mp member)))
  exact Nat.lt_of_succ_le bounded

end EquationDomain

/-- The actual ordering proof enumerates the equation set. Constant and
metadata installations retain it; equation installations add at most one rule. -/
theorem Ordered.equationDomain (formed : env.Ordered) : Nonempty (EquationDomain env) := by
  induction formed with
  | empty =>
    exact ⟨⟨[], by simp, by intro rule; change rule ∈ [] ↔ False; simp⟩⟩
  | const _ _ installed ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.extend (VEnv.addConst_defeqs installed)⟩
  | defeq _ _ ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.add _⟩
  | eliminator _ ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.extend rfl⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨domain⟩ := ih
    exact ⟨domain.extend (by simp)⟩

noncomputable def Ordered.equationCount (formed : env.Ordered) : Nat :=
  (Classical.choice formed.equationDomain).rules.length

theorem Ordered.equationCount_le (left : env.Ordered) (right : extended.Ordered)
    (below : env ≤ extended) : left.equationCount ≤ right.equationCount :=
  (Classical.choice left.equationDomain).length_le (Classical.choice right.equationDomain) below

theorem Ordered.equationCount_eq (left right : env.Ordered) :
    left.equationCount = right.equationCount :=
  (Classical.choice left.equationDomain).length_eq (Classical.choice right.equationDomain)

theorem Ordered.equationCount_lt_of_new (left : env.Ordered) (right : extended.Ordered)
    (below : env ≤ extended) (absent : ¬ env.defeqs rule) (present : extended.defeqs rule) :
    left.equationCount < right.equationCount :=
  (Classical.choice left.equationDomain).length_lt_of_new
    (Classical.choice right.equationDomain) below absent present

namespace DefinitionDeclarationOrigin

/-- The name of this definition was fresh before the whole mutual header. -/
theorem base_name_absent (origin : DefinitionDeclarationOrigin env declarations value) :
    origin.base.constants value.name = none := by
  cases lookup : origin.base.constants value.name with
  | none => rfl
  | some constant =>
    have quiet := origin.current_old lookup
    rw [origin.current_self] at quiet
    cases quiet

/-- Header installation adds no equations, and freshness excludes this
definition's left-hand head from every old equation. -/
theorem header_equation_absent (origin : DefinitionDeclarationOrigin env declarations value) :
    ¬ origin.stage.header.defeqs value.toDefEq := by
  rw [origin.header_defeqs]
  intro present
  exact (VEnv.WF.ordered ⟨_, origin.history⟩).rigid_of_absent origin.base_name_absent
    value.toDefEq present (VLevel.params value.uvars) rfl

/-- The actual source may contain exactly the same constants as the retained
header. Its installed defining equation still gives a strict decrease. -/
theorem header_equationCount_lt (origin : DefinitionDeclarationOrigin env declarations value)
    (sourceOrdered : source.Ordered) (headerBelow : origin.stage.header ≤ source)
    (present : source.defeqs value.toDefEq) :
    origin.headerWF.ordered.equationCount < sourceOrdered.equationCount :=
  origin.headerWF.ordered.equationCount_lt_of_new sourceOrdered headerBelow
    origin.header_equation_absent present

end DefinitionDeclarationOrigin
end Lean4Lean.VEnv
