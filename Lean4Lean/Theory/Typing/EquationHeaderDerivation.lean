import Lean4Lean.Theory.Typing.EquationStratification
import Lean4Lean.Theory.Typing.AnchoredOriginalDerivation

/-! Fixed original equation endpoints below the recursive query grammar.
Selection and reification use only the target's actual ordered provenance;
this module does not depend on rich observations or their interpreters. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure
set_option Elab.async false

/-- Universe specialization of the actual chosen rule RHS proof. -/
noncomputable def EquationHeaderOrigin.instantiatedRhs
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Derivation origin.source U [] (rule.rhs.instL levels) (rule.rhs.instL levels)
      (rule.type.instL levels) :=
  Classical.choice (Derivation.reify (origin.strong.2.instL levelsWF))

theorem EquationHeaderOrigin.typeInstance
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    ∃ level, origin.source.IsDefEqStrong U [] (rule.type.instL levels)
      (rule.type.instL levels) (.sort level) := by
  have left : origin.source.HasType rule.uvars [] rule.lhs rule.type := origin.formation.1
  obtain ⟨level, formed⟩ := left.isType origin.ordered (Γ := []) trivial
  exact ⟨level.inst levels, (formed.strong origin.ordered (Γ := []) trivial).instL levelsWF⟩

noncomputable def EquationHeaderOrigin.instantiatedTypeLevel
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U) : VLevel :=
  (EquationHeaderOrigin.typeInstance origin levelsWF).choose

noncomputable def EquationHeaderOrigin.instantiatedType
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U) :
    Derivation origin.source U [] (rule.type.instL levels) (rule.type.instL levels)
      (.sort (EquationHeaderOrigin.instantiatedTypeLevel origin levelsWF)) :=
  Classical.choice (Derivation.reify (EquationHeaderOrigin.typeInstance origin levelsWF).choose_spec)

end Lean4Lean.AnchoredSource.Adapted
