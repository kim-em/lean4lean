import Lean4Lean.Theory.Typing.Strengthening.StructureLevelCompatibility
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointQuotRepair

/-! # Universe compatibility of the quotient-repaired declaration collection

The closed proposition-source quotient value is an instance of a fixed two-level
expression. Equivalent levels preserve its source-zero guard and change the
value only structurally. Selected structure equations already have their own
proved compatibility; the two results compose without saturating declarations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation

namespace ClosedQuot
/-- The quotient unfolding value is a fixed template instantiated at its two
universe arguments. No reduction or equation is used in this identity. -/
theorem value_template : (value (.param 0) (.param 1)).instL [u,v] = value u v := by
  rfl

/-- Equivalent well-formed universes change the closed quotient unfolding only
by structural level equivalence, including its dependent lambda telescope. -/
theorem value_level_equiv
    (hu : u.WF U) (hv : v.WF U) (hu' : u'.WF U) (hv' : v'.WF U)
    (eu : u ≈ u') (ev : v ≈ v') : LEquiv U (value u v) (value u' v') := by
  rw [← value_template, ← value_template (u := u') (v := v')]
  exact .instL_expr _ (by simpa using And.intro hu hv) (by simpa using And.intro hu' hv')
    (.cons eu (.cons ev .nil))

/-- Adding the closed proposition-source quotient equation to actual stored
definitions preserves universe compatibility with no change to its syntax. -/
theorem definitions_levelCompatible {env : VEnv} (henv : env.WF) (hq : QuotRegistered env) :
    (definitions env U henv hq).LevelCompatible U := by
  intro name ls ls' rhs H hw' he
  rcases H with H | ⟨rfl, u, v, rfl, hu, hv, hz, rfl⟩
  · obtain ⟨rhs', HD, HE⟩ := Definitions.ofEnv_levelCompatible henv H hw' he
    exact ⟨rhs', .inl HD, HE⟩
  · cases he with
    | @cons _ u' _ ls' eu he =>
      cases he with
      | @cons _ v' _ tail ev he =>
        cases he
        have hu' := hw' u' (by simp)
        have hv' := hw' v' (by simp)
        exact ⟨_, .inr ⟨rfl, _, _, rfl, hu', hv', eu.symm.trans hz, rfl⟩,
          value_level_equiv hu hv hu' hv' eu ev⟩
end ClosedQuot

variable [Params]
namespace RegisteredStructure
/-- Universe compatibility of the base collection and the selected structure
programs compose. The base may contain the repaired quotient equation. -/
theorem definitions_levelCompatible (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    (definitions D).LevelCompatible univs := by
  intro name ls ls' rhs H hw he
  rcases H with HD | HS
  · obtain ⟨rhs', H', HE⟩ := hlevels HD hw he
    exact ⟨rhs', .inl H', HE⟩
  · obtain ⟨rhs', H', HE⟩ := HS.congr_levels hcon hw he
    exact ⟨rhs', .inr H', HE⟩
end RegisteredStructure

namespace ErasedQuotCore
/-- The complete repaired collection of stored definitions, selected structure
programs and the proposition-source quotient equation is universe-compatible. -/
theorem levelCompatible (hq : QuotRegistered env)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) :
    (definitions hq).LevelCompatible univs :=
  RegisteredStructure.definitions_levelCompatible (ClosedQuot.definitions_levelCompatible henv hq) hcon
end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
