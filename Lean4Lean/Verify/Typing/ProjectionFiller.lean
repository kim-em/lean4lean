import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean

/-!
Closed filler data for Prop-valued motives and minors that are irrelevant to
one primitive projection.  These terms mention no environment constant.

This is intentionally *not* a universe-polymorphic filler: `truth` has type
`Prop`, not `Sort u` for arbitrary `u`.  A primary-rec projection construction
at a nonzero or variable eliminator universe still needs separately derived
inhabitants for every unused motive.
-/

namespace ProjectionFiller

variable (env : VEnv) (U : Nat) (Gamma : List VExpr)

/-- The closed proposition `forall P : Prop, P -> P`. -/
def truth : VExpr :=
  .forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1))

/-- The canonical closed inhabitant `fun P p => p` of `truth`. -/
def witness : VExpr :=
  .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

theorem truth_hasType :
    env.HasType U Gamma truth (.sort .zero) := by
  unfold truth
  have hraw : env.HasType U Gamma
      (.forallE (.sort .zero) (.forallE (.bvar 0) (.bvar 1)))
      (.sort (.imax (.succ .zero) .zero)) := by
    apply VEnv.HasType.forallE
    · exact VEnv.HasType.sort (l := .zero) (by trivial)
    · have hinner : env.HasType U (.sort .zero :: Gamma)
          (.forallE (.bvar 0) (.bvar 1))
          (.sort (.imax .zero .zero)) := by
        apply VEnv.HasType.forallE
        · exact VEnv.HasType.bvar .zero
        · exact VEnv.HasType.bvar (.succ .zero)
      exact VEnv.IsDefEq.defeq
        (.sortDF (by trivial) (by trivial) VLevel.imax_zero) hinner
  exact VEnv.IsDefEq.defeq
    (.sortDF (by trivial) (by trivial) VLevel.imax_zero) hraw

theorem truth_isType : env.IsType U Gamma truth :=
  ⟨.zero, truth_hasType env U Gamma⟩

theorem witness_hasType : env.HasType U Gamma witness truth := by
  unfold witness truth
  apply VEnv.HasType.lam
  · exact VEnv.HasType.sort (l := .zero) (by trivial)
  · apply VEnv.HasType.lam
    · exact VEnv.HasType.bvar .zero
    · exact VEnv.HasType.bvar .zero

theorem witness_wf : witness.WF env U Gamma :=
  ⟨truth, witness_hasType env U Gamma⟩

@[simp] theorem truth_instL (levels : List VLevel) :
    truth.instL levels = truth := rfl

@[simp] theorem witness_instL (levels : List VLevel) :
    witness.instL levels = witness := rfl

end ProjectionFiller

end Lean4Lean
