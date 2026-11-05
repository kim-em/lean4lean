import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLowerTypeHistory

/-! # Fixed lower histories cannot observe parameter-dependent constructors

Adding a bare-constructor rule to the term observer is insufficient. Its native
soundness conclusion would demand a fixed lower history for the constructor's
codomain under a fresh parameter binder. A retained occurrence of that parameter
cannot be the lift of any lower type. The demand language must change together
with the term grammar, for example by tracking parameter values or allowing
origins to depend on the newly supplied parameter.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private ProofShape.liftN_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params] {D : PureObservation.Definitions}

/-- A fixed lower type history excludes a retained temporary variable in an
application argument, regardless of the computation witnessing the history. -/
theorem LowerTypeHistory.no_temporary_argument
    (H : LowerTypeHistory D Γ origin n Δ (.app f (.bvar j))) (hj : j < n) : False := by
  obtain ⟨A, _, _, _, EA, _⟩ := H
  obtain ⟨_, a, _, _, Ea⟩ := ProofShape.liftN_app_inv EA
  cases a <;> simp only [ProofShape.liftN] at Ea <;> try cases Ea
  simp only [liftVar, Nat.not_lt_zero, ↓reduceIte] at hj
  omega

/-- No input-demand list can make a fresh-parameter codomain into a fixed
lower result history. In particular this excludes the literal type of a
fieldless one-parameter constructor, Pi S (family #0). -/
theorem lower_type_demand_no_parameter_function
    (H : LowerTypeDemand D Γ origin (.app keys .pi) n Δ
      (.forallE A (.app f (.bvar 0)))) : False := by
  have HB := H.function_parts.2
  simp only [NativeGroundDemand] at HB
  exact HB.no_temporary_argument (by omega)

/-- More generally, any parameter still inside the temporary prefix is
excluded from the terminal codomain of this one-argument demand. -/
theorem lower_type_demand_no_temporary_result
    (H : LowerTypeDemand D Γ origin (.app keys .pi) n Δ
      (.forallE A (.app f (.bvar j)))) (hj : j < n+1) : False := by
  have HB := H.function_parts.2
  simp only [NativeGroundDemand] at HB
  exact HB.no_temporary_argument hj

end Lean4Lean.VEnv.Strengthening
