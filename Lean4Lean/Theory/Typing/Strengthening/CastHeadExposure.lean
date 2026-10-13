import Lean4Lean.Theory.Typing.Strengthening.CastTypedReplay
import Lean4Lean.Theory.Typing.Strengthening.FullHeadExposure

/-! # Typed cast elimination around mixed computational head exposure

The payload's mixed path can contain both eta forms and all computations of the
existing constructor model. Typed replay removes an enclosing cast without any
syntactic endpoint match. This is a root cast rule, not compatible raw cast erasure.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
open ConstructorObservation (EtaCompute ConstructorRigid)
variable [Params] {D : Definitions}

/-- Pi observation of a lifted payload recovers a Pi below its typed cast.
The payload trace's eta annotations need not descend, and neither cast endpoint
needs to match the other syntactically. -/
theorem cast_mixed_pi_exposure_below (heq : env.HasCanonicalEq)
    (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.HasType univs Γ (typeCast u X Y p x) (.sort v))
    (R : EtaCompute D (x.lift' ρ) (.forallE A B)) :
    ∃ A₀ B₀, env.IsDefEq univs Γ (typeCast u X Y p x) (.forallE A₀ B₀) (.sort v) := by
  obtain ⟨A', B', RP⟩ := R.pi_exposure hD
  exact cast_pi_exposure_below heq hs hΓ hc (CastCompute.base RP)

/-- A function whose type is an outer cast acquires a Pi typing below whenever
its payload has a mixed Pi exposure above. No cast-to-payload equality is assumed. -/
theorem cast_function_type_below (heq : env.HasCanonicalEq)
    (hD : ConstructorRigid D) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (typeCast u X Y p x))
    (R : EtaCompute D (x.lift' ρ) (.forallE A B)) :
    ∃ A₀ B₀, env.HasType univs Γ f (.forallE A₀ B₀) ∧
      env.IsDefEqU univs Γ (typeCast u X Y p x) (.forallE A₀ B₀) := by
  obtain ⟨v, hc⟩ := hf.isType henv hΓ
  obtain ⟨A₀, B₀, h⟩ := cast_mixed_pi_exposure_below heq hD hs hΓ hc R
  exact ⟨A₀, B₀, h.defeq hf, _, h⟩

end Lean4Lean.VEnv.Strengthening
