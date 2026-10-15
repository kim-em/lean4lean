import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierResynthesisStrength
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreHeadBoundary

/-! # Joint domain re-synthesis fails for ordinary core recovery

The failure is independent of the argument comparison language: reflexive
arguments already force Pi exposure of a reflexive cast along a free proof.
Every well-formed canonical-Eq environment supplies the needed proof context.
No recursive definition or special structure is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Ordinary core recovery cannot satisfy joint domain re-synthesis, however
strong the carrier comparison primitives are. A free reflexive equality proof
gives the obstructing type cast in any canonical-Eq environment. -/
theorem not_carrier_domain_resynthesis_core {env : VEnv} (henv : env.WF)
    (U : Nat) (heq : env.HasCanonicalEq)
    (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    letI := henv.params U
    ¬ CarrierDomainResynthesis ErasedCore.Step Step := by
  letI := henv.params U
  intro H
  let u : VLevel := .succ (.succ (.succ .zero))
  let X : VExpr := .sort (.succ (.succ .zero))
  let F : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX : env.HasType U [] X (.sort u) := .sort (by trivial)
  have hF : env.HasType U [] F X :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hQ : env.HasType U [] Q (.sort .zero) :=
    HasType.eqApp heq hu (HasType.sort hu) hX hX
  have hΓ : OnCtx [Q] (env.IsType U) := ⟨trivial, _, hQ⟩
  have hXΓ : env.HasType U [Q] X (.sort u) := hX.weak0 henv.ordered
  have hFΓ : env.HasType U [Q] F X := hF.weak0 henv.ordered
  have hq : env.HasType U [Q] (.bvar 0) Q := by
    have HH : env.HasType U [Q] (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, VExpr.lift, liftN] using HH
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hXΓ hq hFΓ
  obtain ⟨A', B', R⟩ := H.positive_pi_exposure
    (fun H => erased_iota_primitive_subst H) hΓ HC.hasType.1 ⟨_, HC⟩
  exact ErasedCore.cast_no_pi henv U heq hu hΓ hXΓ hq hFΓ
    (R.scoped (fun H => .base H))

/-- One compared-K stage repairs Pi recovery of a variable declared at a
reflexive Pi cast. The free equality proof need not compute. This is a checked
repair of the obstruction, not a claim of same-stage or finite-stage completeness. -/
theorem reflexive_cast_variable_pi_stage_one [Params]
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ (.sort v) (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) (.sort v) (.sort v)))
    (hPi : env.HasType univs Γ (.forallE A B) (.sort v))
    (hl : Lookup Γ i (typeCast u (.sort v) (.sort v) q (.forallE A B)))
    (hn : ¬ IsProof Γ (.bvar i)) :
    ProofShape.TypeRecovery (ErasedComparedKStage D 1) (ProofShape.contextOracle (proofEraseCtx Γ))
      (proofErase Γ (.bvar i))
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) := by
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hPi
  have RC := proofErase_compared_K_forward (stage := 0) heq hs hΓ HC.hasType.1 .refl
  have EPi : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) := if_neg (not_isProof_of_sort hΓ hPi)
  rw [EPi] at RC
  have R : ProofShape.TypeRecovery (ErasedComparedKStage D 1) (erasedTypeOracle Γ)
      (.bvar i) (proofErase Γ (typeCast u (.sort v) (.sort v) q (.forallE A B))) := by
    rw [← erasedTypeOracle_valid hΓ hl]
    exact .bvar
  rw [proofEraseCtx_oracle, show proofErase Γ (.bvar i) = .bvar i from if_neg hn]
  exact R.convert RC

end Lean4Lean.VEnv.Strengthening
