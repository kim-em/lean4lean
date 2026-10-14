import Lean4Lean.Theory.Typing.Strengthening.TypeRecovery
import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaCore

/-! # Compatible eta with recoverable function types

The first eta stage uses certified K computation to recover its annotations.
Further stages are defined separately in StagedEtaComputation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- The original recovered eta computation is one eta layer over certified K. -/
abbrev RecoveredEtaCompute (D : Definitions) (depth : Nat) :=
  RecoveredEtaWith (CertifiedKCompute D depth)

namespace RecoveredEtaCompute
export RecoveredEtaWith (base eta trans app lam forallE proj)
end RecoveredEtaCompute

/-- Identity is included in the computational base. -/
theorem RecoveredEtaCompute.refl : RecoveredEtaCompute D depth Γ e e := .base (.base .refl)

namespace RecoveredEtaWith
export RecoveredEtaCompute (refl)
end RecoveredEtaWith

/-- Recovered eta certificates survive finite binder insertion. -/
theorem RecoveredEtaCompute.weakN (W : Ctx.LiftN n k Γ Γ')
    (R : RecoveredEtaCompute D depth Γ e out) :
    RecoveredEtaCompute D depth Γ' (e.liftN n k) (out.liftN n k) :=
  RecoveredEtaWith.weakN (fun W H => H.weakN (fun W H => KCertificate.weakN W H) W) W R

/-- A typed lifted source determines the full lower result and typed equality. -/
theorem RecoveredEtaCompute.descend
    (R : RecoveredEtaCompute D depth Γ' (e.lift' ρ) target)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ out, target = out.lift' ρ ∧ env.IsDefEq univs Γ e out T :=
  RecoveredEtaWith.descend R (CertifiedKCompute.computeDescent heq hs) W hΓ hΓ' ht

/-- Typed replay is the identity-insertion instance of descent. -/
theorem RecoveredEtaCompute.simAt (R : RecoveredEtaCompute D depth Γ e out)
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.SimAt univs Γ e out :=
  RecoveredEtaWith.simAt R (CertifiedKCompute.computeDescent heq hs) hΓ

/-- Pi exposure includes recovered eta in computational bodies. -/
theorem RecoveredEtaCompute.pi_exposure_below
    (R : RecoveredEtaCompute D depth Γ' (e.lift' ρ) (.forallE A B))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    ∃ A₀ B₀, env.IsDefEq univs Γ e (.forallE A₀ B₀) T :=
  RecoveredEtaWith.pi_exposure_below R (CertifiedKCompute.computeDescent heq hs) W hΓ hΓ' ht

end Lean4Lean.VEnv.Strengthening
