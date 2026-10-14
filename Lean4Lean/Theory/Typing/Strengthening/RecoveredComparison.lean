import Lean4Lean.Theory.Typing.Strengthening.TypeRecovery
import Lean4Lean.Theory.Typing.Strengthening.RecoveredComparisonCore

/-! # Independent comparison with certified K type recovery

The original comparison is the generic relation specialized to fixed-depth K
computation. Its public constructors and descent interface are retained.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- The original application comparison uses certified K to recover types. -/
abbrev RecoveredComparison (D : Definitions) (depth : Nat) :=
  RecoveredComparisonWith (CertifiedKCompute D depth)

namespace RecoveredComparison
export RecoveredComparisonWith (base app recover sameType)
end RecoveredComparison

/-- Specialized ambient soundness, retaining field-notation compatibility. -/
theorem RecoveredComparison.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : RecoveredComparison D depth mode Γ a b) : env.IsDefEqU univs Γ a b :=
  RecoveredComparisonWith.defeq hΓ H

/-- Independent comparison can also be used in common mode. -/
theorem RecoveredComparison.promote (H : RecoveredComparison D depth false Γ a b) :
    RecoveredComparison D depth true Γ a b := RecoveredComparisonWith.promote H

/-- Both modes descend using checked certified K computation. -/
theorem RecoveredComparison.descend
    (H : RecoveredComparison D depth mode Γ' (a.lift' ρ) (b.lift' ρ))
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (hmode : if mode then env.IsDefEqU univs Γ A B else ¬ IsProof Γ a) :
    env.IsDefEqU univs Γ a b :=
  RecoveredComparisonWith.descend H (CertifiedKCompute.computeDescent heq hs) W hΓ hΓ' ha hb hmode

/-- Weakening preserves the original depth bound. -/
theorem RecoveredComparison.weakN (W : Ctx.LiftN k j Γ Γ')
    (H : RecoveredComparison D depth mode Γ a b) :
    RecoveredComparison D depth mode Γ' (a.liftN k j) (b.liftN k j) :=
  RecoveredComparisonWith.weakN
    (fun W R => R.weakN (fun W H => KCertificate.weakN W H) W) W H

end Lean4Lean.VEnv.Strengthening
