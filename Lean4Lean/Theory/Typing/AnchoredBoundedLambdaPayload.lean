import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaJoint
import Lean4Lean.Theory.Typing.AnchoredBoundedPiPayload

/-! The actual lambda constructor of the bounded original Strong motive. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged.OriginalPayload
open VExpr VEnv
variable {current : Name → Bool} {fuel : Nat} {sourceEnv finalEnv : VEnv}
  {U : Nat} {registry : CanonicalHead.Registry}

theorem lamDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A' (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HB' : IsDefEqStrong sourceEnv U (A' :: Γ) B B (.sort v)}
    {He : IsDefEqStrong sourceEnv U (A :: Γ) body other B}
    {He' : IsDefEqStrong sourceEnv U (A' :: Γ) body other B}
    (domain : OriginalPayload current fuel sourceEnv finalEnv U registry HA)
    (codomain : OriginalPayload current fuel sourceEnv finalEnv U registry HB)
    (codomain' : OriginalPayload current fuel sourceEnv finalEnv U registry HB')
    (body : OriginalPayload current fuel sourceEnv finalEnv U registry He)
    (body' : OriginalPayload current fuel sourceEnv finalEnv U registry He') :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.lamDF hu hv HA HB HB' He He') :=
  ⟨Joint.lamDF henv hscoped domain.joint codomain.joint codomain'.joint body.joint body'.joint
      (HA.defeq.mono hle) (HB.defeq.mono hle) (HB'.defeq.mono hle)
      (He.defeq.mono hle) (He'.defeq.mono hle),
    trivial, trivial⟩

end Lean4Lean.AnchoredSource.Adapted.Staged.OriginalPayload
