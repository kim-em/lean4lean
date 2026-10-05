import Lean4Lean.Theory.Typing.AnchoredBoundedPiRule
import Lean4Lean.Theory.Typing.AnchoredBoundedOriginalPayload

/-! The actual forallEDF constructor of the Strong induction motive. Its
literal formation trees retain precisely the original domain/body children. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged.OriginalPayload
open VExpr VEnv
variable {current : Name → Bool} {fuel : Nat} {sourceEnv finalEnv : VEnv}
  {U : Nat} {registry : CanonicalHead.Registry}

theorem forallEDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A' (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B' (.sort v)}
    {HB' : IsDefEqStrong sourceEnv U (A' :: Γ) B B' (.sort v)}
    (domain : OriginalPayload current fuel sourceEnv finalEnv U registry HA)
    (body : OriginalPayload current fuel sourceEnv finalEnv U registry HB)
    (body' : OriginalPayload current fuel sourceEnv finalEnv U registry HB') :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.forallEDF hu hv HA HB HB') :=
  ⟨Joint.forallEDF henv hscoped domain.joint body.joint body'.joint
      (HA.defeq.mono hle) (HB.defeq.mono hle) (HB'.defeq.mono hle),
    .pi (domain.leftType henv hscoped) (body.leftType henv hscoped)
      domain.leftFormation body.leftFormation,
    .pi (domain.rightType henv hscoped) (body'.rightType henv hscoped)
      domain.rightFormation body'.rightFormation⟩

theorem proofIrrel (henv : finalEnv.Ordered)
    {HP : IsDefEqStrong sourceEnv U Γ P P (.sort .zero)}
    {HL : IsDefEqStrong sourceEnv U Γ left left P}
    {HR : IsDefEqStrong sourceEnv U Γ right right P}
    (proposition : OriginalPayload current fuel sourceEnv finalEnv U registry HP)
    (left : OriginalPayload current fuel sourceEnv finalEnv U registry HL)
    (right : OriginalPayload current fuel sourceEnv finalEnv U registry HR) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.proofIrrel HP HL HR) :=
  ⟨Joint.proofIrrel henv proposition.joint left.joint right.joint,
    left.leftFormation, right.leftFormation⟩

end Lean4Lean.AnchoredSource.Adapted.Staged.OriginalPayload
