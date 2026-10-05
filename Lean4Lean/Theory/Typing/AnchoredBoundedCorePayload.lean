import Lean4Lean.Theory.Typing.AnchoredBoundedSort
import Lean4Lean.Theory.Typing.AnchoredBoundedApplication
import Lean4Lean.Theory.Typing.AnchoredBoundedBetaJoint
import Lean4Lean.Theory.Typing.AnchoredBoundedEtaJoint
import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaPayload

/-! Ordinary constructors of the original Strong induction motive. Every
semantic premise is an actual original proof child, at the same native fuel. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged.OriginalPayload
open VExpr VEnv
variable {current : Name → Bool} {fuel : Nat} {sourceEnv finalEnv : VEnv}
  {U : Nat} {registry : CanonicalHead.Registry}

theorem sortDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hu : u.WF U) (hv : v.WF U) (equal : u ≈ v) :
    OriginalPayload current fuel sourceEnv finalEnv U registry
      (Γ := Γ) (.sortDF hu hv equal) :=
  ⟨Joint.sortDF henv hscoped hu hv equal, trivial, trivial⟩

theorem appDF (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {Hf : IsDefEqStrong sourceEnv U Γ f f' (.forallE A B)}
    {Ha : IsDefEqStrong sourceEnv U Γ a a' A}
    {HBa : IsDefEqStrong sourceEnv U Γ (B.inst a) (B.inst a') (.sort v)}
    (domain : OriginalPayload current fuel sourceEnv finalEnv U registry HA)
    (body : OriginalPayload current fuel sourceEnv finalEnv U registry HB)
    (function : OriginalPayload current fuel sourceEnv finalEnv U registry Hf)
    (argument : OriginalPayload current fuel sourceEnv finalEnv U registry Ha)
    (result : OriginalPayload current fuel sourceEnv finalEnv U registry HBa) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.appDF hu hv HA HB Hf Ha HBa) :=
  ⟨Joint.appDF henv hscoped domain.joint body.joint function.joint argument.joint result.joint
      (HA.defeq.mono hle) (HB.defeq.mono hle) (Ha.defeq.mono hle), trivial, trivial⟩

theorem beta (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {He : IsDefEqStrong sourceEnv U (A :: Γ) e e B}
    {Ha : IsDefEqStrong sourceEnv U Γ a a A}
    {HBa : IsDefEqStrong sourceEnv U Γ (B.inst a) (B.inst a) (.sort v)}
    {Hea : IsDefEqStrong sourceEnv U Γ (e.inst a) (e.inst a) (B.inst a)}
    (domain : OriginalPayload current fuel sourceEnv finalEnv U registry HA)
    (codomain : OriginalPayload current fuel sourceEnv finalEnv U registry HB)
    (body : OriginalPayload current fuel sourceEnv finalEnv U registry He)
    (argument : OriginalPayload current fuel sourceEnv finalEnv U registry Ha)
    (_result : OriginalPayload current fuel sourceEnv finalEnv U registry HBa)
    (instantiated : OriginalPayload current fuel sourceEnv finalEnv U registry Hea) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.beta hu hv HA HB He Ha HBa Hea) :=
  ⟨Joint.beta henv hscoped domain.joint argument.joint body.joint codomain.joint instantiated.joint
      (HA.defeq.mono hle) (HB.defeq.mono hle) (He.defeq.mono hle) (Ha.defeq.mono hle)
      (HBa.defeq.mono hle), trivial, instantiated.rightFormation⟩

theorem eta (henv : finalEnv.Ordered) (hscoped : registry.Scoped)
    (hle : sourceEnv ≤ finalEnv) (hu : u.WF U) (hv : v.WF U)
    {HA : IsDefEqStrong sourceEnv U Γ A A (.sort u)}
    {HB : IsDefEqStrong sourceEnv U (A :: Γ) B B (.sort v)}
    {HBlift : IsDefEqStrong sourceEnv U (A.lift :: A :: Γ)
      (B.liftN 1 1) (B.liftN 1 1) (.sort v)}
    {Hf : IsDefEqStrong sourceEnv U Γ f f (.forallE A B)}
    {Hflift : IsDefEqStrong sourceEnv U (A :: Γ) f.lift f.lift (.forallE A.lift (B.liftN 1 1))}
    {HAlift : IsDefEqStrong sourceEnv U (A :: Γ) A.lift A.lift (.sort u)}
    (domain : OriginalPayload current fuel sourceEnv finalEnv U registry HA)
    (codomain : OriginalPayload current fuel sourceEnv finalEnv U registry HB)
    (_liftedCodomain : OriginalPayload current fuel sourceEnv finalEnv U registry HBlift)
    (function : OriginalPayload current fuel sourceEnv finalEnv U registry Hf)
    (_liftedFunction : OriginalPayload current fuel sourceEnv finalEnv U registry Hflift)
    (_liftedDomain : OriginalPayload current fuel sourceEnv finalEnv U registry HAlift) :
    OriginalPayload current fuel sourceEnv finalEnv U registry (.eta hu hv HA HB HBlift Hf Hflift HAlift) :=
  ⟨Joint.eta henv hscoped domain.joint codomain.joint function.joint
      (HA.defeq.mono hle) (HB.defeq.mono hle) (Hf.defeq.mono hle), trivial, function.rightFormation⟩

end Lean4Lean.AnchoredSource.Adapted.Staged.OriginalPayload
