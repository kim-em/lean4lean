import Lean4Lean.Theory.Typing.AnchoredConstructorDisplay
import Lean4Lean.Theory.Typing.AnchoredExposureLevels

/-! Universe-equivalent constructor endpoints retain their exact displayed
constructor and argument packet. The finite origin records the endpoint
congruence explicitly. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv
set_option backward.isDefEq.respectTransparency false

def ConstructorDisplay.changeLevels
    {env : VEnv} {U : Nat} {registry : CanonicalDataHead.Registry}
    (henv : env.Ordered)
    (display : ConstructorDisplay env U registry Γ expression type Δ ρ head)
    (equal : EqUpToLevels U expression expression') :
    ConstructorDisplay env U registry Γ expression' type Δ ρ head :=
  { display with
    origin := .trans
      (.symm (.levels (display.targetWF henv) display.sound.hasType.1 (equal.lift' ρ)))
      display.origin
    sound := (display.sound.hasType.1.eqUpToLevels henv (display.targetWF henv)
      (equal.lift' ρ)).symm.trans display.sound }

end Lean4Lean.AnchoredSemantics
