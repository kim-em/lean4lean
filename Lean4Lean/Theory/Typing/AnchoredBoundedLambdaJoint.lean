import Lean4Lean.Theory.Typing.AnchoredBoundedLambdaRule
import Lean4Lean.Theory.Typing.AnchoredBoundedPiRule
import Lean4Lean.Theory.Typing.AnchoredBoundedConversion

/-! Both directions of the original strong lambda rule. The reverse natural
Pi type is converted by the concrete Pi producer built from the same original
formation children, rather than by interpreting a synthesized typing proof. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

theorem Joint.lamDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : Joint current fuel env U registry source A A' (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalCodomain' : Joint current fuel env U registry (A' :: source) B B (.sort bodyLevel))
    (originalBody : Joint current fuel env U registry (A :: source) body other B)
    (originalBody' : Joint current fuel env U registry (A' :: source) body other B)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (codomain' : env.HasType U (A' :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (bodies' : env.IsDefEq U (A' :: source) body other B) :
    Joint current fuel env U registry source (.lam A body) (.lam A' other) (.forallE A B) := by
  have pi := Joint.forallEDF henv hscoped originalDomain originalCodomain originalCodomain'
    domains codomain codomain'
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have forward : Transfer current fuel env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) := Transfer.lamDF henv hscoped originalDomain originalBody originalCodomain
    domains codomain bodies bodies'.hasType.2 closed hTarget substitutions fits
  have backward : Transfer current fuel env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A' B) := Transfer.lamDF henv hscoped originalDomain.symm originalBody'.symm
    originalCodomain' domains.symm codomain' bodies'.symm bodies.hasType.1
    closed hTarget substitutions fits
  exact ⟨forward, Transfer.convert henv hscoped pi.symm closed hTarget substitutions fits backward⟩

end Lean4Lean.AnchoredSource.Adapted.Staged
