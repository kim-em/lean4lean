import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedLambdaRule
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedPiRule
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedConversion

/-! Both directions of the original strong lambda rule. The reverse natural
Pi type is converted by the concrete Pi producer built from the same original
formation children, rather than by interpreting a synthesized typing proof. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem GradedJoint.lamDF
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (originalDomain : GradedJoint env U registry source A A' (.sort domainLevel))
    (originalCodomain : GradedJoint env U registry (A :: source) B B (.sort bodyLevel))
    (originalCodomain' : GradedJoint env U registry (A' :: source) B B (.sort bodyLevel))
    (originalBody : GradedJoint env U registry (A :: source) body other B)
    (originalBody' : GradedJoint env U registry (A' :: source) body other B)
    (domains : env.IsDefEq U source A A' (.sort domainLevel))
    (codomain : env.HasType U (A :: source) B (.sort bodyLevel))
    (codomain' : env.HasType U (A' :: source) B (.sort bodyLevel))
    (bodies : env.IsDefEq U (A :: source) body other B)
    (bodies' : env.IsDefEq U (A' :: source) body other B) :
    GradedJoint env U registry source (.lam A body) (.lam A' other) (.forallE A B) := by
  have pi := GradedJoint.forallEDF henv hscoped originalDomain originalCodomain originalCodomain'
    domains codomain codomain'
  apply GradedJoint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  have forward : GradedTransfer env U registry target locals σ τ available
      (.lam A body) (.lam A' other) (.forallE A B) := GradedTransfer.lamDF henv hscoped originalDomain originalBody originalCodomain
    domains codomain bodies bodies'.hasType.2 closed hTarget substitutions fits
  have backward : GradedTransfer env U registry target locals σ τ available
      (.lam A' other) (.lam A body) (.forallE A' B) := GradedTransfer.lamDF henv hscoped originalDomain.symm originalBody'.symm
    originalCodomain' domains.symm codomain' bodies'.symm bodies.hasType.1
    closed hTarget substitutions fits
  exact ⟨forward, GradedTransfer.convert henv hscoped pi.symm closed hTarget substitutions fits backward⟩

end Lean4Lean.AnchoredSource.Adapted
