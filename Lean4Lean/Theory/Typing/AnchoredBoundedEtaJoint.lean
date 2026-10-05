import Lean4Lean.Theory.Typing.AnchoredBoundedEtaContraction
import Lean4Lean.Theory.Typing.AnchoredBoundedEtaExpansion
import Lean4Lean.Theory.Typing.AnchoredBoundedConversion

/-! The actual eta rule closes the graded joint contract in both directions.
Only original domain, codomain, and function children are interpreted. -/
namespace Lean4Lean.AnchoredSource.Adapted.Staged
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
variable {current : Name → Bool} {fuel : Nat}

theorem Joint.eta
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {source : List VExpr} {A B f : VExpr}
    (originalDomain : Joint current fuel env U registry source A A (.sort domainLevel))
    (originalCodomain : Joint current fuel env U registry (A :: source) B B (.sort bodyLevel))
    (originalFunction : Joint current fuel env U registry source f f (.forallE A B))
    (formedA : env.HasType U source A (.sort domainLevel))
    (formedB : env.HasType U (A :: source) B (.sort bodyLevel))
    (functionTyped : env.HasType U source f (.forallE A B)) :
    Joint current fuel env U registry source (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) := by
  apply Joint.of_transfers henv
  intro target locals σ τ available closed hTarget substitutions fits
  constructor
  · intro n demand footprint observation observationBound resources
    exact Obs.eta_contract henv hscoped originalDomain originalCodomain originalFunction
      formedA formedB functionTyped closed hTarget substitutions fits observation observationBound resources
  · intro n demand footprint observation observationBound resources
    obtain ⟨result⟩ := (originalFunction target locals σ τ available closed hTarget
      substitutions fits).1 observation observationBound resources
    exact result.etaExpand henv hscoped originalDomain originalCodomain
      formedA formedB functionTyped closed hTarget substitutions fits

end Lean4Lean.AnchoredSource.Adapted.Staged
