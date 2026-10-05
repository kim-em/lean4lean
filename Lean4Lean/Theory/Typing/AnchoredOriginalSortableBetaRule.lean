import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBetaBackward

/-! Both hereditary beta directions use only the original stored premises.
Backward query factoring retains the original instantiated endpoint as its root. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

/-- Both beta directions replay only actual stored original children. The
inverse-substitution worker changes finite syntax, not source proof origins. -/
theorem OriginalTail.DerivationHereditaryFundamental.beta
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (bodyRef : Derivation sourceEnv U (A :: source) body body B)
    (argumentRef : Derivation sourceEnv U source argument argument A)
    (result : Derivation sourceEnv U source (B.inst argument) (B.inst argument) (.sort bodyLevel))
    (instantiated : Derivation sourceEnv U source (body.inst argument) (body.inst argument) (B.inst argument))
    (domainIH : DerivationHereditaryFundamental env registry context domain)
    (codomainIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) codomain)
    (bodyIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) bodyRef)
    (argumentIH : DerivationHereditaryFundamental env registry context argumentRef)
    (instantiatedIH : DerivationHereditaryFundamental env registry context instantiated) :
    DerivationHereditaryFundamental env registry context
      (.beta domainWF bodyWF domain codomain bodyRef argumentRef result instantiated) := by
  intro target locals σ τ available closed hTarget substitutions fits
  have forward : SortableComputationalTransfer env U registry target locals σ τ available
      (.app (.lam A body) argument) (body.inst argument) (B.inst argument) :=
    SortableComputationalTransfer.betaForwardOriginal henv hscoped context (.left domain) (.ref (.left argumentRef))
      (.ref (.left bodyRef)) (.ref (.left codomain)) (.ref (.left instantiated))
      (fun target locals σ τ available closed formed substitutions fits => (domainIH target locals σ τ available closed formed substitutions fits).1)
      (fun target locals σ τ available closed formed substitutions fits => (argumentIH target locals σ τ available closed formed substitutions fits).1)
      (fun target locals σ τ available closed formed substitutions fits => (bodyIH target locals σ τ available closed formed substitutions fits).1)
      (fun target locals σ τ available closed formed substitutions fits => (codomainIH target locals σ τ available closed formed substitutions fits).1)
      (fun target locals σ τ available closed formed substitutions fits => (instantiatedIH target locals σ τ available closed formed substitutions fits).1)
      (domain.forget.defeq.mono hle) (codomain.forget.defeq.mono hle)
      (bodyRef.forget.defeq.mono hle) (argumentRef.forget.defeq.mono hle)
      closed hTarget substitutions fits
  have argumentChild : SortableComputationalTransfer env U registry target locals τ τ available argument argument A :=
    (argumentIH target locals τ τ available closed hTarget (substitutions.right henv hTarget) fits.right).1
  have instantiatedChild : SortableComputationalTransfer env U registry target locals σ τ available
      (body.inst argument) (body.inst argument) (B.inst argument) :=
    (instantiatedIH target locals σ τ available closed hTarget substitutions fits).1
  have backward : SortableComputationalTransfer env U registry target locals σ τ available
      (body.inst argument) (.app (.lam A body) argument) (B.inst argument) := by
    intro n demand footprint observation resources
    obtain ⟨value⟩ := instantiatedChild observation resources
    exact value.betaExpandOriginal henv (.left instantiated) argumentChild (bodyRef.forget.defeq.mono hle)
      (argumentRef.forget.defeq.mono hle) (result.forget.defeq.mono hle)
      closed hTarget substitutions
  exact ⟨forward, backward⟩


end Lean4Lean.AnchoredSource.Adapted
