import Lean4Lean.Theory.Typing.Strengthening.SingletonTransportComparison
import Lean4Lean.Theory.Typing.Injectivity

/-! # The result-index obligation retained by transported extraction

For canonical Eq with its rigid family head, the constructor can be typed at
Eq A a b exactly when a and b already convert. Producing its (empty) field list
therefore cannot by itself supply a generic constructor at arbitrary indices.
The rigidity premise is explicit; this is not a strengthening counterexample.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv} {u : VLevel}

/-- Typing reflexivity at a requested second endpoint is exactly endpoint
conversion. A proof of Eq at arbitrary endpoints cannot replace this condition. -/
theorem eqRefl_typed_iff_endpoint_eq (henv : env.WF) (heq : env.HasCanonicalEq)
    (hr : env.Rigid ``Eq) (hu : u.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (ha : env.HasType U Γ a A) :
    env.HasType U Γ (eqReflApp u A a) (eqApp u A a b) ↔ env.IsDefEq U Γ a b A := by
  have href := HasType.eqReflApp heq hu hA ha
  constructor
  · intro ht
    have htypes := href.uniqU henv hΓ ht
    have hprop := HasType.eqApp heq hu hA ha ha
    have hspine : env.IsDefEqU U Γ (mkApps (.const ``Eq [u]) [A, a, a])
        (mkApps (.const ``Eq [u]) [A, a, b]) := htypes
    obtain ⟨_, hargs⟩ := hspine.rigidApp_inv henv hΓ hr hprop
    cases hargs with | cons _ hargs =>
    cases hargs with | cons _ hargs =>
    cases hargs with | cons hab _ =>
    exact hab.of_l henv hΓ ha
  · intro hab
    exact (IsDefEq.eqApp_r heq hu hA ha hab).defeq href

end Lean4Lean.VEnv.Strengthening
