import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBoxTypeChange
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRelatedRecovery

/-! # Recovery with recursive Pi and Box oracle changes

Native recovered domains and record parameters may themselves change. Source and target recovery
replay provide actual equal types for the computation simulation, avoiding
an assumed global output-congruence theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Typed recovery transports between actually convertible contexts when
their oracle types differ recursively through Pi and Box structure. The new
output is related by BoxTypeChange, including changes to domains and projected field types.
Conversion uses the equality obtained by replaying both recovery certificates;
it does not assume comparison or recovery completeness. -/
theorem proofErase_recovery_recursive_box
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hiBox : env.projections family infoBox) (hpBox : infoBox.nparams = 1)
    (hfBox : infoBox.numFields = 1)
    (hshapeBox : infoBox.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hcBox : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hinert : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const family []) args) out)
    (R : ScopedTypeRecovery Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : IsDefEqCtx env univs [] Γ Γ')
    (HO : ∀ i, BoxTypeChange family k (contextOracle Δ i) (contextOracle (proofEraseCtx Γ') i)) :
    ∃ out', ScopedTypeRecovery Step (proofEraseCtx Γ') source out' ∧ BoxTypeChange family k out out' :=
  proofErase_recovery_type_change hstep hsubst
    (BoxTypeChange.transport_laws hstep hhead hsubst hiBox hpBox hfBox hshapeBox hcBox hinert)
    R hΓ ht EΓ Ee W HO

end Lean4Lean.VEnv.Strengthening
