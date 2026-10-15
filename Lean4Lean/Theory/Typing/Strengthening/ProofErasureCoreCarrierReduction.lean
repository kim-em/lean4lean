import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction

/-! # Subsingleton guards at the newly recovered ordinary-core domain

Composite recovery under oracle computation chooses a new Pi and computes the
old domain to its new domain. Structural subsingleton certificates survive that
computation, so their argument guards can be rebuilt at the selected domain.
Arbitrary function/field carrier guards remain a separate transport problem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private forall_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
variable [Params]

/-- Structural subsingleton carriers survive all repaired ordinary-core
computation. Rigid empty-structure heads keep their arity, and Pi computation
preserves the recursively subsingleton codomain. -/
theorem ProofShape.SubsingletonCarrier.quot_core_compute
    (hq : QuotRegistered env) (H : SubsingletonCarrier A)
    (R : Compute (ErasedQuotCore.Step hq) A B) : SubsingletonCarrier B := by
  induction H generalizing B with
  | unit hi hx hf hp =>
    have RS := R.scoped (Step' := fun _ => ErasedQuotCore.Step hq) (Δ := []) (fun H => .base H)
    obtain ⟨ps', rfl, Hps⟩ := RS.const_spine (fun H =>
      erased_iota_primitive_no_rigid (henv.projectionRigid hi)
        (ErasedQuotCore.no_rigid hq (henv.projectionRigid hi)) H (ProofShape.constHead_mkApps _ _))
    exact .unit hi hx hf (Hps.length_eq.symm.trans hp)
  | forallE H ih =>
    obtain ⟨A', B', rfl, _, RB⟩ := forall_parts hq R
    exact .forallE (ih RB)

namespace ErasedQuotCore
/-- Oracle reduction re-synthesizes a recovered Pi and its argument guard
jointly when the original recovered domain is structurally subsingleton. The
selected domain is free to change and its guard is rebuilt at that new domain.
This does not assume full JointCarrierDomainResynthesis. -/
theorem recovery_subsingleton_oracle_reduce
    (hq : QuotRegistered env) (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f T)
    (HO : ∀ i, Compute (Step hq) (contextOracle (proofEraseCtx Γ) i) (contextOracle Δ' i))
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B))
    (HS : SubsingletonCarrier A) :
    ∃ A' B', ScopedTypeRecovery (fun _ => Step hq) Δ' (proofErase Γ f) (.forallE A' B') ∧
      JointCarrierGuard (fun _ => Step hq) Δ' A' x y := by
  obtain ⟨A', B', HR, HA, _⟩ := recovery_pi_oracle_reduce hq hcon hΓ hf HO R
  exact ⟨A', B', HR, .carrierSubsingleton (HS.quot_core_compute hq HA)⟩

end ErasedQuotCore
end Lean4Lean.VEnv.Strengthening
